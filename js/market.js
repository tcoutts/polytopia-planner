// Polytopia Planner v17 – MARKET planner (mode 'market').
// Rule (community wiki, please verify in game): a Market on an Empty tile earns ★ per turn = sum of the levels of the
// adjacent (8-neighbourhood) Windmill, Forge and Sawmill, capped at 8. Windmill level = adjacent Farms, Forge level =
// adjacent Mines, Sawmill level = adjacent Lumber Huts (of any owner). Market / Windmill / Forge / Sawmill need an
// Empty tile without resource (Fruit can be harvested first); a Farm needs Empty with Crop (for Farm), a Mine a
// Mountain with Metal, a Lumber Hut a Forest. One Market, Windmill, Forge and Sawmill per city, built in its own
// territory (tiles within 2, nearest city wins); a Market counts the workshops of any city next to it.
//
// v16: the user paints the board as it is (terrain Empty / Forest / Mountain / Water / City, resources Crop / Metal /
// Fruit, existing buildings). An exact branch & bound search finds the plan with the most ★/turn, then the lowest
// cost, then the fewest steps – using Clear / Burn / Grow Forest, Destroy (relocations), new Farms / Mines / Lumber
// Huts as allowed by the option toggles. Assumptions: Destroy is free (0 ★, one step) and leaves the terrain and its
// resource; Burn Forest gives Crop; Grow Forest removes a field resource.
//
// Steps: ① Cities (tap own cities; territory 3×3 or 5×5 each, borders editable per tile) → ② What's here (paint) →
// ③ Plan (exact optimizer, runs in chunks with a spinner). Only the tiles of the selected territories are planned.
// Pure logic (node-testable): PP.market.optimize(cells, opts), PP.market.createJob(cells, opts).step(deadline)
// cells [{ c, r, terrain, res:[crop|ore|fruit], bld, name?, own? }], opts { clear, burn, grow, destroy, produce, windmill, forge, sawmill, costs }.
// windmill / forge / sawmill = false: no NEW workshop of that type (tech not researched); existing ones still count.
// own = 'c,r' of the city tile the cell belongs to (explicit territory); without it: nearest city within 2.
(function (root) { root.PP = root.PP || {}; })(typeof window !== 'undefined' ? window : globalThis);
(function (PP) {
  'use strict';

  // ======================================================================== rules + data
  const CAP = 8;
  const WS = ['windmill', 'forge', 'sawmill'];
  const PROD = { windmill: 'farm', forge: 'mine', sawmill: 'lumber' }; // workshop → producer it counts
  const PROC_OF = { farm: 'windmill', mine: 'forge', lumber: 'sawmill' };
  const PRODS = ['farm', 'mine', 'lumber'];
  const UNIQUE = ['market', 'windmill', 'forge', 'sawmill'];
  const BLDS = PRODS.concat(UNIQUE);
  const TERR = ['field', 'forest', 'mountain', 'water', 'city'];
  const OPT_KEYS = ['clear', 'burn', 'grow', 'destroy', 'produce'];
  const WS_KEYS = WS; // workshop types the user allows to be built (opts.windmill / forge / sawmill)
  // resource actions the user can do (opts.fruit = Harvest Fruit needs Organization, opts.hunt = Hunt needs Hunting;
  // both 2 ★ and +1 population – the population is not valued by the plan, only the cost and the step)
  const RES_KEYS = ['fruit', 'hunt', 'fish']; // opts.fish = Catch Fish needs Fishing (only counts for the population)
  // ★ per action. destroy: free in the game (assumed 0 ★, still one action)
  const DEF_COST = { market: 5, windmill: 5, forge: 5, sawmill: 5, farm: 5, mine: 5, lumber: 3, clear: -1, burn: 5, plant: 5, fruit: 2, hunt: 2, destroy: 0 };
  const RANGE = 2; // city territory radius (Chebyshev)
  const BASE = { farm: 'field', mine: 'mountain', lumber: 'forest', windmill: 'field', forge: 'field', sawmill: 'field', market: 'field' };
  const PHASE = { destroy: 0, fruit: 1, hunt: 1, plant: 2, clear: 3, burn: 4, farm: 5, mine: 5, lumber: 5, windmill: 6, forge: 6, sawmill: 6, market: 7 };
  const BIG = 10000;     // w = primary·BIG + secondary (cost & actions)
  const HUGE = 1e9;      // V = income·HUGE − w
  const NB = [[-1, -1], [0, -1], [1, -1], [-1, 0], [1, 0], [-1, 1], [0, 1], [1, 1]];
  const key = (c, r) => c + ',' + r;
  const ITEM = id => (PP.ITEM && PP.ITEM[id]) || null;

  function normRegion(reg) {
    if (!reg || ![reg.c1, reg.r1, reg.c2, reg.r2].every(v => isFinite(v))) return null;
    return { c1: Math.min(reg.c1, reg.c2), c2: Math.max(reg.c1, reg.c2), r1: Math.min(reg.r1, reg.r2), r2: Math.max(reg.r1, reg.r2) };
  }
  const inRegion = (reg, c, r) => !!reg && c >= reg.c1 && c <= reg.c2 && r >= reg.r1 && r <= reg.r2;

  // cell: { c, r, terrain: field|forest|mountain|water|city, res: [crop|ore|fruit], bld, name }
  // (legacy { kind } cells of v13 are accepted too). A building implies its terrain (Farm ⇒ Empty with Crop …).
  function normCell(x) {
    let t = x.terrain, bld = x.bld || null;
    if (x.kind) {
      if (x.kind === 'city') t = 'city';
      else if (x.kind === 'free') t = 'field';
      else if (x.kind === 'blocked') t = 'water';
      else if (BLDS.indexOf(x.kind) >= 0) bld = x.kind;
    }
    if (x.city) t = 'city';
    if (TERR.indexOf(t) < 0) t = t ? 'water' : 'field';
    if (t === 'city') bld = null;
    if (bld && BLDS.indexOf(bld) < 0) bld = 'other';
    if (bld && BASE[bld]) t = BASE[bld];
    const res = (Array.isArray(x.res) ? x.res : []).map(q => (q === 'metal' ? 'ore' : q));
    const o = {
      c: +x.c, r: +x.r, t, bld,
      crop: t === 'field' && (res.indexOf('crop') >= 0 || bld === 'farm'),
      ore: t === 'mountain' && (res.indexOf('ore') >= 0 || bld === 'mine'),
      fruit: t === 'field' && res.indexOf('fruit') >= 0 && res.indexOf('crop') < 0 && bld !== 'farm',
      animal: t === 'forest' && res.indexOf('animal') >= 0 && bld !== 'lumber',
      fish: t === 'water' && res.indexOf('fish') >= 0,
    };
    if (t === 'city' && x.name) o.name = String(x.name);
    if (t !== 'city' && x.own != null) o.own = String(x.own);
    return o;
  }
  // v36 tech limits (only set by the tech advisor): market = new Markets (Trade), farm / mine / lumber = new producers
  const TECH_KEYS = ['market', 'farm', 'mine', 'lumber'];
  function normOpts(opts) {
    const o = {};
    for (const k of OPT_KEYS.concat(WS_KEYS, RES_KEYS, TECH_KEYS)) o[k] = !(opts && opts[k] === false);
    return o;
  }
  function costs(opts) {
    const out = {};
    for (const T of Object.keys(DEF_COST)) {
      const oc = opts && opts.costs && opts.costs[T], it = ITEM(T);
      out[T] = isFinite(oc) ? +oc : T !== 'destroy' && it && isFinite(it.cost) ? it.cost : DEF_COST[T];
    }
    return out;
  }
  // terrain path of a tile (building ignored) → list of actions, or null if impossible
  // Market / Windmill / Forge / Sawmill go on a field – also on one with Crop (built right on it); Fruit is harvested first
  // (Organization; without it the tile stays blocked). An Animal doesn't block a forest: Lumber Hut, Clear and Burn
  // work on it, but the animal is lost – so with Hunting it is hunted first (2 ★, +1 population), without Hunting the
  // forest is used as it is.
  const hunted = (x, o, p) => (!p ? null : x.animal && o.hunt !== false ? ['hunt'].concat(p) : p);
  function fieldPath(x, o) {
    if (x.t === 'field') return !x.fruit ? [] : o.fruit === false ? null : ['fruit'];
    if (x.t === 'forest') return hunted(x, o, o.clear ? ['clear'] : null);
    return null;
  }
  function prodPath(x, X, o) {
    if (o && o[X] === false) return null; // tech not there (Farming / Mining / Forestry)
    if (X === 'farm') {
      if (x.t === 'field') return x.crop ? ['farm'] : o.grow && o.burn ? ['plant', 'burn', 'farm'] : null;
      if (x.t === 'forest') return hunted(x, o, o.burn ? ['burn', 'farm'] : null);
      return null;
    }
    if (X === 'lumber') {
      if (x.t === 'forest') return hunted(x, o, ['lumber']);
      if (x.t === 'field') return o.grow ? ['plant', 'lumber'] : null;
      return null;
    }
    if (X === 'mine') return x.t === 'mountain' && x.ore ? ['mine'] : null;
    return null;
  }
  // nearest city of a tile: Chebyshev distance (≤ max), then Euclid, then first city
  function nearestCity(x, cities, max) {
    let best = -1, bd = 0, be = 0;
    cities.forEach((ci, k) => {
      const dc = Math.abs(x.c - ci.c), dr = Math.abs(x.r - ci.r), d = Math.max(dc, dr), e = dc * dc + dr * dr;
      if (d > max) return;
      if (best < 0 || d < bd || (d === bd && e < be)) { best = k; bd = d; be = e; }
    });
    return best;
  }

  function prepare(cellsIn, opts) {
    const o = normOpts(opts), C = costs(opts);
    const cells = cellsIn.map(normCell), n = cells.length;
    const idx = new Map(cells.map((x, i) => [key(x.c, x.r), i]));
    const nb = cells.map(x => NB.map(([dc, dr]) => idx.get(key(x.c + dc, x.r + dr))).filter(i => i !== undefined));
    const cIdx = [];
    cells.forEach((x, i) => { if (x.t === 'city') cIdx.push(i); });
    const implicit = !cIdx.length;
    const cities = implicit ? [{ i: -1, c: null, r: null, name: null, implicit: true }]
      : cIdx.map(i => ({ i, c: cells[i].c, r: cells[i].r, name: cells[i].name || null, implicit: false }));
    const cKeys = cIdx.map(i => key(cells[i].c, cells[i].r));
    // explicit territory (cell.own = city key) or nearest city within RANGE
    const owner = cells.map((x, i) => (implicit ? 0 : x.t === 'city' ? cIdx.indexOf(i) : x.own != null ? cKeys.indexOf(x.own) : nearestCity(x, cities, RANGE)));
    const home = owner.map((w, i) => (w >= 0 ? w : implicit ? 0 : nearestCity(cells[i], cities, 1e9)));
    const canAct = cells.map((x, i) => owner[i] >= 0 && x.t !== 'city');
    const dOK = canAct.map(a => a && o.destroy);
    const seq = steps => { let cost = 0; for (const s of steps) cost += C[s]; return { steps, cost, act: steps.length }; };
    const pField = cells.map((x, i) => { if (!canAct[i]) return null; const p = fieldPath(x, o); return p ? seq(p) : null; });
    const pProd = cells.map((x, i) => {
      const m = {};
      for (const X of PRODS) { const p = canAct[i] && o.produce ? prodPath(x, X, o) : null; m[X] = p ? seq(p) : null; }
      return m;
    });
    const isUniq = i => UNIQUE.indexOf(cells[i].bld) >= 0;
    // can tile i end up as producer X (existing or built; a unique building there is freed by its own slot)
    const canProd = cells.map((x, i) => {
      const m = {};
      for (const X of PRODS) m[X] = x.bld === X || (!!pProd[i][X] && (!x.bld || dOK[i]));
      return m;
    });
    const terrTiles = cities.map(() => []);
    cells.forEach((x, i) => { if (canAct[i]) terrTiles[owner[i]].push(i); });
    const E = cities.map(() => ({ market: [], windmill: [], forge: [], sawmill: [] }));
    const fixedU = []; // unique buildings outside every territory: stay as they are
    cells.forEach((x, i) => {
      if (!isUniq(i)) return;
      if (owner[i] >= 0) E[owner[i]][x.bld].push(i); else fixedU.push({ i, T: x.bld });
    });
    const potLevel = (x, T) => { let k = 0; for (const t of nb[x]) if (canProd[t][PROD[T]]) k++; return k; };
    return { o, C, cells, n, idx, nb, cities, implicit, owner, home, canAct, dOK, pField, pProd, canProd, terrTiles, E, fixedU, isUniq, potLevel };
  }

  // ======================================================================== exact search
  // Decision model: per city one "slot" per unique type (Market, Windmill, Forge, Sawmill): keep what exists, destroy
  // it, or build a new one on a tile of its territory (destroying the old one). Then every tile next to a workshop
  // may become a Farm / Mine / Lumber Hut (with Burn / Grow / Destroy as needed).
  //  outer: all Market combinations (one option per city), sorted by an upper bound;
  //  inner: depth-first over the Windmill / Forge / Sawmill slots with branch & bound;
  //  leaf : exact DP over the producer tiles with the capped Market sums as state.
  // Bound: per Market, every slot may pick its best tile and level independently; a level costs the cheapest producer
  // tiles around the workshop (cost shared by the workshops of that type that could touch it), a workshop's cost is
  // shared by the Markets next to it. This never overestimates the income or underestimates the cost.
  // Objective: V = min(income, incCap)·HUGE − w, w = cost·BIG + actions (mode 'steps': actions·BIG + cost).
  function makeSearch(P, sopts) {
    const mode = sopts.mode || 'cost', incCap = sopts.incCap == null ? Infinity : sopts.incCap;
    // v29: weight of one ★/turn (default: income first). With incW = λ (w units per ★/turn) the search maximises
    // λ·income − w – a positive value means a better payback than λ (Dinkelbach, used for the fastest payback)
    const IW = sopts.incW || HUGE;
    const { C, cells, n, nb, cities, owner, dOK, pField, pProd, canProd, terrTiles, E, fixedU } = P;
    const K = cities.length;
    const wOf = (cost, act) => (mode === 'steps' ? act * BIG + cost : cost * BIG + act);
    const wPath = p => wOf(p.cost, p.act);
    const wD = wOf(C.destroy, 1);
    const fixedTiles = fixedU.map(f => f.i);
    const fixedMk = fixedU.filter(f => f.T === 'market').map(f => f.i);
    const fixedProc = fixedU.filter(f => f.T !== 'market');
    let best = sopts.init ? sopts.init : null, bestV = best ? best.V : -Infinity;
    const stats = { combos: 0, nodes: 0, leaves: 0 };

    // market options per city
    const adjCanProcAny = x => nb[x].some(y => {
      // y could hold a workshop with some level: existing (any city / fixed) or new
      const b = cells[y].bld;
      for (const T of WS) {
        if (P.potLevel(y, T) === 0) continue;
        if (b === T) return true;
        if (P.o[T] && P.canAct[y] && pField[y] && (!b || dOK[y])) return true;
      }
      return false;
    });
    const mOpts = cities.map((ci, k) => {
      const Ek = E[k].market, list = [{ kind: 'keep', tiles: Ek, frees: [], w: 0, cost: 0, act: 0, k, T: 'market' }];
      const allD = Ek.every(i => dOK[i]);
      if (Ek.length && allD) list.push({ kind: 'destroy', tiles: [], frees: Ek, w: Ek.length * wD, cost: Ek.length * C.destroy, act: Ek.length, k, T: 'market' });
      if (!allD || !P.o.market) return list; // no Trade → only the Markets that exist
      for (const x of terrTiles[k]) {
        if (Ek.indexOf(x) >= 0 || !pField[x]) continue;
        const b = cells[x].bld;
        if (b && !dOK[x]) continue;
        if (!adjCanProcAny(x)) continue;
        const extra = b && !P.isUniq(x) ? 1 : 0;
        const cost = (Ek.length + extra) * C.destroy + pField[x].cost + C.market, act = Ek.length + extra + pField[x].act + 1;
        list.push({ kind: 'new', x, tiles: [x], frees: Ek, w: wOf(cost, act), cost, act, k, T: 'market' });
      }
      return list;
    });

    // ---------------------------------------------------------------- per market combination
    const sCnt = { windmill: new Int16Array(n), forge: new Int16Array(n), sawmill: new Int16Array(n) };
    const stamp = new Int32Array(n); let stampN = 0;
    function buildCombo(mSel) {
      const mt = [], occ0 = new Set(fixedTiles);
      let mW = 0;
      for (const o of mSel) { mW += o.w; for (const x of o.tiles) { mt.push(x); occ0.add(x); } }
      for (const x of fixedMk) mt.push(x);
      const J = mt.length;
      const mAdj = new Map();
      mt.forEach((m, j) => { for (const y of nb[m]) { const a = mAdj.get(y); if (a) a.push(j); else mAdj.set(y, [j]); } });
      const stages = [];
      for (let k = 0; k < K; k++) for (const T of WS) {
        const Ek = E[k][T], list = [], allD = Ek.every(i => dOK[i]);
        if (!Ek.some(i => occ0.has(i))) list.push({ kind: 'keep', tiles: Ek, frees: [], w: 0, cost: 0, act: 0 });
        if (Ek.length && allD) list.push({ kind: 'destroy', tiles: [], frees: Ek, w: Ek.length * wD, cost: Ek.length * C.destroy, act: Ek.length });
        if (allD && P.o[T]) {
          for (const x of terrTiles[k]) {
            if (!mAdj.has(x) || occ0.has(x) || Ek.indexOf(x) >= 0 || !pField[x]) continue;
            const b = cells[x].bld;
            if (b && !dOK[x]) continue;
            if (P.potLevel(x, T) === 0) continue;
            const extra = b && !P.isUniq(x) ? 1 : 0;
            const cost = (Ek.length + extra) * C.destroy + pField[x].cost + C[T], act = Ek.length + extra + pField[x].act + 1;
            list.push({ kind: 'new', x, tiles: [x], frees: Ek, w: wOf(cost, act), cost, act });
          }
        }
        if (!list.length) return null;
        stages.push({ k, T, opts: list });
      }
      for (const f of fixedProc) stages.push({ k: -1, T: f.T, opts: [{ kind: 'fixed', tiles: [f.i], frees: [], w: 0, cost: 0, act: 0 }] });
      // sharing count s(t,T): workshop slots of type T that could touch t
      for (const T of WS) sCnt[T].fill(0);
      for (const st of stages) {
        stampN++;
        for (const o of st.opts) for (const y of o.tiles) for (const t of nb[y]) if (stamp[t] !== stampN) { stamp[t] = stampN; sCnt[st.T][t]++; }
      }
      // per option: markets touched and level curves per market
      for (const st of stages) {
        const X = PROD[st.T], sc = sCnt[st.T];
        for (const o of st.opts) {
          const tm = new Set();
          o.curves = new Map(); // j → Float64Array(9)
          o.maxL = 0;
          const tileCurves = [];
          for (const y of o.tiles) {
            const units = [];
            for (const t of nb[y]) {
              if (occ0.has(t) || !canProd[t][X]) continue;
              let u = 0;
              if (cells[t].bld !== X) u = wPath(pProd[t][X]) + (cells[t].bld && !P.isUniq(t) ? wD : 0);
              units.push(u / Math.max(1, sc[t]));
            }
            units.sort((a, b) => a - b);
            const L = Math.min(CAP, units.length), S = new Float64Array(L + 1);
            for (let q = 1; q <= L; q++) S[q] = S[q - 1] + units[q - 1];
            const A = mAdj.get(y) || [];
            A.forEach(j => tm.add(j));
            tileCurves.push({ y, S, A });
            o.maxL += L;
          }
          o.A = [...tm];
          for (const j of o.A) {
            let cur = new Float64Array(CAP + 1).fill(Infinity); cur[0] = 0;
            for (const tc of tileCurves) {
              if (tc.A.indexOf(j) < 0) continue;
              const nx = new Float64Array(CAP + 1).fill(Infinity);
              for (let a = 0; a <= CAP; a++) {
                if (cur[a] === Infinity) continue;
                for (let L = 0; L < tc.S.length; L++) {
                  const b = Math.min(CAP, a + L), v = cur[a] + tc.S[L] / tc.A.length;
                  if (v < nx[b]) nx[b] = v;
                }
              }
              cur = nx;
            }
            o.curves.set(j, cur);
          }
        }
        // undecided stage per market: g[j][L] = min over options (w/|A| + curve)
        st.g = [];
        for (let j = 0; j < J; j++) {
          const g = new Float64Array(CAP + 1).fill(Infinity); g[0] = 0;
          for (const o of st.opts) {
            const cv = o.curves.get(j); if (!cv) continue;
            const share = o.w / o.A.length;
            for (let L = 1; L <= CAP; L++) if (cv[L] + share < g[L]) g[L] = cv[L] + share;
          }
          st.g.push(g);
        }
        st.relevant = st.g.some(g => g.some((v, L) => L > 0 && v < Infinity));
        st.opts.sort((a, b) => (b.maxL * b.A.length - a.maxL * a.A.length) || (a.w - b.w));
      }
      stages.sort((a, b) => a.opts.length - b.opts.length);
      const cb = { mSel, mt, J, mW, occ0, stages };
      suffixTables(cb);
      return cb;
    }

    // capped min-plus convolution: out[min(8, a+b)] = min(x[a] + y[b])
    function conv(x, y, out) {
      out.fill(Infinity);
      for (let a = 0; a <= CAP; a++) {
        const xa = x[a]; if (xa === Infinity) continue;
        for (let L = 0; L <= CAP; L++) {
          const yl = y[L]; if (yl === Infinity) continue;
          const b = a + L > CAP ? CAP : a + L, v = xa + yl;
          if (v < out[b]) out[b] = v;
        }
      }
      return out;
    }
    const ZERO = new Float64Array(CAP + 1).fill(Infinity); ZERO[0] = 0;
    // suffix tables: U[j][d] = best levels at market j from the undecided stages d..end
    function suffixTables(cb) {
      const { J, stages } = cb, S = stages.length;
      cb.U = [];
      for (let j = 0; j < J; j++) {
        const U = new Array(S + 1);
        U[S] = ZERO;
        for (let d = S - 1; d >= 0; d--) U[d] = stages[d].relevant ? conv(U[d + 1], stages[d].g[j], new Float64Array(CAP + 1)) : U[d + 1];
        cb.U.push(U);
      }
    }
    // upper bound of V: dec[j] = levels at market j from the decided stages 0..d-1 (their own cost in fixedW)
    const tmp9 = new Float64Array(CAP + 1);
    function bound(cb, dec, d, fixedW) {
      const J = cb.J;
      let tot = [0];
      for (let j = 0; j < J; j++) {
        const f = conv(dec[j], cb.U[j][d], tmp9);
        const nt = new Array(tot.length + CAP).fill(Infinity);
        for (let a = 0; a < tot.length; a++) {
          if (tot[a] === Infinity) continue;
          for (let b = 0; b <= CAP; b++) { const v = tot[a] + f[b]; if (v < nt[a + b]) nt[a + b] = v; }
        }
        tot = nt;
      }
      let ub = -Infinity;
      for (let I = 0; I < tot.length; I++) {
        if (tot[I] === Infinity) continue;
        const v = Math.min(I, incCap) * IW - fixedW - tot[I];
        if (v > ub) ub = v;
      }
      return ub;
    }

    // exact producer DP for a full layout; returns { V, prods } or null when it can't beat bestV
    function leaf(cb, chosen, fixedW, track) {
      stats.leaves++;
      const { mt, J, stages } = cb;
      const occ = new Set(cb.occ0), freed = new Set();
      for (const o of cb.mSel) o.frees.forEach(x => freed.add(x));
      const procs = [];
      for (let s = 0; s < stages.length; s++) {
        const o = chosen[s];
        o.frees.forEach(x => freed.add(x));
        for (const x of o.tiles) { occ.add(x); procs.push({ x, T: stages[s].T }); }
      }
      const mIdx = new Map(mt.map((m, j) => [m, j]));
      // per tile: contribution vectors per producer type
      const contrib = new Map();
      for (const p of procs) {
        const js = [];
        for (const y of nb[p.x]) { const j = mIdx.get(y); if (j !== undefined) js.push(j); }
        if (!js.length) continue;
        const X = PROD[p.T];
        for (const t of nb[p.x]) {
          if (occ.has(t)) continue;
          let e = contrib.get(t);
          if (!e) { e = {}; contrib.set(t, e); }
          const v = e[X] || (e[X] = new Array(J).fill(0));
          for (const j of js) v[j]++;
        }
      }
      const tilesL = [];
      for (const [t, e] of contrib) {
        const bEff = freed.has(t) ? null : cells[t].bld;
        const options = [];
        const keepV = bEff && e[bEff] ? e[bEff] : null;
        options.push({ X: null, v: keepV, w: 0 });
        for (const X of PRODS) {
          if (!e[X] || X === bEff || !pProd[t][X]) continue;
          if (bEff && !dOK[t]) continue;
          options.push({ X, v: e[X], w: wPath(pProd[t][X]) + (bEff ? wD : 0) });
        }
        if (options.length === 1 && !keepV) continue;
        tilesL.push({ t, options });
      }
      // remaining max per market (for pruning)
      const m = tilesL.length, rem = [];
      let acc = new Array(J).fill(0);
      rem[m] = acc.slice();
      for (let q = m - 1; q >= 0; q--) {
        for (let j = 0; j < J; j++) { let mx = 0; for (const op of tilesL[q].options) if (op.v && op.v[j] > mx) mx = op.v[j]; acc[j] += mx; }
        rem[q] = acc.slice();
      }
      const enc = s => { let h = 0; for (let j = 0; j < J; j++) h = h * 9 + s[j]; return h; };
      const ubOf = (s, q, w) => { let inc = 0; for (let j = 0; j < J; j++) inc += Math.min(CAP, s[j] + rem[q][j]); return Math.min(inc, incCap) * IW - fixedW - w; };
      let states = new Map([[0, { s: new Array(J).fill(0), w: 0, from: null, op: null }]]);
      const hist = track ? [] : null;
      for (let q = 0; q < m; q++) {
        const next = new Map();
        for (const st of states.values()) {
          for (const op of tilesL[q].options) {
            const s = st.s.slice();
            if (op.v) for (let j = 0; j < J; j++) if (op.v[j]) s[j] = Math.min(CAP, s[j] + op.v[j]);
            const w = st.w + op.w;
            if (ubOf(s, q + 1, w) <= bestV + 0.5) continue;
            const h = enc(s), cur = next.get(h);
            if (!cur || w < cur.w) next.set(h, { s, w, from: st, op });
          }
        }
        states = next;
        if (!states.size) return null;
      }
      let bst = null, bv = -Infinity;
      for (const st of states.values()) {
        let inc = 0; for (let j = 0; j < J; j++) inc += st.s[j];
        const V = Math.min(inc, incCap) * IW - fixedW - st.w;
        if (V > bv) { bv = V; bst = st; }
      }
      if (!bst || bv <= bestV + 0.5) return null;
      const prods = [];
      for (let st = bst, q = m - 1; st && st.op; st = st.from, q--) if (st.op.X) prods.push({ t: tilesL[q].t, X: st.op.X });
      return { V: bv, prods };
    }

    function searchCombo(cb) {
      const { stages, J } = cb, S = stages.length, chosen = new Array(S);
      const occ = new Set(cb.occ0);
      const dec = [];
      for (let d = 0; d <= S; d++) { const l = []; for (let j = 0; j < J; j++) l.push(d ? new Float64Array(CAP + 1) : ZERO); dec.push(l); }
      (function rec(d, fixedW) {
        stats.nodes++;
        if (bound(cb, dec[d], d, fixedW) <= bestV + 0.5) return;
        if (d === S) {
          const r = leaf(cb, chosen, fixedW);
          if (r) { bestV = r.V; best = { V: r.V, mSel: cb.mSel.slice(), stages: stages.map((s, i) => ({ k: s.k, T: s.T, o: chosen[i] })), prods: r.prods }; }
          return;
        }
        for (const o of stages[d].opts) {
          if (o.kind !== 'fixed' && o.tiles.some(x => occ.has(x))) continue;
          o.tiles.forEach(x => occ.add(x));
          chosen[d] = o;
          for (let j = 0; j < J; j++) { const cv = o.curves.get(j); if (cv) conv(dec[d][j], cv, dec[d + 1][j]); else dec[d + 1][j].set(dec[d][j]); }
          rec(d + 1, fixedW + o.w);
          o.tiles.forEach(x => occ.delete(x));
        }
        chosen[d] = undefined;
      })(0, cb.mW);
    }

    // ---------------------------------------------------------------- driver (resumable)
    const sizes = mOpts.map(l => l.length);
    let total = 1; for (const s of sizes) total *= s;
    const list = [];
    let phase = 0, ci = 0, li = 0;
    function comboAt(z) { const sel = []; for (let k = 0; k < K; k++) { sel.push(mOpts[k][z % sizes[k]]); z = Math.floor(z / sizes[k]); } return sel; }
    return {
      stats, total,
      get best() { return best; },
      step(deadline) {
        while (true) {
          if (phase === 0) {
            if (ci >= total) { list.sort((a, b) => b.ub - a.ub); phase = 1; continue; }
            const cb = buildCombo(comboAt(ci++));
            stats.combos++;
            if (cb) { const ub = bound(cb, cb.U.map(() => ZERO), 0, cb.mW); if (ub > -Infinity) list.push({ ub, cb }); }
          } else {
            if (li >= list.length || list[li].ub <= bestV + 0.5) { list.length = 0; return true; }
            searchCombo(list[li++].cb);
          }
          if ((stats.combos & 15) === 0 && Date.now() > deadline) return false;
          if (phase === 1 && Date.now() > deadline) return false;
        }
      },
    };
  }

  // ======================================================================== plan object
  function materialize(P, d, tag) {
    const { cells, nb, C, home, owner } = P;
    const fin = cells.map(x => x.bld), why = cells.map(() => null);
    const stepsAt = cells.map(() => []);
    const isNew = cells.map(() => false);
    const destroyed = new Set();
    const place = (x, T) => {
      const b = cells[x].bld;
      if (b && b !== T) destroyed.add(x);
      fin[x] = T; isNew[x] = true;
      stepsAt[x].push(...P.pField[x].steps, T);
    };
    const all = d.mSel.map(o => ({ T: 'market', o })).concat(d.stages.filter(s => s.k >= 0).map(s => ({ T: s.T, o: s.o })));
    for (const { o } of all) for (const x of o.frees) { destroyed.add(x); if (fin[x] === cells[x].bld) fin[x] = null; }
    for (const { T, o } of all) if (o.kind === 'new') place(o.x, T);
    for (const p of d.prods) {
      const b = fin[p.t];
      if (b && b !== p.X) destroyed.add(p.t);
      fin[p.t] = p.X; isNew[p.t] = true;
      stepsAt[p.t].push(...P.pProd[p.t][p.X].steps);
    }
    destroyed.forEach(x => stepsAt[x].unshift('destroy'));
    // incomes from the final layout (independent recomputation)
    const at = i => ({ c: cells[i].c, r: cells[i].r });
    const level = i => { const X = PROD[fin[i]]; let k = 0; for (const t of nb[i]) if (fin[t] === X) k++; return k; };
    const ws = [], markets = [];
    cells.forEach((x, i) => {
      if (PROD[fin[i]]) ws.push(Object.assign(at(i), { i, item: fin[i], isNew: isNew[i], level: level(i), city: home[i], feeds: [],
        producers: nb[i].filter(t => fin[t] === PROD[fin[i]]).map(t => Object.assign(at(t), { item: fin[t], isNew: isNew[t] })) }));
    });
    cells.forEach((x, i) => {
      if (fin[i] !== 'market') return;
      const feeders = ws.filter(w => nb[i].indexOf(w.i) >= 0);
      let raw = 0; feeders.forEach(w => { raw += w.level; });
      markets.push(Object.assign(at(i), { i, item: 'market', isNew: isNew[i], city: home[i], raw, income: Math.min(CAP, raw), capped: raw > CAP,
        feeders: feeders.map(w => ({ c: w.c, r: w.r, item: w.item, level: w.level, city: w.city })) }));
    });
    markets.forEach((m, mi) => m.feeders.forEach(f => { const w = ws.find(q => q.c === f.c && q.r === f.r); if (w) w.feeds.push(mi); }));
    let income = 0; markets.forEach(m => { income += m.income; });
    // ordered steps
    const steps = [];
    cells.forEach((x, i) => stepsAt[i].forEach((item, q) => steps.push({ i, c: x.c, r: x.r, item, q, cost: C[item], city: home[i],
      what: item === 'destroy' ? cells[i].bld : null })));
    steps.sort((a, b) => PHASE[a.item] - PHASE[b.item] || a.city - b.city || a.r - b.r || a.c - b.c || a.q - b.q);
    steps.forEach((s, k) => { s.no = k + 1; });
    let cost = 0; steps.forEach(s => { cost += s.cost; });
    const tiles = [];
    cells.forEach((x, i) => { if (stepsAt[i].length) tiles.push(Object.assign(at(i), { item: fin[i], from: cells[i].bld, city: home[i], steps: steps.filter(s => s.i === i) })); });
    const used = ws.filter(w => w.feeds.length || w.isNew);
    const groups = P.cities.map((ci, k) => {
      const g = { k, city: { c: ci.c, r: ci.r, name: ci.name, implicit: ci.implicit }, markets: markets.filter(m => m.city === k), workshops: used.filter(w => w.city === k), steps: steps.filter(s => s.city === k) };
      g.income = 0; g.markets.forEach(m => { g.income += m.income; });
      g.cost = 0; g.steps.forEach(s => { g.cost += s.cost; });
      return g;
    });
    ws.forEach(w => { delete w.i; }); markets.forEach(m => { delete m.i; });
    return {
      tag, income, cost, actions: steps.length, steps, tiles, markets, workshops: used, groups,
      marketCount: markets.filter(m => m.income > 0).length, capped: markets.some(m => m.capped),
      buildings: used.concat(markets), n: steps.length,
      payback: income > 0 && cost > 0 ? Math.ceil(cost / income) : null,
      final: fin.map((b, i) => (b ? { c: cells[i].c, r: cells[i].r, bld: b } : null)).filter(Boolean),
      ownerOk: steps.every(s => owner[s.i] >= 0),
    };
  }

  // full optimization as a resumable job: best plan first (job.partial), then alternatives (fewer steps, cheaper)
  function createJob(cellsIn, opts) {
    const t0 = Date.now(), P = prepare(cellsIn || [], opts);
    const st = { combos: 0, nodes: 0, leaves: 0 };
    const add = s => { st.combos += s.combos; st.nodes += s.nodes; st.leaves += s.leaves; };
    const altBudget = opts && opts.altMs != null ? opts.altMs : 5000;
    const alts = !(opts && opts.alts === false);
    let phase = 0, cur = makeSearch(P, { mode: 'cost', incW: opts && opts.incW }), bestD = null, bestP = null, I0 = 0, frontier = [], fewD = null, tAlt = 0, Ilev = 0, msBest = 0;
    const job = { P, done: false, result: null, partial: null, combos: cur.total };
    // ms until the alternatives are done (they get at most altBudget after the best plan) – null before that
    job.eta = () => (job.done ? 0 : tAlt ? Math.max(0, tAlt + altBudget - Date.now()) : null);
    const half = () => Math.ceil(I0 / 2);
    const cheaperFound = () => frontier.some(d => !d.inherited);
    const mkResult = altList => ({
      best: bestP, alts: altList, ms: Date.now() - t0, msBest, stats: Object.assign({}, st), opts: P.o,
      cells: P.cells, owner: P.owner, cities: P.cities.map(ci => ({ c: ci.c, r: ci.r, name: ci.name, implicit: ci.implicit })),
    });
    job.step = function (deadline) {
      while (!job.done) {
        const fin = cur ? cur.step(deadline) : true;
        if (!fin) return false;
        if (cur) add(cur.stats);
        if (phase === 0) {
          bestD = cur.best;
          // income of the best (V = I·HUGE − w with 0 ≤ w < HUGE)
          if (opts && opts.incW) { bestP = bestD ? materialize(P, bestD, 'best') : null; I0 = bestP ? bestP.income : 0; if (!I0) bestP = null; }
          else { I0 = bestD ? Math.ceil(bestD.V / HUGE) : 0; bestP = bestD && I0 > 0 ? materialize(P, bestD, 'best') : null; }
          job.bestDecision = bestD;
          msBest = Date.now() - t0;
          job.partial = mkResult([]);
          tAlt = Date.now();
          if (!alts || !bestP || !bestP.actions) { phase = 9; cur = null; continue; }
          phase = 1; cur = makeSearch(P, { mode: 'steps', incCap: I0 });
        } else if (phase === 1) {
          fewD = cur.best;
          phase = 2; Ilev = I0 - 1; cur = null;
        } else if (phase === 2) {
          if (cur && cur.best) frontier.push(cur.best);
          // levels down to half the best income; further down only while nothing cheaper turned up
          // v29: all levels down to 1 ★ (the fastest payback can be a small plan), within the time budget
          if (Ilev < 1 || Date.now() - tAlt > altBudget) { phase = 9; cur = null; continue; }
          const prev = frontier.length ? frontier[frontier.length - 1] : bestD;
          // incumbent: the plan one level up still reaches Ilev
          const pv = prev.V - Math.ceil(prev.V / HUGE) * HUGE + Ilev * HUGE;
          cur = makeSearch(P, { mode: 'cost', incCap: Ilev, init: { V: pv, mSel: prev.mSel, stages: prev.stages, prods: prev.prods, inherited: true } });
          Ilev--;
        } else {
          job.done = true;
          const alt = [];
          if (bestP && fewD) {
            const f = materialize(P, fewD, 'fewer');
            if (f.actions < bestP.actions && f.income === bestP.income) alt.push(f);
          }
          if (bestP) {
            // cheaper: Pareto plans of lower income – the best payback (at least half the income if possible)
            const ch = [];
            let minCost = bestP.cost;
            for (const d of frontier) {
              if (d.inherited) continue;
              const p = materialize(P, d, 'cheaper');
              if (p.income > 0 && p.cost < minCost) { ch.push(p); minCost = p.cost; }
            }
            const pool = ch.some(p => p.income >= half()) ? ch.filter(p => p.income >= half()) : ch;
            pool.sort((a, b) => a.cost / a.income - b.cost / b.income || b.income - a.income);
            if (pool[0]) alt.push(pool[0]);
            // v29: fastest payback over every income level (cost ÷ ★ per turn; ties: more ★)
            // whole turns as shown; ties → more ★ per turn
            const fast = ch.concat([bestP]).filter(q => q.payback != null).sort((a, b) => a.payback - b.payback || b.income - a.income)[0];
            if (fast && fast !== bestP && fast.payback != null && bestP.payback != null && fast.payback < bestP.payback) {
              const dup = alt.find(q => q.income === fast.income && q.cost === fast.cost);
              if (dup) dup.tag = 'fast'; else alt.push(Object.assign(fast, { tag: 'fast' }));
            }
          }
          job.result = mkResult(alt);
          return true;
        }
      }
      return true;
    };
    return job;
  }
  // one exact search (tests): mode 'cost' | 'steps', incCap = income that is enough
  function solveOnce(cellsIn, opts, sopts) {
    const P = prepare(cellsIn || [], opts), s = makeSearch(P, sopts || {});
    s.step(Infinity);
    return s.best ? materialize(P, s.best, 'best') : null;
  }
  function optimize(cellsIn, opts) { const j = createJob(cellsIn, opts); j.step(Infinity); return j.result; }

  // income of a finished layout: cells with { terrain, bld } – independent check for the tests
  function incomeOf(cellsIn) {
    const P = prepare(cellsIn, {});
    let total = 0;
    P.cells.forEach((x, i) => {
      if (x.bld !== 'market') return;
      let raw = 0;
      for (const j of P.nb[i]) { const T = P.cells[j].bld; if (PROD[T]) for (const t of P.nb[j]) if (P.cells[t].bld === PROD[T]) raw++; }
      total += Math.min(CAP, raw);
    });
    return total;
  }
  function territory(cellsIn) {
    const P = prepare(cellsIn, {});
    return { owner: P.owner, cities: P.cities, cells: P.cells, implicit: P.implicit };
  }

  // ======================================================================== large search (any number of cities)
  // The exact search multiplies the Market options of all cities – with many cities that is far too much. Here the
  // cities are re-planned in small groups, each group EXACTLY: the group's territories plus everything within 4 tiles
  // are cut out, the other cities in there are frozen in their currently planned state (as existing buildings), and
  // that small board is solved by the exact search. The result goes back into the global plan if the whole plan gets
  // better (more ★, or as many ★ for less). Groups: every single city, every pair and every triple of neighbouring
  // cities (territories ≤ 2 tiles apart) – again and again until nothing improves. The best plan so far is always
  // available (job.partial; job.version counts improvements). Proven optimal when every possible Market has 8 ★.
  function createLargeJob(cellsIn, opts) {
    const t0 = Date.now(), P = prepare(cellsIn || [], opts), K = P.cities.length, raw = (cellsIn || []).map(normCell);
    const budget = opts && opts.largeMs != null ? opts.largeMs : 3000, perWin = opts && opts.winMs != null ? opts.winMs : 3000;
    const st = { combos: 0, nodes: 0, leaves: 0, windows: 0, improved: 0, skipped: 0 };
    const { cells, idx, E } = P;
    const cheb = (a, b) => Math.max(Math.abs(a.c - b.c), Math.abs(a.r - b.r));
    const tilesOf = P.cities.map((ci, k) => P.terrTiles[k].concat(ci.i >= 0 ? [ci.i] : []));
    const adj = P.cities.map((_, a) => P.cities.map((__, b) => a !== b && tilesOf[a].some(x => tilesOf[b].some(y => cheb(cells[x], cells[y]) <= 2))));
    const groups = [[], [], []];
    for (let a = 0; a < K; a++) groups[0].push([a]);
    for (let a = 0; a < K; a++) for (let b = a + 1; b < K; b++) if (adj[a][b]) groups[1].push([a, b]);
    for (let a = 0; a < K; a++) for (let b = a + 1; b < K; b++) for (let c = b + 1; c < K; c++)
      if ((adj[a][b] ? 1 : 0) + (adj[a][c] ? 1 : 0) + (adj[b][c] ? 1 : 0) >= 2) groups[2].push([a, b, c]);
    const fixedMk = P.fixedU.filter(f => f.T === 'market').length, ub = CAP * (K + fixedMk);
    // decisions in the format of the exact search (materialize needs kind / x / tiles / frees)
    const keepOpt = (k, T) => ({ kind: 'keep', tiles: E[k][T].slice(), frees: [] });
    const optOf = (k, T, kind, x) => (kind === 'new' ? { kind, x, tiles: [x], frees: E[k][T].slice() } : kind === 'destroy' ? { kind, tiles: [], frees: E[k][T].slice() } : keepOpt(k, T));
    let cur = { mSel: P.cities.map((_, k) => keepOpt(k, 'market')), stages: [], prods: [] };
    for (let k = 0; k < K; k++) for (const T of WS) cur.stages.push({ k, T, o: keepOpt(k, T) });
    const value = p => (p ? p.income * HUGE - (p.cost * BIG + p.actions) : 0);
    let curP = materialize(P, cur, 'best'), curV = value(curP);
    let level = 0, gi = 0, sub = null, winStart = 0, swept = false, done = false, msBest = 0, complete = true, quickAlts = [];
    const job = { P, done: false, result: null, partial: null, combos: 0, large: true, version: 0 };
    // estimated ms until all four options are there (group search budget + every city alone + the payback search)
    job.eta = () => (job.done ? 0 : (done ? 0 : Math.max(0, t0 + budget - Date.now())) + (quickDone ? 0 : (K - qi) * cityMs + quickMs));
    const mk = () => ({ best: curP && curP.income > 0 ? curP : null, alts: quickAlts.slice(), ms: Date.now() - t0, msBest, stats: Object.assign({}, st), opts: P.o,
      cells: P.cells, owner: P.owner, cities: P.cities.map(ci => ({ c: ci.c, r: ci.r, name: ci.name, implicit: ci.implicit })),
      decision: cur, large: { cities: K, groups: groups.map(g => g.length), optimal: !!curP && curP.income >= ub, complete, ub } });
    job.partial = mk();
    // the small board around a group of cities: group territories as they are, the rest frozen in the current plan
    function subBoard(win, orig, inPlan) {
      const fin = new Map(); (orig ? [] : (inPlan || curP).final || []).forEach(f => fin.set(key(f.c, f.r), f.bld));
      const inWin = i => win.some(k => tilesOf[k].indexOf(i) >= 0);
      const core = []; win.forEach(k => tilesOf[k].forEach(i => core.push(cells[i])));
      const out = [];
      cells.forEach((x, i) => {
        if (!core.some(y => cheb(x, y) <= 4)) return;
        const o = raw[i], ci = win.find(k => P.cities[k].i === i);
        if (ci != null) { out.push({ c: x.c, r: x.r, terrain: 'city', name: o.name }); return; }
        if (inWin(i)) {
          const k = P.owner[i], cc = P.cities[k];
          out.push({ c: x.c, r: x.r, terrain: o.t, res: (o.crop ? ['crop'] : []).concat(o.ore ? ['ore'] : [], o.fruit ? ['fruit'] : [], o.animal ? ['animal'] : [], o.fish ? ['fish'] : []), bld: o.bld, own: key(cc.c, cc.r) });
          return;
        }
        if (o.t === 'city') { out.push({ c: x.c, r: x.r, terrain: 'water', own: '-' }); return; } // another city: blocked
        const b = orig ? o.bld : fin.has(key(x.c, x.r)) ? fin.get(key(x.c, x.r)) : null;
        out.push({ c: x.c, r: x.r, terrain: b && BASE[b] ? BASE[b] : o.t, res: (o.crop ? ['crop'] : []).concat(o.ore ? ['ore'] : [], o.fruit ? ['fruit'] : [], o.animal ? ['animal'] : [], o.fish ? ['fish'] : []), bld: b, own: '-' });
      });
      return out;
    }
    // the exact sub-result → a global decision (cur with the group's choices replaced)
    function merge(win, sj, base) { return mergeD(win, sj.P, sj.bestDecision, base || cur); }
    function mergeD(win, SP, D, base) {
      if (!D) return null;
      const cur = base;
      const g = i => idx.get(key(SP.cells[i].c, SP.cells[i].r));
      const kOf = sk => P.cities.findIndex(ci => ci.c === SP.cities[sk].c && ci.r === SP.cities[sk].r);
      const n = { mSel: cur.mSel.slice(), stages: cur.stages.slice(), prods: [] };
      D.mSel.forEach((o, sk) => { const k = kOf(sk); if (win.indexOf(k) >= 0) n.mSel[k] = optOf(k, 'market', o.kind, o.kind === 'new' ? g(o.x) : null); });
      D.stages.forEach(s => {
        if (s.k < 0) return;
        const k = kOf(s.k); if (win.indexOf(k) < 0) return;
        const at = n.stages.findIndex(q => q.k === k && q.T === s.T);
        n.stages[at] = { k, T: s.T, o: optOf(k, s.T, s.o.kind, s.o.kind === 'new' ? g(s.o.x) : null) };
      });
      const winTile = new Set(); win.forEach(k => P.terrTiles[k].forEach(i => winTile.add(i)));
      n.prods = cur.prods.filter(q => !winTile.has(q.t)).concat(D.prods.map(q => ({ t: g(q.t), X: q.X })).filter(q => q.t != null));
      return n;
    }
    // ---- v29 quick option: every city alone (exact, all income levels) + Dinkelbach group search → fastest payback
    const SCQ = 1000, ratio = p => (p.cost * SCQ + p.actions) / p.income;
    const base0 = { mSel: cur.mSel.slice(), stages: cur.stages.slice(), prods: [] }; // keep everything
    const perCity = []; let qi = 0, quickDone = !!(opts && opts.quick === false), cityMs = 150;
    const quickMs = opts && opts.quickMs != null ? opts.quickMs : 4000;
    // generators: every heavy search runs in slices of ~25 ms, so the page stays responsive
    function* runSearch(SP, so) { const sr = makeSearch(SP, so); while (!sr.step(Date.now() + 25)) yield; return sr.best; }
    function* quickCity(k) {
      const sb = subBoard([k], true), SP = prepare(sb, opts);
      const Db = yield* runSearch(SP, { mode: 'cost' }); if (!Db) return null;
      const pb = materialize(SP, Db, 'x'); if (!(pb.income > 0)) return null;
      let Dr = Db, pr = pb;
      for (let L = pb.income - 1; L >= 1; L--) {
        const D = yield* runSearch(SP, { mode: 'cost', incCap: L }); if (!D) continue;
        const p = materialize(SP, D, 'x'); if (p.income > 0 && ratio(p) < ratio(pr)) { Dr = D; pr = p; }
      }
      return { k, ratio: ratio(pr), SP, raw: { Dr, Db } };
    }
    function combine(list, field) {
      // the chosen per-city decisions on top of "keep everything"
      let d = base0;
      for (const c of list) { const SP = c.SP, D = c.raw[field]; if (D) d = mergeD([c.k], SP, D, d); }
      return d;
    }
    // group search maximising λ·★ − w from a start decision (Dinkelbach step); returns the best plan found
    const wOfP = p => p.cost * BIG + p.actions, rq = p => wOfP(p) / p.income;
    function* groupImprove(D0, p0, lam, until) {
      let D = D0, p = p0, v = lam * p0.income - wOfP(p0), improved = true;
      while (improved && Date.now() < until) {
        improved = false;
        for (const lev of [0, 1, 2]) for (const win of groups[lev]) {
          if (Date.now() > until) return { D, p };
          const j = createJob(subBoard(win, false, p), Object.assign({}, opts, { alts: false, incW: lam }));
          if (j.combos > MAX_COMBOS_EXACT) continue;
          const end = Math.min(until, Date.now() + perWin);
          let fin = false;
          while (!(fin = j.step(Math.min(end, Date.now() + 25))) && Date.now() < end) yield;
          if (!fin) continue;
          const n = mergeD(win, j.P, j.bestDecision, D); if (!n) continue;
          const pn = materialize(P, n, 'fast'), vn = lam * pn.income - wOfP(pn);
          if (pn.income > 0 && vn > v + 0.5) { D = n; p = pn; v = vn; improved = true; }
        }
      }
      return { D, p };
    }
    function* quickGen() {
      for (qi = 0; qi < K; qi++) {
        const tq = Date.now();
        let c = null; try { c = yield* quickCity(qi); } catch (e) { c = null; }
        perCity.push(c); cityMs = (cityMs + (Date.now() - tq)) / 2;
      }
      const best = curP; quickAlts = [];
      if (!best || !(best.income > 0)) return;
      const cands = [best];
      // Dinkelbach over the group search: λ = best ratio so far; a plan with λ·★ − cost > 0 pays back faster
      let D = cur, pl = best, lam = rq(best);
      const until = Date.now() + quickMs;
      for (let it = 0; it < 6 && Date.now() < until; it++) {
        const r = yield* groupImprove(D, pl, lam, until);
        if (r.p === pl || !(rq(r.p) < lam - 1e-9)) break;
        D = r.D; pl = r.p; lam = rq(pl); cands.push(pl);
      }
      const order = perCity.filter(Boolean).sort((a, b) => a.ratio - b.ratio);
      // plus: the cities alone, added in the order of their own payback (catches plans without neighbour synergy)
      for (let n = 1; n <= order.length; n++) {
        const p = materialize(P, combine(order.slice(0, n), 'Dr'), 'fast');
        if (p.income > 0) cands.push(p);
        yield;
      }
      let fast = null;
      for (const p of cands) if (!fast || rq(p) < rq(fast)) fast = p;
      if (fast && rq(best) <= rq(fast)) fast = null;
      if (fast) quickAlts.push(Object.assign(fast, { tag: 'fast', quick: true }));

    }
    let gen = null;
    job.step = function (deadline) {
      while (done && !quickDone) {
        if (!gen) gen = quickGen();
        let r; try { r = gen.next(); } catch (e) { r = { done: true }; quickAlts = []; }
        if (r.done) { quickDone = true; break; }
        if (Date.now() > deadline) return false;
      }
      if (done && quickDone) { job.done = true; job.result = mk(); job.partial = job.result; return true; }
      while (!done) {
        if (!sub) {
          if (Date.now() - t0 > budget) { done = true; complete = false; break; }
          if (gi >= groups[level].length) {
            if (swept) { level = 0; gi = 0; swept = false; continue; } // improvements → once more from single cities
            if (level >= 2) { done = true; break; }
            level++; gi = 0; continue;
          }
          const win = groups[level][gi++], j = createJob(subBoard(win), Object.assign({}, opts, { alts: false }));
          st.windows++;
          if (j.combos > MAX_COMBOS_EXACT) { st.skipped++; complete = false; continue; }
          sub = { win, j }; winStart = Date.now();
        }
        const fin = sub.j.step(Math.min(deadline, winStart + perWin));
        if (!fin) {
          if (Date.now() >= winStart + perWin) { st.skipped++; complete = false; sub = null; continue; } // too slow → skip this group
          return false;
        }
        const r = sub.j.result; if (r && r.stats) { st.combos += r.stats.combos; st.nodes += r.stats.nodes; st.leaves += r.stats.leaves; }
        const n = merge(sub.win, sub.j); sub = null;
        if (!n) continue;
        const p = materialize(P, n, 'best'), v = value(p);
        if (v > curV + 0.5) { cur = n; curP = p; curV = v; swept = true; st.improved++; msBest = Date.now() - t0; job.partial = mk(); job.version++; }
      }
      if (!quickDone) { job.partial = mk(); job.version++; return job.step(deadline); }
      job.done = true; job.result = mk(); job.partial = job.result;
      return true;
    };
    return job;
  }
  const MAX_COMBOS_EXACT = 20000;

  PP.market = { CAP, PROD, WS, WS_KEYS, RES_KEYS, UNIQUE, PRODS, BLDS, OPT_KEYS, DEF_COST, RANGE, HUGE, BIG, optimize, createJob, createLargeJob, materialize, solveOnce, prepare, incomeOf, territory, normRegion, inRegion, normCell, costs, fieldPath, prodPath };


  // ======================================================================== UI (browser only)
  if (typeof document === 'undefined') return;

  // Destroy is no item of data.js – registered here (map only, so the Costs ring does not list it)
  if (PP.ITEM && !PP.ITEM.destroy) PP.ITEM.destroy = { id: 'destroy', name: 'Destroy', icon: '💥', cost: 0, pop: 0, tech: 'construction', terrain: ['field', 'forest', 'mountain', 'water'], note: 'removes the building' };

  const EMOJI_FONT = '"Apple Color Emoji","Segoe UI Emoji","Noto Color Emoji",system-ui,sans-serif';
  const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
  const esc = s => (PP.ui && PP.ui.esc ? PP.ui.esc(s) : String(s).replace(/[&<>"']/g, ch => '&#' + ch.charCodeAt(0) + ';'));
  const toast = m => PP.ui && PP.ui.toast && PP.ui.toast(m);
  const NAME = { field: 'Empty', forest: 'Forest', mountain: 'Mountain', water: 'Water', city: 'City', crop: 'Crop (for Farm)', ore: 'Metal', fruit: 'Fruit', animal: 'Animal', fish: 'Fish',
    lumber: 'Lumber Hut', plant: 'Grow Forest', fruitH: 'Harvest Fruit', hunt: 'Hunt', other: 'Other building' };
  const nm = id => NAME[id] || (ITEM(id) || {}).name || ({ cloud: 'Cloud', space: 'Space', monument: 'Monument' })[id] || id;
  const stepName = s => (s.item === 'destroy' ? 'Destroy ' + nm(s.what || 'building') : s.item === 'fruit' ? 'Harvest Fruit' : s.item === 'hunt' ? 'Hunt Animal' : UNIQUE.indexOf(s.item) >= 0 || PRODS.indexOf(s.item) >= 0 ? 'Build ' + nm(s.item) : nm(s.item));
  const ICON = {
    field: '🟩', forest: '🌲', mountain: '⛰️', water: '🌊', city: '🏠', crop: '🌾', ore: '💎', fruit: '🍒', animal: '🦌', hunt: '🏹', fish: '🐟',
    farm: '🌾', mine: '⛏️', lumber: '🪵', windmill: '🌬️', forge: '🔨', sawmill: '🪚', market: '🏪',
    destroy: '💥', clear: '🪓', burn: '🔥', plant: '🌱', other: '🏛️', space: '🌌', cloud: '☁️', monument: '🗽',
  };
  const ICON_NAME = { ore: 'metal', plant: 'forest', hunt: 'animal', destroy: null, clear: null, burn: null, other: null };
  const iconName = id => (id in ICON_NAME ? ICON_NAME[id] : id);
  const hasIcon = id => { const n = iconName(id); return !!(n && PP.icons && PP.icons.has && PP.icons.has(n)); };
  function iconHtml(id, size) {
    if (hasIcon(id) && PP.icons.svg) { try { const s = PP.icons.svg(iconName(id), size || 18); if (s) return s; } catch (e) { /* emoji */ } }
    return ICON[id] || '▪️';
  }
  const WS_COL = { windmill: '#facc15', forge: '#fb923c', sawmill: '#a3e635' };
  const CITY_COL = ['#4cc9f0', '#ff70a6', '#b69cff', '#7bd389', '#ff9f43', '#f9f871', '#2ec4b6', '#e76f51', '#a0c4ff', '#d4a373', '#ff4d6d', '#c0ca33'];
  // "built" marks: deep emerald + diagonal hatching – no city, workshop, Market or level colour is anywhere near it
  const BUILT_COL = '#16a34a', BUILT_FILL = 'rgba(22,163,74,.5)', BUILT_DARK = 'rgba(8,60,28,.95)';
  const ACT_COL = '#3ddc84'; // what the ✓ Built button acts on
  const cityCol = k => CITY_COL[(k >= 0 ? k : 0) % CITY_COL.length];
  const TER_B = ['field', 'forest', 'mountain', 'water', 'space', 'cloud', 'city'];
  const RES_B = ['crop', 'ore', 'fruit', 'animal', 'fish'];
  const BLD_B = ['farm', 'mine', 'lumber', 'windmill', 'forge', 'sawmill', 'market'];
  const BRUSH = TER_B.concat(RES_B, BLD_B, ['monument']);
  const PAL_ORDER = ['field', 'sawmill', 'lumber', 'forest', 'animal', 'windmill', 'farm', 'crop', 'fruit', 'forge', 'mine', 'ore', 'mountain', 'city', 'market', 'water', 'fish', 'space', 'cloud', 'monument'];
  const BRUSH_LABEL = { field: 'Empty', forest: 'Forest', mountain: 'Mountain', water: 'Water', space: 'Space', cloud: 'Cloud', monument: 'Monument', city: 'City', crop: 'Crop', ore: 'Metal', fruit: 'Fruit', animal: 'Animal', fish: 'Fish',
    farm: 'Farm', mine: 'Mine', lumber: 'Lumber', windmill: 'Windmill', forge: 'Forge', sawmill: 'Sawmill', market: 'Market' };
  const RES_TER = { crop: 'field', fruit: 'field', ore: 'mountain', animal: 'forest', fish: 'water' };
  const OPT_LABEL = { clear: ['🪓', 'Clear Forest', '+1 ★'], burn: ['🔥', 'Burn Forest', '→ Crop'], grow: ['🌱', 'Grow Forest', 'Empty → Forest'],
    destroy: ['💥', 'Destroy buildings', 'move / replace'], produce: ['🏗️', 'New Farms, Mines, Lumber Huts', ''] };
  const TECH_OF_WS = { windmill: 'Construction', forge: 'Smithery', sawmill: 'Mathematics' }; // fallback when PP.TECH is missing
  const RES_TECH = { fruit: 'Organization', hunt: 'Hunting', fish: 'Fishing' }; // fallback when PP.TECH is missing

  const ui = { step: 1, brush: 'forest', paint: null, alt: 0, sel: null, entered: false, borders: false, edit: null, onlyForest: false, growMenu: false, techMenu: false };
  const S = () => PP.state;
  // state.market: { cities: [{ c, r, rad: 1|2, made? }], edits: { 'c,r': 1 (added) | 0 (removed) }, touched, opts }
  // (v16 had a rectangle `region`; now always false – core resets it to null when a new screenshot is loaded)
  function M() {
    const st = S();
    if (!st.market || typeof st.market !== 'object') st.market = {};
    const m = st.market;
    if (!m.opts || typeof m.opts !== 'object') m.opts = {};
    // steps the player has marked as built (checklist only – the plan is not computed again): { 'c,r:item': 1 }
    if (!m.done || typeof m.done !== 'object' || Array.isArray(m.done)) m.done = {};
    for (const k of OPT_KEYS.concat(WS_KEYS, RES_KEYS)) if (typeof m.opts[k] !== 'boolean') m.opts[k] = true;
    if (!st.tiles || typeof st.tiles !== 'object' || Array.isArray(st.tiles)) st.tiles = {};
    if (!Array.isArray(st.cities)) st.cities = [];
    // region === false: v17 state. null: fresh state or a new screenshot (core resets it) → start over.
    // A v16 rectangle → the cities inside it with the old territory (radius 2). (Not deleted: core would re-add null.)
    if (m.region !== false) {
      const reg = normRegion(m.region);
      m.cities = []; m.edits = {}; m.done = {}; m.touched = false;
      if (reg) {
        st.cities.forEach(ci => { if (ci && inRegion(reg, ci.c, ci.r) && noCity().indexOf(key(ci.c, ci.r)) < 0) m.cities.push({ c: ci.c, r: ci.r, rad: 2 }); });
        m.touched = true;
      }
      m.region = false;
    }
    if (!Array.isArray(m.cities)) m.cities = [];
    m.cities = m.cities.filter(x => x && Number.isInteger(x.c) && Number.isInteger(x.r));
    m.cities.forEach(x => { if (x.rad !== 2) x.rad = 1; });
    if (!m.edits || typeof m.edits !== 'object' || Array.isArray(m.edits)) m.edits = {};
    return m;
  }
  const build = () => S().build || (S().build = {});
  const placements = () => { const b = build(); if (!Array.isArray(b.placements)) b.placements = []; return b.placements; };
  const noCity = () => { const b = build(); if (!Array.isArray(b.noCity)) b.noCity = []; return b.noCity; };
  const cityEntry = (c, r) => (Array.isArray(S().cities) ? S().cities.find(x => x && x.c === c && x.r === r) : null) || null;

  // terrain suggestion from the screenshot (only on request)
  function suggest(c, r) {
    const a = autoTerrain(c, r);
    if (a) return a.terrain;
    try {
      const smp = PP.board && PP.board.sampleTile ? PP.board.sampleTile(c, r) : null;
      const px = smp && (Array.isArray(smp) ? smp : smp.pixels);
      if (px && px.length && PP.vision && PP.vision.classifyTile) return PP.vision.classifyTile(px, smp.lower ? { lower: smp.lower } : undefined).terrain || null;
    } catch (e) { /* none */ }
    return null;
  }
  const TERRAINS = ['field', 'forest', 'mountain', 'water', 'ocean', 'cloud', 'space'];
  // effective tile: { c, r, terrain, res, bld, stored, name?, cityId? } – unmarked tiles count as Empty
  // v29: terrain of an unmarked tile from the screenshot (PP.tilemodel, in the browser) → { terrain, conf, sure }
  // Cloud / space / foreign cities and villages count as unusable (water). Cached per screenshot + grid.
  let autoMemo = { sig: '', m: new Map() };
  function autoTerrain(c, r) {
    const TM = PP.tilemodel, g = S().grid;
    if (!TM || !TM.ready || !g || !PP.board || !PP.board.pixels || S().board !== 'image') return null;
    const P = PP.board.pixels(); if (!P) return null;
    const sig = [P.w, P.h, g.ox, g.oy, g.ux, g.uy, g.vx, g.vy].map(v => (+v).toFixed(2)).join(',');
    if (autoMemo.sig !== sig || autoMemo.src !== P.src) autoMemo = { sig, src: P.src, m: new Map() };
    const k = key(c, r);
    if (autoMemo.m.has(k)) return autoMemo.m.get(k);
    const ctr = PP.grid.center(c, r), w = Math.abs(g.ux - g.vx);
    let out = null;
    // v33: a tile whose centre is not on the screenshot is outside the map → Space (never part of a territory)
    if (!(ctr.x >= 0 && ctr.y >= 0 && ctr.x < P.w && ctr.y < P.h)) { out = { terrain: 'space', model: 'outside', conf: 1, sure: true, res: [] }; autoMemo.m.set(k, out); return out; }
    try {
      const p = TM.classify(P, ctr.x, ctr.y, w);
      if (p) {
        // "outside" (space / map edge): only when the model is sure – unsure stays water (also not usable)
        const t = /^(field|forest|mountain|water)$/.test(p.terrain) ? p.terrain : p.terrain === 'outside' && p.conf >= TM.SURE ? 'space' : 'water';
        // v2 models: a resource is only filled in when the model is sure about it (crop / fruit on fields, metal on mountains)
        const rs = p.res && p.resConf >= (p.res === 'crop' ? TM.CROP_SURE || 0.6 : p.res === 'fruit' ? TM.FRUIT_SURE || 0.6 : TM.RES_SURE || 0.7) ? (p.res === 'metal' ? 'ore' : p.res) : null; // v3: crop from 0.6
        out = { terrain: t, model: p.terrain, conf: p.conf, sure: p.conf >= TM.SURE, res: rs && RES_TER[rs] === t ? [rs] : [], cloud: p.terrain === 'cloud' };
      }
    } catch (e) { out = null; }
    autoMemo.m.set(k, out);
    return out;
  }
  function cellAt(c, r) {
    const k = key(c, r), t = S().tiles[k], ce = cityEntry(c, r);
    if ((ce || (t && t.city)) && noCity().indexOf(k) < 0) {
      return { c, r, terrain: 'city', res: [], bld: null, stored: true, name: (ce && ce.name) || '', cityId: ce ? ce.id : null };
    }
    if (t && t.src !== 'auto') {
      if (t.bld === 'monument') return { c, r, terrain: 'water', res: [], bld: null, stored: true, monument: true }; // v41: nothing can be built, can't be destroyed
      let ter = TERRAINS.indexOf(t.terrain) >= 0 ? t.terrain : 'field';
      const cloud = ter === 'cloud';           // v37: marked as Cloud (not explored) – nothing is built there, like water
      if (ter === 'ocean' || ter === 'cloud') ter = 'water';
      if (t.mk === 'blocked' && ter === 'field') ter = 'water'; // v13 "Blocked"
      const res = (Array.isArray(t.res) ? t.res : []).filter(q => RES_TER[q] === ter);
      const bld = t.bld ? (BLDS.indexOf(t.bld) >= 0 ? t.bld : 'other') : null;
      return { c, r, terrain: ter, res, bld, other: bld === 'other' ? t.bld : null, stored: true, cloud };
    }
    const a = autoTerrain(c, r);
    if (a) return { c, r, terrain: a.terrain, res: a.res || [], bld: null, stored: false, auto: true, unsure: !a.sure, conf: a.conf, cloud: !!(a.cloud && a.sure) };
    return { c, r, terrain: 'field', res: [], bld: null, stored: false };
  }
  // ------------------------------------------------------------------ planning area = territories of the selected cities
  const isCityAt = (c, r) => cellAt(c, r).terrain === 'city';
  const selCities = () => M().cities.filter(s => isCityAt(s.c, s.r));
  const selAt = (c, r) => M().cities.find(s => s.c === c && s.r === r) || null;
  // nearest city: Chebyshev, then Euclid, then first selected
  function nearestOf(c, r, list) {
    let best = null, bd = 0, be = 0;
    for (const ci of list) {
      const dc = Math.abs(c - ci.c), dr = Math.abs(r - ci.r), d = Math.max(dc, dr), e = dc * dc + dr * dr;
      if (!best || d < bd || (d === bd && e < be)) { best = ci; bd = d; be = e; }
    }
    return best;
  }
  // { cities: [{ c, r, rad, name, k }], owner: Map 'c,r' → k, base: Set (inside some radius), ownerOf(c, r), has(c, r) }
  // Base territory: every tile within the city's radius (3×3 / 5×5), nearest selected city wins; foreign city tiles
  // are left out. Edits: 0 removes a base tile, 1 adds a tile (to the nearest selected city).
  // grow: 'c,r' of a city whose territory is taken as 5×5 (v29: "what if this city gets Border Growth?")
  function area(grow) {
    const m = M(), sel = selCities();
    const grows = k => (grow instanceof Set ? grow.has(k) : grow === k);
    if (grow != null && (!(grow instanceof Set) || grow.size) && sel.some(s => s.rad === 1 && grows(key(s.c, s.r)))) return grownArea(grows);
    const cities = sel.map((s, k) => { const ce = cityEntry(s.c, s.r); return { c: s.c, r: s.r, rad: grows(key(s.c, s.r)) ? 2 : s.rad, name: (ce && ce.name) || '', k, implicit: false }; });
    const owner = new Map(), base = new Set(), cand = new Map();
    const cityK = new Map(cities.map(ci => [key(ci.c, ci.r), ci.k]));
    for (const ci of cities) {
      for (let dr = -ci.rad; dr <= ci.rad; dr++) for (let dc = -ci.rad; dc <= ci.rad; dc++) {
        const k = key(ci.c + dc, ci.r + dr);
        if (!cand.has(k)) cand.set(k, { c: ci.c + dc, r: ci.r + dr, by: [] });
        cand.get(k).by.push(ci);
      }
    }
    for (const [k, t] of cand) {
      if (cityK.has(k)) { owner.set(k, cityK.get(k)); continue; }
      if (isCityAt(t.c, t.r)) continue; // someone else's city
      base.add(k);
      if (m.edits[k] === 0) continue;
      if (cellAt(t.c, t.r).terrain === 'space') continue; // outside the map
      // v44: a tile given to a city in "Edit borders" belongs to that city, else to the nearest one
      const as = typeof m.edits[k] === 'string' && cityK.has(m.edits[k]) ? cityK.get(m.edits[k]) : null;
      owner.set(k, as != null ? as : nearestOf(t.c, t.r, t.by).k);
    }
    if (cities.length) {
      for (const k of Object.keys(m.edits)) {
        const v = m.edits[k];
        if (!(v === 1 || typeof v === 'string') || owner.has(k) || cand.has(k)) continue;
        const [c, r] = k.split(',').map(Number);
        if (!isFinite(c) || !isFinite(r) || isCityAt(c, r) || cellAt(c, r).terrain === 'space') continue;
        owner.set(k, typeof v === 'string' && cityK.has(v) ? cityK.get(v) : nearestOf(c, r, cities).k);
      }
    }
    const ownerOf = (c, r) => { const v = owner.get(key(c, r)); return v === undefined ? -1 : v; };
    return { cities, owner, base, ownerOf, has: (c, r) => owner.has(key(c, r)), implicit: false, n: owner.size };
  }
  // Border Growth only claims tiles nobody owns yet: today's territory (with your border edits) stays exactly as it
  // is, the grown city gets the free tiles of its 5×5 ring. Not free: tiles of another planned city, tiles you took
  // out with Edit borders, Space, and the 3×3 around any city that isn't planned (enemy or own city left out).
  // Two growing cities that both reach a free tile: the nearer one gets it.
  function grownArea(grows) {
    const m = M(), cur = area();
    const cities = cur.cities.map(ci => Object.assign({}, ci, { rad: ci.rad === 1 && grows(key(ci.c, ci.r)) ? 2 : ci.rad }));
    const owner = new Map(cur.owner), base = new Set(cur.base), cand = new Map();
    const cityK = new Set(cities.map(ci => key(ci.c, ci.r)));
    const foreignNear = (c, r) => NB.some(([dc, dr]) => !cityK.has(key(c + dc, r + dr)) && isCityAt(c + dc, r + dr));
    for (const ci of cities) {
      if (ci.rad !== 2 || cur.cities[ci.k].rad === 2) continue;
      for (let dr = -2; dr <= 2; dr++) for (let dc = -2; dc <= 2; dc++) {
        const c = ci.c + dc, r = ci.r + dr, k = key(c, r);
        if (cur.owner.has(k) || cur.base.has(k)) continue; // owned today, or taken out of a territory with Edit borders
        if (!cand.has(k)) cand.set(k, { c, r, by: [] });
        cand.get(k).by.push(ci);
      }
    }
    for (const [k, t] of cand) {
      if (isCityAt(t.c, t.r) || foreignNear(t.c, t.r)) continue; // a city, or the territory of a city you don't plan
      base.add(k);
      if (m.edits[k] === 0) continue;
      if (cellAt(t.c, t.r).terrain === 'space') continue; // outside the map
      owner.set(k, nearestOf(t.c, t.r, t.by).k);
    }
    const ownerOf = (c, r) => { const v = owner.get(key(c, r)); return v === undefined ? -1 : v; };
    return { cities, owner, base, ownerOf, has: (c, r) => owner.has(key(c, r)), implicit: false, n: owner.size };
  }
  const terr = area;
  const inArea = (c, r) => area().has(c, r);
  // v31 the extra ring every 3×3 city would get with Border Growth: tiles of the "all grown" area that are not in
  // today's area. They can be marked in ② (only the Border Growth check uses them). → { A, keys: Map 'c,r' → city k }
  function ringInfo() {
    const A = area(), small = A.cities.filter(ci => ci.rad === 1), keys = new Map();
    if (!small.length) return { A, keys, G: null };
    const G = area(new Set(small.map(ci => key(ci.c, ci.r))));
    for (const [k, own] of G.owner) {
      if (A.owner.has(k)) continue;
      const [c, r] = k.split(',').map(Number);
      if (!isCityAt(c, r)) keys.set(k, own);
    }
    return { A, keys, G };
  }
  const inRing = (c, r) => ringInfo().keys.has(key(c, r));
  // paintable: everything inside a radius (also Space tiles, so they can be changed back), today's and grown
  const inPaint = (c, r) => { const k = key(c, r), R = ringInfo(); return R.A.base.has(k) || R.A.owner.has(k) || (R.G && R.G.base.has(k)); };
  // tiles inside a radius that are Space (outside the map) – shown in ② so they can be corrected
  function spaceKeys() {
    const R = ringInfo(), out = new Set();
    [R.A.base].concat(R.G ? [R.G.base] : []).forEach(B => B.forEach(k => { const [c, r] = k.split(',').map(Number); if (cellAt(c, r).terrain === 'space') out.add(k); }));
    return out;
  }
  const ringCells = () => [...ringInfo().keys.keys()].map(k => { const [c, r] = k.split(',').map(Number); return Object.assign(cellAt(c, r), { ring: true }); });
  const RING_COL = 'rgba(190,255,120,.85)'; // dashed outline of the Border Growth ring in ②
  // per city: ring tiles you have not marked yourself, and how many of them the detection is unsure about
  function ringStats() {
    const out = {};
    for (const [k, own] of ringInfo().keys) {
      const [c, r] = k.split(',').map(Number), x = cellAt(c, r), o = out[own] || (out[own] = { n: 0, open: 0, unsure: 0 });
      // only tiles the detection is unsure about (the ones with ?) – a sure detection or your own mark is fine
      o.n++; if (!x.stored && x.unsure) { o.open++; o.unsure++; }
    }
    return out;
  }
  function areaCells(A) {
    A = A || area();
    const out = [];
    for (const [k, own] of A.owner) {
      const [c, r] = k.split(',').map(Number), x = cellAt(c, r), ci = A.cities[own];
      if (x.terrain !== 'city') x.own = key(ci.c, ci.r);
      out.push(x);
    }
    out.sort((a, b) => a.r - b.r || a.c - b.c);
    return out;
  }
  const optCells = list => list.map(x => (x.terrain === 'city' ? { c: x.c, r: x.r, terrain: 'city', name: x.name } : { c: x.c, r: x.r, terrain: x.terrain, res: x.res, bld: x.bld, own: x.own }));
  // tiles next to the area (8-neighbourhood) that could be added
  function fringe(A) {
    const out = new Map();
    for (const k of A.owner.keys()) {
      const [c, r] = k.split(',').map(Number);
      for (const [dc, dr] of NB) {
        const q = key(c + dc, r + dr);
        if (!A.owner.has(q) && !out.has(q) && !isCityAt(c + dc, r + dr)) out.set(q, [c + dc, r + dr]);
      }
    }
    return [...out.values()];
  }
  const cityName = (ci, k) => (!ci || ci.implicit ? 'City' : ci.name || 'City ' + (k < 26 ? String.fromCharCode(65 + k) : k + 1));
  const plural = (n, a, b) => n + ' ' + (n === 1 ? a : b);

  // ------------------------------------------------------------------ plan (async job, memoized)
  let cache = null, cacheSig = '', running = null;
  const MAX_COMBOS = 20000, QUICK_EXACT = 300, EXACT_MS = 30000; // exact search ≤ MAX_COMBOS (≤ EXACT_MS in the background); below QUICK_EXACT right away
  function planSig() {
    const m = M();
    return JSON.stringify([optCells(areaCells()), m.opts]);
  }
  // v29 Border Growth check – only on request (button). Greedy over combinations: start from the plan as it is, add the
  // city whose growth to 5×5 brings the most ★ TOGETHER with the ones already chosen, repeat. Plus "all of them" to
  // catch synergies the steps miss. Each configuration is solved like the main plan (exact or group search).
  // growth = { sig, state: 'running'|'done', steps: [{ key, name, k, income, cost, gain }], all: { income, cost }, base, done, total }
  let growth = null, growthAuto = false;
  const GROW_PROOF_SECS = 10, GROW_COST_SECS = 5; // HiGHS time per Border Growth plan (alone usually a few seconds)
  const growthNow = () => (growth && growth.sig === cacheSig && (!growth.prio || growth.prio === (GROW_PRIO[M().growPrio] ? M().growPrio : 'bal')) ? growth : null);
  const growVerdict = k => { const g = growthNow(); return g && g.state === 'done' && g.byKey ? g.byKey[k] || null : null; };
  // one configuration: group search / exact search first, then HiGHS proves the maximum ★ (same model as the main proof),
  // so the numbers are the same on every run. → { income, cost, proven }
  function growthWorker(g) {
    if (g.worker !== undefined) return g.worker;
    g.worker = null;
    if (PP.marketMilp && typeof Worker !== 'undefined') try { g.worker = new Worker('js/market-worker.js?v=STAMP'); } catch (e) { g.worker = null; }
    return g.worker;
  }
  function runJob(g, job) {
    return new Promise(done => {
      const step = () => { if (!alive(g)) return done(null); if (job.step(Date.now() + 20)) done(job.result); else setTimeout(step, 0); };
      setTimeout(step, 0);
    });
  }
  // HiGHS in the Border Growth worker. spec = { mode: 'income' } or { mode: 'cost', minIncome } → { p, D, optimal, bound } | null
  function milpRun(g, P, spec, D, secs) {
    const w = growthWorker(g);
    if (!w) return Promise.resolve(null);
    return new Promise(done => {
      const model = PP.marketMilp.build(P, spec), id = (g.msg = (g.msg || 0) + 1);
      let names = null;
      w.onmessage = ev => {
        const m = ev.data || {};
        if (m.id !== id) return;
        if (m.type === 'names') { names = m.names; return; }
        if (m.type === 'error') return done(null);
        if (m.type !== 'done') return;
        let p = null, d = null;
        if (names) { const cols = {}; names.forEach((nm, k) => { cols[nm] = { Primal: m.values[k] }; }); d = model.decode(cols); p = materialize(P, d, 'inc'); }
        done({ p, D: d, optimal: !!m.optimal, bound: isFinite(m.bound) ? Math.floor(m.bound + 1e-6) : null });
      };
      w.postMessage({ id, lp: model.lp, start: D ? model.start(D) : null, opts: { time_limit: secs } });
    });
  }
  // one configuration: quick search, then HiGHS proves the maximum ★ (same model as the main proof). If HiGHS finds
  // more ★ than the search, a short cost run makes the cost of that plan comparable. → { income, cost, proven }
  // a background check (Border Growth, tech advisor) is still wanted? g.alive() for the tech advisor
  const alive = g => (g.alive ? g.alive() : growth === g);
  async function solveGrowCfg(g, set) { return solveScenario(g, optCells(areaCells(area(set))), M().opts); }
  // best plan for these cells and options: quick search, then HiGHS proves the maximum ★ → { income, cost, proven }
  async function solveScenario(g, cells, opts) {
    const o = Object.assign({}, opts, { alts: false });
    let job = createJob(cells, o);
    if (job.combos > QUICK_EXACT) job = createLargeJob(cells, Object.assign(o, { largeMs: 3000, quick: false }));
    const r = await runJob(g, job);
    if (!alive(g) || !r) return null;
    const b = r.best;
    let out = { income: b ? b.income : 0, cost: b ? b.cost : 0, proven: !r.large || !!(b && b.income >= r.large.ub) };
    if (out.proven) return out;
    const P = prepare(cells, Object.assign({}, opts));
    const pr = await milpRun(g, P, { mode: 'income' }, r.decision, GROW_PROOF_SECS);
    if (!alive(g)) return null;
    if (!pr) return out;
    out.proven = pr.optimal;
    if (pr.p && pr.p.income > out.income) {
      out.income = pr.p.income; out.cost = pr.p.cost;
      const pc = await milpRun(g, P, { mode: 'cost', minIncome: out.income }, pr.D, GROW_COST_SECS);
      if (!alive(g)) return null;
      if (pc && pc.p && pc.p.income >= out.income && pc.p.cost < out.cost) out.cost = pc.p.cost;
    }
    return out;
  }
  // Which cities should grow? Up to GROW_ALL_MAX cities with 3×3: every combination is solved → the best one for sure.
  // More: every city alone, then added one by one (in the order of their gain alone, each together with the ones
  // already chosen), then every left-out city again on top of the result, then left-out NEIGHBOURS in pairs (only
  // neighbours can help each other). Result per city: take it or not, the ★ it adds, its cost, synergy partners.
  const GROW_ALL_MAX = 5;
  const growSolves = n => (n <= GROW_ALL_MAX ? 2 ** n : 3 * n + 4);
  function startGrowth(res) {
    if (!res || !res.best) return;
    const skip = growSkip(), A = area(), cand = A.cities.filter(ci => ci.rad === 1 && !skip.has(key(ci.c, ci.r)) && popReach(A, ci).ok).map(ci => ({ key: key(ci.c, ci.r), name: cityName(ci, ci.k), k: ci.k, c: ci.c, r: ci.r }));
    if (!cand.length) return;
    stopGrowth(); if (tech && tech.state !== 'done') stopTech(); // only one check at a time; finished results stay
    const n = cand.length, exhaustive = n <= GROW_ALL_MAX;
    const g = growth = { sig: cacheSig, state: 'running', exhaustive, n, done: 0, total: growSolves(n), t0: Date.now(), open: 0, cities: [], best: null, base: null };
    const memo = new Map(), cfgKey = set => [...set].sort().join('|');
    const refresh = () => { if (growth === g && PP.modes && PP.modes.current === 'market') PP.app.refresh(); };
    const solve = async set => {
      const k = cfgKey(set);
      if (!memo.has(k)) {
        const v = await solveGrowCfg(g, set); if (!v) return null;
        if (!v.proven) g.open++; memo.set(k, v); g.done++; if (g.done > g.total) g.total = g.done; refresh();
      }
      return memo.get(k);
    };
    const got = set => memo.get(cfgKey(set));
    // v40: a city only grows if Border Growth beats Population Growth (+3 pop ≈ 7.5 ★ + a bonus for the Giant sooner):
    // value of a choice = extra Market ★/turn × horizon − extra building cost − (cities that grow) × value of Pop Growth
    const PR = growPrio(); g.prio = PR.id; g.PR = PR;
    const valOf = (r, set) => (r.income - g.base.income) * PR.H - (r.cost - g.base.cost) - set.size * PR.pg;
    const better = (a, sa, b, sb) => { if (!b) return true; const va = valOf(a, sa), vb = valOf(b, sb); return va > vb + 1e-9 || (Math.abs(va - vb) <= 1e-9 && sa.size < sb.size); };
    const near = (a, b) => Math.max(Math.abs(a.c - b.c), Math.abs(a.r - b.r)) <= 5;
    (async () => {
      pauseProof(g);
      g.t0 = Date.now();
      const base = await solve(new Set()); if (!base) return;
      g.base = base;
      let bestSet = new Set(), bestR = base;
      const addGain = {};
      if (exhaustive) {
        const masks = []; for (let m = 1; m < (1 << n); m++) masks.push(m);
        const bits = m => { let c = 0; for (; m; m &= m - 1) c++; return c; };
        masks.sort((a, b) => bits(a) - bits(b) || a - b);
        for (const m of masks) {
          const set = new Set(cand.filter((c, i) => m & (1 << i)).map(c => c.key));
          const r = await solve(set); if (!r) return;
          if (better(r, set, bestR, bestSet)) { bestR = r; bestSet = set; }
        }
      } else {
        g.total = 3 * n + 4;
        for (const c of cand) if (!(await solve(new Set([c.key])))) return;
        const aloneOf = c => got(new Set([c.key])).income - base.income;
        const order = cand.slice().sort((a, b) => aloneOf(b) - aloneOf(a));
        const tryAdd = async keys => {
          const set = new Set([...bestSet, ...keys]), r = await solve(set); if (!r) return null;
          if (valOf(r, set) > valOf(bestR, bestSet) + 1e-9) { keys.forEach(k => { addGain[k] = { gain: r.income - bestR.income, dcost: r.cost - bestR.cost, with: keys.length > 1 ? keys : null }; }); bestSet = set; bestR = r; return true; }
          return false;
        };
        for (const c of order) if ((await tryAdd([c.key])) === null) return;
        // local search: add a city, take one out, swap a chosen city for a neighbour, add two neighbours –
        // the first move that makes the result better is kept, then again, until no move helps (or the budget is used)
        const lsCap = g.done + 6 * n;
        for (let improved = true; improved && g.done < lsCap;) {
          improved = false;
          const inn = cand.filter(c => bestSet.has(c.key)), out = cand.filter(c => !bestSet.has(c.key));
          const moves = [];
          out.forEach(c => moves.push({ add: [c.key], del: [] }));
          inn.forEach(c => moves.push({ add: [], del: [c.key] }));
          inn.forEach(a => out.forEach(b => { if (near(a, b)) moves.push({ add: [b.key], del: [a.key] }); }));
          for (let a = 0; a < out.length; a++) for (let b = a + 1; b < out.length; b++) if (near(out[a], out[b])) moves.push({ add: [out[a].key, out[b].key], del: [] });
          for (const mv of moves) {
            if (g.done >= lsCap) break;
            const set = new Set([...bestSet].filter(k => mv.del.indexOf(k) < 0).concat(mv.add));
            const r = await solve(set); if (!r) return;
            if (better(r, set, bestR, bestSet)) { bestSet = set; bestR = r; improved = true; break; }
          }
        }
      }
      // what each chosen city adds on top of the others (exact: the choice without it)
      for (const k of bestSet) if (!(await solve(new Set([...bestSet].filter(x => x !== k))))) return;
      g.verdicts = (bestSet, bestR) => {
      // verdict per city
      g.best = { set: bestSet, income: bestR.income, cost: bestR.cost };
      const aloneR = c => got(new Set([c.key]));
      g.cities = cand.map(c => {
        const al = aloneR(c), alone = al ? al.income - base.income : 0, take = bestSet.has(c.key);
        let gain = 0, dcost = 0, partners = [];
        if (take) {
          const without = new Set([...bestSet].filter(k => k !== c.key)), w = got(without);
          if (w) { gain = bestR.income - w.income; dcost = bestR.cost - w.cost; }
          else if (addGain[c.key]) { gain = addGain[c.key].gain; dcost = addGain[c.key].dcost; }
          // synergy: a partner in the choice with which the pair earns more than both alone
          for (const d of cand) {
            if (d === c || !bestSet.has(d.key)) continue;
            const pr = got(new Set([c.key, d.key])), ad = aloneR(d);
            if (pr && ad && pr.income - base.income > alone + (ad.income - base.income)) partners.push(d);
          }
          if (!partners.length && addGain[c.key] && addGain[c.key].with) partners = cand.filter(d => d !== c && addGain[c.key].with.indexOf(d.key) >= 0);
        }
        // why not: no gain at all / pays back too slowly against Population Growth / nothing on top of the growing cities
        const aloneCost = al ? al.cost - base.cost : 0, why = take ? null : alone <= 0 ? 'nogain' : alone * PR.H - aloneCost - PR.pg <= 0 ? 'slow' : 'others';
        return { key: c.key, k: c.k, name: c.name, c: c.c, r: c.r, take, gain, dcost, alone, aloneCost, why, partners: partners.map(d => ({ k: d.k, name: d.name })) };
      });
      g.byKey = {}; g.cities.forEach(ci => { g.byKey[ci.key] = ci; });
      };
      g.verdicts(bestSet, bestR);
      // v40: all combinations known → another priority is just another choice among them (no new plans needed)
      if (exhaustive) g.rechoose = P2 => {
        Object.assign(PR, P2); g.prio = P2.id;
        let bs = new Set(), br = g.base;
        for (const [k, r] of memo) { const set = new Set(k ? k.split('|') : []); if (better(r, set, br, bs)) { br = r; bs = set; } }
        g.verdicts(bs, br);
      };
      g.state = 'done'; g.ms = Date.now() - g.t0;
      if (g.worker) try { g.worker.terminate(); } catch (e) { /* gone */ }
      resumeProof(g);
      refresh();
    })();
  }
  // the proof of the main plan needs the same CPU (each check is ~4× slower next to it) → pause it, go on afterwards
  function pauseProof(g) {
    if (!prover) return;
    const pr = prover;
    g.paused = { res: pr.res, sig: pr.sig, costSecs: pr.costSecs || COST_SECS };
    stopProver();
    ['inc', 'cost', 'fast'].forEach(k => { if (pr.res.proof && (pr.res.proof[k] === 'running' || pr.res.proof[k] === 'waiting')) pr.res.proof[k] = 'waiting'; });
    if (pr.res.proof) pr.res.proof.paused = true;
  }
  function resumeProof(g) {
    const pz = g && g.paused; if (!pz) return;
    g.paused = null;
    if (pz.res.proof) pz.res.proof.paused = false;
    if (pz.sig === cacheSig && cache === pz.res && !prover) startProof(pz.res, pz.sig, pz.costSecs, true);
  }
  function stopGrowth() {
    const g = growth;
    if (g && g.worker) try { g.worker.terminate(); } catch (e) { /* gone */ }
    growth = null;
    if (g && g.state !== 'done') resumeProof(g);
  }
  // ====================================================================== v36 tech advisor
  // Which tech (that you don't have yet) brings your Markets the most? Every scenario is the best Market plan with your
  // techs plus that tech (and the techs it needs) – solved like the Border Growth check. Then the best order: the best
  // tech counts as bought and the others are checked again on top of it.
  const MK_TECHS = ['trade', 'construction', 'mathematics', 'smithery', 'farming', 'forestry', 'mining', 'spiritualism', 'organization'];
  const TECH_PICK = ['riding', 'roads', 'trade', 'organization', 'farming', 'construction', 'hunting', 'forestry', 'mathematics', 'climbing', 'mining', 'smithery', 'archery', 'spiritualism', 'philosophy'];
  const TECH_UNLOCKS = { trade: 'Markets', construction: 'Windmill, Burn Forest', mathematics: 'Sawmill', smithery: 'Forge', farming: 'Farm', forestry: 'Lumber Hut, Clear Forest', mining: 'Mine', spiritualism: 'Grow Forest', organization: 'Harvest Fruit' };
  let tech = null;
  const techName = id => (PP.TECH && PP.TECH[id] ? PP.TECH[id].name : id);
  const ownedTechs = () => { const b = S().build || {}; return new Set(Array.isArray(b.owned) ? b.owned : []); };
  const techNow = () => (tech && tech.sig === techSig() ? tech : null);
  function techSig() { return cacheSig + '|' + [...ownedTechs()].sort().join(','); }
  // the techs needed for id that are not in have, prerequisites first
  function techPath(id, have) { const out = []; let t = PP.TECH && PP.TECH[id]; while (t && !have.has(t.id)) { out.unshift(t.id); t = t.parent ? PP.TECH[t.parent] : null; } return out; }
  function techCityCount() {
    const own = (S().cities || []).filter(c => c && c.side === 'me').length, b = S().build || {};
    return Math.max(1, own, selCities().length, +b.cityCount || 1);
  }
  function techCost(list, owned) {
    const n = techCityCount(), ow = [...owned];
    return list.reduce((a, id) => a + (PP.engine && PP.engine.techCost ? PP.engine.techCost(id, n, ow) : (PP.TECH[id] ? PP.TECH[id].tier : 1) * n + 4), 0);
  }
  // what the plan may build with these techs (and the options you set)
  function techOpts(have) {
    const h = id => have.has(id), u = M().opts, o = Object.assign({}, u);
    const lim = { market: h('trade'), farm: h('farming'), mine: h('mining'), lumber: h('forestry'), clear: h('forestry'), burn: h('construction'),
      destroy: h('construction'), grow: h('spiritualism'), windmill: h('construction'), sawmill: h('mathematics'), forge: h('smithery'),
      fruit: h('organization'), hunt: h('hunting') };
    for (const k in lim) o[k] = u[k] !== false && lim[k];
    return o;
  }
  function stopTech() {
    const g = tech;
    if (g && g.worker) try { g.worker.terminate(); } catch (e) { /* gone */ }
    tech = null;
    if (g && g.state !== 'done') resumeProof(g);
  }
  function startTech() {
    if (growth && growth.state !== 'done') stopGrowth(); // only one check at a time; finished results stay
    stopTech();
    const owned = ownedTechs(), cand = MK_TECHS.filter(t => !owned.has(t));
    const g = tech = { sig: techSig(), state: 'running', done: 0, total: 1 + cand.length, open: 0, rows: [], order: [], t0: Date.now(), alive: () => tech === g };
    const cells = optCells(areaCells()), memo = new Map();
    const refresh = () => { if (tech === g && PP.modes && PP.modes.current === 'market') PP.app.refresh(); };
    const solve = async have => {
      const k = [...have].sort().join(',');
      if (!memo.has(k)) {
        const v = await solveScenario(g, cells, techOpts(have)); if (!v) return null;
        if (!v.proven) g.open++; memo.set(k, v); g.done++; if (g.done > g.total) g.total = g.done; refresh();
      }
      return memo.get(k);
    };
    // a scenario always includes Trade (no Trade → no new Market)
    const withTech = (have, id) => { const add = techPath(id, have); const h2 = new Set([...have, ...add]); if (!h2.has('trade')) techPath('trade', h2).forEach(t => { add.push(t); h2.add(t); }); return { have: h2, add }; };
    (async () => {
      pauseProof(g);
      g.t0 = Date.now();
      const base = await solve(owned); if (!base) return;
      g.base = base;
      for (const id of cand) {
        const { have, add } = withTech(owned, id), r = await solve(have); if (!r) return;
        g.rows.push({ id, add, income: r.income, gain: r.income - base.income, tcost: techCost(add, owned), dcost: r.cost - base.cost, proven: r.proven });
        refresh();
      }
      // best order: always the tech that adds the most ★/turn on top of the ones before (ties: cheaper)
      let have = owned, cur = base, left = cand.slice();
      while (left.length) {
        let best = null;
        for (const id of left) {
          if (have.has(id)) continue;
          const w = withTech(have, id), r = await solve(w.have); if (!r) return;
          const gain = r.income - cur.income, tc = techCost(w.add, have), dc = r.cost - cur.cost;
          if (!best || gain > best.gain || (gain === best.gain && tc + dc < best.tc + best.dc)) best = { id, w, r, gain, tc, dc };
        }
        if (!best || best.gain <= 0) break;
        g.order.push({ id: best.id, add: best.w.add, gain: best.gain, tc: best.tc, dc: best.dc, income: best.r.income });
        have = best.w.have; cur = best.r; left = left.filter(id => !have.has(id));
        refresh();
      }
      g.state = 'done'; g.ms = Date.now() - g.t0;
      if (g.worker) try { g.worker.terminate(); } catch (e) { /* gone */ }
      resumeProof(g);
      refresh();
    })();
  }
  function techHtml(res) {
    if (!res || res.pending || res.tooBig || res.altPending || !res.best) return '';
    const g = techNow(), owned = ownedTechs();
    if (!g) {
      if (!ui.techMenu) return '<button class="mk-btn" data-a="techMenu">🔬 Which tech helps my Markets most? ▾</button>';
      const cand = MK_TECHS.filter(t => !owned.has(t)), solves = 1 + cand.length * 2;
      const est = Math.max(5, Math.round(solves * (res.large ? 6 : 1.5)));
      let h = '<div class="gw-menu"><div class="gw-mh"><b>🔬 Which techs do you have?</b><button class="lnk" data-a="techMenu">close ▴</button></div><div class="gw-pick">';
      h += TECH_PICK.map(id => { const on = owned.has(id); return `<button class="${on ? 'on' : ''}" data-tech="${id}" style="--cc:${on ? '#06d6a0' : '#5a6488'}" aria-pressed="${on}"><span class="bx">${on ? '✓' : ''}</span>${esc(techName(id))}</button>`; }).join('');
      h += '</div>';
      h += cand.length ? `<button class="mk-btn pri" data-a="tech">▶ Start <small style="opacity:.8">(about ${plural(solves, 'plan', 'plans')} · about ${est < 90 ? est + ' s' : Math.round(est / 60) + ' min'})</small></button>`
        : '<div class="mk-note">You have every tech the Markets need.</div>';
      return h + '</div>';
    }
    const box = inner => '<div class="mk-grow"><div class="gw-t">🔬 Which tech helps my Markets most?</div>' + inner + '</div>';
    if (g.state === 'running') {
      const pct = Math.min(100, Math.round(100 * g.done / Math.max(1, g.total)));
      return box(`<div class="mk-prog"><div class="bar"><i style="width:${pct}%;background:#7bd389"></i></div><span><span class="mk-spin"></span>checking plan ${Math.min(g.done + 1, g.total)} of ≈${g.total}…</span></div>`);
    }
    const nm = id => `<b>${esc(techName(id))}</b>`, extra = (add, id) => { const o = add.filter(x => x !== id); return o.length ? ` <small>(+ ${o.map(techName).map(esc).join(', ')})</small>` : ''; };
    const pay = (gain, c) => (gain > 0 ? (c > 0 ? 'pays back in ' + plural(Math.ceil(c / gain), 'turn', 'turns') : 'pays back at once') : '');
    let h = '';
    const first = g.order[0];
    h += first ? `<div class="gw-sum">👉 Buy first: ${nm(first.id)}${extra(first.add, first.id)} – <b class="gw-plus">+${first.gain} ★/turn</b> from Markets<br><small>${g.base.income} → ${first.income} ★/turn · techs ${first.tc} ★ + building ${Math.max(0, first.dc)} ★ · ${pay(first.gain, first.tc + Math.max(0, first.dc))}</small></div>`
      : '<div class="gw-sum">👉 <b>No new tech adds Market income</b> with these cities and tiles.</div>';
    if (g.order.length > 1) {
      h += '<div class="mk-note" style="margin:0 0 4px">Best order (each on top of the ones before):</div><div class="tc-order">';
      let sum = g.base.income;
      h += g.order.map((o, i) => { sum = o.income; return `<span><b>${i + 1}.</b> ${esc(techName(o.id))}${o.add.length > 1 ? ' <small>(+' + plural(o.add.length - 1, 'tech', 'techs') + ')</small>' : ''} <b class="gw-plus">+${o.gain} ★</b></span>`; }).join('<i>→</i>');
      h += `</div><div class="mk-note" style="margin:2px 0 8px">All together: ${g.base.income} → <b>${sum} ★/turn</b></div>`;
    }
    h += '<div class="mk-note" style="margin:4px 0">Each tech alone (with the techs it needs):</div>';
    const rows = g.rows.slice().sort((a, b) => b.gain - a.gain || (a.tcost + a.dcost) - (b.tcost + b.dcost));
    h += rows.map(r => `<div class="gw-card ${r.gain > 0 ? 'take' : 'skip'}" style="--cc:${r.gain > 0 ? '#7bd389' : '#5a6488'}"><div class="gw-h">${nm(r.id)}${extra(r.add, r.id)}` +
      `<span class="gw-v">${r.gain > 0 ? '+' + r.gain + ' ★/turn' : 'no gain'}</span></div>` +
      `<div class="gw-d"><small>${esc(TECH_UNLOCKS[r.id] || '')} · techs ${r.tcost} ★${r.gain > 0 ? ' + building ' + Math.max(0, r.dcost) + ' ★ · ' + pay(r.gain, r.tcost + Math.max(0, r.dcost)) : ''}</small></div></div>`).join('');
    if (g.open) h += `<p class="mk-note" style="margin:8px 0 0;color:#ffb703">⚠ ${plural(g.open, 'plan', 'plans')} not proven</p>`;
    h += '<button class="mk-btn sm" data-a="techAgain" style="margin-top:8px">↻ Change my techs and check again</button>';
    return box(h);
  }
  // v33: cities the player does not want to grow (chosen in the Border Growth menu) – kept with the plan
  const GROW_PRIO = {
    eco: { id: 'eco', name: '💰 Economy', H: 20, giant: 0, note: 'Market income first' },
    bal: { id: 'bal', name: '⚖️ Balanced', H: 10, giant: 5, note: 'only a clear gain' },
    war: { id: 'war', name: '🛡️ War – Giants first', H: 5, giant: 20, note: 'only if it pays back very fast' },
  };
  function growPrio() { const id = M().growPrio; const P = GROW_PRIO[id] || GROW_PRIO.bal; return Object.assign({ pg: 7.5 + P.giant }, P); }
  function growSkip() { const m = M(); if (!Array.isArray(m.growSkip)) m.growSkip = []; return new Set(m.growSkip); }
  // Border Growth is the level-4 reward: a city must first gain 2 + 3 + 4 = 9 population (level 1 → 4), and it has to
  // come from its 3×3 territory (the ring is only there after growing). Population a city can still get there:
  // Harvest Fruit / Hunt / Catch Fish +1, Farm +2, Mine +2, Lumber Hut +1, Windmill +1 per Farm, Forge +2 per Mine, Sawmill +1 per
  // Lumber Hut next to it – with your techs and allowed actions. Upper bound (a tile is counted for its best use; ports,
  // temples and roads are not counted). The city's level / population from the city editor count as reached,
  // and so do the buildings already in its territory, whichever is more. Level 4+ with 3×3: the choice is gone.
  const POP_NEED = 9, PROD_POP = { farm: 2, mine: 2, lumber: 1 }, WS_POP = { windmill: 1, forge: 2, sawmill: 1 };
  function popReach(A, ci) {
    const ce = cityEntry(ci.c, ci.r) || {}, L = Math.max(1, Math.min(8, +ce.level || 1)), p = Math.max(0, +ce.pop || 0);
    if (L >= 4) return { ok: false, why: 'level', level: L };
    let soFar = p; for (let k = 1; k < L; k++) soFar += k + 1;
    const o = normOpts(M().opts), mine = (c, r) => A.ownerOf(c, r) === ci.k && !(c === ci.c && r === ci.r);
    const X = new Map(); // normalized cells, any tile asked for
    const at = (c, r) => { const k = key(c, r); if (!X.has(k)) { const x = cellAt(c, r); X.set(k, normCell(x.terrain === 'city' ? { c, r, terrain: 'city' } : x)); } return X.get(k); };
    const canBe = (x, P) => !x.bld && x.t !== 'city' && o.produce && !!prodPath(x, P, o);
    const tiles = []; for (const k of A.owner.keys()) { const [c, r] = k.split(',').map(Number); if (mine(c, r)) tiles.push(at(c, r)); }
    const nbs = x => NB.map(([dc, dr]) => at(x.c + dc, x.r + dr));
    // already there: producers and workshops in the territory (a workshop counts the producers next to it, any owner)
    let have = 0, bonus = 0;
    for (const x of tiles) {
      if (PROD_POP[x.bld]) have += PROD_POP[x.bld];
      if (WS_POP[x.bld]) have += WS_POP[x.bld] * nbs(x).filter(y => y.bld === PROD[x.bld]).length;
      // Harvest Fruit / Hunt / Catch Fish: +1 each, whatever the tile is used for afterwards
      if (!x.bld) bonus += (x.fruit && o.fruit ? 1 : 0) + (x.animal && o.hunt ? 1 : 0) + (x.fish && o.fish ? 1 : 0);
    }
    // exact maximum of the rest: every placement of the new workshops (one per type, on a free tile that can hold
    // one), then each other free tile takes its best use: producer pop + the pop it adds to the workshops next to it
    const free = tiles.filter(x => !x.bld);
    const wsAt = {}; for (const T of WS) { const e = tiles.find(x => x.bld === T); if (e) wsAt[T] = [e]; }
    const opts = WS.map(T => (wsAt[T] ? [wsAt[T][0]] : [null].concat(o[T] ? free.filter(w => fieldPath(w, o)) : [])));
    const adj = (a, b) => a !== b && Math.max(Math.abs(a.c - b.c), Math.abs(a.r - b.r)) === 1;
    let pot = 0;
    for (const w0 of opts[0]) for (const w1 of opts[1]) for (const w2 of opts[2]) {
      const W = [w0, w1, w2];
      if (new Set(W.filter(Boolean)).size !== W.filter(Boolean).length) continue; // two workshops on one tile
      let v = 0;
      W.forEach((w, j) => { if (w && !w.bld) v += WS_POP[WS[j]] * nbs(w).filter(y => y.bld === PROD[WS[j]]).length; }); // new workshop next to producers already built
      for (const x of free) {
        if (W.indexOf(x) >= 0) continue;
        let best = 0;
        for (const P of PRODS) {
          if (!canBe(x, P)) continue;
          let s = PROD_POP[P];
          W.forEach((w, j) => { if (w && PROD[WS[j]] === P && adj(w, x)) s += WS_POP[WS[j]]; });
          best = Math.max(best, s);
        }
        v += best;
      }
      pot = Math.max(pot, v);
    }
    pot += bonus;
    const reached = Math.max(soFar, have), max = reached + pot;
    return { ok: max >= POP_NEED, why: max >= POP_NEED ? null : 'pop', level: L, reached, max };
  }
  const popWhy = r => (r.why === 'level' ? `level ${r.level} already – Border Growth was the level-4 choice`
    : `only ${r.max} of ${POP_NEED} population reachable in its 3×3 – can't reach level 4`);
  function growthHtml(res) {
    if (!res || res.pending || res.tooBig || res.altPending || !res.best) return '';
    const A = area(), small = A.cities.filter(ci => ci.rad === 1), grown = A.cities.filter(ci => ci.rad === 2);
    const box = inner => '<div class="mk-grow"><div class="gw-t">🌱 Border Growth – which cities should take it?</div>' + inner + '</div>';
    // cities set to 5×5 count as already grown and are not checked – say so clearly and offer to check them all
    const allBtn = grown.length ? `<button class="mk-btn" data-a="growthAll" style="margin-top:8px;width:100%">🌱 Check all ${A.cities.length} cities from 3×3</button>` : '';
    if (growthAuto && !growthNow()) { growthAuto = false; setTimeout(() => { startGrowth(planResult()); PP.app.refresh(); }, 0); }
    if (!small.length) return box(allBtn.replace('margin:8px 0 0', 'margin:0'));
    const g = growthNow(), rs = ringStats(), skip = growSkip();
    const reach = new Map(small.map(ci => [ci.k, popReach(A, ci)])), blocked = small.filter(ci => !reach.get(ci.k).ok);
    const pick = small.filter(ci => !skip.has(key(ci.c, ci.r)) && reach.get(ci.k).ok), n = pick.length, solves = growSolves(n);
    const blockedHtml = blocked.length ? '<div class="gw-warn" style="color:var(--muted,#9aa5c8);background:rgba(255,255,255,.04)">🚫 Can\'t take Border Growth (needs level 4 = 9 population first):' +
      blocked.map(ci => `<br><b style="color:${cityCol(ci.k)}">${esc(cityName(ci, ci.k))}</b>: ${esc(popWhy(reach.get(ci.k)))}`).join('') +
      '<br><small>Level / population are set in the city editor; ports, temples and roads are not counted.</small></div>' : '';
    const openRing = pick.reduce((a, ci) => a + ((rs[ci.k] || {}).open || 0), 0);
    const ringWarn = openRing ? `<div class="gw-warn">⚠ ${plural(openRing, 'tile', 'tiles')} with <b>?</b> in the Border Growth rings (dashed light-green, outside 3×3) – <button class="lnk" data-step="2">check them in ②</button></div>` : '';
    if (!g) {
      // v33: a plain button; tapping it opens a small menu: which cities may grow, then Start
      if (!ui.growMenu) return `<button class="mk-btn" data-a="growthMenu">🌱 Check Border Growth ▾</button>`;
      const est = Math.max(5, Math.round(solves * (res.large ? 6 : 1.5)));
      const PRn = growPrio();
      let h = '<div class="gw-menu"><div class="gw-mh"><b>🌱 Border Growth or Population Growth?</b><button class="lnk" data-a="growthMenu">close ▴</button></div>';
      h += '<div class="gw-prio">' +
        Object.values(GROW_PRIO).map(P => `<button class="${PRn.id === P.id ? 'on' : ''}" data-gprio="${P.id}"><b>${P.name}</b><small>${esc(P.note)}</small></button>`).join('') + '</div>';
      h += '<div class="mk-note" style="margin:8px 0 4px">Which cities may grow?</div><div class="gw-pick">';
      h += small.filter(ci => reach.get(ci.k).ok).map(ci => { const k = key(ci.c, ci.r), on = !skip.has(k);
        return `<button class="${on ? 'on' : ''}" data-gskip="${k}" style="--cc:${cityCol(ci.k)}" aria-pressed="${on}"><span class="bx">${on ? '✓' : ''}</span>${esc(cityName(ci, ci.k))}</button>`; }).join('');
      h += '</div>';
      if (grown.length) h += `<div class="mk-note" style="margin:4px 0">Already 5×5: ${grown.map(ci => esc(cityName(ci, ci.k))).join(', ')} <button class="lnk" data-a="growthAll">set all to 3×3 and check</button></div>`;
      h += blockedHtml + ringWarn;
      h += n ? `<button class="mk-btn pri" data-a="growth">▶ Start <small style="opacity:.8">(${n <= GROW_ALL_MAX ? '' : 'about '}${plural(solves, 'plan', 'plans')} · about ${est < 90 ? est + ' s' : Math.round(est / 60) + ' min'})</small></button>`
        : `<button class="mk-btn" disabled>${blocked.length === small.length ? 'No city can reach level 4' : 'Pick at least one city'}</button>`;
      return h + '</div>';
    }
    if (g.state === 'running') {
      const pct = Math.min(100, Math.round(100 * g.done / Math.max(1, g.total)));
      return box(`<div class="mk-prog"><div class="bar"><i style="width:${pct}%;background:#7bd389"></i></div><span><span class="mk-spin"></span>checking plan ${Math.min(g.done + 1, g.total)} of ${g.exhaustive ? '' : '≈'}${g.total}…</span></div>`);
    }
    const nm = (k, name) => `<b style="color:${cityCol(k)}">${esc(name)}</b>`;
    const take = g.cities.filter(c => c.take).sort((a, b) => b.gain - a.gain), noTake = g.cities.filter(c => !c.take).sort((a, b) => b.alone - a.alone);
    const sum = g.best.income - g.base.income, dc = g.best.cost - g.base.cost;
    let h = '';
    { const PRr = growPrio(); h += `<div class="gw-prio" style="margin:0 0 8px">` + Object.values(GROW_PRIO).map(P => `<button class="${PRr.id === P.id ? 'on' : ''}" data-gprio="${P.id}"><b>${P.name}</b><small>${esc(P.note)}</small></button>`).join('') + '</div>'; }
    h += take.length
      ? `<div class="gw-sum">👉 🌱 Border Growth in <b>${take.length} of ${g.cities.length}</b> ${g.cities.length === 1 ? 'city' : 'cities'}: ${take.map(c => nm(c.k, c.name)).join(', ')}${noTake.length ? `<br>👥 Population Growth in ${noTake.map(c => nm(c.k, c.name)).join(', ')}` : ''}<br>` +
        `<b class="gw-plus">+${sum} ★/turn</b> <small>(${g.base.income} → ${g.best.income}${dc > 0 ? ' · builds ' + dc + ' ★ more · pays back in ' + plural(Math.ceil(dc / Math.max(1, sum)), 'turn', 'turns') : ''})</small></div>` +
        `<button class="mk-btn pri" data-a="growthApply" style="width:100%;margin:0 0 8px">Plan with 5×5 for ${take.map(c => esc(c.name)).join(', ')}</button>`
      : '<div class="gw-sum">👉 <b>Population Growth in every city</b> – Border Growth doesn\'t pay back fast enough here (Giant sooner).</div>';
    const card = c => {
      const rr = rs[c.k] || { open: 0, unsure: 0 };
      let x = '';
      if (c.take) {
        x += `<div class="gw-d"><b class="gw-plus">+${c.gain} ★/turn</b>${c.dcost > 0 ? ` · builds ${c.dcost} ★ · pays back in ${plural(Math.ceil(c.dcost / Math.max(1, c.gain)), 'turn', 'turns')}` : c.dcost < 0 ? ` · plan gets ${-c.dcost} ★ cheaper` : ' · no extra cost'}</div>`;
        if (c.partners.length) x += `<div class="gw-x">🔗 ${c.alone > 0 ? 'Pays off more' : 'Only pays off'} together with ${c.partners.map(d => nm(d.k, d.name)).join(' + ')} <small>(alone +${c.alone})</small></div>`;
        else if (c.alone > c.gain) x += `<div class="gw-x">Alone it would add +${c.alone} – less together, because the growing neighbours share tiles and Markets</div>`;
        else if (c.alone < c.gain) x += `<div class="gw-x">Alone only +${c.alone} – more together with the other growing cities</div>`;
      } else {
        const PRc = g.PR || growPrio(), pb = c.alone > 0 && c.aloneCost > 0 ? Math.ceil(c.aloneCost / c.alone) : 0;
        x += `<div class="gw-d">${c.why === 'nogain' ? 'Border Growth adds no ★/turn to the Markets here'
          : c.why === 'slow' ? `Border Growth: +${c.alone} ★/turn${c.aloneCost > 0 ? ` for ${c.aloneCost} ★ (pays back in ${plural(pb, 'turn', 'turns')})` : ''} – less than +3 population is worth (${PRc.H} turns, ${PRc.name.replace(/^\S+ /, '')})`
          : `Alone +${c.alone} ★/turn – but not enough on top of the cities that grow`}</div><div class="gw-x">+3 population: Level 5 (Giant / Park) sooner</div>`;
      }
      if (rr.open) x += `<div class="gw-w">⚠ ${plural(rr.open, 'tile', 'tiles')} with ? in its Border Growth ring – check them in ②</div>`;
      return `<div class="gw-card ${c.take ? 'take' : 'skip'}" style="--cc:${cityCol(c.k)}"><div class="gw-h"><span class="dot"></span>${nm(c.k, c.name)}` +
        `<span class="gw-v">${c.take ? '🌱 Border Growth' : '👥 Population Growth'}</span></div>${x}</div>`;
    };
    h += take.concat(noTake).map(card).join('');
    h += ringWarn;
    if (g.open) h += `<p class="mk-note" style="margin:8px 0 0;color:#ffb703">⚠ ${plural(g.open, 'plan', 'plans')} not proven</p>`;
    h += blockedHtml;
    const left = small.filter(ci => skip.has(key(ci.c, ci.r)) && reach.get(ci.k).ok);
    if (left.length) h += `<div class="mk-note" style="margin:4px 0 0">Not checked (your choice): ${left.map(ci => esc(cityName(ci, ci.k))).join(', ')}</div>`;
    h += '<button class="mk-btn sm" data-a="growthAgain" style="margin-top:8px">↻ Choose cities and check again</button>';
    return box(h);
  }
  // v29 proof with HiGHS (js/market-worker.js): after the group search (many cities) the plan is checked by a MILP –
  // first that no plan earns more ★, then that no plan with these ★ is cheaper. Better plans found on the way replace
  // the shown one. res.proof = { inc: 'proven'|'running'|'open', cost: …, incBound, costBound, gap, secs }
  let prover = null; // { sig, worker, res }
  const PROOF_SECS = 300, COST_SECS = 60, COST_MORE_SECS = 600; // income proof · automatic cost proof · on request
  function stopProver() { if (prover && prover.worker) try { prover.worker.terminate(); } catch (e) { /* gone */ } prover = null; }
  function proofRefresh() { if (PP.modes && PP.modes.current === 'market' && ui.step === 3) PP.app.refresh(); }
  // time budget (s) of a worker task – used for the "≤ … s" hints at the plan options
  const taskBudget = (t, costSecs) => (t === 'inc' ? PROOF_SECS : t === 'cost' || t === 'fast' ? costSecs : Math.min(costSecs, 30));
  // seconds until the task that refines an option is done (upper bound) – null if nothing is pending for it
  function etaFor(res, tag) {
    if (!prover || prover.res !== res || !prover.task) return null;
    const seq = [prover.task].concat(prover.queue || []);
    const want = tag === 'best' ? (seq.indexOf('cost') >= 0 ? 'cost' : 'inc') : tag;
    let t = Math.max(0, (prover.until - Date.now()) / 1000);
    if (seq[0] === want) return t;
    for (const k of seq.slice(1)) { t += taskBudget(k, prover.costSecs); if (k === want) return t; }
    return null;
  }
  const fmtEta = sec => (sec == null ? '' : sec < 60 ? '≤ ' + Math.max(1, Math.ceil(sec / 5) * 5) + ' s' : '≤ ' + Math.ceil(sec / 60) + ' min');
  // Tasks run one after the other in the worker (time-limited each):
  //   fast    fastest payback (Dinkelbach: min cost − λ·★, λ = best ratio so far; an optimum ≥ 0 proves it)
  //   inc     no plan earns more ★ (many cities only; instant when every Market can reach 8 ★)
  //   cost    no plan with these ★ is cheaper (many cities only)
  // resume = true: after a pause (Border Growth check) – parts that already ended ('proven' or timed out) are kept
  function startProof(res, sig, costSecs, resume) {
    if (!res || !res.best) return;
    costSecs = costSecs || COST_SECS;
    const prev = res.proof || {};
    const large = !!res.large;
    if (!PP.marketMilp || typeof Worker === 'undefined') { res.proof = { inc: large ? (res.large.optimal ? 'proven' : 'open') : 'proven', cost: large ? 'open' : 'proven', exact: !large, fast: 'open', noSolver: true }; return; }
    stopProver();
    const P = prepare(optCells(areaCells()), Object.assign({}, M().opts));
    const pr = prover = { sig, res, t0: Date.now() };
    const incDone = !large || res.best.income >= res.large.ub || prev.inc === 'proven';
    res.proof = { inc: incDone ? 'proven' : 'waiting', cost: !large || prev.cost === 'proven' ? 'proven' : 'waiting', fast: prev.fast === 'proven' ? 'proven' : 'waiting',
      exact: !large, secs: 0, costSecs };
    if (resume) ['inc', 'cost', 'fast'].forEach(k => { if (prev[k] === 'open') res.proof[k] = 'open'; ['incBound', 'costBound'].forEach(b => { if (prev[b] != null) res.proof[b] = prev[b]; }); });
    // ?v=STAMP becomes the worker's content hash on release (scripts/stamp-assets.js)
    let worker;
    try { worker = pr.worker = new Worker('js/market-worker.js?v=STAMP'); } catch (e) { res.proof.noSolver = true; ['inc', 'cost', 'fast'].forEach(k => { if (res.proof[k] !== 'proven') res.proof[k] = 'open'; }); return; }
    const SC = PP.marketMilp.SCALE;
    const val = p => p.income * HUGE - (p.cost * BIG + p.actions);
    const score = p => (p.cost * SC + p.actions) / p.income;   // fastest payback: ★ cost per ★/turn (steps break ties)
    const same = (a, b) => a && b && a.income === b.income && a.cost === b.cost && a.actions === b.actions;
    const setAlt = (tag, p) => {
      res.alts = (res.alts || []).filter(q => q.tag !== tag);
      if (p && p.income > 0) res.alts.push(Object.assign({}, p, { tag }));
    };
    let model = null, names = null, stage = null, task = null, until = 0;
    // the fastest payback is the best ratio of ALL plans we know – any task may find a better one
    const improveFast = p => {
      if (!p || !(p.income > 0)) return;
      if (res.fastPlan && score(p) >= score(res.fastPlan) - 1e-9) return;
      res.fastPlan = p; setAlt('fast', same(p, res.best) ? null : p);
      if (res.proof.fast === 'proven') res.proof.fast = 'open'; // (cannot happen: a proven optimum has no better plan)
    };
    const plan = values => {
      const cols = {}; names.forEach((nm, j) => { cols[nm] = { Primal: values[j] }; });
      const D = model.decode(cols); return { D, p: materialize(P, D, task) };
    };
    const send = (spec, secs, startD) => {
      stage = (stage || 0) + 1; model = PP.marketMilp.build(P, spec); names = null;
      worker.postMessage({ id: stage, lp: model.lp, start: startD ? model.start(startD) : null, opts: { time_limit: Math.max(5, secs) } });
    };
    const left = () => (until - Date.now()) / 1000;
    const queue = pr.queue = [];
    pr.costSecs = costSecs;
    if (res.proof.fast === 'waiting') queue.push('fast');
    if (res.proof.inc === 'waiting') queue.push('inc');
    if (res.proof.cost === 'waiting') queue.push('cost');
    let dk = null; // Dinkelbach state { tag, minInc, plan, D }
    const next = () => {
      if (prover !== pr) return;
      task = queue.shift();
      if (!task) { try { worker.terminate(); } catch (e) { /* gone */ } prover = null; proofRefresh(); return; }
      res.proof[task] = 'running'; pr.tc = Date.now(); pr.task = task;
      const B = taskBudget(task, costSecs); pr.until = Date.now() + B * 1000; proofRefresh();
      if (task === 'inc') { until = Date.now() + PROOF_SECS * 1000; send({ mode: 'income' }, PROOF_SECS, res.decision); }
      else if (task === 'cost') { until = Date.now() + costSecs * 1000; send({ mode: 'cost', minIncome: res.best.income }, costSecs, res.decision); }
      else {
        // fast: start from the best known ratio among the plans we have
        const minInc = 1;
        let st = res.best, D = res.decision || null;
        (res.alts || []).forEach(q => { if (q.income >= minInc && q.income > 0 && score(q) < score(st)) { st = q; D = null; } });
        dk = { minInc, plan: st, D };
        improveFast(st);
        until = Date.now() + costSecs * 1000;
        dkStep();
      }
    };
    const dkStep = () => {
      if (left() < 3) { dkDone(false); return; }
      send({ mode: 'ratio', lambda: score(dk.plan) / SC, minIncome: dk.minInc }, left(), dk.D);
    };
    const dkDone = proven => {
      const p = dk.plan;
      improveFast(p); res.proof.fast = proven ? 'proven' : 'open';
      proofRefresh(); next();
    };
    worker.onmessage = ev => {
      if (prover !== pr) return;
      const m = ev.data || {};
      if (m.id !== stage) return;
      res.proof.secs = Math.round((Date.now() - pr.tc) / 1000);
      if (m.type === 'names') { names = m.names; return; }
      if (m.type === 'incumbent') {
        if (!names) return;
        const { D, p } = plan(m.values);
        if ((task === 'inc' || task === 'cost') && val(p) > val(res.best) + 0.5) { res.best = Object.assign(p, { tag: 'best' }); res.decision = D; improveFast(p); proofRefresh(); }
        // fast: show a better ratio right away (the search goes on with the old λ)
        if (task === 'fast' && dk && p.income >= dk.minInc && p.income > 0 && score(p) < score(dk.plan) - 1e-9) {
          dk.plan = p; dk.D = D; improveFast(p); proofRefresh();
        }
        return;
      }
      if (m.type === 'progress') {
        if (task === 'inc' && isFinite(m.bound)) res.proof.incBound = Math.floor(m.bound + 1e-6);
        if (task === 'cost' && isFinite(m.bound)) res.proof.costBound = Math.ceil(m.bound / SC - 1e-6);
        proofRefresh(); return;
      }
      if (m.type === 'error') {
        res.proof.error = m.message;
        ['inc', 'cost', 'fast'].forEach(k => { if (res.proof[k] !== 'proven') res.proof[k] = 'open'; });
        try { worker.terminate(); } catch (e) { /* gone */ } prover = null; proofRefresh(); return;
      }
      if (m.type !== 'done') return;
      const got = names ? plan(m.values) : null;
      if (task === 'inc' || task === 'cost') {
        if (got && val(got.p) > val(res.best) + 0.5) { res.best = Object.assign(got.p, { tag: 'best' }); res.decision = got.D; improveFast(got.p); }
        if (task === 'inc') { res.proof.inc = m.optimal ? 'proven' : 'open'; if (!m.optimal && isFinite(m.bound)) res.proof.incBound = Math.floor(m.bound + 1e-6); }
        else { res.proof.cost = m.optimal ? 'proven' : 'open'; if (isFinite(m.bound)) res.proof.costBound = Math.ceil(m.bound / SC - 1e-6); }
        proofRefresh(); next(); return;
      }
      // fast (Dinkelbach)
      const p = got && got.p;
      if (p && p.income >= dk.minInc && m.obj < -1e-6 && score(p) < score(dk.plan) - 1e-9) { dk.plan = p; dk.D = got.D; dkStep(); return; }
      dkDone(m.optimal && m.obj > -1e-6);
    };
    next();
  }
  function proofHtml(res) {
    if (res && res.exactPending) return '<p class="mk-note"><span class="mk-spin"></span>Exact search running…</p>';
    const q = res && res.proof; if (!q) return '';
    if (q.paused) return '<p class="mk-note">⏸ Plan check paused</p>';
    const ok = '<b style="color:#7bd389">✓</b>', spin = '<span class="mk-spin"></span>', b = res.best, lines = [];
    if (q.exact) lines.push(`${ok} Most ★ and cheapest proven`);
    else {
      if (q.inc === 'proven') lines.push(`${ok} Most ★ proven`);
      else if (q.inc === 'running') lines.push(`${spin}Checking for more ★…`);
      else if (q.inc === 'waiting') lines.push('⏳ Next: check for more ★');
      else lines.push(`⚠ More ★ not ruled out${q.incBound != null ? ` (at most ${q.incBound} ★/turn)` : ''}`);
      if (q.cost === 'proven') lines.push(`${ok} Cheapest proven`);
      else if (q.cost === 'running') lines.push(`${spin}Checking for a cheaper plan…`);
      else if (q.cost === 'open') lines.push('Cheapest not proven');
    }
    if (q.fast === 'proven') lines.push(`${ok} Fastest payback proven`);
    else if (q.fast === 'running') lines.push(`${spin}Checking the fastest payback…`);
    else if (q.fast === 'open') lines.push('Fastest payback not proven');
    if (q.noSolver) lines.push('<small>Check not available in this browser</small>');
    else if ((q.cost === 'open' || q.fast === 'open') && !(q.costSecs >= COST_MORE_SECS) && !prover)
      lines.push(`<button class="mk-btn sm" data-a="proveMore">🔎 Keep checking (up to ${Math.round(COST_MORE_SECS / 60)} min)</button>`);
    return `<p class="mk-note">${lines.join('<br>')}${q.secs && prover ? ` <small>· ${q.secs} s</small>` : ''}</p>`;
  }
  function planResult() {
    const m = M(); if (!selCities().length) return null;
    const sig = planSig();
    if (cache && sig === cacheSig) return cache;
    if (prover && prover.sig !== sig) stopProver();
    if (growth && growth.sig !== sig) stopGrowth(); // board changed → that check is worthless
    if (tech && tech.sig.split('|')[0] !== sig) stopTech();
    if (running && running.sig === sig) return running.job.partial ? Object.assign({}, running.job.partial, { altPending: true, etaMs: running.job.eta ? running.job.eta() : null }) : { pending: true, job: running.job };
    let job = createJob(optCells(areaCells()), Object.assign({}, m.opts)), exact = null;
    // v29: results first. Tiny problems: the exact search right away. Otherwise the fast group search shows a plan within
    // milliseconds and quick options within seconds; if the problem is small enough (≤ MAX_COMBOS Market combinations)
    // the exact search runs afterwards and replaces it with the proven result. More: group search + HiGHS proof.
    if (job.combos > QUICK_EXACT) {
      // the exact check only proves the best plan (the options come from the quick search and HiGHS)
      if (job.combos <= MAX_COMBOS) exact = createJob(optCells(areaCells()), Object.assign({}, m.opts, { alts: false }));
      job = createLargeJob(optCells(areaCells()), Object.assign({}, m.opts));
    }
    const run = running = { sig, job };
    // the exact search after the quick one (same board): its result replaces the quick one and starts the proof
    const runExact = () => {
      if (!exact) { startProof(cache, sig); return; }
      cache.exactPending = true;
      const ex = run.exact = exact, t0 = Date.now(), tickEx = () => {
        if (cacheSig !== sig || run.exact !== ex) return; // board changed
        if (!ex.step(Date.now() + 25)) {
          // some boards take the exact search minutes – after EXACT_MS HiGHS takes over the proof
          if (Date.now() - t0 > EXACT_MS) { cache.exactPending = false; run.exact = null; startProof(cache, sig); proofRefresh(); return; }
          setTimeout(tickEx, 0); return;
        }
        const r = ex.result;
        // keep the better plan (the exact one is never worse – but keep quick options it doesn't have)
        const quickAlts = (cache.alts || []).filter(q => !r.alts.some(a => a.tag === q.tag));
        r.alts = r.alts.concat(quickAlts);
        cache = r; ui.alt = ui.alt || 0;
        startProof(cache, sig);
        if (PP.modes && PP.modes.current === 'market') PP.app.refresh();
      };
      setTimeout(tickEx, 0);
    };
    if (job.step(Date.now() + 60)) { running = null; cacheSig = sig; cache = job.result; ui.alt = 0; runExact(); return cache; }
    let shown = !!job.partial, ver = job.version || 0;
    const tick = () => {
      if (running !== run) return; // abandoned (board changed)
      const done = job.step(Date.now() + 28);
      if (done) {
        running = null; cacheSig = sig; cache = job.result;
        runExact();
      } else setTimeout(tick, 0);
      const better = job.large && job.version !== ver; ver = job.version || 0;
      if (done || (!shown && job.partial) || better) {
        const first = !shown; shown = true;
        if (PP.modes && PP.modes.current === 'market') { PP.app.refresh(); if (ui.step === 3 && first) requestAnimationFrame(fitPlan); }
      }
    };
    setTimeout(tick, 0);
    return job.partial ? Object.assign({}, job.partial, { altPending: true, etaMs: job.eta ? job.eta() : null }) : { pending: true, job };
  }
  // v29: the plan options are fixed (ui.alt = tag); a missing one falls back to Best
  const ALT_TAGS = ['best', 'fast']; // v29: Cheaper / Fewer steps removed on request
  const altOf = (res, tag) => (!tag || tag === 'best' ? res.best
    : (res.alts || []).find(q => q.tag === tag && (tag !== 'fewer' || q.income >= res.best.income)) || null);
  const curPlan = res => (res && !res.pending ? altOf(res, ui.alt) || res.best : null);
  function altsHtml(res) {
    const q = res.proof || {}, info = { best: 'most ★/turn', fast: 'return on investment' };
    const pending = tag => !res.proof || res.altPending || (tag === 'fast' ? q.fast === 'waiting' || q.fast === 'running'
      : res.large && (q[tag] === 'waiting' || q[tag] === 'running'));
    const shown = [];
    // state of an option: still searching (with time), quick result being improved, final or proven
    const status = (tag, pl) => {
      if (res.exactPending) return pl ? '<span class="mk-spin"></span>quick result · exact check running' : '<span class="mk-spin"></span>exact check running';
      if (res.altPending) return `<span class="mk-spin"></span>${pl && tag === 'best' ? 'quick result · ' : 'calculating… '}${fmtEta(res.etaMs != null ? res.etaMs / 1000 : null)}`;
      const eta = etaFor(res, tag);
      if (eta != null) return `<span class="mk-spin"></span>${pl ? 'quick result · improving ' : 'calculating… '}${fmtEta(eta)}`;
      if (!pl) return '';
      if (tag === 'best') return q.exact || (q.inc === 'proven' && q.cost === 'proven') ? '✓ proven best' : q.inc === 'proven' ? '✓ most ★ proven' : 'final';
      if (tag === 'fast') return q.fast === 'proven' ? '✓ proven fastest' : 'final · not proven';
      return 'final';
    };
    let h = '<div class="mk-alts">';
    for (const tag of ALT_TAGS) {
      const pl = altOf(res, tag), on = (ui.alt || 'best') === tag, stt = status(tag, pl);
      const sline = stt ? `<small style="display:block;opacity:.75;font-size:10.5px">${stt}</small>` : '';
      let body;
      if (pl) {
        const twin = shown.find(x => x.p.income === pl.income && x.p.cost === pl.cost && x.p.actions === pl.actions);
        body = `<b>${pl.income} ★/turn</b>${pl.cost} ★ · ${plural(pl.actions, 'step', 'steps')}` +
          (pl.payback ? `<small style="display:block;opacity:.8">pays back in ${plural(pl.payback, 'turn', 'turns')}</small>` : '') +
          (twin ? `<small style="display:block;opacity:.65">same plan as ${TAG[twin.tag]}</small>` : '') + sline;
        shown.push({ tag, p: pl });
      } else if (pending(tag) || stt) body = `<small style="display:block">${stt || '<span class="mk-spin"></span>calculating…'}</small>`;
      else body = '<small style="display:block;opacity:.75">Best already pays back fastest</small>';
      h += `<button class="mk-alt ${on ? 'on' : ''}" data-alt="${tag}" title="${esc(info[tag])}"${pl ? '' : ' disabled'}>${TAG[tag]}${body}</button>`;
    }
    return h + '</div>';
  }

  // ------------------------------------------------------------------ cities (shared PP.state.cities)
  function sideOf(color) {
    const my = S().ui && S().ui.myColor, ok = v => Array.isArray(v) && v.length >= 3 && v.every(x => isFinite(x));
    if (!ok(my) || !ok(color)) return null;
    if (PP.recog && PP.recog.sideFor) {
      let tl = []; try { tl = PP.recog.tribes ? PP.recog.tribes() : []; } catch (e) { tl = []; }
      return PP.recog.sideFor(color, my, tl);
    }
    return Math.hypot(color[0] - my[0], color[1] - my[1], color[2] - my[2]) < 60 ? 'me' : 'enemy';
  }
  const uid = () => (PP.util && PP.util.uid ? PP.util.uid() : Date.now().toString(36) + Math.random().toString(36).slice(2, 7));
  function upsertCity(c, r, src, extra) {
    const list = S().cities, k = key(c, r);
    const nc = noCity(), ni = nc.indexOf(k);
    if (src === 'user' && ni >= 0) nc.splice(ni, 1);
    let ci = cityEntry(c, r);
    if (ci) {
      if (src === 'user' && ci.src === 'auto') ci.src = 'user';
      if (extra && extra.color && !ci.color) ci.color = extra.color;
      if (ci.side == null && extra && extra.side) ci.side = extra.side;
      return ci;
    }
    ci = { id: uid(), c, r, side: (extra && extra.side) || null, name: '', level: 1, pop: 0, capital: false, src };
    if (extra && extra.color) ci.color = extra.color;
    if (extra && extra.conf != null) ci.conf = extra.conf;
    list.push(ci);
    return ci;
  }
  function removeCity(c, r) {
    const k = key(c, r), t = S().tiles[k];
    S().cities = S().cities.filter(x => !(x && x.c === c && x.r === r));
    if (t && t.city) { delete t.city; if (!Object.keys(t).some(q => q !== 'src')) delete S().tiles[k]; }
    if (noCity().indexOf(k) < 0) noCity().push(k);
  }
  // cities on the screenshot (name plates), from the Units tool's detection (cached there)
  function detectedList() {
    let list = [];
    try {
      if (PP.units && PP.units.detectedCities) list = PP.units.detectedCities() || [];
      else if (PP.vision && PP.vision.detectCities && PP.board && PP.board.image && S().grid) {
        const tr = [[150, 95, 60], [100, 66, 51], [60, 60, 170]];
        try { if (PP.recog && PP.recog.tribes) PP.recog.tribes().forEach(k => { if (Array.isArray(k.color)) tr.push(k.color.slice(0, 3)); }); } catch (e) { /* ignore */ }
        list = PP.vision.detectCities(PP.board.image, Object.assign({}, S().grid), tr) || [];
      }
    } catch (e) { list = []; }
    return list.filter(d => d && Number.isInteger(d.c) && Number.isInteger(d.r) && noCity().indexOf(key(d.c, d.r)) < 0);
  }
  const detColor = d => (Array.isArray(d.color) ? d.color.slice(0, 3).map(Math.round) : null);
  // own cities the app knows (city list side 'me', detected name plates of my colour) that are not selected yet
  function knownOwn() {
    const out = [], seen = new Set(M().cities.map(s => key(s.c, s.r)));
    const add = (c, r) => { const k = key(c, r); if (!seen.has(k)) { seen.add(k); out.push({ c, r }); } };
    S().cities.forEach(ci => { if (ci && ci.side === 'me' && noCity().indexOf(key(ci.c, ci.r)) < 0) add(ci.c, ci.r); });
    detectedList().forEach(d => { if (!cityEntry(d.c, d.r) && sideOf(detColor(d)) === 'me') add(d.c, d.r); });
    return out;
  }
  // select a city tile (creates the city entry if the app did not know it)
  function selectCity(c, r, rad) {
    const m = M();
    let s = selAt(c, r);
    if (!isCityAt(c, r)) {
      const d = detectedList().find(q => q.c === c && q.r === r);
      const made = !cityEntry(c, r) && !(S().tiles[key(c, r)] || {}).city;
      upsertCity(c, r, 'user', d ? { color: detColor(d), side: sideOf(detColor(d)) || 'me', conf: d.conf } : { side: 'me' });
      if (s) s.made = s.made || made;
      else s = { c, r, rad: 1, made };
    }
    if (!s) s = { c, r, rad: 1 };
    if (rad) s.rad = rad;
    if (m.cities.indexOf(s) < 0) {
      m.cities = m.cities.filter(x => !(x.c === c && x.r === r)).concat(s);
    }
    m.touched = true;
    ui.alt = 0;
    return s;
  }
  function unselectCity(c, r) {
    const m = M(), s = selAt(c, r);
    m.cities = m.cities.filter(x => x !== s);
    m.touched = true; ui.alt = 0;
    // a city this tool created (tap on an unknown tile) disappears again
    if (s && s.made) {
      const ce = cityEntry(c, r);
      if (ce && ce.src === 'user' && !ce.name) S().cities = S().cities.filter(x => x !== ce);
    }
    if (!m.cities.length) m.edits = {};
  }
  // tap in step ①: city → select (3×3) → 5×5 → off; other tiles → snap to a city next to it or mark a new city
  function tapCity(c, r) {
    const s = selAt(c, r);
    if (s && isCityAt(c, r)) {
      const nm1 = cityLabel(c, r);
      if (s.rad === 1) { s.rad = 2; M().touched = true; ui.alt = 0; toast(nm1 + ': 5×5 territory (tap again to remove)'); }
      else { unselectCity(c, r); toast(nm1 + ' removed'); }
      return;
    }
    if (!isCityAt(c, r)) {
      if (inArea(c, r)) { toast('Tap a city tile – or use ✏️ Edit borders to change single tiles'); return; }
      // a known / detected city right next to the tapped tile (name plates sit below the city)
      const near = S().cities.filter(ci => ci && !selAt(ci.c, ci.r) && Math.max(Math.abs(ci.c - c), Math.abs(ci.r - r)) <= 1 && isCityAt(ci.c, ci.r))
        .concat(detectedList().filter(d => !selAt(d.c, d.r) && Math.max(Math.abs(d.c - c), Math.abs(d.r - r)) <= 1));
      if (near.length === 1 || (near.length > 1 && near.every(q => q.c === near[0].c && q.r === near[0].r))) { c = near[0].c; r = near[0].r; }
    }
    const was = isCityAt(c, r), n = selectCity(c, r, 1);
    if (n) toast(cityLabel(c, r) + (was ? '' : ' (marked as city)') + ': 3×3 territory · tap again for 5×5');
  }
  // name as shown in the chips (City A, B … by selection order)
  const cityLabel = (c, r) => {
    const ce = cityEntry(c, r);
    if (ce && ce.name) return ce.name;
    const k = selCities().findIndex(s => s.c === c && s.r === r);
    return k >= 0 ? cityName({}, k) : 'City ' + c + '/' + r;
  };
  // Edit borders: add a tile next to the territory / remove a territory tile (want: true add, false remove, null toggle)
  // v44: borders are edited for ONE city (ui.editCity = 'c,r'): tap a tile → it belongs to that city (also when it
  // belonged to another one); tap one of its tiles → it is removed. want: true add, false remove, null toggle.
  function editCityK(A) {
    A = A || area();
    if (!A.cities.some(ci => key(ci.c, ci.r) === ui.editCity)) ui.editCity = A.cities.length ? key(A.cities[0].c, A.cities[0].r) : null;
    return ui.editCity;
  }
  function editBorder(c, r, want) {
    const m = M(), A = area(), k = key(c, r), ek = editCityK(A);
    if (!A.cities.length || !ek) return 'none';
    if (isCityAt(c, r)) return 'city';
    const ci = A.cities.find(x => key(x.c, x.r) === ek), mine = A.ownerOf(c, r) === ci.k;
    if (mine) {
      if (want === true) return 'same';
      m.edits[k] = 0;                                                     // not part of any territory any more
    } else {
      if (want === false) return 'same';
      const near = Math.max(Math.abs(c - ci.c), Math.abs(r - ci.r)) <= ci.rad || NB.some(([dc, dr]) => A.ownerOf(c + dc, r + dr) === ci.k);
      if (!near) return 'far';
      m.edits[k] = ek;                                                    // belongs to the chosen city
    }
    m.touched = true; ui.alt = 0;
    return 'ok';
  }

  // ------------------------------------------------------------------ painting
  function storeTile(c, r, o) {
    const tiles = S().tiles, k = key(c, r), cur = tiles[k] || {};
    const next = Object.assign({}, cur, o, { src: 'user' });
    next.res = (next.res || []).filter((x, i, a) => a.indexOf(x) === i && RES_TER[x] === next.terrain);
    if (!next.city) delete next.city;
    delete next.mk;
    if (!next.bld) next.bld = null;
    tiles[k] = next;
  }
  function brushOn(id, x) {
    if (id === 'city') return x.terrain === 'city';
    if (id === 'cloud') return x.stored && !!x.cloud;
    if (id === 'monument') return !!x.monument;
    if (id === 'water' && x.cloud) return false;
    if (TER_B.indexOf(id) >= 0) return x.stored && x.terrain === id && !x.bld && !x.res.length;
    if (RES_B.indexOf(id) >= 0) return x.res.indexOf(id) >= 0;
    return x.bld === id;
  }
  function applyBrush(c, r, id, on) {
    if (!inPaint(c, r) || BRUSH.indexOf(id) < 0) return;
    const x = cellAt(c, r), k = key(c, r);
    if (id === 'city') {
      // a city inside the area is one of the planned cities (own territory 3×3)
      if (on) { upsertCity(c, r, 'user', { side: 'me' }); storeTile(c, r, { terrain: 'field', res: [], bld: null }); selectCity(c, r); }
      else { unselectCity(c, r); removeCity(c, r); delete S().tiles[k]; }
      return;
    }
    if (x.terrain === 'city') { if (!ui.paint || ui.paint.first) toast('City tile – use the City brush to remove it'); return; }
    if (id === 'monument') { if (on) storeTile(c, r, { terrain: 'field', res: [], bld: 'monument' }); else delete S().tiles[k]; return; }
    if (TER_B.indexOf(id) >= 0) {
      if (!on) { delete S().tiles[k]; return; } // back to "not marked" (= Empty)
      const bld = x.bld && BASE[x.bld] === id && !(x.bld === 'farm' && id !== 'field') ? x.bld : null;
      storeTile(c, r, { terrain: id, res: x.res.filter(q => RES_TER[q] === id), bld: x.bld === 'other' && id === x.terrain ? x.other : bld });
      return;
    }
    if (RES_B.indexOf(id) >= 0) {
      const ter = RES_TER[id];
      if (!on) {
        storeTile(c, r, { terrain: x.terrain, res: x.res.filter(q => q !== id), bld: (id === 'crop' && x.bld === 'farm') || (id === 'ore' && x.bld === 'mine') ? null : x.bld === 'other' ? x.other : x.bld });
        return;
      }
      let res = x.terrain === ter ? x.res.filter(q => q !== 'crop' && q !== 'fruit' && q !== 'ore' && q !== 'animal' && q !== 'fish') : [];
      res = res.concat(id);
      // Market / workshops need a tile without resource; Farm needs Crop, Mine needs Metal
      let bld = x.terrain === ter ? x.bld : null;
      if (bld && ((UNIQUE.indexOf(bld) >= 0 && id !== 'crop') || (bld === 'farm' && id !== 'crop') || (bld === 'lumber' && id === 'animal'))) bld = null; // a Market / workshop may stand on Crop
      storeTile(c, r, { terrain: ter, res, bld: bld === 'other' ? x.other : bld });
      return;
    }
    // buildings
    if (!on) { storeTile(c, r, { terrain: x.terrain, res: x.res, bld: null }); return; }
    if (UNIQUE.indexOf(id) >= 0) {
      const T = terr(), own = T.ownerOf(c, r);
      if (own >= 0 && !T.implicit) {
        for (const y of areaCells(T)) {
          if (y.bld === id && !(y.c === c && y.r === r) && T.ownerOf(y.c, y.r) === own) {
            storeTile(y.c, y.r, { terrain: y.terrain, res: y.res, bld: null });
            toast(nm(id) + ' moved – one per city');
          }
        }
      }
    }
    const ter = BASE[id];
    const res = id === 'farm' ? ['crop'] : id === 'mine' ? ['ore'] : UNIQUE.indexOf(id) >= 0 && x.res.indexOf('crop') >= 0 ? ['crop'] : [];
    storeTile(c, r, { terrain: ter, res, bld: id });
  }
  function paintAt(c, r) {
    if (!ui.paint || !ui.brush) return;
    const k = key(c, r);
    if (ui.paint.done.has(k) || !inPaint(c, r)) return;
    ui.paint.done.add(k);
    applyBrush(c, r, ui.brush, ui.paint.on);
    ui.paint.first = false;
  }
  function suggestAll() {
    let n = 0;
    for (const x of areaCells()) {
      if (x.stored) continue;
      let t = suggest(x.c, x.r);
      if (t === 'ocean' || t === 'cloud') t = 'water';
      if (TER_B.indexOf(t) < 0 || t === 'city') continue;
      S().tiles[key(x.c, x.r)] = Object.assign({}, S().tiles[key(x.c, x.r)] || {}, { terrain: t, res: [], bld: null, src: 'user' });
      n++;
    }
    return n;
  }

  function fitTiles(list, maxTile) {
    if (!list.length || !PP.board || !PP.grid || !PP.board.visibleRect) return;
    const pts = [];
    for (const [c, r] of list) PP.grid.corners(c, r).forEach(p => pts.push(p));
    const xs = pts.map(p => p.x), ys = pts.map(p => p.y);
    const w = Math.max(...xs) - Math.min(...xs), h = Math.max(...ys) - Math.min(...ys);
    const vr = PP.board.visibleRect(), g = S().grid, tw = Math.max(Math.abs(g.ux + g.vx), Math.abs(g.ux - g.vx)) || 1;
    let s = Math.min((vr.w - 16) / w, (vr.h - 30) / h);
    if (maxTile) s = Math.min(s, maxTile / tw);
    const cx = (Math.max(...xs) + Math.min(...xs)) / 2, cy = (Math.max(...ys) + Math.min(...ys)) / 2;
    PP.board.setView({ s, x: vr.x + vr.w / 2 - cx * s, y: vr.y + vr.h / 2 - cy * s });
  }
  function fitRegion() {
    const A = area(); if (!A.n) return;
    const l = [...A.owner.keys()].map(k => k.split(',').map(Number));
    if (ui.step === 1) fringe(A).forEach(q => l.push(q));
    fitTiles(l, 150);
  }
  function fitPlan() {
    const p = curPlan(planResult()); if (!p) { fitRegion(); return; }
    const l = [];
    if (ui.onlyForest && forestSteps(p).length) { forestSteps(p).forEach(s => l.push([s.c, s.r])); fitTiles(l, 150); return; }
    p.tiles.forEach(t => l.push([t.c, t.r]));
    p.buildings.forEach(b => { l.push([b.c, b.r]); (b.producers || []).forEach(q => l.push([q.c, q.r])); });
    if (!l.length) { fitRegion(); return; }
    fitTiles(l, 150);
  }
  const mode = {
    label: 'Market', icon: '🏪',
    mapAct: () => mapActHtml(),
    mapActClick,
    hint() {
      if (ui.step === 1 || !selCities().length) {
        if (ui.borders) { const A = area(), ek = editCityK(A), ci = A.cities.find(x => key(x.c, x.r) === ek); return ci ? 'Editing ' + cityName(ci, ci.k) + ': tap a tile to give it to ' + cityName(ci, ci.k) + ' · tap one of its tiles to remove it' : ''; }
        return selCities().length ? 'Tap more cities · tap a city again: 3×3 → 5×5 → off' : 'Tap your own cities (the city tile) to plan their Markets';
      }
      if (ui.step === 2) return ui.brush ? 'Tap or drag: ' + nm(ui.brush) + ' (tap again = remove)' : 'Pick a brush, then tap tiles';
      if (ui.onlyForest) return '🪓 Only the forests to cut down (🔥 = burn) · tap 🪓 again for the whole plan';
      return 'Tap a Market or a city to see what belongs to it · tap any tile for details';
    },
    onEnter() {
      const m = M();
      ui.onlyForest = false;
      if (!m.touched && !m.cities.length) knownOwn().forEach(q => { if (cityEntry(q.c, q.r)) m.cities.push({ c: q.c, r: q.r, rad: 1 }); });
      if (!selCities().length) ui.step = 1; else if (ui.step === 1 && !ui.entered) ui.step = 2;
      ui.entered = true;
    },
    onExit() { ui.paint = null; ui.edit = null; },
    wantsDrag(t) {
      if (!t) return false;
      if (ui.step === 1 || !selCities().length) {
        if (!ui.borders) return false;
        const A = area(), ek = editCityK(A), ci = A.cities.find(x => key(x.c, x.r) === ek);
        if (!ci) return false;
        return A.ownerOf(t.c, t.r) === ci.k || Math.max(Math.abs(t.c - ci.c), Math.abs(t.r - ci.r)) <= ci.rad || NB.some(([dc, dr]) => A.ownerOf(t.c + dc, t.r + dr) === ci.k);
      }
      return ui.step === 2 && !!ui.brush && inPaint(t.c, t.r);
    },
    onDrag(phase, t) {
      if (ui.step === 1 || !selCities().length) {
        if (phase === 'start') { const A = area(), ek = editCityK(A), ci = A.cities.find(x => key(x.c, x.r) === ek); ui.edit = { want: !(ci && A.ownerOf(t.c, t.r) === ci.k), done: new Set() }; }
        if (ui.edit && t && (phase === 'start' || phase === 'move' || phase === 'end')) {
          const k = key(t.c, t.r);
          if (!ui.edit.done.has(k)) { ui.edit.done.add(k); editBorder(t.c, t.r, ui.edit.want); }
        }
        if (phase === 'end' || phase === 'cancel') { ui.edit = null; PP.app.commit(); return; }
        PP.board.redraw();
        return;
      }
      if (ui.step === 2) {
        if (phase === 'start') { ui.paint = { on: !brushOn(ui.brush, cellAt(t.c, t.r)), done: new Set(), first: true }; paintAt(t.c, t.r); }
        else if (phase === 'move' && ui.paint) paintAt(t.c, t.r);
        else if (ui.paint) { if (phase === 'end') paintAt(t.c, t.r); ui.paint = null; PP.app.commit(); return; }
        PP.board.redraw();
      }
    },
    onTap(t) {
      if (ui.step === 1 || !selCities().length) {
        if (ui.borders) {
          const A0 = area(), sel = A0.cities.find(x => x.c === t.c && x.r === t.r);
          if (sel) { ui.editCity = key(sel.c, sel.r); toast('Editing ' + cityName(sel, sel.k)); PP.app.commit(); return; } // tap a city: edit that one
          const r = editBorder(t.c, t.r, null);
          const A = area(), ci = A.cities.find(x => key(x.c, x.r) === ui.editCity);
          if (r === 'far') toast('Too far from ' + cityName(ci, ci.k) + ' – pick another city above');
          else if (r === 'city') tapCity(t.c, t.r);
          else if (r === 'none') toast('Tap a city first');
          else if (r === 'ok' && ci) toast(A.ownerOf(t.c, t.r) === ci.k ? '→ ' + cityName(ci, ci.k) : 'Removed from ' + cityName(ci, ci.k), 1200);
        } else tapCity(t.c, t.r);
        PP.app.commit(); return;
      }
      if (ui.step === 2 && ui.brush) {
        if (!inPaint(t.c, t.r)) { toast('Outside the cities’ territories – change them in ① Cities'); return; }
        ui.paint = null;
        applyBrush(t.c, t.r, ui.brush, !brushOn(ui.brush, cellAt(t.c, t.r)));
        // v44: say whose tile it is
        { const A = area(), o = A.ownerOf(t.c, t.r), ci = A.cities[o];
          toast((ci ? cityName(ci, o) : inRing(t.c, t.r) ? 'Border Growth ring' : 'Outside the territories') + ' · ' + t.c + '/' + t.r, 1200); }
        PP.app.commit(); return;
      }
      ui.sel = ui.sel && ui.sel.c === t.c && ui.sel.r === t.r ? null : (inArea(t.c, t.r) ? { c: t.c, r: t.r } : null);
      PP.app.refresh();
    },
    renderPanel,
    drawUnder,
    drawOver,
  };

  // ------------------------------------------------------------------ drawer
  let cssDone = false;
  function injectCss() {
    if (cssDone) return; cssDone = true;
    const s = document.createElement('style');
    s.textContent = `
.mk{font-size:14px;line-height:1.35}
.mk h3{margin:12px 0 4px;font-size:14px;color:var(--muted,#9aa5c8);font-weight:700;text-transform:none}
.mk svg{vertical-align:middle}
.mk .mk-steps{display:flex;gap:3px;background:var(--bg,#12172b);border-radius:10px;padding:3px;margin:0 0 6px}
.mk .mk-steps button{flex:1;min-width:0;border:0;background:none;color:var(--muted,#9aa5c8);font-weight:650;font-size:13px;padding:6px 2px;border-radius:8px;line-height:1.1;min-height:36px;white-space:nowrap;touch-action:manipulation}
.mk .mk-steps button.on{background:var(--panel2,#252e52);color:var(--text,#e8ecf8)}
.mk .mk-steps button:disabled{opacity:.4}
.mk .mk-pal{display:grid;grid-template-columns:repeat(10,minmax(0,1fr));gap:3px;margin:0 0 2px}
.mk .mk-pal button{border:1px solid var(--line,#33406e);background:var(--panel2,#252e52);color:var(--text,#e8ecf8);border-radius:8px;padding:2px 0 1px;font-size:clamp(7.5px,2.45vw,9.5px);letter-spacing:-.4px;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:0;min-width:0;min-height:44px;overflow:hidden;white-space:nowrap;touch-action:manipulation}
.mk .mk-pal button span{font-size:18px;line-height:1.1;height:22px;display:flex;align-items:center}
.mk .mk-pal button.on{border-color:var(--gold,#ffd166);background:rgba(255,209,102,.22);color:var(--gold,#ffd166);box-shadow:inset 0 0 0 1px var(--gold,#ffd166)}
.mk .mk-pal button.t{background:rgba(155,211,90,.08)}
.mk .mk-pal button.rs{background:rgba(255,255,255,.04);border-style:dashed}
.mk .mk-pal button.b{background:rgba(76,201,240,.08)}
.mk .mk-pal button.on{background:rgba(255,209,102,.22)}
.mk .mk-plan{margin:6px 0 2px;min-height:46px;font-size:15px;border-radius:12px}
.mk .mk-pal button.go{background:var(--accent,#4cc9f0);color:#08121f;border-color:transparent;font-weight:800;font-size:11px}
.mk .mk-btn{display:block;width:100%;border:0;border-radius:11px;padding:10px;margin:6px 0;font-weight:700;background:var(--panel2,#252e52);color:var(--text,#e8ecf8);min-height:44px;font-size:14px}
.mk .mk-btn.pri{background:var(--accent,#4cc9f0);color:#08121f}
.mk .mk-btn.ok{background:rgba(6,214,160,.18);color:var(--ok,#06d6a0);border:1px solid rgba(6,214,160,.5)}
.mk .mk-btn.sm{display:inline-block;width:auto;min-height:36px;padding:6px 12px;font-size:13px;margin:4px 4px 4px 0}
.mk .mk-note{color:var(--muted,#9aa5c8);font-size:12.5px;margin:6px 0}
.mk .mk-key{display:flex;align-items:center;gap:8px;background:var(--panel2,#252e52);border:1px solid var(--line,#33406e);border-radius:12px;padding:6px 6px 6px 10px;min-height:44px}
.mk .mk-key .t{flex:1;min-width:0;font-size:13.5px;line-height:1.3}
.mk .mk-key .t b.g{color:var(--gold,#ffd166);font-size:16px}
.mk .mk-key .t small{color:var(--muted,#9aa5c8);font-size:12px}
.mk .mk-key .mk-btn{margin:0;width:auto;min-height:40px;padding:6px 10px;font-size:13px;flex:none}
.mk .mk-spin{display:inline-block;width:16px;height:16px;border:2.5px solid rgba(255,255,255,.25);border-top-color:var(--accent,#4cc9f0);border-radius:50%;animation:mkspin .8s linear infinite;vertical-align:-3px;margin-right:6px}
@keyframes mkspin{to{transform:rotate(360deg)}}
.mk .mk-alts{display:grid;grid-template-columns:1fr 1fr;gap:5px;margin:6px 0 2px}
.mk .mk-alt:disabled{opacity:.6;cursor:default}
.mk .mk-alt{flex:1;min-width:0;border:1px solid var(--line,#33406e);background:var(--panel2,#252e52);color:var(--text,#e8ecf8);border-radius:10px;padding:4px 3px;font-size:11.5px;line-height:1.25;text-align:center;min-height:44px}
.mk .mk-alt b{display:block;font-size:13.5px;color:var(--gold,#ffd166)}
.mk .mk-alt.on{border-color:var(--accent,#4cc9f0);box-shadow:inset 0 0 0 1px var(--accent,#4cc9f0)}
.mk .mk-opts{display:grid;grid-template-columns:1fr 1fr;gap:5px;margin:4px 0}
.mk .mk-opt{display:flex;align-items:center;gap:6px;border:1px solid var(--line,#33406e);background:var(--bg,#12172b);color:var(--muted,#9aa5c8);border-radius:10px;padding:5px 7px;min-height:42px;text-align:left;font-size:12.5px;line-height:1.2}
.mk .mk-opt .bx{flex:none;width:18px;height:18px;border-radius:5px;border:2px solid var(--line,#33406e);display:flex;align-items:center;justify-content:center;font-size:12px;font-weight:900}
.mk .mk-opt.on{color:var(--text,#e8ecf8);border-color:rgba(76,201,240,.6);background:rgba(76,201,240,.1)}
.mk .mk-opt.on .bx{background:var(--accent,#4cc9f0);border-color:var(--accent,#4cc9f0);color:#08121f}
.mk .mk-opt small{display:block;color:var(--muted,#9aa5c8);font-size:11px}
.mk .mk-opt.wide{grid-column:1/-1}
.mk .mk-city{display:flex;align-items:center;gap:7px;margin:10px 0 0;padding:5px 2px 3px;border-bottom:2px solid var(--cc,#4cc9f0);font-size:14px}
.mk .mk-city .dot{width:12px;height:12px;border-radius:50%;background:var(--cc,#4cc9f0);flex:none}
.mk .mk-city .nmx{flex:1;min-width:0;font-weight:700;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.mk .mk-city .inc{color:var(--gold,#ffd166);font-weight:700;white-space:nowrap}
.mk ol.mk-list{list-style:none;margin:2px 0 6px;padding:0}
.mk ol.mk-list li{display:flex;align-items:center;gap:7px;padding:5px 2px;border-bottom:1px solid rgba(255,255,255,.06);font-size:13px;min-height:32px}
.mk ol.mk-list li .no{flex:none;min-width:22px;height:22px;padding:0 3px;box-sizing:border-box;border-radius:11px;background:#ffd166;color:#1b1300;font-weight:800;font-size:11.5px;display:flex;align-items:center;justify-content:center}
.mk ol.mk-list li .no.ex{background:rgba(255,255,255,.18);color:var(--text,#e8ecf8)}
.mk ol.mk-list li .ic{font-size:17px;width:24px;text-align:center;flex:none;display:flex;justify-content:center}
.mk ol.mk-list li .tx{flex:1;min-width:0}
.mk ol.mk-list li .tx small{color:var(--muted,#9aa5c8)}
.mk ol.mk-list li .co{font-weight:700;white-space:nowrap}
.mk ol.mk-list li.sel{background:rgba(76,201,240,.12)}
.mk .mk-btn.on{box-shadow:inset 0 0 0 2px #ffb703;background:rgba(255,183,3,.15)}
.mk .mk-grow{margin:12px 0 4px;padding:10px;border:1px solid var(--line,#33406e);border-radius:12px;background:rgba(123,211,137,.05)}
.mk .gw-t{font-weight:800;margin-bottom:6px}
.mk .tc-order{display:flex;flex-wrap:wrap;align-items:center;gap:4px 6px;font-size:13px}
.mk .tc-order span{background:rgba(255,255,255,.06);border-radius:8px;padding:4px 8px}
.mk .tc-order i{font-style:normal;color:var(--muted,#9aa5c8)}
.mk .gw-menu{margin:6px 0;padding:8px 10px;border:1px solid var(--line,#33406e);border-radius:12px;background:rgba(255,255,255,.03)}
.mk .gw-mh{display:flex;align-items:center;justify-content:space-between;margin-bottom:6px}
.mk .gw-pick{display:flex;flex-wrap:wrap;gap:6px}
.mk .mk-ecity{display:flex;flex-wrap:wrap;align-items:center;gap:5px;margin:2px 0 6px}
.mk .mk-ecity span{color:var(--muted,#9aa5c8);font-size:12.5px;font-weight:700;margin-right:2px}
.mk .mk-ecity button{border:2px solid transparent;border-radius:9px;padding:6px 10px;background:var(--panel2,#252e52);color:var(--text,#e8ecf8);font-weight:800;font-size:13px;box-shadow:inset 4px 0 0 var(--cc)}
.mk .mk-ecity button.on{border-color:var(--cc);background:color-mix(in srgb,var(--cc) 25%,transparent)}
.mk .gw-prio{display:flex;gap:5px}
.mk .gw-prio button{flex:1;display:flex;flex-direction:column;align-items:center;gap:2px;border:1px solid rgba(255,255,255,.12);border-radius:10px;padding:7px 4px;background:var(--panel2,#252e52);color:var(--text,#e8ecf8);font-size:12.5px;min-width:0}
.mk .gw-prio button small{color:var(--muted,#9aa5c8);font-size:10.5px;text-align:center}
.mk .gw-prio button.on{border-color:var(--accent,#4cc9f0);background:rgba(76,201,240,.15)}
.mk .gw-pick button{display:flex;align-items:center;gap:6px;border:1px solid rgba(255,255,255,.12);border-left:4px solid var(--cc);border-radius:9px;padding:6px 9px;background:var(--panel2,#252e52);color:var(--text,#e8ecf8);font-weight:700;font-size:13px;opacity:.6}
.mk .gw-pick button.on{opacity:1}
.mk .gw-pick .bx{width:16px;height:16px;border-radius:4px;border:2px solid rgba(255,255,255,.4);display:inline-flex;align-items:center;justify-content:center;font-size:11px;line-height:1}
.mk .gw-pick button.on .bx{background:var(--accent,#4cc9f0);border-color:var(--accent,#4cc9f0);color:#08121f}
.mk .gw-sum{font-size:14.5px;line-height:1.45;margin:0 0 8px;padding:8px 10px;border-radius:10px;background:rgba(123,211,137,.12)}
.mk .gw-plus{color:#7bd389}
.mk .gw-card{margin:6px 0;padding:8px 10px;border-radius:10px;border:1px solid rgba(255,255,255,.08);border-left:5px solid var(--cc);background:rgba(255,255,255,.03)}
.mk .gw-card.skip{opacity:.72}
.mk .gw-h{display:flex;align-items:center;gap:7px;flex-wrap:wrap}
.mk .gw-h .dot{width:10px;height:10px;border-radius:50%;background:var(--cc);flex:none}
.mk .gw-v{margin-left:auto;font-weight:800;font-size:12.5px;padding:3px 9px;border-radius:9px;white-space:nowrap}
.mk .gw-card.take .gw-v{background:#1f8a4c;color:#eafff0}
.mk .gw-card.skip .gw-v{background:rgba(255,255,255,.13);color:var(--text,#e8ecf8)}
.mk .gw-d{margin-top:4px;font-size:13px}
.mk .gw-x{margin-top:3px;font-size:12.5px;color:var(--muted,#9aa5c8)}
.mk .gw-w{margin-top:3px;font-size:12px;color:#ffb703}
.mk .gw-warn{margin:8px 0;font-size:12.5px;color:#ffd58a;background:rgba(255,183,3,.08);border-radius:8px;padding:6px 8px}
.mk button.lnk{background:none;border:0;padding:0;color:#4cc9f0;text-decoration:underline;font:inherit;cursor:pointer}
.mk ol.mk-list li .ck{flex:none;width:24px;height:24px;border-radius:6px;border:2px solid rgba(255,255,255,.35);background:transparent;color:#0b0f1f;font-weight:900;font-size:14px;line-height:1;padding:0;cursor:pointer;display:flex;align-items:center;justify-content:center}
.mk ol.mk-list li.done .ck{background:#16a34a;border-color:#16a34a;color:#fff}
.mk ol.mk-list li.done{background:rgba(22,163,74,.18);box-shadow:inset 4px 0 0 #16a34a}
.mk ol.mk-list li.done .tx{opacity:.8}
.mk ol.mk-list li .bt{flex:none;background:#16a34a;color:#fff;font-weight:900;font-size:11px;border-radius:8px;padding:3px 7px;white-space:nowrap}
.mk .mk-prog{display:flex;align-items:center;gap:8px;font-size:12.5px;margin:2px 0 4px;color:var(--muted,#9aa5c8)}
.mk .mk-prog .bar{flex:none;width:90px;height:7px;border-radius:4px;background:rgba(255,255,255,.12);overflow:hidden}
.mk .mk-prog .bar i{display:block;height:100%;background:#16a34a}
.mk .mk-prog.all{color:#16a34a;font-weight:700}
.mk ol.mk-list li.none{color:var(--muted,#9aa5c8);font-size:12.5px}
.mk ol.mk-list li.tot{font-weight:700;border-bottom:0}
.mk ol.mk-list li.tot .co{color:var(--gold,#ffd166)}
.mk .mk-bd{font-size:12.5px;color:var(--muted,#9aa5c8);margin:4px 0;overflow-wrap:anywhere}
.mk .mk-bd b{color:var(--text,#e8ecf8)}
.mk .mk-cnt{display:flex;gap:5px;flex-wrap:wrap;margin:4px 0}
.mk .mk-cnt span{background:var(--bg,#12172b);border-radius:8px;padding:3px 7px;font-size:12px;display:inline-flex;align-items:center;gap:3px}
.mk .mk-cities{margin:6px 0}
.mk .mk-chips{display:flex;flex-direction:column;gap:5px;margin:4px 0 2px}
.mk .mk-chip{display:flex;align-items:center;gap:7px;border:1px solid var(--line,#33406e);border-left:4px solid var(--cc,#4cc9f0);background:var(--panel2,#252e52);border-radius:10px;padding:3px 4px 3px 8px;min-height:44px}
.mk .mk-chip .dot{width:12px;height:12px;border-radius:50%;background:var(--cc,#4cc9f0);flex:none}
.mk .mk-chip .nmx{flex:1;min-width:0;font-weight:700;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;line-height:1.15}
.mk .mk-chip .nmx small{display:block;font-weight:400;color:var(--muted,#9aa5c8);font-size:11.5px}
.mk .mk-chip .seg{display:flex;background:var(--bg,#12172b);border-radius:9px;padding:2px;flex:none}
.mk .mk-chip .seg button{border:0;background:none;color:var(--muted,#9aa5c8);font-weight:700;font-size:13px;min-height:36px;min-width:44px;border-radius:7px;touch-action:manipulation}
.mk .mk-chip .seg button.on{background:var(--cc,#4cc9f0);color:#08121f}
.mk .mk-chip .x{border:0;background:none;color:var(--muted,#9aa5c8);font-size:16px;min-width:40px;min-height:40px;flex:none;touch-action:manipulation}
.mk .mk-row{display:flex;flex-wrap:wrap}
.mk .mk-cities label{display:flex;align-items:center;gap:7px;margin:4px 0;font-size:12.5px;color:var(--muted,#9aa5c8)}
.mk .mk-cities .dot{width:12px;height:12px;border-radius:50%;flex:none}
.mk .mk-cities input{flex:1;min-width:0;background:var(--bg,#12172b);color:var(--text,#e8ecf8);border:1px solid var(--line,#33406e);border-radius:8px;padding:6px 8px;font-size:16px}
`;
    document.head.appendChild(s);
  }

  function stepsHtml() {
    const has = selCities().length > 0;
    return '<div class="mk-steps">' + [[1, '① Cities'], [2, '② What’s here'], [3, '③ Plan']].map(([s, l]) =>
      `<button data-step="${s}" class="${s === ui.step ? 'on' : ''}" ${s !== 1 && !has ? 'disabled' : ''}>${l}</button>`).join('') + '</div>';
  }
  const TAG = { best: 'Best', fewer: 'Fewer steps', cheaper: 'Cheaper', fast: 'Fastest payback (ROI)' };
  function keyLine(p, res) {
    if (res && res.pending) return '<span class="mk-spin"></span><b>Searching all plans…</b> <small>exact search</small>';
    if (res && res.tooBig) return '<b>Too many possibilities</b> <small>– see below</small>';
    if (!p) return '<b>No income possible</b> <small>– check the tiles and the options below</small>';
    const mk = plural(p.marketCount, 'market', 'markets');
    if (!p.actions) return `${TAG[p.tag]}: <b class="g">${p.income} ★/turn</b> · ${mk} <small>– all built already</small>`;
    return `${TAG[p.tag]}: <b class="g">${p.income} ★/turn</b> · ${mk} · cost <b>${p.cost}&nbsp;★</b> · ${plural(p.actions, 'step', 'steps')}`;
  }

  function renderPanel(el) {
    injectCss();
    const m = M();
    if (!selCities().length) ui.step = 1;
    let h = '<div class="mk">';
    if (ui.step === 1) {
      const A = area(), nEd = Object.keys(m.edits).length;
      h += `<div data-peek="cities:${ui.borders ? 'b' : 'c'}:${A.cities.length}">${stepsHtml()}`;
      // v32: Edit borders right at the top
      if (A.cities.length) h += `<button class="mk-btn ${ui.borders ? 'pri' : ''}" data-a="borders" style="margin:6px 0 4px">${ui.borders ? '✓ Done editing borders' : '✏️ Edit city borders'}</button>`;
      if (ui.borders && A.cities.length) {
        const ek = editCityK(A);
        h += '<div class="mk-ecity"><span>Editing:</span>' + A.cities.map(ci => { const k = key(ci.c, ci.r);
          return `<button data-ecity="${k}" class="${k === ek ? 'on' : ''}" style="--cc:${cityCol(ci.k)}">${esc(cityName(ci, ci.k))}</button>`; }).join('') + '</div>';
      }
      h += chipsHtml(A);
      if (nEd) h += `<div class="mk-row"><button class="mk-btn sm" data-a="resetBorders">↺ Reset borders (${nEd})</button></div>`;
      const ko = knownOwn();
      if (ko.length) h += `<button class="mk-btn sm" data-a="addKnown">＋ Add my ${plural(ko.length, 'city', 'cities')}: ${ko.slice(0, 4).map(q => esc(cityLabel(q.c, q.r))).join(', ')}${ko.length > 4 ? ' …' : ''}</button>`;
      if (A.cities.length) h += `<button class="mk-btn pri" data-step="2">Next: ② What’s here ▶</button>`;
      h += '</div>';
    } else if (ui.step === 2) {
      const bt = id => `<button data-brush="${id}" class="${ui.brush === id ? 'on' : ''} ${TER_B.indexOf(id) >= 0 ? 't' : RES_B.indexOf(id) >= 0 ? 'rs' : 'b'}" title="${esc(nm(id))}"><span>${iconHtml(id, 21)}</span>${BRUSH_LABEL[id]}</button>`;
      // v33: brushes grouped by what belongs together (16 = two rows of 8), the Plan button as a wide row below
      h += `<div data-peek="tiles">${stepsHtml()}<div class="mk-pal">` + PAL_ORDER.map(bt).join('') + '</div>' +
        '<button class="mk-btn pri mk-plan" data-step="3">▶ Show the plan</button></div>' +
        // v37: the explanation is below the collapsed panel (Less shows only up to "Show the plan")
        (autoStats().unsure ? `<div class="mk-note" style="margin:3px 0 0;color:#ffb703">⚠ ${plural(autoStats().unsure, 'tile', 'tiles')} with ? – please check</div>` : '');
      h += citiesHtml();
      h += countsHtml();
      h += '<button class="mk-btn sm" data-a="suggest">🪄 Suggest terrain from screenshot</button><button class="mk-btn sm" data-a="clearTiles">Clear marks in territories</button>';
    } else {
      const res = planResult(), p = curPlan(res);
      const added = p && p.actions && planAdded(p);
      h += `<div data-peek="plan:${ui.alt}:${ui.onlyForest ? 'f' : ''}:${ui.sel ? ui.sel.c + '/' + ui.sel.r : ''}:${res && res.pending ? 'p' : 'd'}">${stepsHtml()}<div class="mk-key"><div class="t">${keyLine(p, res)}</div>` +
        (p && p.actions ? `<button class="mk-btn ${added ? 'ok' : 'pri'}" data-a="${added ? 'fromPlan' : 'toPlan'}">${added ? '✓ In plan' : '➕ Cost plan'}</button>` : '') + '</div>';
      // v32: "only forests to cut down" right at the top (off by default; also the 🪓 in the bar on the map)
      const fo = forestSteps(p);
      if (fo.length) h += `<button class="mk-btn ${ui.onlyForest ? 'on' : ''}" data-a="onlyForest" style="margin:6px 0">${ui.onlyForest ? '🗺️ Show the whole plan again' : '🪓 Show which forests to cut down'}</button>`;
      if (p) h += altsHtml(res);
      h += (ui.sel && p ? selLine(p, ui.sel.c, ui.sel.r) : '') + '</div>';
      h += '<h3>Allowed actions</h3><div class="mk-opts">' + OPT_KEYS.map(k => {
        const [ic, lab, sub] = OPT_LABEL[k];
        return `<button class="mk-opt ${m.opts[k] ? 'on' : ''} ${k === 'produce' ? 'wide' : ''}" data-opt="${k}"><span class="bx">${m.opts[k] ? '✓' : ''}</span><span>${ic} ${lab}${sub ? `<small>${sub}</small>` : ''}</span></button>`;
      }).join('') + '</div>';
      h += '<h3>Workshops you can build</h3><div class="mk-opts">' + WS_KEYS.map(k => {
        const it = ITEM(k) || {}, tech = it.tech && PP.TECH && PP.TECH[it.tech] ? PP.TECH[it.tech].name : TECH_OF_WS[k];
        return `<button class="mk-opt ${m.opts[k] ? 'on' : ''}" data-opt="${k}" title="Uncheck if you don't have ${esc(tech)} – existing ${esc(nm(k))}s still count"><span class="bx">${m.opts[k] ? '✓' : ''}</span><span>${iconHtml(k, 16)} ${esc(nm(k))}<small>${esc(tech)}</small></span></button>`;
      }).join('') + '</div>';
      if (!WS_KEYS.some(k => m.opts[k])) h += '<p class="mk-note" style="margin-top:2px">No new workshops</p>';
      h += '<h3>Resources you can use</h3><div class="mk-opts">' + RES_KEYS.map(k => {
        const it = ITEM(k) || {}, tech = it.tech && PP.TECH && PP.TECH[it.tech] ? PP.TECH[it.tech].name : RES_TECH[k], lab = k === 'fruit' ? 'Harvest Fruit' : k === 'fish' ? 'Catch Fish' : 'Hunt Animal';
        const why = k === 'fruit' ? 'without it, Empty tiles with Fruit stay blocked' : k === 'fish' ? 'Fish only count for the population a city can reach (Border Growth)' : 'without it, an Animal is lost when its forest is used (no Hunt first)';
        return `<button class="mk-opt ${m.opts[k] ? 'on' : ''}" data-opt="${k}" title="Uncheck if you don't have ${esc(tech)} – ${esc(why)}"><span class="bx">${m.opts[k] ? '✓' : ''}</span><span>${iconHtml(k === 'hunt' ? 'animal' : k, 16)} ${lab}<small>${esc(tech)}</small></span></button>`;
      }).join('') + '</div>';
      if (p) h += growthHtml(res);
      if (p) h += techHtml(res);
      const au = autoStats();
      if (au.unsure) h += `<p class="mk-note" style="color:#ffb703">⚠ ${plural(au.unsure, 'tile', 'tiles')} with ? – check in ②</p>`;
      if (p) h += planHtml(p, res);
      else if (res && res.tooBig) h += `<p class="mk-note" style="color:var(--warn,#ffaa00)">⚠ Too many possibilities – mark the tiles in ② or plan fewer cities</p>`;
      else if (res && !res.pending) h += '<p class="mk-note">No Market can earn anything here</p>';
      if (res && !res.pending && !res.altPending) h += proofHtml(res);
      if (res && res.large && res.altPending) h += '<p class="mk-note"><span class="mk-spin"></span>Still improving…</p>';
    }
    h += '</div>';
    el.innerHTML = h;
    el.firstChild.addEventListener('click', onClick);
    el.firstChild.addEventListener('change', onChange);
  }
  // v29: what the screenshot detection did for the planned tiles
  function autoStats() {
    let auto = 0, unsure = 0;
    for (const x of areaCells()) { if (x.terrain === 'city' || x.stored) continue; if (x.auto) auto++; if (x.unsure) unsure++; }
    return { auto, unsure };
  }
  function chipsHtml(A) {
    if (!A.cities.length) return '';
    return '<div class="mk-chips">' + A.cities.map((ci, k) => {
      const n = [...A.owner.values()].filter(o => o === k).length - 1, at = ci.c + ',' + ci.r;
      const gi = ci.rad === 1 ? growVerdict(at) : null;
      const gtxt = gi ? (gi.take ? ` · <b style="color:#7bd389">🌱 Grow: +${gi.gain} ★</b>` : ' · 👥 Pop. Growth') : '';
      return `<div class="mk-chip" style="--cc:${cityCol(k)}"><span class="dot"></span><span class="nmx">${esc(cityName(ci, k))}<small>${ci.c}/${ci.r} · ${n} tiles${gtxt}</small></span>` +
        `<span class="seg"><button data-rad="${at},1" class="${ci.rad === 1 ? 'on' : ''}">3×3</button><button data-rad="${at},2" class="${ci.rad === 2 ? 'on' : ''}">5×5</button></span>` +
        `<button class="x" data-unsel="${at}" title="Remove" aria-label="Remove ${esc(cityName(ci, k))}">✕</button></div>`;
    }).join('') + '</div>';
  }
  function citiesHtml() {
    const T = area();
    return '<div class="mk-cities">' + T.cities.map((ci, k) => {
      const n = [...T.owner.values()].filter(o => o === k).length - 1;
      return `<label><span class="dot" style="background:${cityCol(k)}"></span><input data-city="${ci.c},${ci.r}" value="${esc(ci.name || '')}" placeholder="${esc(cityName(ci, k))} – name" enterkeyhint="done"><span>${ci.c}/${ci.r} · ${n} tiles</span></label>`;
    }).join('') + '</div>';
  }
  function onChange(ev) {
    const inp = ev.target.closest('input[data-city]'); if (!inp) return;
    const [c, r] = inp.dataset.city.split(',').map(Number);
    const ci = upsertCity(c, r, 'user');
    ci.name = inp.value.trim();
    PP.app.commit();
  }
  function countsHtml() {
    const cells = areaCells(), n = {};
    let un = 0;
    for (const x of cells) {
      n[x.terrain] = (n[x.terrain] || 0) + 1;
      x.res.forEach(q => { n[q] = (n[q] || 0) + 1; });
      if (x.bld && x.bld !== 'other') n[x.bld] = (n[x.bld] || 0) + 1;
      if (!x.stored) un++;
    }
    const order = ['city', 'field', 'forest', 'mountain', 'water', 'crop', 'ore', 'fruit', 'animal', 'fish'].concat(BLD_B);
    return '<div class="mk-cnt">' + order.filter(k => n[k]).map(k => `<span title="${esc(nm(k))}">${iconHtml(k, 15)} ${n[k]}</span>`).join('') + (un ? `<span title="Not marked – counted as Empty">❔ ${un} unmarked</span>` : '') + '</div>';
  }
  // v32: the plan numbers its cities in board order, the map (colours, "City A/B/…") in the order they were selected →
  // translate by the city's position, so a building always has the colour and name of its own city
  function pk(p, k) {
    if (!p._ak) { const A = area(); p._ak = p.groups.map((g, i) => { if (g.city.implicit) return i; const j = A.cities.findIndex(ci => ci.c === g.city.c && ci.r === g.city.r); return j >= 0 ? j : i; }); }
    return p._ak[k] != null ? p._ak[k] : k;
  }
  const pCol = (p, k) => cityCol(pk(p, k));
  const groupName = (p, k) => { const g = p.groups[k]; return g ? cityName(g.city, pk(p, k)) : 'City'; };
  function selLine(p, c, r) {
    const x = cellAt(c, r), T = terr(), own = T.ownerOf(c, r);
    let h = `<div class="mk-bd" style="margin:6px 2px 0">📍 <b>${c}/${r}</b> · ${iconHtml(x.terrain === 'city' ? 'city' : x.terrain, 15)} ${esc(x.terrain === 'city' ? cityName(T.cities[own] || {}, own) : nm(x.terrain))}${x.res.map(q => ' + ' + esc(nm(q))).join('')}${x.bld ? ' + ' + esc(nm(x.other || x.bld)) : ''}`;
    if (x.terrain !== 'city') h += own >= 0 ? ` <small>· territory of <b style="color:${cityCol(own)}">${esc(cityName(T.cities[own], own))}</b></small>` : ' <small>· outside the territories</small>';
    h += ': ';
    const tp = p.tiles.find(t => t.c === c && t.r === r);
    const b = p.buildings.find(v => v.c === c && v.r === r);
    if (b && b.item === 'market') h += '<small style="color:#ffd166">✨ highlighted: this Market, its workshops and their producers</small> · ';
    if (x.terrain === 'city' && own >= 0) h += '<small style="color:#ffd166">✨ highlighted: everything this city builds and uses</small> · ';
    if (tp) {
      const all = tp.steps.every(isDone);
      h += (all ? `<b style="color:${BUILT_COL}">✓ BUILT</b> · ` : '') + tp.steps.map(s => `${isDone(s) ? '✅' : ''}<b>${s.no}</b> ${esc(stepName(s))}`).join(' → ') + (b ? ' · ' + bldText(b, p) : '');
    }
    else if (b) h += bldText(b, p);
    else {
      const ws = p.workshops.find(w => w.producers.some(q => q.c === c && q.r === r));
      h += ws ? 'counts for the ' + nm(ws.item) + ' at ' + ws.c + '/' + ws.r : 'not used by this plan';
    }
    return h + '</div>';
  }
  function bldText(b, p) {
    if (b.item === 'market') {
      const f = b.feeders.map(w => `${nm(w.item)} Lv${w.level}${w.city !== b.city && p.groups.length > 1 ? ' of ' + esc(groupName(p, w.city)) : ''}`).join(' + ');
      return `<b>Market</b> ${b.isNew ? '' : '(built) '}= <b>${b.income} ★/turn</b>${f ? ` <small>(${f}${b.capped ? ' = ' + b.raw + ', max. ' + CAP : ''})</small>` : ''}`;
    }
    const pn = { farm: ['Farm', 'Farms'], mine: ['Mine', 'Mines'], lumber: ['Lumber Hut', 'Lumber Huts'] }[PROD[b.item]];
    const nNew = b.producers.filter(q => q.isNew).length;
    let h = `<b>${nm(b.item)}</b> ${b.isNew ? '' : '(built) '}<small>Lv${b.level}: ${plural(b.level, pn[0], pn[1])}${nNew ? ', ' + nNew + ' new' : ''}</small>`;
    const other = b.feeds.map(i => p.markets[i]).filter(mm => mm.city !== b.city);
    if (other.length) h += ` <small>· ${b.feeds.length > other.length ? 'also ' : ''}feeds ${other.map(mm => esc(groupName(p, mm.city)) + '’s Market').join(', ')}</small>`;
    return h;
  }
  const doneKey = s => s.c + ',' + s.r + ':' + s.item;
  const isDone = s => !!M().done[doneKey(s)];
  let doneSeq = Date.now(); // marks store when they were set → "undo" takes back the latest
  // what the ✓ Built bar on the map acts on: the tapped tile (all its steps), else the next step that is not built yet
  function actTarget(p) {
    if (!p || !p.steps.length) return null;
    if (ui.sel) { // a tapped tile: only that tile – never silently something else
      const tp = p.tiles.find(t => t.c === ui.sel.c && t.r === ui.sel.r);
      return tp ? { steps: tp.steps, c: tp.c, r: tp.r, tile: true } : { steps: [], c: ui.sel.c, r: ui.sel.r, tile: true, none: true };
    }
    const nx = (ui.onlyForest ? forestSteps(p) : p.steps).find(s => !isDone(s));
    return nx ? { steps: [nx], c: nx.c, r: nx.r, tile: false } : null;
  }
  const actOnSel = () => { const p = curPlan(planResult()); return !!(p && ui.sel && p.tiles.some(t => t.c === ui.sel.c && t.r === ui.sel.r)); };
  function mapActHtml() {
    if (ui.step !== 3) return '';
    const res = planResult(), p = curPlan(res);
    if (!p || !p.steps.length) return '';
    // v32: left a 🪓 toggle "only forests to cut down" (undo is the ↶ in the header now)
    const fo = forestSteps(p), only = ui.onlyForest && fo.length > 0, list = only ? fo : p.steps;
    const n = list.length, nDone = list.filter(isDone).length;
    const undo = fo.length ? `<button class="ma-undo ${only ? 'on' : ''}" data-ma="forest" title="${only ? 'Show the whole plan again' : 'Show which forests to cut down'}" aria-label="${only ? 'Show the whole plan again' : 'Show which forests to cut down'}" aria-pressed="${only}">🪓</button>` : '';
    const t = actTarget(p), cnt = only ? `${nDone}/${n} forests` : `${nDone}/${n} built`;
    if (!t) return undo + (only ? `<span class="ma-tx">🎉 <b>All ${n} forests cut down</b><br><small>Tap 🪓 to see the whole plan again</small></span>`
      : `<span class="ma-tx">🎉 <b>All ${n} steps built</b><br><small>The Markets earn ${p.income} ★/turn</small></span>`);
    if (t.none) return undo + `<span class="ma-tx">📍 <b>${t.c}/${t.r}</b>: nothing to build here<br><small>Tap a numbered tile · tap this tile again for the next step</small></span><button class="ma-ok" disabled>✓ Built</button>`;
    const all = t.steps.every(isDone), s0 = t.steps[0];
    const nos = t.steps.map(s => `<span class="no" style="background:${pCol(p, s.city)}">${s.no}</span>`).join('');
    const what = t.steps.map(s => esc(stepName(s))).join(' → ');
    return undo + `<span class="ma-tx">${t.tile ? '' : '<small>Next:</small> '}${nos}${what}<br><small>${s0.c}/${s0.r} · ${cnt}</small></span>` +
      (all ? '<button class="ma-un" data-ma="toggle">Not built</button>' : '<button class="ma-ok" data-ma="toggle">✓ Built</button>');
  }
  function mapActClick(ev) {
    const b = ev.target.closest('button[data-ma]'); if (!b || b.disabled) return;
    const m = M(), p = curPlan(planResult());
    if (b.dataset.ma === 'forest') { ui.onlyForest = !ui.onlyForest; ui.sel = null; PP.app.refresh(); requestAnimationFrame(fitPlan); return; }
    const t = actTarget(p); if (!t || t.none) return;
    const all = t.steps.every(isDone);
    t.steps.forEach(s => { if (all) delete m.done[doneKey(s)]; else m.done[doneKey(s)] = ++doneSeq; });
    if (t.tile && !all) ui.sel = null; // back to "Next step"
    PP.app.commit();
  }
  function planHtml(p, res) {
    const multi = p.groups.length > 1;
    let h = '<h3>Markets</h3>';
    for (const g of p.groups) {
      const col = pCol(p, g.k);
      if (multi || !g.city.implicit) h += `<div class="mk-city" style="--cc:${col}"><span class="dot"></span><span class="nmx">${esc(cityName(g.city, pk(p, g.k)))} <small style="color:var(--muted,#9aa5c8);font-weight:400">${g.city.implicit ? '' : g.city.c + '/' + g.city.r}</small></span><span class="inc">${g.income} ★/turn</span></div>`;
      h += '<ol class="mk-list">';
      const list = g.markets.concat(g.workshops);
      if (!list.length) h += '<li class="none">No Market here – nothing with a level fits into this city’s territory.</li>';
      h += list.map(b => `<li data-go="${b.c},${b.r}" class="${ui.sel && ui.sel.c === b.c && ui.sel.r === b.r ? 'sel' : ''}"><span class="ic">${iconHtml(b.item, 19)}</span><span class="tx">${bldText(b, p)} <small>· ${b.c}/${b.r}${b.isNew ? ' · new' : ''}</small></span></li>`).join('');
      if (g.steps.length) h += `<li class="none">${plural(g.steps.length, 'step', 'steps')} in this territory · ${g.cost} ★</li>`;
      h += '</ol>';
    }
    if (p.steps.length) {
      const nDone = p.steps.filter(isDone).length, left = p.steps.filter(s => !isDone(s)).reduce((a, s) => a + s.cost, 0);
      // v32: no step list any more – progress here, ticking happens in the bar on the map
      h += '<h3>Building</h3>';
      h += nDone === p.steps.length
        ? '<div class="mk-prog all">🎉 All steps built – the Markets earn ' + p.income + ' ★/turn.</div>'
        : `<div class="mk-prog"><div class="bar"><i style="width:${Math.round(100 * nDone / p.steps.length)}%"></i></div><span>${nDone ? `<b>${nDone}</b> of ${p.steps.length} built · ${left} ★ to go` : `0 of ${p.steps.length} built`}</span></div>`;
      if (nDone) h += '<button class="mk-btn" data-a="clearDone" style="margin:0 0 6px">Clear all ✓ marks</button>';
    }
    h += `<ol class="mk-list"><li class="tot"><span class="tx">Total: ${p.income} ★/turn · ${plural(p.actions, 'step', 'steps')}${p.payback ? ' · pays off in ' + plural(p.payback, 'turn', 'turns') : ''}</span><span class="co">${p.cost} ★</span></li></ol>`;
    const owned = (S().build && Array.isArray(S().build.owned)) ? S().build.owned : [];
    const techs = [];
    p.steps.forEach(s => { const t = (ITEM(s.item) || {}).tech; if (t && owned.indexOf(t) < 0 && techs.indexOf(t) < 0) techs.push(t); });
    if (techs.length) h += '<p class="mk-note">Needs tech: ' + techs.map(t => '<b>' + esc((PP.TECH && PP.TECH[t] ? PP.TECH[t].name : t)) + '</b>').join(', ') + '</p>';
    if (p.actions) {
      const added = planAdded(p);
      h += `<button class="mk-btn ${added ? 'ok' : 'pri'}" data-a="${added ? 'fromPlan' : 'toPlan'}">${added ? '✓ In the cost plan – tap to remove' : '➕ Add all ' + p.actions + ' steps to the cost plan'}</button>`;
    } else h += '<p class="mk-note">Everything is already built – the Markets earn this now.</p>';
    return h;
  }
  const sameStep = (q, s) => q.c === s.c && q.r === s.r && q.item === s.item && q.src === 'market';
  function planAdded(p) {
    const pl = placements();
    return p.steps.length > 0 && p.steps.every(s => pl.some(q => sameStep(q, s)));
  }
  function addToPlan(p) {
    const b = build();
    b.placements = placements().filter(q => q.src !== 'market'); // replaces an earlier Market plan
    for (const s of p.steps) {
      const g = p.groups[s.city], ce = g && !g.city.implicit ? cityEntry(g.city.c, g.city.r) : null;
      const e = { id: uid(), c: s.c, r: s.r, item: s.item, src: 'market' };
      if (ce) e.city = ce.id;
      b.placements.push(e);
    }
  }
  function onClick(ev) {
    const b = ev.target.closest('button,[data-go]'); if (!b || b.disabled) return;
    const d = b.dataset, m = M();
    if (d.step) {
      ui.step = +d.step; ui.sel = null; ui.onlyForest = false; if (ui.step !== 1) ui.borders = false;
      PP.app.refresh();
      requestAnimationFrame(ui.step === 3 ? fitPlan : fitRegion);
      return;
    }
    if (d.brush) { ui.brush = ui.brush === d.brush ? null : d.brush; PP.app.refresh(); return; }
    if (d.alt) { ui.alt = d.alt === 'best' ? 0 : d.alt; ui.sel = null; PP.app.refresh(); requestAnimationFrame(fitPlan); return; }
    if (d.opt) { m.opts[d.opt] = !m.opts[d.opt]; ui.alt = 0; PP.app.commit(); return; }
    if (d.tech) { const b = S().build || (S().build = {}); if (!Array.isArray(b.owned)) b.owned = []; const i = b.owned.indexOf(d.tech); if (i >= 0) b.owned.splice(i, 1); else b.owned.push(d.tech); PP.app.commit(); return; }
    if (d.ecity) { ui.editCity = d.ecity; PP.app.refresh(); return; }
    if (d.gprio) {
      M().growPrio = d.gprio;
      if (growth && growth.state === 'done' && growth.rechoose && growth.sig === cacheSig) growth.rechoose(growPrio()); // instant
      PP.app.commit(); return;
    }
    if (d.gskip) { const sk = growSkip(); if (sk.has(d.gskip)) sk.delete(d.gskip); else sk.add(d.gskip); M().growSkip = [...sk]; PP.app.commit(); return; }
    if (d.done) { if (m.done[d.done]) delete m.done[d.done]; else m.done[d.done] = ++doneSeq; PP.app.commit(); return; }
    if (d.go) {
      const [c, r] = d.go.split(',').map(Number);
      ui.sel = ui.sel && ui.sel.c === c && ui.sel.r === r ? null : { c, r };
      PP.app.refresh(); return;
    }
    const a = d.a;
    if (d.rad) {
      const [c, r, rad] = d.rad.split(',').map(Number), sc = selAt(c, r);
      if (sc) { sc.rad = rad; m.touched = true; ui.alt = 0; PP.app.commit(); requestAnimationFrame(fitRegion); }
      return;
    }
    if (d.unsel) {
      const [c, r] = d.unsel.split(',').map(Number);
      unselectCity(c, r);
      if (!selCities().length) ui.borders = false;
      PP.app.commit(); return;
    }
    if (a === 'borders') { ui.borders = !ui.borders; PP.app.refresh(); if (ui.borders) requestAnimationFrame(fitRegion); return; }
    if (a === 'resetBorders') { m.edits = {}; ui.alt = 0; PP.app.commit(); toast('Borders reset to 3×3 / 5×5'); return; }
    if (a === 'addKnown') {
      let n = 0;
      for (const q of knownOwn()) if (selectCity(q.c, q.r)) n++;
      PP.app.commit(); requestAnimationFrame(fitRegion);
      toast(n ? plural(n, 'city', 'cities') + ' added' : 'Nothing added'); return;
    }
    if (a === 'techMenu') { ui.techMenu = !ui.techMenu; PP.app.refresh(); return; }
    if (a === 'techAgain') { stopTech(); ui.techMenu = true; PP.app.refresh(); return; }
    if (a === 'tech') { ui.techMenu = false; startTech(); PP.app.refresh(); return; }
    if (a === 'growthMenu') { ui.growMenu = !ui.growMenu; PP.app.refresh(); return; }
    if (a === 'growthAgain') { stopGrowth(); ui.growMenu = true; PP.app.refresh(); return; }
    if (a === 'growth') { ui.growMenu = false; }
    if (a === 'growth') { const r = planResult(); if (r && r.best) { startGrowth(r); PP.app.refresh(); } return; }
    if (a === 'growthAll') { M().cities.forEach(sc => { sc.rad = 1; }); stopGrowth(); growthAuto = true; ui.growMenu = false; M().touched = true; ui.alt = 0; PP.app.commit(); return; }
    if (a === 'growthApply') {
      const g = growthNow(); if (!g) return;
      const keys = new Set((g.cities || []).filter(c => c.take).map(c => c.key));
      M().cities.forEach(sc => { if (keys.has(key(sc.c, sc.r))) sc.rad = 2; });
      M().touched = true; ui.alt = 0; PP.app.commit(); toast(plural(keys.size, 'city', 'cities') + ' now planned with 5×5'); return;
    }
    if (a === 'proveMore') { const r = planResult(); if (r && r.best) { startProof(r, cacheSig, COST_MORE_SECS); PP.app.refresh(); } return; }
    if (a === 'suggest') { const n = suggestAll(); toast(n ? n + ' tiles suggested – please check them' : 'Nothing to suggest (all tiles marked)'); PP.app.commit(); return; }
    if (a === 'clearTiles') {
      for (const x of areaCells()) if (x.terrain !== 'city') delete S().tiles[key(x.c, x.r)];
      toast('Marks cleared (cities stay)'); PP.app.commit(); return;
    }
    if (a === 'onlyForest') { ui.onlyForest = !ui.onlyForest; ui.sel = null; PP.app.refresh(); requestAnimationFrame(fitPlan); return; }
    if (a === 'clearDone') { m.done = {}; PP.app.commit(); return; }
    if (a === 'toPlan') {
      const p = curPlan(planResult()); if (!p) return;
      addToPlan(p);
      PP.app.commit(); toast('Added ' + plural(p.actions, 'step', 'steps') + ' to the cost plan: ' + p.cost + ' ★'); return;
    }
    if (a === 'fromPlan') {
      const p = curPlan(planResult()); if (!p) return;
      build().placements = placements().filter(q => !p.steps.some(s => sameStep(q, s)));
      PP.app.commit(); toast('Removed from the cost plan'); return;
    }
  }

  // ------------------------------------------------------------------ canvas
  const scr = (x, y) => PP.board.toScreen(x, y);
  function diamondPath(ctx, c, r, shrink) {
    const p = PP.board.tileToScreen(c, r), k = shrink || 1;
    const pts = PP.grid.corners(c, r).map(q => scr(q.x, q.y));
    ctx.beginPath();
    pts.forEach((q, i) => { const x = p.x + (q.x - p.x) * k, y = p.y + (q.y - p.y) * k; if (i) ctx.lineTo(x, y); else ctx.moveTo(x, y); });
    ctx.closePath();
  }
  function emoji(ctx, s, x, y, size, alpha) {
    ctx.save();
    if (alpha != null) ctx.globalAlpha = alpha;
    ctx.font = `${Math.round(size)}px ${EMOJI_FONT}`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillStyle = '#fff';
    ctx.fillText(s, x, y + size * 0.06);
    ctx.restore();
  }
  function drawIcon(ctx, id, x, y, size, alpha) {
    if (hasIcon(id) && PP.icons.draw) {
      ctx.save();
      if (alpha != null) ctx.globalAlpha = alpha;
      let ok = true;
      try { PP.icons.draw(ctx, iconName(id), x, y, size); } catch (e) { ok = false; }
      ctx.restore();
      if (ok) return;
    }
    emoji(ctx, ICON[id] || '▪️', x, y, size * 0.86, alpha);
  }
  function disc(ctx, x, y, rad, fill, stroke, lw, dash) {
    ctx.beginPath(); ctx.arc(x, y, rad, 0, Math.PI * 2);
    if (fill) { ctx.fillStyle = fill; ctx.fill(); }
    if (stroke) { ctx.lineWidth = lw || 1.5; ctx.strokeStyle = stroke; if (dash) ctx.setLineDash(dash); ctx.stroke(); ctx.setLineDash([]); }
  }
  function numBadge(ctx, n, x, y, rad, bg, fg) {
    const s = String(n);
    ctx.font = `800 ${Math.round(rad * 1.2)}px system-ui,sans-serif`;
    const w = Math.max(rad * 2, ctx.measureText(s).width + rad * 0.9);
    ctx.beginPath();
    if (ctx.roundRect) ctx.roundRect(x - w / 2, y - rad, w, rad * 2, rad); else ctx.arc(x, y, rad, 0, Math.PI * 2);
    ctx.fillStyle = bg || '#ffd166'; ctx.fill(); ctx.lineWidth = 1.5; ctx.strokeStyle = 'rgba(0,0,0,.7)'; ctx.stroke();
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillStyle = fg || '#1b1300'; ctx.fillText(s, x, y + rad * 0.08);
  }
  function hexA(hex, a) { const n = parseInt(hex.slice(1), 16); return `rgba(${n >> 16},${(n >> 8) & 255},${n & 255},${a})`; }
  const EDGES = [[0, 1, 0, -1], [1, 2, 1, 0], [2, 3, 0, 1], [3, 0, -1, 0]];
  // per-city tint + outline (solid where the area ends, dashed between two cities)
  function drawTerritory(ctx, A, faint) {
    for (const [k, own] of A.owner) {
      const [c, r] = k.split(',').map(Number), col = cityCol(own);
      if (!faint) { diamondPath(ctx, c, r, 1); ctx.fillStyle = hexA(col, ui.step === 1 ? 0.2 : 0.08); ctx.fill(); }
      const pts = PP.grid.corners(c, r).map(q => scr(q.x, q.y));
      for (const [a, b, dc, dr] of EDGES) {
        const o = A.ownerOf(c + dc, r + dr);
        if (o === own) continue;
        ctx.beginPath(); ctx.moveTo(pts[a].x, pts[a].y); ctx.lineTo(pts[b].x, pts[b].y);
        if (o < 0) {
          ctx.lineWidth = 4; ctx.strokeStyle = 'rgba(0,0,0,.55)'; ctx.stroke();
          ctx.lineWidth = 2.2; ctx.strokeStyle = hexA(col, faint ? 0.7 : 1); ctx.stroke();
        } else {
          ctx.lineWidth = 2; ctx.strokeStyle = hexA(col, faint ? 0.55 : 0.9); ctx.setLineDash([6, 4]); ctx.stroke(); ctx.setLineDash([]);
        }
      }
    }
  }
  const TER_FILL = { monument: 'rgba(255,209,102,.35)', cloud: 'rgba(225,230,245,.55)', space: 'rgba(0,0,0,.55)', field: 'rgba(155,211,90,.22)', forest: 'rgba(30,120,50,.42)', mountain: 'rgba(150,150,160,.45)', water: 'rgba(20,60,140,.6)' };
  function drawUnder(ctx) {
    const A = area();
    if (!A.n) return;
    const sz = PP.board.size();
    ctx.save();
    // dim everything outside the territories (screen rect clockwise, tiles counter-clockwise → holes with 'nonzero')
    ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, sz.h); ctx.lineTo(sz.w, sz.h); ctx.lineTo(sz.w, 0); ctx.closePath();
    const ringK = ui.step === 2 ? [...ringInfo().keys.keys()] : [];
    for (const k of [...A.owner.keys()].concat(ringK)) {
      const [c, r] = k.split(',').map(Number), pts = PP.grid.corners(c, r).map(q => scr(q.x, q.y));
      const cw = (pts[1].x - pts[0].x) * (pts[2].y - pts[0].y) - (pts[1].y - pts[0].y) * (pts[2].x - pts[0].x) > 0;
      const ord = cw ? [0, 3, 2, 1] : [0, 1, 2, 3];
      ord.forEach((q, i) => (i ? ctx.lineTo(pts[q].x, pts[q].y) : ctx.moveTo(pts[q].x, pts[q].y))); ctx.closePath();
    }
    ctx.fillStyle = ui.step === 1 ? 'rgba(6,9,22,.42)' : 'rgba(6,9,22,.55)'; ctx.fill('nonzero');
    if (ui.step === 1 && ui.borders) {
      const ek = editCityK(A), eci = A.cities.find(x => key(x.c, x.r) === ek);
      if (eci) {
        const col = cityCol(eci.k), seen = new Set();
        for (const [k, o] of A.owner) if (o === eci.k) { const [c, r] = k.split(',').map(Number); diamondPath(ctx, c, r, 0.96); ctx.fillStyle = hexA(col, 0.32); ctx.fill(); }
        // tiles it can take: inside its radius or next to its territory, not its own
        const tryAdd = (c, r) => { const k = key(c, r); if (seen.has(k) || A.ownerOf(c, r) === eci.k || isCityAt(c, r)) return; seen.add(k);
          diamondPath(ctx, c, r, 0.82); ctx.lineWidth = 2; ctx.strokeStyle = hexA(col, 0.9); ctx.setLineDash([4, 4]); ctx.stroke(); ctx.setLineDash([]); };
        for (let dr = -eci.rad; dr <= eci.rad; dr++) for (let dc = -eci.rad; dc <= eci.rad; dc++) tryAdd(eci.c + dc, eci.r + dr);
        for (const [k, o] of A.owner) if (o === eci.k) { const [c, r] = k.split(',').map(Number); NB.forEach(([dc, dr]) => tryAdd(c + dc, r + dr)); }
      }
      for (const k of Object.keys(M().edits)) {
        if (M().edits[k] !== 0 || !A.base.has(k)) continue;
        const [c, r] = k.split(',').map(Number);
        diamondPath(ctx, c, r, 0.86); ctx.lineWidth = 1.5; ctx.strokeStyle = 'rgba(255,120,120,.85)'; ctx.setLineDash([4, 4]); ctx.stroke(); ctx.setLineDash([]);
      }
    }
    if (ui.step === 2) {
      // Space (outside the map) inside a radius: black, thin grey edge – never part of a territory
      for (const k of spaceKeys()) {
        const [c, r] = k.split(',').map(Number);
        diamondPath(ctx, c, r, 0.94); ctx.fillStyle = 'rgba(0,0,0,.6)'; ctx.fill();
        ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(200,200,220,.35)'; ctx.setLineDash([2, 3]); ctx.stroke(); ctx.setLineDash([]);
      }
      // the Border Growth ring: a bit darker than the territory, dashed light-green edge
      for (const x of ringCells()) {
        diamondPath(ctx, x.c, x.r, 1); ctx.fillStyle = 'rgba(6,9,22,.3)'; ctx.fill();
        diamondPath(ctx, x.c, x.r, 0.9);
        if (x.stored || (x.auto && !x.unsure)) { ctx.globalAlpha = x.stored ? 0.8 : 0.45; ctx.fillStyle = TER_FILL[x.monument ? 'monument' : x.cloud ? 'cloud' : x.terrain] || TER_FILL.water; ctx.fill(); ctx.globalAlpha = 1; }
        ctx.lineWidth = 1.6; ctx.strokeStyle = x.unsure && !x.stored ? 'rgba(255,183,3,.9)' : RING_COL; ctx.setLineDash([5, 4]); ctx.stroke(); ctx.setLineDash([]);
      }
      for (const x of areaCells(A)) {
        if (x.terrain === 'city') continue;
        diamondPath(ctx, x.c, x.r, 0.94);
        if (!x.stored) {
          if (x.auto && !x.unsure) { ctx.globalAlpha = 0.6; ctx.fillStyle = TER_FILL[x.monument ? 'monument' : x.cloud ? 'cloud' : x.terrain] || TER_FILL.water; ctx.fill(); ctx.globalAlpha = 1; }
          ctx.lineWidth = x.unsure ? 1.8 : 1.2; ctx.strokeStyle = x.unsure ? 'rgba(255,183,3,.9)' : 'rgba(255,255,255,.45)';
          ctx.setLineDash([3, 3]); ctx.stroke(); ctx.setLineDash([]); continue;
        }
        ctx.fillStyle = TER_FILL[x.monument ? 'monument' : x.cloud ? 'cloud' : x.terrain] || TER_FILL.water; ctx.fill();
        ctx.lineWidth = 1.4; ctx.strokeStyle = 'rgba(255,255,255,.55)'; ctx.stroke();
      }
    }
    drawTerritory(ctx, A, ui.step === 3);
    if (ui.step === 3) {
      const p = curPlan(planResult());
      if (p && !ui.onlyForest) {
        for (const m of p.markets) { diamondPath(ctx, m.c, m.r, 0.98); ctx.fillStyle = hexA(pCol(p, m.city), 0.45); ctx.fill(); }
        for (const w of p.workshops) { const o = A.ownerOf(w.c, w.r); diamondPath(ctx, w.c, w.r, 0.92); ctx.globalAlpha = 0.3; ctx.fillStyle = o >= 0 ? cityCol(o) : pCol(p, w.city || 0); ctx.fill(); ctx.globalAlpha = 1; }
      }
    }
    ctx.restore();
  }
  // v31: the Border Growth verdict right below each city's name – drawn last, so nothing of the plan covers it
  function drawGrowBadges(ctx, D, u, big, small) {
    if (!(ui.step === 3 || ui.step === 1)) return;
    if (!D || !D.pill || !growthNow()) return;
    const T = area(), fs = small ? clamp(u * 0.17, 9, 11) : clamp(u * 0.2, 9, 13);
    T.cities.forEach(ci => {
      const gi = ci.rad === 1 ? growVerdict(key(ci.c, ci.r)) : null; if (!gi) return;
      const q = PP.board.tileToScreen(ci.c, ci.r), R = big * (small ? 0.42 : 0.66);
      const gt = gi.take ? '🌱 Grow · +' + gi.gain + ' ★/turn' : '👥 Pop. Growth', gy = q.y + R + fs * 0.8 + fs * 1.5, gf = fs * 0.95;
      D.pill(ctx, q.x, gy, gt, gi.take ? 'rgba(31,138,76,.97)' : 'rgba(70,76,100,.95)', gf);
      ctx.save(); ctx.font = `bold ${gf}px system-ui,sans-serif`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillStyle = gi.take ? '#eafff0' : '#d6dbea'; ctx.fillText(gt, q.x, gy + 1); ctx.restore();
    });
  }
  function drawCities(ctx, D, u, big, small) {
    const T = area();
    const fs = small ? clamp(u * 0.17, 9, 11) : clamp(u * 0.2, 9, 13);
    T.cities.forEach((ci, k) => {
      const q = PP.board.tileToScreen(ci.c, ci.r), R = big * (small ? 0.42 : 0.66);
      disc(ctx, q.x, q.y, R, 'rgba(10,14,30,.75)', cityCol(k), small ? 2 : 2.4);
      drawIcon(ctx, 'city', q.x, q.y, R * 1.45);
      const name = cityName(ci, k) + (ui.step === 1 ? ' · ' + (ci.rad === 2 ? '5×5' : '3×3') : ''), y = q.y + R + fs * 0.8;
      if (D && D.pill) {
        D.pill(ctx, q.x, y, name, hexA(cityCol(k), 0.9), fs);
        ctx.save(); ctx.font = `bold ${fs}px system-ui,sans-serif`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
        ctx.fillStyle = '#0b0f1f'; ctx.fillText(name, q.x, y + 1); ctx.restore();
        // v29: Border Growth worth it for this city?
      }
    });
  }
  function drawOver(ctx, D) {
    const t = PP.board.tileScreenSize(), u = clamp(t.h, 14, 90);
    const sz = PP.board.size(), vis = q => q.x > -60 && q.y > -60 && q.x < sz.w + 60 && q.y < sz.h + 60;
    const big = clamp(u * 0.5, 11, 34);
    if (ui.step === 1 || !selCities().length) {
      ctx.save();
      // known cities that are not selected: dashed ring = tap target
      const seen = new Set();
      const ring = (c, r, me) => {
        const k = key(c, r); if (seen.has(k) || selAt(c, r) && isCityAt(c, r)) return; seen.add(k);
        const q = PP.board.tileToScreen(c, r); if (!vis(q)) return;
        const R = clamp(u * 0.42, 10, 28);
        disc(ctx, q.x, q.y, R, me ? 'rgba(76,201,240,.22)' : 'rgba(255,255,255,.12)', 'rgba(0,0,0,.6)', 4);
        disc(ctx, q.x, q.y, R, null, me ? 'rgba(76,201,240,.95)' : 'rgba(255,255,255,.9)', 2, [5, 4]);
      };
      S().cities.forEach(ci => { if (ci && isCityAt(ci.c, ci.r)) ring(ci.c, ci.r, ci.side === 'me'); });
      detectedList().forEach(d => ring(d.c, d.r, sideOf(detColor(d)) === 'me'));
      drawCities(ctx, D, u, big);
      drawGrowBadges(ctx, D, u, big);
      ctx.restore();
      return;
    }
    ctx.save();
    if (ui.step === 2) {
      for (const k of spaceKeys()) {
        const [c, r] = k.split(',').map(Number), q = PP.board.tileToScreen(c, r);
        if (vis(q)) drawIcon(ctx, 'space', q.x, q.y, big * 0.5, 0.6);
      }
      for (const x of areaCells().concat(ringCells())) {
        if (x.terrain === 'city') continue;
        if (!x.stored) {
          const q = PP.board.tileToScreen(x.c, x.r); if (!vis(q)) continue;
          if (x.unsure) {
            disc(ctx, q.x, q.y, big * 0.42, 'rgba(40,28,0,.82)', '#ffb703', 1.5);
            ctx.save(); ctx.font = `bold ${Math.round(big * 0.58)}px system-ui,sans-serif`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
            ctx.fillStyle = '#ffd166'; ctx.fillText('?', q.x, q.y + 1); ctx.restore();
          } else if (x.auto && x.terrain !== 'field') drawIcon(ctx, x.cloud ? 'cloud' : x.terrain, q.x, q.y, big * 0.7, 0.75);
          // resources the detection is sure about
          (x.res || []).forEach((rs, i) => {
            const rx = q.x + big * (0.5 + i * 0.5), ry = q.y + big * 0.3;
            disc(ctx, rx, ry, big * 0.28, 'rgba(10,14,30,.7)', 'rgba(255,255,255,.55)', 1, [3, 2]);
            drawIcon(ctx, rs, rx, ry, big * 0.44, 0.9);
          });
          continue;
        }
        const q = PP.board.tileToScreen(x.c, x.r); if (!vis(q)) continue;
        if (x.bld) {
          const R = big * 0.62, U = UNIQUE.indexOf(x.bld) >= 0;
          disc(ctx, q.x, q.y, R, U ? 'rgba(40,30,5,.78)' : 'rgba(10,14,30,.65)', U ? '#ffd166' : 'rgba(255,255,255,.8)', 1.5);
          drawIcon(ctx, x.bld, q.x, q.y, big * 0.95);
        } else if (x.terrain !== 'field') drawIcon(ctx, x.monument ? 'monument' : x.cloud ? 'cloud' : x.terrain, q.x, q.y, big * 0.8, 0.95);
        x.res.forEach((rs, i) => {
          if ((rs === 'crop' && x.bld === 'farm') || (rs === 'ore' && x.bld === 'mine')) return;
          const rx = q.x + big * (0.55 + i * 0.5), ry = q.y + big * 0.32;
          disc(ctx, rx, ry, big * 0.3, 'rgba(10,14,30,.75)', 'rgba(255,255,255,.7)', 1);
          drawIcon(ctx, rs, rx, ry, big * 0.48);
        });
      }
      drawCities(ctx, D, u, big);
    } else {
      const res = planResult(), p = curPlan(res);
      drawCities(ctx, D, u, big, true);
      if (p) drawPlan(ctx, D, p, u, big);
      // the tile the ✓ Built button acts on: green outline with a glow (same green as the bar's edge)
      const t = p ? actTarget(p) : null;
      if (t && !t.none) {
        ctx.save(); diamondPath(ctx, t.c, t.r, 1.06);
        ctx.shadowColor = ACT_COL; ctx.shadowBlur = clamp(u * 0.3, 6, 14);
        ctx.lineWidth = clamp(u * 0.08, 3, 5.5); ctx.strokeStyle = ACT_COL; ctx.stroke(); ctx.restore();
      }
      drawGrowBadges(ctx, D, u, big, true);
    }
    if (ui.sel && !(ui.step === 3 && actOnSel())) { diamondPath(ctx, ui.sel.c, ui.sel.r, 1); ctx.lineWidth = 2.5; ctx.strokeStyle = '#fff'; ctx.setLineDash([4, 3]); ctx.stroke(); ctx.setLineDash([]); }
    ctx.restore();
  }
  // v32: steps that remove a forest (cut down / burn) – the "only forests" view at the start of a turn
  // (a Hunt on a forest that is cut down / burnt belongs to it: it has to happen first)
  const forestSteps = p => {
    if (!p) return [];
    const cut = new Set(p.steps.filter(s => s.item === 'clear' || s.item === 'burn').map(s => key(s.c, s.r)));
    return p.steps.filter(s => cut.has(key(s.c, s.r)) && (s.item === 'clear' || s.item === 'burn' || s.item === 'hunt'));
  };
  function drawForest(ctx, D, p, u, big) {
    const rad = clamp(u * 0.15, 6.5, 11), byTile = new Map();
    forestSteps(p).forEach(s => { const k = key(s.c, s.r); if (!byTile.has(k)) byTile.set(k, []); byTile.get(k).push(s); });
    const later = [];
    for (const [, st] of byTile) {
      const s0 = st[0], q = PP.board.tileToScreen(s0.c, s0.r), col = pCol(p, s0.city), done = st.every(isDone), R = big * 0.62;
      diamondPath(ctx, s0.c, s0.r, 0.94);
      if (done) { ctx.fillStyle = BUILT_FILL; ctx.fill(); ctx.lineWidth = clamp(u * 0.07, 2.5, 5); ctx.strokeStyle = BUILT_COL; ctx.stroke(); }
      else { ctx.fillStyle = hexA(col, 0.3); ctx.fill(); ctx.lineWidth = clamp(u * 0.08, 3, 5.5); ctx.strokeStyle = col; ctx.stroke(); }
      disc(ctx, q.x, q.y, R, done ? BUILT_DARK : 'rgba(10,14,30,.85)', done ? BUILT_COL : col, 2.5);
      emoji(ctx, st.some(x => x.item === 'burn') && !st.some(x => x.item === 'clear') ? '🔥' : '🪓', q.x, q.y, big * 0.75, done ? 0.55 : 1);
      later.push(() => numBadge(ctx, done ? '✓' : st.map(x => x.no).join('·'), q.x - R * 0.8, q.y - R * 0.9, rad * (done ? 1.2 : 1), done ? BUILT_COL : col, done ? '#fff' : '#0b0f1f'));
    }
    later.forEach(f => f());
  }
  const ACT_GLYPH = { destroy: '💥', fruit: '🍒', hunt: '🏹', plant: '🌱', clear: '🪓', burn: '🔥' };
  // v29: a tapped Market of the plan → { set of 'c,r' (Market, its workshops, their producers), market }
  function focusOf(p) {
    if (!p || !ui.sel) return null;
    const m = p.markets.find(q => q.c === ui.sel.c && q.r === ui.sel.r);
    if (!m) {
      // v33: a tapped city → everything of its territory that the plan builds or uses lights up
      const A = area(), k = A.cities.findIndex(ci => ci.c === ui.sel.c && ci.r === ui.sel.r);
      if (k < 0) return null;
      const F = new Set([key(ui.sel.c, ui.sel.r)]), mine = (c, r) => A.ownerOf(c, r) === k;
      p.tiles.forEach(t => { if (mine(t.c, t.r)) F.add(key(t.c, t.r)); });
      p.buildings.forEach(b => { if (mine(b.c, b.r)) F.add(key(b.c, b.r)); });
      p.workshops.forEach(w => { if (mine(w.c, w.r)) { F.add(key(w.c, w.r)); w.producers.forEach(pr => { if (mine(pr.c, pr.r)) F.add(key(pr.c, pr.r)); }); } });
      p.markets.forEach(q => { if (mine(q.c, q.r)) F.add(key(q.c, q.r)); });
      return { F, m: null, city: k };
    }
    const F = new Set([key(m.c, m.r)]);
    for (const f of m.feeders) {
      F.add(key(f.c, f.r));
      const w = p.workshops.find(q => q.c === f.c && q.r === f.r);
      if (w) w.producers.forEach(pr => F.add(key(pr.c, pr.r)));
    }
    return { F, m };
  }
  function drawPlan(ctx, D, p, u, big) {
    if (ui.onlyForest) { drawForest(ctx, D, p, u, big); return; }
    const foc = focusOf(p), dim = (c, r) => (foc && !foc.F.has(key(c, r)) ? 0.16 : 1);
    // v32: every building marker in the colour of the city whose territory it is in
    const TA = area(), colAt = (c, r, fb) => { const o = TA.ownerOf(c, r); return o >= 0 ? cityCol(o) : pCol(p, fb >= 0 ? fb : 0); };
    // workshop → counted producers (thin, dashed, workshop colour)
    for (const w of p.workshops) {
      const wp = PP.board.tileToScreen(w.c, w.r);
      for (const pr of w.producers) {
        const q = PP.board.tileToScreen(pr.c, pr.r);
        ctx.beginPath(); ctx.moveTo(wp.x, wp.y); ctx.lineTo(q.x, q.y);
        const on = foc && foc.F.has(key(w.c, w.r));
        ctx.lineWidth = clamp(u * (on ? 0.07 : 0.04), 1.2, on ? 4 : 2.4); ctx.strokeStyle = colAt(w.c, w.r, w.city); ctx.globalAlpha = foc ? (on ? 1 : 0.12) : 0.85; ctx.setLineDash([4, 3]); ctx.stroke(); ctx.setLineDash([]);
        ctx.globalAlpha = 1;
      }
    }
    // Market → workshops (thick, city colour)
    for (const m of p.markets) {
      const mp = PP.board.tileToScreen(m.c, m.r);
      ctx.globalAlpha = foc && (foc.m ? foc.m !== m : !foc.F.has(key(m.c, m.r))) ? 0.15 : 1;
      for (const w of m.feeders) {
        const wp = PP.board.tileToScreen(w.c, w.r);
        ctx.beginPath(); ctx.moveTo(mp.x, mp.y); ctx.lineTo(wp.x, wp.y);
        ctx.lineWidth = clamp(u * 0.16, 3, 9); ctx.strokeStyle = 'rgba(0,0,0,.6)'; ctx.stroke();
        ctx.lineWidth = clamp(u * 0.1, 2, 6); ctx.strokeStyle = pCol(p, m.city); ctx.stroke();
      }
    }
    ctx.globalAlpha = 1;
    const pill = (x, y, txt, bg, s) => { if (D && D.pill) D.pill(ctx, x, y, txt, bg, s); };
    const fs = clamp(u * 0.2, 9, 13), rad = clamp(u * 0.15, 6.5, 11);
    // producers that are used (existing or new)
    const prodSeen = new Set();
    for (const w of p.workshops) for (const pr of w.producers) {
      const k = key(pr.c, pr.r); if (prodSeen.has(k)) continue; prodSeen.add(k);
      if (p.tiles.some(t => t.c === pr.c && t.r === pr.r)) continue;
      const q = PP.board.tileToScreen(pr.c, pr.r);
      ctx.globalAlpha = dim(pr.c, pr.r);
      disc(ctx, q.x, q.y, big * 0.42, 'rgba(10,14,30,.6)', colAt(pr.c, pr.r, w.city), 1.8);
      drawIcon(ctx, pr.item, q.x, q.y, big * 0.62, ctx.globalAlpha);
      ctx.globalAlpha = 1;
    }
    for (const m of p.markets) { ctx.globalAlpha = dim(m.c, m.r); diamondPath(ctx, m.c, m.r, 0.98); ctx.lineWidth = 3; ctx.strokeStyle = pCol(p, m.city); ctx.stroke(); ctx.globalAlpha = 1; }
    // tiles with steps: final building (or 💥 if only destroyed); existing buildings that count: ✓
    const bAt = new Map(p.buildings.map(b => [key(b.c, b.r), b]));
    const later = [], pills = [];
    for (const t of p.tiles) {
      const q = PP.board.tileToScreen(t.c, t.r), col = pCol(p, t.city), b = bAt.get(key(t.c, t.r)), a = dim(t.c, t.r);
      const R = big * (b ? 0.7 : 0.5), allDone = t.steps.every(isDone);
      ctx.globalAlpha = a;
      if (allDone) { // built: the whole tile green with a strong outline
        // emerald fill + white diagonal hatching + white inner edge: nothing else on the map is hatched
        ctx.save(); diamondPath(ctx, t.c, t.r, 0.94); ctx.fillStyle = BUILT_FILL; ctx.fill(); ctx.clip();
        const hw = u * 1.2, step = Math.max(5, u * 0.14);
        ctx.beginPath(); for (let d = -hw; d <= hw; d += step) { ctx.moveTo(q.x + d - hw, q.y + hw); ctx.lineTo(q.x + d + hw, q.y - hw); }
        ctx.lineWidth = Math.max(1.2, u * 0.03); ctx.strokeStyle = 'rgba(255,255,255,.28)'; ctx.stroke(); ctx.restore();
        diamondPath(ctx, t.c, t.r, 0.94); ctx.lineWidth = clamp(u * 0.08, 3, 5.5); ctx.strokeStyle = BUILT_COL; ctx.stroke();
        diamondPath(ctx, t.c, t.r, 0.86); ctx.lineWidth = 1.5; ctx.strokeStyle = 'rgba(255,255,255,.8)'; ctx.stroke();
      }
      disc(ctx, q.x, q.y, R, allDone ? BUILT_DARK : 'rgba(25,30,55,.88)', allDone ? BUILT_COL : col, allDone ? 3 : 2.2, allDone ? null : [4, 2]);
      if (t.item) drawIcon(ctx, t.item, q.x, q.y, big * (b ? 1.0 : 0.72), a); else emoji(ctx, '💥', q.x, q.y, big * 0.6, a);
      ctx.globalAlpha = 1;
      const open = t.steps.filter(s => !isDone(s)), nos = open.map(s => s.no);
      if (a < 1) continue;
      // built (ticked) steps: green ✓ instead of the step numbers
      if (allDone) { later.push(() => numBadge(ctx, '✓', q.x - R * 0.8, q.y - R * 0.9, rad * 1.25, BUILT_COL, '#fff')); continue; }
      later.push(() => numBadge(ctx, nos.length > 2 ? nos[0] + '–' + nos[nos.length - 1] : nos.join('·'), q.x - R * 0.8, q.y - R * 0.9, rad, col, '#0b0f1f'));
      const gl = open.map(s => ACT_GLYPH[s.item]).filter(Boolean);
      if (gl.length) later.push(() => {
        const gs = clamp(u * 0.18, 9, 13), tx = gl.join('');
        ctx.save(); ctx.font = `${gs}px ${EMOJI_FONT}`;
        const wdt = ctx.measureText(tx).width + 6, gx = q.x + R * 0.95, gy = q.y - R * 0.55;
        ctx.beginPath(); if (ctx.roundRect) ctx.roundRect(gx - wdt / 2, gy - gs * 0.62, wdt, gs * 1.24, gs * 0.5); else ctx.rect(gx - wdt / 2, gy - gs * 0.62, wdt, gs * 1.24);
        ctx.fillStyle = 'rgba(0,0,0,.75)'; ctx.fill();
        ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillStyle = '#fff'; ctx.fillText(tx, gx, gy + 1);
        ctx.restore();
      });
    }
    for (const b of p.buildings) {
      const q = PP.board.tileToScreen(b.c, b.r), R = big * 0.7, a = dim(b.c, b.r);
      if (!b.isNew) {
        ctx.globalAlpha = a;
        disc(ctx, q.x, q.y, R, 'rgba(10,14,30,.7)', colAt(b.c, b.r, b.city), 2.2);
        drawIcon(ctx, b.item, q.x, q.y, big * 1.0, a);
        ctx.globalAlpha = 1;
        if (a === 1) later.push(() => numBadge(ctx, '✓', q.x - R * 0.8, q.y - R * 0.9, rad * 0.9, '#e8ecf8', '#0b6b4f'));
      }
      if (a < 1) continue;
      if (b.item === 'market') pills.push(() => pill(q.x, q.y + R + fs * 0.7, b.income + ' ★/turn', 'rgba(150,100,0,.97)', fs));
      else pills.push(() => pill(q.x, q.y + R + fs * 0.55, 'Lv' + b.level, 'rgba(6,120,90,.95)', fs * 0.92));
    }
    // the focused Market and everything that feeds it: glowing outlines on top
    if (foc) {
      ctx.save();
      for (const k of foc.F) {
        const [c, r] = k.split(',').map(Number), isM = foc.m ? c === foc.m.c && r === foc.m.r : c === ui.sel.c && r === ui.sel.r;
        diamondPath(ctx, c, r, isM ? 1.02 : 0.96);
        ctx.shadowColor = isM ? '#ffd166' : '#fff'; ctx.shadowBlur = clamp(u * 0.3, 6, 16);
        ctx.lineWidth = isM ? 3.5 : 2.2; ctx.strokeStyle = isM ? '#ffd166' : 'rgba(255,255,255,.95)'; ctx.stroke();
      }
      ctx.restore();
    }
    later.forEach(f => f());
    pills.forEach(f => f());
  }

  if (PP.modes && PP.modes.register) PP.modes.register('market', mode);
  PP.market.ui = ui;
  PP.market.plan = () => planResult();
  PP.market.cellAt = cellAt;
  PP.market.territoryOfArea = () => terr();
  PP.market.area = grow => area(grow);
  PP.market.popReach = (c, r) => { const A = area(), ci = A.cities.find(q => q.c === c && q.r === r); return ci ? popReach(A, ci) : null; };
  PP.market.tapCity = (c, r) => { tapCity(c, r); PP.app.commit(); };
  PP.market.selectCity = (c, r, rad) => { const x = selectCity(c, r, rad); PP.app.commit(); return x; };
  PP.market.unselectCity = (c, r) => { unselectCity(c, r); PP.app.commit(); };
  PP.market.editBorder = (c, r, want) => { const x = editBorder(c, r, want == null ? null : want); PP.app.commit(); return x; };
  PP.market.setBorders = on => { ui.borders = !!on; PP.app.refresh(); };
  PP.market.setStep = s => { ui.step = s; ui.onlyForest = false; PP.app.refresh(); };
  PP.market.setBrush = b => { ui.brush = b; PP.app.refresh(); };
  PP.market.paint = (c, r, id, on) => { applyBrush(c, r, id, on !== false); PP.app.commit(); };
  PP.market.setOpts = o => { Object.assign(M().opts, o); PP.app.commit(); };
  PP.market.fitPlan = () => fitPlan();
})((typeof window !== 'undefined' ? window : globalThis).PP);
