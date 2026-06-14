# =============================================================================
# Bm-m3-enumerate.sage  --  Reproduce CHL's r=16 M_3 (210)+(120) enumeration.
#
# Independently reproduces the first half of Conner-Harper-Landsberg's
# R_(M_3) >= 17 computation (arXiv:1911.07981, S.9 lines 966-978): enumerate all
# Borel-fixed 7-planes E_110' in U*(x)sl(V)(x)W (72-dim) at r=16 and apply the
# (210) and (120) tests. CHL report exactly 8 seven-planes pass.
#
# METHOD (validated against CHL's M_2 hand-proof, which gives ranks {20,20,19}):
#   - Build M_3 directly (NOT T_sl3); decompose T(C*)^perp = U*(x)sl(V)(x)W
#     under sl(V)=sl_3. It is 9 copies of the 8-dim adjoint (hw space dim 9).
#   - Enumerate B-fixed 7-dim E_110' via upper sets of the positive-root poset
#     and Grassmannian charts with raising-operator closure (kashbari method,
#     ported from github.com/kashbari/BorderApolarity borderapolarity3.sage).
#   - For each chart's parametric family, form the full E_110 = T(C*) (+) E_110'
#     (dim 16 in A(x)B) and apply the DUAL skew (210)/(120) test:
#       (210) passes iff rank( E_110 (x) A -> Lambda^2(A) (x) B ) <= dim - r = 128.
#     The rank-drop locus over QQ[t] is computed by eliminating the rank-81
#     constant block (T(C*)(x)A) then taking minors (CHL S.10 row-reduction).
#
# USAGE (the stdout-only contract; see infodumps/Pl8.md S.1):
#   sager Sager/Bm-m3-enumerate.sage              # all upsets (heavy)
#   UPSETS=0,1,2 sager Sager/Bm-m3-enumerate.sage # selected upsets
#   The script prints a JSON object per surviving plane to stdout, and a final
#   JSON summary line. Capture stdout and persist via the host Write tool into
#   infodumps/Bm5-planes.json. The script MUST NOT self-write that file.
#
# Self-contained: inlines all Bm4 infra; does NOT load() any sibling file.
# =============================================================================

import os, sys, time, json
import builtins
from itertools import product as cart_product, combinations

def _pyint(x):
    """Coerce any Sage/RDF numeric weight value to a plain Python int.
    Weights here are integers but may be stored as RealDoubleElement."""
    f = float(x)
    return builtins.int(f + (0.5 if f >= 0 else -0.5))

# -----------------------------------------------------------------------------
# 1. sl_3 / M_n infrastructure (inlined from Sager/Bm-sl3-infra.sage, validated by Bm4)
# -----------------------------------------------------------------------------
def cartan_matrix_sln(n):
    C = matrix(QQ, n - 1, n - 1)
    for i in range(n - 1): C[i, i] = 2
    for i in range(n - 2):
        C[i + 1, i] = -1; C[i, i + 1] = -1
    return C

def _restrict_map(m, C, B):
    I = C.pivot_rows()
    return C[I, :].solve_right((m * B)[I, :])

def module_product(a, b):
    return [[xa.tensor_product(identity_matrix(QQ, yb.dimensions()[0], sparse=True)) +
             identity_matrix(QQ, xa.dimensions()[0], sparse=True).tensor_product(yb)
             for xa, yb in zip(s1, s2)] for s1, s2 in zip(a, b)]

def module_dual(a):
    return [[-x.transpose() for x in s] for s in a]

def simultaneous_eigenspaces(ms):
    n = ms[0].dimensions()[0]
    spaces = [(identity_matrix(n, sparse=True), ())]
    for m in ms:
        ns = []
        for B, wt in spaces:
            mr = _restrict_map(m, B, B)
            for ev, es in mr.eigenspaces_right():
                W = es.basis_matrix().transpose().sparse_matrix()
                ns.append((B * W, wt + (ev,)))
        spaces = ns
    return spaces

def weight_decomposition(a, C):
    eig = simultaneous_eigenspaces(a[2])
    tk = lambda wt: tuple(C.solve_right(vector(QQ, wt)).list())
    eig.sort(key=lambda p: tk(p[1]))
    M = {wt: V for V, wt in eig}
    tot = [(wt, V.dimensions()[1]) for V, wt in eig]
    wtg = DiGraph()
    for p in tot:
        wt, mult = p; B = M[wt]
        for i, x in enumerate(a[0]):
            wt2 = tuple((C[:, i] + vector(wt).column()).list())
            if wt2 in M:
                wtg.add_edge(p, (wt2, M[wt2].dimensions()[1]), _restrict_map(x, M[wt2], B))
    return {'M': M, 'tot': tot, 'C': C, 'a': a, 'wtg': wtg}

def build_Mn_tensor(n):
    """Matrix-mult tensor M_n in A(x)B(x)C with A=U*(x)V, B=V*(x)W, C=W*(x)U,
    plus the sl(V)=sl_n action on each factor. Returns (T, [rA,rB,rC], Cartan)."""
    Td = n^2
    T = [{} for _ in range(Td)]
    for i in range(n):
        for j in range(n):
            a = i * n + j
            for k in range(n):
                T[a][(j * n + k, k * n + i)] = QQ(1)
    T = [matrix(QQ, Td, Td, m, sparse=True) for m in T]
    def eij(i, j): return matrix(QQ, n, n, {(i, j): 1})
    X = [eij(i, i + 1) for i in range(n - 1)]
    Y = [eij(i + 1, i) for i in range(n - 1)]
    H = [eij(i, i) - eij(i + 1, i + 1) for i in range(n - 1)]
    gV = [X, Y, H]; gVs = [[-g.transpose() for g in gs] for gs in gV]
    Id = identity_matrix(QQ, n, sparse=True)
    rA = [[Id.tensor_product(g) for g in gs] for gs in gV]       # U*(x)V: act on V
    rB = [[g.tensor_product(Id) for g in gs] for gs in gVs]       # V*(x)W: act on V*
    rC = [[matrix(QQ, n^2, n^2, sparse=True) for _ in range(n - 1)] for _ in range(3)]
    return T, [rA, rB, rC], cartan_matrix_sln(n)

def build_Tperp_and_module(T, reps, C):
    """T(C*)^perp = U*(x)sl(V)(x)W and its sl(V) module structure for M_n."""
    rAB = module_product(reps[0], reps[1])
    rABd = module_dual(rAB)
    Tmat = matrix(QQ, [m.list() for m in T], sparse=True)
    Tp = Tmat.right_kernel_matrix().transpose().sparse_matrix()
    Mr = [[_restrict_map(m, Tp, Tp) for m in s] for s in rABd]
    return weight_decomposition(Mr, C), Tp

def TCstar_matrix(T, n):
    """T(C*) = U*(x)Id_V(x)W as columns in A(x)B (an (a*b) x a matrix)."""
    adim = n^2; cols = {}
    for alpha in range(adim):
        for (beta, gamma) in T[alpha].dict():
            cols[(alpha * adim + beta, gamma)] = T[alpha][beta, gamma]
    return matrix(QQ, adim * adim, adim, cols)

# -----------------------------------------------------------------------------
# 2. Upper-set enumeration + B-fixed (Borel) subspace generation (kashbari port)
# -----------------------------------------------------------------------------
def enumerate_upsets(mdata, subdim):
    M = mdata['M']; C = mdata['C']; tot = mdata['tot']; wtg = mdata['wtg']
    lp = MixedIntegerLinearProgram()
    for p in tot: lp.set_min(lp[p], 0); lp.set_max(lp[p], p[1])
    lp.add_constraint(lp.sum(lp[p] for p in tot) == subdim)
    for p in tot:
        for k in range(1, len(wtg.outgoing_edges(p)) + 1):
            for es in combinations(wtg.outgoing_edges(p), k):
                kd = block_matrix([[xr] for _, q, xr in es]).right_kernel().dimension()
                lp.add_constraint(lp[p] <= lp.sum(lp[q] for _, q, xr in es) + kd)
        for k in range(2, len(wtg.incoming_edges(p)) + 1):
            for es in combinations(wtg.incoming_edges(p), k):
                ck = block_matrix([[xr.transpose()] for q, _, xr in es]).right_kernel().dimension()
                lp.add_constraint(p[-1] - lp[p] <= lp.sum(q[-1] - lp[q] for q, _, xr in es) + ck)
    for p in tot:
        for _, q, x1 in wtg.outgoing_edges(p):
            for _, w, x2 in wtg.outgoing_edges(q):
                kd = (x2 * x1).right_kernel().dimension()
                lp.add_constraint(lp[p] <= lp[w] + kd)
    from sage.numerical.mip import MIPSolverException
    def dfs(i):
        if i == len(tot):
            yield [(p, int(lp.get_min(lp[p]))) for p in tot if int(lp.get_min(lp[p])) > 0]; return
        p = tot[i]
        for val in range(0, p[1] + 1):
            lp.set_min(lp[p], val); lp.set_max(lp[p], val)
            try:
                lp.solve()
                for up in dfs(i + 1): yield up
            except MIPSolverException: pass
        lp.set_min(lp[p], 0); lp.set_max(lp[p], p[1])
    return list(dfs(0))

def _minors_sparse(M, r):
    rnz = [i for i in range(M.dimensions()[0]) if not M[i].is_zero()]
    cnz = [j for j in range(M.dimensions()[1]) if not M[:, j].is_zero()]
    Ms = M[rnz, cnz]; a, b = Ms.dimensions(); out = []
    for ix in combinations(range(a), r):
        for jx in combinations([j for j in range(b) if not Ms[ix, j].is_zero()], r):
            out.extend([e for e in Ms[ix, jx].minors(r) if not e.is_zero()])
    return out

def charts_for_upset(up):
    """Yield (nzs, nvars) over all Grassmannian charts of an upset."""
    for nzs in cart_product(*[combinations(range(p[-1]), m) for p, m in up]):
        nvars = sum((nzi + 1) * (j - i - 1) for ((wt, f), m), nz in zip(up, nzs)
                    for nzi, (i, j) in enumerate(zip(nz, nz[1:] + (f,))))
        yield nzs, nvars

def hwv_for_chart(mdata, up, nzs, nvars):
    """Build the parametric E_110' (module coords, 72 x 7) for one chart, with
    raising-closure imposed. Returns (cur_matrix_over_quo_or_QQ, R, ideal_gens)
    or None if closure is inconsistent (ideal = (1))."""
    C = mdata['C']; reps = mdata['a']; M = mdata['M']; ssrank = len(reps[0])
    R = PolynomialRing(QQ, 't', nvars, implementation='singular') if nvars > 0 else QQ
    W = {}; pi = 0
    for q, nz in zip(up, nzs):
        p, m = q; wt, f = p
        t = matrix(R, f, m, sparse=True); t[nz, :] = identity_matrix(R, m, sparse=True)
        for j_idx, ks in enumerate(zip(nz, nz[1:] + (f,))):
            inc = (ks[1] - ks[0] - 1) * (j_idx + 1)
            if inc > 0:
                t[ks[0] + 1:ks[1], :j_idx + 1] = matrix(R, ks[1] - ks[0] - 1, j_idx + 1, R.gens()[pi:pi + inc]); pi += inc
        W[wt] = (M[p[0]] * t, m, f)
    cur = block_matrix([[B for B, m, f in W.values()]], subdivide=False)
    eqs = []
    for wt, v in W.items():
        B_mat, m, f = v
        def raisewt(wt, k): return tuple(aa + bb for aa, bb in zip(wt, C[:, k].list()))
        for k in range(ssrank):
            rwt = raisewt(wt, k); curd = W.get(rwt, None)
            if curd is not None:
                Braise, mr, fr = curd
                if mr == fr: continue
                mm = Braise.augment(reps[0][k] * B_mat); eqs.extend(_minors_sparse(mm, mr + 1))
            elif rwt in M:
                eqs.extend((reps[0][k] * B_mat).coefficients())
    if len(eqs) > 0:
        I = R.ideal(eqs)
        if R.one() in I: return None
        Rbar = R.quo(I)
        cur = cur.apply_map(Rbar, sparse=True, R=Rbar)
        return cur, Rbar, list(I.gens())
    return cur, R, []

# -----------------------------------------------------------------------------
# 3. The DUAL skew (210)/(120) test (validated on M_2: ranks {20,20,19})
# -----------------------------------------------------------------------------
def transpose_tensor(B, a):
    b = B.dimensions()[0] // a; Bp = {}
    for I, k in B.nonzero_positions():
        i, j = I // b, I % b; Bp[(j * a + i, k)] = B[I, k]
    return matrix(B.base_ring(), B.dimensions()[0], B.dimensions()[1], Bp)

def skew_210_map(B, a):
    """E_110 (x) A -> Lambda^2(A) (x) B. For v=e_i(x)e_j and basis e_k of A:
    e_k . v = (e_k ^ e_i) (x) e_j. Target dim binom(a,2)*b, domain S*a."""
    b = B.dimensions()[0] // a; S = B.dimensions()[1]; W = {}
    for I, s in B.nonzero_positions():
        i, j = I // b, I % b; v = B[I, s]
        for k in range(a):
            if k == i: continue
            p, q = (k, i) if k < i else (i, k); sign = 1 if k < i else -1
            ix = (binomial(q, 2) + p) * b + j; col = s * a + k
            W[(ix, col)] = W.get((ix, col), 0) + sign * v
    return matrix(B.base_ring(), binomial(a, 2) * b, S * a, W)

# ---- constant-block reduction (CHL S.10 "row reduction by constant entries") ----
# The skew (210) map of E_110 = [TCstar | E_110'] splits into a CONSTANT block
# skew(TCstar (x) A) (rank = a*a = 81 for M_3, computed ONCE) and a PARAMETRIC
# block skew(E_110' (x) A) (a*(r-a^2) = 63 cols). Total (210) rank = 81 + rank(P),
# where P = projection of the parametric columns onto the cokernel of the constant
# block. Pass iff total rank <= dim - r, i.e. rank(P) <= (dim - r) - 81.
# This shrinks the symbolic rank test from 324x144 to (324-81)x63 and removes the
# expensive R/I elimination of the 81 constant pivots.
def constant_skew_projection(TCstar, adim):
    """Return (proj_rows, const_rank) where proj_rows is a QQ matrix whose rows
    are a basis of the cokernel of skew(TCstar (x) A) (i.e. left-kernel of the
    constant block). Multiplying proj_rows * (parametric skew block) gives the
    projected residual whose rank adds to the constant rank."""
    Mc = skew_210_map(TCstar, adim)               # 324 x 81 over QQ
    const_rank = Mc.rank()
    coker = Mc.left_kernel_matrix()               # (324 - const_rank) x 324 over QQ
    return coker, const_rank

def is_unit_safe(e):
    try: return e.is_unit()
    except (NotImplementedError, AttributeError): return False

def sparse_elimination_by_units(M):
    """Kashbari: row/col reduce pivoting only on UNIT entries. Returns (M, r)."""
    M = copy(M); r = 0
    while True:
        if r == min(*M.dimensions()): break
        try:
            i, j = next((i + r, j + r) for i, j in M[r:, r:].nonzero_positions() if is_unit_safe(M[i + r, j + r]))
        except StopIteration:
            break
        M.swap_rows(r, i); M.swap_columns(r, j)
        M[r, :] *= M[r, r].inverse_of_unit()
        for ii in M.column(r)[r + 1:].nonzero_positions():
            ii += r + 1; M.add_multiple_of_row(ii, r, -M[ii, r])
        r += 1
    return M, r

def rankdrop_minors(M, r):
    """Generators of the ideal where rank(M) < r (i.e. all r x r minors vanish),
    after eliminating unit pivots (CHL S.10 row reduction; kashbari minors_ideal
    fast path). Returns: [] => rank < r identically (drops everywhere);
    [1] => rank >= r identically (never drops); else => proper minors ideal."""
    Rorig = M.base_ring()
    if M.is_zero() or r > min(*M.dimensions()):
        return []
    M, lo = sparse_elimination_by_units(M)
    if r <= lo:
        return [Rorig.one()]
    r2 = r - lo
    M = M[lo:, lo:]
    if M.is_zero():
        return []
    M = M[[i for i in range(M.dimensions()[0]) if not M[i].is_zero()],
          [j for j in range(M.dimensions()[1]) if not M[:, j].is_zero()]]
    if r2 > min(*M.dimensions()):
        return []
    return _minors_sparse(M, r2)

def test_210_120(E110, adim, r):
    """Apply both (210) and (120) tests to E_110 (full, dim r in A(x)B).
    Returns (verdict, pass_ideal_gens). verdict in:
      'fail'        : no parameter value passes (rank too high everywhere).
      'pass_all'    : passes for all parameters (rank <= dim-r identically).
      'pass_locus'  : passes exactly on the variety of pass_ideal_gens (a proper
                      subvariety, possibly empty -- check with the ring's 1-in-I)."""
    R = E110.base_ring()
    dom = E110.dimensions()[1] * adim     # 16*9 = 144
    need = dom - r                        # 128; pass iff rank <= need iff (need+1)-minors vanish
    M210 = skew_210_map(E110, adim)
    g210 = rankdrop_minors(M210, need + 1)
    one = (R.one() if R is not QQ else 1)
    drops210_everywhere = (g210 == [])
    never210 = (g210 == [one] or g210 == [1])
    if never210:
        return ('fail', None)
    M120 = skew_210_map(transpose_tensor(E110, adim), adim)
    g120 = rankdrop_minors(M120, need + 1)
    never120 = (g120 == [one] or g120 == [1])
    if never120:
        return ('fail', None)
    drops120_everywhere = (g120 == [])
    if drops210_everywhere and drops120_everywhere:
        return ('pass_all', [])
    # pass-locus = V(g210) cap V(g120). Combine.
    gens = [g for g in (g210 + g120) if g != 0 and g != one]
    if R is QQ:
        # numeric: both passed (not 'fail'), and no nontrivial gens => passes
        return ('pass_all', [])
    I = R.ideal(gens) if gens else R.ideal([])
    if R.one() in I:
        return ('fail', None)
    return ('pass_locus', [str(g) for g in I.gens()])

def test_210_120_fast(E110p_AB, adim, r, ctx):
    """Optimized (210)/(120) test via constant-block reduction (ctx precomputes
    the cokernel projectors and constant ranks for both orientations). E110p_AB is
    the 81 x (r-a^2) parametric matrix (E_110' embedded in A(x)B). Equivalent to
    test_210_120 but ~order-of-magnitude faster (small projected residual).

    rank_210 = const_rank_210 + rank(coker_210 * skew(E110p))  and pass iff
    rank_210 <= 144 - r, i.e. rank(residual) <= (144 - r) - const_rank_210."""
    R = E110p_AB.base_ring()
    a = adim
    # full domain of skew(E110): dim E110 = a^2 (TCstar) + (r - a^2) (E110') columns = r cols, * a.
    full_cols = r * a                              # 16*9 = 144
    need = full_cols - r                           # 128
    one = (R.one() if R is not QQ else 1)

    def side(E110p, coker, crank):
        # parametric skew block of just the E110' columns (324 x (r-a^2)*a)
        Sp = skew_210_map(E110p, a)
        P = coker * Sp                             # (324 - crank) x (r-a^2)*a over R
        need_res = need - crank                    # 128 - 81 = 47 ; pass iff rank(P) <= need_res
        return rankdrop_minors(P, need_res + 1)    # 48-minors

    g210 = side(E110p_AB, ctx['coker210'], ctx['crank210'])
    if g210 == [one] or g210 == [1]:
        return ('fail', None)
    drops210 = (g210 == [])
    # (120) side: transpose A<->B in the parametric block (constant block handled in ctx)
    E110p_T = transpose_tensor(E110p_AB, a)
    g120 = side(E110p_T, ctx['coker120'], ctx['crank120'])
    if g120 == [one] or g120 == [1]:
        return ('fail', None)
    drops120 = (g120 == [])
    if drops210 and drops120:
        return ('pass_all', [])
    gens = [g for g in (g210 + g120) if g != 0 and g != one]
    if R is QQ:
        return ('pass_all', [])
    I = R.ideal(gens) if gens else R.ideal([])
    if R.one() in I:
        return ('fail', None)
    return ('pass_locus', [str(g) for g in I.gens()])

# -----------------------------------------------------------------------------
# 4. Driver
# -----------------------------------------------------------------------------
def run(n=3, r=16, upset_filter=None, chart_budget=None, verbose=True):
    T, reps, C = build_Mn_tensor(n)
    mdata, em = build_Tperp_and_module(T, reps, C)
    adim = n^2
    TCstar = TCstar_matrix(T, n)
    ups = enumerate_upsets(mdata, r - n^2)
    # Precompute the CONSTANT-block cokernel projectors (CHL S.10 reduction), once.
    coker210, crank210 = constant_skew_projection(TCstar, adim)
    coker120, crank120 = constant_skew_projection(transpose_tensor(TCstar, adim), adim)
    ctx = {'TCstar': TCstar, 'coker210': coker210, 'crank210': crank210,
           'coker120': coker120, 'crank120': crank120}
    survivors = []
    stats = {'n': n, 'r': r, 'num_upsets': len(ups), 'charts_total': 0,
             'charts_closure_rejected': 0, 'charts_fail': 0,
             'charts_pass_all': 0, 'charts_pass_locus': 0}
    idxs = range(len(ups)) if upset_filter is None else upset_filter
    for ui in idxs:
        up = ups[ui]
        desc = [([_pyint(x) for x in p[0]], builtins.int(p[1]), builtins.int(m)) for p, m in up]
        ncharts = prod(binomial(p[1], m) for p, m in up)
        t0 = time.time(); cc = 0
        for nzs, nvars in charts_for_upset(up):
            if chart_budget is not None and cc >= chart_budget: break
            cc += 1; stats['charts_total'] += 1
            res = hwv_for_chart(mdata, up, nzs, nvars)
            if res is None:
                stats['charts_closure_rejected'] += 1; continue
            E110p_module, Rq, ideal_gens = res
            E110p_AB = em * E110p_module                       # 81 x 7 (E_110' in A(x)B)
            # Default: validated full test (M_2 gold-checked). The constant-block
            # 'fast' variant (test_210_120_fast) is verdict-consistent on QQ cases
            # but its symbolic coker*Sp projection over R/I is costly on high-param
            # upsets; left available but NOT the default until further tuned.
            if os.environ.get('BM5_FAST'):
                verdict, plocus = test_210_120_fast(E110p_AB, adim, r, ctx)
            else:
                E110 = TCstar.change_ring(Rq).augment(E110p_AB)    # 81 x 16
                verdict, plocus = test_210_120(E110, adim, r)
            if verdict == 'fail':
                stats['charts_fail'] += 1
            elif verdict == 'pass_all':
                stats['charts_pass_all'] += 1
                survivors.append({'upset': builtins.int(ui), 'nzs': [[builtins.int(x) for x in z] for z in nzs],
                                  'nvars': builtins.int(nvars), 'verdict': 'pass_all',
                                  'closure_ideal': [str(g) for g in ideal_gens]})
                if verbose: print(json.dumps(survivors[-1])); sys.stdout.flush()
            else:
                stats['charts_pass_locus'] += 1
                survivors.append({'upset': builtins.int(ui), 'nzs': [[builtins.int(x) for x in z] for z in nzs],
                                  'nvars': builtins.int(nvars), 'verdict': 'pass_locus',
                                  'pass_ideal': plocus,
                                  'closure_ideal': [str(g) for g in ideal_gens]})
                if verbose: print(json.dumps(survivors[-1])); sys.stdout.flush()
        if verbose:
            print(json.dumps({'_upset_done': builtins.int(ui), 'desc': desc,
                              'charts_theory': builtins.int(ncharts), 'charts_done': builtins.int(cc),
                              'time_s': builtins.round(float(time.time() - t0), 1)})); sys.stdout.flush()
    stats['num_survivor_charts'] = len(survivors)
    stats = {k: (builtins.int(v) if isinstance(v, (int, Integer)) else v) for k, v in stats.items()}
    return survivors, stats

# =============================================================================
# SHARD PARAMETERS  --  EDIT THESE PER FANOUT SHARD (env vars DO NOT cross the
# sager container boundary, so parametrize by editing these constants).
#   UPSET_FILTER : list of upset indices to process, or None for ALL 37.
#   CHART_BUDGET : cap on charts per upset (None = no cap), for sharding heavy
#                  upsets across processes (combine with a chart-offset if needed).
#   USE_FAST     : True to use the constant-block 'fast' (210)/(120) test variant.
# Run each shard as a SEPARATE `sager` invocation (fresh process) to avoid the
# Sage ring-cache memory growth that OOM-kills long single-process runs.
# =============================================================================
UPSET_FILTER = None        # e.g. [0, 1, 2] ; None = all
CHART_BUDGET = None        # e.g. 5000 ; None = unlimited
USE_FAST = False

if __name__ == '__main__' or True:
    if USE_FAST:
        os.environ['BM5_FAST'] = '1'
    survivors, stats = run(n=3, r=16, upset_filter=UPSET_FILTER,
                           chart_budget=CHART_BUDGET, verbose=True)
    print(json.dumps({'_SUMMARY': stats}))
    print(json.dumps({'_SURVIVORS': survivors}))
