# Bm5 FULL-PIPELINE validation on M_2 (gold test). Inlines Bm-m3-enumerate.sage's
# functions and runs the COMPLETE enumeration + (210)/(120) test on M_2:
#   - At r=6: CHL prove NO B-fixed 2-plane passes => expect 0 survivors.
#   - At r=7: R_(M_2)=7, so some B-fixed planes pass => expect >=1 survivor.
# Also prints the enumerated B-fixed 2-planes to confirm there are 3 (CHL L719-723).
# Self-contained.

import os, sys, time, json
from itertools import product as cart_product, combinations

# ---- paste the core from Bm-m3-enumerate.sage ----
def cartan_matrix_sln(n):
    C = matrix(QQ, n - 1, n - 1)
    for i in range(n - 1): C[i, i] = 2
    for i in range(n - 2):
        C[i + 1, i] = -1; C[i, i + 1] = -1
    return C
def _restrict_map(m, C, B):
    I = C.pivot_rows(); return C[I, :].solve_right((m * B)[I, :])
def module_product(a, b):
    return [[xa.tensor_product(identity_matrix(QQ, yb.dimensions()[0], sparse=True)) +
             identity_matrix(QQ, xa.dimensions()[0], sparse=True).tensor_product(yb)
             for xa, yb in zip(s1, s2)] for s1, s2 in zip(a, b)]
def module_dual(a): return [[-x.transpose() for x in s] for s in a]
def simultaneous_eigenspaces(ms):
    n = ms[0].dimensions()[0]; spaces = [(identity_matrix(n, sparse=True), ())]
    for m in ms:
        ns = []
        for B, wt in spaces:
            mr = _restrict_map(m, B, B)
            for ev, es in mr.eigenspaces_right():
                W = es.basis_matrix().transpose().sparse_matrix(); ns.append((B * W, wt + (ev,)))
        spaces = ns
    return spaces
def weight_decomposition(a, C):
    eig = simultaneous_eigenspaces(a[2])
    tk = lambda wt: tuple(C.solve_right(vector(QQ, wt)).list()); eig.sort(key=lambda p: tk(p[1]))
    M = {wt: V for V, wt in eig}; tot = [(wt, V.dimensions()[1]) for V, wt in eig]
    wtg = DiGraph()
    for p in tot:
        wt, mult = p; B = M[wt]
        for i, x in enumerate(a[0]):
            wt2 = tuple((C[:, i] + vector(wt).column()).list())
            if wt2 in M: wtg.add_edge(p, (wt2, M[wt2].dimensions()[1]), _restrict_map(x, M[wt2], B))
    return {'M': M, 'tot': tot, 'C': C, 'a': a, 'wtg': wtg}
def build_Mn_tensor(n):
    Td = n^2; T = [{} for _ in range(Td)]
    for i in range(n):
        for j in range(n):
            a = i*n+j
            for k in range(n): T[a][(j*n+k, k*n+i)] = QQ(1)
    T = [matrix(QQ, Td, Td, m, sparse=True) for m in T]
    def eij(i, j): return matrix(QQ, n, n, {(i, j): 1})
    X = [eij(i, i+1) for i in range(n-1)]; Y = [eij(i+1, i) for i in range(n-1)]
    H = [eij(i, i) - eij(i+1, i+1) for i in range(n-1)]
    gV = [X, Y, H]; gVs = [[-g.transpose() for g in gs] for gs in gV]
    Id = identity_matrix(QQ, n, sparse=True)
    rA = [[Id.tensor_product(g) for g in gs] for gs in gV]
    rB = [[g.tensor_product(Id) for g in gs] for gs in gVs]
    rC = [[matrix(QQ, n^2, n^2, sparse=True) for _ in range(n-1)] for _ in range(3)]
    return T, [rA, rB, rC], cartan_matrix_sln(n)
def build_Tperp_and_module(T, reps, C):
    rAB = module_product(reps[0], reps[1]); rABd = module_dual(rAB)
    Tmat = matrix(QQ, [m.list() for m in T], sparse=True)
    Tp = Tmat.right_kernel_matrix().transpose().sparse_matrix()
    Mr = [[_restrict_map(m, Tp, Tp) for m in s] for s in rABd]
    return weight_decomposition(Mr, C), Tp
def TCstar_matrix(T, n):
    adim = n^2; cols = {}
    for alpha in range(adim):
        for (beta, gamma) in T[alpha].dict():
            cols[(alpha*adim+beta, gamma)] = T[alpha][beta, gamma]
    return matrix(QQ, adim*adim, adim, cols)
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
        for val in range(0, p[1]+1):
            lp.set_min(lp[p], val); lp.set_max(lp[p], val)
            try:
                lp.solve()
                for up in dfs(i+1): yield up
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
    for nzs in cart_product(*[combinations(range(p[-1]), m) for p, m in up]):
        nvars = sum((nzi+1)*(j-i-1) for ((wt, f), m), nz in zip(up, nzs)
                    for nzi, (i, j) in enumerate(zip(nz, nz[1:]+(f,))))
        yield nzs, nvars
def hwv_for_chart(mdata, up, nzs, nvars):
    C = mdata['C']; reps = mdata['a']; M = mdata['M']; ssrank = len(reps[0])
    R = PolynomialRing(QQ, 't', nvars, implementation='singular') if nvars > 0 else QQ
    W = {}; pi = 0
    for q, nz in zip(up, nzs):
        p, m = q; wt, f = p
        t = matrix(R, f, m, sparse=True); t[nz, :] = identity_matrix(R, m, sparse=True)
        for j_idx, ks in enumerate(zip(nz, nz[1:]+(f,))):
            inc = (ks[1]-ks[0]-1)*(j_idx+1)
            if inc > 0:
                t[ks[0]+1:ks[1], :j_idx+1] = matrix(R, ks[1]-ks[0]-1, j_idx+1, R.gens()[pi:pi+inc]); pi += inc
        W[wt] = (M[p[0]]*t, m, f)
    cur = block_matrix([[B for B, m, f in W.values()]], subdivide=False)
    eqs = []
    for wt, v in W.items():
        B_mat, m, f = v
        def raisewt(wt, k): return tuple(aa+bb for aa, bb in zip(wt, C[:, k].list()))
        for k in range(ssrank):
            rwt = raisewt(wt, k); curd = W.get(rwt, None)
            if curd is not None:
                Braise, mr, fr = curd
                if mr == fr: continue
                mm = Braise.augment(reps[0][k]*B_mat); eqs.extend(_minors_sparse(mm, mr+1))
            elif rwt in M:
                eqs.extend((reps[0][k]*B_mat).coefficients())
    if len(eqs) > 0:
        I = R.ideal(eqs)
        if R.one() in I: return None
        Rbar = R.quo(I)
        cur = cur.apply_map(Rbar, sparse=True, R=Rbar)
        return cur, Rbar, list(I.gens())
    return cur, R, []
def transpose_tensor(B, a):
    b = B.dimensions()[0] // a; Bp = {}
    for I, k in B.nonzero_positions():
        i, j = I // b, I % b; Bp[(j*a+i, k)] = B[I, k]
    return matrix(B.base_ring(), B.dimensions()[0], B.dimensions()[1], Bp)
def skew_210_map(B, a):
    b = B.dimensions()[0] // a; S = B.dimensions()[1]; W = {}
    for I, s in B.nonzero_positions():
        i, j = I // b, I % b; v = B[I, s]
        for k in range(a):
            if k == i: continue
            p, q = (k, i) if k < i else (i, k); sign = 1 if k < i else -1
            ix = (binomial(q, 2)+p)*b + j; col = s*a + k
            W[(ix, col)] = W.get((ix, col), 0) + sign*v
    return matrix(B.base_ring(), binomial(a, 2)*b, S*a, W)
def is_unit_safe(e):
    try: return e.is_unit()
    except (NotImplementedError, AttributeError): return False
def sparse_elimination_by_units(M):
    M = copy(M); r = 0
    while True:
        if r == min(*M.dimensions()): break
        try:
            i, j = next((i+r, j+r) for i, j in M[r:, r:].nonzero_positions() if is_unit_safe(M[i+r, j+r]))
        except StopIteration: break
        M.swap_rows(r, i); M.swap_columns(r, j)
        M[r, :] *= M[r, r].inverse_of_unit()
        for ii in M.column(r)[r+1:].nonzero_positions():
            ii += r+1; M.add_multiple_of_row(ii, r, -M[ii, r])
        r += 1
    return M, r
def rankdrop_minors(M, r):
    Rorig = M.base_ring()
    if M.is_zero() or r > min(*M.dimensions()): return []
    M, lo = sparse_elimination_by_units(M)
    if r <= lo: return [Rorig.one()]
    r2 = r - lo; M = M[lo:, lo:]
    if M.is_zero(): return []
    M = M[[i for i in range(M.dimensions()[0]) if not M[i].is_zero()],
          [j for j in range(M.dimensions()[1]) if not M[:, j].is_zero()]]
    if r2 > min(*M.dimensions()): return []
    return _minors_sparse(M, r2)
def test_210_120(E110, adim, r):
    R = E110.base_ring(); dom = E110.dimensions()[1]*adim; need = dom - r
    one = (R.one() if R is not QQ else 1)
    M210 = skew_210_map(E110, adim); g210 = rankdrop_minors(M210, need+1)
    if g210 == [one] or g210 == [1]: return ('fail', None)
    drops210 = (g210 == [])
    M120 = skew_210_map(transpose_tensor(E110, adim), adim); g120 = rankdrop_minors(M120, need+1)
    if g120 == [one] or g120 == [1]: return ('fail', None)
    drops120 = (g120 == [])
    if drops210 and drops120: return ('pass_all', [])
    gens = [g for g in (g210+g120) if g != 0 and g != one]
    if R is QQ: return ('pass_all', [])
    I = R.ideal(gens) if gens else R.ideal([])
    if R.one() in I: return ('fail', None)
    return ('pass_locus', [str(g) for g in I.gens()])

def run(n, r):
    T, reps, C = build_Mn_tensor(n)
    mdata, em = build_Tperp_and_module(T, reps, C); adim = n^2
    TCstar = TCstar_matrix(T, n)
    ups = enumerate_upsets(mdata, r - n^2)
    print("M_%d r=%d : module dim=%d, %d upsets for %d-planes" % (
        n, r, em.dimensions()[1], len(ups), r - n^2))
    for ui, up in enumerate(ups):
        print("   upset %d: %s charts=%d" % (ui, str([(tuple(p[0]), m) for p, m in up]),
              prod(binomial(p[1], m) for p, m in up)))
    survivors = []; cf = 0; cr = 0
    for ui, up in enumerate(ups):
        for nzs, nvars in charts_for_upset(up):
            res = hwv_for_chart(mdata, up, nzs, nvars)
            if res is None: cr += 1; continue
            E110p, Rq, ig = res
            E110 = TCstar.change_ring(Rq).augment(em * E110p)
            v, pl = test_210_120(E110, adim, r)
            if v == 'fail': cf += 1
            else: survivors.append((ui, nzs, nvars, v, pl))
    print("   closure-rejected=%d fail=%d survivors=%d" % (cr, cf, len(survivors)))
    for s in survivors[:20]:
        print("   SURVIVOR upset=%d nzs=%s nvars=%d verdict=%s" % (s[0], str(s[1]), s[2], s[3]))
    return survivors

print("=== M_2 at r=6 (CHL: NO plane passes; R_(M_2)>6) ===")
s6 = run(2, 6)
print()
print("=== M_2 at r=7 (R_(M_2)=7; expect some plane passes) ===")
s7 = run(2, 7)
print()
print("VALIDATION: r=6 survivors=%d (expect 0); r=7 survivors=%d (expect >0)" % (len(s6), len(s7)))
print("VERDICT: %s" % ("PASS" if (len(s6) == 0 and len(s7) > 0) else "FAIL -- investigate"))
