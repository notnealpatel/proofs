#!/usr/bin/env python3
# mcupper_bilinrank.py
# Bilinear rank (= number of GF(2)-bilinear multiplications) of:
#   (1) a single GF(2^4) multiplication  a*w         -> validates mu_2=9
#   (2) the JOINT tower output stage (a,b,w)->(a*w, b*w)   [cross-sharing lever]
#
# A rank-r bilinear algorithm: products P_i = (alpha_i . left)(beta_i . right),
# outputs = linear combos of {P_i}.  Tensor identity  T[l][r][o] = XOR_i
# alpha_i[l] beta_i[r] gamma_i[o].  We SAT for existence at rank r.
# MC <= bilinear rank; a rank < 18 joint stage beats the 32-AND record directly
# (total = M1(9)+inv(5)+stage). mu_2(GF16)=9 [Wang/Winograd] is the single-mult
# baseline; r=8 UNSAT confirms it and validates the encoder.
#
# Pinned rep: GF(2^4)=GF(2)[t]/(t^4+t+1), bit i = coeff t^i. (matches Sage.)

import sys, time
sys.path.insert(0, "/tmp/satenv/lib/python3.12/site-packages")
from pysat.solvers import Cadical195 as Solver
from pysat.formula import IDPool

MOD = 0x13
def gmul(a, b):
    r = 0
    for i in range(4):
        if (b >> i) & 1: r ^= a << i
    for i in range(7, 3, -1):
        if (r >> i) & 1: r ^= (MOD << (i - 4))
    return r & 0xF
assert gmul(3, 14) == 1 and gmul(1, 15) == 15

# single-mult tensor M[l][r][o], l,r,o in 0..3
M = [[[0]*4 for _ in range(4)] for _ in range(4)]
for l in range(4):
    for rr in range(4):
        prod = gmul(1 << l, 1 << rr)
        for o in range(4):
            M[l][rr][o] = (prod >> o) & 1

def single_tensor():
    # left dim 4, right 4, out 4
    T = {}
    for l in range(4):
        for rr in range(4):
            for o in range(4):
                T[(l, rr, o)] = M[l][rr][o]
    return T, 4, 4, 4

def joint_tensor():
    # left = (a[0..3], b[0..3]) dim 8; right = w dim 4; out = (aw[0..3], bw[0..3]) dim 8
    T = {}
    for l in range(8):
        for rr in range(4):
            for o in range(8):
                v = 0
                if l < 4 and o < 4:       # a-bit -> aw-bit
                    v = M[l][rr][o]
                elif l >= 4 and o >= 4:    # b-bit -> bw-bit
                    v = M[l-4][rr][o-4]
                T[(l, rr, o)] = v
    return T, 8, 4, 8

# --- GF(2^2) analogs (tiny; validate encoder + base-level sharing question) ---
MOD2 = 0x7
def gmul2(a, b):
    r = 0
    for i in range(2):
        if (b >> i) & 1: r ^= a << i
    for i in range(2, 1, -1):
        if (r >> i) & 1: r ^= (MOD2 << (i - 2))
    return r & 0x3
M2 = [[[ (gmul2(1<<l,1<<rr)>>o)&1 for o in range(2)] for rr in range(2)] for l in range(2)]
def single2_tensor():
    T = {(l,rr,o): M2[l][rr][o] for l in range(2) for rr in range(2) for o in range(2)}
    return T, 2, 2, 2
def joint2_tensor():
    # left (u,v) 4 bits, right w 2 bits, out (uw,vw) 4 bits  == scalar mult GF4^2 by w
    T = {}
    for l in range(4):
        for rr in range(2):
            for o in range(4):
                v = 0
                if l < 2 and o < 2: v = M2[l][rr][o]
                elif l >= 2 and o >= 2: v = M2[l-2][rr][o-2]
                T[(l,rr,o)] = v
    return T, 4, 2, 4

def solve_rank(Tspec, r, timeout=None, verbose=True, sym=True):
    T, L, R, O = Tspec
    pool = IDPool(); cls = []
    A = [[pool.id() for _ in range(L)] for _ in range(r)]
    B = [[pool.id() for _ in range(R)] for _ in range(r)]
    G = [[pool.id() for _ in range(O)] for _ in range(r)]
    def and3(x, y, z):
        w = pool.id()
        cls.append([-w, x]); cls.append([-w, y]); cls.append([-w, z])
        cls.append([w, -x, -y, -z]); return w
    def xor2(a, b):
        y = pool.id()
        cls.append([-a, -b, -y]); cls.append([a, b, -y])
        cls.append([a, -b, y]); cls.append([-a, b, y]); return y
    # per tensor entry: XOR_i and3(A[i][l],B[i][rr],G[i][o]) == T
    for (l, rr, o), tval in T.items():
        terms = [and3(A[i][l], B[i][rr], G[i][o]) for i in range(r)]
        acc = None
        for tt in terms:
            acc = tt if acc is None else xor2(acc, tt)
        if acc is None:
            if tval != 0: cls.append([])
        else:
            cls.append([acc] if tval == 1 else [-acc])
    # symmetry: forbid all-zero terms (each product must be nonzero on both sides)
    if sym:
        for i in range(r):
            cls.append([A[i][l] for l in range(L)])   # alpha_i != 0
            cls.append([B[i][rr] for rr in range(R)])  # beta_i != 0
            cls.append([G[i][o] for o in range(O)])    # gamma_i != 0
        # break r! permutation symmetry: term vectors non-decreasing (lex, MSB first)
        TRUE = pool.id(); cls.append([TRUE])
        def lex_le(av, bv):
            # force av <=_lex bv (index 0 = MSB); av,bv equal-length lists of vars
            pe = TRUE
            for j in range(len(av)):
                # if pe then a[j] -> b[j]
                cls.append([-pe, -av[j], bv[j]])
                # e_j = (a[j]==b[j]);  pe_{j+1} = pe AND e_j
                ej = pool.id()
                cls.append([-ej, -av[j], bv[j]]); cls.append([-ej, av[j], -bv[j]])
                cls.append([ej, av[j], bv[j]]);   cls.append([ej, -av[j], -bv[j]])
                npe = pool.id()
                cls.append([-npe, pe]); cls.append([-npe, ej]); cls.append([npe, -pe, -ej])
                pe = npe
        for i in range(r - 1):
            vi = A[i] + B[i] + G[i]
            vj = A[i+1] + B[i+1] + G[i+1]
            lex_le(vi, vj)
    if verbose:
        print("  rank r=%d: vars=%d clauses=%d" % (r, pool.top, len(cls)), flush=True)
    s = Solver(bootstrap_with=cls)
    t0 = time.time()
    sat = s.solve()
    dt = time.time() - t0
    res = None
    if sat:
        model = set(x for x in s.get_model() if x > 0)
        res = dict(
            alpha=[[1 if A[i][l] in model else 0 for l in range(L)] for i in range(r)],
            beta=[[1 if B[i][rr] in model else 0 for rr in range(R)] for i in range(r)],
            gamma=[[1 if G[i][o] in model else 0 for o in range(O)] for i in range(r)],
        )
    s.delete()
    if verbose:
        print("  rank r=%d -> %s (%.1fs)" % (r, "SAT" if sat else "UNSAT", dt), flush=True)
    return sat, res

def verify_decomp(Tspec, res):
    T, L, R, O = Tspec
    r = len(res['alpha'])
    for (l, rr, o), tval in T.items():
        acc = 0
        for i in range(r):
            acc ^= res['alpha'][i][l] & res['beta'][i][rr] & res['gamma'][i][o]
        if acc != tval:
            return False
    return True

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("which", choices=["single", "joint", "single2", "joint2"])
    ap.add_argument("r", type=int)
    args = ap.parse_args()
    Tspec = {"single": single_tensor, "joint": joint_tensor,
             "single2": single2_tensor, "joint2": joint2_tensor}[args.which]()
    print("bilinear rank test: %s, r=%d, dims L=%d R=%d O=%d" %
          (args.which, args.r, Tspec[1], Tspec[2], Tspec[3]))
    sat, res = solve_rank(Tspec, args.r)
    if sat:
        ok = verify_decomp(Tspec, res)
        print("SAT: rank <= %d bilinear circuit exists; verified tensor identity:" % args.r, ok)
    else:
        print("UNSAT: bilinear rank > %d" % args.r)
