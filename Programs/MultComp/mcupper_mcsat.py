#!/usr/bin/env python3
# mcupper_mcsat.py
# Exact multiplicative-complexity SAT search (Stoffelen-style XOR-AND normal
# form) for (possibly partial / don't-care) multi-output Boolean functions.
# Solver: python-sat (cadical) in /tmp/satenv.
#
# Circuit model: k AND gates g_0..g_{k-1}; g_i = A_i AND B_i where A_i, B_i are
# GF(2)-affine forms over {1, inputs, g_0..g_{i-1}}. Each output = affine form
# over {1, inputs, all gates}. XOR/const are free. This is complete for MC.
#
# Partial functions: only 'care' input points are constrained; off-care points
# are unconstrained (don't-cares). Care points given as {input_int: out_int}.
#
# Pinned field rep (must match Scratch/mcupper_domain_structure.sage):
#   GF(2^4) = GF(2)[t]/(t^4+t+1) = mod 0x13; bit i = coeff t^i.
#   GF(2^8)=K[Y]/(Y^2+Y+nu), nu=8. d=nu*a^2+a*b+b^2, w=d^{-1}, out=a*w or (a+b)*w.

import sys, time
sys.path.insert(0, "/tmp/satenv/lib/python3.12/site-packages")
from pysat.solvers import Cadical195 as Solver
from pysat.formula import IDPool

# ---------- pinned GF(2^4) arithmetic ----------
MOD = 0x13  # t^4 + t + 1
def gmul(a, b):
    r = 0
    for i in range(4):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(7, 3, -1):
        if (r >> i) & 1:
            r ^= (MOD << (i - 4))
    return r & 0xF
def gpow(a, e):
    r = 1
    for _ in range(e): r = gmul(r, a)
    return r
def ginv(a):
    return 0 if a == 0 else gpow(a, 14)
NU = 8
def norm(a, b):  # d = nu*a^2 + a*b + b^2
    return gmul(NU, gmul(a, a)) ^ gmul(a, b) ^ gmul(b, b)

# self-check against printed Sage anchors
assert norm(1, 0) == 8 and ginv(8) == 15 and gmul(1, 15) == 15, "rep mismatch a=1,b=0"
assert norm(3, 5) == 3 and ginv(3) == 14 and gmul(3, 14) == 1, "rep mismatch a=3,b=5"
assert gmul(15, 10) == gmul(10, 15), "gmul comm"

# ---------- CNF builder ----------
class CNF:
    def __init__(self):
        self.pool = IDPool()
        self.clauses = []
    def newv(self):
        return self.pool.id()
    def add(self, cl):
        self.clauses.append(list(cl))
    def and2(self, a, b):
        # y = a AND b
        y = self.newv()
        self.add([-y, a]); self.add([-y, b]); self.add([y, -a, -b])
        return y
    def xor2(self, a, b):
        y = self.newv()
        self.add([-a, -b, -y]); self.add([a, b, -y])
        self.add([a, -b, y]); self.add([-a, b, y])
        return y
    def fold_xor(self, lits, const=0):
        # returns a literal equal to XOR(lits) XOR const.  lits: list of ints
        # (positive var ids; may include None meaning skip). const in {0,1}.
        acc = None
        cval = const
        for l in lits:
            if l is None:
                continue
            if acc is None:
                acc = l
            else:
                acc = self.xor2(acc, l)
        if acc is None:
            # XOR of nothing = 0; result = const (a constant)
            return ('const', cval)
        if cval:
            # need acc XOR 1 = NOT acc
            return ('lit', -acc)
        return ('lit', acc)
    def force_eq_const(self, expr, c):
        # expr is ('const',v) or ('lit',l); force it == c in {0,1}
        kind, val = expr
        if kind == 'const':
            if val != c:
                self.add([])  # unsat: empty clause
        else:
            self.add([val] if c == 1 else [-val])
    def expr_to_lit(self, expr):
        kind, val = expr
        if kind == 'lit':
            return val
        # constant: make a var forced to that value
        y = self.newv()
        self.add([y] if val == 1 else [-y])
        return y

def build_and_solve(n, m, care, k, timeout=None, verbose=True, sym_break=True):
    """n inputs, m outputs, care = {inp_int: out_int}, k AND gates.
    Returns (True, circuit) or (False, None) or ('timeout', None)."""
    C = CNF()
    # structure vars
    # gate i sources: wire ids 0..n-1 (inputs), n..n+i-1 (prior gates)
    selA = [[C.newv() for _ in range(n + i)] for i in range(k)]
    selB = [[C.newv() for _ in range(n + i)] for i in range(k)]
    conA = [C.newv() for _ in range(k)]
    conB = [C.newv() for _ in range(k)]
    selO = [[C.newv() for _ in range(n + k)] for _ in range(m)]
    conO = [C.newv() for _ in range(m)]

    # symmetry break: AND is commutative -> force A_i <=_lex B_i (const then sels)
    if sym_break:
        TRUE = C.newv(); C.add([TRUE])
        def lex_le(av, bv):
            pe = TRUE
            for j in range(len(av)):
                C.add([-pe, -av[j], bv[j]])
                ej = C.newv()
                C.add([-ej, -av[j], bv[j]]); C.add([-ej, av[j], -bv[j]])
                C.add([ej, av[j], bv[j]]); C.add([ej, -av[j], -bv[j]])
                npe = C.newv()
                C.add([-npe, pe]); C.add([-npe, ej]); C.add([npe, -pe, -ej])
                pe = npe
        for i in range(k):
            lex_le([conA[i]] + selA[i], [conB[i]] + selB[i])

    # light symmetry breaking: gate i must use at least one prior-gate or input
    # in A; and forbid A being empty-constant (optional). We instead force each
    # gate's A to reference gate i-1 is too strong; skip. Add: output must use
    # gates (not identically affine in inputs) -- skip for generality.

    pts = list(care.items())
    for (xin, yout) in pts:
        xv = [(xin >> j) & 1 for j in range(n)]
        gv = []  # gate value literals at this point
        for i in range(k):
            # affine A value
            litsA = []
            for j in range(n):
                if xv[j]:
                    litsA.append(selA[i][j])       # active input contributes sel var
            for j in range(i):
                litsA.append(C.and2(selA[i][n + j], gv[j]))
            exprA = C.fold_xor(litsA, 0)
            aLit = C.expr_to_lit(exprA)
            # XOR the constant term conA
            aLit = C.xor2(aLit, conA[i])
            # affine B value
            litsB = []
            for j in range(n):
                if xv[j]:
                    litsB.append(selB[i][j])
            for j in range(i):
                litsB.append(C.and2(selB[i][n + j], gv[j]))
            exprB = C.fold_xor(litsB, 0)
            bLit = C.expr_to_lit(exprB)
            bLit = C.xor2(bLit, conB[i])
            # gate value = aLit AND bLit
            gval = C.and2(aLit, bLit)
            gv.append(gval)
        # outputs
        for r in range(m):
            litsO = []
            for j in range(n):
                if xv[j]:
                    litsO.append(selO[r][j])
            for j in range(k):
                litsO.append(C.and2(selO[r][n + j], gv[j]))
            exprO = C.fold_xor(litsO, 0)
            oLit = C.expr_to_lit(exprO)
            oLit = C.xor2(oLit, conO[r])
            want = (yout >> r) & 1
            C.add([oLit] if want == 1 else [-oLit])

    if verbose:
        print("  [k=%d] vars=%d clauses=%d care=%d" %
              (k, C.pool.top, len(C.clauses), len(pts)), flush=True)
    s = Solver(bootstrap_with=C.clauses)
    t0 = time.time()
    if timeout:
        # pysat interrupt via time budget: use solve_limited with a wrapper
        import threading
        result = {}
        def run():
            result['sat'] = s.solve()
        th = threading.Thread(target=run); th.start(); th.join(timeout)
        if th.is_alive():
            s.interrupt(); th.join()
            return ('timeout', None)
        sat = result.get('sat')
    else:
        sat = s.solve()
    dt = time.time() - t0
    if verbose:
        print("  [k=%d] -> %s (%.1fs)" % (k, sat, dt), flush=True)
    if not sat:
        s.delete()
        return (False, None)
    model = set(l for l in s.get_model() if l > 0)
    s.delete()
    # decode
    def bit(v): return 1 if v in model else 0
    circ = dict(k=k, gatesA=[], gatesB=[], outs=[])
    for i in range(k):
        A = [j for j in range(n + i) if bit(selA[i][j])]
        B = [j for j in range(n + i) if bit(selB[i][j])]
        circ['gatesA'].append((bit(conA[i]), A))
        circ['gatesB'].append((bit(conB[i]), B))
    for r in range(m):
        O = [j for j in range(n + k) if bit(selO[r][j])]
        circ['outs'].append((bit(conO[r]), O))
    return (True, circ)

def eval_circuit(circ, n, xin):
    xv = [(xin >> j) & 1 for j in range(n)]
    wires = list(xv)
    for i in range(circ['k']):
        cA, A = circ['gatesA'][i]; cB, B = circ['gatesB'][i]
        av = cA
        for j in A: av ^= wires[j]
        bv = cB
        for j in B: bv ^= wires[j]
        wires.append(av & bv)
    out = 0
    for r, (cO, O) in enumerate(circ['outs']):
        ov = cO
        for j in O: ov ^= wires[j]
        out |= ov << r
    return out

def verify(circ, n, care):
    for xin, yout in care.items():
        if eval_circuit(circ, n, xin) != yout:
            return False
    return True

# ---------- domain builders ----------
def total_gf4_mult():
    care = {}
    for a in range(4):
        for b in range(4):
            care[a | (b << 2)] = gmul_gf2m(a, b, 2)
    return care
def gmul_gf2m(a, b, m):
    # generic small-field mult for GF(2^2) with modulus t^2+t+1 (0x7)
    mod = 0x7
    r = 0
    for i in range(m):
        if (b >> i) & 1: r ^= a << i
    for i in range(2*m-2, m-1, -1):
        if (r >> i) & 1: r ^= (mod << (i - m))
    return r & ((1 << m) - 1)

def norm2(a, b):  # n=4 GF(2^2), nu=? Tr=1 -> nu in {t, t+1}; pick t=2
    nu = 2
    return gmul_gf2m(nu, gmul_gf2m(a, a, 2), 2) ^ gmul_gf2m(a, b, 2) ^ gmul_gf2m(b, b, 2)
def ginv2(a):
    if a == 0: return 0
    for x in range(1, 4):
        if gmul_gf2m(a, x, 2) == 1: return x
def partial_mult_n4():
    care = {}
    for a in range(4):
        for b in range(4):
            if a == 0 and b == 0: continue
            d = norm2(a, b); w = ginv2(d)
            care[a | (w << 2)] = gmul_gf2m(a, w, 2)  # p=a side
    return care

def partial_mult_n8_pside():
    care = {}
    for a in range(16):
        for b in range(16):
            if a == 0 and b == 0: continue
            d = norm(a, b); w = ginv(d)
            care[a | (w << 4)] = gmul(a, w)
    return care
def total_mult_n8():
    care = {}
    for a in range(16):
        for b in range(16):
            care[a | (b << 4)] = gmul(a, b)
    return care
def joint_stage_n8():
    # inputs (a,b,w) 12 bits; outputs (a*w,(a+b)*w) 8 bits
    care = {}
    for a in range(16):
        for b in range(16):
            if a == 0 and b == 0: continue
            d = norm(a, b); w = ginv(d)
            xin = a | (b << 4) | (w << 8)
            out = gmul(a, w) | (gmul(a ^ b, w) << 4)
            care[xin] = out
    return care

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("task")
    ap.add_argument("k", type=int)
    ap.add_argument("--timeout", type=float, default=None)
    args = ap.parse_args()
    T = {
        "n4total": (4, 2, total_gf4_mult()),
        "n4partial": (4, 2, partial_mult_n4()),
        "n8partial": (8, 4, partial_mult_n8_pside()),
        "n8total": (8, 4, total_mult_n8()),
        "n8joint": (12, 8, joint_stage_n8()),
    }
    n, m, care = T[args.task]
    print("task=%s n=%d m=%d |care|=%d target k=%d" % (args.task, n, m, len(care), args.k))
    sat, circ = build_and_solve(n, m, care, args.k, timeout=args.timeout)
    if sat is True:
        ok = verify(circ, n, care)
        print("SAT; verified on care set:", ok)
        print("circuit:", circ)
    elif sat is False:
        print("UNSAT: no %d-AND circuit exists (partial MC > %d)" % (args.k, args.k))
    else:
        print("TIMEOUT at k=%d" % args.k)
