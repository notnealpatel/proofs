"""
MCLOWER P2: the defect map def(g) = D6(g) - phi(D7(g)) on degree-7 MC-6
functions (candidates for the first high gate A of the rigid profile).

phi is inversion's forced slice-coupling map (Lambda^7 -> Lambda^6), loaded
from mclower_p1_phi_aes.json (AES modulus).

We sample degree-7 functions computed by 6-AND circuits (MC=6 automatically,
since deg 7 forces MC>=6 by Schnorr and the circuit gives MC<=6). For each we
compute def in Lambda^6 (28-dim). Questions:
  (Q1) dim of span{def(A) : sampled}  -- is the defect space small?
  (Q2) is 0 in the achievable def-set? (i.e. does any MC-6 deg-7 A lie exactly
       on inversion's slice-graph)
  (Q3) pure-product family: A = prod_{k=1}^7 (c_k + ell_k). For fixed linear
       parts (fixed D7=sigma), the D6 ranges over sigma-dependent 7-dim space;
       report def-coset structure.
Deterministic seeds. Structured JSON out.
"""
import json, random

n = 8
N = 256
FULL = N - 1
random.seed(20260723r)

with open("/home/exedev/p/proofs/Scratch/mclower_p1_phi_aes.json") as fh:
    P = json.load(fh)

PAIRS = [tuple(p) for p in P["pairs"]]
W7 = [FULL ^^ (1 << i) for i in range(8)]
W6 = [FULL ^^ (1 << i) ^^ (1 << j) for (i, j) in PAIRS]
# phi as matrix over GF(2): row-vector action t = s * phi, phi is 8x28
PHI = matrix(GF(2), P["phi"])            # 8 x 28
Smat = matrix(GF(2), P["S"])             # 8x8 D7-slices of coords (basis change)


def mobius(tt):
    a = list(tt)
    k = 1
    while k < N:
        for i in range(N):
            if i & k:
                a[i] ^^= a[i ^^ k]
        k <<= 1
    return a


def anf_of_tt(tt):
    return mobius(tt)


def D7vec(anf):
    return vector(GF(2), [anf[m] for m in W7])


def D6vec(anf):
    return vector(GF(2), [anf[m] for m in W6])


def degree(anf):
    return max((bin(m).count('1') for m in range(N) if anf[m]), default=0)


def defect(anf):
    s7 = D7vec(anf)
    s6 = D6vec(anf)
    # phi(s7) in row-vector convention: s7 (as row) * PHI  -> 28-vec
    phi_s7 = s7 * PHI
    return s6 - phi_s7


# --- truth tables of input variables ---
# x_i(point p) = bit i of p
VAR_TT = [[(p >> i) & 1 for p in range(N)] for i in range(8)]


def rand_linear(signals, allow_const=True):
    """random F2 linear combo (optionally + const) of given signal truth tables"""
    tt = [0] * N
    for s in signals:
        if random.getrandbits(1):
            tt = [a ^^ b for a, b in zip(tt, s)]
    if allow_const and random.getrandbits(1):
        tt = [a ^^ 1 for a in tt]
    return tt


def rand_6gate_deg7():
    """random 6-AND circuit; return anf of the 6th gate if degree 7 else None"""
    signals = [VAR_TT[i][:] for i in range(8)]
    gates = []
    for g in range(6):
        pool = signals + gates
        L = rand_linear(pool)
        R = rand_linear(pool)
        AND = [a & b for a, b in zip(L, R)]
        gates.append(AND)
    anf = anf_of_tt(gates[-1])
    if degree(anf) == 7:
        return anf
    return None


# ---- Q1/Q2: sample MC-6 deg-7 functions ----
defs = []
zero_hit = 0
tries = 0
got = 0
target = 4000
while got < target and tries < 400000:
    tries += 1
    anf = rand_6gate_deg7()
    if anf is None:
        continue
    got += 1
    d = defect(anf)
    defs.append(d)
    if d == 0:
        zero_hit += 1

Dmat = matrix(GF(2), defs) if defs else matrix(GF(2), 0, 28)
span_dim = Dmat.rank()

# Also collect the achievable (D7, D6) and check: for the graph, def == 0.
# Build the affine span of achievable def vectors (do they form a subspace or
# an affine coset?). Test: is span linear (0 in span always) -- yes since we
# take rank of vectors; also check whether translates matter by centering.

# ---- Q3: pure product family ----
# choose 7 random independent linear forms (homogeneous), vary the 7 constants
def homog_linear_tt(coeffs):
    tt = [0] * N
    for i in range(8):
        if coeffs[i]:
            tt = [a ^^ b for a, b in zip(tt, VAR_TT[i])]
    return tt

def product_family_report(trial):
    # pick 7 independent linear forms
    while True:
        rows = [[random.getrandbits(1) for _ in range(8)] for _ in range(7)]
        M = matrix(GF(2), rows)
        if M.rank() == 7:
            break
    ell = [homog_linear_tt(r) for r in rows]
    # base product with all constants 0 -> homogeneous deg-7 product = D7
    def prod_with_consts(cs):
        tt = [1] * N
        for k in range(7):
            factor = ell[k][:]
            if cs[k]:
                factor = [x ^^ 1 for x in factor]
            tt = [a & b for a, b in zip(tt, factor)]
        return tt
    anf0 = anf_of_tt(prod_with_consts([0]*7))
    sigma = D7vec(anf0)
    deg0 = degree(anf0)
    # vary constants: collect def vectors
    dset = []
    for mask in range(128):
        cs = [(mask >> k) & 1 for k in range(7)]
        anf = anf_of_tt(prod_with_consts(cs))
        if degree(anf) != 7:
            continue
        dset.append(defect(anf))
    Dm = matrix(GF(2), dset)
    # affine structure: subtract first
    base = dset[0]
    Dm_c = matrix(GF(2), [d - base for d in dset])
    return {
        "trial": int(trial),
        "sigma_nonzero": bool(sigma != 0),
        "deg0": int(deg0),
        "num_const_settings_deg7": len(dset),
        "affine_def_span_dim": int(Dm_c.rank()),  # dim of achievable def coset
        "contains_zero_def": bool(any(d == 0 for d in dset)),
    }

prod_reports = [product_family_report(t) for t in range(8)]

out = {
    "phi_rank": int(PHI.rank()),
    "sampled_mc6_deg7": int(got),
    "tries": int(tries),
    "defect_span_dim (Q1)": int(span_dim),
    "zero_defect_hits (Q2)": int(zero_hit),
    "Lambda6_dim": int(28),
    "product_family (Q3)": prod_reports,
}
print(json.dumps(out, indent=1))
