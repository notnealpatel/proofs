"""
MCLOWER P1: slice data of inv8 = x^254 on GF(2^8) (0 -> 0).

Computes, for a fixed field representation:
  - D7 slices of the 8 coordinates (matrix S, 8x8) and rank
  - D6 slices (matrix T, 8x28) and rank  -> rank(phi)
  - D5 slices (matrix U, 8x56) and rank  -> rank(phi5)
  - the graph map phi = S^-1 T (row-vector convention: t = s * phi)
  - for all 255 components f_b = Tr(b * inv(x)): dual 2-form omega_b of
    D6(f_b) (8x8 alternating matrix over GF(2), entry (i,j) = ANF coeff of
    the degree-6 monomial missing {i,j}); rank distribution
Runs under the AES modulus (FIPS-197: x^8+x^4+x^3+x+1) and the Sage/Conway
modulus, and compares invariants.

Deterministic. Structured JSON at the end.
"""
import json
from collections import Counter

n = 8
N = 256
FULL = N - 1  # mask 0xFF


def mobius(tt):
    a = list(tt)
    k = 1
    while k < N:
        for i in range(N):
            if i & k:
                a[i] ^^= a[i ^^ k]
        k <<= 1
    return a


W7 = [FULL ^^ (1 << i) for i in range(8)]                      # missing {i}
PAIRS = [(i, j) for i in range(8) for j in range(i + 1, 8)]     # 28
W6 = [FULL ^^ (1 << i) ^^ (1 << j) for (i, j) in PAIRS]
TRIPLES = [(i, j, k) for i in range(8) for j in range(i + 1, 8)
           for k in range(j + 1, 8)]                            # 56
W5 = [FULL ^^ (1 << i) ^^ (1 << j) ^^ (1 << k) for (i, j, k) in TRIPLES]


def slice_vec(anf, masks):
    return [anf[m] for m in masks]


def analyze(modulus_name, F):
    V = F.vector_space(map=False)
    a = F.gen()
    # bit i of integer repr <-> coefficient of a^i (polynomial basis)
    elems = [F.from_integer(i) for i in range(N)]
    inv_img = [F(0) if e == F(0) else e ^ 254 for e in elems]

    # sanity anchor (AES modulus only): inv(0x53) must have known value?
    # (we anchor instead on algebraic identities below)
    # check x * inv(x) == 1 for x != 0
    assert all(elems[i] * inv_img[i] == F(1) for i in range(1, N))

    # coordinate ANFs
    coord_anf = []
    for j in range(n):
        tt = [int(vector(V(inv_img[i]))[j]) for i in range(N)]
        coord_anf.append(mobius(tt))

    S = matrix(GF(2), [slice_vec(anf, W7) for anf in coord_anf])
    T = matrix(GF(2), [slice_vec(anf, W6) for anf in coord_anf])
    U = matrix(GF(2), [slice_vec(anf, W5) for anf in coord_anf])
    deg8 = [anf[FULL] for anf in coord_anf]

    rS, rT, rU = S.rank(), T.rank(), U.rank()

    # component ANFs for all b, via truth tables (exact, 255 x Mobius)
    omega_ranks = Counter()
    comp_deg = Counter()
    for bi in range(1, N):
        b = F.from_integer(bi)
        tt = [int((b * inv_img[i]).trace()) for i in range(N)]
        anf = mobius(tt)
        deg = max((bin(m).count('1') for m in range(N) if anf[m]), default=0)
        comp_deg[deg] += 1
        # dual 2-form of D6
        M = matrix(GF(2), 8, 8, 0)
        for (idx, (i, j)) in enumerate(PAIRS):
            v = anf[W6[idx]]
            M[i, j] = v
            M[j, i] = v
        omega_ranks[M.rank()] += 1

    phi = None
    if rS == 8:
        phi = S.inverse() * T   # row-vector convention: t = s * phi... careful:
        # rows of S are s_i; rows of T are t_i;  S^-1*T maps: row_i(S^-1*T)
        # solves  sum_k (S^-1)_{ik} t_k, and  e_i = sum_k (S^-1)_{ik} s_k...
        # Actually (S^-1*T) has rows = phi(e_i) where e_i = standard basis of
        # Lambda^7 expressed via s-basis: S * (S^-1 T) = T, i.e. s_i * (S^-1 T)
        # interpreted as row_i(S) * (S^-1 T) = row_i(T) = t_i.  So for a row
        # vector s, phi(s) = s * (S^-1 T).  Correct.

    out = {
        "modulus": modulus_name,
        "modulus_poly": str(F.modulus()),
        "rank_D7_coords": int(rS),
        "rank_D6_coords(=rank phi)": int(rT),
        "rank_D5_coords(=rank phi5)": int(rU),
        "coord_deg8_coeffs": [int(d) for d in deg8],
        "component_degree_multiset": {str(k): int(v) for k, v in sorted(comp_deg.items())},
        "omega_rank_distribution": {str(k): int(v) for k, v in sorted(omega_ranks.items())},
    }
    return out, phi, S, T, U


# --- AES modulus ---
R.<X> = GF(2)[]
Faes = GF(2 ^ 8, name='a', modulus=X ^ 8 + X ^ 4 + X ^ 3 + X + 1)
out_aes, phi_aes, S_aes, T_aes, U_aes = analyze("AES", Faes)

# FIPS-197 sanity anchor: multiplicative inverse table, e.g. inv(0x53)=0xCA
x53 = Faes.from_integer(0x53)
anchor = (x53 ^ 254).to_integer()
out_aes["fips197_anchor_inv_0x53"] = hex(anchor)
out_aes["fips197_anchor_ok"] = bool(anchor == 0xCA)

# --- Conway modulus (Sage default) ---
Fcon = GF(2 ^ 8, name='a')
out_con, phi_con, S_con, T_con, U_con = analyze("Conway", Fcon)

print(json.dumps(out_aes, indent=1))
print(json.dumps(out_con, indent=1))

# persist phi and slice matrices (AES modulus) for downstream programs
data = {
    "convention": "bit i of x = coeff of a^i; monomial mask bit i = x_i; "
                  "W7[i]=mask missing i; W6 ordered by PAIRS lex; W5 by TRIPLES lex; "
                  "row-vector action t = s * phi",
    "pairs": [[int(i), int(j)] for (i, j) in PAIRS],
    "triples": [[int(i), int(j), int(k)] for (i, j, k) in TRIPLES],
    "S": [[int(x) for x in row] for row in S_aes.rows()],
    "T": [[int(x) for x in row] for row in T_aes.rows()],
    "U": [[int(x) for x in row] for row in U_aes.rows()],
    "phi": [[int(x) for x in row] for row in phi_aes.rows()] if phi_aes is not None else None,
}
with open("/home/exedev/p/proofs/Scratch/mclower_p1_phi_aes.json", "w") as fh:
    json.dump(data, fh)
print("WROTE Scratch/mclower_p1_phi_aes.json")
