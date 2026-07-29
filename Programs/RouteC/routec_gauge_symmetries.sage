# Route C (concrete track): exact symmetry census of the gauged
# per-column round matrix at the k = k' = 0 gauge slice
#
#     Lambda(a,a') = mult_{a'} . MC . Aff . mult_a     (32x32 / GF(2))
#
# per .tasks/f5exp/docs/route-c-gauge-dual-ciphers.md ("telescoping"
# section, normal form).  Everything here is EXACT linear algebra —
# no heuristics.  Purpose: find or refute symmetries of the 255^2
# edge table W(a,a') = SLPcost(Lambda(a,a')) BEFORE anyone computes
# it.  A symmetry must map the gauged family to itself by cost-free
# (wire-permutation) equivalence; anything else does not collapse
# the table.
#
# Checks:
#   S1  fact-2: mult32(a) commutes with MC32, all 255 a.  [expect PASS]
#   S2  fact-3: frob32 . MC32 . frob32^-1 = MC32 with squared
#       constants (02,03,01,01) -> (04,05,01,01).       [expect PASS]
#   S2b is the frobenius matrix a wire permutation in the polynomial
#       basis?  (If not, the x8 Frobenius collapse of the table is
#       unavailable without a basis move.)               [expect NO]
#   S3  exact translation stabilizer
#         Stab = {(c,d) in F*^2 : mult(d).Aff.mult(c) = Aff}.
#       By S1 the 32x32 condition mult32(d).M.mult32(c) = M,
#       M = MC32.Aff32, reduces bytewise to this 8x8 condition.
#       |Stab| > 1  =>  the 255^2 table is constant on Stab-cosets.
#   S4  free-equivalence stabilizer: (c,d) such that
#       mult(d).Aff.mult(c) = P.Aff.Q for permutation matrices P,Q.
#       Wire permutations cost 0 in bitsliced code, so these also
#       collapse the table.  Tested by canonical labeling of the
#       bipartite row/column graph (parts held setwise fixed).
#   S5  Frobenius pair-squaring: is Lambda(a^2,a'^2) permutation-
#       equivalent to Lambda(a,a')?  Sampled.  YES on all samples
#       would collapse 255^2 by the x8 orbit action (a,a')->(a^2,a'^2).
#   S6  factorization: Lambda(a,a') = MC32 . diag4(N(a,a')),
#       N(a,a') = mult_{a'}.Aff.mult_a  (8x8).  The edge-table oracle
#       input is really the single 8x8 matrix N; injectivity of
#       (a,a') -> N is equivalent to S3 triviality (derived, and the
#       identity is verified on random pairs).
#   S7  transpose symmetry probe: by the transposition principle,
#       SLPcost(M^T) = SLPcost(M) for square M, so if
#       Lambda(a,a')^T were permutation-equivalent to Lambda(a',a)
#       the table would fold along its diagonal.  Sampled.
#
# Runtime estimate: S3 is 65k 8x8 products (fast); S4 is weight-
# profile-prefiltered canonical labelings (fast); S5/S7 are ~40
# canonizations of 64-vertex graphs (fast).  Whole script: minutes.

from collections import Counter

set_random_seed(0)

# ---- field and byte conventions -------------------------------------
R.<x> = PolynomialRing(GF(2))
F.<z> = GF(2^8, modulus=x^8 + x^4 + x^3 + x + 1)

def vec(u):
    c = u.polynomial().list()
    return vector(GF(2), c + [0]*(8 - len(c)))

def byte2f(b):
    return sum(F(1)*z^i for i in range(8) if (b >> i) & 1) if b else F(0)

def f2byte(u):
    return sum(int(t) << i for i, t in enumerate(vec(u)))

def matof(f):
    """8x8 GF(2) matrix of a GF(2)-linear map on F, columns = images
    of the basis 1, z, ..., z^7 (bit i = coefficient of z^i, LSB-first)."""
    return matrix(GF(2), [vec(f(z^j)) for j in range(8)]).transpose()

mult_cache = {a: matof(lambda u, a=a: a*u) for a in F if a != 0}
mult = lambda a: mult_cache[a]
frob = matof(lambda u: u^2)

# AES S-box output linear layer (FIPS-197): b'_i = b_i + b_{i+4} +
# b_{i+5} + b_{i+6} + b_{i+7}  (indices mod 8), constant 0x63 omitted
# (constants fold into round keys; they are runtime-free).
Aff = matrix(GF(2), 8, 8,
             lambda i, j: 1 if (j - i) % 8 in (0, 4, 5, 6, 7) else 0)

# convention sanity: reproduce known S-box values S(0)=63, S(1)=7c,
# S(53)=ed.  A failure here means the bit order is wrong and every
# downstream claim is about the wrong matrix.
def sbox(b):
    u = byte2f(b)
    v = u^254            # x -> x^-1 with 0 -> 0
    return f2byte(F(sum(int(t)*z^i for i, t in enumerate(Aff * vec(v))))) ^^ 0x63
assert sbox(0x00) == 0x63 and sbox(0x01) == 0x7c and sbox(0x53) == 0xed, \
    "byte/bit convention broken"
print("convention KATs: PASS (S(00)=63, S(01)=7c, S(53)=ed)")

# ---- 32x32 layer ----------------------------------------------------
c01, c02, c03 = F(1), z, z + 1
MCC = [[c02, c03, c01, c01],
       [c01, c02, c03, c01],
       [c01, c01, c02, c03],
       [c03, c01, c01, c02]]

def bd4(B):
    return block_diagonal_matrix([B]*4, subdivide=False)

MC32  = block_matrix(4, 4, [mult(MCC[i][j]) for i in range(4) for j in range(4)],
                     subdivide=False)
Aff32 = bd4(Aff)
mult32 = lambda a: bd4(mult(a))
frob32 = bd4(frob)

def Lam(a, ap):
    return mult32(ap) * MC32 * Aff32 * mult32(a)

Fstar = [a for a in F if a != 0]

# ---- S1: mult commutes with MC --------------------------------------
s1 = all(mult32(a) * MC32 == MC32 * mult32(a) for a in Fstar)
print("S1 mult32(a).MC32 == MC32.mult32(a) for all 255 a:", s1)

# ---- S2: frobenius conjugation squares the MC constants -------------
MC32sq = block_matrix(4, 4, [mult(MCC[i][j]^2) for i in range(4) for j in range(4)],
                      subdivide=False)
print("S2 frob32.MC32.frob32^-1 == MC32 with (04,05,01,01):",
      frob32 * MC32 * frob32^-1 == MC32sq)
print("S2b frob is a permutation matrix in the polynomial basis:",
      frob.is_permutation_matrix() if hasattr(frob, 'is_permutation_matrix')
      else all(sum(map(int, r)) == 1 for r in frob.rows()))

# ---- S3: exact translation stabilizer -------------------------------
stab = [(c, d) for c in Fstar for d in Fstar if mult(d) * Aff * mult(c) == Aff]
print("S3 |exact stabilizer|:", len(stab),
      "elements:", [(f2byte(c), f2byte(d)) for c, d in stab[:8]])
# |stab| = 1 (only (01,01))  =>  no translation collapse and, by the
# S6 derivation below, (a,a') -> N(a,a') is injective: 65025 distinct
# oracle inputs.

# ---- S4: free-equivalence (wire-permutation) stabilizer -------------
def canon(M):
    n, m = M.nrows(), M.ncols()
    G = Graph()
    G.add_vertices(range(n + m))
    for i in range(n):
        for j in range(m):
            if M[i, j]:
                G.add_edge(i, n + j)
    return G.canonical_label(
        partition=[list(range(n)), list(range(n, n + m))]).graph6_string()

def wprofile(M):
    return (tuple(sorted(sum(map(int, r)) for r in M.rows())),
            tuple(sorted(sum(map(int, c)) for c in M.columns())))

target_prof, target_can = wprofile(Aff), canon(Aff)
survivors = []
for c in Fstar:
    Ac = Aff * mult(c)
    for d in Fstar:
        M = mult(d) * Ac
        if wprofile(M) == target_prof and canon(M) == target_can:
            survivors.append((f2byte(c), f2byte(d)))
print("S4 |perm-equivalence stabilizer|:", len(survivors),
      "elements:", survivors[:16])

# ---- S5: Frobenius pair-squaring on the full 32x32 ------------------
hits, tries = 0, 20
for _ in range(tries):
    a, ap = choice(Fstar), choice(Fstar)
    if canon(Lam(a^2, ap^2)) == canon(Lam(a, ap)):
        hits += 1
print("S5 Lambda(a^2,a'^2) ~perm~ Lambda(a,a'):", hits, "/", tries,
      "sampled pairs  (20/20 => x8 orbit collapse of the table)")

# ---- S6: factorization through the 8x8 core -------------------------
ok = all((lambda a, ap: Lam(a, ap) ==
          MC32 * bd4(mult(ap) * Aff * mult(a)))(choice(Fstar), choice(Fstar))
         for _ in range(20))
print("S6 Lambda(a,a') == MC32.diag4(mult_{a'}.Aff.mult_a):", ok,
      " (oracle input is one 8x8 matrix; injectivity <=> S3 trivial)")

# ---- S7: transpose folding probe ------------------------------------
hits7 = sum(1 for _ in range(20)
            if (lambda a, ap: canon(Lam(a, ap).transpose()) ==
                canon(Lam(ap, a)))(choice(Fstar), choice(Fstar)))
print("S7 Lambda(a,a')^T ~perm~ Lambda(a',a):", hits7, "/ 20 sampled",
      " (20/20 => diagonal fold of the table via transposition principle)")
