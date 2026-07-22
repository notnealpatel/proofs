# b1_levelcut_222.sage — Bf1 (Pl25 line B): level-cut probe for the
# Strassen <2,2,2> decomposition over F_2 at the pinned published
# 1969 gauge.
#
# WRITTEN BY Bf1, NOT RUN BY Bf1. Execution is USER-gated (card Hu14).
# Target runtime: seconds (128 subsets, 128-state DPs).
#
# Conventions (match the Pl25 campaign):
#   * peak counts residuals at j >= 1 only (nonempty peel sets S);
#     S = emptyset (weight nnz(T)) is NOT counted.
#   * f(S) = wt(T - sigma(S)) with sigma(S) = sum_{i in S} tau_i;
#     over F_2 this depends only on the SET S, so the 7! = 5040
#     orderings collapse to the 2^7 = 128 subset weights.
#   * All tensors live in F_2^64, index = 16*x + 4*y + z with the
#     Strassen.lean packing x = 2i+j (A), y = 2j+l (B), z = 2l+i
#     (C transposed).
#
# Output sections (deterministic; Bf2 parses by eye):
#   SECTION 0  instance + self-asserts (aborts loudly on failure)
#   SECTION 1  weight table f(S) for all 128 subsets S
#   SECTION 2  minpeak(D) by DP over the subset lattice + one
#              optimal ordering with its weight trajectory
#   SECTION 3  for t = minpeak(D)+1 down to 1: heavy family H_t,
#              per-level census, blocking verdict, greedy minimal
#              blocking sub-family, level-cut verdict

import sys

# --------------------------------------------------------------------
# Transcription: Proofs/Proofs/BilinearComplexity/Strassen.lean :44-77
# (canonical published 1969 gauge; header pins the M1-M7 table).
# Rows verbatim over Z, exactly as in the Lean source; reduced mod 2
# on coercion into GF(2) below (so -1 |-> 1).
# --------------------------------------------------------------------
U_rows = [
    [1, 0, 0, 1],    # M1 : A11 + A22
    [0, 0, 1, 1],    # M2 : A21 + A22
    [1, 0, 0, 0],    # M3 : A11
    [0, 0, 0, 1],    # M4 : A22
    [1, 1, 0, 0],    # M5 : A11 + A12
    [-1, 0, 1, 0],   # M6 : A21 - A11
    [0, 1, 0, -1],   # M7 : A12 - A22
]
V_rows = [
    [1, 0, 0, 1],    # M1 : B11 + B22
    [1, 0, 0, 0],    # M2 : B11
    [0, 1, 0, -1],   # M3 : B12 - B22
    [-1, 0, 1, 0],   # M4 : B21 - B11
    [0, 0, 0, 1],    # M5 : B22
    [1, 1, 0, 0],    # M6 : B11 + B12
    [0, 0, 1, 1],    # M7 : B21 + B22
]
W_rows = [
    [1, 0, 0, 1],    # M1 -> C11,  C22
    [0, 1, 0, -1],   # M2 -> C21, -C22
    [0, 0, 1, 1],    # M3 -> C12,  C22
    [1, 1, 0, 0],    # M4 -> C11,  C21
    [-1, 0, 1, 0],   # M5 -> -C11, C12
    [0, 0, 0, 1],    # M6 -> C22
    [1, 0, 0, 0],    # M7 -> C11
]

F = GF(2)
V64 = VectorSpace(F, 64)
r = 7
NSUB = 2^r  # 128


def idx(x, y, z):
    return 16 * x + 4 * y + z


# Rank-one triads tau_s in F_2^64.
triads = []
for s in range(r):
    v = V64(0)
    for x in range(4):
        for y in range(4):
            for z in range(4):
                v[idx(x, y, z)] = F(U_rows[s][x]) * F(V_rows[s][y]) * F(W_rows[s][z])
    triads.append(v)

# matMulTensor F_2 2 2 2, built INDEPENDENTLY of the triads from the
# trace(X*Y*Z) support { (2i+j, 2j+l, 2l+i) : i,j,l in {0,1} }
# (Strassen.lean header, re-verified there by #eval).
T = V64(0)
for i in range(2):
    for j in range(2):
        for l in range(2):
            T[idx(2 * i + j, 2 * j + l, 2 * l + i)] = F(1)

# ---------------------------- SECTION 0 -----------------------------
print("SECTION 0: instance + self-asserts")
print("  tensor: <2,2,2> matmul over F_2, packing x=2i+j, y=2j+l, z=2l+i")
print("  decomposition: 7 Strassen triads, published 1969 gauge")
print("  peak convention: j >= 1 (nonempty peel sets only)")

nnzT = T.hamming_weight()
print("  nnz(T) = %d" % nnzT)
if nnzT != 8:
    print("ABORT: nnz(matMulTensor F_2 2 2 2) = %d, expected 8" % nnzT)
    sys.exit(1)

sum_triads = V64(0)
for s in range(r):
    sum_triads = sum_triads + triads[s]
if sum_triads != T:
    print("ABORT: the 7 triads do NOT sum to the 2x2x2 matmul tensor over F_2.")
    print("  sum has weight %d; (sum - T) has weight %d"
          % (sum_triads.hamming_weight(), (sum_triads + T).hamming_weight()))
    sys.exit(1)
print("  ASSERT OK: sum of the 7 triads == matMulTensor F_2 2 2 2")

for s in range(r):
    if triads[s].hamming_weight() == 0:
        print("ABORT: triad M%d vanishes mod 2 (rank drop)" % (s + 1))
        sys.exit(1)
print("  ASSERT OK: all 7 triads nonzero mod 2 "
      "(weights: %s)" % [triads[s].hamming_weight() for s in range(r)])


def label(mask):
    """Deterministic subset label, e.g. {M1,M3,M7}; {} for empty."""
    mem = ["M%d" % (s + 1) for s in range(r) if (mask >> s) & 1]
    return "{" + ",".join(mem) + "}"


def pop(mask):
    return Integer(mask).popcount()

ONE = int(1)

def bit_test(mask, s):
    return (int(mask) >> s) & ONE

def bit_clear(mask, s):
    return int(mask) & ~(ONE << s)


# f(S) for all 128 subsets (S encoded as bitmask, bit s = triad M_{s+1}).
f = [0] * NSUB
for mask in range(NSUB):
    acc = V64(T)
    for s in range(r):
        if (mask >> s) & 1:
            acc = acc + triads[s]
    f[mask] = acc.hamming_weight()

if f[0] != nnzT:
    print("ABORT: f(emptyset) = %d != nnz(T) = %d" % (f[0], nnzT))
    sys.exit(1)
if f[NSUB - 1] != 0:
    print("ABORT: f(full set) = %d != 0" % f[NSUB - 1])
    sys.exit(1)
print("  ASSERT OK: f(emptyset) = nnz(T) = %d, f({M1..M7}) = 0" % nnzT)

# Deterministic subset order: by (cardinality, bitmask value).
order = [int(m) for m in sorted(range(NSUB), key=lambda m: (pop(m), m))]

# ---------------------------- SECTION 1 -----------------------------
print("")
print("SECTION 1: weight table  f(S) = wt(T - sigma(S)), all 128 subsets")
for m in range(r + 1):
    lev = [mask for mask in order if pop(mask) == m]
    print("  level m=%d (%d subsets):" % (m, len(lev)))
    for mask in lev:
        print("    f%-25s = %2d" % (label(mask), f[mask]))
    print("    level min = %2d, level max = %2d"
          % (min(f[mask] for mask in lev), max(f[mask] for mask in lev)))

# ---------------------------- SECTION 2 -----------------------------
# DP over the subset lattice (Bellman on the Hasse DAG):
#   g(emptyset) = 0
#   g(S) = max( f(S), min_{i in S} g(S \ {i}) )   for S nonempty
#   minpeak(D) = g([r])   -- nonempty-S convention: f(emptyset) is
#   never max'ed in.
g = [0] * NSUB
for mask in order:
    if mask == 0:
        continue
    best = min(g[bit_clear(mask, s)] for s in range(r) if bit_test(mask, s))
    g[mask] = max(f[mask], best)
minpeak = g[NSUB - 1]

# Reconstruct one optimal ordering (backward greedy, smallest-index
# tie-break => deterministic).
chain = [NSUB - 1]
cur = NSUB - 1
while cur != 0:
    cands = [(g[bit_clear(cur, s)], s) for s in range(r) if bit_test(cur, s)]
    cands.sort()
    cur = bit_clear(cur, cands[0][1])
    chain.append(cur)
chain.reverse()  # emptyset -> ... -> full set
traj = [f[mask] for mask in chain[1:]]  # j >= 1
if max(traj) != minpeak:
    print("ABORT: reconstructed chain peak %d != DP minpeak %d"
          % (max(traj), minpeak))
    sys.exit(1)
peel_order = []
for j in range(r):
    added = int(chain[j + 1]) & ~int(chain[j])
    peel_order.append("M%d" % (Integer(added).exact_log(2) + 1))

print("")
print("SECTION 2: minpeak by subset-lattice DP (5040 orderings ~ 128 subsets)")
print("  minpeak(D) = %d   [fixed published gauge, F_2, j >= 1]" % minpeak)
print("  one optimal peel order: %s" % " -> ".join(peel_order))
print("  weight trajectory (j=1..7): %s   (peak = %d)"
      % (traj, max(traj)))
print("  cross-refs:")
print("    * orbit-min sanity: minpeak*(<2,2,2>) = 10 EXACT (CONTEXT),")
print("      so the fixed-gauge value must be >= 10: %s"
      % ("OK" if minpeak >= 10 else "VIOLATED -- FINDING, surface immediately"))
print("    * Nc1 (Lean native_decide, same gauge, same j>=1 convention)")
print("      must report exactly %d; any mismatch is a FINDING." % minpeak)


# ---------------------------- SECTION 3 -----------------------------
def blocks(family_set):
    """Does family_set (set of nonempty masks) meet every maximal chain?
    reach(S) = S not in family and some (S minus a point) reachable."""
    reach = [False] * NSUB
    reach[0] = True
    for mask in order:
        if mask == 0 or mask in family_set:
            continue
        reach[mask] = any(reach[bit_clear(mask, s)]
                          for s in range(r) if bit_test(mask, s))
    return not reach[NSUB - 1]


def avoiding_chain(family_set):
    """A maximal chain avoiding family_set at all nonempty levels
    (assumes one exists). Deterministic forward greedy."""
    reach = [False] * NSUB
    reach[0] = True
    for mask in order:
        if mask == 0 or mask in family_set:
            continue
        reach[mask] = any(reach[bit_clear(mask, s)]
                          for s in range(r) if bit_test(mask, s))
    # walk back from full set
    ch = [NSUB - 1]
    cur = NSUB - 1
    while cur != 0:
        for s in range(r):
            prev = bit_clear(cur, s)
            if bit_test(cur, s) and reach[prev] and (prev == 0 or prev not in family_set):
                cur = prev
                ch.append(cur)
                break
    ch.reverse()
    return ch


print("")
print("SECTION 3: threshold analysis, t = %d down to 1" % (minpeak + 1))
print("  H_t = { S nonempty : f(S) >= t };  level cut = all m-subsets, some m")

for t in range(minpeak + 1, 0, -1):
    H = set(mask for mask in range(1, NSUB) if f[mask] >= t)
    counts = [0] * (r + 1)
    for mask in H:
        counts[pop(mask)] += 1
    full_levels = [m for m in range(1, r + 1)
                   if counts[m] == binomial(r, m)]
    b = blocks(H)
    print("")
    print("  t = %d: |H_t| = %d" % (t, len(H)))
    print("    per-level census (heavy/total): %s"
          % ", ".join("m=%d: %d/%d" % (m, counts[m], binomial(r, m))
                      for m in range(1, r + 1)))
    print("    full heavy levels: %s"
          % (full_levels if full_levels else "NONE"))
    print("    H_t blocks every maximal chain: %s" % b)
    if t > minpeak and b:
        print("    ABORT: H_%d blocks but minpeak = %d (duality violated)"
              % (t, minpeak))
        sys.exit(1)
    if t <= minpeak and not b:
        print("    ABORT: H_%d fails to block but minpeak = %d "
              "(duality violated)" % (t, minpeak))
        sys.exit(1)
    if not b:
        ch = avoiding_chain(H)
        print("    witness avoiding chain (weights j=1..7): %s"
              % [f[mask] for mask in ch[1:]])
        print("    witness chain subsets: %s"
              % " -> ".join(label(mask) for mask in ch[1:]))
        continue
    # Greedy inclusion-minimal blocking sub-family. Deterministic:
    # scan H_t by (cardinality, mask) and drop whatever stays blocking.
    B = set(H)
    for mask in sorted(H, key=lambda m2: (pop(m2), m2)):
        B.discard(mask)
        if not blocks(B):
            B.add(mask)
    Bcounts = [0] * (r + 1)
    for mask in B:
        Bcounts[pop(mask)] += 1
    is_level_cut = any(
        len(B) == binomial(r, m) and Bcounts[m] == binomial(r, m)
        for m in range(1, r + 1))
    print("    greedy minimal blocking sub-family: size %d, "
          "per-level %s" % (len(B),
          ", ".join("m=%d: %d" % (m, Bcounts[m])
                    for m in range(1, r + 1) if Bcounts[m] > 0)))
    print("    minimal sub-family is a LEVEL CUT: %s" % is_level_cut)
    if not is_level_cut:
        print("    irregular cut, explicit members:")
        for mask in sorted(B, key=lambda m2: (pop(m2), m2)):
            print("      %-25s f = %2d" % (label(mask), f[mask]))

print("")
print("DONE (b1_levelcut_222.sage, deterministic output)")
