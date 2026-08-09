# Route C (concrete track): invariants vs covariants on the gauge
# orbit of Lambda(a,a') = mult_{a'}.MC.Aff.mult_a  (32x32 / GF(2)),
# and a test of whether the W2 Paar-1 spread (145-228, identity 226;
# .tasks/f5exp/docs/route-c-gauge-dual-ciphers.md, "witnessed
# computation") is explained by a shallow covariant.
#
# The invariant landscape, stated up front so the computation can
# confirm its vacuity rather than discover it:
#   * byte-block (i,j) of Lambda(a,a') is mult_{c_ij . a'}.Aff.mult_a
#     (MC block constants c_ij slide through by commutation), so every
#     block sits in the SAME two-sided coset  mult . Aff . mult  of
#     GL(8,2).  Block ranks are all 8; the block-level double-coset
#     class is constant.  One-line proof; the rank multiset is
#     computed below only to pin the claim to a run.  [I1]
#   * consequence: no bytewise-local invariant separates gauges.  Any
#     obstruction controlling SLP cost on this orbit must be global
#     (cross-block) — this is the answer to sub-question (a) for this
#     family, and it is negative for cheap invariants.
#
# What is NOT invariant, and might explain the W2 spread:
#   C1  total Hamming weight of Lambda(a,a') and the row-weight
#       profile.  Paar-1 is cancellation-free and greedy, so its cost
#       is (naive cost) - (pair savings) = (weight - 32) - savings;
#       the first-order term is pure weight.
#   C2  Paar-1 greedy SLP cost (reimplementation of the W2 metric;
#       deterministic tie-breaking, so numbers may differ from W2 by
#       a few XOR but the spread should reproduce).
#   I2  a weak but valid lower bound: #distinct rows of weight >= 2
#       (each such output needs its own final gate).  If this LB is
#       flat across gauges while Paar-1 swings 80, the swing is
#       entirely above the known-obstruction floor.
#
# Decision value of the correlation [C1 vs C2]:
#   Spearman high (>~0.8): the W2 spread is first-order weight.
#     Cancellation-capable heuristics (BP-class) specifically eat
#     weight, so expect the spread to collapse in the kill experiment
#     — evidence FOR flatness of true cost, route dead.
#   Spearman low (<~0.4): the spread lives in deeper combinatorial
#     structure that even Paar sees past weight — evidence AGAINST
#     flatness, the kill experiment has a real chance of surviving.
#
# Runtime estimate: Paar-1 on a dense 32x32 is the cost driver;
# 145 gauges x (a few hundred greedy rounds) — order 10 minutes in
# pure Sage.  SAMPLES below tunes it.

from collections import Counter

set_random_seed(0)
SAMPLES = 144          # random gauge pairs, plus (01,01) always

# ---- field and layer construction (same conventions as
# ---- routec_gauge_symmetries.sage, KAT-pinned there) ----------------
R.<x> = PolynomialRing(GF(2))
F.<z> = GF(2^8, modulus=x^8 + x^4 + x^3 + x + 1)

def vec(u):
    c = u.polynomial().list()
    return vector(GF(2), c + [0]*(8 - len(c)))

def f2byte(u):
    return sum(int(t) << i for i, t in enumerate(vec(u)))

def matof(f):
    return matrix(GF(2), [vec(f(z^j)) for j in range(8)]).transpose()

mult_cache = {a: matof(lambda u, a=a: a*u) for a in F if a != 0}
mult = lambda a: mult_cache[a]

Aff = matrix(GF(2), 8, 8,
             lambda i, j: 1 if (j - i) % 8 in (0, 4, 5, 6, 7) else 0)

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

def Lam(a, ap):
    return mult32(ap) * MC32 * Aff32 * mult32(a)

Fstar = [a for a in F if a != 0]

# ---- Paar-1 (greedy cancellation-free SLP, the W2 metric) -----------
def paar1(M):
    """XOR-gate count of the greedy common-pair heuristic.
    Deterministic: ties broken by lowest signal-index pair."""
    rows = [set(j for j in range(M.ncols()) if M[i, j])
            for i in range(M.nrows())]
    gates, nsig = 0, M.ncols()
    while any(len(r) >= 2 for r in rows):
        cnt = Counter()
        for r in rows:
            rr = sorted(r)
            for u in range(len(rr)):
                for v in range(u + 1, len(rr)):
                    cnt[(rr[u], rr[v])] += 1
        best = max(cnt.items(), key=lambda t: (t[1], -t[0][0], -t[0][1]))
        (i, j), _ = best
        gates += 1
        for r in rows:
            if i in r and j in r:
                r.discard(i); r.discard(j); r.add(nsig)
        nsig += 1
    return gates

# ---- invariants / covariants per gauge ------------------------------
def block(M, i, j):
    return M.submatrix(8*i, 8*j, 8, 8)

def stats(a, ap):
    L = Lam(a, ap)
    ranks = tuple(sorted(block(L, i, j).rank()
                         for i in range(4) for j in range(4)))
    rows = [tuple(r) for r in L.rows()]
    weight = sum(sum(map(int, r)) for r in rows)
    lb = len(set(r for r in rows if sum(map(int, r)) >= 2))
    return ranks, weight, lb, paar1(L)

gauges = [(F(1), F(1))]
seen = {(f2byte(F(1)), f2byte(F(1)))}
while len(gauges) < SAMPLES + 1:
    a, ap = choice(Fstar), choice(Fstar)
    key = (f2byte(a), f2byte(ap))
    if key not in seen:
        seen.add(key)
        gauges.append((a, ap))

results = []
rank_multisets = set()
print("  a    a'   weight   rowLB   paar1")
for a, ap in gauges:
    ranks, w, lb, cost = stats(a, ap)
    rank_multisets.add(ranks)
    results.append((f2byte(a), f2byte(ap), w, lb, cost))
    print(" %02x    %02x    %4d    %3d    %4d" %
          (f2byte(a), f2byte(ap), w, lb, cost))

# ---- summary --------------------------------------------------------
ws  = [r[2] for r in results]
lbs = [r[3] for r in results]
cs  = [r[4] for r in results]

print()
print("I1 block-rank multisets seen:", len(rank_multisets),
      " (must be 1, all ranks 8 — proved, run-confirmed)")
print("I2 row-LB range: [%d, %d]  (flat => spread is above the floor)"
      % (min(lbs), max(lbs)))
print("C1 weight range: [%d, %d]" % (min(ws), max(ws)))
print("C2 paar1 range:  [%d, %d]   identity gauge: %d  (W2 said 226)"
      % (min(cs), max(cs), results[0][4]))

def spearman(xs, ys):
    def ranks(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r, i = [0]*len(v), 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j+1]] == v[order[i]]:
                j += 1
            for t in range(i, j + 1):
                r[order[t]] = (i + j)/2 + 1
            i = j + 1
        return r
    rx, ry = ranks(xs), ranks(ys)
    n = len(xs)
    mx, my = sum(rx)/n, sum(ry)/n
    num = sum((rx[i]-mx)*(ry[i]-my) for i in range(n))
    den = sqrt(sum((rx[i]-mx)^2 for i in range(n)) *
               sum((ry[i]-my)^2 for i in range(n)))
    return float(num/den)

rho = spearman(ws, cs)
print("Spearman(weight, paar1) = %.3f" % rho)
print("  >~0.8: W2 spread is first-order weight; BP-class heuristics")
print("         eat weight; expect collapse in the kill experiment.")
print("  <~0.4: spread is structural; kill experiment may survive.")

# residual spread after regressing out weight (crude): spread of
# paar1 within the middle weight band
mid = sorted(results, key=lambda r: r[2])[len(results)//3 : 2*len(results)//3]
if mid:
    mc = [r[4] for r in mid]
    print("paar1 spread within middle-third weight band: [%d, %d]"
          % (min(mc), max(mc)))
