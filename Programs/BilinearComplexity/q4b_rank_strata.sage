#!/usr/bin/env sage
"""
(a) Stratify the 211 G-orbits of nonzero rank-1 tensors by the matrix rank of
    the C-side factor. Rank is the ONLY G-invariant of the C-side, and it
    decides border-gaugeability: rank<=2 C-sides can be gauged into the border
    set (reps e12, e12+e21 are border-supported), rank-3 C-sides cannot
    (border-supported matrices have rank <=2).
    Burnside with z restricted to the rank-r stratum: for each class pair
    (P,R) enumerate the fixed subspace of C -> P^{-T} C R^T and count fixed
    matrices of each rank directly (fixed spaces have dim <= 9, cheap).

(b) Laderman's gauge-invariant column signature: (rank U_k, rank V_k, rank W_k)
    per product, viewing each factor column as a 3x3 matrix. This is the
    testable form of the border/interior split for Johnson-McLoughlin reps.
"""
from collections import Counter

F = GF(2)
I9 = identity_matrix(F, 9)
G3 = GL(3, F)
reps, sizes = [], []
for cc in G3.conjugacy_classes():
    reps.append(cc.representative().matrix())
    sizes.append(cc.cardinality())
nc = len(reps)

def rank_counts_fixed_z(P, R):
    """counts[r] = # fixed matrices of C -> P^{-T} C R^T with rank r."""
    g3 = P.inverse().transpose().tensor_product(R)
    K = (g3 - I9).right_kernel()
    counts = Counter()
    for v in K:
        M = Matrix(F, 3, 3, list(v))
        counts[M.rank()] += 1
    return counts

order_G3 = Integer(168)
sums = {1: Integer(0), 2: Integer(0), 3: Integer(0)}
for i in range(nc):
    Pi = reps[i]
    for k in range(nc):
        Rk = reps[k]
        cz = rank_counts_fixed_z(Pi, Rk)
        if all(cz[r] == 0 for r in (1, 2, 3)):
            continue
        for j in range(nc):
            Qj = reps[j]
            g1 = Pi.tensor_product(Qj.inverse().transpose())
            g2 = Qj.tensor_product(Rk.inverse().transpose())
            d1 = (g1 - I9).right_kernel().dimension()
            d2 = (g2 - I9).right_kernel().dimension()
            w = sizes[i] * sizes[j] * sizes[k] * (2^d1 - 1) * (2^d2 - 1)
            for r in (1, 2, 3):
                sums[r] += w * cz[r]

tot = 0
for r in (1, 2, 3):
    assert sums[r] % order_G3^3 == 0
    n = sums[r] // order_G3^3
    tot += n
    print(f"G-orbits with C-side rank {r}: {n}")
print(f"total (expect 211): {tot}")
print("border-gaugeable orbits (rank<=2):", tot - sums[3] // order_G3^3)

# (b) Laderman signature
load("laderman_matrices.sage")
def colmat(M, k):
    return Matrix(QQ, 3, 3, [M[i, k] for i in range(9)])
sig = []
for k in range(23):
    ru = colmat(U, k).rank()
    rv = colmat(V, k).rank()
    rw = colmat(W, k).rank()
    supp = len([i for i in range(9) if W[i, k] != 0])
    sig.append((k + 1, ru, rv, rw, supp))
print("\nLaderman per-product (k, rankU, rankV, rankW, |suppW|):")
for s in sig:
    print("  m%-3d  %d %d %d   %d" % s)
print("C-side rank profile:", sorted(Counter(s[3] for s in sig).items()))
print("rank-1 C-side products:", [s[0] for s in sig if s[3] == 1])
