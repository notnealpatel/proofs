#!/usr/bin/env sage
"""
Q1: Is "2 outputs at schoolbook cost" forced at rank 7, or a gauge choice?

Strassen's C-side coefficient matrices W_k (2x2 each). The isotropy group acts
on the C-side by W_k -> P * W_k * Q for (P,Q) invertible (Lacelle sec 8
convention, W'_k = X^{-1} W_k Z^{-1}; as (X,Z) range over GL2^2 so do (P,Q)).
By de Groote every rank-7 scheme is in this single orbit, so sweeping (P,Q)
sweeps the C-side hit profiles of ALL rank-7 schemes.

Facts established:
  (a) floor: every output slice of <2,2,2> has matrix rank 2, so every output
      has >= 2 hits in every decomposition (verified below).
  (b) distribution of #outputs-at-floor over the ternary gauge scope, plus
      random wider gauges: min and max achievable.
"""
from itertools import product as iprod
import json

# Strassen C-side: c11=m1+m4-m5+m7; c12=m3+m5; c21=m2+m4; c22=m1-m2+m3+m6
# W_k[i][j] = coeff of m_k in c_{ij}
Wcols = [
    Matrix(QQ, [[1, 0], [0, 1]]),    # m1
    Matrix(QQ, [[0, 0], [1, -1]]),   # m2
    Matrix(QQ, [[0, 1], [0, 1]]),    # m3
    Matrix(QQ, [[1, 0], [1, 0]]),    # m4
    Matrix(QQ, [[-1, 1], [0, 0]]),   # m5
    Matrix(QQ, [[0, 0], [0, 1]]),    # m6
    Matrix(QQ, [[1, 0], [0, 0]]),    # m7
]

# (a) slice-rank floor: output slice C_{ik} of <2,2,2> is sum_j e_{ij} (x) e_{jk}
# as a 4x4 matrix in (A,B) space; its rank = inner dim = 2.
n = 2
for i in range(n):
    for k in range(n):
        S = Matrix(QQ, 4, 4)
        for j in range(n):
            S[i * n + j, j * n + k] = 1
        assert S.rank() == 2
print("floor check: every <2,2,2> output slice has rank 2 -> hits >= 2 always")

def profile(P, Q):
    """hits per output (sorted), and #outputs at floor (=2 hits)."""
    hits = {}
    for Wk in Wcols:
        M = P * Wk * Q
        for i in range(2):
            for j in range(2):
                if M[i, j] != 0:
                    hits[(i, j)] = hits.get((i, j), 0) + 1
    h = sorted(hits.values())
    clean = sum(1 for v in hits.values() if v == 2)
    return tuple(h), clean

# identity gauge = Strassen as published
h0, c0 = profile(identity_matrix(QQ, 2), identity_matrix(QQ, 2))
print(f"Strassen gauge: hits={h0} clean={c0}")

# ternary gauge scope: P,Q with entries in {-1,0,1}, invertible
tern = []
for e in iprod([-1, 0, 1], repeat=4):
    M = Matrix(QQ, 2, 2, list(e))
    if M.det() != 0:
        tern.append(M)
print(f"ternary invertible 2x2 matrices: {len(tern)}")

dist = {}
best = {}
for P in tern:
    for Q in tern:
        h, c = profile(P, Q)
        dist[c] = dist.get(c, 0) + 1
        if c not in best:
            best[c] = (h, [list(r) for r in P.rows()], [list(r) for r in Q.rows()])
print("clean-count distribution over ternary gauge sweep:")
for c in sorted(dist):
    print(f"  clean={c}: {dist[c]} gauges   example hit-profile {best[c][0]}")
    print(f"           P={best[c][1]} Q={best[c][2]}")

# wider random gauges (integer entries in [-5,5])
import random
random.seed(int(20260719))
seen = set()
for _ in range(20000):
    P = Matrix(QQ, 2, 2, [random.randint(-5, 5) for _ in range(4)])
    Q = Matrix(QQ, 2, 2, [random.randint(-5, 5) for _ in range(4)])
    if P.det() == 0 or Q.det() == 0:
        continue
    h, c = profile(P, Q)
    seen.add((h, c))
cs = sorted(set(c for _, c in seen))
print(f"random wide sweep: clean counts observed = {cs}")
print(f"min clean over all sweeps = {min(min(dist), min(cs))}, "
      f"max clean = {max(max(dist), max(cs))}")
