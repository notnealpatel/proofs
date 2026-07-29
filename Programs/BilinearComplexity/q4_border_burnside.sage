#!/usr/bin/env sage
"""
Q4: border/interior structure vs the 211 step-1 orbits over F2.

The border/interior split of C-outputs is NOT invariant under the full
isotropy group G = GL(3,F2)^3 (sandwich): within one G-orbit the C-side
factor sweeps every matrix of its rank, so per-orbit "border concentration"
is not well defined. Two computations that ARE well defined:

 1. The G-invariant obstruction: a C-side supported inside the border set
    {(1,2),(1,3),(2,1),(3,1)} has matrix rank <= 2 (verified exhaustively),
    so orbits with rank-3 C-side can never be gauged border-only.

 2. Refined Burnside under the border-preserving subgroup
    H = B x GL3 x B, B = block-diag(GL1 x GL2) (order 6 over F2):
    the largest subgroup whose C-side action P^{-T} C R^T preserves the
    border/interior coordinate split. Count H-orbits of nonzero rank-1
    tensors, and H-orbits with C-support confined to border / interior.
    This is the symmetry that survives once the partition is imposed --
    i.e. the orbit-compression available to a border/interior-constrained
    search (RECONCILE: orbit reduction at every peeling step).

Action conventions copied from burnside_n3.sage:
  (P,Q,R):  x by P (x) Q^{-T},  y by Q (x) R^{-T},  z by P^{-T} (x) R.
z = vec(C) row-major, so z-transform is C -> P^{-T} C R^{T}.
"""
from itertools import product as iprod

F = GF(2)
I9 = identity_matrix(F, 9)

# --- 1. invariant obstruction ---
border = [(0, 1), (0, 2), (1, 0), (2, 0)]
interior = [(0, 0), (1, 1), (1, 2), (2, 1), (2, 2)]
maxr = 0
for bits in iprod([0, 1], repeat=4):
    M = Matrix(F, 3, 3)
    for (pos, b) in zip(border, bits):
        M[pos] = b
    maxr = max(maxr, M.rank())
print(f"max rank of a border-supported 3x3 matrix over F2: {maxr}")
D = Matrix(F, 3, 3)
D[0, 0] = D[1, 1] = D[2, 2] = 1
print(f"interior-supported rank-3 example (diagonal): rank {D.rank()}")

# --- 2. Burnside counts ---
G3 = GL(3, F)
gl3_reps, gl3_sizes = [], []
for cc in G3.conjugacy_classes():
    gl3_reps.append(cc.representative().matrix())
    gl3_sizes.append(cc.cardinality())

# B: block-diag(1, GL2) inside GL3 -- enumerate all 6 elements
Bgrp = []
for g in GL(2, F):
    M = identity_matrix(F, 3).__copy__()
    m = g.matrix()
    for i in range(2):
        for j in range(2):
            M[1 + i, 1 + j] = m[i, j]
    M.set_immutable()
    Bgrp.append(M)
print(f"|B| = {len(Bgrp)}, |H| = {len(Bgrp)}^2 * 168 = {len(Bgrp)^2 * 168}")

# coordinate subspaces of z-space (row-major vec of C)
def coord_subspace(positions):
    V9 = VectorSpace(F, 9)
    return V9.subspace([V9.gen(3 * i + j) for (i, j) in positions])

S_border = coord_subspace(border)
S_interior = coord_subspace(interior)

def fixed_dim_on(subM, g):
    """dim of fixed space of g restricted to invariant subspace with basis rows of subM."""
    Bs = subM.basis_matrix()
    # solve: v in S, g v = v.  rows of Bs span S; g maps S to S.
    A = Bs * (g - I9).transpose()   # (v = w Bs) -> w Bs (g-I)^T = 0
    return A.left_kernel().dimension()

def burnside(pr_iter, use_border=None):
    """pr_iter yields (P, R, weight_PR); Q summed over conjugacy classes.
    use_border: None -> z unrestricted; else a subspace for z."""
    total = Integer(0)
    wsum = Integer(0)
    for (P, R, wpr) in pr_iter:
        P_invT = P.inverse().transpose()
        g3 = P_invT.tensor_product(R)
        if use_border is None:
            d3 = (g3 - I9).right_kernel().dimension()
        else:
            d3 = fixed_dim_on(use_border, g3)
        f3 = 2^d3 - 1
        for j in range(len(gl3_reps)):
            Qj = gl3_reps[j]
            g1 = P.tensor_product(Qj.inverse().transpose())
            g2 = Qj.tensor_product(R.inverse().transpose())
            d1 = (g1 - I9).right_kernel().dimension()
            d2 = (g2 - I9).right_kernel().dimension()
            total += gl3_sizes[j] * wpr * (2^d1 - 1) * (2^d2 - 1) * f3
        wsum += wpr
    order = wsum * 168
    assert total % order == 0, (total, order)
    return total // order

# sanity: full-G count must reproduce 211
def g_iter():
    for i in range(len(gl3_reps)):
        for j in range(len(gl3_reps)):
            yield (gl3_reps[i], gl3_reps[j], gl3_sizes[i] * gl3_sizes[j])
n_G = burnside(g_iter())
print(f"sanity, full-G orbit count (expect 211): {n_G}")

def h_iter():
    for P in Bgrp:
        for R in Bgrp:
            yield (P, R, 1)

n_H = burnside(h_iter())
n_H_border = burnside(h_iter(), use_border=S_border)
n_H_interior = burnside(h_iter(), use_border=S_interior)
print(f"H-orbits of rank-1 tensors (all z):        {n_H}")
print(f"H-orbits with C-support inside border:     {n_H_border}")
print(f"H-orbits with C-support inside interior:   {n_H_interior}")
print(f"H-orbits with mixed C-support:             {n_H - n_H_border - n_H_interior}")
print(f"symmetry price of imposing the partition: |G|/|H| = "
      f"{Integer(168^3) / Integer(len(Bgrp)^2 * 168)} (~2^{(Integer(168^3)/Integer(len(Bgrp)^2*168)).log(2).n(digits=3)})")
