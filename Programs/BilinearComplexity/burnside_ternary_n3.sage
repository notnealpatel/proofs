"""
Burnside orbit count for rank-1 tensors of <3,3,3> over {-1,0,+1}.

The group: B_3^3 (signed permutation matrices of size 3, three copies)
acting via Kronecker embedding on {-1,0,+1}^9.

For signed permutation matrices P: P^{-T} = P (they're orthogonal).
So the embedding simplifies to: g1 = P (x) Q, g2 = Q (x) R, g3 = P (x) R.

Fixed points of a 9x9 signed permutation matrix sigma acting on
{-1,0,+1}^9: count vectors u with sigma*u = u.

Uses conjugacy class trick: B_3 has 10 conjugacy classes.
Burnside sum over 10^3 = 1000 class triples.
"""
import itertools
import sys

# --- Build B_3 (signed permutation matrices of size 3) ---
# B_3 = {monomial 3x3 matrices with entries in {-1, 0, +1}, one nonzero per row/col}
# Order = 2^3 * 3! = 48

from sage.all import *

F = ZZ
n = 3
N = n * n  # = 9

def build_Bn(n):
    """Build all elements of B_n as n x n matrices over ZZ."""
    from itertools import permutations, product as iproduct
    elems = []
    for perm in permutations(range(n)):
        for signs in iproduct([-1, 1], repeat=n):
            M = matrix(ZZ, n, n)
            for i in range(n):
                M[i, perm[i]] = signs[i]
            elems.append(M)
    return elems

print("Building B_3...")
B3 = build_Bn(n)
print(f"|B_3| = {len(B3)}")

# --- Conjugacy classes of B_3 ---
# Two elements are conjugate iff they have the same signed cycle type.
# We'll group by canonical form (sorted eigenvalue multiset won't work;
# use the actual conjugacy via Sage's matrix groups).

# Instead of abstract classification, just group by conjugacy:
# Two signed perm matrices M1, M2 are conjugate in B_n iff
# there exists P in B_n with P*M1*P^{-1} = M2.
# For n=3 with 48 elements, brute-force classification is instant.

def conjugacy_class_id(M, group):
    """Return a canonical representative for M's conjugacy class."""
    # Use the matrix's rational canonical form as invariant
    # (actually for signed perms, use sorted list of eigenvalues over QQbar)
    # Simpler: just use the characteristic polynomial
    return M.charpoly()

# Group by charpoly first (fast), then verify
from collections import defaultdict
classes_by_charpoly = defaultdict(list)
for M in B3:
    cp = M.charpoly()
    classes_by_charpoly[cp].append(M)

# Charpoly might not fully distinguish classes in B_n.
# Refine: within each charpoly group, do actual conjugacy check.
def are_conjugate_Bn(M1, M2, group):
    for P in group:
        if P * M1 * P.inverse() == M2:
            return True
    return False

print("Computing conjugacy classes of B_3...")
conjugacy_classes = []
assigned = set()

for i, M in enumerate(B3):
    if i in assigned:
        continue
    cls = [M]
    assigned.add(i)
    for j in range(i + 1, len(B3)):
        if j in assigned:
            continue
        if B3[j].charpoly() != M.charpoly():
            continue
        if are_conjugate_Bn(M, B3[j], B3):
            cls.append(B3[j])
            assigned.add(j)
    conjugacy_classes.append(cls)

print(f"Number of conjugacy classes of B_3: {len(conjugacy_classes)}")
for i, cls in enumerate(conjugacy_classes):
    print(f"  Class {i}: size {len(cls)}, rep =")
    print(f"    {list(cls[0].rows())}")
sys.stdout.flush()

# --- Kronecker product and fixed-point counting ---

def kron(A, B):
    """Kronecker product of two integer matrices."""
    return A.tensor_product(B)

def count_fixed_ternary(sigma_9x9):
    """
    Count nonzero vectors in {-1,0,+1}^9 fixed by sigma (a 9x9 signed perm matrix).

    sigma * u = u means each entry u[i] satisfies: sum_j sigma[i,j]*u[j] = u[i].
    Since sigma is a signed permutation, this means u[sigma_perm(i)] * sigma_sign(i) = u[i].

    We enumerate solutions directly by cycle structure.
    """
    # Extract permutation and signs from the signed perm matrix
    perm = [0] * 9
    signs = [0] * 9
    for i in range(9):
        for j in range(9):
            if sigma_9x9[i, j] != 0:
                perm[i] = j
                signs[i] = int(sigma_9x9[i, j])
                break

    # sigma * u = u means: for each i, signs[i] * u[perm[i]] = u[i]
    # Equivalently: u[i] = signs[i] * u[perm[i]]
    # Follow cycles: i -> perm[i] -> perm[perm[i]] -> ...
    # On a cycle (i0, i1, ..., i_{k-1}) with accumulated sign product s:
    #   u[i0] = s * u[i0], so (s-1)*u[i0] = 0.
    #   If s = 1: u[i0] is free (3 choices: -1, 0, +1)
    #   If s = -1: u[i0] = 0 (forced)
    #   If s = other: impossible for signed perms (s is always +-1 after a full cycle)

    visited = [False] * 9
    free_positions = 0  # number of free cycle-start positions

    for start in range(9):
        if visited[start]:
            continue
        # Trace the cycle and compute accumulated sign
        cycle_sign = 1
        pos = start
        while True:
            visited[pos] = True
            cycle_sign *= signs[pos]
            pos = perm[pos]
            if pos == start:
                break

        if cycle_sign == 1:
            free_positions += 1  # u at cycle start can be -1, 0, or +1
        # else cycle_sign == -1: u at cycle start must be 0

    # Total fixed vectors: 3^free_positions (including zero vector)
    # Nonzero fixed vectors: 3^free_positions - 1
    return int(3**free_positions - 1)

# --- Burnside computation ---

print(f"\nComputing Burnside sum over {len(conjugacy_classes)}^3 = {len(conjugacy_classes)**3} class triples...")
sys.stdout.flush()

total_weighted_fix = 0
group_order_cubed = len(B3)**3

n_triples = 0
for i, cls_P in enumerate(conjugacy_classes):
    P_rep = cls_P[0]
    P_size = len(cls_P)
    for j, cls_Q in enumerate(conjugacy_classes):
        Q_rep = cls_Q[0]
        Q_size = len(cls_Q)
        for k, cls_R in enumerate(conjugacy_classes):
            R_rep = cls_R[0]
            R_size = len(cls_R)

            # Compute g1 = P (x) Q, g2 = Q (x) R, g3 = P (x) R
            g1 = kron(P_rep, Q_rep)
            g2 = kron(Q_rep, R_rep)
            g3 = kron(P_rep, R_rep)

            fix1 = count_fixed_ternary(g1)
            fix2 = count_fixed_ternary(g2)
            fix3 = count_fixed_ternary(g3)

            weight = P_size * Q_size * R_size
            total_weighted_fix += weight * fix1 * fix2 * fix3
            n_triples += 1

n_orbits = total_weighted_fix // group_order_cubed
remainder = total_weighted_fix % group_order_cubed

print(f"\nRESULTS:")
print(f"|B_3|^3 = {group_order_cubed}")
print(f"Burnside weighted sum = {total_weighted_fix}")
print(f"Number of orbits = {n_orbits}")
print(f"Remainder (should be 0) = {remainder}")
free_est = float((3**9 - 1)**3) / float(group_order_cubed)
print(f"\nFree-action estimate: (3^9 - 1)^3 / |B_3|^3 = {int((3**9 - 1)**3)} / {int(group_order_cubed)} = {free_est:.1f}")
print(f"\nFor comparison, F2 orbit count for n=3: 211 (from burnside_n3.sage)")
print(f"Ternary has {'MORE' if n_orbits > 211 else 'FEWER'} orbits than F2: {n_orbits} vs 211")
