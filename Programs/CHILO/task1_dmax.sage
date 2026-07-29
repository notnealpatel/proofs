#!/usr/bin/env sage
"""
Task 1: Find dmax = max dim of F2-subspace L <= M3(F2) on which
F = tr(X^3) vanishes formally (as a polynomial).

Strategy:
1. Precompute Z = {v in M3(F2) : tr(v^3)=0}, the set of matrices
   where the cubic diagonal condition holds.
2. For each pair (i,j) with i!=j in Z, precompute whether
   tr(vi^2*vj)=0 (the "bilinear" condition).
3. For each triple (i,j,k) with i<j<k in Z, precompute whether
   tr(vi*vj*vk)+tr(vi*vk*vj)=0.
4. Search for maximal cliques: a set S in Z is a valid basis iff
   all pairs and triples within S satisfy the conditions.
5. Use greedy extension + backtracking to find max dim.
"""
import json, time
from itertools import combinations

start = time.time()

F2 = GF(2)

# Enumerate all 512 matrices in M3(F2)
all_mats = []
for bits in range(512r):
    entries = [(bits >> i) & 1r for i in range(9r)]
    M = matrix(F2, 3, 3, entries)
    all_mats.append(M)

print(f"Total matrices: {len(all_mats)}")

# Step 1: Filter Z = {v : tr(v^3)=0}
Z = []
Z_indices = []
for idx in range(512r):
    M = all_mats[idx]
    if (M^3).trace() == 0:
        Z.append(M)
        Z_indices.append(idx)

print(f"|Z| = {len(Z)} (matrices with tr(v^3)=0)")

# Index Z elements 0..len(Z)-1
n = len(Z)

# Step 2: Precompute pairwise condition tr(vi^2*vj)=0 for all ordered pairs
# Store as a set of valid unordered pairs for the SYMMETRIC condition:
# For a basis, we need tr(vi^2*vj)=0 AND tr(vj^2*vi)=0 for all i!=j
# So pair (i,j) is valid iff both directions work.
print("Precomputing pairwise conditions...")
pair_ok = set()  # set of frozenset({i,j}) where both tr(vi^2*vj)=0 and tr(vj^2*vi)=0
for i in range(n):
    for j in range(i+1r, n):
        vi, vj = Z[i], Z[j]
        if (vi^2 * vj).trace() == 0 and (vj^2 * vi).trace() == 0:
            pair_ok.add((i, j))

print(f"Valid pairs: {len(pair_ok)}")

# Step 3: Precompute triple condition
# tr(vi*vj*vk) + tr(vi*vk*vj) = 0 for all i<j<k in basis
print("Precomputing triple conditions...")
triple_ok = set()
for i in range(n):
    for j in range(i+1r, n):
        if (i, j) not in pair_ok:
            continue
        for k in range(j+1r, n):
            if (i, k) not in pair_ok or (j, k) not in pair_ok:
                continue
            vi, vj, vk = Z[i], Z[j], Z[k]
            if (vi*vj*vk).trace() + (vi*vk*vj).trace() == 0:
                triple_ok.add((i, j, k))

print(f"Valid triples: {len(triple_ok)}")
print(f"Precomputation time: {time.time()-start:.1f}s")

# Step 4: Search for maximum clique
# A valid basis of dimension d is a set S of d elements from Z such that:
# - all pairs in S are in pair_ok
# - all triples in S are in triple_ok
# - they are linearly independent over F2

def is_valid_extension(current_set, new_idx):
    """Check if adding new_idx to current_set maintains all conditions"""
    # Check all pairs with existing elements
    for idx in current_set:
        a, b = min(idx, new_idx), max(idx, new_idx)
        if (a, b) not in pair_ok:
            return False
    # Check all triples with existing pairs
    for i in range(len(current_set)):
        for j in range(i+1r, len(current_set)):
            triple = tuple(sorted([current_set[i], current_set[j], new_idx]))
            if triple not in triple_ok:
                return False
    return True

def is_independent(mats):
    """Check if a list of matrices is linearly independent over F2"""
    if len(mats) == 0:
        return True
    vecs = [vector(F2, m.list()) for m in mats]
    return matrix(F2, vecs).rank() == len(mats)

# Build adjacency for pair_ok (symmetric)
adj = [set() for _ in range(n)]
for (i, j) in pair_ok:
    adj[i].add(j)
    adj[j].add(i)

# Greedy + backtracking search
best_basis = []
best_dim = 0

def search(current_indices, candidates):
    global best_basis, best_dim
    d = len(current_indices)
    if d > best_dim:
        best_dim = d
        best_basis = list(current_indices)
        mats = [Z[i] for i in current_indices]
        print(f"  New best dim={d}, matrices: {[m.list() for m in mats]}")

    if d + len(candidates) <= best_dim:
        return  # prune: can't beat current best

    for ci in range(len(candidates)):
        c = candidates[ci]
        if is_valid_extension(current_indices, c):
            new_mats = [Z[i] for i in current_indices] + [Z[c]]
            if is_independent(new_mats):
                # Filter remaining candidates
                new_cands = []
                for nc in candidates[ci+1r:]:
                    # Quick filter: must be adjacent to c in pair graph
                    if nc in adj[c]:
                        new_cands.append(nc)
                search(current_indices + [c], new_cands)

print("\nSearching for maximum dimension subspace...")
# Start from each vertex
for start_v in range(n):
    if n - start_v <= best_dim:
        break  # remaining vertices can't improve
    cands = sorted(adj[start_v] & set(range(start_v+1r, n)))
    search([start_v], cands)
    if start_v % 50r == 0:
        print(f"  Starting vertex {start_v}/{n}, current best dim={best_dim}")

print(f"\ndmax = {best_dim}")
print(f"Chow rank lower bound: 9 - {best_dim} = {9r - best_dim}")

# Print witness
if best_basis:
    print("\nWitness basis (as 3x3 matrices over F2, row-major flat):")
    for i, idx in enumerate(best_basis):
        M = Z[idx]
        print(f"  v{i+1r} = {M.list()}")
        print(f"       = {M}")

    # Verify the witness
    print("\nVerifying witness...")
    mats = [Z[i] for i in best_basis]
    d = len(mats)
    ok = True
    for i in range(d):
        if (mats[i]^3).trace() != 0:
            print(f"  FAIL: tr(v{i}^3) != 0")
            ok = False
    for i in range(d):
        for j in range(d):
            if i != j and (mats[i]^2 * mats[j]).trace() != 0:
                print(f"  FAIL: tr(v{i}^2*v{j}) != 0")
                ok = False
    for i in range(d):
        for j in range(i+1r, d):
            for k in range(j+1r, d):
                if (mats[i]*mats[j]*mats[k]).trace() + (mats[i]*mats[k]*mats[j]).trace() != 0:
                    print(f"  FAIL: triple ({i},{j},{k})")
                    ok = False
    print(f"  Linear independence: rank = {matrix(F2, [vector(F2, m.list()) for m in mats]).rank()}")
    if ok:
        print("  ALL CONDITIONS VERIFIED")

    # Also verify by polynomial substitution
    R = PolynomialRing(GF(2), 'x', 9)
    xs = R.gens()
    X = matrix(R, 3, 3, list(xs))
    X3 = X * X * X
    Fpoly = sum(X3[i,i] for i in range(3))

    T = PolynomialRing(GF(2), 't', d)
    ts = T.gens()
    vals = [T(0)] * 9r
    for idx_i in range(d):
        entries = mats[idx_i].list()
        for k in range(9r):
            vals[k] += ts[idx_i] * T(entries[k])
    F_sub = Fpoly(vals[0r], vals[1r], vals[2r], vals[3r], vals[4r],
                  vals[5r], vals[6r], vals[7r], vals[8r])
    print(f"  Polynomial substitution F(sum ti*vi) = {F_sub}")
    assert F_sub == 0, "Polynomial check failed!"
    print("  POLYNOMIAL VANISHING CONFIRMED")

elapsed = time.time() - start
print(f"\nTotal time: {elapsed:.1f}s")
