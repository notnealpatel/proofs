#!/usr/bin/env sage
"""
Task 1: Find dmax via bit-packed matrix arithmetic over GF(2).

A 3x3 matrix over GF(2) is stored as a 9-bit integer (row-major).
Matrix multiply and trace are done with bitwise ops.
"""
import time
from itertools import combinations

start = time.time()
F2 = GF(2)

def mat_mul(a, b):
    """Multiply two 3x3 GF(2) matrices stored as 9-bit ints."""
    # a[i][j] = bit i*3+j of a
    # (a*b)[i][j] = XOR over k of a[i][k] & b[k][j]
    r = 0r
    for i in range(3r):
        for j in range(3r):
            v = 0r
            for k in range(3r):
                v ^^= ((a >> (i*3r+k)) & 1r) & ((b >> (k*3r+j)) & 1r)
            r |= (v << (i*3r+j))
    return r

def trace(a):
    """Trace of 3x3 GF(2) matrix: a[0][0] ^ a[1][1] ^ a[2][2]"""
    return ((a >> 0r) ^^ (a >> 4r) ^^ (a >> 8r)) & 1r

def tr_prod(a, b, c):
    """tr(a*b*c) over GF(2)"""
    return trace(mat_mul(mat_mul(a, b), c))

# Precompute all products (we'll need them repeatedly)
# Store mat_mul table? 512*512 = 262144 entries -- feasible
print("Precomputing multiplication table...")
t0 = time.time()
mul_table = {}
for a in range(512r):
    for b in range(512r):
        mul_table[(a,b)] = mat_mul(a, b)
print(f"  Done in {time.time()-t0:.1f}s, {len(mul_table)} entries")

# Actually that's too much memory/time. Let's just use the function directly.
# Better: precompute tr(a*b*c) for needed triples only.
# But first let's just precompute what we need step by step.

# Step 1: Z = {v in M3(F2)\{0} : tr(v^3) = 0}
# tr(v^3) = tr(v*v*v)
print("Computing Z...")
# Don't use the full mul_table, just compute directly
Z = []
for v in range(1r, 512r):  # exclude zero
    v2 = mat_mul(v, v)
    v3 = mat_mul(v2, v)
    if trace(v3) == 0r:
        Z.append(v)

print(f"|Z| = {len(Z)} (nonzero matrices with tr(v^3)=0)")

n = len(Z)

# Step 2: For all ordered pairs, check tr(vi^2 * vj) = 0
# A pair {i,j} is valid iff tr(vi^2*vj)=0 AND tr(vj^2*vi)=0
print("Computing valid pairs...")
t0 = time.time()

# Precompute squares
sq = {}
for v in Z:
    sq[v] = mat_mul(v, v)

pair_ok = set()
# For adjacency list
adj = [[] for _ in range(n)]

for i in range(n):
    vi = Z[i]
    vi2 = sq[vi]
    for j in range(i+1r, n):
        vj = Z[j]
        vj2 = sq[vj]
        # tr(vi^2 * vj) = 0?
        if trace(mat_mul(vi2, vj)) != 0r:
            continue
        # tr(vj^2 * vi) = 0?
        if trace(mat_mul(vj2, vi)) != 0r:
            continue
        pair_ok.add((i, j))
        adj[i].append(j)
        adj[j].append(i)

print(f"  Valid pairs: {len(pair_ok)} in {time.time()-t0:.1f}s")

# Step 3: For valid triples, check tr(vi*vj*vk) + tr(vi*vk*vj) = 0
# Only check triples where all 3 pairs are valid
print("Computing valid triples...")
t0 = time.time()

triple_ok = set()
for i in range(n):
    nbrs_i = set(adj[i])
    for j in adj[i]:
        if j <= i:
            continue
        # k must be > j and adjacent to both i and j
        nbrs_j = set(adj[j])
        common = sorted(nbrs_i & nbrs_j)
        for k in common:
            if k <= j:
                continue
            vi, vj, vk = Z[i], Z[j], Z[k]
            t1 = tr_prod(vi, vj, vk)
            t2 = tr_prod(vi, vk, vj)
            if (t1 ^^ t2) == 0r:
                triple_ok.add((i, j, k))

print(f"  Valid triples: {len(triple_ok)} in {time.time()-t0:.1f}s")

# Step 4: Maximum clique search with linear independence check
print("\nSearching for maximum dimension...")

def is_independent_f2(indices):
    """Check if Z[indices] are linearly independent as GF(2) vectors"""
    vecs = []
    for idx in indices:
        v = Z[idx]
        vecs.append(vector(F2, [(v >> b) & 1r for b in range(9r)]))
    return matrix(F2, vecs).rank() == len(vecs)

best_dim = 0r
best_basis = []

def search(current, candidates):
    global best_dim, best_basis
    d = len(current)
    if d > best_dim:
        if is_independent_f2(current):
            best_dim = d
            best_basis = list(current)
            print(f"  New best dim={d}, time={time.time()-start:.1f}s")

    if d + len(candidates) <= best_dim:
        return

    for ci in range(len(candidates)):
        c = candidates[ci]
        # Check pair condition with all current elements
        ok = True
        for idx in current:
            a, b = (min(idx, c), max(idx, c))
            if (a, b) not in pair_ok:
                ok = False
                break
        if not ok:
            continue

        # Check triple condition with all current pairs
        for pi in range(len(current)):
            for pj in range(pi+1r, len(current)):
                triple = tuple(sorted([current[pi], current[pj], c]))
                if triple not in triple_ok:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue

        # Check independence
        new_set = current + [c]
        if not is_independent_f2(new_set):
            continue

        # Recurse with remaining candidates that are adjacent to c
        nbrs_c = set(adj[c])
        new_cands = [x for x in candidates[ci+1r:] if x in nbrs_c]
        search(new_set, new_cands)

# Start search from each vertex
for sv in range(n):
    if n - sv <= best_dim:
        break
    cands = sorted(x for x in adj[sv] if x > sv)
    search([sv], cands)
    if sv % 50r == 0:
        elapsed = time.time() - start
        print(f"  Start vertex {sv}/{n}, best={best_dim}, elapsed={elapsed:.1f}s")

print(f"\n{'='*60}")
print(f"RESULT: dmax = {best_dim}")
print(f"Chow rank lower bound: 9 - {best_dim} = {9r - best_dim}")

if best_basis:
    print(f"\nWitness basis ({best_dim} matrices):")
    for i, idx in enumerate(best_basis):
        v = Z[idx]
        entries = [(v >> b) & 1r for b in range(9r)]
        M = matrix(F2, 3, 3, entries)
        print(f"  v{i+1r} (bits={v}): {entries}")
        print(M)
        print()

    # Full verification
    print("Full verification:")
    mats = []
    for idx in best_basis:
        v = Z[idx]
        mats.append(matrix(F2, 3, 3, [(v >> b) & 1r for b in range(9r)]))

    d = len(mats)
    all_ok = True
    for i in range(d):
        if (mats[i]^3).trace() != 0:
            print(f"  FAIL: tr(v{i}^3) != 0")
            all_ok = False
    for i in range(d):
        for j in range(d):
            if i != j and (mats[i]^2 * mats[j]).trace() != 0:
                print(f"  FAIL: tr(v{i}^2*v{j}) != 0")
                all_ok = False
    for i in range(d):
        for j in range(i+1r, d):
            for k in range(j+1r, d):
                if (mats[i]*mats[j]*mats[k]).trace() + (mats[i]*mats[k]*mats[j]).trace() != 0:
                    print(f"  FAIL: triple ({i},{j},{k})")
                    all_ok = False

    rk = matrix(F2, [vector(F2, m.list()) for m in mats]).rank()
    print(f"  Rank = {rk}, dim = {d}")

    if all_ok:
        print("  ALL CONDITIONS VERIFIED")

    # Polynomial substitution check
    R = PolynomialRing(GF(2), 'x', 9)
    xs = R.gens()
    X = matrix(R, 3, 3, list(xs))
    X3 = X * X * X
    Fpoly = sum(X3[ii,ii] for ii in range(3))

    T = PolynomialRing(GF(2), 't', d)
    ts = T.gens()
    vals = [T(0)] * 9r
    for idx_i in range(d):
        entries = mats[idx_i].list()
        for k in range(9r):
            vals[k] += ts[idx_i] * T(entries[k])
    F_sub = Fpoly(*vals)
    print(f"  F(sum ti*vi) = {F_sub}")
    if F_sub == 0:
        print("  POLYNOMIAL VANISHING CONFIRMED")
    else:
        print("  POLYNOMIAL VANISHING FAILED")

total = time.time() - start
print(f"\nTotal elapsed: {total:.1f}s")
