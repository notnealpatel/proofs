#!/usr/bin/env sage
"""
Minimal dmax search. No multiplication table. Pure bitops.
"""
import time
start = time.time()
F2 = GF(2)

def mat_mul(a, b):
    r = 0r
    for i in range(3r):
        for j in range(3r):
            v = 0r
            for k in range(3r):
                v ^^= ((a >> (i*3r+k)) & 1r) & ((b >> (k*3r+j)) & 1r)
            r |= (v << (i*3r+j))
    return r

def trace(a):
    return ((a >> 0r) ^^ (a >> 4r) ^^ (a >> 8r)) & 1r

# Z = nonzero matrices with tr(v^3)=0
Z = []
for v in range(1r, 512r):
    v2 = mat_mul(v, v)
    v3 = mat_mul(v2, v)
    if trace(v3) == 0r:
        Z.append(v)

n = len(Z)
print(f"|Z| = {n}, elapsed: {time.time()-start:.1f}s")

# Precompute squares
sq = [0r] * 512r
for v in Z:
    sq[v] = mat_mul(v, v)

# Pair condition: tr(vi^2*vj)=0 AND tr(vj^2*vi)=0
print("Computing pairs...")
adj = [[] for _ in range(n)]
pair_set = set()
for i in range(n):
    vi = Z[i]
    vi2 = sq[vi]
    for j in range(i+1r, n):
        vj = Z[j]
        vj2 = sq[vj]
        if trace(mat_mul(vi2, vj)) != 0r:
            continue
        if trace(mat_mul(vj2, vi)) != 0r:
            continue
        pair_set.add((i, j))
        adj[i].append(j)
        adj[j].append(i)

print(f"Valid pairs: {len(pair_set)}, elapsed: {time.time()-start:.1f}s")

# Convert adj to sets for fast intersection
adj_set = [set(a) for a in adj]

# Triple condition cache (lazy)
triple_cache = {}

def triple_ok(i, j, k):
    """Check tr(vi*vj*vk) + tr(vi*vk*vj) = 0, with i<j<k"""
    key = (i, j, k)
    if key in triple_cache:
        return triple_cache[key]
    vi, vj, vk = Z[i], Z[j], Z[k]
    t1 = trace(mat_mul(mat_mul(vi, vj), vk))
    t2 = trace(mat_mul(mat_mul(vi, vk), vj))
    result = ((t1 ^^ t2) == 0r)
    triple_cache[key] = result
    return result

def is_indep(indices):
    vecs = []
    for idx in indices:
        v = Z[idx]
        vecs.append(vector(F2, [(v >> b) & 1r for b in range(9r)]))
    return matrix(F2, vecs).rank() == len(vecs)

best_dim = 0r
best_basis = []

def search(current, cand_set):
    global best_dim, best_basis
    d = len(current)
    if d > best_dim:
        if is_indep(current):
            best_dim = d
            best_basis = list(current)
            print(f"  dim={d} at {time.time()-start:.1f}s, indices={current[:6]}")
    if d + len(cand_set) <= best_dim:
        return
    cands = sorted(cand_set)
    for ci in range(len(cands)):
        c = cands[ci]
        # Pair check
        ok = True
        for idx in current:
            a, b = (min(idx, c), max(idx, c))
            if (a, b) not in pair_set:
                ok = False
                break
        if not ok:
            continue
        # Triple check
        for pi in range(len(current)):
            for pj in range(pi+1r, len(current)):
                t = tuple(sorted([current[pi], current[pj], c]))
                if not triple_ok(*t):
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue
        new_set = current + [c]
        if not is_indep(new_set):
            continue
        # New candidates: must be adjacent to c and have index > c
        new_cands = cand_set & adj_set[c]
        new_cands = {x for x in new_cands if x > c}
        search(new_set, new_cands)

print("Searching...")
for sv in range(n):
    if n - sv <= best_dim:
        break
    cands = {x for x in adj[sv] if x > sv}
    search([sv], cands)
    if sv % 50r == 0:
        print(f"  sv={sv}/{n}, best={best_dim}, elapsed={time.time()-start:.1f}s")

print(f"\ndmax = {best_dim}")
print(f"Lower bound: 9 - {best_dim} = {9r - best_dim}")

if best_basis:
    print(f"\nWitness ({best_dim} matrices, row-major 9-bit):")
    for i, idx in enumerate(best_basis):
        v = Z[idx]
        entries = [(v >> b) & 1r for b in range(9r)]
        M = matrix(F2, 3, 3, entries)
        print(f"  v{i+1r}: bits={v}, entries={entries}")
        print(M)

    # Polynomial verification
    R = PolynomialRing(GF(2), 'x', 9)
    xs = R.gens()
    X = matrix(R, 3, 3, list(xs))
    X3 = X * X * X
    Fpoly = sum(X3[ii,ii] for ii in range(3))
    d = len(best_basis)
    T = PolynomialRing(GF(2), 't', d)
    ts = T.gens()
    vals = [T(0)] * 9r
    for idx_i in range(d):
        v = Z[best_basis[idx_i]]
        entries = [(v >> b) & 1r for b in range(9r)]
        for k in range(9r):
            vals[k] += ts[idx_i] * T(entries[k])
    F_sub = Fpoly(*vals)
    print(f"\nF(sum ti*vi) = {F_sub}")
    if F_sub == 0:
        print("POLYNOMIAL VANISHING CONFIRMED")

print(f"\nTotal: {time.time()-start:.1f}s")
