#!/usr/bin/env sage
"""
compute_stabilizers.sage — Pre-compute stabilizer data for matmul decompositions.

Writes results incrementally to stabilizer_cache.json so partial runs are usable.
Usage:
    sage compute_stabilizers.sage            # all decompositions
    sage compute_stabilizers.sage --222      # Strassen only
    sage compute_stabilizers.sage --333      # Laderman, Smirnov-1, Smirnov-2
"""

import sys
import os
import json
import time

# Load library and decomposition definitions from interference_viz.sage helpers
load("decomp_stabilizer.sage")
load("laderman_matrices.sage")

# We need the decomposition constructors from interference_viz.sage.
# Rather than loading that file (which runs main), replicate the minimal
# definitions we need.

def matmul_tensor(n, m, p):
    T = {}
    for i in range(n):
        for j in range(m):
            for k in range(p):
                T[(i*m+j, j*p+k, i*p+k)] = 1
    return T


def verify_decomposition(U, V, W, n, m, p, label):
    r = U.ncols()
    T_expected = matmul_tensor(n, m, p)
    T_got = {}
    for k in range(r):
        for a in range(n * m):
            if U[a, k] == 0:
                continue
            for b in range(m * p):
                if V[b, k] == 0:
                    continue
                for c in range(n * p):
                    if W[c, k] == 0:
                        continue
                    key = (a, b, c)
                    T_got[key] = T_got.get(key, 0) + U[a, k] * V[b, k] * W[c, k]
    all_keys = set(T_expected.keys()) | set(T_got.keys())
    for key in all_keys:
        if T_expected.get(key, 0) != T_got.get(key, 0):
            return False
    return True


def _fix_w_convention(W_raw):
    n = 3
    perm = [0]*9
    for i in range(n):
        for l in range(n):
            perm[i*n + l] = l*n + i
    W = Matrix(QQ, 9, W_raw.ncols())
    for j in range(9):
        W.set_row(j, W_raw.row(perm[j]))
    return W


def define_strassen():
    U = Matrix(ZZ, [
        [1, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 0], [0, 0, 0, 1],
        [1, 1, 0, 0], [-1, 0, 1, 0], [0, 1, 0, -1],
    ]).transpose()
    V = Matrix(ZZ, [
        [1, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, -1], [-1, 0, 1, 0],
        [0, 0, 0, 1], [1, 1, 0, 0], [0, 0, 1, 1],
    ]).transpose()
    W = Matrix(ZZ, [
        [1, 0, 0, 1], [0, 0, 1, -1], [0, 1, 0, 1], [1, 0, 1, 0],
        [-1, 1, 0, 0], [0, 0, 0, 1], [1, 0, 0, 0],
    ]).transpose()
    return ("Strassen", U, V, W, 2, 2, 2)


def define_laderman():
    # U, V, W already loaded from laderman_matrices.sage
    return ("Laderman", U, V, W, 3, 3, 3)


def define_smirnov1():
    load("smirnov2018_matrices.sage")
    _, U_s, V_s, W_raw, _, _, _ = define_smirnov_alg1()
    return ("Smirnov-1", U_s, V_s, _fix_w_convention(W_raw), 3, 3, 3)


def define_smirnov2():
    load("smirnov2018_matrices.sage")
    _, U_s, V_s, W_raw, _, _, _ = define_smirnov_alg2()
    return ("Smirnov-2", U_s, V_s, _fix_w_convention(W_raw), 3, 3, 3)


# Use cwd (Scratch/), not __file__ which Sage remaps to a temp copy.
CACHE_FILE = os.path.join(os.getcwd(), "stabilizer_cache.json")


def load_cache():
    if os.path.exists(CACHE_FILE):
        with open(CACHE_FILE, "r") as f:
            return json.load(f)
    return {}


def save_cache(cache):
    with open(CACHE_FILE, "w") as f:
        json.dump(cache, f, indent=2)


def cache_entry(info):
    """Convert compute_stabilizer result to JSON-serializable dict."""
    return {
        "label": str(info["label"]),
        "order": int(info["order"]),
        "lower_bound": bool(info["lower_bound"]),
        "structure_desc": str(info["structure_desc"]),
        "orbits": [[int(x) for x in o] for o in info["orbits"]],
        "orbit_sizes": [int(s) for s in info["orbit_sizes"]],
        "col_order": [int(c) for c in info["col_order"]],
    }


def run_one(label, U, V, W, n, m, p, cache):
    """Compute stabilizer for one decomposition, update cache, save."""
    print(f"\n>>> Computing stabilizer for {label}...")
    if not verify_decomposition(U, V, W, n, m, p, label):
        print(f"ERROR: {label} verification failed, skipping")
        return
    t0 = time.time()
    info = compute_stabilizer(U, V, W, n, label=label, verbose=True)
    elapsed = time.time() - t0
    entry = cache_entry(info)
    entry["elapsed_s"] = float(round(elapsed, 2))
    cache[label] = entry
    save_cache(cache)
    print(f">>> {label} cached ({elapsed:.2f}s)")


# === Main ===

if __name__ == "__main__" or True:
    # Determine which decompositions to compute
    do_222 = "--222" in sys.argv or ("--333" not in sys.argv)
    do_333 = "--333" in sys.argv or ("--222" not in sys.argv)

    decomps = []
    if do_222:
        decomps.append(define_strassen())
    if do_333:
        decomps.append(define_smirnov1())
        decomps.append(define_smirnov2())
        decomps.append(define_laderman())

    cache = load_cache()
    print(f"Cache file: {CACHE_FILE}")
    if cache:
        print(f"Existing entries: {', '.join(cache.keys())}")
    else:
        print("No existing cache.")

    for label, U_d, V_d, W_d, n, m, p in decomps:
        run_one(label, U_d, V_d, W_d, n, m, p, cache)

    print(f"\nDone. Cache has {len(cache)} entries: {', '.join(cache.keys())}")
