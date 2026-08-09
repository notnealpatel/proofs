#!/usr/bin/env sage
# Export three <3,3,3> matmul decompositions to JSON with integral scaling.
#
# Run from the Scratch directory so that load() resolves smirnov2018_matrices.sage:
#   cd ~/p/proofs/Scratch && sage export_decomp.sage [outdir]
#
# Arguments:
#   outdir   Directory for output JSON files (default: current directory).
#
# Outputs: laderman.json, smirnov-1.json, smirnov-2.json
#
# JSON schema (per file):
#   {
#     "name":  string,         // e.g. "Laderman"
#     "r":     int,            // tensor rank (number of terms)
#     "S":     int,            // integral scaling factor applied to T and all terms
#     "T":     [[a,b,c,val],...],        // scaled target tensor (sparse, 9x9x9)
#     "terms": [[[a,b,c,val],...],...]   // r term tensors, each sparse
#   }
#
# Invariant: sum(terms[k]) == T entry-wise for all (a,b,c).

import json, sys

# --- Laderman (rank 23) ---

U_lad = Matrix(ZZ, [
    [ 1, -1, -1,  1, -1,  0,  0, -1, -1],
    [ 1,  0,  0,  1,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  1,  0,  0,  0,  0],
    [-1,  0,  0, -1,  1,  0,  0,  0,  0],
    [ 0,  0,  0, -1,  1,  0,  0,  0,  0],
    [ 1,  0,  0,  0,  0,  0,  0,  0,  0],
    [ 1,  0,  0,  0,  0,  0,  1,  1,  0],
    [ 1,  0,  0,  0,  0,  0,  1,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  1,  1,  0],
    [ 1,  1, -1,  0, -1,  1,  1,  1,  0],
    [ 0,  0,  0,  0,  0,  0,  0,  1,  0],
    [ 0,  0,  1,  0,  0,  0,  0,  1,  1],
    [ 0,  0,  1,  0,  0,  0,  0,  0,  1],
    [ 0,  0,  1,  0,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  0, -1, -1],
    [ 0,  0,  1,  0,  1, -1,  0,  0,  0],
    [ 0,  0, -1,  0,  0,  1,  0,  0,  0],
    [ 0,  0,  0,  0,  1, -1,  0,  0,  0],
    [ 0,  1,  0,  0,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  1,  0,  0,  0],
    [ 0,  0,  0,  1,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  1,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  0,  0,  1],
]).transpose()

V_lad = Matrix(ZZ, [
    [ 0,  0,  0,  0, -1,  0,  0,  0,  0],
    [ 0,  1,  0,  0,  1,  0,  0,  0,  0],
    [ 1, -1,  0,  1, -1, -1,  1,  0, -1],
    [-1,  1,  0,  0,  1,  0,  0,  0,  0],
    [-1,  1,  0,  0,  0,  0,  0,  0,  0],
    [-1,  0,  0,  0,  0,  0,  0,  0,  0],
    [ 1,  0, -1,  0,  0,  1,  0,  0,  0],
    [ 0,  0, -1,  0,  0,  1,  0,  0,  0],
    [ 1,  0, -1,  0,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  1,  0,  0,  0],
    [-1,  0,  1,  1, -1, -1, -1,  1,  0],
    [ 0,  0,  0,  0,  1,  0,  1, -1,  0],
    [ 0,  0,  0,  0, -1,  0,  0,  1,  0],
    [ 0,  0,  0,  0,  0,  0,  1,  0,  0],
    [ 0,  0,  0,  0,  0,  0, -1,  1,  0],
    [ 0,  0,  0,  0,  0,  1, -1,  0,  1],
    [ 0,  0,  0,  0,  0,  1,  0,  0,  1],
    [ 0,  0,  0,  0,  0,  0,  1,  0, -1],
    [ 0,  0,  0,  1,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  0,  1,  0],
    [ 0,  0,  1,  0,  0,  0,  0,  0,  0],
    [ 0,  1,  0,  0,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  0,  0,  1],
]).transpose()

W_lad = Matrix(ZZ, [
    [ 0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  1,  0,  0,  0,  0],
    [ 1,  0,  0, -1,  1, -1,  0,  0,  0,  0,  0, -1,  0,  1,  1,  0,  0,  0,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0, -1, -1,  0,  1,  1,  0,  0,  0,  1,  0,  1,  0,  1,  0,  0,  0,  0,  0],
    [ 0,  1,  1,  1,  0,  1,  0,  0,  0,  0,  0,  0,  0,  1,  0,  1,  1,  0,  0,  0,  0,  0,  0],
    [ 0,  1,  0,  1, -1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  1,  1,  1,  0,  0,  1,  0,  0],
    [ 0,  0,  0,  0,  0,  1,  1, -1,  0,  0,  1,  1,  1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0],
    [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  1, -1, -1,  0,  0,  0,  0,  0,  0,  1,  0],
    [ 0,  0,  0,  0,  0,  1,  1, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1],
])


# --- Smirnov (load from file) ---

load("smirnov2018_matrices.sage")
_, U_s1, V_s1, W_s1_raw, _, _, _ = define_smirnov_alg1()
_, U_s2, V_s2, W_s2_raw, _, _, _ = define_smirnov_alg2()

def fix_w(W_raw):
    perm = [0]*9
    for i in range(3):
        for l in range(3):
            perm[i*3+l] = l*3+i
    W_out = Matrix(QQ, 9, W_raw.ncols())
    for j in range(9):
        W_out.set_row(j, W_raw.row(perm[j]))
    return W_out

W_s1 = fix_w(W_s1_raw)
W_s2 = fix_w(W_s2_raw)


# --- Tensor T: T[(i*3+j, j*3+k, i*3+k)] = 1 ---

T = {}
for i in range(3):
    for j in range(3):
        for k in range(3):
            T[(i*3+j, j*3+k, i*3+k)] = 1


def export_algorithm(name, U, V, W, T):
    """Compute term tensors, scale to integers, verify, write JSON."""
    r = U.ncols()

    # Collect all term entries to find global lcm of denominators.
    term_denoms = set()
    for k in range(r):
        for a in range(9):
            u_ak = QQ(U[a, k])
            if u_ak == 0:
                continue
            for b in range(9):
                v_bk = QQ(V[b, k])
                if v_bk == 0:
                    continue
                for c in range(9):
                    w_ck = QQ(W[c, k])
                    if w_ck == 0:
                        continue
                    val = u_ak * v_bk * w_ck
                    term_denoms.add(val.denominator())

    S = lcm(list(term_denoms))
    print(f"{name}: scaling factor S = {S}", file=sys.stderr)

    # Compute scaled terms.
    terms_json = []
    sum_check = {}
    for k in range(r):
        entries = []
        for a in range(9):
            u_ak = QQ(U[a, k])
            if u_ak == 0:
                continue
            for b in range(9):
                v_bk = QQ(V[b, k])
                if v_bk == 0:
                    continue
                for c in range(9):
                    w_ck = QQ(W[c, k])
                    if w_ck == 0:
                        continue
                    val = S * u_ak * v_bk * w_ck
                    assert val in ZZ, f"Not integral: {val} at term {k}, ({a},{b},{c})"
                    int_val = int(val)
                    if int_val != 0:
                        entries.append([int(a), int(b), int(c), int_val])
                        key = (a, b, c)
                        sum_check[key] = sum_check.get(key, 0) + int_val
        terms_json.append(entries)

    # Scaled T.
    T_scaled = []
    for (a, b, c), val in sorted(T.items()):
        sv = int(S * val)
        T_scaled.append([int(a), int(b), int(c), sv])

    # Verify: sum of scaled terms == scaled T.
    T_dict = {}
    for (a, b, c), val in T.items():
        T_dict[(a, b, c)] = int(S * val)

    errors = 0
    for key, val in T_dict.items():
        if sum_check.get(key, 0) != val:
            print(f"  MISMATCH at {key}: T={val}, sum={sum_check.get(key, 0)}", file=sys.stderr)
            errors += 1
    for key, val in sum_check.items():
        if val != 0 and key not in T_dict:
            print(f"  SPURIOUS at {key}: sum={val}", file=sys.stderr)
            errors += 1
    if errors > 0:
        raise ValueError(f"{name}: verification failed with {errors} errors")
    print(f"{name}: VERIFIED (r={r}, S={S})", file=sys.stderr)

    return {"name": name, "r": int(r), "S": int(S), "T": T_scaled, "terms": terms_json}


outdir = sys.argv[1] if len(sys.argv) > 1 else "."

algos = [
    ("Laderman", U_lad, V_lad, W_lad),
    ("Smirnov-1", U_s1, V_s1, W_s1),
    ("Smirnov-2", U_s2, V_s2, W_s2),
]

for name, U, V, W in algos:
    data = export_algorithm(name, U, V, W, T)
    fname = outdir + "/" + name.lower().replace(" ", "") + ".json"
    with open(fname, "w") as f:
        json.dump(data, f, separators=(",", ":"))
    print(f"Wrote {fname}", file=sys.stderr)

print("Export complete.", file=sys.stderr)
