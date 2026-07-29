#!/usr/bin/env sage
# Residual trajectory comparison: Smirnov-1, Smirnov-2, Laderman side-by-side

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

# --- Tensor and support ---

T = {}
for i in range(3):
    for j in range(3):
        for k in range(3):
            T[(i*3+j, j*3+k, i*3+k)] = 1

T_support = [set() for _ in range(9)]
for (a, b, c) in T:
    T_support[c].add((a, b))

# --- Core functions ---

def sign_char(x):
    if x > 0: return '+'
    elif x < 0: return '-'
    return '.'

def w_pattern(U, V, W, k):
    supp_u = set(a for a in range(9) if U[a, k] != 0)
    supp_v = set(b for b in range(9) if V[b, k] != 0)
    footprint = set((a, b) for a in supp_u for b in supp_v)
    pat = ''
    for c in range(9):
        s = sign_char(W[c, k])
        if s == '.':
            pat += '.'
        elif footprint & T_support[c]:
            pat += s
        else:
            pat += 'S'
    return pat

def remaining_per_output(R):
    counts = [0] * 9
    for (a, b, c), val in R.items():
        if val != 0:
            counts[c] += 1
    return counts


def compute_and_print(label, U, V, W):
    r = U.ncols()
    R = dict(T)

    print("")
    print("  " + label)
    print("  " + "=" * len(label))
    print("  step  pattern    remaining_per_output     nnz")
    print("  ----  ---------  -----------------------  ---")

    rpo = remaining_per_output(R)
    rpo_s = "[" + ",".join(str(x) for x in rpo) + "]"
    print("     0  (initl)    " + rpo_s.ljust(23) + "   27")

    for k in range(r):
        for a in range(9):
            u_ak = U[a, k]
            if u_ak == 0: continue
            for b in range(9):
                v_bk = V[b, k]
                if v_bk == 0: continue
                for c in range(9):
                    w_ck = W[c, k]
                    if w_ck == 0: continue
                    key = (a, b, c)
                    R[key] = R.get(key, 0) - u_ak * v_bk * w_ck
        nz = sum(1 for v in R.values() if v != 0)
        wp = w_pattern(U, V, W, k)
        rpo = remaining_per_output(R)
        rpo_s = "[" + ",".join(str(x) for x in rpo) + "]"
        print("  " + str(k+1).rjust(4) + "  " + wp + "  " + rpo_s.ljust(23) + "  " + str(nz).rjust(3))

    final_nz = sum(1 for v in R.values() if v != 0)
    assert final_nz == 0, label + " did not reach zero residual"


# --- Run all three ---

compute_and_print("Smirnov-1 (rank 25)", U_s1, V_s1, W_s1)
compute_and_print("Smirnov-2 (rank 25)", U_s2, V_s2, W_s2)
compute_and_print("Laderman (rank 23)", U_lad, V_lad, W_lad)
