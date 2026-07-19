#!/usr/bin/env sage
"""
Q2: Strassen^2 on <4,4,4> (rank 49). Which of the 16 outputs finish with
singleton products, which via shared products, and does the split follow a
(2,2) block boundary?

Construction: U2 = U (x) U etc. (Kronecker), with the index identification
(block position, inner position). Rows are then permuted to global row-major
4x4 indexing so outputs read as C[r][c], r,c in 1..4.
"""

# Strassen factors for <2,2,2>: rows = flattened 2x2 (row-major), cols = products
# m1=(a11+a22)(b11+b22); m2=(a21+a22)b11; m3=a11(b12-b22); m4=a22(b21-b11)
# m5=(a11+a12)b22; m6=(a21-a11)(b11+b12); m7=(a12-a22)(b21+b22)
U1 = Matrix(ZZ, [
    [1, 0, 1, 0, 1, -1, 0],   # a11
    [0, 0, 0, 0, 1, 0, 1],    # a12
    [0, 1, 0, 0, 0, 1, 0],    # a21
    [1, 1, 0, 1, 0, 0, -1],   # a22
])
V1 = Matrix(ZZ, [
    [1, 1, 0, -1, 0, 1, 0],   # b11
    [0, 0, 1, 0, 0, 1, 0],    # b12
    [0, 0, 0, 1, 0, 0, 1],    # b21
    [1, 0, -1, 0, 1, 0, 1],   # b22
])
W1 = Matrix(ZZ, [
    [1, 0, 0, 1, -1, 0, 1],   # c11
    [0, 0, 1, 0, 1, 0, 0],    # c12
    [0, 1, 0, 1, 0, 0, 0],    # c21
    [1, -1, 1, 0, 0, 1, 0],   # c22
])

def matmul_tensor(n, m, p):
    T = {}
    for i in range(n):
        for j in range(m):
            for k in range(p):
                T[(i * m + j, j * p + k, i * p + k)] = 1
    return T

def verify(U, V, W, n, m, p, label):
    T_exp = matmul_tensor(n, m, p)
    T_got = {}
    r = U.ncols()
    for k in range(r):
        for a in U.nonzero_positions_in_column(k):
            for b in V.nonzero_positions_in_column(k):
                for c in W.nonzero_positions_in_column(k):
                    key = (a, b, c)
                    T_got[key] = T_got.get(key, 0) + U[a, k] * V[b, k] * W[c, k]
    T_got = {k: v for k, v in T_got.items() if v != 0}
    ok = T_got == T_exp
    print(f"{label}: {'VERIFIED' if ok else 'FAILED'}")
    return ok

assert verify(U1, V1, W1, 2, 2, 2, "Strassen <2,2,2>")

# --- Kronecker square with (block, inner) -> global row-major permutation ---
def perm_rows(M):
    """kron row 4*(2*ib+jb)+(2*ii+ji) -> global row 4*(2*ib+ii)+(2*jb+ji)."""
    P = Matrix(ZZ, 16, 16)
    for ib in range(2):
        for jb in range(2):
            for ii in range(2):
                for ji in range(2):
                    kron = 4 * (2 * ib + jb) + (2 * ii + ji)
                    glob = 4 * (2 * ib + ii) + (2 * jb + ji)
                    P[glob, kron] = 1
    return P * M

U2 = perm_rows(U1.tensor_product(U1))
V2 = perm_rows(V1.tensor_product(V1))
W2 = perm_rows(W1.tensor_product(W1))
assert verify(U2, V2, W2, 4, 4, 4, "Strassen^2 <4,4,4> rank 49")

# hits per output, in kron (block,inner) order for comparison with the
# supplied vector, and in global order for geometry
Wk = W1.tensor_product(W1)
hits_kron = [len(Wk.nonzero_positions_in_row(r)) for r in range(16)]
hits_glob = [len(W2.nonzero_positions_in_row(r)) for r in range(16)]
print(f"hits (block,inner) order: {hits_kron}")
print(f"hits global order:        {hits_glob}")

# column classification
col_hits = [len(W2.nonzero_positions_in_column(k)) for k in range(49)]
singles = [k for k in range(49) if col_hits[k] == 1]
print(f"singleton columns (1-based): {[k+1 for k in singles]}  "
      f"count={len(singles)}")
from collections import Counter
print(f"column-hit histogram: {sorted(Counter(col_hits).items())}")

def outname(r):
    return f"C{r // 4 + 1}{r % 4 + 1}"

# --- residual trajectory in product order m1..m49 ---
T = matmul_tensor(4, 4, 4)
res = dict(T)
finish = {}
nnz_curve = []
for k in range(49):
    for a in U2.nonzero_positions_in_column(k):
        for b in V2.nonzero_positions_in_column(k):
            for c in W2.nonzero_positions_in_column(k):
                key = (a, b, c)
                v = res.get(key, 0) - U2[a, k] * V2[b, k] * W2[c, k]
                if v == 0:
                    res.pop(key, None)
                else:
                    res[key] = v
    per_out = [0] * 16
    for (a, b, c) in res:
        per_out[c] += 1
    nnz_curve.append(sum(per_out))
    for o in range(16):
        if per_out[o] == 0 and o not in finish:
            finish[o] = k + 1          # tentative
        if per_out[o] != 0 and o in finish:
            del finish[o]              # went nonzero again; not finished
assert len(res) == 0
print(f"nnz curve: start 64, peak {max(nnz_curve)}, "
      f"back-to-64-or-less first at step {next(i+1 for i,v in enumerate(nnz_curve) if v <= 64)}, "
      f"end 0 at step 49")

print("\noutput  finish_step  finishing_column_hits  finisher_type")
sing_finished, shared_finished = [], []
for o in range(16):
    f = finish[o]
    ch = col_hits[f - 1]
    typ = "SINGLETON" if ch == 1 else "shared"
    (sing_finished if ch == 1 else shared_finished).append(outname(o))
    print(f"  {outname(o)}    {f:3d}          {ch}                  {typ}")
print(f"\nsingleton-finished outputs: {sing_finished}")
print(f"shared-finished outputs:    {shared_finished}")
