#!/usr/bin/env sage
"""
Interference pattern visualization for bilinear algorithms.

Computes coverage tables from actual (U, V, W) factor matrices,
verifies each decomposition against the matrix multiplication tensor,
and displays sign-pattern interference.
"""

# === Tensor construction ===

def matmul_tensor(n, m, p):
    """
    Build the <n,m,p> matrix multiplication tensor T as an (nm x mp x np) array.
    T[(i*m+j), (j'*p+k), (i'*p+k')] = delta_{i,i'} * delta_{j,j'} * delta_{k,k'}

    Indices: A is n x m (flattened row-major nm), B is m x p (flattened mp),
             C is n x p (flattened np).
    """
    T = {}
    for i in range(n):
        for j in range(m):
            for k in range(p):
                a_idx = i * m + j
                b_idx = j * p + k
                c_idx = i * p + k
                T[(a_idx, b_idx, c_idx)] = 1
    return T


def verify_decomposition(U, V, W, n, m, p, label):
    """
    Verify sum_k U[:,k] otimes V[:,k] otimes W[:,k] equals the <n,m,p> tensor.
    Returns True if correct, prints error and returns False otherwise.
    """
    r = U.ncols()
    T_expected = matmul_tensor(n, m, p)

    # Reconstruct tensor from factors
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

    # Compare
    all_keys = set(T_expected.keys()) | set(T_got.keys())
    for key in all_keys:
        expected = T_expected.get(key, 0)
        got = T_got.get(key, 0)
        if expected != got:
            print(f"ERROR: {label} verification failed at {key}: expected {expected}, got {got}")
            return False
    return True


# === Display ===

def sign_char(v):
    if v > 0: return "+"
    if v < 0: return "-"
    return "."


def print_coverage_matrix(title, W, inner_dim, W_ref=None, num_cols_display=None):
    """
    Display coverage table from W matrix.
    W has shape (n*p) x r: rows = output entries, columns = products.
    inner_dim: the m in <n,m,p> — schoolbook baseline hits per output.
    W_ref: reference (schoolbook) W matrix for coloring comparisons.
    num_cols_display: pad to this many columns (for alignment across algorithms).
    """
    n_outputs = W.nrows()
    r = W.ncols()
    num_cols = num_cols_display if num_cols_display else r

    GREEN = "\033[30;102m"
    RED = "\033[30;101m"
    RESET = "\033[0m"

    products = [f"m{k+1}" for k in range(r)]
    while len(products) < num_cols:
        products.append("  ")

    print(f"\n  {title}")
    print(f"  {'=' * len(title)}\n")

    prod_w = max(len(p) for p in products) + 1
    out_w = 4

    hdr = f"  {'':>{out_w}}"
    for p in products:
        hdr += f" {p:^{prod_w}}"
    hdr += "  hits"
    print(hdr)
    print(f"  {'-'*out_w}" + f" {'-'*prod_w}" * num_cols + "  ----")

    for j in range(n_outputs):
        hits = sum(1 for k in range(r) if W[j, k] != 0)
        line = f"  {j+1:<{out_w}}"
        for k in range(num_cols):
            if k < r:
                v = W[j, k]
                c = sign_char(v)
            else:
                c = "."
            if c == ".":
                cell = f"{'.':^{prod_w}}"
            else:
                cell = f" {c} "
                cell = f"{cell:^{prod_w}}"
                if W_ref is not None and k < W_ref.ncols() and W_ref[j, k] != 0:
                    ref_c = sign_char(W_ref[j, k])
                    if ref_c == c:
                        cell = f"{GREEN}{cell}{RESET}"
                    else:
                        cell = f"{RED}{cell}{RESET}"
            line += f" {cell}"
        line += f"  {hits}"
        print(line)
    print()


def _nnz(M):
    return sum(1 for v in M.list() if v != 0)


def _nns(M):
    """Nonzero entries that are not +-1 (each costs a scalar multiplication)."""
    return sum(1 for v in M.list() if v != 0 and v != 1 and v != -1)


def print_summary(decompositions):
    """Print nnz, density, and multi-hit summary for each decomposition.

    Density is normalized to the decomposition's own footprint (nnz / (rows * r)),
    so figures are comparable across decompositions of different rank.
    """
    for label, _, _, W_mat, _, _, _ in decompositions:
        n_outputs = W_mat.nrows()
        r = W_mat.ncols()
        total_nz = _nnz(W_mat)
        density = float(total_nz) / float(r * n_outputs)
        multi = sum(1 for k in range(r) if sum(1 for j in range(n_outputs) if W_mat[j, k] != 0) > 1)
        print(f"  {label:>10}: nnz={total_nz}  density={density:.4%}  multi-hit={multi}/{r}")
    print()


def print_addition_counts(decompositions):
    """Beniamini-Schwartz style linear-operation counts (arXiv:2008.03759, Remark 2).

    Our matrices are transposed relative to theirs: U, V are (n*m x r) / (m*p x r)
    with columns = products, W is (n*p x r) with rows = outputs. Per side:
      additions = nnz - (number of linear combinations formed)
      scalar multiplications = nns (nonzero entries that are not +-1)
    q = total linear operations = additions + scalar mults, summed over U, V, W.
    """
    print("  Linear operations (Beniamini-Schwartz accounting):")
    for label, U_mat, V_mat, W_mat, _, _, _ in decompositions:
        r = W_mat.ncols()
        adds_U = _nnz(U_mat) - r
        adds_V = _nnz(V_mat) - r
        adds_W = _nnz(W_mat) - W_mat.nrows()
        adds = adds_U + adds_V + adds_W
        smuls = _nns(U_mat) + _nns(V_mat) + _nns(W_mat)
        print(f"  {label:>10}: adds={adds} (U:{adds_U} V:{adds_V} W:{adds_W})"
              f"  scalar-mults={smuls}  q={adds + smuls}")
    print()


# === Decomposition definitions ===

def define_strassen():
    """Strassen's algorithm for <2,2,2>, rank 7."""
    # Index order: a11, a12, a21, a22 (row-major)
    U = Matrix(ZZ, [
        [1, 0, 0, 1],   # M1: a11 + a22
        [0, 0, 1, 1],   # M2: a21 + a22
        [1, 0, 0, 0],   # M3: a11
        [0, 0, 0, 1],   # M4: a22
        [1, 1, 0, 0],   # M5: a11 + a12
        [-1, 0, 1, 0],  # M6: a21 - a11
        [0, 1, 0, -1],  # M7: a12 - a22
    ]).transpose()

    V = Matrix(ZZ, [
        [1, 0, 0, 1],   # M1: b11 + b22
        [1, 0, 0, 0],   # M2: b11
        [0, 1, 0, -1],  # M3: b12 - b22
        [-1, 0, 1, 0],  # M4: b21 - b11
        [0, 0, 0, 1],   # M5: b22
        [1, 1, 0, 0],   # M6: b11 + b12
        [0, 0, 1, 1],   # M7: b21 + b22
    ]).transpose()

    W = Matrix(ZZ, [
        [1, 0, 0, 1],   # M1: +C11, +C22
        [0, 0, 1, -1],  # M2: +C21, -C22
        [0, 1, 0, 1],   # M3: +C12, +C22
        [1, 0, 1, 0],   # M4: +C11, +C21
        [-1, 1, 0, 0],  # M5: -C11, +C12
        [0, 0, 0, 1],   # M6: +C22
        [1, 0, 0, 0],   # M7: +C11
    ]).transpose()

    return ("Strassen", U, V, W, 2, 2, 2)


def define_schoolbook():
    """Schoolbook algorithm for <2,2,2>, rank 8."""
    # Products: a11*b11->c11, a12*b21->c11, a11*b12->c12, a12*b22->c12,
    #           a21*b11->c21, a22*b21->c21, a21*b12->c22, a22*b22->c22
    n, m, p = 2, 2, 2

    # (A index, B index, C index) for each product
    products = [
        (0, 0, 0),  # a11*b11 -> c11
        (1, 2, 0),  # a12*b21 -> c11
        (0, 1, 1),  # a11*b12 -> c12
        (1, 3, 1),  # a12*b22 -> c12
        (2, 0, 2),  # a21*b11 -> c21
        (3, 2, 2),  # a22*b21 -> c21
        (2, 1, 3),  # a21*b12 -> c22
        (3, 3, 3),  # a22*b22 -> c22
    ]

    r = len(products)
    U = Matrix(ZZ, n*m, r)
    V = Matrix(ZZ, m*p, r)
    W = Matrix(ZZ, n*p, r)

    for k, (ai, bi, ci) in enumerate(products):
        U[ai, k] = 1
        V[bi, k] = 1
        W[ci, k] = 1

    return ("Schoolbook", U, V, W, n, m, p)


def define_laderman():
    """Laderman's algorithm for <3,3,3>, rank 23. From arXiv:1108.2830."""
    load("laderman_matrices.sage")
    return ("Laderman", U, V, W, 3, 3, 3)


def _fix_w_convention(W_raw):
    """Permute W rows from C_{l,i} flattening to C_{i,k} flattening."""
    n = 3
    perm = [0]*9
    for i in range(n):
        for l in range(n):
            perm[i*n + l] = l*n + i
    W = Matrix(QQ, 9, W_raw.ncols())
    for j in range(9):
        W.set_row(j, W_raw.row(perm[j]))
    return W


def define_smirnov1():
    """Smirnov (Chokaev-Shumkin) Algorithm 1 for <3,3,3>, rank 25."""
    load("smirnov2018_matrices.sage")
    _, U, V, W_raw, _, _, _ = define_smirnov_alg1()
    return ("Smirnov-1", U, V, _fix_w_convention(W_raw), 3, 3, 3)


def define_smirnov2():
    """Smirnov (Chokaev-Shumkin) Algorithm 2 for <3,3,3>, rank 25."""
    load("smirnov2018_matrices.sage")
    _, U, V, W_raw, _, _, _ = define_smirnov_alg2()
    return ("Smirnov-2", U, V, _fix_w_convention(W_raw), 3, 3, 3)


def define_schoolbook_333():
    """Schoolbook algorithm for <3,3,3>, rank 27."""
    n, m, p = 3, 3, 3
    r = n * m * p
    U_mat = Matrix(ZZ, n*m, r)
    V_mat = Matrix(ZZ, m*p, r)
    W_mat = Matrix(ZZ, n*p, r)
    k = 0
    for i in range(n):
        for j in range(m):
            for l in range(p):
                U_mat[i*m + j, k] = 1
                V_mat[j*p + l, k] = 1
                W_mat[i*p + l, k] = 1
                k += 1
    return ("Schoolbook", U_mat, V_mat, W_mat, n, m, p)


# === Main ===

import sys
if "--333" in sys.argv:
    decompositions_raw = [define_schoolbook_333(), define_smirnov1(), define_smirnov2(), define_laderman()]
else:
    decompositions_raw = [define_schoolbook(), define_strassen()]

# Verify and collect
decompositions = []
for label, U, V, W, n, m, p in decompositions_raw:
    if not verify_decomposition(U, V, W, n, m, p, label):
        import sys
        sys.exit(1)
    decompositions.append((label, U, V, W, n, m, p))

# Determine max rank for column alignment
max_rank = max(W.ncols() for _, _, _, W, _, _, _ in decompositions)

# Display — first decomposition is reference (no coloring), rest get colored against it
W_ref = decompositions[0][3]  # schoolbook W
for idx, (label, U, V, W, n, m, p) in enumerate(decompositions):
    r = W.ncols()
    title = f"{label.upper()} (rank {r})"
    ref = W_ref if idx > 0 else None
    print_coverage_matrix(title, W, m, W_ref=ref, num_cols_display=max_rank)

print_summary(decompositions)
print_addition_counts(decompositions)
