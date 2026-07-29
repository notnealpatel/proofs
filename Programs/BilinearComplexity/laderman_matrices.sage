# Laderman (1976) 3x3 matrix multiplication algorithm using 23 multiplications.
# Extracted from: Courtois, Bard, Hulme (arXiv:1108.2830), Section 2.4.
#
# Convention:
#   U: 9 x 23 matrix. Row i = A entry i (row-major: a11,a12,a13,a21,...,a33).
#                      Column k = coefficients of A entries in product P_k.
#   V: 9 x 23 matrix. Row i = B entry i (row-major: b11,b12,b13,b21,...,b33).
#                      Column k = coefficients of B entries in product P_k.
#   W: 9 x 23 matrix. Row i = C entry i (row-major: c11,c12,c13,c21,...,c33).
#                      Column k = coefficient of product P_k in output c_i.
#
# The bilinear identity is: for C = A * B (3x3),
#   c_{ij} = sum_k W[i*3+j-1, k] * (sum_l U[l, k] * A_l) * (sum_m V[m, k] * B_m)
#
# Equivalently, the structure tensor T of 3x3 matrix multiplication satisfies:
#   T = sum_{k=1}^{23} U[:,k] (x) V[:,k] (x) W[:,k]

# U: each row below is the A-coefficient vector for one product P01..P23 (length 9).
# Transposed so columns = products.
U = Matrix(ZZ, [
    [ 1, -1, -1,  1, -1,  0,  0, -1, -1],  # P01
    [ 1,  0,  0,  1,  0,  0,  0,  0,  0],  # P02
    [ 0,  0,  0,  0,  1,  0,  0,  0,  0],  # P03
    [-1,  0,  0, -1,  1,  0,  0,  0,  0],  # P04
    [ 0,  0,  0, -1,  1,  0,  0,  0,  0],  # P05
    [ 1,  0,  0,  0,  0,  0,  0,  0,  0],  # P06
    [ 1,  0,  0,  0,  0,  0,  1,  1,  0],  # P07
    [ 1,  0,  0,  0,  0,  0,  1,  0,  0],  # P08
    [ 0,  0,  0,  0,  0,  0,  1,  1,  0],  # P09
    [ 1,  1, -1,  0, -1,  1,  1,  1,  0],  # P10
    [ 0,  0,  0,  0,  0,  0,  0,  1,  0],  # P11
    [ 0,  0,  1,  0,  0,  0,  0,  1,  1],  # P12
    [ 0,  0,  1,  0,  0,  0,  0,  0,  1],  # P13
    [ 0,  0,  1,  0,  0,  0,  0,  0,  0],  # P14
    [ 0,  0,  0,  0,  0,  0,  0, -1, -1],  # P15
    [ 0,  0,  1,  0,  1, -1,  0,  0,  0],  # P16
    [ 0,  0, -1,  0,  0,  1,  0,  0,  0],  # P17
    [ 0,  0,  0,  0,  1, -1,  0,  0,  0],  # P18
    [ 0,  1,  0,  0,  0,  0,  0,  0,  0],  # P19
    [ 0,  0,  0,  0,  0,  1,  0,  0,  0],  # P20
    [ 0,  0,  0,  1,  0,  0,  0,  0,  0],  # P21
    [ 0,  0,  0,  0,  0,  0,  1,  0,  0],  # P22
    [ 0,  0,  0,  0,  0,  0,  0,  0,  1],  # P23
]).transpose()

# V: each row below is the B-coefficient vector for one product P01..P23 (length 9).
V = Matrix(ZZ, [
    [ 0,  0,  0,  0, -1,  0,  0,  0,  0],  # P01
    [ 0,  1,  0,  0,  1,  0,  0,  0,  0],  # P02
    [ 1, -1,  0,  1, -1, -1,  1,  0, -1],  # P03
    [-1,  1,  0,  0,  1,  0,  0,  0,  0],  # P04
    [-1,  1,  0,  0,  0,  0,  0,  0,  0],  # P05
    [-1,  0,  0,  0,  0,  0,  0,  0,  0],  # P06
    [ 1,  0, -1,  0,  0,  1,  0,  0,  0],  # P07
    [ 0,  0, -1,  0,  0,  1,  0,  0,  0],  # P08
    [ 1,  0, -1,  0,  0,  0,  0,  0,  0],  # P09
    [ 0,  0,  0,  0,  0,  1,  0,  0,  0],  # P10
    [-1,  0,  1,  1, -1, -1, -1,  1,  0],  # P11
    [ 0,  0,  0,  0,  1,  0,  1, -1,  0],  # P12
    [ 0,  0,  0,  0, -1,  0,  0,  1,  0],  # P13
    [ 0,  0,  0,  0,  0,  0,  1,  0,  0],  # P14
    [ 0,  0,  0,  0,  0,  0, -1,  1,  0],  # P15
    [ 0,  0,  0,  0,  0,  1, -1,  0,  1],  # P16
    [ 0,  0,  0,  0,  0,  1,  0,  0,  1],  # P17
    [ 0,  0,  0,  0,  0,  0,  1,  0, -1],  # P18
    [ 0,  0,  0,  1,  0,  0,  0,  0,  0],  # P19
    [ 0,  0,  0,  0,  0,  0,  0,  1,  0],  # P20
    [ 0,  0,  1,  0,  0,  0,  0,  0,  0],  # P21
    [ 0,  1,  0,  0,  0,  0,  0,  0,  0],  # P22
    [ 0,  0,  0,  0,  0,  0,  0,  0,  1],  # P23
]).transpose()

# W: 9 x 23 matrix. Row i = C entry i. W[i, k] = coefficient of product P_{k+1} in c_i.
# Rows: c11, c12, c13, c21, c22, c23, c31, c32, c33.
# Already 9x23 (no transpose needed — contrast with U, V which are given product-first).
W = Matrix(ZZ, [
    # P01 P02 P03 P04 P05 P06 P07 P08 P09 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23
    [ 0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  1,  0,  0,  0,  0],  # c11
    [ 1,  0,  0, -1,  1, -1,  0,  0,  0,  0,  0, -1,  0,  1,  1,  0,  0,  0,  0,  0,  0,  0,  0],  # c12
    [ 0,  0,  0,  0,  0, -1, -1,  0,  1,  1,  0,  0,  0,  1,  0,  1,  0,  1,  0,  0,  0,  0,  0],  # c13
    [ 0,  1,  1,  1,  0,  1,  0,  0,  0,  0,  0,  0,  0,  1,  0,  1,  1,  0,  0,  0,  0,  0,  0],  # c21
    [ 0,  1,  0,  1, -1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0],  # c22
    [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  1,  1,  1,  0,  0,  1,  0,  0],  # c23
    [ 0,  0,  0,  0,  0,  1,  1, -1,  0,  0,  1,  1,  1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0],  # c31
    [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  1, -1, -1,  0,  0,  0,  0,  0,  0,  1,  0],  # c32
    [ 0,  0,  0,  0,  0,  1,  1, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1],  # c33
])

# =========================================================================
# Verification: check that sum_k U[:,k] (x) V[:,k] (x) W[:,k] equals the
# structure tensor of 3x3 matrix multiplication.
# The structure tensor T[a,b,c] = 1 iff (a = (i,j), b = (j,k), c = (i,k))
# in the standard basis, i.e., T[(i-1)*3+(j-1), (j-1)*3+(k-1), (i-1)*3+(k-1)] = 1.
# =========================================================================

def verify():
    """Verify that the factorization reproduces 3x3 matrix multiplication."""
    # Build the structure tensor from the factorization
    T_computed = {}
    for k in range(23):
        u = U.column(k)
        v = V.column(k)
        w = W.column(k)
        for a in range(9):
            for b in range(9):
                for c in range(9):
                    val = u[a] * v[b] * w[c]
                    if val != 0:
                        key = (a, b, c)
                        T_computed[key] = T_computed.get(key, 0) + val

    # Build the target structure tensor
    T_target = {}
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a_idx = i * 3 + j  # A_{i,j}
                b_idx = j * 3 + k  # B_{j,k}
                c_idx = i * 3 + k  # C_{i,k}
                T_target[(a_idx, b_idx, c_idx)] = 1

    # Compare
    errors = 0
    # Check all entries in target
    for key, val in T_target.items():
        if T_computed.get(key, 0) != val:
            print(f"MISMATCH at {key}: expected {val}, got {T_computed.get(key, 0)}")
            errors += 1

    # Check no spurious entries
    for key, val in T_computed.items():
        if val != 0 and key not in T_target:
            print(f"SPURIOUS at {key}: got {val}")
            errors += 1

    if errors == 0:
        print("VERIFIED: Laderman factorization is correct for 3x3 matrix multiplication.")
    else:
        print(f"FAILED: {errors} errors found.")

    return errors == 0

ok = verify()
if not ok:
    raise SystemExit(1)
