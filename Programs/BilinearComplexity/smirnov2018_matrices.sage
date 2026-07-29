# Chokaev & Shumkin 2018 - Two rank-25 decompositions of <3,3,3>.
# Each algorithm uses 25 products with cyclic structure:
#   Product 1: identity (fixed point)
#   Products 2-25: eight base triples, each generating 3 products by cyclic permutation.
#
# Convention (same as laderman_matrices.sage):
#   U: 9 x 25 matrix (A-coefficients), V: 9 x 25 (B-coefficients), W: 9 x 25 (C-coefficients).
#   vec() flattens row-major: M -> [M[0,0], M[0,1], ..., M[2,2]].

def _vec(M):
    """Flatten 3x3 matrix row-major to length-9 vector over QQ."""
    return vector(QQ, [M[i][j] for i in range(3) for j in range(3)])

def _vec_T(M):
    """Flatten 3x3 matrix column-major (i.e., row-major of transpose) to length-9 vector over QQ."""
    return vector(QQ, [M[j][i] for i in range(3) for j in range(3)])

def _build_decomposition(base_triples):
    """Build U, V, W (9x25 over QQ) from identity + 8 cyclic base triples."""
    n = 9
    R = 25
    U = Matrix(QQ, n, R)
    V = Matrix(QQ, n, R)
    W = Matrix(QQ, n, R)

    # Product 1: identity
    id_vec = _vec([[1,0,0],[0,1,0],[0,0,1]])
    for i in range(n):
        U[i, 0] = id_vec[i]
        V[i, 0] = id_vec[i]
        W[i, 0] = id_vec[i]

    # Products 2-25: eight base triples at columns 1..24 (0-indexed)
    for idx, (A, B, C) in enumerate(base_triples):
        a = _vec(A)
        b = _vec(B)
        c = _vec(C)
        col_base = 1 + idx * 3  # 0-indexed columns: 1,4,7,10,13,16,19,22
        # col_base:   U=a, V=b, W=c
        # col_base+1: U=b, V=c, W=a
        # col_base+2: U=c, V=a, W=b
        for i in range(n):
            U[i, col_base]     = a[i]
            V[i, col_base]     = b[i]
            W[i, col_base]     = c[i]

            U[i, col_base + 1] = b[i]
            V[i, col_base + 1] = c[i]
            W[i, col_base + 1] = a[i]

            U[i, col_base + 2] = c[i]
            V[i, col_base + 2] = a[i]
            W[i, col_base + 2] = b[i]

    return U, V, W


# =========================================================================
# Algorithm 1
# =========================================================================

def define_smirnov_alg1():
    base_triples = [
        # rho=2
        ([[1, QQ(1)/2, 0], [1, QQ(1)/2, 0], [0, 0, QQ(1)/2]],
         [[QQ(-2)/3, QQ(2)/3, 0], [0, 0, 0], [0, 0, 0]],
         [[0, QQ(-1)/2, 0], [0, 1, 0], [0, 0, 1]]),
        # rho=5
        ([[QQ(-1)/2, QQ(1)/2, 0], [1, -1, 0], [0, 0, -1]],
         [[1, QQ(1)/2, 0], [0, 0, 0], [0, 0, 0]],
         [[0, QQ(2)/3, 0], [0, QQ(2)/3, 0], [0, 0, QQ(2)/3]]),
        # rho=8
        ([[0, 1, 1], [0, -1, -1], [0, 0, 0]],
         [[0, 0, 0], [0, 0, 0], [0, 0, QQ(1)/2]],
         [[0, 0, 0], [-1, 1, 0], [1, -1, 0]]),
        # rho=11
        ([[0, 1, 1], [0, 1, 1], [0, 0, 0]],
         [[0, 0, 0], [0, 0, 0], [0, 0, QQ(1)/2]],
         [[0, 0, 0], [-1, -1, 0], [1, 1, 0]]),
        # rho=14
        ([[0, 1, 0], [1, 1, 0], [0, 0, 0]],
         [[0, 0, 1], [0, 0, 1], [0, 0, -1]],
         [[0, 0, 0], [0, 0, 0], [0, QQ(1)/2, QQ(1)/2]]),
        # rho=17
        ([[0, 1, 0], [-1, 1, 0], [0, 0, 0]],
         [[0, 0, -1], [0, 0, 1], [0, 0, -1]],
         [[0, 0, 0], [0, 0, 0], [0, QQ(1)/2, QQ(1)/2]]),
        # rho=20
        ([[0, 0, 0], [0, 0, -1], [0, 0, 1]],
         [[0, 0, 0], [0, 0, 0], [-1, 1, 1]],
         [[0, 1, 0], [0, 0, 0], [0, 0, 0]]),
        # rho=23
        ([[1, 0, 0], [0, 0, 0], [0, 0, 0]],
         [[0, 0, 1], [0, 0, 0], [0, 0, 0]],
         [[0, 0, 0], [0, 0, 0], [1, 0, 0]]),
    ]
    U, V, W = _build_decomposition(base_triples)
    return ("Smirnov-1", U, V, W, 3, 3, 3)


# =========================================================================
# Algorithm 2
# =========================================================================

def define_smirnov_alg2():
    base_triples = [
        # rho=2
        ([[QQ(-1)/2, QQ(1)/2, 0], [1, -1, 0], [0, 0, QQ(-1)/2]],
         [[1, QQ(1)/2, 0], [0, 0, 0], [0, 0, 1]],
         [[0, QQ(2)/3, 0], [0, QQ(2)/3, 0], [0, 0, 0]]),
        # rho=5
        ([[1, QQ(1)/2, 0], [1, QQ(1)/2, 0], [0, 0, 1]],
         [[QQ(2)/3, QQ(-2)/3, 0], [0, 0, 0], [0, 0, QQ(2)/3]],
         [[0, QQ(1)/2, 0], [0, -1, 0], [0, 0, 0]]),
        # rho=8
        ([[1, 0, 1], [0, 0, 0], [1, 0, 1]],
         [[0, 0, 0], [0, 0, 0], [-1, 0, 1]],
         [[QQ(-1)/2, 0, 0], [0, 0, 0], [QQ(1)/2, 0, 0]]),
        # rho=11
        ([[-1, 0, 1], [0, 0, 0], [1, 0, -1]],
         [[0, 0, 0], [0, 0, 0], [1, 0, 1]],
         [[QQ(1)/2, 0, 0], [0, 0, 0], [QQ(1)/2, 0, 0]]),
        # rho=14
        ([[0, 0, QQ(1)/2], [0, 0, 0], [0, 0, -1]],
         [[0, QQ(1)/2, 0], [0, 0, 0], [0, 1, 0]],
         [[0, 0, 0], [1, 0, QQ(-1)/2], [0, 0, 0]]),
        # rho=17
        ([[0, 0, QQ(1)/2], [0, 0, 0], [0, 0, 1]],
         [[0, QQ(-1)/2, 0], [0, 0, 0], [0, 1, 0]],
         [[0, 0, 0], [1, 0, QQ(1)/2], [0, 0, 0]]),
        # rho=20
        ([[0, -1, 0], [0, 0, 0], [0, 0, 0]],
         [[0, 0, 0], [0, 0, 1], [0, 0, 0]],
         [[0, 0, QQ(-1)/4], [0, 0, 0], [-1, 0, 0]]),
        # rho=23
        ([[0, 0, 0], [0, 1, 0], [0, 0, 0]],
         [[0, 0, 0], [0, 0, 1], [0, 0, 0]],
         [[0, 0, 0], [0, 0, 0], [0, 1, 0]]),
    ]
    U, V, W = _build_decomposition(base_triples)
    return ("Smirnov-2", U, V, W, 3, 3, 3)


# =========================================================================
# Verification
# =========================================================================

def verify(name, U, V, W, m, n, p):
    """Verify that sum_k U[:,k] (x) V[:,k] (x) W[:,k] equals the <m,n,p> matmul tensor."""
    R = U.ncols()
    dim = m * n  # = n * p = m * p for square case

    # Build the structure tensor from the factorization
    T_computed = {}
    for k in range(R):
        u = U.column(k)
        v = V.column(k)
        w = W.column(k)
        for a in range(dim):
            for b in range(dim):
                for c in range(dim):
                    val = u[a] * v[b] * w[c]
                    if val != 0:
                        key = (a, b, c)
                        T_computed[key] = T_computed.get(key, 0) + val

    # Build the target structure tensor for <m,n,p>
    # Paper convention: T[a_{ij}, b_{kl}, c_{ts}] = delta_{is} * delta_{jk} * delta_{lt}
    # i.e., T[i*n+j, j*p+l, l*m+i] = 1
    T_target = {}
    for i in range(m):
        for j in range(n):
            for l in range(p):
                a_idx = i * n + j  # A_{i,j}
                b_idx = j * p + l  # B_{j,l}
                c_idx = l * m + i  # C_{l,i} (transposed output convention)
                T_target[(a_idx, b_idx, c_idx)] = 1

    # Compare
    errors = 0
    for key, val in T_target.items():
        if T_computed.get(key, 0) != val:
            print(f"  MISMATCH at {key}: expected {val}, got {T_computed.get(key, 0)}")
            errors += 1

    for key, val in T_computed.items():
        if val != 0 and key not in T_target:
            print(f"  SPURIOUS at {key}: got {val}")
            errors += 1

    if errors == 0:
        print(f"{name}: VERIFIED")
    else:
        print(f"{name}: FAILED ({errors} errors)")

    return errors == 0


# Run verification
ok = True

name1, U1, V1, W1, m1, n1, p1 = define_smirnov_alg1()
ok = verify(name1, U1, V1, W1, m1, n1, p1) and ok

name2, U2, V2, W2, m2, n2, p2 = define_smirnov_alg2()
ok = verify(name2, U2, V2, W2, m2, n2, p2) and ok

if not ok:
    raise SystemExit(1)
