# Johnson-McLoughlin one-parameter family of rank-23 decompositions of <3,3,3>
# Transcribed from Table 2 of their 1986 paper.
#
# Convention: Each product r has three 3x3 matrices A^r, B^r, C^r.
# U[:,r] = vec(A^r) row-major, V[:,r] = vec(B^r) row-major, W[:,r] = vec(C^r^T) row-major.
# The paper's C^r is transposed when stored in W so that the standard tensor identity holds:
#   sum_r U[i*3+j, r] * V[k*3+l, r] * W[t*3+s, r] = delta(i,t)*delta(j,k)*delta(l,s)
# This matches the matrix multiplication structure tensor for C = A*B.

def _build_triples(x):
    """Return list of 23 triples (A, B, C), each a list-of-lists 3x3, with symbolic x."""
    triples = []

    # r=1
    triples.append((
        [[1,0,0],[0,0,0],[0,0,0]],
        [[1,0,0],[0,0,0],[0,0,0]],
        [[1,0,0],[0,0,0],[0,0,0]],
    ))
    # r=2
    triples.append((
        [[0,0,0],[0,1,0],[0,0,0]],
        [[0,0,0],[-1,-1,0],[0,0,0]],
        [[0,0,0],[1,-1,0],[0,0,0]],
    ))
    # r=3
    triples.append((
        [[0,-1,1],[0,-1,0],[0,0,0]],
        [[0,0,0],[1,0,0],[0,-1,1]],
        [[0,-1,-1],[0,1,1],[1,0,1]],
    ))
    # r=4
    triples.append((
        [[0,0,0],[-1,0,-1],[0,0,0]],
        [[0,0,0],[0,0,0],[1,1,0]],
        [[0,-1,0],[0,0,0],[0,0,0]],
    ))
    # r=5 (parameter-dependent)
    triples.append((
        [[-x, x-1, 0],[0, x-1, 0],[0, 1, 0]],
        [[0, 1-2/x, -1],[0, 1, -1],[0, 1, -1]],
        [[0, 0, 0],[QQ(1)/2, 0, QQ(1)/2],[QQ(1)/2, 0, -QQ(1)/2]],
    ))
    # r=6
    triples.append((
        [[0,0,0],[1,0,0],[-QQ(1)/2, 0, QQ(1)/2]],
        [[1,0,0],[0,0,0],[-1,-1,0]],
        [[0,1,0],[0,-1,-1],[0,0,1]],
    ))
    # r=7 (parameter-dependent)
    triples.append((
        [[-1, 1, 0],[0, 1, 0],[0, 0, 0]],
        [[0, 1-x, x-1],[0, -x, x],[0, -x, x]],
        [[0, 0, 0],[0, 0, 0],[1, 0, 0]],
    ))
    # r=8
    triples.append((
        [[0,0,0],[-1,0,0],[0,0,0]],
        [[-1,-1,0],[0,0,0],[1,1,0]],
        [[0,0,0],[0,1,1],[0,0,-1]],
    ))
    # r=9
    triples.append((
        [[0,0,0],[0,0,0],[1,-1,0]],
        [[0,1,1],[0,0,0],[0,-1,1]],
        [[0,0,0],[0,0,0],[0,0,1]],
    ))
    # r=10
    triples.append((
        [[0,0,0],[0,0,1],[0,0,0]],
        [[0,0,0],[0,0,0],[0,0,-1]],
        [[0,1,1],[0,-1,-1],[0,-1,-1]],
    ))
    # r=11 (parameter-dependent)
    triples.append((
        [[-1, 1-1/x, 0],[-1, 1-1/x, 0],[1, 1/x-1, 0]],
        [[0, 1, 0],[0, 0, 0],[0, 0, 0]],
        [[0, 0, 0],[0, 0, 1],[0, 0, -1]],
    ))
    # r=12
    triples.append((
        [[0,0,0],[0,0,0],[-1,0,1]],
        [[-1,0,0],[0,0,0],[1,0,1]],
        [[0, QQ(1)/2, QQ(1)/2],[0, -QQ(1)/2, -QQ(1)/2],[0, 0, QQ(1)/2]],
    ))
    # r=13 (parameter-dependent)
    triples.append((
        [[-x, x-1, 0],[0, x-1, 0],[0, 0, 0]],
        [[0, 1, -1],[0, 1, -1],[0, 1, -1]],
        [[0, 0, 0],[-QQ(1)/2, 0, -QQ(1)/2],[QQ(1)/2, 0, QQ(1)/2]],
    ))
    # r=14
    triples.append((
        [[0,1,-1],[0,0,0],[0,0,0]],
        [[0,0,0],[1,0,0],[0,0,0]],
        [[1,-1,0],[-1,1,0],[0,0,0]],
    ))
    # r=15
    triples.append((
        [[0,-1,1],[0,-1,1],[0,1,-1]],
        [[0,0,0],[0,0,0],[0,1,0]],
        [[0,0,1],[0,0,-1],[0,0,-1]],
    ))
    # r=16
    triples.append((
        [[0,0,0],[0,1,0],[0,0,0]],
        [[0,0,0],[0,0,-1],[0,0,0]],
        [[0,0,0],[0,0,0],[1,-1,0]],
    ))
    # r=17 (parameter-dependent)
    triples.append((
        [[0,1,0],[0,1,0],[0,-1,0]],
        [[0, 1-1/x, 0],[0, 1, 0],[0, 1, 0]],
        [[0,0,0],[1,0,0],[1,0,0]],
    ))
    # r=18
    triples.append((
        [[0,0,0],[-1,0,0],[0,0,0]],
        [[0,0,1],[0,0,0],[0,0,0]],
        [[0,0,0],[0,0,0],[0,-1,0]],
    ))
    # r=19
    triples.append((
        [[0,0,1],[0,0,0],[0,0,0]],
        [[0,0,0],[1,0,0],[1,0,0]],
        [[1,0,0],[0,0,0],[0,0,0]],
    ))
    # r=20
    triples.append((
        [[0,-1,1],[0,-1,0],[0,1,0]],
        [[0,0,0],[1,0,0],[0,-1,0]],
        [[0,0,1],[-1,0,-1],[-1,0,-1]],
    ))
    # r=21
    triples.append((
        [[0,0,0],[0,0,0],[-1,0,-1]],
        [[1,0,0],[0,0,0],[1,1,0]],
        [[0,0,-QQ(1)/2],[0,0,0],[0,0,0]],
    ))
    # r=22
    triples.append((
        [[0,1,-1],[0,1,-1],[-QQ(1)/2, 0, QQ(1)/2]],
        [[0,0,0],[0,0,0],[0,-1,1]],
        [[0,-1,-1],[0,1,1],[0,0,1]],
    ))
    # r=23
    triples.append((
        [[0,0,0],[0,0,0],[0,1,0]],
        [[0,-QQ(1)/2,-QQ(1)/2],[-1,-QQ(1)/2,-QQ(1)/2],[0,QQ(1)/2,-QQ(1)/2]],
        [[0,0,0],[-1,0,-1],[-1,0,-1]],
    ))

    return triples


def jm_family(xval):
    """Return (U, V, W) as 9x23 matrices over QQ for the given parameter value xval."""
    x = var('x')
    triples = _build_triples(x)
    U = matrix(QQ, 9, 23)
    V = matrix(QQ, 9, 23)
    W = matrix(QQ, 9, 23)
    for r, (A, B, C) in enumerate(triples):
        for i in range(3):
            for j in range(3):
                val_a = A[i][j]
                val_b = B[i][j]
                val_c = C[i][j]
                # Substitute x -> xval
                if hasattr(val_a, 'subs'):
                    val_a = QQ(val_a.subs(x=xval))
                else:
                    val_a = QQ(val_a)
                if hasattr(val_b, 'subs'):
                    val_b = QQ(val_b.subs(x=xval))
                else:
                    val_b = QQ(val_b)
                if hasattr(val_c, 'subs'):
                    val_c = QQ(val_c.subs(x=xval))
                else:
                    val_c = QQ(val_c)
                U[i*3+j, r] = val_a
                V[i*3+j, r] = val_b
                # Transpose C: W[i*3+j, r] = C^r[j][i]
                val_ct = C[j][i]
                if hasattr(val_ct, 'subs'):
                    val_ct = QQ(val_ct.subs(x=xval))
                else:
                    val_ct = QQ(val_ct)
                W[i*3+j, r] = val_ct
    return U, V, W


def verify_tensor(U, V, W, label=""):
    """Verify sum_r U[a,r]*V[b,r]*W[c,r] = delta(i,t)*delta(j,k)*delta(l,s)
    where a=3i+j, b=3k+l, c=3t+s."""
    ok = True
    for i in range(3):
        for j in range(3):
            for k in range(3):
                for l in range(3):
                    for t in range(3):
                        for s in range(3):
                            a = 3*i + j
                            b = 3*k + l
                            c = 3*t + s
                            val = sum(U[a,r]*V[b,r]*W[c,r] for r in range(23))
                            expected = (1 if (i==t and j==k and l==s) else 0)
                            if val != expected:
                                ok = False
                                if not ok:
                                    print(f"  FAIL at i={i},j={j},k={k},l={l},t={t},s={s}: got {val}, expected {expected}")
    if ok:
        print(f"{label}: VERIFIED")
    else:
        print(f"{label}: FAILED")
    return ok


def factor_rank_signature(U, V, W):
    """Compute (rank(A^r), rank(B^r), rank(C^r)) for each product r and return histogram."""
    from collections import Counter
    sig = Counter()
    for r in range(23):
        A = matrix(QQ, 3, 3, list(U.column(r)))
        B = matrix(QQ, 3, 3, list(V.column(r)))
        C = matrix(QQ, 3, 3, list(W.column(r)))
        sig[(A.rank(), B.rank(), C.rank())] += 1
    return dict(sig)


# ---- Main ----

print("=" * 60)
print("Johnson-McLoughlin one-parameter family for <3,3,3>")
print("=" * 60)

for xval in [2, 3]:
    print(f"\n--- x = {xval} ---")
    U, V, W = jm_family(xval)
    verify_tensor(U, V, W, label=f"x={xval}")
    sig = factor_rank_signature(U, V, W)
    print(f"x={xval}: factor-rank signature: {sig}")

# Laderman's known signature
laderman_sig = {(1,1,1): 13, (2,2,2): 4, (1,1,3): 2}
print(f"\nLaderman signature: {laderman_sig}")
for xval in [2, 3]:
    U, V, W = jm_family(xval)
    sig = factor_rank_signature(U, V, W)
    # Normalize for comparison
    match = (sig == laderman_sig)
    if match:
        print(f"x={xval}: MATCHES Laderman signature")
    else:
        print(f"x={xval}: DIFFERS from Laderman signature")
        print(f"  JM:       {sig}")
        print(f"  Laderman: {laderman_sig}")
