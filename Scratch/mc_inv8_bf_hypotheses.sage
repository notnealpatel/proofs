"""
Independent witness: algebraic-degree properties of x^254 on GF(2^8)
viewed as an (8,8) vectorial Boolean function.

Computes ANF via Mobius transform (256 points, exact).
"""

import json

# ---------------------------------------------------------------
# Mobius transform: truth table -> ANF coefficients over GF(2)
# ---------------------------------------------------------------
def mobius_transform(tt):
    """
    Given a truth table tt of length 2^n (list of 0/1),
    return the ANF coefficient vector (list of 0/1).
    tt[i] = f(x) where x is the bit-vector of i.
    """
    n = len(tt)
    a = list(tt)
    k = 1
    while k < n:
        for i in range(n):
            if i & k:
                a[i] ^^= a[i ^^ k]    # xor in Sage syntax
        k <<= 1
    return a

def anf_degree(anf_coeffs, n):
    """Algebraic degree = max Hamming weight of indices with nonzero ANF coefficient."""
    deg = 0
    for i in range(len(anf_coeffs)):
        if anf_coeffs[i]:
            w = bin(i).count('1')
            if w > deg:
                deg = w
    return deg

def degree7_monomial_indices(n):
    """Return sorted list of indices with Hamming weight exactly n-1 = 7 (for n=8)."""
    return sorted([i for i in range(2^n) if bin(i).count('1') == n - 1])

# ---------------------------------------------------------------
# Setup GF(2^8) with polynomial basis
# ---------------------------------------------------------------
n = 8
N = 2^n  # 256

F.<alpha> = GF(2^n)

# Enumerate all elements; fix ordering by integer representation
elements = [F.from_integer(i) for i in range(N)]

# Basis 1: canonical polynomial basis {1, alpha, alpha^2, ..., alpha^7}
basis1 = [alpha^i for i in range(n)]

def to_bits(elem, basis):
    """Express elem in terms of the given basis over GF(2). Returns list of n bits."""
    V = F.vector_space(map=False)
    # We'll use the coordinate extraction manually
    # Build the change-of-basis matrix
    M = matrix(GF(2), n, n, [list(V(b)) for b in basis])
    coords = M.solve_left(vector(GF(2), list(V(elem))))
    return [int(c) for c in coords]

# Precompute coordinate extraction for basis1
V = F.vector_space(map=False)
M1 = matrix(GF(2), n, n, [list(V(b)) for b in basis1])
M1_inv = M1.inverse()

def coords_basis1(elem):
    v = vector(GF(2), list(V(elem)))
    c = M1_inv * v
    return [int(x) for x in c]

# ---------------------------------------------------------------
# Compute inversion map truth tables for each coordinate (basis 1)
# ---------------------------------------------------------------
print("=" * 60)
print("PART 1 & 2: Coordinate functions in polynomial basis")
print("Basis: {1, alpha, alpha^2, ..., alpha^7}")
print("Modulus:", F.modulus())
print("=" * 60)

# f(x) = x^254, with f(0) = 0
inv_images = []
for i in range(N):
    x = elements[i]
    if x == F(0):
        inv_images.append(F(0))
    else:
        inv_images.append(x^254)

# Build truth tables for each coordinate function
# tt_j[i] = j-th coordinate of f(elements[i]) in basis1
coord_tts = []
for j in range(n):
    tt = []
    for i in range(N):
        bits = coords_basis1(inv_images[i])
        tt.append(bits[j])
    coord_tts.append(tt)

# Compute ANF and degrees for each coordinate
coord_anfs = []
coord_degrees = []
for j in range(n):
    anf = mobius_transform(coord_tts[j])
    coord_anfs.append(anf)
    deg = anf_degree(anf, n)
    coord_degrees.append(deg)

print("\n--- Part 1: Algebraic degrees of 8 coordinate functions ---")
for j in range(n):
    print(f"  Coordinate f_{j}: degree = {coord_degrees[j]}")

all_deg7 = all(d == 7 for d in coord_degrees)
print(f"\n  All degree 7? {all_deg7}")

# Part 2: degree-7 homogeneous parts
deg7_indices = degree7_monomial_indices(n)
print(f"\n--- Part 2: Degree-7 homogeneous parts ---")
print(f"  Number of degree-7 monomials: {len(deg7_indices)}")
print(f"  Monomial indices (binary): {[bin(idx) for idx in deg7_indices]}")

# Build 8x8 matrix: row j = coefficients of coordinate j at the 8 degree-7 monomials
deg7_matrix_rows = []
for j in range(n):
    row = [coord_anfs[j][idx] for idx in deg7_indices]
    deg7_matrix_rows.append(row)
    print(f"  f_{j} degree-7 coeffs: {row}")

M_deg7 = matrix(GF(2), deg7_matrix_rows)
rk = M_deg7.rank()
print(f"\n  8x8 matrix over GF(2):")
print(M_deg7)
print(f"  Rank = {rk}")

# ---------------------------------------------------------------
# PART 3: All 255 nonzero component functions Tr(b * x^254)
# ---------------------------------------------------------------
print("\n" + "=" * 60)
print("PART 3: Degree of Tr(b * x^254) for all 255 nonzero b")
print("=" * 60)

component_degrees = {}
for b_int in range(1, N):
    b = F.from_integer(b_int)
    # Build truth table: for each x in GF(2^8), compute Tr(b * x^254)
    tt = []
    for i in range(N):
        x = elements[i]
        if x == F(0):
            val = F(0)
        else:
            val = b * x^254
        tr = val.trace()  # absolute trace to GF(2)
        tt.append(int(tr))
    anf = mobius_transform(tt)
    deg = anf_degree(anf, n)
    component_degrees[b_int] = deg

# Collect multiset of degrees
from collections import Counter
degree_counts = Counter(component_degrees.values())
print(f"\n  Degree multiset: {dict(degree_counts)}")
print(f"  (degree -> count)")
for d in sorted(degree_counts.keys()):
    print(f"    degree {d}: {degree_counts[d]} component(s)")

all_comp_deg7 = all(d == 7 for d in component_degrees.values())
print(f"\n  All 255 components have degree 7? {all_comp_deg7}")

# ---------------------------------------------------------------
# PART 4: Repeat in a SECOND basis (normal basis)
# ---------------------------------------------------------------
print("\n" + "=" * 60)
print("PART 4: Sanity check in a DIFFERENT basis")
print("=" * 60)

# Try to find a normal basis: {beta, beta^2, beta^4, ..., beta^(2^7)}
# A normal basis exists iff beta has full orbit under Frobenius.
# We search for such a beta.
normal_beta = None
for trial in range(1, N):
    beta = F.from_integer(trial)
    if beta == F(0):
        continue
    basis_candidate = [beta^(2^i) for i in range(n)]
    M_test = matrix(GF(2), n, n, [list(V(b)) for b in basis_candidate])
    if M_test.rank() == n:
        normal_beta = beta
        break

if normal_beta is None:
    print("  ERROR: No normal basis found (should not happen for GF(2^8))")
else:
    print(f"  Normal element: beta = {normal_beta} (fetch_int index {trial})")
    basis2 = [normal_beta^(2^i) for i in range(n)]
    print(f"  Basis: {{beta^(2^i) : i = 0..7}}")

    M2 = matrix(GF(2), n, n, [list(V(b)) for b in basis2])
    M2_inv = M2.inverse()

    def coords_basis2(elem):
        v = vector(GF(2), list(V(elem)))
        c = M2_inv * v
        return [int(x) for x in c]

    # Coordinate truth tables in basis 2
    coord_tts2 = []
    for j in range(n):
        tt = []
        for i in range(N):
            bits = coords_basis2(inv_images[i])
            tt.append(bits[j])
        coord_tts2.append(tt)

    coord_anfs2 = []
    coord_degrees2 = []
    for j in range(n):
        anf = mobius_transform(coord_tts2[j])
        coord_anfs2.append(anf)
        deg = anf_degree(anf, n)
        coord_degrees2.append(deg)

    print(f"\n  Coordinate degrees (basis 2): {coord_degrees2}")
    all_deg7_b2 = all(d == 7 for d in coord_degrees2)
    print(f"  All degree 7? {all_deg7_b2}")

    # Degree-7 matrix in basis 2
    deg7_matrix_rows2 = []
    for j in range(n):
        row = [coord_anfs2[j][idx] for idx in deg7_indices]
        deg7_matrix_rows2.append(row)

    M_deg7_b2 = matrix(GF(2), deg7_matrix_rows2)
    rk2 = M_deg7_b2.rank()
    print(f"  Degree-7 matrix (basis 2):")
    print(f"  {M_deg7_b2}")
    print(f"  Rank = {rk2}")

# ---------------------------------------------------------------
# SUMMARY
# ---------------------------------------------------------------
print("\n" + "=" * 60)
print("SUMMARY (witnessed via Sage)")
print("=" * 60)
print(f"  H1 (coordinate degrees): {'CONFIRMED' if all_deg7 else 'REFUTED'} — all 8 coordinate functions have degree {set(coord_degrees)}")
print(f"  H2 (degree-7 matrix rank): rank = {rk} over GF(2) — {'full rank (invertible)' if rk == 8 else 'RANK DEFICIENT'}")
print(f"  H3 (all 255 components): {'CONFIRMED' if all_comp_deg7 else 'REFUTED'} — degree multiset = {dict(degree_counts)}")
if normal_beta is not None:
    print(f"  H4 (basis independence): {'CONFIRMED' if (all_deg7_b2 and rk2 == rk) else 'DIFFERS'} — basis 2 degrees {set(coord_degrees2)}, rank {rk2}")
