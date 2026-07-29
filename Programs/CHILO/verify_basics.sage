#!/usr/bin/env sage
"""
Quick verifications for tr(X^3) over GF(2).
(i)   11 monomials of F
(ii)  F == e1^3 + e1*e2 + e3 over GF(2)
(iii) 5-product split of e1^2 + e2
(iv)  Formal vanishing on span{E12, E13, E21, E23}
(v)   tr(Xc^3) == 3*tr(ABC) for block-cyclic Xc over ZZ
"""

import json

print("=" * 60)
print("VERIFICATION (i): Monomials of F = tr(X^3) over GF(2)")
print("=" * 60)

R = PolynomialRing(GF(2), 'x', 9)
xs = R.gens()
# x11,x12,x13,x21,x22,x23,x31,x32,x33
x11,x12,x13,x21,x22,x23,x31,x32,x33 = xs

X = matrix(R, 3, 3, [x11,x12,x13,x21,x22,x23,x31,x32,x33])
X3 = X * X * X
F = sum(X3[i,i] for i in range(3))  # tr(X^3)

mons = F.monomials()
print("Number of monomials:", len(mons))
print("Monomials:", sorted([str(m) for m in mons]))
# All coefficients should be 1 over GF(2)
coeffs = F.coefficients()
print("All coefficients 1?", all(c == 1 for c in coeffs))
assert len(mons) == 11, f"Expected 11 monomials, got {len(mons)}"
print("PASS: 11 monomials confirmed\n")

print("=" * 60)
print("VERIFICATION (ii): F == e1^3 + e1*e2 + e3 over GF(2)")
print("=" * 60)

e1 = x11 + x22 + x33  # tr(X)
# e2 = sum of 2x2 minors of X
e2 = (x11*x22 + x12*x21 + x11*x33 + x13*x31 + x22*x33 + x23*x32)
# e3 = det(X) = perm(X) over GF(2)
e3 = (x11*x22*x33 + x11*x23*x32 + x12*x21*x33 + x12*x23*x31
      + x13*x21*x32 + x13*x22*x31)

newton_p3 = e1^3 + e1*e2 + e3  # Newton: p3 = e1^3 - 3*e1*e2 + 3*e3, mod 2

diff = F + newton_p3  # over GF(2), + is -
print("F + (e1^3 + e1*e2 + e3) =", diff)
assert diff == 0, f"Expected 0, got {diff}"
print("PASS: F = e1^3 + e1*e2 + e3 over GF(2)\n")

print("=" * 60)
print("VERIFICATION (iii): 5-product split of q = e1^2 + e2")
print("=" * 60)

q = e1^2 + e2
print("q =", q)

# Claimed: q = (x22+x33)^2 + (x11+x22)(x11+x33) + x12x21 + x13x31 + x23x32
# Over GF(2): a^2 = a, so (x22+x33)^2 = x22^2 + x33^2 = x22 + x33 (wrong)
# Wait: in characteristic 2, (a+b)^2 = a^2 + b^2. For linear forms over GF(2),
# a^2 = a only for elements of GF(2), not for polynomial variables.
# Actually x22^2 is NOT x22 in the polynomial ring - it's a separate monomial.
# But q is degree 2, so let's check directly.

# The claim says q splits into 5 products of pairs of linear forms.
# Let's check what q actually is:
print("e1^2 =", e1^2)
print("e2 =", e2)
print("q = e1^2 + e2 =", q)

# Over GF(2), e1^2 = (x11+x22+x33)^2 = x11^2+x22^2+x33^2
# so q = x11^2 + x22^2 + x33^2 + x11*x22 + x12*x21 + x11*x33 + x13*x31 + x22*x33 + x23*x32

# The 5-product claim:
# (x22+x33)^2 + (x11+x22)(x11+x33) + x12*x21 + x13*x31 + x23*x32
t1 = (x22 + x33)^2
t2 = (x11 + x22) * (x11 + x33)
t3 = x12 * x21
t4 = x13 * x31
t5 = x23 * x32

claimed_q = t1 + t2 + t3 + t4 + t5
print("Claimed decomposition =", claimed_q)
diff_q = q + claimed_q
print("Difference =", diff_q)

if diff_q == 0:
    print("PASS: 5-product decomposition of q confirmed")
else:
    # Let me check if the claim needs adjustment
    print("FAIL: difference is nonzero, investigating...")
    # Expand each term
    print("  (x22+x33)^2 =", t1)
    print("  (x11+x22)(x11+x33) =", t2)

    # Maybe the claim is that q splits into 5 products of LINEAR forms
    # where "product" means a product of 2 linear forms. Let me try
    # a slightly different decomposition.
    # q = x11^2 + x22^2 + x33^2 + x11*x22 + x12*x21 + x11*x33 + x13*x31 + x22*x33 + x23*x32
    # x11^2 = x11*x11, x22^2 = x22*x22, x33^2 = x33*x33
    # So we need at least 3 "self-products" for the diagonal terms
    # Plus x11*x22 + x11*x33 + x22*x33 (from e2 diagonal part)
    # Plus x12*x21 + x13*x31 + x23*x32
    #
    # Actually let me re-read: the user says the QUADRATIC form q splits
    # into 5 products of two linear forms (i.e., rank at most 5 as a
    # symmetric bilinear form over GF(2)).
    # But bilinear rank is different from expression as sum of products...

    # Let me just try to find a valid 5-term decomposition
    # x11^2 + x22^2 + x33^2 = x11*x11 + x22*x22 + x33*x33 (3 products)
    # x11*x22 + x11*x33 + x22*x33 can be grouped:
    # = x11*(x22+x33) + x22*x33 (2 products)
    # Total diagonal: x11^2 + x22^2 + x33^2 + x11*(x22+x33) + x22*x33
    # = x11*(x11+x22+x33) + x22*(x22+x33) + x33^2
    # = x11*e1 + x22*(x22+x33) + x33*x33
    # = x11*e1 + (x22+x33)*x22 + x33^2
    # Hmm, let me try: x11*(x11+x22+x33) = x11^2 + x11*x22 + x11*x33
    # (x22+x33)*x22 = x22^2 + x22*x33
    # x33*x33 = x33^2
    # Sum = x11^2 + x11*x22 + x11*x33 + x22^2 + x22*x33 + x33^2 = YES
    # So diagonal part = x11*e1 + x22*(x22+x33) + x33^2 (3 products)
    # Plus x12*x21 + x13*x31 + x23*x32 (3 products) = 6 total

    # The claim from the problem says 5 products. Let me try harder.
    # x11*e1 + x22*(x22+x33) + x33^2 + x12*x21 + x13*x31 + x23*x32
    # Can we merge? x22*(x22+x33) + x33^2 = x22^2 + x22*x33 + x33^2
    # = (x22+x33)^2 + x22*x33  (in char 2: (a+b)^2 = a^2+b^2)
    # Wait, (x22+x33)^2 = x22^2 + x33^2 (char 2), so
    # x22^2 + x22*x33 + x33^2 = (x22+x33)^2 + x22*x33. That's 2 products.
    # So total: x11*e1 + (x22+x33)^2 + x22*x33 + x12*x21 + x13*x31 + x23*x32
    # = 1 + 1 + 1 + 1 + 1 + 1 = 6 products
    #
    # Hmm. But squares in char 2: (x22+x33)^2 is a product of (x22+x33) with itself
    # Can any two of the 6 products be combined into one?
    # x11*e1 + x22*x33 = x11*(x11+x22+x33) + x22*x33
    # = x11^2 + x11*x22 + x11*x33 + x22*x33
    # = x11^2 + (x11+x33)*x22 + x11*x33... no simple merge
    #
    # Try: x11*e1 + (x22+x33)^2 = x11*(x11+x22+x33) + (x22+x33)^2
    # Let a = x11, b = x22+x33. Then a*(a+b) + b^2 = a^2 + ab + b^2
    # Not a product of two linear forms in general.
    #
    # OK, the claim might be about Waring rank or might need a specific form.
    # Let me just verify what the user actually claimed:
    # "q = e1^2 + e2 splits into 5 products of two linear forms:
    # (x22+x33)^2 + (x11+x22)(x11+x33) + x12x21 + x13x31 + x23x32"
    # That's (x22+x33)*(x22+x33) + (x11+x22)*(x11+x33) + x12*x21 + x13*x31 + x23*x32
    # = 5 products. Let me verify this sum.
    pass

print()

print("=" * 60)
print("VERIFICATION (iv): Formal vanishing on span{E12,E13,E21,E23}")
print("=" * 60)

# E12: matrix with 1 at (1,2), rest 0 -> x12=1, rest=0
# E13: x13=1
# E21: x21=1
# E23: x23=1
# General element: t1*E12 + t2*E13 + t3*E21 + t4*E23

S = PolynomialRing(GF(2), 't', 4)
t1,t2,t3,t4 = S.gens()

# Substitute into F: xij -> coefficient from the linear combination
# x11=0, x12=t1, x13=t2, x21=t3, x22=0, x23=t4, x31=0, x32=0, x33=0
sub = {x11: S(0), x12: t1, x13: t2, x21: t3, x22: S(0),
       x23: t4, x31: S(0), x32: S(0), x33: S(0)}

# Need to evaluate F at these values
# F is a polynomial in R = GF(2)[x11,...,x33]
# We substitute by evaluating
F_restricted = F(S(0), t1, t2, t3, S(0), t4, S(0), S(0), S(0))
print("F restricted to span{E12,E13,E21,E23} =", F_restricted)
assert F_restricted == 0, f"Expected 0, got {F_restricted}"
print("PASS: F vanishes formally on span{E12,E13,E21,E23}\n")

# Also verify the criterion: tr(vi^3)=0, tr(vi^2*vj)=0, tr(vivjvk)+tr(vivkvj)=0
print("Verifying vanishing criterion on the basis:")
E12 = matrix(GF(2), 3, 3, [0,1,0, 0,0,0, 0,0,0])
E13 = matrix(GF(2), 3, 3, [0,0,1, 0,0,0, 0,0,0])
E21 = matrix(GF(2), 3, 3, [0,0,0, 1,0,0, 0,0,0])
E23 = matrix(GF(2), 3, 3, [0,0,0, 0,0,1, 0,0,0])
basis = [E12, E13, E21, E23]
names = ["E12", "E13", "E21", "E23"]

all_ok = True
for i in range(4):
    vi = basis[i]
    tr_vi3 = (vi^3).trace()
    if tr_vi3 != 0:
        print(f"  FAIL: tr({names[i]}^3) = {tr_vi3}")
        all_ok = False

for i in range(4):
    for j in range(4):
        if i == j:
            continue
        vi, vj = basis[i], basis[j]
        tr_vi2vj = (vi^2 * vj).trace()
        if tr_vi2vj != 0:
            print(f"  FAIL: tr({names[i]}^2 * {names[j]}) = {tr_vi2vj}")
            all_ok = False

for i in range(4):
    for j in range(i+1, 4):
        for k in range(j+1, 4):
            vi, vj, vk = basis[i], basis[j], basis[k]
            val = (vi*vj*vk).trace() + (vi*vk*vj).trace()
            if val != 0:
                print(f"  FAIL: tr({names[i]}*{names[j]}*{names[k]}) + tr({names[i]}*{names[k]}*{names[j]}) = {val}")
                all_ok = False

if all_ok:
    print("PASS: All vanishing conditions satisfied for the basis\n")
else:
    print("FAIL: Some conditions not satisfied\n")

print("=" * 60)
print("VERIFICATION (v): tr(Xc^3) == 3*tr(ABC) over ZZ")
print("=" * 60)

# Block-cyclic: Xc = [[0,A,0],[0,0,B],[C,0,0]] with generic 3x3 blocks
Rz = PolynomialRing(ZZ, [f'a{i}{j}' for i in range(3) for j in range(3)]
                      + [f'b{i}{j}' for i in range(3) for j in range(3)]
                      + [f'c{i}{j}' for i in range(3) for j in range(3)])
gs = Rz.gens()
A = matrix(Rz, 3, 3, gs[0:9])
B = matrix(Rz, 3, 3, gs[9:18])
C = matrix(Rz, 3, 3, gs[18:27])

Z = matrix(Rz, 3, 3, 0)
# Xc = [[0, A, 0], [0, 0, B], [C, 0, 0]]
Xc = block_matrix(Rz, [[Z, A, Z], [Z, Z, B], [C, Z, Z]], subdivide=False)

Xc3 = Xc * Xc * Xc
tr_Xc3 = sum(Xc3[i,i] for i in range(9))

ABC = A * B * C
tr_ABC = sum(ABC[i,i] for i in range(3))

diff_z = tr_Xc3 - 3 * tr_ABC
print("tr(Xc^3) - 3*tr(ABC) =", diff_z)
assert diff_z == 0, f"Expected 0, got {diff_z}"
print("PASS: tr(Xc^3) = 3*tr(ABC) over ZZ\n")

print("=" * 60)
print("SANITY CHECK: Criterion validation on random subspaces")
print("=" * 60)

import random
random.seed(42r)

# Generate a random dim-3 subspace of M3(F2) and check:
# (a) criterion says vanish => F actually vanishes on substitution
# (b) criterion says not vanish => F doesn't vanish on substitution
def rand_mat():
    return matrix(GF(2), 3, 3, [GF(2).random_element() for _ in range(9)])

def check_formal_vanish_criterion(basis_mats):
    """Check the formal vanishing criterion for a list of matrices over GF(2)"""
    d = len(basis_mats)
    for i in range(d):
        if (basis_mats[i]^3).trace() != 0:
            return False
    for i in range(d):
        for j in range(d):
            if i != j:
                if (basis_mats[i]^2 * basis_mats[j]).trace() != 0:
                    return False
    for i in range(d):
        for j in range(i+1, d):
            for k in range(j+1, d):
                vi, vj, vk = basis_mats[i], basis_mats[j], basis_mats[k]
                if (vi*vj*vk).trace() + (vi*vk*vj).trace() != 0:
                    return False
    return True

def check_formal_vanish_polynomial(basis_mats):
    """Check formal vanishing by substituting into F with formal variables"""
    d = len(basis_mats)
    T = PolynomialRing(GF(2), 't', d)
    ts = T.gens()
    # Build generic element as sum t_i * v_i
    # Substitute into F
    vals = [T(0)] * 9
    for idx in range(d):
        entries = basis_mats[idx].list()  # row-major
        for k in range(9):
            vals[k] += ts[idx] * T(entries[k])
    F_sub = F(vals[0], vals[1], vals[2], vals[3], vals[4],
              vals[5], vals[6], vals[7], vals[8])
    return F_sub == 0

n_tests = 200
n_agree = 0
n_disagree = 0
for _ in range(n_tests):
    d = random.randint(2, 4)
    b = [rand_mat() for _ in range(d)]
    crit = check_formal_vanish_criterion(b)
    poly = check_formal_vanish_polynomial(b)
    if crit == poly:
        n_agree += 1
    else:
        n_disagree += 1
        print(f"  DISAGREE: criterion={crit}, polynomial={poly}, basis={[m.list() for m in b]}")

print(f"Tested {n_tests} random subspaces: {n_agree} agree, {n_disagree} disagree")
if n_disagree == 0:
    print("PASS: Criterion matches polynomial formal vanishing on all tests\n")
else:
    print("FAIL: Criterion disagrees with polynomial check\n")

print("ALL VERIFICATIONS COMPLETE")
