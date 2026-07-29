# Route C, program 6 (Sage layer): structural proof that the exact
# stabilizer {(c,d) in F*^2 : mult_d.Aff.mult_c = Aff} is trivial,
# upgrading the exhaustive S3 witness to an argument that explains it.
#
# Proof skeleton (T = torus of mult matrices in GL(8,2), |T| = 255):
#   (c,d) in Stab  =>  mult_d = Aff.mult_{c^-1}.Aff^-1,
#   so Stab nontrivial  <=>  T  intersect  Aff.T.Aff^-1  is nontrivial.
#   If the intersection contains an element x of order 17: x acts
#   irreducibly on F_2^8 (ord_2(17) = 8), so its commutant is a field
#   isomorphic to GF(256) [L1, verified: 8-dimensional commutant with
#   255 units], hence T = units(commutant(x)) = Aff.T.Aff^-1, i.e.
#   Aff normalizes T.  Then Aff lies in N(T) = GammaL(1,256), so
#   Aff(x) = b.x^{2^k} — refuted by direct check [L3].
#   If the intersection is nontrivial but 17-free, it contains an
#   element of order 3 or 5; only 6 such elements exist in T and each
#   fails Aff.mult_e.Aff^-1 in T by finite check [L2].
#   Either way: contradiction.  QED (modulo Lean; the companion Lean
#   file RouteCGaugeStab.lean certifies the finite statement by
#   native_decide).
#
# Also: the gauge-group structure correction.  G = {(mult_a frob^k,
# frob^-k mult_a)} composes as (a,k)(b,m) = (a.b^{2^k}, k+m) —
# GammaL(1,256) = Z/255 : Z/8, NONABELIAN (the session note's
# "Z/255 x Z/8" direct product is wrong).  Verified below via the
# matrix group <mult_g, frob> in GL(8,2) and GAP StructureDescription.

R.<x> = PolynomialRing(GF(2))
F.<z> = GF(2^8, modulus=x^8 + x^4 + x^3 + x + 1)

def vec(u):
    c = u.polynomial().list()
    return vector(GF(2), c + [0]*(8 - len(c)))

def f2byte(u):
    return sum(int(t) << i for i, t in enumerate(vec(u)))

def matof(f):
    return matrix(GF(2), [vec(f(z^j)) for j in range(8)]).transpose()

mult = lambda a: matof(lambda u: a*u)
frob = matof(lambda u: u^2)
Aff = matrix(GF(2), 8, 8,
             lambda i, j: 1 if (j - i) % 8 in (0, 4, 5, 6, 7) else 0)

Fstar = [a for a in F if a != 0]
Tset = {mult(a).str(): a for a in Fstar}  # torus as a hashable set

# ---- L0: exhaustive intersection (re-derivation of S3 in the torus
# ---- formulation): T  intersect  Aff.T.Aff^-1  = {1}
Ai = Aff^-1
hits = [a for a in Fstar if (Aff * mult(a) * Ai).str() in Tset]
print("L0  |T  ^  Aff.T.Aff^-1| =", len(hits),
      " elements:", [f2byte(a) for a in hits])
assert hits == [F(1)]

# ---- L1: commutant of an order-17 element is an 8-dim field --------
x17 = None
for a in Fstar:
    if a.multiplicative_order() == 17:
        x17 = a
        break
M17 = mult(x17)
# solve M.X = X.M as a linear system on 64 unknowns
import itertools
eqs = []
basis = []
E = [[matrix(GF(2), 8, 8, {(i, j): 1}) for j in range(8)] for i in range(8)]
rowsys = []
for i in range(8):
    for j in range(8):
        C = M17*E[i][j] - E[i][j]*M17
        rowsys.append(vector(GF(2), sum((list(C.row(t)) for t in range(8)), [])))
K = matrix(GF(2), rowsys).left_kernel()  # coefficients over E[i][j]
dim = K.dimension()
print("L1  dim commutant(x17) =", dim, " (field GF(256) iff 8)")
# count units among the 2^8 commutant elements
units = 0
for co in K.basis_matrix().row_space():
    Mx = sum(co[8*i+j]*E[i][j] for i in range(8) for j in range(8))
    if Mx.is_invertible():
        units += 1
print("L1  units in commutant:", units, " (= 255 iff commutant is a field)")
print("L1  torus containing an order-17 element is unique:",
      dim == 8 and units == 255)

# ---- L2: the six elements of order 3 or 5 fail individually --------
small = [a for a in Fstar if a.multiplicative_order() in (3, 5)]
print("L2  elements of order 3 or 5:", [f2byte(a) for a in small])
bad = [f2byte(a) for a in small if (Aff * mult(a) * Ai).str() in Tset]
print("L2  of those, conjugated into T by Aff:", bad, " (must be empty)")
assert bad == []

# ---- L3: Aff is not semilinear (not in GammaL(1,256)) --------------
# if Aff(u) = b.u^{2^k} for all u, then b = Aff(1) and Aff equals the
# matrix of u -> b.u^{2^k}; test the FULL matrix for every k (pointwise
# tests at a single u can pass by coincidence — k=0 does at u=z).
b = F(sum(int(t)*z^i for i, t in enumerate(Aff * vec(F(1)))))
cands = [k for k in range(8)
         if matof(lambda u, k=k: b * u^(2^k)) == Aff]
print("L3  semilinear forms u -> Aff(1).u^(2^k) equal to Aff:", cands,
      " (must be empty; Aff(1) = %02x)" % f2byte(b))
assert cands == []

# ---- G: group structure of the gauge --------------------------------
gen = F.multiplicative_generator()
G = MatrixGroup([mult(gen), frob])
print("G   |<mult_g, frob>| =", G.order(), " (expect 2040)")
print("G   abelian:", G.is_abelian(), " (expect False)")
print("G   structure:", G.structure_description())
