import json

# ---------- 1. Symbolic identities over the rational function field ----------
# Variables a,b (fixed P), x,y (varying Q). Work in fraction field of QQ[a,b,x,y].
R.<a,b,x,y> = QQ[]
F = R.fraction_field()
a,b,x,y = F(a),F(b),F(x),F(y)

d   = x - a
lam = (y - b)/d
X   = lam^2 - x - a
Y   = lam*(a - X) - b
c   = a - X

# claim: c == d + 3a - lam^2   and   X == a - c   and   Y == c*lam - b
id1 = (c - (d + 3*a - lam^2))
id2 = (X - (a - c))
id3 = (Y - (c*lam - b))
print("id1 (c = d+3a-lam^2) is zero:", id1 == 0)
print("id2 (X = a-c)         is zero:", id2 == 0)
print("id3 (Y = c*lam - b)   is zero:", id3 == 0)

# ---------- 2. Non-injectivity of Phi:(c,lam)->(a-c, c*lam-b) at c=0 ----------
p = 2^256 - 2^32 - 977            # secp256k1 prime
K = GF(p)
aa, bb = K(0), K(7)               # secp256k1: y^2 = x^3 + 7, a,b arbitrary constants
def Phi(cval, lval):
    return (aa - cval, cval*lval - bb)
out1 = Phi(K(0), K(12345))
out2 = Phi(K(0), K(999999))
print("Phi(0,l1) == Phi(0,l2):", out1 == out2, "-> collapses c=0 fibre to", (out1[0], out1[1]))

# ---------- 3. Single-shear composite over F_p ----------
# M(u,v,w) = (u,v,w+uv);  A1 = identity;  A2(u,v,w) = (a-u, w-b, v)
def M(u,v,w): return (u, v, w + u*v)
def A2(u,v,w): return (aa - u, w - bb, v)
import random
random.seed(1r)
allgood = True
for _ in range(2000r):
    cval = K(random.randrange(int(p))); lval = K(random.randrange(int(p)))
    st = M(cval, lval, K(0))       # third arg initially zero
    st = A2(*st)                   # affine bijection
    Xv, Yv = aa - cval, cval*lval - bb
    ok = (st == (Xv, Yv, lval))    # composite yields (X, Y, lam)  -- aux holds lam, NOT 0
    allgood = allgood and ok
print("single-shear composite == (X, Y, lam) for all trials:", allgood)

# A2 is an affine bijection (linear part invertible):
L2 = matrix(K, [[-1,0,0],[0,0,1],[0,1,0]])
print("A2 linear part invertible (det!=0):", L2.det() != 0, "det =", int(L2.det()))

# ---------- 4. Rank obstruction: no affine functional of (c,lam,c*lam) is identically 0
# The functions {1, c, lam, c*lam} are linearly independent, so the only affine
# combination mu0 + mu1*c + mu2*lam + mu3*(c*lam) that vanishes for all (c,lam) is mu=0.
# Demonstrate independence via a 4x4 evaluation (Vandermonde-ish) matrix over F_p.
pts = [(K(0),K(0)), (K(1),K(0)), (K(0),K(1)), (K(1),K(1))]
Mev = matrix(K, [[1, cc, ll, cc*ll] for (cc,ll) in pts])
print("basis {1,c,lam,c*lam} independent (eval-matrix invertible):", Mev.det() != 0)

print(json.dumps({
    "identities_hold": bool(id1==0 and id2==0 and id3==0),
    "Phi_noninjective_at_c0": bool(out1==out2),
    "single_shear_yields_X_Y_lambda": bool(allgood),
    "aux_cannot_be_zero_because_functions_independent": bool(Mev.det()!=0),
}))
