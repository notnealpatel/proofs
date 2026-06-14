# Oe1 pre-screen baseline: reproduce Or2's box-box / rho'-rho' obstruction for
# the GM S_4 group-orbit ansatz on <3,3,3>, then probe whether each follow-up
# family (>=3 orbits, relaxed sigma-twist) escapes it.
#
# Conventions mirror cmd/probe-gm-orbit exactly (group.go, basis.go):
#   rho = standard 3-dim irrep of S_4 (signed permutation / tetrahedron basis).
#   K = Q(sqrt3); the box (2-dim) basis carries sqrt3.
#   Frobenius pairing <X,A> = sum_ij X_ij A_ij  (mat.go frob).
#   conj(g,X) = rho(g) X rho(g)^T  (rho orthogonal).
#   sigma = rho((123)); twist m2 = sigma m1 sigma^-1, m3 = sigma^2 m1 sigma^-2.
#
# A constraint triple (A,B,C) is "obstructed" iff the SYMBOLIC orbit-sum
#   sum_g <A, g m1 g^-1> <B, g m2 g^-1> <C, g m3 g^-1>
# is identically zero as a polynomial in the seed variables (the coordinates of
# m1 in the H-fixed space). On such triples the ansatz can never supply the
# residual tr(A)tr(B)tr(C) - tr(ABC), so a nonzero residual => unit ideal.

import json, itertools

K.<r3> = QuadraticField(3)

def Mt(rows): return matrix(K, rows)

# Generators of rho (group.go generatorMats)
rho_12 = Mt([[0,1,0],[1,0,0],[0,0,1]])
rho_23 = Mt([[1,0,0],[0,0,1],[0,1,0]])
rho_34 = Mt([[0,-1,0],[-1,0,0],[0,0,1]])
sigma  = Mt([[0,0,1],[1,0,0],[0,1,0]])   # rho((123))

# Enumerate S_4 (BFS) as perm-tuple -> matrix.
gens = {(1,0,2,3): rho_12, (0,2,1,3): rho_23, (0,1,3,2): rho_34}
def compose(p,q): return tuple(p[q[i]] for i in range(4))
ident = (0,1,2,3)
elems = {ident: identity_matrix(K,3)}
frontier=[ident]
for _ in range(100):
    if not frontier: break
    new=[]
    for e in frontier:
        for gp in gens:
            ne = compose(gp,e)
            if ne not in elems:
                elems[ne] = gens[gp]*elems[e]
                new.append(ne)
    frontier=new
assert len(elems)==24, len(elems)
ELEM = list(elems.values())

# rho-conjugation: conj(g,X) = g X g^T
def conjM(g, X): return g*X*g.transpose()

# rho⊗rho* basis (basis.go rrStarBasis), 9 matrices, names match the Go code.
def rrStarBasis():
    idm = identity_matrix(K,3)
    boxX = diagonal_matrix(K,[1, -1/2, -1/2])
    boxY = diagonal_matrix(K,[0, r3/2, -r3/2])
    def E(pairs):
        M = matrix(K,3,3)
        for (i,j,v) in pairs: M[i,j]=v
        return M
    s1 = E([(1,2,1),(2,1,1)])
    s2 = E([(0,2,1),(2,0,1)])
    s3 = E([(0,1,1),(1,0,1)])
    a1 = E([(1,2,1),(2,1,-1)])
    a2 = E([(0,2,-1),(2,0,1)])
    a3 = E([(0,1,1),(1,0,-1)])
    return [idm,boxX,boxY,s1,s2,s3,a1,a2,a3]
BR = rrStarBasis()
NAMES = ["id","box_x","box_y","s1","s2","s3","a1","a2","a3"]

# Fixed-space basis for a subgroup given by perm generators (fixed.go fixedBasis):
# null space of stacked (conj_h - I) over h in H, on vec(X) row-major.
def subgroup(genperms):
    H={ident}; fr=[ident]
    while fr:
        nn=[]
        for e in fr:
            for g in genperms:
                ne=compose(g,e)
                if ne not in H: H.add(ne); nn.append(ne)
        fr=nn
    return H

def conjOperator(g):  # 9x9 over K, row-major vec: out = C vec(X), C vec(E_ij)=vec(g E_ij g^T)
    C = matrix(K,9,9)
    for i in range(3):
        for j in range(3):
            E = matrix(K,3,3); E[i,j]=1
            img = conjM(elems[g], E)
            col = i*3+j
            for a in range(3):
                for b in range(3):
                    C[a*3+b, col] = img[a,b]
    return C

def fixedBasis(genperms):
    H = subgroup(genperms)
    rows = []
    I9 = identity_matrix(K,9)
    for h in H:
        rows.append(conjOperator(h) - I9)
    big = block_matrix(K,[[m] for m in rows])
    ker = big.right_kernel().basis()
    # reshape each length-9 vector to 3x3 row-major
    out=[]
    for v in ker:
        out.append(matrix(K,3,3,[v[k] for k in range(9)]))
    return out, len(H)

# Catalog (group.go), perm gens for each stabilizer type.
S3   = [(0,2,1,3),(0,1,3,2)]
K4   = [(1,0,3,2),(2,3,0,1)]
Z4   = [(1,2,3,0)]
Z3   = [(1,2,0,3)]
Z2t  = [(1,0,2,3)]
Z2d  = [(1,0,3,2)]
CATALOG = [("S_3",S3,4),("K_4",K4,6),("Z_4",Z4,6),("Z_3",Z3,8),
           ("Z_2t",Z2t,12),("Z_2d",Z2d,12)]

# Symbolic orbit-sum support: for a single orbit with H-fixed basis of dim d, the
# orbit term on triple (A,B,C) is a degree-3 poly in d variables. We test whether
# it is identically zero by evaluating its symbolic structure. Implement with a
# polynomial ring so "identically zero" is exact (not a random-point probe).
def orbit_obstructed_set(genperms, sigmaMat, twist=True):
    fb, hord = fixedBasis(genperms)
    d = len(fb)
    R = PolynomialRing(K, d, [f"x{i}" for i in range(d)] if d>0 else ["x0"])
    xs = R.gens()
    # symbolic m1 = sum x_p fb[p]   (3x3 matrix over R)
    m1 = matrix(R,3,3)
    for p in range(d):
        m1 += xs[p]*fb[p].change_ring(R)
    if twist:
        s = sigmaMat.change_ring(R)
        m2 = s*m1*s.transpose()
        s2 = (sigmaMat*sigmaMat).change_ring(R)
        m3 = s2*m1*s2.transpose()
    else:
        # decoupled: independent seeds (handled by caller for >1 free seed)
        m2 = m1; m3 = m1
    # precompute g m_f g^-1 for all g, f
    gm = {}
    for gi,g in enumerate(ELEM):
        gR = g.change_ring(R)
        gm[(gi,0)] = gR*m1*gR.transpose()
        gm[(gi,1)] = gR*m2*gR.transpose()
        gm[(gi,2)] = gR*m3*gR.transpose()
    def frobR(Xconst, Msym):
        acc = R(0)
        Xc = Xconst
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0:
                    acc += Xc[i,j]*Msym[i,j]
        return acc
    obstructed=[]
    nonzero=[]
    for ai in range(9):
        for bi in range(9):
            for ci in range(9):
                orb = R(0)
                for gi in range(len(ELEM)):
                    la = frobR(BR[ai], gm[(gi,0)])
                    if la==0: continue
                    lb = frobR(BR[bi], gm[(gi,1)])
                    if lb==0: continue
                    lc = frobR(BR[ci], gm[(gi,2)])
                    if lc==0: continue
                    orb += la*lb*lc
                if orb==0:
                    obstructed.append((ai,bi,ci))
                else:
                    nonzero.append((ai,bi,ci))
    return obstructed, nonzero, d, hord

# Required residual tr(A)tr(B)tr(C) - tr(ABC) for MM target.
def residual(ai,bi,ci):
    A,B,C = BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace() - (A*B*C).trace()

print("=== BASELINE: per-orbit obstructed-triple sets (twisted, MM target) ===")
results = {}
for name, g, orb in CATALOG:
    obs, nz, d, hord = orbit_obstructed_set(g, sigma, twist=True)
    # Among obstructed triples, how many have NONZERO required residual?
    # Those are the killers: orbit term identically 0 but residual !=0.
    killers = [(ai,bi,ci) for (ai,bi,ci) in obs if residual(ai,bi,ci)!=0]
    results[name] = {"orbit":orb,"fixed_dim":d,"|H|":hord,
                     "n_obstructed":len(obs),"n_nonzero":len(nz),
                     "n_killer_triples":len(killers)}
    print(f"{name:5s} orbit={orb:2d} dim={d} |H|={hord:2d}: "
          f"{len(obs):3d} obstructed, {len(nz):3d} nonzero, "
          f"{len(killers):3d} KILLER triples (orbit=0 but residual!=0)")

print(json.dumps(results))
