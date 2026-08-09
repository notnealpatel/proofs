# Oe1 Family 1 pre-screen: >=3 orbits under S_4 (same H-fixed seed spaces).
#
# Or2's obstruction is per-orbit and ADDITIVE: on a basis triple (A,B,C), the
# total orbit-sum is sum over orbits of that orbit's contribution. If a triple is
# obstructed (contribution identically 0 in the seed vars) for EVERY orbit type,
# then ANY multiset of orbits -- 3, 4, ... -- still contributes identically 0
# there. If such a commonly-obstructed triple also has nonzero MM residual
# tr(A)tr(B)tr(C)-tr(ABC), it is a KILLER that no number of catalog orbits can
# satisfy => the >=3-orbit family is DEAD by the same mechanism, rank budget moot.
#
# Decisive computation: intersect the 6 catalog obstructed-sets; among the common
# triples, count those with nonzero residual. If >0, Family 1 is PRE-SCREEN-DEAD.

import json, itertools

K.<r3> = QuadraticField(3)
def Mt(rows): return matrix(K, rows)
rho_12 = Mt([[0,1,0],[1,0,0],[0,0,1]])
rho_23 = Mt([[1,0,0],[0,0,1],[0,1,0]])
rho_34 = Mt([[0,-1,0],[-1,0,0],[0,0,1]])
sigma  = Mt([[0,0,1],[1,0,0],[0,1,0]])
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
                elems[ne] = gens[gp]*elems[e]; new.append(ne)
    frontier=new
assert len(elems)==24
ELEM = list(elems.values())
def conjM(g, X): return g*X*g.transpose()

def rrStarBasis():
    idm = identity_matrix(K,3)
    boxX = diagonal_matrix(K,[1, -1/2, -1/2])
    boxY = diagonal_matrix(K,[0, r3/2, -r3/2])
    def E(pairs):
        M = matrix(K,3,3)
        for (i,j,v) in pairs: M[i,j]=v
        return M
    s1=E([(1,2,1),(2,1,1)]); s2=E([(0,2,1),(2,0,1)]); s3=E([(0,1,1),(1,0,1)])
    a1=E([(1,2,1),(2,1,-1)]); a2=E([(0,2,-1),(2,0,1)]); a3=E([(0,1,1),(1,0,-1)])
    return [idm,boxX,boxY,s1,s2,s3,a1,a2,a3]
BR = rrStarBasis()
NAMES = ["id","box_x","box_y","s1","s2","s3","a1","a2","a3"]

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
def conjOperator(g):
    C = matrix(K,9,9)
    for i in range(3):
        for j in range(3):
            E = matrix(K,3,3); E[i,j]=1
            img = conjM(elems[g], E); col=i*3+j
            for a in range(3):
                for b in range(3): C[a*3+b, col]=img[a,b]
    return C
def fixedBasis(genperms):
    H=subgroup(genperms); rows=[]; I9=identity_matrix(K,9)
    for h in H: rows.append(conjOperator(h)-I9)
    big=block_matrix(K,[[m] for m in rows]); ker=big.right_kernel().basis()
    return [matrix(K,3,3,[v[k] for k in range(9)]) for v in ker], len(H)

S3=[(0,2,1,3),(0,1,3,2)]; K4=[(1,0,3,2),(2,3,0,1)]; Z4=[(1,2,3,0)]
Z3=[(1,2,0,3)]; Z2t=[(1,0,2,3)]; Z2d=[(1,0,3,2)]
CATALOG=[("S_3",S3,4),("K_4",K4,6),("Z_4",Z4,6),("Z_3",Z3,8),
         ("Z_2t",Z2t,12),("Z_2d",Z2d,12)]

def orbit_obstructed_set(genperms):
    fb,hord = fixedBasis(genperms); d=len(fb)
    R = PolynomialRing(K, d, [f"x{i}" for i in range(d)] if d>0 else ["x0"])
    xs=R.gens()
    m1=matrix(R,3,3)
    for p in range(d): m1 += xs[p]*fb[p].change_ring(R)
    s=sigma.change_ring(R); m2=s*m1*s.transpose()
    s2=(sigma*sigma).change_ring(R); m3=s2*m1*s2.transpose()
    gm={}
    for gi,g in enumerate(ELEM):
        gR=g.change_ring(R)
        gm[(gi,0)]=gR*m1*gR.transpose(); gm[(gi,1)]=gR*m2*gR.transpose(); gm[(gi,2)]=gR*m3*gR.transpose()
    def frobR(Xc,Ms):
        acc=R(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc += Xc[i,j]*Ms[i,j]
        return acc
    obs=set()
    for ai in range(9):
        for bi in range(9):
            for ci in range(9):
                orb=R(0)
                for gi in range(len(ELEM)):
                    la=frobR(BR[ai],gm[(gi,0)])
                    if la==0: continue
                    lb=frobR(BR[bi],gm[(gi,1)])
                    if lb==0: continue
                    lc=frobR(BR[ci],gm[(gi,2)])
                    if lc==0: continue
                    orb += la*lb*lc
                if orb==0: obs.add((ai,bi,ci))
    return obs

def residual(ai,bi,ci):
    A,B,C=BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()

# Compute the 6 obstructed sets and intersect them.
obs_sets={}
for name,g,orb in CATALOG:
    obs_sets[name]=orbit_obstructed_set(g)
    print(f"{name}: {len(obs_sets[name])} obstructed")

common = set(range(9*9*9))  # placeholder; build intersection properly
common = None
for name in obs_sets:
    s = obs_sets[name]
    common = s if common is None else (common & s)
print(f"\nCOMMON obstructed (all 6 orbit types): {len(common)} of 729")

# Among the common-obstructed triples, which have NONZERO MM residual?
# These are killers that NO multiset of catalog orbits can satisfy.
common_killers = [(ai,bi,ci) for (ai,bi,ci) in common if residual(ai,bi,ci)!=0]
print(f"COMMON-KILLER triples (obstructed for all + residual!=0): {len(common_killers)}")

# Show a few, with the canonical (id,box_x,box_x)=(0,1,1) check.
for t in sorted(common_killers)[:10]:
    ai,bi,ci=t
    print(f"  ({ai},{bi},{ci})=({NAMES[ai]},{NAMES[bi]},{NAMES[ci]}): residual={residual(ai,bi,ci)}")

canonical=(0,1,1)
print(f"\nCanonical box-box triple (id,box_x,box_x)=(0,1,1):")
print(f"  in COMMON obstructed set: {canonical in common}")
print(f"  residual: {residual(*canonical)}")

# Verdict logic.
if len(common_killers)>0:
    print("\nVERDICT Family 1 (>=3 orbits S_4): PRE-SCREEN-DEAD")
    print(f"  {len(common_killers)} triples are obstructed for every catalog orbit type")
    print(f"  yet carry nonzero MM residual. Adding any number of these orbits keeps")
    print(f"  the contribution identically zero there => constant generator => unit ideal.")
else:
    print("\nVERDICT Family 1: SURVIVES pre-screen -- a third orbit can reach the obstructed directions; build the probe.")
