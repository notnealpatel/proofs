# Oe1 Family 1 STRUCTURAL pre-screen via direction coverage.
#
# Each orbit type H reaches a FIXED set of basis-triple directions (those where
# its symbolic orbit-sum is not identically zero). Stacking multiple orbits of
# the SAME type does NOT enlarge this set -- it only adds parameters in the same
# directions. So a multi-orbit config can satisfy the MM constraints only if the
# UNION of its orbit types' reachable sets covers every triple with nonzero
# required residual (else that triple is a constant generator => unit ideal).
#
# There are 137 nonzero-residual triples (matches Or2's "137 constraint polys").
# Necessary condition for ANY config: union of reachable sets >= the 137.
# We compute reach(H) per catalog type, find the residual-support R (137 triples),
# and report which single types / unions cover R. A config whose union misses
# even one triple in R is INFEASIBLE by a constant generator, regardless of rank.
#
# NOTE: coverage is NECESSARY, not sufficient (covering all directions does not
# mean the nonlinear system is solvable). A config that PASSES coverage still
# needs the Groebner probe. A config that FAILS coverage is provably dead.

import json
K.<r3> = QuadraticField(3)
def Mt(rows): return matrix(K, rows)
rho_12=Mt([[0,1,0],[1,0,0],[0,0,1]]); rho_23=Mt([[1,0,0],[0,0,1],[0,1,0]])
rho_34=Mt([[0,-1,0],[-1,0,0],[0,0,1]]); sigma=Mt([[0,0,1],[1,0,0],[0,1,0]])
gens={(1,0,2,3):rho_12,(0,2,1,3):rho_23,(0,1,3,2):rho_34}
def compose(p,q): return tuple(p[q[i]] for i in range(4))
ident=(0,1,2,3); elems={ident:identity_matrix(K,3)}; frontier=[ident]
for _ in range(100):
    if not frontier: break
    new=[]
    for e in frontier:
        for gp in gens:
            ne=compose(gp,e)
            if ne not in elems: elems[ne]=gens[gp]*elems[e]; new.append(ne)
    frontier=new
ELEM=list(elems.values())
def conjM(g,X): return g*X*g.transpose()
def rrStarBasis():
    idm=identity_matrix(K,3); boxX=diagonal_matrix(K,[1,-1/2,-1/2]); boxY=diagonal_matrix(K,[0,r3/2,-r3/2])
    def E(p):
        M=matrix(K,3,3)
        for (i,j,v) in p: M[i,j]=v
        return M
    s1=E([(1,2,1),(2,1,1)]); s2=E([(0,2,1),(2,0,1)]); s3=E([(0,1,1),(1,0,1)])
    a1=E([(1,2,1),(2,1,-1)]); a2=E([(0,2,-1),(2,0,1)]); a3=E([(0,1,1),(1,0,-1)])
    return [idm,boxX,boxY,s1,s2,s3,a1,a2,a3]
BR=rrStarBasis(); NAMES=["id","box_x","box_y","s1","s2","s3","a1","a2","a3"]
def subgroup(gp):
    H={ident}; fr=[ident]
    while fr:
        nn=[]
        for e in fr:
            for g in gp:
                ne=compose(g,e)
                if ne not in H: H.add(ne); nn.append(ne)
        fr=nn
    return H
def conjOperator(g):
    C=matrix(K,9,9)
    for i in range(3):
        for j in range(3):
            E=matrix(K,3,3); E[i,j]=1; img=conjM(elems[g],E); col=i*3+j
            for a in range(3):
                for b in range(3): C[a*3+b,col]=img[a,b]
    return C
def fixedBasis(gp):
    H=subgroup(gp); rows=[]; I9=identity_matrix(K,9)
    for h in H: rows.append(conjOperator(h)-I9)
    big=block_matrix(K,[[m] for m in rows]); ker=big.right_kernel().basis()
    return [matrix(K,3,3,[v[k] for k in range(9)]) for v in ker], len(H)

S3=[(0,2,1,3),(0,1,3,2)]; K4=[(1,0,3,2),(2,3,0,1)]; Z4=[(1,2,3,0)]
Z3=[(1,2,0,3)]; Z2t=[(1,0,2,3)]; Z2d=[(1,0,3,2)]
CATALOG=[("S_3",S3,4),("K_4",K4,6),("Z_4",Z4,6),("Z_3",Z3,8),("Z_2t",Z2t,12),("Z_2d",Z2d,12)]

def reach_set(gp):
    """Set of triple-indices (ai,bi,ci) where one orbit of this type has a
    NONZERO symbolic orbit-sum (i.e. reachable directions)."""
    fb,hord=fixedBasis(gp); d=len(fb)
    R=PolynomialRing(K, d, [f"x{i}" for i in range(d)] if d>0 else ["x0"])
    xs=R.gens(); m1=matrix(R,3,3)
    for p in range(d): m1 += xs[p]*fb[p].change_ring(R)
    s=sigma.change_ring(R); m2=s*m1*s.transpose(); s2=(sigma*sigma).change_ring(R); m3=s2*m1*s2.transpose()
    def frobR(Xc,Ms):
        acc=R(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc += Xc[i,j]*Ms[i,j]
        return acc
    gm={}
    for gi,g in enumerate(ELEM):
        gR=g.change_ring(R); gm[(gi,0)]=gR*m1*gR.transpose(); gm[(gi,1)]=gR*m2*gR.transpose(); gm[(gi,2)]=gR*m3*gR.transpose()
    reach=set()
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
                if orb!=0: reach.add((ai,bi,ci))
    return reach, d, hord

def residual(t):
    ai,bi,ci=t; A,B,C=BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()

# Residual support R: triples with nonzero MM residual.
Rsupport = set(t for t in [(a,b,c) for a in range(9) for b in range(9) for c in range(9)] if residual(t)!=0)
print(f"Residual support |R| = {len(Rsupport)} (nonzero required residual triples)")

reach={}; dims={}; orbsz={}
for name,g,orb in CATALOG:
    rs,d,hord = reach_set(g)
    reach[name]=rs; dims[name]=d; orbsz[name]=orb
    covered = len(rs & Rsupport)
    print(f"{name:5s} orbit={orb:2d} dim={d}: reaches {len(rs):3d} dirs, covers {covered:3d}/{len(Rsupport)} of R; MISSES {len(Rsupport-rs)}")

# Which residual triples does NO catalog orbit reach? (Union of all reach sets.)
union_all = set().union(*reach.values())
intrinsically_missed = Rsupport - union_all
print(f"\nResidual triples reached by NO catalog orbit: {len(intrinsically_missed)}")
if intrinsically_missed:
    print("  -> even the union of ALL catalog types cannot cover R => Family 1 PRE-SCREEN-DEAD (coverage).")
    for t in sorted(intrinsically_missed)[:10]:
        print(f"     missed {t}=({NAMES[t[0]]},{NAMES[t[1]]},{NAMES[t[2]]}) residual={residual(t)}")
else:
    print("  -> union of all catalog types covers R; coverage alone does not kill Family 1.")
    print("     Now check which SPECIFIC configs (rank<=22) cover R.")
