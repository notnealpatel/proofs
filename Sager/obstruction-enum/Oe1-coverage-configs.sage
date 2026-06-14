# Oe1 Family 1: enumerate which TYPE-SETS cover the 137 residual directions, and
# for each covering set find the minimum total orbit size achievable with rank
# <=22. Coverage by a config depends only on the SET of distinct stabilizer types
# present (same-type stacking does not enlarge reach). A config whose type-union
# misses any residual triple is INFEASIBLE (constant generator). Only configs
# whose type-set covers R need the Groebner probe.
#
# Reuse reach sets computed previously by recomputing them here (self-contained).

import json, itertools
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
    fb,hord=fixedBasis(gp); d=len(fb)
    R=PolynomialRing(K, d, [f"x{i}" for i in range(d)] if d>0 else ["x0"]); xs=R.gens()
    m1=matrix(R,3,3)
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
    return reach
def residual(t):
    ai,bi,ci=t; A,B,C=BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()

Rsupport=set(t for t in [(a,b,c) for a in range(9) for b in range(9) for c in range(9)] if residual(t)!=0)
reach={}; orbsz={}
for name,g,orb in CATALOG:
    reach[name]=reach_set(g); orbsz[name]=orb

names=[c[0] for c in CATALOG]
# All nonempty subsets of distinct types: does the union cover R? min orbit to
# realize that type-set = sum of one orbit of each type in the set (the cheapest
# way to include a type at least once). Multi-orbit-of-a-type only adds rank.
print("type-set                         | covers R? | min_total_orbit | min_rank")
covering=[]
for r in range(1,len(names)+1):
    for combo in itertools.combinations(names, r):
        u=set().union(*[reach[c] for c in combo])
        covers = Rsupport.issubset(u)
        min_orbit = sum(orbsz[c] for c in combo)
        if covers:
            covering.append((combo,min_orbit))
        if covers and min_orbit<=21:
            print(f"{'+'.join(combo):32s} | YES       | {min_orbit:2d}              | {1+min_orbit}  <= 22  CANDIDATE")
print()
# Minimum-rank covering type-set overall (ignoring rank cap), to see the wall.
covering.sort(key=lambda x:x[1])
print("Cheapest covering type-sets (by min total orbit):")
for combo,mo in covering[:12]:
    flag = "  <=21 OK" if mo<=21 else "  > 21 (over budget)"
    print(f"  {'+'.join(combo):32s} min_orbit={mo:2d} rank={1+mo}{flag}")

candidates=[(c,mo) for (c,mo) in covering if mo<=21]
print(f"\nNumber of distinct-type-sets that cover R within rank<=22: {len(candidates)}")
if not candidates:
    print("=> NO type-set covers R within rank<=22 => Family 1 PRE-SCREEN-DEAD (coverage wall).")
else:
    print("=> Some type-sets cover R within budget; these need the Groebner probe.")
