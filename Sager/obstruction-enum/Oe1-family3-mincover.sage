# Oe1 Family 3 follow-up: the cheapest-covering list came back EMPTY for the
# decoupled construction. That could mean (a) no type-set covers R even unbounded,
# or (b) the smallest covering rank is just > 21. Pin it down: compute the union
# of ALL decoupled type reach sets (does it cover R?), and the minimum covering
# rank. Also report WHICH 6 residual directions decoupled Z_2t (best single,
# 131/137) misses, and whether ANY decoupled orbit reaches them -- the true wall.

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
def residual(t):
    ai,bi,ci=t; A,B,C=BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
Rsupport=set(t for t in [(a,b,c) for a in range(9) for b in range(9) for c in range(9)] if residual(t)!=0)
def decoupled_reach(gp):
    fb,hord=fixedBasis(gp); d=len(fb)
    R=PolynomialRing(K, 3*d, [f"x{i}" for i in range(d)]+[f"y{i}" for i in range(d)]+[f"z{i}" for i in range(d)] if d>0 else ["x0"])
    g=R.gens()
    def seed(off):
        M=matrix(R,3,3)
        for p in range(d): M += g[off+p]*fb[p].change_ring(R)
        return M
    m1=seed(0); m2=seed(d); m3=seed(2*d)
    def frobR(Xc,Ms):
        acc=R(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc += Xc[i,j]*Ms[i,j]
        return acc
    gm={}
    for gi,gg in enumerate(ELEM):
        gR=gg.change_ring(R)
        gm[(gi,0)]=gR*m1*gR.transpose(); gm[(gi,1)]=gR*m2*gR.transpose(); gm[(gi,2)]=gR*m3*gR.transpose()
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
dec={}; orbsz={}
for name,gp,orb in CATALOG:
    dec[name]=decoupled_reach(gp); orbsz[name]=orb

union_all=set().union(*dec.values())
print(f"Union of ALL decoupled type reach sets covers R: {Rsupport.issubset(union_all)}")
missed_by_all = Rsupport - union_all
print(f"Residual dirs reached by NO decoupled catalog orbit: {len(missed_by_all)}")
for t in sorted(missed_by_all)[:12]:
    print(f"   {t}=({NAMES[t[0]]},{NAMES[t[1]]},{NAMES[t[2]]}) residual={residual(t)}")

# minimum covering rank over distinct-type-sets (unbounded)
names=[c[0] for c in CATALOG]; covering=[]
for r in range(1,len(names)+1):
    for combo in itertools.combinations(names,r):
        u=set().union(*[dec[c] for c in combo])
        if Rsupport.issubset(u): covering.append((combo,sum(orbsz[c] for c in combo)))
covering.sort(key=lambda x:x[1])
if covering:
    print(f"\nMinimum covering type-set: {'+'.join(covering[0][0])} total orbit {covering[0][1]} rank {1+covering[0][1]}")
else:
    print("\nNO distinct-type-set covers R, even unbounded (decoupled).")

# What does Z_2t miss, and does anything reach those 6?
miss_z2t = Rsupport - dec["Z_2t"]
print(f"\nDecoupled Z_2t (131/137) misses {len(miss_z2t)} residual dirs:")
for t in sorted(miss_z2t):
    reachers=[nm for nm in names if t in dec[nm]]
    print(f"   {t}=({NAMES[t[0]]},{NAMES[t[1]]},{NAMES[t[2]]}) residual={residual(t)} reached by: {reachers}")
