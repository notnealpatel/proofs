# Oe1 Family 3 pre-screen: RELAXING the sigma-twist coupling.
#
# GM's ansatz (1612.01527 eq z3orbit, line 250) couples m2=sigma m1 sigma^-1,
# m3=sigma^2 m1 sigma^-2. This makes the ansatz Z_3-symmetric (invariant under
# cyclic rotation of the 3 tensor factors), matching the MM tensor's own Z_3
# symmetry. Relaxing it means independent m1,m2,m3, each free in the H-fixed
# space: 3x the parameters per orbit, but loses the cyclic guarantee.
#
# The decisive question for beating Laderman: does decoupling ENLARGE the set of
# residual directions a single orbit can reach? If decoupled per-orbit reach
# still cannot cover the 137 residual triples within rank<=22, Family 3 is dead
# by the SAME coverage wall. We compute, per catalog orbit type, the reach set of
# the DECOUPLED construction (m1,m2,m3 independent fixed-space seeds) and compare
# to the twisted reach.
#
# NOTE on rank: decoupling does NOT change the tensor rank. Each orbit still
# contributes |orbit| = 24/|H| rank-1 terms (the orbit of m1 (x) m2 (x) m3 under
# diagonal conjugation), regardless of whether m1,m2,m3 are twist-coupled. So the
# rank budget (total orbit <= 21) is identical; only the reachable directions
# can differ.

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

def residual(t):
    ai,bi,ci=t; A,B,C=BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
Rsupport=set(t for t in [(a,b,c) for a in range(9) for b in range(9) for c in range(9)] if residual(t)!=0)

def decoupled_reach(gp):
    """Reach set for DECOUPLED m1,m2,m3 (independent fixed-space seeds). Each
    seed gets its own variable block; orbit term is sum_g <A,g m1 g^-1><B,g m2
    g^-1><C,g m3 g^-1>, a trilinear form. Reachable iff this poly is not
    identically zero. With independent m1,m2,m3, the trilinear form is nonzero
    iff there EXIST seeds making it nonzero -- i.e. the bilinear/trilinear
    structure is nondegenerate on (fixed_A, fixed_B, fixed_C). We test by
    symbolic non-vanishing over 3d variables."""
    fb,hord=fixedBasis(gp); d=len(fb)
    # variables: m1 -> x0..x{d-1}, m2 -> y, m3 -> z
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
    return reach, d, hord

# Also recompute twisted reach for direct comparison.
def twisted_reach(gp):
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
    for gi,gg in enumerate(ELEM):
        gR=gg.change_ring(R); gm[(gi,0)]=gR*m1*gR.transpose(); gm[(gi,1)]=gR*m2*gR.transpose(); gm[(gi,2)]=gR*m3*gR.transpose()
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

print(f"residual support |R|={len(Rsupport)}")
print("type  | twisted_reach | decoupled_reach | dec covers of R | orbit")
dec={}; orbsz={}
for name,gp,orb in CATALOG:
    tw = twisted_reach(gp)
    dr,d,hord = decoupled_reach(gp)
    dec[name]=dr; orbsz[name]=orb
    print(f"{name:5s} | {len(tw):3d}           | {len(dr):3d}             | {len(dr & Rsupport):3d}/{len(Rsupport)}        | {orb}")

# Decoupled coverage wall: cheapest distinct-type-set covering R, by min orbit.
import itertools
names=[c[0] for c in CATALOG]
covering=[]
for r in range(1,len(names)+1):
    for combo in itertools.combinations(names,r):
        u=set().union(*[dec[c] for c in combo])
        if Rsupport.issubset(u):
            covering.append((combo,sum(orbsz[c] for c in combo)))
covering.sort(key=lambda x:x[1])
print("\nDECOUPLED cheapest covering type-sets (by min total orbit):")
for combo,mo in covering[:8]:
    flag="  <=21 CANDIDATE" if mo<=21 else "  >21 over budget"
    print(f"  {'+'.join(combo):28s} min_orbit={mo:2d} rank={1+mo}{flag}")
cand=[(c,mo) for (c,mo) in covering if mo<=21]
print(f"\nDecoupled type-sets covering R within rank<=22: {len(cand)}")
if not cand:
    print("=> Family 3 (sigma-twist relaxed) PRE-SCREEN-DEAD: even decoupled, no rank<=22 config covers R.")
else:
    print("=> Family 3 SURVIVES: a decoupled config covers R within budget; build the probe.")
    for c,mo in cand: print(f"     candidate {'+'.join(c)} rank {1+mo}")
