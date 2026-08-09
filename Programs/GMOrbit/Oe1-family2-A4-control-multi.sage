# Oe1 Family 2: A_4 builder validation (Os1-style) + multi-orbit A_4 sweep.
# A_4 orbits are small (3,4,6,12) so multi-orbit configs fit rank<=22. Validate
# the builder with a planted seed, then sweep single- and multi-orbit A_4 configs
# (total orbit <= 21) for any SOLUTION-FOUND (would beat Laderman 23 => STOP).

import json, itertools
K=QQ
def Mt(rows): return matrix(K,rows)
rho_12=Mt([[0,1,0],[1,0,0],[0,0,1]]); rho_23=Mt([[1,0,0],[0,0,1],[0,1,0]])
rho_34=Mt([[0,-1,0],[-1,0,0],[0,0,1]]); sigma=Mt([[0,0,1],[1,0,0],[0,1,0]])
def matkey(M): return tuple(M.list())
I3=identity_matrix(K,3)
r1234=rho_12*rho_34
A4d={matkey(I3):I3}; fr=[I3]
for _ in range(200):
    if not fr: break
    new=[]
    for e in fr:
        for g in [sigma,r1234]:
            ne=g*e; k=matkey(ne)
            if k not in A4d: A4d[k]=ne; new.append(ne)
    fr=new
ELEM=list(A4d.values()); assert len(ELEM)==12
def matorder(M):
    P=M; o=1
    while P!=I3 and o<50: P=P*M; o+=1
    return o
def conjOp(g):
    gi=g.inverse(); C=matrix(K,9,9)
    for i in range(3):
        for j in range(3):
            E=matrix(K,3,3); E[i,j]=1; img=g*E*gi; col=i*3+j
            for a in range(3):
                for b in range(3): C[a*3+b,col]=img[a,b]
    return C
def fixedBasis_sub(H):
    rows=[]; I9=identity_matrix(K,9)
    for h in H: rows.append(conjOp(h)-I9)
    big=block_matrix(K,[[m] for m in rows]); ker=big.right_kernel().basis()
    return [matrix(K,3,3,[v[k] for k in range(9)]) for v in ker]
def cyclic(g):
    H=[I3]; P=g
    while P!=I3: H.append(P); P=P*g
    return H
Eb=[]
for i in range(3):
    for j in range(3):
        E=matrix(K,3,3); E[i,j]=1; Eb.append(E)
def residual(ai,bi,ci):
    A,B,C=Eb[ai],Eb[bi],Eb[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()

def ansatz_inner(seeds, A,B,C):  # concrete, multi-orbit
    val=A.trace()*B.trace()*C.trace()
    def fr(X,M):
        s=K(0)
        for i in range(3):
            for j in range(3): s+=X[i,j]*M[i,j]
        return s
    for m1 in seeds:
        m2=sigma*m1*sigma.inverse(); m3=sigma*sigma*m1*(sigma.inverse())**2
        for g in ELEM:
            gi=g.inverse()
            f1=fr(A,g*m1*gi)
            if f1==0: continue
            f2=fr(B,g*m2*gi)
            if f2==0: continue
            f3=fr(C,g*m3*gi)
            if f3==0: continue
            val += f1*f2*f3
    return val

# catalog of A_4 stabilizer types
Z3=cyclic([g for g in ELEM if matorder(g)==3][0])
Z2=cyclic([g for g in ELEM if matorder(g)==2][0])
V4=[M for M in ELEM if matorder(M)<=2]
CAT=[("Z_3",Z3,4),("Z_2",Z2,6),("V_4",V4,3),("Z_1",[I3],12)]
fbs={name:fixedBasis_sub(H) for (name,H,orb) in CAT}

# --- builder validation (Os1-style) using Z_3 orbit (orbit4, rank5) ---
fbz3=fbs["Z_3"]; d=len(fbz3)
mstar=fbz3[0]+2*fbz3[1]-fbz3[2]
R=PolynomialRing(K,d,[f"x{i}" for i in range(d)]); xs=R.gens()
m1=matrix(R,3,3)
for p in range(d): m1+=xs[p]*fbz3[p].change_ring(R)
s=sigma.change_ring(R); m2=s*m1*s.inverse(); s2=(sigma*sigma).change_ring(R); m3=s2*m1*s2.inverse()
def frobR(Xc,Ms):
    acc=R(0)
    for i in range(3):
        for j in range(3):
            if Xc[i,j]!=0: acc+=Xc[i,j]*Ms[i,j]
    return acc
gm={}
for gi,gg in enumerate(ELEM):
    gR=gg.change_ring(R); gmi=gR.inverse()
    gm[(gi,0)]=gR*m1*gmi; gm[(gi,1)]=gR*m2*gmi; gm[(gi,2)]=gR*m3*gmi
def build_polys_single(targetInner):
    polys=[]
    for ai in range(9):
        for bi in range(9):
            for ci in range(9):
                orb=R(0)
                for gi in range(len(ELEM)):
                    la=frobR(Eb[ai],gm[(gi,0)])
                    if la==0: continue
                    lb=frobR(Eb[bi],gm[(gi,1)])
                    if lb==0: continue
                    lc=frobR(Eb[ci],gm[(gi,2)])
                    if lc==0: continue
                    orb += la*lb*lc
                P=orb+(Eb[ai].trace()*Eb[bi].trace()*Eb[ci].trace()-targetInner(ai,bi,ci))
                if P!=0: polys.append(P)
    return polys
tp={}
def tprime(ai,bi,ci):
    k=(ai,bi,ci)
    if k not in tp: tp[k]=ansatz_inner([mstar],Eb[ai],Eb[bi],Eb[ci])
    return tp[k]
pos=build_polys_single(tprime); Ipos=R.ideal(pos)
xstar={xs[p]:[K(1),K(2),K(-1)][p] for p in range(d)}
posvanish=all(P.subs(xstar)==0 for P in pos)
unitpos=(R.one() in Ipos)
def tmm(ai,bi,ci): return (Eb[ai]*Eb[bi]*Eb[ci]).trace()
neg=build_polys_single(tmm); Ineg=R.ideal(neg); unitneg=(R.one() in Ineg)
print("A_4 builder validation (Z_3 orbit, rank 5):")
print(f"  POSITIVE planted x* vanishes all: {posvanish}, unit ideal: {unitpos} (want True,False)")
print(f"  NEGATIVE T_MM unit ideal: {unitneg} (want True)")
print(f"  VALIDATION: {'PASS' if (posvanish and not unitpos and unitneg) else 'FAIL'}")

# --- multi-orbit A_4 sweep with coverage + Groebner ---
def reach_single(name):
    fb=fbs[name]; d=len(fb)
    if d==0: return set()
    Rr=PolynomialRing(K,d,[f"x{i}" for i in range(d)]); xv=Rr.gens()
    mm=matrix(Rr,3,3)
    for p in range(d): mm+=xv[p]*fb[p].change_ring(Rr)
    ss=sigma.change_ring(Rr); mm2=ss*mm*ss.inverse(); ss2=(sigma*sigma).change_ring(Rr); mm3=ss2*mm*ss2.inverse()
    def fR(Xc,Ms):
        acc=Rr(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc+=Xc[i,j]*Ms[i,j]
        return acc
    g2={}
    for gi,gg in enumerate(ELEM):
        gR=gg.change_ring(Rr); gmi=gR.inverse()
        g2[(gi,0)]=gR*mm*gmi; g2[(gi,1)]=gR*mm2*gmi; g2[(gi,2)]=gR*mm3*gmi
    reach=set()
    for ai in range(9):
        for bi in range(9):
            for ci in range(9):
                orb=Rr(0)
                for gi in range(len(ELEM)):
                    la=fR(Eb[ai],g2[(gi,0)])
                    if la==0: continue
                    lb=fR(Eb[bi],g2[(gi,1)])
                    if lb==0: continue
                    lc=fR(Eb[ci],g2[(gi,2)])
                    if lc==0: continue
                    orb+=la*lb*lc
                if orb!=0: reach.add((ai,bi,ci))
    return reach
reach={name:reach_single(name) for (name,H,orb) in CAT}
Rsupport=set((a,b,c) for a in range(9) for b in range(9) for c in range(9) if residual(a,b,c)!=0)
orbsz={name:orb for (name,H,orb) in CAT}

# enumerate >=1-orbit A_4 configs total orbit<=21 (multisets of types incl Z_1)
names=[c[0] for c in CAT]
def enum_cfgs(maxtot, minorb):
    out=[]
    def rec(start,cur,tot):
        if len(cur)>=minorb: out.append(list(cur))
        for i in range(start,len(names)):
            if tot+orbsz[names[i]]<=maxtot:
                rec(i,cur+[names[i]],tot+orbsz[names[i]])
    rec(0,[],0)
    return out
cfgs=enum_cfgs(21,1)
print(f"\nA_4 configs (>=1 orbit, total<=21): {len(cfgs)}")
def build_multi_polys(cfg):
    # variables per orbit block
    blocks=[]; nv=0; fbcfg=[]
    for name in cfg:
        fb=fbs[name]; d=len(fb); blocks.append((nv,d)); fbcfg.append(fb); nv+=d
    Rr=PolynomialRing(K,nv,[f"x{i}" for i in range(nv)]) if nv>0 else PolynomialRing(K,1,["x0"])
    xv=Rr.gens()
    seedsR=[]
    for (off,d),fb in zip(blocks,fbcfg):
        mm=matrix(Rr,3,3)
        for p in range(d): mm+=xv[off+p]*fb[p].change_ring(Rr)
        ss=sigma.change_ring(Rr); mm2=ss*mm*ss.inverse(); ss2=(sigma*sigma).change_ring(Rr); mm3=ss2*mm*ss2.inverse()
        seedsR.append((mm,mm2,mm3))
    def fR(Xc,Ms):
        acc=Rr(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc+=Xc[i,j]*Ms[i,j]
        return acc
    polys=[]
    for ai in range(9):
        for bi in range(9):
            for ci in range(9):
                orb=Rr(0)
                for (mm,mm2,mm3) in seedsR:
                    for gg in ELEM:
                        gR=gg.change_ring(Rr); gmi=gR.inverse()
                        la=fR(Eb[ai],gR*mm*gmi)
                        if la==0: continue
                        lb=fR(Eb[bi],gR*mm2*gmi)
                        if lb==0: continue
                        lc=fR(Eb[ci],gR*mm3*gmi)
                        if lc==0: continue
                        orb+=la*lb*lc
                P=orb+residual(ai,bi,ci)
                if P!=0: polys.append(P)
    return Rr,polys
sol=[]
for cfg in cfgs:
    # coverage screen on distinct types
    u=set()
    for nm in set(cfg): u|=reach[nm]
    cov=len(u&Rsupport)
    tot=sum(orbsz[nm] for nm in cfg)
    if not Rsupport.issubset(u):
        # infeasible by coverage; skip Groebner
        verdict="INFEASIBLE-BY-COVERAGE"
        print(f"  {'+'.join(cfg):20s} rank {1+tot:2d} cov {cov}/48: {verdict}")
        continue
    Rr,polys=build_multi_polys(cfg)
    I=Rr.ideal(polys); unit=(Rr.one() in I)
    if unit:
        print(f"  {'+'.join(cfg):20s} rank {1+tot:2d} cov {cov}/48: INFEASIBLE (unit ideal)")
    else:
        dim=I.dimension()
        print(f"  {'+'.join(cfg):20s} rank {1+tot:2d} cov {cov}/48: SOLUTION-FOUND dim {dim} *** STOP rank {1+tot} ***")
        sol.append((cfg,tot,dim))
print(f"\nA_4 SOLUTION-FOUND configs (rank<23): {len(sol)}")
for cfg,tot,dim in sol: print(f"  {'+'.join(cfg)} rank {1+tot} dim {dim}")
