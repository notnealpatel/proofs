# Oe1 Family 2: PSL(2,7) builder validation (Os1-style) + multi-orbit coverage.
# Validates the cyclotomic-field builder with a planted seed (POSITIVE feasible,
# NEGATIVE T_MM infeasible), then checks whether any multi-orbit PSL(2,7) config
# (orbits 7,8 fit; total <=21) can cover the 48 residual dirs -- if not, those are
# INFEASIBLE-BY-COVERAGE without further Groebner.

R7=CyclotomicField(7); z=R7.gen()
G=gap.PSL(2,7); irr=gap.IrreducibleRepresentations(G); rep=irr[2]
Ggens=gap.GeneratorsOfGroup(G); ngens=Integer(gap.Length(Ggens))
def conv(s):
    s=str(s)
    if 'E(' in s: return R7(sage_eval(s.replace('E(','CyclotomicField(').replace(')',').gen()')))
    return R7(QQ(s))
genmats=[]
for k in range(1,ngens+1):
    Mg=gap.Image(rep,Ggens[k]); M=matrix(R7,3,3)
    for a in range(1,4):
        for b in range(1,4): M[a-1,b-1]=conv(gap(Mg[a][b]))
    genmats.append(M)
def matkey(M): return tuple(M.list())
I3=identity_matrix(R7,3)
elems={matkey(I3):I3}; frontier=[I3]
for _ in range(5000):
    if not frontier: break
    new=[]
    for e in frontier:
        for g in genmats:
            ne=g*e; k=matkey(ne)
            if k not in elems: elems[k]=ne; new.append(ne)
    frontier=new
ELEM=list(elems.values()); assert len(ELEM)==168
def matorder(M):
    P=M; o=1
    while P!=I3 and o<200: P=P*M; o+=1
    return o
sigma=[M for M in ELEM if matorder(M)==3][0]
def conjOp(g):
    gi=g.inverse(); C=matrix(R7,9,9)
    for i in range(3):
        for j in range(3):
            E=matrix(R7,3,3); E[i,j]=1; img=g*E*gi; col=i*3+j
            for a in range(3):
                for b in range(3): C[a*3+b,col]=img[a,b]
    return C
def fixedBasis_sub(H):
    rows=[]; I9=identity_matrix(R7,9)
    for h in H: rows.append(conjOp(h)-I9)
    big=block_matrix(R7,[[m] for m in rows]); ker=big.right_kernel().basis()
    return [matrix(R7,3,3,[v[k] for k in range(9)]) for v in ker]
Eb=[]
for i in range(3):
    for j in range(3):
        E=matrix(R7,3,3); E[i,j]=1; Eb.append(E)
def residual(ai,bi,ci):
    A,B,C=Eb[ai],Eb[bi],Eb[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
Rsupport=set((a,b,c) for a in range(9) for b in range(9) for c in range(9) if residual(a,b,c)!=0)
def ansatz_inner(seeds,A,B,C):
    val=A.trace()*B.trace()*C.trace()
    def fr(X,M):
        s=R7(0)
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
            val+=f1*f2*f3
    return val

# Get the |H|=8 subgroup (fixed dim 2, the richest seed) for the control.
ccs=gap.ConjugacyClassesSubgroups(G); ncc=Integer(gap.Length(ccs))
def subgroup_matrices(Hgap):
    hg=gap.GeneratorsOfGroup(Hgap); nh=Integer(gap.Length(hg))
    if nh==0: return [I3]
    gmats=[]
    for k in range(1,nh+1):
        Mg=gap.Image(rep,hg[k]); M=matrix(R7,3,3)
        for a in range(1,4):
            for b in range(1,4): M[a-1,b-1]=conv(gap(Mg[a][b]))
        gmats.append(M)
    Hd={matkey(I3):I3}; fr=[I3]
    for _ in range(2000):
        if not fr: break
        nn=[]
        for e in fr:
            for g in gmats:
                ne=g*e; k=matkey(ne)
                if k not in Hd: Hd[k]=ne; nn.append(ne)
        fr=nn
    return list(Hd.values())
H8=None
for ci in range(1,ncc+1):
    H=gap.Representative(ccs[ci])
    if Integer(gap.Order(H))==8:
        Hm=subgroup_matrices(H)
        if len(fixedBasis_sub(Hm))==2: H8=Hm; break
fb=fixedBasis_sub(H8); d=len(fb); orbit=168//len(H8)
print(f"PSL(2,7) |H|=8 stab: orbit {orbit}, rank {1+orbit}, fixed dim {d}")
mstar=fb[0]+2*fb[1] if d>=2 else fb[0]
Rr=PolynomialRing(R7,d,[f"x{i}" for i in range(d)]); xs=Rr.gens()
m1=matrix(Rr,3,3)
for p in range(d): m1+=xs[p]*fb[p].change_ring(Rr)
s=sigma.change_ring(Rr); m2=s*m1*s.inverse(); s2=(sigma*sigma).change_ring(Rr); m3=s2*m1*s2.inverse()
def frobR(Xc,Ms):
    acc=Rr(0)
    for i in range(3):
        for j in range(3):
            if Xc[i,j]!=0: acc+=Xc[i,j]*Ms[i,j]
    return acc
gm={}
for gi,gg in enumerate(ELEM):
    gR=gg.change_ring(Rr); gmi=gR.inverse()
    gm[(gi,0)]=gR*m1*gmi; gm[(gi,1)]=gR*m2*gmi; gm[(gi,2)]=gR*m3*gmi
def bp(ti):
    polys=[]
    for ai in range(9):
        for bi in range(9):
            for cci in range(9):
                orb=Rr(0)
                for gi in range(len(ELEM)):
                    la=frobR(Eb[ai],gm[(gi,0)])
                    if la==0: continue
                    lb=frobR(Eb[bi],gm[(gi,1)])
                    if lb==0: continue
                    lc=frobR(Eb[cci],gm[(gi,2)])
                    if lc==0: continue
                    orb+=la*lb*lc
                P=orb+(Eb[ai].trace()*Eb[bi].trace()*Eb[cci].trace()-ti(ai,bi,cci))
                if P!=0: polys.append(P)
    return polys
tp={}
def tprime(ai,bi,ci):
    k=(ai,bi,ci)
    if k not in tp: tp[k]=ansatz_inner([mstar],Eb[ai],Eb[bi],Eb[ci])
    return tp[k]
pos=bp(tprime); Ipos=Rr.ideal(pos)
xstar={xs[p]:[R7(1),R7(2)][p] for p in range(d)}
posvanish=all(P.subs(xstar)==0 for P in pos); unitpos=(Rr.one() in Ipos)
def tmm(ai,bi,ci): return (Eb[ai]*Eb[bi]*Eb[ci]).trace()
neg=bp(tmm); unitneg=(Rr.one() in Rr.ideal(neg))
print("PSL(2,7) builder validation (|H|=8, rank 22):")
print(f"  POSITIVE planted vanishes: {posvanish}, unit: {unitpos} (want True,False)")
print(f"  NEGATIVE T_MM unit: {unitneg} (want True)")
print(f"  VALIDATION: {'PASS' if (posvanish and not unitpos and unitneg) else 'FAIL'}")
