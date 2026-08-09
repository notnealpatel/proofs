# Oe1 Family 2: multi-orbit OCTAHEDRAL ROTATION group O sweep (rank<=22). O ~ S_4
# but realized as pure rotations; rho (x) rho* is the SAME as T_d (sign cancels in
# rho' (x) rho'*), so this should mirror S_4's all-infeasible -- verify directly
# since the fixed-space BASES (not just dims) could differ.
import json, itertools
K.<r3>=QuadraticField(3)
def Mt(rows): return matrix(K,rows)
g4=Mt([[0,-1,0],[1,0,0],[0,0,1]]); g3=Mt([[0,0,1],[1,0,0],[0,1,0]])
def matkey(M): return tuple(M.list())
I3=identity_matrix(K,3)
elems={matkey(I3):I3}; frontier=[I3]
for _ in range(500):
    if not frontier: break
    new=[]
    for e in frontier:
        for g in [g4,g3]:
            ne=g*e; k=matkey(ne)
            if k not in elems: elems[k]=ne; new.append(ne)
    frontier=new
ELEM=list(elems.values()); assert len(ELEM)==24
sigma=g3
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
def cyclic(g):
    H=[I3]; P=g
    while P!=I3: H.append(P); P=P*g
    return H
def subgroup(gens):
    H={matkey(I3):I3}; fr=[I3]
    while fr:
        nn=[]
        for e in fr:
            for g in gens:
                ne=g*e; k=matkey(ne)
                if k not in H: H[k]=ne; nn.append(ne)
        fr=nn
    return list(H.values())
def fixedBasis_sub(H):
    rows=[]; I9=identity_matrix(K,9)
    for h in H: rows.append(conjOp(h)-I9)
    big=block_matrix(K,[[m] for m in rows]); ker=big.right_kernel().basis()
    return [matrix(K,3,3,[v[k] for k in range(9)]) for v in ker]
Eb=[]
for i in range(3):
    for j in range(3):
        E=matrix(K,3,3); E[i,j]=1; Eb.append(E)
def residual(ai,bi,ci):
    A,B,C=Eb[ai],Eb[bi],Eb[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
Rsupport=set((a,b,c) for a in range(9) for b in range(9) for c in range(9) if residual(a,b,c)!=0)

# O stabilizer types by order: Z_4(orbit6,dim3), Z_3(orbit8,dim3), Z_2(orbit12,dim5).
# Distinct conjugacy of order-2: O has 9 order-2 elements -> two classes (face-2fold
# vs edge-2fold). Take cyclic reps. Build catalog of types.
Z4=cyclic([g for g in ELEM if matorder(g)==4][0])
Z3=cyclic([g for g in ELEM if matorder(g)==3][0])
# two order-2 classes: pick elements with distinct fixed-dim
ord2=[g for g in ELEM if matorder(g)==2]
z2types=[]
for g in ord2:
    H=cyclic(g); fd=len(fixedBasis_sub(H))
    key=fd
    if key not in [t[0] for t in z2types]:
        z2types.append((fd,H))
CAT=[("Z_4",Z4,6,len(fixedBasis_sub(Z4)))]
CAT.append(("Z_3",Z3,8,len(fixedBasis_sub(Z3))))
for idx,(fd,H) in enumerate(z2types):
    CAT.append((f"Z_2_{fd}",H,12,fd))
fbs={name:fixedBasis_sub(H) for (name,H,orb,fd) in CAT}
orbsz={name:orb for (name,H,orb,fd) in CAT}
fdim={name:fd for (name,H,orb,fd) in CAT}
print("O catalog:", [(n,orbsz[n],fdim[n]) for n in [c[0] for c in CAT]])

names=[c[0] for c in CAT]
def enum(maxtot,maxvars):
    out=[]
    def rec(start,cur,tot,nv):
        if len(cur)>=1 and nv<=maxvars: out.append(list(cur))
        for i in range(start,len(names)):
            if tot+orbsz[names[i]]<=maxtot and nv+fdim[names[i]]<=maxvars:
                rec(i,cur+[names[i]],tot+orbsz[names[i]],nv+fdim[names[i]])
    rec(0,[],0,0)
    return out
cfgs=enum(21,11)
print(f"O configs (total<=21, <=11 vars): {len(cfgs)}")
def build_solve(cfg):
    nv=sum(fdim[n] for n in cfg)
    Rr=PolynomialRing(K,nv,[f"x{i}" for i in range(nv)]); xv=Rr.gens()
    seeds=[]; off=0
    for n in cfg:
        fb=fbs[n]; d=fdim[n]
        mm=matrix(Rr,3,3)
        for p in range(d): mm+=xv[off+p]*fb[p].change_ring(Rr)
        ss=sigma.change_ring(Rr); mm2=ss*mm*ss.inverse(); ss2=(sigma*sigma).change_ring(Rr); mm3=ss2*mm*ss2.inverse()
        seeds.append((mm,mm2,mm3)); off+=d
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
                for (mm,mm2,mm3) in seeds:
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
    I=Rr.ideal(polys); unit=(Rr.one() in I)
    return unit, (None if unit else I.dimension())
sols=[]
for cfg in cfgs:
    unit,dim=build_solve(cfg); tot=sum(orbsz[n] for n in cfg)
    if unit:
        print(f"  {'+'.join(cfg):18s} rank {1+tot:2d}: INFEASIBLE")
    else:
        print(f"  {'+'.join(cfg):18s} rank {1+tot:2d}: SOLUTION-FOUND dim {dim} *** STOP ***")
        sols.append((cfg,tot,dim))
print(f"\nO SOLUTION-FOUND (rank<23): {len(sols)}")
