# Oe1 Family 2: EFFICIENT multi-orbit A_4 sweep. Precompute each orbit type's
# symbolic orbit-sum contribution per triple ONCE (in a shared ring with disjoint
# variable blocks for up to maxorbits orbits), then for each config just SUM the
# precomputed contributions of its orbits and solve. Avoids rebuilding 729
# trilinear sums per config.
#
# A_4 INFEASIBLE single-orbit (all types) already shown. This rules out the
# multi-orbit configs (total orbit <= 21) the same way.

import json, itertools
K=QQ
def Mt(rows): return matrix(K,rows)
rho_12=Mt([[0,1,0],[1,0,0],[0,0,1]]); rho_23=Mt([[1,0,0],[0,0,1],[0,1,0]])
rho_34=Mt([[0,-1,0],[-1,0,0],[0,0,1]]); sigma=Mt([[0,0,1],[1,0,0],[0,1,0]])
def matkey(M): return tuple(M.list())
I3=identity_matrix(K,3); r1234=rho_12*rho_34
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

Z3=cyclic([g for g in ELEM if matorder(g)==3][0])
Z2=cyclic([g for g in ELEM if matorder(g)==2][0])
V4=[M for M in ELEM if matorder(M)<=2]
CAT=[("Z_3",Z3,4,3),("V_4",V4,3,3),("Z_2",Z2,6,5),("Z_1",[I3],12,9)]  # name,H,orbit,fdim
fbs={name:fixedBasis_sub(H) for (name,H,orb,fd) in CAT}
orbsz={name:orb for (name,H,orb,fd) in CAT}
fdim={name:fd for (name,H,orb,fd) in CAT}

# Decide config list: multisets of types, total orbit<=21, >=2 orbits (single done).
# Cap total vars to keep Groebner feasible: skip configs with > 12 vars.
names=[c[0] for c in CAT]
def enum(maxtot,minorb,maxvars):
    out=[]
    def rec(start,cur,tot,nv):
        if len(cur)>=minorb and nv<=maxvars: out.append(list(cur))
        for i in range(start,len(names)):
            if tot+orbsz[names[i]]<=maxtot and nv+fdim[names[i]]<=maxvars:
                rec(i,cur+[names[i]],tot+orbsz[names[i]],nv+fdim[names[i]])
    rec(0,[],0,0)
    return out
cfgs=enum(21,2,12)
print(f"multi-orbit A_4 configs (>=2 orbits, <=21 orbit, <=12 vars): {len(cfgs)}")
for c in cfgs: print("   ", "+".join(c), "rank", 1+sum(orbsz[n] for n in c), "vars", sum(fdim[n] for n in c))

def build_solve(cfg):
    nv=sum(fdim[n] for n in cfg)
    Rr=PolynomialRing(K,nv,[f"x{i}" for i in range(nv)])
    xv=Rr.gens()
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
    unit,dim=build_solve(cfg)
    tot=sum(orbsz[n] for n in cfg)
    if unit:
        print(f"  {'+'.join(cfg):16s} rank {1+tot:2d}: INFEASIBLE (unit ideal)")
    else:
        print(f"  {'+'.join(cfg):16s} rank {1+tot:2d}: SOLUTION-FOUND dim {dim} *** STOP ***")
        sols.append((cfg,tot,dim))
print(f"\nmulti-orbit A_4 SOLUTION-FOUND (rank<23): {len(sols)}")
