# Oe1 Family 2: PSL(2,7) full feasibility. Build the 3-dim irrep (cyclotomic
# field, contains sqrt-7), enumerate subgroups of order >= 8 (=> orbit <= 21),
# compute their conjugation fixed-space dims, and solve the GM sigma-twisted
# single-orbit system over the cyclotomic field. SOLUTION-FOUND rank<23 => STOP.
#
# PSL(2,7) is 2-transitive (not 3-transitive) on 7 points, so GM's clean T_MM
# mechanism (needs 3-transitivity on 4 points) does not apply -- expect INFEASIBLE,
# but VERIFY by Groebner over the correct character field.

R7=CyclotomicField(7); z=R7.gen()
G=gap.PSL(2,7)
irr=gap.IrreducibleRepresentations(G)
# 3-dim irrep index 2
rep=irr[2]
Ggens=gap.GeneratorsOfGroup(G); ngens=Integer(gap.Length(Ggens))
def conv(s):
    s=str(s)
    if 'E(' in s:
        return R7(sage_eval(s.replace('E(','CyclotomicField(').replace(')',').gen()')))
    return R7(QQ(s))
genmats=[]
for k in range(1,ngens+1):
    Mg=gap.Image(rep,Ggens[k]); rows=Integer(gap.Length(Mg))
    M=matrix(R7,rows,rows)
    for a in range(1,rows+1):
        for b in range(1,rows+1):
            M[a-1,b-1]=conv(gap(Mg[a][b]))
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
ELEM=list(elems.values()); assert len(ELEM)==168, len(ELEM)
# order-3 element for sigma
def matorder(M):
    P=M; o=1
    while P!=I3 and o<200: P=P*M; o+=1
    return o
sigma=[M for M in ELEM if matorder(M)==3][0]
print("PSL(2,7) 3-dim irrep built, order 168, sigma order 3 found.")

# conjugation fixed space (over R7). rho irreducible: check End dim.
def conjOp(g):
    gi=g.inverse(); C=matrix(R7,9,9)
    for i in range(3):
        for j in range(3):
            E=matrix(R7,3,3); E[i,j]=1; img=g*E*gi; col=i*3+j
            for a in range(3):
                for b in range(3): C[a*3+b,col]=img[a,b]
    return C
rows=[]; I9=identity_matrix(R7,9)
for g in ELEM: rows.append(conjOp(g)-I9)
big=block_matrix(R7,[[m] for m in rows])
print("dim End(rho) =", 9-big.rank(), "(1 => irreducible)")

def fixedBasis_sub(Hmats):
    rows=[]; I9=identity_matrix(R7,9)
    for h in Hmats: rows.append(conjOp(h)-I9)
    big=block_matrix(R7,[[m] for m in rows]); ker=big.right_kernel().basis()
    return [matrix(R7,3,3,[v[k] for k in range(9)]) for v in ker]

# Use GAP to get subgroups of order >=8 (=> orbit <=21). Get conjugacy class reps.
ccs=gap.ConjugacyClassesSubgroups(G)
print("num subgroup conjugacy classes:", Integer(gap.Length(ccs)))
# For each class rep H with |H|>=8, map its generators through rep, build matrix
# subgroup, compute fixed dim and orbit = 168/|H|.
Eb=[]
for i in range(3):
    for j in range(3):
        E=matrix(R7,3,3); E[i,j]=1; Eb.append(E)
def residual(ai,bi,ci):
    A,B,C=Eb[ai],Eb[bi],Eb[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
Rsupport=set((a,b,c) for a in range(9) for b in range(9) for c in range(9) if residual(a,b,c)!=0)

def subgroup_matrices(Hgap):
    hg=gap.GeneratorsOfGroup(Hgap); nh=Integer(gap.Length(hg))
    if nh==0:
        return [I3]
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

print("\nsubgroups order>=8 (orbit<=21): fixed dims and single-orbit feasibility")
ncc=Integer(gap.Length(ccs))
seen_orders=set()
for ci in range(1,ncc+1):
    H=gap.Representative(ccs[ci]); o=Integer(gap.Order(H))
    if o<8 or o>=168: continue
    orbit=168//o
    if orbit>21: continue
    Hmats=subgroup_matrices(H)
    if len(Hmats)!=o:
        print(f"  |H|={o}: matrix subgroup order {len(Hmats)} != {o}, skip"); continue
    fb=fixedBasis_sub(Hmats); d=len(fb)
    tag=f"|H|={o} orbit={orbit} rank={1+orbit} fixed_dim={d}"
    if d==0:
        print(f"  {tag}: fixed dim 0 => no seed (id^3 only); skip"); continue
    # build & solve single-orbit system over R7
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
    polys=[]; reach=set()
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
                if orb!=0: reach.add((ai,bi,cci))
                P=orb+residual(ai,bi,cci)
                if P!=0: polys.append(P)
    I=Rr.ideal(polys); unit=(Rr.one() in I)
    cov=len(reach&Rsupport); missed=Rsupport-reach
    v="INFEASIBLE (unit ideal)" if unit else f"SOLUTION-FOUND dim {I.dimension()} *** STOP rank {1+orbit} ***"
    print(f"  {tag}: cov {cov}/{len(Rsupport)}{' MISS '+str(len(missed)) if missed else ''}; {v}")
