# Oe1 Family 2: the OCTAHEDRAL ROTATION group O (~ S_4, all det +1) vs GM's
# T_d = S_4 (standard rep, odd perms det -1). Both are ~ S_4 abstractly, but S_4
# has TWO 3-dim irreps: standard rho and anti-standard rho' = rho (x) sign. If O
# realizes rho' (a DIFFERENT irrep), an O-symmetric ansatz might escape the
# obstruction. Check: build O = pure rotation octahedral group (signed perms with
# det +1), confirm order 24, irreducibility, and whether its rho (x) rho*
# structure / feasibility differs from T_d's.
#
# ALSO: the +-I (inversion) extensions T_h,O_h,I_h add NOTHING -- inversion -I
# conjugates trivially ((-I)X(-I)=X) and (-g)^{(x)3}(...)( -g)^{dag(x)3} equals
# g^{(x)3}(...)g^{dag(x)3}, so the orbit sum just doubles (absorbable into seed).
# So only O (octahedral rotation) is a genuinely new candidate vs S_4=T_d.

import json
K.<r3>=QuadraticField(3)
def Mt(rows): return matrix(K,rows)

# Octahedral rotation group O: the 24 rotation matrices = signed permutation
# matrices with determinant +1 (proper rotations permuting the +-axes). Generate
# from a 4-fold rotation about z and a 3-fold about a body diagonal.
g4 = Mt([[0,-1,0],[1,0,0],[0,0,1]])   # 90deg about z, det +1
g3 = Mt([[0,0,1],[1,0,0],[0,1,0]])    # 120deg cycling axes, det +1
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
ELEM=list(elems.values())
print(f"octahedral rotation group O order: {len(ELEM)} (expect 24)")
# all det +1?
print(f"all det +1: {all(M.det()==1 for M in ELEM)}")
# order distribution
def matorder(M):
    P=M; o=1
    while P!=I3 and o<50: P=P*M; o+=1
    return o
from collections import Counter
print("order dist:", dict(Counter(matorder(M) for M in ELEM)))
# S_4 has order dist: 1(1),2(...),3(8),4(6). O ~ S_4 so expect orders {1,2,3,4}.
sigma=g3  # order 3

def conjOp(g):
    gi=g.inverse(); C=matrix(K,9,9)
    for i in range(3):
        for j in range(3):
            E=matrix(K,3,3); E[i,j]=1; img=g*E*gi; col=i*3+j
            for a in range(3):
                for b in range(3): C[a*3+b,col]=img[a,b]
    return C
rows=[]; I9=identity_matrix(K,9)
for g in ELEM: rows.append(conjOp(g)-I9)
big=block_matrix(K,[[m] for m in rows])
print(f"dim End_O(rho) = {9-big.rank()} (1 => irreducible)")

# Is O's rho the STANDARD or ANTI-STANDARD rep? Distinguish by the character on a
# transposition-class. In S_4 standard rep chi(transposition)=1, anti-standard
# chi(transposition)=-1 (= sign*standard). But O has no "transpositions" labeled;
# instead compare rho (x) rho* decomposition. KEY: rho (x) rho* is the SAME for
# rho and rho' (since rho' (x) rho'* = rho (x) rho*, sign cancels). So conjugation
# action is IDENTICAL => fixed spaces and orbit-sum structure are identical to S_4.
# Hence O gives the SAME feasibility as T_d. Verify by checking the fixed-dim of a
# representative order-3 stabilizer matches S_4 Z_3 (=3) and solving one orbit.
def cyclic(g):
    H=[I3]; P=g
    while P!=I3: H.append(P); P=P*g
    return H
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

# subgroup orbits in O
subs={}
for g in ELEM:
    H=cyclic(g); subs.setdefault(len(H),H)
print("\nO subgroup orbit table (cyclic):")
for o,H in sorted(subs.items()):
    fb=fixedBasis_sub(H); orbit=24//o
    print(f"  |H|={o} orbit={orbit} rank={1+orbit} fixed_dim={len(fb)}")

# Solve the smallest single-orbit O configs (rank<=22) over Q(sqrt3).
def build_solve(H, label):
    fb=fixedBasis_sub(H); d=len(fb); orbit=24//len(H)
    if d==0 or 1+orbit>22:
        return
    R=PolynomialRing(K,d,[f"x{i}" for i in range(d)]); xs=R.gens()
    m1=matrix(R,3,3)
    for p in range(d): m1+=xs[p]*fb[p].change_ring(R)
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
    reach=set(); polys=[]
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
                    orb+=la*lb*lc
                if orb!=0: reach.add((ai,bi,ci))
                P=orb+residual(ai,bi,ci)
                if P!=0: polys.append(P)
    I=R.ideal(polys); unit=(R.one() in I)
    cov=len(reach&Rsupport); missed=Rsupport-reach
    v="INFEASIBLE (unit ideal)" if unit else f"SOLUTION-FOUND dim {I.dimension()} *** STOP rank {1+orbit} ***"
    print(f"  O single-orbit |H|={len(H)} orbit {orbit} rank {1+orbit} dim {d}: cov {cov}/{len(Rsupport)}{' MISS '+str(len(missed)) if missed else ''}; {v}")
    return unit

print("\nO single-orbit verdicts (rank<=22):")
for o,H in sorted(subs.items()):
    build_solve(H, f"Z_{o}")
