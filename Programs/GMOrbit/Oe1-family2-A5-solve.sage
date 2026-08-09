# Oe1 Family 2: A_5 single-orbit GM-ansatz feasibility for <3,3,3>.
# Only single-orbit A_5 fits rank<=22 (two orbits >=24). Two candidate
# stabilizers: C_5 (orbit12, rank13, fixed dim3) and C_3 (orbit20, rank21, dim3).
# For each, build the sigma-twisted orbit-sum constraint system against T_MM over
# the canonical M_3 basis (E_ij), and (1) coverage pre-screen, (2) full Groebner
# over Q(sqrt5). SOLUTION-FOUND at rank 13 or 21 would beat Laderman 23 -- STOP.

import json, itertools
K.<s5> = QuadraticField(5)
phi=(1+s5)/2; half=K(1)/2
def Mt(rows): return matrix(K,rows)
g3=Mt([[0,0,1],[1,0,0],[0,1,0]])
g5=Mt([[half,-phi/2,(phi-1)/2],[phi/2,(phi-1)/2,-half],[(phi-1)/2,half,phi/2]])
def matkey(M): return tuple(M.list())
I3=identity_matrix(K,3)
elems={matkey(I3):I3}; frontier=[I3]
for _ in range(2000):
    if not frontier: break
    new=[]
    for e in frontier:
        for g in [g3,g5]:
            ne=g*e; k=matkey(ne)
            if k not in elems: elems[k]=ne; new.append(ne)
    frontier=new
ELEM=list(elems.values()); assert len(ELEM)==60
sigma=g3

def cyclic(g):
    H=[I3]; P=g
    while P!=I3: H.append(P); P=P*g
    return H
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

# canonical M_3 basis
Eb=[]
for i in range(3):
    for j in range(3):
        E=matrix(K,3,3); E[i,j]=1; Eb.append(E)
def residual(ai,bi,ci):
    A,B,C=Eb[ai],Eb[bi],Eb[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
Rsupport=set((a,b,c) for a in range(9) for b in range(9) for c in range(9) if residual(a,b,c)!=0)

# pick a C_5 generator (order 5) and a C_3 generator (order 3)
g_ord5=[g for g in ELEM if cyclic(g) and len(cyclic(g))==5][0]
g_ord3=[g for g in ELEM if len(cyclic(g))==3][0]

def build_and_solve(Hgen, label):
    H=cyclic(Hgen); fb=fixedBasis_sub(H); d=len(fb)
    orbit=60//len(H)
    print(f"\n=== A_5 stabilizer order {len(H)} -> orbit {orbit}, rank {1+orbit}, fixed dim {d} ({label}) ===")
    # symbolic seed m1 = sum x_p fb[p], twisted m2,m3
    R=PolynomialRing(K, d, [f"x{i}" for i in range(d)]); xs=R.gens()
    m1=matrix(R,3,3)
    for p in range(d): m1 += xs[p]*fb[p].change_ring(R)
    s=sigma.change_ring(R); m2=s*m1*s.inverse(); s2=(sigma*sigma).change_ring(R); m3=s2*m1*s2.inverse()
    def frobR(Xc,Ms):
        acc=R(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc += Xc[i,j]*Ms[i,j]
        return acc
    gm={}
    for gi,gg in enumerate(ELEM):
        gR=gg.change_ring(R); gmi=gR.inverse()
        gm[(gi,0)]=gR*m1*gmi; gm[(gi,1)]=gR*m2*gmi; gm[(gi,2)]=gR*m3*gmi
    # coverage + constraint polys
    reach=set(); polys=[]
    for ai in range(9):
        for bi in range(9):
            for ci in range(9):
                orb=R(0)
                for gi in range(60):
                    la=frobR(Eb[ai],gm[(gi,0)])
                    if la==0: continue
                    lb=frobR(Eb[bi],gm[(gi,1)])
                    if lb==0: continue
                    lc=frobR(Eb[ci],gm[(gi,2)])
                    if lc==0: continue
                    orb += la*lb*lc
                if orb!=0: reach.add((ai,bi,ci))
                # constraint P_{A,B,C} = tr(A)tr(B)tr(C) + orb - tr(ABC)
                #                      = orb + residual   (residual = tr(A)tr(B)tr(C) - tr(ABC))
                # matches Go buildPairSystemTarget: constVal=tr(A)tr(B)tr(C)-targetInner, P=constVal+orbitSum.
                P = orb + residual(ai,bi,ci)
                if P != 0:
                    polys.append(P)
    covered = len(reach & Rsupport)
    print(f"  reach {len(reach)} dirs, covers {covered}/{len(Rsupport)} of residual support")
    missed = Rsupport - reach
    if missed:
        print(f"  MISSES {len(missed)} residual dirs => constant generator => INFEASIBLE by coverage")
        # show a sample missed triple's residual (a constant generator)
        t=sorted(missed)[0]
        print(f"    e.g. missed {t} residual={residual(*t)} (bare constant in ideal)")
    else:
        print(f"  COVERS ALL residual dirs -- coverage passes; Groebner decides.")
    # Groebner over Q(sqrt5)
    if d>0:
        I=R.ideal(polys)
        gb=I.groebner_basis()
        gbs=[str(x) for x in gb]
        is_unit = (R.one() in I)
        if is_unit:
            print(f"  GROEBNER over Q(sqrt5): [1] UNIT IDEAL => INFEASIBLE")
        else:
            dim=I.dimension()
            print(f"  GROEBNER over Q(sqrt5): NON-unit, dimension {dim} => SOLUTION-FOUND (rank {1+orbit}) *** STOP ***")
            print(f"    GB={gbs[:6]}")
            try:
                V=I.variety(ring=QQbar)
                print(f"    variety points: {len(V)}")
            except Exception as e:
                print(f"    variety err: {e}")
    return

build_and_solve(g_ord5, "C_5 stab, rank 13")
build_and_solve(g_ord3, "C_3 stab, rank 21")
