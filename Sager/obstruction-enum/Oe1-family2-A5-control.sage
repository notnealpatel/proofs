# Oe1 Family 2: A_5 POSITIVE/NEGATIVE control, mirroring Os1's validation of the
# S_4 builder. Before trusting the INFEASIBLE verdict for T_MM, validate the A_5
# constraint-system builder the same way Os1 validated Or2's:
#   POSITIVE: plant a concrete C_5-fixed seed m*, define T' = id^3 + A_5-orbit(m*)
#     via the SAME orbit sum, build the system against T', confirm it is FEASIBLE
#     (the planted x* is a root; Groebner NOT unit ideal) and the planted point
#     actually satisfies every constraint.
#   NEGATIVE: against T_MM (the real target) the system is the unit ideal.
# Same builder, only the target term differs => if positive=FEASIBLE(with planted
# root) and negative=INFEASIBLE, the builder discriminates and the T_MM unit-ideal
# verdict is trustworthy (not a builder bug that makes everything infeasible).

import json
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
Eb=[]
for i in range(3):
    for j in range(3):
        E=matrix(K,3,3); E[i,j]=1; Eb.append(E)
def residual(ai,bi,ci):
    A,B,C=Eb[ai],Eb[bi],Eb[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()

# concrete orbit-sum inner product <T_ansatz, A(x)B(x)C> for concrete seed m1
def ansatz_inner(m1, A, B, C):
    val = A.trace()*B.trace()*C.trace()
    m2 = sigma*m1*sigma.inverse(); m3 = sigma*sigma*m1*(sigma.inverse())**2
    def fr(X,M):
        s=K(0)
        for i in range(3):
            for j in range(3): s+=X[i,j]*M[i,j]
        return s
    for g in ELEM:
        gi=g.inverse()
        f1=fr(A, g*m1*gi)
        if f1==0: continue
        f2=fr(B, g*m2*gi)
        if f2==0: continue
        f3=fr(C, g*m3*gi)
        if f3==0: continue
        val += f1*f2*f3
    return val

g_ord5=[g for g in ELEM if len(cyclic(g))==5][0]
H=cyclic(g_ord5); fb=fixedBasis_sub(H); d=len(fb)
print(f"C_5 stab: orbit {60//len(H)}, rank {1+60//len(H)}, fixed dim {d}")

# planted seed m* = fb[0] + 2*fb[1] - fb[2]  (a concrete C_5-fixed seed)
coef_star=[K(1),K(2),K(-1)][:d]
mstar=matrix(K,3,3)
for p in range(d): mstar += coef_star[p]*fb[p]
print(f"planted m* (C_5-fixed). matrix rank {mstar.rank()}")

# Build symbolic system against a target functional.
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

def build_polys(targetInner):
    polys=[]
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
                P = orb + (Eb[ai].trace()*Eb[bi].trace()*Eb[ci].trace() - targetInner(ai,bi,ci))
                if P!=0: polys.append(P)
    return polys

# POSITIVE: target T' = id^3 + orbit(mstar). targetInner = ansatz_inner(mstar).
tprime = {}
def target_prime(ai,bi,ci):
    key=(ai,bi,ci)
    if key not in tprime:
        tprime[key]=ansatz_inner(mstar, Eb[ai],Eb[bi],Eb[ci])
    return tprime[key]
pos_polys = build_polys(target_prime)
Ipos=R.ideal(pos_polys)
# planted x* satisfies every constraint?
xstar={xs[p]: coef_star[p] for p in range(d)}
all_vanish = all(P.subs(xstar)==0 for P in pos_polys)
print(f"\nPOSITIVE control (target T'=id^3+orbit(m*)):")
print(f"  planted x*={[str(c) for c in coef_star]} satisfies all {len(pos_polys)} constraints: {all_vanish}")
gbpos=Ipos.groebner_basis()
unit_pos = (R.one() in Ipos)
print(f"  Groebner unit ideal? {unit_pos}  (expect False => FEASIBLE, planted solution exists)")
if not unit_pos:
    print(f"  dimension {Ipos.dimension()} => SOLUTION-FOUND as required")

# NEGATIVE: target T_MM. targetInner = tr(ABC).
def target_mm(ai,bi,ci):
    return (Eb[ai]*Eb[bi]*Eb[ci]).trace()
neg_polys = build_polys(target_mm)
Ineg=R.ideal(neg_polys)
unit_neg = (R.one() in Ineg)
print(f"\nNEGATIVE control (target T_MM):")
print(f"  Groebner unit ideal? {unit_neg}  (expect True => INFEASIBLE)")
print(f"  planted x* satisfies all T_MM constraints: {all(P.subs(xstar)==0 for P in neg_polys)}  (expect False)")

print("\nVALIDATION:", "PASS (builder discriminates; T_MM INFEASIBLE is trustworthy)"
      if (all_vanish and not unit_pos and unit_neg) else "FAIL -- investigate builder")
