# Oe1 Family 1 refinement: WHICH catalog orbit types reach the canonical
# box-box / rho'-rho' killer directions, and what does the 2-orbit Groebner
# verdict (all INFEASIBLE) actually imply for >=3 orbits?
#
# The naive "common obstructed intersection" gave 0 killers -- meaning some
# orbit reaches (id,box_x,box_x). But Or2 found ALL 18 two-orbit pairs
# INFEASIBLE via global Groebner. So the obstruction is not a single constant
# generator on a commonly-obstructed triple; it is a global incompatibility.
#
# Here we (1) report, per catalog orbit, whether the canonical box-box triple
# (0,1,1) and the canonical rho'-rho' triple are obstructed, and (2) for the
# box-box direction, show the actual orbit-sum polynomial each orbit produces
# there -- so we can see whether a 3rd orbit adds an INDEPENDENT direction or
# is linearly dependent on what 2 orbits already provide.

import json
K.<r3> = QuadraticField(3)
def Mt(rows): return matrix(K, rows)
rho_12 = Mt([[0,1,0],[1,0,0],[0,0,1]]); rho_23 = Mt([[1,0,0],[0,0,1],[0,1,0]])
rho_34 = Mt([[0,-1,0],[-1,0,0],[0,0,1]]); sigma = Mt([[0,0,1],[1,0,0],[0,1,0]])
gens = {(1,0,2,3): rho_12, (0,2,1,3): rho_23, (0,1,3,2): rho_34}
def compose(p,q): return tuple(p[q[i]] for i in range(4))
ident=(0,1,2,3); elems={ident: identity_matrix(K,3)}; frontier=[ident]
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

def orbit_poly_on_triple(gp, ai, bi, ci):
    """Return the symbolic orbit-sum polynomial on (A,B,C) for one orbit with
    stabilizer gp, in its own seed variables."""
    fb,hord=fixedBasis(gp); d=len(fb)
    R=PolynomialRing(K, d, [f"x{i}" for i in range(d)] if d>0 else ["x0"])
    xs=R.gens(); m1=matrix(R,3,3)
    for p in range(d): m1 += xs[p]*fb[p].change_ring(R)
    s=sigma.change_ring(R); m2=s*m1*s.transpose()
    s2=(sigma*sigma).change_ring(R); m3=s2*m1*s2.transpose()
    def frobR(Xc,Ms):
        acc=R(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc += Xc[i,j]*Ms[i,j]
        return acc
    orb=R(0)
    for gi,g in enumerate(ELEM):
        gR=g.change_ring(R)
        gm0=gR*m1*gR.transpose(); gm1=gR*m2*gR.transpose(); gm2=gR*m3*gR.transpose()
        la=frobR(BR[ai],gm0)
        if la==0: continue
        lb=frobR(BR[bi],gm1)
        if lb==0: continue
        lc=frobR(BR[ci],gm2)
        if lc==0: continue
        orb += la*lb*lc
    return orb, d

# The two canonical obstructed directions Or2 named.
canon_box  = (0,1,1)   # (id, box_x, box_x)  -- box-box, eq (4box)
# rho'-rho' (antisymmetric): (id, a1, a1) is the natural analogue.
canon_anti = (0,6,6)   # (id, a1, a1)

def residual(t):
    ai,bi,ci=t; A,B,C=BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()

for label,trip in [("box-box (id,box_x,box_x)",canon_box),("rho'-rho' (id,a1,a1)",canon_anti)]:
    print(f"=== {label} idx={trip}, residual={residual(trip)} ===")
    for name,g,orb in CATALOG:
        poly,d = orbit_poly_on_triple(g, *trip)
        zero = (poly==0)
        print(f"  {name:5s} (dim {d}): orbit poly {'IDENTICALLY ZERO' if zero else 'NONZERO: '+str(poly)}")
    print()
