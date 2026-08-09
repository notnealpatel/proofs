# Oe1: the INTRINSIC obstruction. Or2 infodump: GM's unconstrained full-orbit
# seed (H={e}, full 9-dim M_3) still leaves 121 triples obstructed, and supplies
# the cancelling residual on exactly those. Identify the H={e} obstructed set:
# triples where the SYMBOLIC orbit-sum is identically zero EVEN for a free 9-dim
# seed. These are the directions no sigma-twisted S_4-orbit construction can ever
# reach, regardless of how many orbits or which stabilizers. If every such
# intrinsically-obstructed triple has ZERO residual, then the obstruction is only
# about RESTRICTING the seed (smaller H), and >=3 small orbits MIGHT cover the
# residual. If some intrinsically-obstructed triple has NONZERO residual, then NO
# multi-orbit S_4 sigma-twist ansatz can ever work => Families 1 dead, and the
# sigma-twist relaxation (Family 3) is the only hope IF decoupling changes this.

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

def residual(ai,bi,ci):
    A,B,C=BR[ai],BR[bi],BR[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()

# H={e}: full 9-dim seed. m1 = sum over all 9 entries x_{i,j} E_ij. Twisted.
def trivial_obstructed():
    d=9
    R=PolynomialRing(K, d, [f"x{k}" for k in range(d)])
    xs=R.gens()
    m1=matrix(R,3,3)
    for i in range(3):
        for j in range(3):
            m1[i,j]=xs[i*3+j]
    s=sigma.change_ring(R); m2=s*m1*s.transpose()
    s2=(sigma*sigma).change_ring(R); m3=s2*m1*s2.transpose()
    def frobR(Xc,Ms):
        acc=R(0)
        for i in range(3):
            for j in range(3):
                if Xc[i,j]!=0: acc += Xc[i,j]*Ms[i,j]
        return acc
    # precompute g m_f g^-1
    gm={}
    for gi,g in enumerate(ELEM):
        gR=g.change_ring(R)
        gm[(gi,0)]=gR*m1*gR.transpose(); gm[(gi,1)]=gR*m2*gR.transpose(); gm[(gi,2)]=gR*m3*gR.transpose()
    obs=[]
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
                if orb==0: obs.append((ai,bi,ci))
    return obs

obs = trivial_obstructed()
print(f"H=&#123;e&#125; (full 9-dim seed, sigma-twisted) obstructed triples: {len(obs)} of 729")
killers = [(t,residual(*t)) for t in obs if residual(*t)!=0]
print(f"  of which with NONZERO MM residual (INTRINSIC killers): {len(killers)}")
for (t,r) in sorted(killers)[:20]:
    ai,bi,ci=t
    print(f"    ({ai},{bi},{ci})=({NAMES[ai]},{NAMES[bi]},{NAMES[ci]}): residual={r}")
if len(killers)==0:
    print("  -> EVERY intrinsically-obstructed triple has zero residual.")
    print("  -> The sigma-twisted S_4 orbit construction CAN in principle reach")
    print("     every direction with a nonzero required residual (given enough free seed).")
    print("  -> Or2's 2-orbit failure is about RANK/RESTRICTION, not an intrinsic wall.")
    print("  -> >=3 orbits is NOT structurally dead; the probe must decide.")
else:
    print("  -> INTRINSIC WALL: these directions are unreachable by ANY sigma-twisted")
    print("     S_4 orbit sum, for any seed or orbit count => Families 1 (and 2, same group)")
    print("     are PRE-SCREEN-DEAD. Only relaxing the construction (sigma-twist) could help.")
