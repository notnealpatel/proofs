# Oe1: verify the 6 antisymmetric directions (a1,a2,a3)-permutations are
# reachable by the FULL (H={e}, 9-dim) seed, both twisted and decoupled. If yes,
# the wall that kills restricted-symmetry orbits is purely a RESTRICTION effect
# (small H => fixed seed space too small to reach (a1,a2,a3)), consistent with
# GM's full-orbit rank-25 success -- NOT a contradiction. This pins the
# representation-theoretic story: rho'^{(x)3} contains the diagonal trivial in
# the totally-antisymmetric component, which only an UNRESTRICTED seed populates.
#
# Also: confirm the twisted H={e} reaches all 6 (matches the earlier finding that
# H={e} twisted leaves 592 obstructed, ALL with zero residual => it reaches every
# nonzero-residual direction including these antisymmetric ones).

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
ANTI=[(6,7,8),(6,8,7),(7,6,8),(7,8,6),(8,6,7),(8,7,6)]

def frobR(Xc,Ms,R):
    acc=R(0)
    for i in range(3):
        for j in range(3):
            if Xc[i,j]!=0: acc += Xc[i,j]*Ms[i,j]
    return acc

def full_twisted_on(ai,bi,ci):
    R=PolynomialRing(K,9,[f"x{k}" for k in range(9)]); xs=R.gens()
    m1=matrix(R,3,3)
    for i in range(3):
        for j in range(3): m1[i,j]=xs[i*3+j]
    s=sigma.change_ring(R); m2=s*m1*s.transpose(); s2=(sigma*sigma).change_ring(R); m3=s2*m1*s2.transpose()
    orb=R(0)
    for gg in ELEM:
        gR=gg.change_ring(R)
        la=frobR(BR[ai],gR*m1*gR.transpose(),R)
        if la==0: continue
        lb=frobR(BR[bi],gR*m2*gR.transpose(),R)
        if lb==0: continue
        lc=frobR(BR[ci],gR*m3*gR.transpose(),R)
        if lc==0: continue
        orb += la*lb*lc
    return orb

def full_decoupled_on(ai,bi,ci):
    R=PolynomialRing(K,27,[f"x{k}" for k in range(9)]+[f"y{k}" for k in range(9)]+[f"z{k}" for k in range(9)]); g=R.gens()
    def seed(off):
        M=matrix(R,3,3)
        for i in range(3):
            for j in range(3): M[i,j]=g[off+i*3+j]
        return M
    m1=seed(0); m2=seed(9); m3=seed(18)
    orb=R(0)
    for gg in ELEM:
        gR=gg.change_ring(R)
        la=frobR(BR[ai],gR*m1*gR.transpose(),R)
        if la==0: continue
        lb=frobR(BR[bi],gR*m2*gR.transpose(),R)
        if lb==0: continue
        lc=frobR(BR[ci],gR*m3*gR.transpose(),R)
        if lc==0: continue
        orb += la*lb*lc
    return orb

print("Antisymmetric directions reachable by the FULL (H={e}) seed?")
print("triple            | twisted_full | decoupled_full")
for (ai,bi,ci) in ANTI:
    tw = full_twisted_on(ai,bi,ci)
    dc = full_decoupled_on(ai,bi,ci)
    print(f"({NAMES[ai]},{NAMES[bi]},{NAMES[ci]})  | {'REACHES' if tw!=0 else 'zero':12s} | {'REACHES' if dc!=0 else 'zero'}")
print()
print("If twisted_full REACHES all 6 => GM's full-orbit construction DOES populate")
print("the antisymmetric directions; the restricted (catalog-H) failure is purely")
print("a RANK/RESTRICTION effect, fully consistent with GM rank-25 success.")
