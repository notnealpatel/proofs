# Oe1 DISPATCH (medium, single-core): PSL(2,7) MULTI-ORBIT closure.
# Single-orbit PSL(2,7) is already ALL-INFEASIBLE (Oe1-family2-psl27-solve.sage:
# every stabilizer of order>=8 gives the unit ideal). This closes the multi-orbit
# case: combine the small-orbit stabilizers (orbit 7 from S_4-stab, orbit 8 from
# 7:3-stab) into configs with total orbit <= 21 (so rank <= 22) and solve each
# over the cyclotomic field. SOLUTION-FOUND rank<23 => STOP.
#
# Run:  sager Sager/Oe1-dispatch-psl27-multi.sage
# Emits one JSON line per config + summary.
#
# Configs in budget (orbit 7 = a, orbit 8 = b):
#   a+a (14), a+b (15), b+b (16), a+a+a... no (21 with three 7s => rank22 ok),
#   a+a+b (22 -> orbit 22 >21 NO). So: {a,a},{a,b},{b,b},{a,a,a}. Each orbit's
#   stabilizer (S_4 or 7:3) has fixed_dim 1, so a k-orbit config has k variables.

import json
def _coerce(o):
    from sage.all import Integer, Rational
    if isinstance(o, Integer): return int(o)
    if isinstance(o, Rational): return int(o) if o.denominator()==1 else float(o)
    if isinstance(o, dict): return {k:_coerce(v) for k,v in o.items()}
    if isinstance(o, (list,tuple)): return [_coerce(v) for v in o]
    return o
def emit(d): print(json.dumps(_coerce(d)), flush=True)
R7=CyclotomicField(7)
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
            ne=g*e; kk=matkey(ne)
            if kk not in elems: elems[kk]=ne; new.append(ne)
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
def sub_mats(Hgap):
    hg=gap.GeneratorsOfGroup(Hgap); nh=Integer(gap.Length(hg))
    if nh==0: return [I3]
    gm=[]
    for k in range(1,nh+1):
        Mg=gap.Image(rep,hg[k]); M=matrix(R7,3,3)
        for a in range(1,4):
            for b in range(1,4): M[a-1,b-1]=conv(gap(Mg[a][b]))
        gm.append(M)
    Hd={matkey(I3):I3}; fr=[I3]
    for _ in range(2000):
        if not fr: break
        nn=[]
        for e in fr:
            for g in gm:
                ne=g*e; kk=matkey(ne)
                if kk not in Hd: Hd[kk]=ne; nn.append(ne)
        fr=nn
    return list(Hd.values())
# get one S_4 stab (orbit7) and one 7:3 stab (orbit8)
ccs=gap.ConjugacyClassesSubgroups(G); ncc=Integer(gap.Length(ccs))
H_s4=None; H_73=None
for ci in range(1,ncc+1):
    H=gap.Representative(ccs[ci]); o=Integer(gap.Order(H))
    if o==24 and H_s4 is None: H_s4=sub_mats(H)
    if o==21 and H_73 is None: H_73=sub_mats(H)
fb_s4=fixedBasis_sub(H_s4); fb_73=fixedBasis_sub(H_73)
emit({"info":"stabs","S4_orbit":168//len(H_s4),"S4_fixed_dim":len(fb_s4),
      "F21_orbit":168//len(H_73),"F21_fixed_dim":len(fb_73)})
Eb=[]
for i in range(3):
    for j in range(3):
        E=matrix(R7,3,3); E[i,j]=1; Eb.append(E)
def residual(ai,bi,ci):
    A,B,C=Eb[ai],Eb[bi],Eb[ci]
    return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
TYPES={"S4":(fb_s4,168//len(H_s4)),"F21":(fb_73,168//len(H_73))}
def build_solve(cfg):
    # cfg: list of type names; each orbit own variable block
    nv=sum(len(TYPES[t][0]) for t in cfg)
    Rr=PolynomialRing(R7,nv,[f"x{i}" for i in range(nv)]); xs=Rr.gens()
    seeds=[]; off=0
    for t in cfg:
        fb,_=TYPES[t]; d=len(fb)
        mm=matrix(Rr,3,3)
        for p in range(d): mm+=xs[off+p]*fb[p].change_ring(Rr)
        s=sigma.change_ring(Rr); mm2=s*mm*s.inverse(); s2=(sigma*sigma).change_ring(Rr); mm3=s2*mm*s2.inverse()
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
            for cci in range(9):
                orb=Rr(0)
                for (mm,mm2,mm3) in seeds:
                    for gg in ELEM:
                        gR=gg.change_ring(Rr); gmi=gR.inverse()
                        la=fR(Eb[ai],gR*mm*gmi)
                        if la==0: continue
                        lb=fR(Eb[bi],gR*mm2*gmi)
                        if lb==0: continue
                        lc=fR(Eb[cci],gR*mm3*gmi)
                        if lc==0: continue
                        orb+=la*lb*lc
                P=orb+residual(ai,bi,cci)
                if P!=0: polys.append(P)
    I=Rr.ideal(polys); unit=(Rr.one() in I)
    return unit,(None if unit else I.dimension())
CFGS=[["S4","S4"],["S4","F21"],["F21","F21"],["S4","S4","S4"]]
any_sol=False
for cfg in CFGS:
    tot=sum(TYPES[t][1] for t in cfg)
    if tot>21:
        emit({"config":"+".join(cfg),"total_orbit":int(tot),"verdict":"OVER-BUDGET"}); continue
    unit,dim=build_solve(cfg)
    rec={"config":"+".join(cfg),"num_orbits":len(cfg),"total_orbit":int(tot),"rank":int(1+tot)}
    if unit: rec["verdict"]="INFEASIBLE"
    else: rec["verdict"]="SOLUTION-FOUND"; rec["dimension"]=int(dim); any_sol=True
    emit(rec)
emit({"group":"PSL(2,7)","summary":True,"multi_orbit_verdict":("RANK-IMPROVED *** STOP ***" if any_sol else "ALL-INFEASIBLE")})
