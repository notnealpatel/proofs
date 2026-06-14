# Oe1 DISPATCH (heavy, single-core): Valentiner group 3.A_6 (order 1080)
# single-orbit GM-ansatz feasibility for <3,3,3>.
#
# Run:  sager Sager/Oe1-dispatch-valentiner.sage
# Emits one JSON line per viable stabilizer (orbit<=21) with the Groebner verdict,
# plus a final summary JSON line {"group":"3.A_6","verdict":...}.
#
# WHY THIS MATTERS (Oe1 Family 2): 3.A_6 (the Valentiner triple cover) has four
# faithful 3-dim COMPLEX irreps (the icosahedral-analogue on CP^2), char field
# inside Q(zeta_15). It is one of the few finite groups with a faithful 3-dim
# irrep beyond the O(3) point groups (Blichfeldt classification). If a single
# 3.A_6 orbit with total orbit <= 21 yields a SOLUTION-FOUND, that is a rank<23
# matrix-multiplication decomposition => FIRST improvement on Laderman 1976 =>
# STOP and escalate. Expected outcome INFEASIBLE (3.A_6 is not 3-transitive on a
# 4-point set, so GM's clean T_MM mechanism does not apply -- but VERIFY).
#
# COST: builds the 1080-element 3-dim matrix group, then for each stabilizer H
# with orbit = 1080/|H| <= 21 (i.e. |H| >= 52), forms the sigma-twisted orbit-sum
# over all 1080 group elements for all 9^3 = 729 basis triples (a degree-3 poly in
# fixed_dim vars), and computes a Groebner basis over the cyclotomic field. The
# 1080-element inner loop x 729 triples is the single-core cost; minutes to tens
# of minutes per stabilizer.
#
# PARALLELISM NOTE: if this single script is too slow, split by stabilizer --
# duplicate this file as Oe1-dispatch-valentiner-H<order>.sage and hardcode one
# target |H| in the `if o != TARGET` filter. Each becomes an independent core job.

import json, math

def conv_factory(Rn):
    def conv(s):
        s=str(s)
        if 'E(' in s:
            try: return Rn(sage_eval(s.replace('E(','CyclotomicField(').replace(')',').gen()')))
            except Exception: return None
        try: return Rn(QQ(s))
        except Exception: return None
    return conv

def _coerce(o):
    from sage.all import Integer, Rational
    if isinstance(o, Integer): return int(o)
    if isinstance(o, Rational): return int(o) if o.denominator()==1 else float(o)
    if isinstance(o, dict): return {k:_coerce(v) for k,v in o.items()}
    if isinstance(o, (list,tuple)): return [_coerce(v) for v in o]
    return o
RESULTS=[]
def emit(d): print(json.dumps(_coerce(d)), flush=True); RESULTS.append(d)

realized=False
for cycloN in [15, 45, 60]:
    Rn=CyclotomicField(cycloN); conv=conv_factory(Rn)
    G=gap.SchurCover(gap.AlternatingGroup(6))
    ordG=Integer(gap.Order(G))
    irr=gap.IrreducibleRepresentations(G); nirr=Integer(gap.Length(irr))
    Ggens=gap.GeneratorsOfGroup(G); ng=Integer(gap.Length(Ggens))
    chosen=None
    for i in range(1,nirr+1):
        rep=irr[i]
        if Integer(gap.Length(gap.Image(rep,Ggens[1])))!=3: continue
        ok=True; gmats=[]
        for k in range(1,ng+1):
            Mk=gap.Image(rep,Ggens[k]); M=matrix(Rn,3,3)
            for a in range(1,4):
                for b in range(1,4):
                    v=conv(gap(Mk[a][b]))
                    if v is None: ok=False; break
                    M[a-1,b-1]=v
                if not ok: break
            if not ok: break
            gmats.append(M)
        if ok: chosen=(i,rep,gmats); break
    if chosen is None: continue
    i,rep,gmats=chosen
    # Realize via GAP permutation iso for SPEED (cyclotomic BFS to 1080 is slow),
    # then map each group element to its 3x3 matrix once. We index GAP elements by
    # a canonical permutation-image string. If the iso path fails, fall back to
    # matrix BFS.
    def matkey(M): return tuple(M.list())
    I3=identity_matrix(Rn,3)
    ELEM=None
    try:
        Pgap=gap.IsomorphismPermGroup(G)
        Gp=gap.Image(Pgap)
        gelems=gap.Elements(Gp)
        ne=Integer(gap.Length(gelems))
        # preimage iso to compute matrices via rep
        Pinv=gap.InverseGeneralMapping(Pgap)
        ELEM=[]
        for t in range(1,ne+1):
            gg=gap.Image(Pinv, gelems[t])
            Mg=gap.Image(rep, gg); M=matrix(Rn,3,3); okk=True
            for a in range(1,4):
                for b in range(1,4):
                    v=conv(gap(Mg[a][b]))
                    if v is None: okk=False; break
                    M[a-1,b-1]=v
                if not okk: break
            if not okk: ELEM=None; break
            ELEM.append(M)
    except Exception:
        ELEM=None
    if ELEM is None:
        elems={matkey(I3):I3}; frontier=[I3]
        for _ in range(100000):
            if not frontier: break
            new=[]
            for e in frontier:
                for g in gmats:
                    ne2=g*e; kk=matkey(ne2)
                    if kk not in elems: elems[kk]=ne2; new.append(ne2)
            frontier=new
        ELEM=list(elems.values())
    realN=len(ELEM)
    emit({"info":"realized 3-dim irrep","cycloN":int(cycloN),"irrep_index":int(i),"realized_order":int(realN)})
    realized=True

    def matorder(M):
        P=M; o=1
        while P!=I3 and o<3000: P=P*M; o+=1
        return o
    sig=[M for M in ELEM if matorder(M)==3]
    if not sig:
        emit({"group":"3.A_6","verdict":"NO-SIGMA","note":"no order-3 element"}); break
    sigma=sig[0]
    def conjOp(g):
        gi=g.inverse(); C=matrix(Rn,9,9)
        for ii in range(3):
            for jj in range(3):
                E=matrix(Rn,3,3); E[ii,jj]=1; img=g*E*gi; col=ii*3+jj
                for a in range(3):
                    for b in range(3): C[a*3+b,col]=img[a,b]
        return C
    def fixedBasis_sub(H):
        rows=[]; I9=identity_matrix(Rn,9)
        for h in H: rows.append(conjOp(h)-I9)
        big=block_matrix(Rn,[[m] for m in rows]); ker=big.right_kernel().basis()
        return [matrix(Rn,3,3,[v[k] for k in range(9)]) for v in ker]
    Eb=[]
    for ii in range(3):
        for jj in range(3):
            E=matrix(Rn,3,3); E[ii,jj]=1; Eb.append(E)
    def residual(ai,bi,ci):
        A,B,C=Eb[ai],Eb[bi],Eb[ci]
        return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
    Rsupport=set((a,b,c) for a in range(9) for b in range(9) for c in range(9) if residual(a,b,c)!=0)
    need=math.ceil(realN/21)
    ccs=gap.ConjugacyClassesSubgroups(G); ncc=Integer(gap.Length(ccs))
    def sub_mats(Hgap):
        hg=gap.GeneratorsOfGroup(Hgap); nh=Integer(gap.Length(hg))
        if nh==0: return [I3]
        gm=[]
        for k in range(1,nh+1):
            Mg=gap.Image(rep,hg[k]); M=matrix(Rn,3,3); okk=True
            for a in range(1,4):
                for b in range(1,4):
                    v=conv(gap(Mg[a][b]))
                    if v is None: okk=False; break
                    M[a-1,b-1]=v
                if not okk: break
            if not okk: return None
            gm.append(M)
        Hd={matkey(I3):I3}; fr=[I3]
        for _ in range(8000):
            if not fr: break
            nn=[]
            for e in fr:
                for g in gm:
                    ne=g*e; kk=matkey(ne)
                    if kk not in Hd: Hd[kk]=ne; nn.append(ne)
            fr=nn
        return list(Hd.values())
    any_sol=False; checked=0
    for ci in range(1,ncc+1):
        H=gap.Representative(ccs[ci]); o=Integer(gap.Order(H))
        if o<need or o>=ordG: continue
        Hm=sub_mats(H)
        if not Hm: continue
        orbit=realN//len(Hm)
        if orbit>21 or orbit<1: continue
        fb=fixedBasis_sub(Hm); d=len(fb)
        if d==0:
            emit({"group":"3.A_6","H_order":int(len(Hm)),"orbit":int(orbit),"rank":int(1+orbit),"fixed_dim":0,"verdict":"NO-SEED"}); continue
        Rr=PolynomialRing(Rn,d,[f"x{ix}" for ix in range(d)]); xs=Rr.gens()
        m1=matrix(Rr,3,3)
        for p in range(d): m1+=xs[p]*fb[p].change_ring(Rr)
        s=sigma.change_ring(Rr); m2=s*m1*s.inverse(); s2=(sigma*sigma).change_ring(Rr); m3=s2*m1*s2.inverse()
        def frobR(Xc,Ms):
            acc=Rr(0)
            for ii in range(3):
                for jj in range(3):
                    if Xc[ii,jj]!=0: acc+=Xc[ii,jj]*Ms[ii,jj]
            return acc
        gm2={}
        for gi,gg in enumerate(ELEM):
            gR=gg.change_ring(Rr); gmi=gR.inverse()
            gm2[(gi,0)]=gR*m1*gmi; gm2[(gi,1)]=gR*m2*gmi; gm2[(gi,2)]=gR*m3*gmi
        polys=[]; reach=set()
        for ai in range(9):
            for bi in range(9):
                for cci in range(9):
                    orb=Rr(0)
                    for gi in range(len(ELEM)):
                        la=frobR(Eb[ai],gm2[(gi,0)])
                        if la==0: continue
                        lb=frobR(Eb[bi],gm2[(gi,1)])
                        if lb==0: continue
                        lc=frobR(Eb[cci],gm2[(gi,2)])
                        if lc==0: continue
                        orb+=la*lb*lc
                    if orb!=0: reach.add((ai,bi,cci))
                    P=orb+residual(ai,bi,cci)
                    if P!=0: polys.append(P)
        I=Rr.ideal(polys); unit=(Rr.one() in I)
        cov=len(reach&Rsupport)
        rec={"group":"3.A_6","H_order":int(len(Hm)),"orbit":int(orbit),"rank":int(1+orbit),
             "fixed_dim":int(d),"covered":int(cov),"residual_support":int(len(Rsupport))}
        if unit:
            rec["verdict"]="INFEASIBLE"
        else:
            rec["verdict"]="SOLUTION-FOUND"; rec["dimension"]=int(I.dimension()); any_sol=True
        emit(rec); checked+=1
    emit({"group":"3.A_6","summary":True,"stabilizers_checked":int(checked),
          "verdict":("RANK-IMPROVED *** STOP ***" if any_sol else "ALL-INFEASIBLE")})
    break

if not realized:
    emit({"group":"3.A_6","verdict":"UNREALIZED","note":"no 3-dim faithful irrep over tried cyclotomic fields; widen cycloN"})
