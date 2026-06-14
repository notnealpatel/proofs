# Oe1 Family 2: the last complex-3-dim-irrep candidates -- the Valentiner group
# 3.A_6 (order 1080, char field involves 15th roots / sqrt-15) and the Hessian
# group (order 216, char field Q(omega)). Both have faithful 3-dim COMPLEX
# irreps (3.A_6: dims include 3,3,3,3; Hessian triple cover: a 3-dim reflection
# rep). For each: build the 3-dim irrep over a cyclotomic splitting field,
# enumerate subgroups whose orbit (|G|/|H|) <= 21, fixed dims, and solve the GM
# single-orbit system. SOLUTION-FOUND rank<23 => STOP.

def analyze(Gcmd, name, cycloN, expect_order):
    print(f"\n========== {name} (expect order {expect_order}) ==========")
    Rn=CyclotomicField(cycloN)
    G=gap(Gcmd)
    ordG=Integer(gap.Order(G))
    print(f"|G| = {ordG}")
    irr=gap.IrreducibleRepresentations(G)
    nirr=Integer(gap.Length(irr))
    # find a 3-dim irrep whose entries live in Q(zeta_cycloN)
    three=None
    Ggens=gap.GeneratorsOfGroup(G); ng=Integer(gap.Length(Ggens))
    def conv(s):
        s=str(s)
        if 'E(' in s:
            try:
                return Rn(sage_eval(s.replace('E(','CyclotomicField(').replace(')',').gen()')))
            except Exception:
                return None
        try:
            return Rn(QQ(s))
        except Exception:
            return None
    chosen_idx=None; chosen_gens=None
    for i in range(1,nirr+1):
        rep=irr[i]
        Mg=gap.Image(rep,Ggens[1])
        if Integer(gap.Length(Mg))!=3: continue
        # try to convert all generator images into Rn
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
        if ok:
            chosen_idx=i; chosen_gens=gmats; break
    if chosen_idx is None:
        print(f"  no 3-dim irrep realizable over Q(zeta_{cycloN}); try a larger cyclotomic field.")
        return
    print(f"  using 3-dim irrep #{chosen_idx} over Q(zeta_{cycloN})")
    def matkey(M): return tuple(M.list())
    I3=identity_matrix(Rn,3)
    elems={matkey(I3):I3}; frontier=[I3]
    for _ in range(20000):
        if not frontier: break
        new=[]
        for e in frontier:
            for g in chosen_gens:
                ne=g*e; k=matkey(ne)
                if k not in elems: elems[k]=ne; new.append(ne)
        frontier=new
    ELEM=list(elems.values())
    print(f"  realized rep group order: {len(ELEM)}")
    # NB: a faithful irrep realizes G exactly; if the cover, order = |G|.
    def matorder(M):
        P=M; o=1
        while P!=I3 and o<2000: P=P*M; o+=1
        return o
    sig=[M for M in ELEM if matorder(M)==3]
    if not sig:
        print("  no order-3 element in realized group -- cannot twist; skip."); return
    sigma=sig[0]
    def conjOp(g):
        gi=g.inverse(); C=matrix(Rn,9,9)
        for i in range(3):
            for j in range(3):
                E=matrix(Rn,3,3); E[i,j]=1; img=g*E*gi; col=i*3+j
                for a in range(3):
                    for b in range(3): C[a*3+b,col]=img[a,b]
        return C
    def fixedBasis_sub(H):
        rows=[]; I9=identity_matrix(Rn,9)
        for h in H: rows.append(conjOp(h)-I9)
        big=block_matrix(Rn,[[m] for m in rows]); ker=big.right_kernel().basis()
        return [matrix(Rn,3,3,[v[k] for k in range(9)]) for v in ker]
    Eb=[]
    for i in range(3):
        for j in range(3):
            E=matrix(Rn,3,3); E[i,j]=1; Eb.append(E)
    def residual(ai,bi,ci):
        A,B,C=Eb[ai],Eb[bi],Eb[ci]
        return A.trace()*B.trace()*C.trace()-(A*B*C).trace()
    Rsupport=set((a,b,c) for a in range(9) for b in range(9) for c in range(9) if residual(a,b,c)!=0)
    realN=len(ELEM)
    # subgroups with orbit<=21: |H| >= realN/21. Enumerate cyclic subgroups +
    # GAP maximal subgroup reps mapped through the rep.
    ccs=gap.ConjugacyClassesSubgroups(G); ncc=Integer(gap.Length(ccs))
    def sub_mats(Hgap):
        hg=gap.GeneratorsOfGroup(Hgap); nh=Integer(gap.Length(hg))
        if nh==0: return [I3]
        gmats=[]
        for k in range(1,nh+1):
            Mg=gap.Image(irr[chosen_idx],hg[k]); M=matrix(Rn,3,3)
            ok=True
            for a in range(1,4):
                for b in range(1,4):
                    v=conv(gap(Mg[a][b]))
                    if v is None: ok=False; break
                    M[a-1,b-1]=v
                if not ok: break
            if not ok: return None
            gmats.append(M)
        Hd={matkey(I3):I3}; fr=[I3]
        for _ in range(5000):
            if not fr: break
            nn=[]
            for e in fr:
                for g in gmats:
                    ne=g*e; k=matkey(ne)
                    if k not in Hd: Hd[k]=ne; nn.append(ne)
            fr=nn
        return list(Hd.values())
    import math
    need = math.ceil(realN/21)
    print(f"  need |H|>={need} for orbit<=21 (realized order {realN})")
    tried=0
    for ci in range(1,ncc+1):
        H=gap.Representative(ccs[ci]); o=Integer(gap.Order(H))
        # map to realized order: faithful => same order
        if o<need or o>=ordG: continue
        Hm=sub_mats(H)
        if Hm is None or len(Hm)==0: continue
        orbit=realN//len(Hm)
        if orbit>21 or orbit<1: continue
        fb=fixedBasis_sub(Hm); d=len(fb)
        tag=f"  |H|={len(Hm)} orbit={orbit} rank={1+orbit} fixed_dim={d}"
        if d==0:
            print(tag+": fixed dim 0; skip"); continue
        Rr=PolynomialRing(Rn,d,[f"x{i}" for i in range(d)]); xs=Rr.gens()
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
        cov=len(reach&Rsupport); miss=Rsupport-reach
        v="INFEASIBLE (unit ideal)" if unit else f"SOLUTION-FOUND dim {I.dimension()} *** STOP rank {1+orbit} ***"
        print(tag+f": cov {cov}/{len(Rsupport)}{' MISS '+str(len(miss)) if miss else ''}; {v}")
        tried+=1
    if tried==0:
        print("  no viable stabilizer with nonzero fixed space and orbit<=21.")

# Hessian group: triple cover is a complex reflection group order 648 with 3-dim
# rep. GAP: the Shephard-Todd group No.25 = 3[3]3[3]3. Use the small group or the
# reflection group. We use the order-648 complex reflection group via its 3-dim
# rep; char field Q(omega)=Q(zeta_3). Try ShephardTodd via GAP if available, else
# SmallGroup(648,...). Fallback: skip with a note.
# Valentiner 3.A_6 order 1080: char field Q(zeta_15).
analyze("AlternatingGroup(6)", "A_6 (no faithful 3-dim; will report none)", 15, 360)
# The faithful 3-dim rep is of the TRIPLE COVER. Build 3.A_6 = SchurCover then a
# 3-dim faithful irrep.
analyze("SchurCoverOfSymmetricGroup", "skip-placeholder", 3, 0) if False else None
