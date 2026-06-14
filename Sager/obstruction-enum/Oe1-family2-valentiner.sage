# Oe1 Family 2: Valentiner group 3.A_6 (order 1080) feasibility.
# 3.A_6 has four faithful 3-dim complex irreps (Valentiner action on CP^2). Build
# via the Schur cover of A_6 (order 2160 = 6.A_6), find a 3-dim faithful irrep
# (it factors through 3.A_6), realize over its cyclotomic splitting field, and
# solve the GM single-orbit systems for stabilizers with orbit<=21.

def conv_factory(Rn):
    def conv(s):
        s=str(s)
        if 'E(' in s:
            try: return Rn(sage_eval(s.replace('E(','CyclotomicField(').replace(')',').gen()')))
            except Exception: return None
        try: return Rn(QQ(s))
        except Exception: return None
    return conv

# Schur cover of A_6 (GAP). Its order is 2160 (= 6.A_6). A faithful 3-dim irrep
# of 3.A_6 lifts to a 3-dim irrep of 6.A_6 (on which the central involution acts
# as +-1). We search 6.A_6's irreps for a 3-dim one realizable over a cyclotomic
# field, build the realized matrix group (its order is 1080 if the kernel is the
# Z_2, giving exactly 3.A_6), and proceed.
for cycloN in [15, 60, 45, 105, 9]:
    Rn=CyclotomicField(cycloN); conv=conv_factory(Rn)
    G=gap.SchurCover(gap.AlternatingGroup(6))
    ordG=Integer(gap.Order(G))
    irr=gap.IrreducibleRepresentations(G); nirr=Integer(gap.Length(irr))
    Ggens=gap.GeneratorsOfGroup(G); ng=Integer(gap.Length(Ggens))
    found=False
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
        if not ok: continue
        # realize
        def matkey(M): return tuple(M.list())
        I3=identity_matrix(Rn,3)
        elems={matkey(I3):I3}; frontier=[I3]
        for _ in range(50000):
            if not frontier: break
            new=[]
            for e in frontier:
                for g in gmats:
                    ne=g*e; kk=matkey(ne)
                    if kk not in elems: elems[kk]=ne; new.append(ne)
            frontier=new
        ELEM=list(elems.values())
        print(f"cycloN={cycloN}: 3-dim irrep #{i} realized, group order {len(ELEM)} (3.A_6 => 1080)")
        found=True
        # proceed with feasibility on this realization
        def matorder(M):
            P=M; o=1
            while P!=I3 and o<3000: P=P*M; o+=1
            return o
        sig=[M for M in ELEM if matorder(M)==3]
        if not sig: print("  no order-3 elt; skip"); break
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
        realN=len(ELEM)
        import math
        need=math.ceil(realN/21)
        print(f"  need |H|>={need} for orbit<=21")
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
        tried=0
        for ci in range(1,ncc+1):
            H=gap.Representative(ccs[ci]); o=Integer(gap.Order(H))
            if o<need or o>=ordG: continue
            Hm=sub_mats(H)
            if not Hm: continue
            orbit=realN//len(Hm)
            if orbit>21 or orbit<1: continue
            fb=fixedBasis_sub(Hm); d=len(fb)
            tag=f"  |H|={len(Hm)} orbit={orbit} rank={1+orbit} fixed_dim={d}"
            if d==0: print(tag+": dim0; skip"); continue
            Rr=PolynomialRing(Rn,d,[f"x{i}" for i in range(d)]); xs=Rr.gens()
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
            cov=len(reach&Rsupport); miss=Rsupport-reach
            v="INFEASIBLE (unit ideal)" if unit else f"SOLUTION-FOUND dim {I.dimension()} *** STOP rank {1+orbit} ***"
            print(tag+f": cov {cov}/{len(Rsupport)}{' MISS '+str(len(miss)) if miss else ''}; {v}")
            tried+=1
        if tried==0: print("  no viable stabilizer orbit<=21 with nonzero fixed space.")
        break
    if found: break
if not found:
    print("could not realize a 3-dim faithful irrep of 3.A_6 over the tried cyclotomic fields")
