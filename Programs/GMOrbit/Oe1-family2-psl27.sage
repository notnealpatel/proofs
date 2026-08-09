# Oe1 Family 2: PSL(2,7) (order 168) GM-ansatz feasibility for <3,3,3>.
# PSL(2,7) ~ PSL(3,2) ~ GL(3,2) has a faithful 3-dim COMPLEX irrep over Q(sqrt-7)
# (and its conjugate). It is the automorphism group of the Fano plane PG(2,2) and
# of the Klein quartic. Order 168 = 2^3 * 3 * 7, so it has order-3 elements (the
# twist sigma exists). It is 2-transitive on the 7 Fano points (NOT 3-transitive).
#
# Cleanest concrete model: PSL(2,7) ~ GL(3,2) = the 3x3 invertible matrices over
# GF(2). But we need the 3-dim COMPLEX irrep (a lift), not the GF(2) action. Get
# the irrep from GAP's IrreducibleRepresentations over a splitting field, then
# realize over Q(sqrt-7).
#
# Use GAP to obtain the 3-dim irreducible representation matrices, then port to
# Sage matrices over the cyclotomic field (which contains sqrt-7 = a Gauss sum of
# 7th roots of unity).

R7 = CyclotomicField(7)   # contains sqrt(-7); splitting field for PSL(2,7) 3-dim irrep
z = R7.gen()

# Get PSL(2,7) and its irreducible representations from GAP.
G = gap.PSL(2,7)
print("PSL(2,7) order:", gap.Order(G))
irr = gap.IrreducibleRepresentations(G)   # over a splitting field (cyclotomic)
nirr = Integer(gap.Length(irr))
print("number of irreps:", nirr)
# find a 3-dimensional one
dims=[]
three_idx=None
for i in range(1, nirr+1):
    rep = irr[i]
    gens = gap.GeneratorsOfGroup(G)
    img = gap.Image(rep, gens[1])
    d = Integer(gap.Length(img))   # dimension = matrix size
    dims.append(d)
    if d==3 and three_idx is None:
        three_idx=i
print("irrep dims:", dims)
print("first 3-dim irrep index:", three_idx)
if three_idx is None:
    print("NO 3-dim irrep found -- unexpected; PSL(2,7) has two 3-dim irreps.")
else:
    rep = irr[three_idx]
    Ggens = gap.GeneratorsOfGroup(G)
    ngens = Integer(gap.Length(Ggens))
    # convert GAP matrices to Sage matrices over the cyclotomic field
    def gapmat_to_sage(M):
        rows = Integer(gap.Length(M))
        cols = Integer(gap.Length(M[1]))
        entries=[]
        for a in range(1,rows+1):
            for b in range(1,cols+1):
                entries.append(R7(gap.Image(M[a][b])) if False else R7(sage_eval(str(gap(M[a][b])), locals={'E':lambda n: CyclotomicField(n).gen()})) )
        return matrix(R7, rows, cols, entries)
    # simpler: pull the whole image group and its generators numerically
    genmats=[]
    for k in range(1,ngens+1):
        Mg = gap.Image(rep, Ggens[k])
        rows = Integer(gap.Length(Mg))
        M = matrix(R7, rows, rows)
        for a in range(1,rows+1):
            for b in range(1,rows+1):
                # GAP entry may be a cyclotomic; convert via its string in E(n) form
                val = gap(Mg[a][b])
                s = str(val)
                M[a-1,b-1] = R7(sage_eval(s.replace('E(','CyclotomicField(').replace(')',').gen()' ) )) if 'E(' in s else R7(QQ(s))
        genmats.append(M)
    print("got", len(genmats), "generator matrices of size", genmats[0].nrows())
    # build the group by BFS
    def matkey(M): return tuple(M.list())
    I3=identity_matrix(R7,3)
    elems={matkey(I3):I3}; frontier=[I3]
    for _ in range(5000):
        if not frontier: break
        new=[]
        for e in frontier:
            for g in genmats:
                ne=g*e; k=matkey(ne)
                if k not in elems: elems[k]=ne; new.append(ne)
        frontier=new
    ELEM=list(elems.values())
    print("realized 3-dim rep group order:", len(ELEM), "(expect 168)")
