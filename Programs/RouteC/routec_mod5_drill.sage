# Route C, program 5b: drill into the mod-5 coset structure found by
# routec_torus_slices.sage.  The index-5 quotient of F* is detected by
# the invariant chi(a) = a^51, which lands in the group mu_5 of fifth
# roots of unity inside GF(16) subset GF(256).  Questions:
#   (1) per-coset means of weight, savings, AND raw Paar-1 cost on
#       both 1D slices — does cost itself carry the harmonic, or only
#       weight (savings being 0.96-entangled with weight)?
#   (2) full 65,025-entry table: 5x5 cell means of the closed-form
#       weight w(a,a') by (chi(a), chi(a')) — is the 2D structure a
#       product of the two 1D harmonics or something richer?

from collections import Counter

set_random_seed(0)

R.<x> = PolynomialRing(GF(2))
F.<z> = GF(2^8, modulus=x^8 + x^4 + x^3 + x + 1)

def vec(u):
    c = u.polynomial().list()
    return vector(GF(2), c + [0]*(8 - len(c)))

def matof(f):
    return matrix(GF(2), [vec(f(z^j)) for j in range(8)]).transpose()

mult_cache = {a: matof(lambda u, a=a: a*u) for a in F if a != 0}
mult = lambda a: mult_cache[a]

Aff = matrix(GF(2), 8, 8,
             lambda i, j: 1 if (j - i) % 8 in (0, 4, 5, 6, 7) else 0)

c01, c02, c03 = F(1), z, z + 1
MCC = [[c02, c03, c01, c01],
       [c01, c02, c03, c01],
       [c01, c01, c02, c03],
       [c03, c01, c01, c02]]

def bd4(B):
    return block_diagonal_matrix([B]*4, subdivide=False)

MC32  = block_matrix(4, 4, [mult(MCC[i][j]) for i in range(4) for j in range(4)],
                     subdivide=False)
Aff32 = bd4(Aff)
mult32 = lambda a: bd4(mult(a))

def Lam(a, ap):
    return mult32(ap) * MC32 * Aff32 * mult32(a)

def paar1(M):
    rows = [set(j for j in range(M.ncols()) if M[i, j])
            for i in range(M.nrows())]
    gates, nsig = 0, M.ncols()
    while any(len(r) >= 2 for r in rows):
        cnt = Counter()
        for r in rows:
            rr = sorted(r)
            for u in range(len(rr)):
                for v in range(u + 1, len(rr)):
                    cnt[(rr[u], rr[v])] += 1
        (i, j), _ = max(cnt.items(), key=lambda t: (t[1], -t[0][0], -t[0][1]))
        gates += 1
        for r in rows:
            if i in r and j in r:
                r.discard(i); r.discard(j); r.add(nsig)
        nsig += 1
    return gates

g = F.multiplicative_generator()
Fstar = [a for a in F if a != 0]

# chi(a) = index of a^51 in mu_5 (dlog mod 5 in generator order)
mu5 = sorted(set(a^51 for a in Fstar), key=lambda t: 0 if t == 1 else 1)
# stable labeling: chi(g^i) = i mod 5
chi = {}
for i in range(255):
    chi[g^i] = i % 5

print("(1) per-coset means on the 1D slices")
for (label, mk) in [("a' = 1, sweep a", lambda a: Lam(a, F(1))),
                    ("a = 1, sweep a'", lambda a: Lam(F(1), a))]:
    acc = {r: [0, 0, 0, 0] for r in range(5)}  # n, w, sav, cost
    for i in range(255):
        a = g^i
        L = mk(a)
        w = sum(sum(map(int, r)) for r in L.rows())
        c = paar1(L)
        t = acc[i % 5]
        t[0] += 1; t[1] += w; t[2] += w - 32 - c; t[3] += c
    print(" slice %s:" % label)
    print("   coset   n    mean_w   mean_sav  mean_cost")
    for r in range(5):
        n, sw, ss, sc = acc[r]
        print("     %d    %2d    %6.1f   %6.1f    %6.1f"
              % (r, n, float(sw/n), float(ss/n), float(sc/n)))

print()
print("(2) full-table 5x5 weight decomposition (closed form)")
W8 = {}
for u in Fstar:
    Mu = mult(u) * Aff
    for v in Fstar:
        W8[(u, v)] = sum(sum(map(int, r)) for r in (Mu * mult(v)).rows())

cell = {(i, j): [0, 0] for i in range(5) for j in range(5)}
for a in Fstar:
    for ap in Fstar:
        w = 4*W8[(c02*ap, a)] + 4*W8[(c03*ap, a)] + 8*W8[(ap, a)]
        t = cell[(chi[a], chi[ap])]
        t[0] += 1; t[1] += w
print("   rows chi(a), cols chi(a'): mean weight per cell")
print("        " + "".join("  ch'=%d " % j for j in range(5)))
grand = sum(t[1] for t in cell.values()) / sum(t[0] for t in cell.values())
for i in range(5):
    print("  ch=%d " % i + "".join(" %6.1f" % float(cell[(i, j)][1]/cell[(i, j)][0])
                                   for j in range(5)))
print("   grand mean %.1f" % float(grand))
# additivity check: cell(i,j) vs rowmean + colmean - grand
rowm = [sum(cell[(i, j)][1] for j in range(5)) / sum(cell[(i, j)][0] for j in range(5))
        for i in range(5)]
colm = [sum(cell[(i, j)][1] for i in range(5)) / sum(cell[(i, j)][0] for i in range(5))
        for j in range(5)]
resid = max(abs(float(cell[(i, j)][1]/cell[(i, j)][0] - rowm[i] - colm[j] + grand))
            for i in range(5) for j in range(5))
print("   max |interaction residual| after additive model: %.2f" % resid)
