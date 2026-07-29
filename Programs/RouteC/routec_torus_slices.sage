# Route C, program 5: 1D slices of the cost surface along the
# multiplicative torus.  Fix one side of the gauge, sweep the other
# over all of F* ordered by discrete log (generator g, ord(g)=255),
# and decompose both components — weight and Paar-1 savings — against
# the subgroup lattice of Z/255 = Z/3 x Z/5 x Z/17.
#
# Pre-registered (2026-07-23): no periodicity aligned with the
# 3/5/17 coset structure in either component (65% confidence); if
# structure appears anywhere it appears in weight, not savings.
#
# Test: for each slice and each component, one-way ANOVA-style
# variance ratio across cosets of the index-3, index-5, index-17
# quotients (grouping i mod 3 / mod 5 / mod 17 in dlog coordinates,
# i.e. cosets of the subgroups of order 85, 51, 15), F-statistic =
# between-group mean square / within-group mean square, plus the
# Frobenius pairing rho(f(i), f(2i mod 255)) (a -> a^2).

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
assert g.multiplicative_order() == 255
print("generator g =", hex(sum(int(t) << i for i, t in enumerate(vec(g)))))

def slice_stats(name, fvals):
    """fvals[i] = component value at g^i, i = 0..254 (dlog order)."""
    n = 255
    mean = sum(fvals)/n
    var = sum((v-mean)^2 for v in fvals)/n
    print("  %s: mean %.1f  sd %.1f" % (name, float(mean), float(sqrt(var))))
    for m in (3, 5, 17):
        groups = [[fvals[i] for i in range(n) if i % m == r] for r in range(m)]
        gm = [sum(G)/len(G) for G in groups]
        ssb = sum(len(G)*(gm[k]-mean)^2 for k, G in enumerate(groups))
        ssw = sum(sum((v-gm[k])^2 for v in G) for k, G in enumerate(groups))
        Fstat = (ssb/(m-1)) / (ssw/(n-m))
        print("    cosets mod %2d: F = %.2f   (F ~ 1 noise; F >> 1 structure)"
              % (m, float(Fstat)))
    # Frobenius pairing: value at a vs a^2 (i -> 2i mod 255)
    xs = fvals
    ys = [fvals[(2*i) % 255] for i in range(n)]
    mx, my = sum(xs)/n, sum(ys)/n
    num = sum((xs[i]-mx)*(ys[i]-my) for i in range(n))
    den = sqrt(sum((v-mx)^2 for v in xs) * sum((v-my)^2 for v in ys))
    print("    Frobenius pairing corr(f(a), f(a^2)) = %.3f" % float(num/den))

for (label, fixed, side) in [("a' = 1, sweep a", F(1), "in"),
                             ("a = 1, sweep a'", F(1), "out")]:
    print("slice:", label)
    W, S = [], []
    for i in range(255):
        a = g^i
        L = Lam(a, fixed) if side == "in" else Lam(fixed, a)
        w = sum(sum(map(int, r)) for r in L.rows())
        c = paar1(L)
        W.append(w)
        S.append(w - 32 - c)
    slice_stats("weight ", W)
    slice_stats("savings", S)
    print("    weight  slice head:", [int(t) for t in W[:20]])
    print("    savings slice head:", [int(t) for t in S[:20]])
