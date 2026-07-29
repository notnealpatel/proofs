# Route C (concrete track), program 3: decompose Paar-1 SAVINGS, not
# cost, on the gauge orbit of Lambda(a,a') = mult_{a'}.MC.Aff.mult_a.
#
# Identity (exact): paar1 = weight - 32 - savings, since the naive
# SLP costs sum(w_i - 1) = weight - 32 and every Paar merge chosen
# with frequency f saves f-1.  So savings is precisely the weight-
# blind component of the Program-2 spread, and cancellation
# statistics are excluded as explanations BY CAUSALITY: Paar-1
# cannot cancel.
#
# Predictors (all exact, free, second-order):
#   * 32x32 column-coincidence Gram G = Lambda^T.Lambda over ZZ;
#     off-diagonal entry (j,k) = #rows containing both columns j,k.
#     Stats: max, sum of top-k (k = 32, 96, 160), total.
#   * 8x8 core N(a,a') = mult_{a'}.Aff.mult_a (granularity admitted
#     by the S6 factorization Lambda = MC32.diag4(N)): same stats.
#   * weight itself, for partialling.
#
# Pre-registered (session 2026-07-23): 32x32 granularity dominates
# the 8x8 core; sum-of-top-96 is the best single predictor; partial
# Spearman(savings, top96 | weight) >= 0.5 at 60% confidence;
# max-coincidence alone weak (~0.3).
#
# Same seed and sampling code as routec_gauge_invariants.sage, so
# the 145 gauges (and Paar-1 values) reproduce exactly.

from collections import Counter

set_random_seed(0)
SAMPLES = 144

R.<x> = PolynomialRing(GF(2))
F.<z> = GF(2^8, modulus=x^8 + x^4 + x^3 + x + 1)

def vec(u):
    c = u.polynomial().list()
    return vector(GF(2), c + [0]*(8 - len(c)))

def f2byte(u):
    return sum(int(t) << i for i, t in enumerate(vec(u)))

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

Fstar = [a for a in F if a != 0]

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

# ---- same gauge sample as program 2 ---------------------------------
gauges = [(F(1), F(1))]
seen = {(f2byte(F(1)), f2byte(F(1)))}
while len(gauges) < SAMPLES + 1:
    a, ap = choice(Fstar), choice(Fstar)
    key = (f2byte(a), f2byte(ap))
    if key not in seen:
        seen.add(key)
        gauges.append((a, ap))

# ---- per-gauge response + predictors --------------------------------
def offdiag_sorted(M):
    Z = M.change_ring(ZZ)
    G = Z.transpose() * Z
    return sorted((G[i, j] for i in range(G.nrows())
                   for j in range(i + 1, G.ncols())), reverse=True)

rows_out = []
for a, ap in gauges:
    L = Lam(a, ap)
    w = sum(sum(map(int, r)) for r in L.rows())
    cost = paar1(L)
    sav = w - 32 - cost
    off32 = offdiag_sorted(L)
    N = mult(ap) * Aff * mult(a)
    off8 = offdiag_sorted(N)
    rows_out.append(dict(
        a=f2byte(a), ap=f2byte(ap), w=w, cost=cost, sav=sav,
        max32=off32[0], top32=sum(off32[:32]), top96=sum(off32[:96]),
        top160=sum(off32[:160]), tot32=sum(off32),
        max8=off8[0], tot8=sum(off8),
    ))

print("  a   a'    w   cost  sav  max32 top32 top96 top160 tot32 max8 tot8")
for r in rows_out:
    print(" %02x   %02x  %4d  %4d  %4d   %3d  %5d %5d  %5d %6d  %3d  %4d"
          % (r['a'], r['ap'], r['w'], r['cost'], r['sav'], r['max32'],
             r['top32'], r['top96'], r['top160'], r['tot32'],
             r['max8'], r['tot8']))

# ---- correlations ---------------------------------------------------
def spearman(xs, ys):
    def rk(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r, i = [0]*len(v), 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j+1]] == v[order[i]]:
                j += 1
            for t in range(i, j + 1):
                r[order[t]] = (i + j)/2 + 1
            i = j + 1
        return r
    rx, ry = rk(xs), rk(ys)
    n = len(xs)
    mx, my = sum(rx)/n, sum(ry)/n
    num = sum((rx[i]-mx)*(ry[i]-my) for i in range(n))
    den = sqrt(sum((rx[i]-mx)^2 for i in range(n)) *
               sum((ry[i]-my)^2 for i in range(n)))
    return float(num/den)

def residual(ys, xs):
    n = len(ys)
    mx, my = sum(xs)/n, sum(ys)/n
    b = sum((xs[i]-mx)*(ys[i]-my) for i in range(n)) / \
        sum((xs[i]-mx)^2 for i in range(n))
    return [ys[i] - my - b*(xs[i]-mx) for i in range(n)]

W   = [r['w']    for r in rows_out]
C   = [r['cost'] for r in rows_out]
S   = [r['sav']  for r in rows_out]
preds = ['max32', 'top32', 'top96', 'top160', 'tot32', 'max8', 'tot8']

print()
print("response = savings (= weight - 32 - paar1); n =", len(rows_out))
print("Spearman(savings, weight) = %.3f   [entanglement baseline]"
      % spearman(S, W))
print()
print("predictor   raw rho(sav)   partial rho(sav|w)")
Sres = residual(S, W)
for p in preds:
    X = [r[p] for r in rows_out]
    print("  %-8s     %6.3f          %6.3f"
          % (p, spearman(S, X), spearman(Sres, residual(X, W))))

# two-term OLS surrogate for COST: cost ~ alpha*w + beta*top96 + c
def ols2_r2(ys, x1, x2):
    n = len(ys)
    M = matrix(RDF, [[x1[i], x2[i], 1] for i in range(n)])
    yv = vector(RDF, ys)
    coef = (M.transpose()*M).solve_right(M.transpose()*yv)
    fit = M*coef
    my = sum(ys)/n
    ssr = sum((fit[i]-ys[i])^2 for i in range(n))
    sst = sum((ys[i]-my)^2 for i in range(n))
    return 1 - ssr/sst, coef

def ols1_r2(ys, xs):
    res = residual(ys, xs)
    my = sum(ys)/len(ys)
    return 1 - sum(t^2 for t in res)/sum((y-my)^2 for y in ys)

print()
print("OLS R^2 for COST:  weight alone = %.3f" % ols1_r2(C, W))
for p in ['top96', 'top160', 'tot32']:
    r2, coef = ols2_r2(C, W, [r[p] for r in rows_out])
    print("                   weight + %-6s = %.3f  (coef %.4f, %.4f)"
          % (p, r2, coef[0], coef[1]))
