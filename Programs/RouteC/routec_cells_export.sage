# Route C, program 4a: select the three BP-contrast cells and export
# their gauged matrices for the Go xPaar engine.
#
#   cell "low":      bottom 15 gauges by EXACT weight over the full
#                    65,025-entry table (weight computed in closed
#                    form: w(a,a') = 4 W8[02a',a] + 4 W8[03a',a]
#                    + 8 W8[a',a], W8[u,v] = wt(mult_u.Aff.mult_v);
#                    identity verified against direct construction).
#   cell "contrast": the max-|cost gap| pair at |weight gap| <= 8
#                    from the seeded 145-gauge Paar-1 table of
#                    program 2, plus the 20 sample gauges nearest in
#                    weight (the equal-weight band).
#   cell "control":  30 fresh random gauges (seeded, disjoint).
#
# Output: JSON at the session scratchpad, one record per gauge with
# rows as uint32 bitmasks (bit j = column j) and the Sage Paar-1
# cost for cross-checking the Go engine's deterministic mode.

import json
from collections import Counter

set_random_seed(0)
SAMPLES = 144
OUT = "/tmp/claude-1000/-home-exedev-p-proofs/4c4b9d3c-93da-41fa-8589-a4a4bd09d953/scratchpad/routec_cells.json"

R.<x> = PolynomialRing(GF(2))
F.<z> = GF(2^8, modulus=x^8 + x^4 + x^3 + x + 1)

def vec(u):
    c = u.polynomial().list()
    return vector(GF(2), c + [0]*(8 - len(c)))

def f2byte(u):
    return sum(int(t) << i for i, t in enumerate(vec(u)))

byte2f_tab = {f2byte(a): a for a in F}
def byte2f(b): return byte2f_tab[b]

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

# ---- full-table weight scan -----------------------------------------
W8 = {}
for u in Fstar:
    Mu = mult(u) * Aff
    for v in Fstar:
        W8[(f2byte(u), f2byte(v))] = sum(sum(map(int, r))
                                         for r in (Mu * mult(v)).rows())

def w32(ab, apb):
    ap = byte2f(apb)
    return (4*W8[(f2byte(c02*ap), ab)] + 4*W8[(f2byte(c03*ap), ab)]
            + 8*W8[(apb, ab)])

# identity check on 5 random pairs
for _ in range(5):
    a, ap = choice(Fstar), choice(Fstar)
    direct = sum(sum(map(int, r)) for r in Lam(a, ap).rows())
    assert direct == w32(f2byte(a), f2byte(ap)), "weight formula broken"
print("weight formula verified against direct construction")

allw = sorted(((w32(ab, apb), ab, apb)
               for ab in range(1, 256) for apb in range(1, 256)))
print("full-table weight range: [%d, %d]" % (allw[0][0], allw[-1][0]))
low = allw[:15]
print("low tail:", [(("%02x" % a), ("%02x" % p), w) for w, a, p in low])

# ---- reproduce the seeded 145-gauge sample and its Paar-1 costs -----
gauges = [(F(1), F(1))]
seen = {(1, 1)}
while len(gauges) < SAMPLES + 1:
    a, ap = choice(Fstar), choice(Fstar)
    key = (f2byte(a), f2byte(ap))
    if key not in seen:
        seen.add(key)
        gauges.append((a, ap))

sample = []
for a, ap in gauges:
    ab, apb = f2byte(a), f2byte(ap)
    sample.append((ab, apb, w32(ab, apb), paar1(Lam(a, ap))))

# max-contrast pair at |dw| <= 8
best = None
for i in range(len(sample)):
    for j in range(i+1, len(sample)):
        if abs(sample[i][2] - sample[j][2]) <= 8:
            gap = abs(sample[i][3] - sample[j][3])
            if best is None or gap > best[0]:
                best = (gap, sample[i], sample[j])
gap, g1, g2 = best
print("max equal-weight contrast: gap %d XOR  %02x/%02x (w=%d,c=%d) vs %02x/%02x (w=%d,c=%d)"
      % (gap, g1[0], g1[1], g1[2], g1[3], g2[0], g2[1], g2[2], g2[3]))
wmid = (g1[2] + g2[2]) / 2
band = sorted((s for s in sample if (s[0], s[1]) not in
               {(g1[0], g1[1]), (g2[0], g2[1])}),
              key=lambda s: abs(s[2] - wmid))[:20]

# controls: 30 fresh
controls = []
cseen = set(seen) | {(a, p) for _, a, p in low}
while len(controls) < 30:
    a, ap = choice(Fstar), choice(Fstar)
    key = (f2byte(a), f2byte(ap))
    if key not in cseen:
        cseen.add(key)
        controls.append(key)

# ---- export ---------------------------------------------------------
def rows_u32(M):
    return [sum(int(M[i, j]) << j for j in range(32)) for i in range(32)]

records = []
def add(ab, apb, cell, cost=None):
    L = Lam(byte2f(ab), byte2f(apb))
    records.append(dict(a=int(ab), ap=int(apb), cell=cell,
                        weight=int(w32(ab, apb)),
                        paar1=int(cost) if cost is not None
                              else int(paar1(L)),
                        rows=[int(t) for t in rows_u32(L)]))

for w, ab, apb in low:
    add(ab, apb, "low")
add(g1[0], g1[1], "contrast", g1[3])
add(g2[0], g2[1], "contrast", g2[3])
for ab, apb, w, c in band:
    add(ab, apb, "contrast", c)
for ab, apb in controls:
    add(ab, apb, "control")

with open(OUT, "w") as fh:
    json.dump(records, fh)
print("exported %d gauges (%d low, %d contrast, %d control) -> %s"
      % (len(records), 15, 22, 30, OUT))
