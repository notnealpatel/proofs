# mcupper_ranks.sage
# LINCHPIN: does the n=4 "partial-multiplier don't-care saving" (pMC=2 < MC=3)
# transfer to n=8?  We measure the BILINEAR don't-care freedom of the tower
# output multiplier as a function of tower size, via the rank of the
# realizable-set evaluation matrix.
#
# Setup: L = GF(2^{2k}) = K[Y]/(Y^2+Y+nu), K = GF(2^k).  For x = a*Y + b
# (a,b in K), norm d = nu*a^2 + a*b + b^2 in K, w = d^{-1} (=0 if d=0).
# Output multipliers (poly-basis tower inversion): p = a, q = a+b, outputs
# p*w and q*w in K.
#
# A single-side output multiplier is a bilinear map K x K -> K,
# (p, w) |-> p*w.  Over GF(2) its coordinate bits are bilinear forms in the
# k bits of p and k bits of w: k^2 monomials p_i*w_j.  The "realizable set"
# is R = {(p(x), w(x)) : x in L*} (union {0}).  A bilinear output stage that
# is CORRECT on R is FORCED equal to the true multiplier everywhere iff the
# k^2 monomials {p_i*w_j} are linearly independent as functions on R, i.e.
# iff the |R| x k^2 evaluation matrix has full column rank k^2.
#   rank < k^2  <=>  bilinear don't-care freedom exists (n=4 saving mechanism)
#   rank = k^2  <=>  NO bilinear don't-care freedom (mechanism dead)
#
# We report per-side rank (p*w) and joint rank ({p*w, q*w} coeff span, 2k^2)
# for k = 1,2,3,4 and, at k=4, for all 8 admissible nu.  Deterministic.

def analyze(k, nu_choices=None, verbose=True):
    R.<T> = GF(2)[]
    # build K = GF(2^k)
    K = GF(2^k, 'z', modulus=None) if k > 1 else GF(2)
    if k == 1:
        Kelts = [GF(2)(0), GF(2)(1)]
    else:
        Kelts = list(K)
    # admissible nu: y^2+y+nu irreducible over K  <=>  Tr_{K/GF2}(nu) = 1
    def trace_to_gf2(e):
        if k == 1: return e
        return e.trace()  # absolute trace K->GF(2)
    good_nu = [nu for nu in Kelts if nu != 0 and trace_to_gf2(nu) == 1]
    if nu_choices is None: nu_choices = good_nu
    results = []
    for nu in nu_choices:
        # coordinate-bit extractor for a K-element: k bits
        def bits(e):
            if k == 1: return [ZZ(e)]
            v = e.polynomial().coefficients(sparse=False)
            v = v + [K(0).polynomial()]*0
            cs = list(e.polynomial().coefficients(sparse=False))
            cs += [0]*(k - len(cs))
            return [ZZ(c) for c in cs]
        # enumerate x = a*Y + b over L* : (a,b) in K^2 not both zero
        rowsP = []   # per-side: monomials p_i * w_j, p=a
        rowsQ = []   # per-side q=a+b
        rowsJ = []   # joint: [a_i*w_j , b_i*w_j]  (spans both sides)
        realizable_pw = set()
        for a in Kelts:
            for b in Kelts:
                if a == 0 and b == 0: continue
                d = nu*a*a + a*b + b*b
                w = d^(-1) if d != 0 else K(0)  # d=0 -> off-domain sentinel
                pbits = bits(a)
                qbits = bits(a + b)
                wbits = bits(w)
                rowsP.append([pbits[i]*wbits[j] for i in range(k) for j in range(k)])
                rowsQ.append([qbits[i]*wbits[j] for i in range(k) for j in range(k)])
                rowsJ.append([pbits[i]*wbits[j] for i in range(k) for j in range(k)]
                             +[bits(b)[i]*wbits[j] for i in range(k) for j in range(k)])
                realizable_pw.add((tuple(pbits), tuple(wbits)))
        MP = matrix(GF(2), rowsP); MQ = matrix(GF(2), rowsQ); MJ = matrix(GF(2), rowsJ)
        rP, rQ, rJ = MP.rank(), MQ.rank(), MJ.rank()
        ndc_side = k*k - rP
        ndc_joint = 2*k*k - rJ
        results.append((nu, rP, rQ, rJ, k*k, 2*k*k, len(realizable_pw)))
        if verbose:
            print("  nu=%-6s per-side rank(p)=%d/%d  rank(q)=%d/%d  joint rank=%d/%d  |realiz (p,w)|=%d  bilinear-DC-freedom: side=%d joint=%d"
                  % (str(nu), rP, k*k, rQ, k*k, rJ, 2*k*k, len(realizable_pw), ndc_side, ndc_joint))
    return results

print("== bilinear don't-care freedom of tower output multiplier vs tower size ==")
print("(DC-freedom > 0  <=>  a bilinear circuit correct on-domain can deviate off-domain,")
print(" the n=4 partial-multiplier saving mechanism; = 0 means mechanism is DEAD.)")
for k in [1, 2, 3, 4]:
    print("k=%d  (K=GF(2^%d), L=GF(2^%d)):" % (k, k, 2*k))
    analyze(k)

print()
print("== SUMMARY across all admissible nu at k=4 (n=8) ==")
res4 = analyze(4, verbose=False)
sides = set((r[1], r[2]) for r in res4)
joints = set(r[3] for r in res4)
print("  per-side ranks over all 8 nu:", sorted(set(r[1] for r in res4)),
      " (full = 16)")
print("  joint ranks over all 8 nu:", sorted(joints), " (full = 32)")
print("  => n=8 bilinear don't-care freedom (side):",
      [16 - r for r in sorted(set(r[1] for r in res4))])
print("  => n=8 bilinear don't-care freedom (joint):",
      [32 - r for r in sorted(joints)])
