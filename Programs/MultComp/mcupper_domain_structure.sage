# mcupper_domain_structure.sage
# Pin ONE GF(2^4) representation.  Build the realizable domains and output
# truth tables for the partial multipliers, and measure the don't-care
# freedom that a NON-bilinear circuit could exploit.  Export self-checking
# data (with cross-check vectors) for the search harness.
#
# Representation (pinned end-to-end):
#   K = GF(2^4) = GF(2)[t]/(t^4 + t + 1);  element bits: bit i = coeff of t^i.
#   L = GF(2^8) = K[Y]/(Y^2 + Y + nu), nu chosen with Tr_{K/GF2}(nu)=1
#     (y^2+y+nu irreducible).  x = a*Y + b, a,b in K.
#   norm  d = nu*a^2 + a*b + b^2  in K ;  w = d^{-1} (d != 0 on realizable set).
#   outputs:  p-side = a*w ;  q-side = (a+b)*w.  (poly-basis tower inversion)
#
# Cross-check vectors are printed so any consumer of the exported data can
# confirm it is in THIS representation (wrong-basis failure is silent).

import json

R.<t> = GF(2)[]
K.<z> = GF(2^4, modulus=t^4 + t + 1)
def kbits(e):
    cs = list(e.polynomial().coefficients(sparse=False)); cs += [0]*(4-len(cs))
    return [int(c) for c in cs]
def kfrom(bits): return K(sum((bits[i])*z^i for i in range(4)))
def kint(e): return sum(kbits(e)[i]<<i for i in range(4))

# admissible nu: Tr(nu)=1
nus = [e for e in K if e != 0 and e.trace() == 1]
nu = nus[0]
print("pinned rep: K=GF(2)[t]/(t^4+t+1); nu =", nu, "(int %d); Tr(nu)=%d" % (kint(nu), nu.trace()))

# verify y^2+y+nu irreducible
S.<Y> = K[]
assert (Y^2 + Y + nu).is_irreducible(), "nu bad"

# ---- build realizable domain for single p-side multiplier (p=a, w=d^-1) ----
Dp = {}   # (pint, wint) -> outint   (=a*w)
Dq = {}   # (qint, wint) -> outint   (q=a+b)
Djoint = {}  # (aint,bint,wint) -> (awint, abw... ) store (a*w, (a+b)*w)
for a in K:
    for b in K:
        if a == 0 and b == 0: continue
        d = nu*a*a + a*b + b*b
        assert d != 0
        w = d^(-1)
        Dp[(kint(a), kint(w))] = kint(a*w)
        Dq[(kint(a+b), kint(w))] = kint((a+b)*w)
        Djoint[(kint(a), kint(b), kint(w))] = (kint(a*w), kint((a+b)*w))

print("single p-side domain |Dp| =", len(Dp), " (expect 135)")
print("single q-side domain |Dq| =", len(Dq), " (expect 135)")
print("joint domain |Djoint| =", len(Djoint), " (expect 255)")

# ---- cross-check vectors (representation anchors) ----
# pick a few field elements and record their images, for any consumer to verify.
def anchor(ai, bi):
    a = kfrom([(ai>>i)&1 for i in range(4)]); b = kfrom([(bi>>i)&1 for i in range(4)])
    d = nu*a*a+a*b+b*b; w = d^(-1) if d!=0 else K(0)
    return dict(a=ai, b=bi, d=kint(d), w=kint(w), aw=kint(a*w), abw=kint((a+b)*w))
anchors = [anchor(1,0), anchor(1,1), anchor(3,5), anchor(0xF,0xA), anchor(0,7)]
print("cross-check anchors (a,b,d,w,aw,(a+b)w):")
for A in anchors: print("   ", A)

# ---- don't-care freedom: degree-<=2 polynomials vanishing on Dp ----
# variables p0..p3, w0..w3 (8 bits).  Monomials of degree <=2 over GF(2)
# (square-free, since bits are idempotent): 1 + 8 + C(8,2) = 1+8+28 = 37.
from itertools import combinations
vars8 = ['p0','p1','p2','p3','w0','w1','w2','w3']
monos = [()] + [(i,) for i in range(8)] + [tuple(c) for c in combinations(range(8),2)]
def pt_bits(pw):  # pw=(pint,wint) -> 8 bit list
    p,wv = pw
    return [(p>>i)&1 for i in range(4)] + [(wv>>i)&1 for i in range(4)]
def mono_eval(mn, bits):
    r = 1
    for i in mn: r &= bits[i]
    return r
# Evaluation matrix over the 135 domain points x monomials
rows = []
for pw in Dp:
    b = pt_bits(pw); rows.append([mono_eval(m,b) for m in monos])
Mev = matrix(GF(2), rows)
# vanishing degree-<=2 polynomials = right kernel of Mev
ker = Mev.right_kernel()
print("degree<=2 monomials:", len(monos), " rank on Dp:", Mev.rank(),
      " => dim of deg<=2 polynomials VANISHING on Dp:", ker.dimension())

# how many domain points does each output bit constrain vs free (Boolean 8-var)
# full space 256 points; care 135; free (don't-care) = 256 - |image points|.
allpts = set((p,w) for p in range(16) for w in range(16))
print("total (p,w) points = 256; care =", len(Dp), "; don't-care =", 256-len(Dp))

# ---- deg-<=2 and deg-<=3 vanishing freedom on JOINT domain (12 vars) ----
def vanishing_dim(domain_points, nbits, maxdeg):
    vs = list(range(nbits))
    ms = [()]
    for dd in range(1, maxdeg+1):
        ms += [tuple(c) for c in combinations(range(nbits), dd)]
    rows = []
    for pt in domain_points:
        bitv = pt
        rows.append([1 if all(bitv[i] for i in m) else 0 for m in ms])
    M = matrix(GF(2), rows)
    return len(ms), M.rank(), len(ms) - M.rank()

# single p-side, degree <=3
def pw_bits(pw): p,wv = pw; return [(p>>i)&1 for i in range(4)]+[(wv>>i)&1 for i in range(4)]
for dd in [2,3,4]:
    nm3, rk3, van3 = vanishing_dim([pw_bits(k) for k in Dp], 8, dd)
    print("single p-side deg<=%d: monos=%d rank=%d VANISHING dim=%d" % (dd, nm3, rk3, van3))

# joint 12-bit domain (a,b,w), degree <=2 and <=3
def abw_bits(k): a,b,wv = k; return [(a>>i)&1 for i in range(4)]+[(b>>i)&1 for i in range(4)]+[(wv>>i)&1 for i in range(4)]
jpts = [abw_bits(k) for k in Djoint]
for dd in [2,3]:
    nm, rk, van = vanishing_dim(jpts, 12, dd)
    print("joint stage deg<=%d: monos=%d rank=%d VANISHING dim=%d" % (dd, nm, rk, van))

# ---- n=4 SANITY: deg<=2 vanishing dim on the n=4 single-side domain (expect >0) ----
K2.<z2> = GF(4, modulus=t^2+t+1)
def k2int(e):
    cs=list(e.polynomial().coefficients(sparse=False)); cs+=[0]*(2-len(cs)); return sum(int(cs[i])<<i for i in range(2))
nu2=[e for e in K2 if e!=0 and e.trace()==1][0]
Dp4={}
for a in K2:
    for b in K2:
        if a==0 and b==0: continue
        d=nu2*a*a+a*b+b*b; w=d^(-1)
        Dp4[(k2int(a),k2int(w))]=k2int(a*w)
def pw4_bits(pw): p,wv=pw; return [(p>>i)&1 for i in range(2)]+[(wv>>i)&1 for i in range(2)]
nm4,rk4,van4 = vanishing_dim([pw4_bits(k) for k in Dp4], 4, 2)
print("n=4 SANITY single-side deg<=2: |dom|=%d monos=%d rank=%d VANISHING dim=%d (expect >0)" % (len(Dp4),nm4,rk4,van4))

# ---- re-witness substitution soundness (mandate) ----
import random as _r; _r.seed(int(12345))
fails = 0
for trial in range(150):
    # random total extension of the p-side and q-side multipliers
    ext_p = dict(Dp); ext_q = dict(Dq)
    for p in range(16):
        for wv in range(16):
            if (p,wv) not in ext_p: ext_p[(p,wv)] = _r.randint(0,15)
            if (p,wv) not in ext_q: ext_q[(p,wv)] = _r.randint(0,15)
    ok = True
    for a in K:
        for b in K:
            if a==0 and b==0:
                continue
            d = nu*a*a+a*b+b*b; w = d^(-1)
            aw = ext_p[(kint(a),kint(w))]; abw = ext_q[(kint(a+b),kint(w))]
            if aw != kint(a*w) or abw != kint((a+b)*w): ok=False
    if not ok: fails += 1
print("substitution soundness re-witness: 150 random total extensions, failures =", fails)

# ---- export self-checking artifact ----
out = dict(
    rep="GF(2)[t]/(t^4+t+1); Y^2+Y+nu; bit i = coeff t^i; nu_int=%d" % kint(nu),
    nu_int=kint(nu),
    anchors=anchors,
    Dp=[[int(p),int(w),int(o)] for (p,w),o in sorted(Dp.items())],
    Dq=[[int(p),int(w),int(o)] for (p,w),o in sorted(Dq.items())],
    Djoint=[[int(a),int(b),int(w),int(o[0]),int(o[1])] for (a,b,w),o in sorted(Djoint.items())],
    deg2_vanishing_dim=int(ker.dimension()),
)
with open("/tmp/scratch/mcupper_domain.json","w") as f:
    json.dump(out, f)
print("exported /tmp/scratch/mcupper_domain.json")
