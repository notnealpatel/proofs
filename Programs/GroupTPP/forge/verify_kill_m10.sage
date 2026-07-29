# Standalone reduction-free verifier for the M_10 kill candidate
# (Pl15 campaign, kill protocol).  Config from pl15_census_M10.log:
#   shape (16,16,24) = (QD16, QD16, S4), k=3, |Sigma| = 3072
#   > beta_0(M_10) = 2304 (Go engine, exact).
# QD16 has abelianization C2 x C2 (3 index-2 kernels), so the
# generic verify_witness.sage unique-kernel path cannot run; this
# script enumerates ALL character combinations (3 x 3 x 1) and
# brute-checks the graph triple in C_2 x M_10 for each:
#   pass 1: exact pair arithmetic in the direct product C_2 x G
#   pass 2: raw permutation-group re-check on 13 points for any hit
#           (model: a6-tight-verify.sage; tau on (12,13) avoids the
#           NrMovedPoints/LargestMovedPoint pitfall - G moves 2..11)
import json, time, itertools
from sage.all import libgap, PermutationGroup

t0 = time.time()

G = libgap.eval("Stabilizer(MathieuGroup(11),1)")
nG = int(libgap.Size(G))
assert nG == 720

S_gens = "(2,3)(5,11)(6,7)(8,9), (2,3)(4,5,6,11,10,8,7,9)"
T_gens = "(2,4)(5,9)(6,11)(7,8), (2,4)(3,7,9,8,10,11,5,6)"
U_gens = "(3,9)(4,7)(5,6)(8,10), (2,11,10,8)(5,9,6,7)"

S = libgap.eval("Group(%s)" % S_gens)
T = libgap.eval("Group(%s)" % T_gens)
U = libgap.eval("Group(%s)" % U_gens)

print("orders:", int(libgap.Size(S)), int(libgap.Size(T)), int(libgap.Size(U)), flush=True)
print("structs:", libgap.StructureDescription(S), libgap.StructureDescription(T),
      libgap.StructureDescription(U), flush=True)
assert [int(libgap.Size(S)), int(libgap.Size(T)), int(libgap.Size(U))] == [16, 16, 24]

for H in (S, T, U):
    assert bool(libgap.IsSubgroup(G, H)), "member not inside M_10"

# pairwise trivial intersections
for A, B, nm in ((S, T, "S^T"), (S, U, "S^U"), (T, U, "T^U")):
    isz = int(libgap.Size(libgap.Intersection(A, B)))
    print("|%s| = %d" % (nm, isz), flush=True)
    assert isz == 1, "nontrivial pairwise intersection %s" % nm

# covering
gen = libgap.eval("Group(%s, %s, %s)" % (S_gens, T_gens, U_gens))
print("<S,T,U> order:", int(libgap.Size(gen)), flush=True)

def index2_kernels(H):
    return [K for K in libgap.NormalSubgroups(H)
            if 2 * int(libgap.Size(K)) == int(libgap.Size(H))]

kS, kT, kU = index2_kernels(S), index2_kernels(T), index2_kernels(U)
print("index-2 kernels: S=%d T=%d U=%d" % (len(kS), len(kT), len(kU)), flush=True)

def char_map(H, K):
    ker = set(str(e) for e in libgap.Elements(K))
    return {str(e): (0 if str(e) in ker else 1) for e in libgap.Elements(H)}

S_el = list(libgap.Elements(S))
T_el = list(libgap.Elements(T))
U_el = list(libgap.Elements(U))
S_str = {str(e): e for e in S_el}
one = libgap.One(G)

hits = []
for (iS, KS), (iT, KT), (iU, KU) in itertools.product(
        enumerate(kS), enumerate(kT), enumerate(kU)):
    fS, fT, fU = char_map(S, KS), char_map(T, KT), char_map(U, KU)
    # T_hat ^ U_hat is trivial automatically (T ^ U = 1 checked above).
    # S_hat ^ (T_hat U_hat): (t u, fT(t)+fU(u)) in S_hat iff
    #   t u in S and fS(t u) == fT(t) + fU(u) mod 2; nontrivial unless t u = 1
    #   (t u = 1 forces t = u^-1 in T ^ U = 1, so t = u = 1, f-sum 0: identity).
    bad = 0
    for t in T_el:
        ft = fT[str(t)]
        for u in U_el:
            x = t * u
            xs = str(x)
            if xs in S_str:
                if x == one and t == one and u == one:
                    continue
                if fS[xs] == (ft + fU[str(u)]) % 2:
                    bad += 1
    verdict = {"combo": [int(iS), int(iT), int(iU)],
               "violations": int(bad), "TPP": bool(bad == 0)}
    print(json.dumps(verdict), flush=True)
    if bad == 0:
        hits.append((KS, KT, KU, fS, fT, fU))

print("pair-arithmetic pass: %d/%d combos give a TPP triple (%.1fs)"
      % (len(hits), len(kS) * len(kT) * len(kU), time.time() - t0), flush=True)

# pass 2: raw permutation re-check of the first hit on 13 points
if hits:
    KS, KT, KU, fS, fT, fU = hits[0]
    tau = "(12,13)"
    def lift(el_list, f):
        out = []
        for g in el_list:
            gs = str(g)
            if f[gs] % 2 == 0:
                out.append(gs if gs != "()" else "()")
            else:
                out.append((gs if gs != "()" else "") + tau if gs != "()" else tau)
        return out
    Shat = PermutationGroup(lift(S_el, fS))
    That = PermutationGroup(lift(T_el, fT))
    Uhat = PermutationGroup(lift(U_el, fU))
    print("graph orders:", Shat.order(), That.order(), Uhat.order(), flush=True)
    assert (Shat.order(), That.order(), Uhat.order()) == (16, 16, 24)
    TU = set()
    for t in That:
        for u in Uhat:
            TU.add(t * u)
    s_bad = [g for g in Shat if g in TU and not g.is_one()]
    tu_bad = [g for g in That if g in set(Uhat) and not g.is_one()]
    size = Shat.order() * That.order() * Uhat.order()
    res = {"raw_TPP": bool(len(s_bad) == 0 and len(tu_bad) == 0),
           "triple_size": int(size),
           "exceeds": "%d > 2*beta0(M10) = 4608" % int(size),
           "S^TU": int(len(s_bad)), "T^U": int(len(tu_bad)),
           "elapsed": float(time.time() - t0)}
    print(json.dumps(res), flush=True)
    if res["raw_TPP"]:
        print("*** KILL VERIFIED: TPP triple of size %d in C_2 x M_10; "
              "beta_0(C_2 x M_10) >= %d > 4608 = 2*beta_0(M_10) ***"
              % (size, size), flush=True)
else:
    print("NO character combo yields a TPP triple: census eligibility "
          "is NOT confirmed for this config (possible census bug).", flush=True)
