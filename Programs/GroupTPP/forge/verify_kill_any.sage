# Generalized reduction-free kill verifier (Pl15 kill protocol).
# Same two-pass method as verify_kill_m10.sage, but target/config
# come from the command line and ALL index-2 kernel combinations
# are enumerated (handles members with abelianization C2 x C2 or
# larger, where verify_witness.sage's unique-kernel path fails).
#
#   sage verify_kill_any.sage -- --target "SymmetricGroup(6)" \
#     --S-gens "(2,5), (1,5), (3,4)" --T-gens "..." --U-gens "..."
#
# p = 2 only (all Pl15 kill candidates are p = 2).
import argparse, json, sys, time, itertools
from sage.all import libgap, PermutationGroup

parser = argparse.ArgumentParser()
parser.add_argument("--target", required=True)
parser.add_argument("--S-gens", dest="S_gens", required=True)
parser.add_argument("--T-gens", dest="T_gens", required=True)
parser.add_argument("--U-gens", dest="U_gens", required=True)
argv = sys.argv[1:]
if "--" in argv:
    argv = argv[argv.index("--") + 1:]
args = parser.parse_args(argv)

t0 = time.time()
G = libgap.eval(args.target)
nG = int(libgap.Size(G))

def strip(g):
    return g.strip().lstrip("[").rstrip("]")

S = libgap.eval("Group(%s)" % strip(args.S_gens))
T = libgap.eval("Group(%s)" % strip(args.T_gens))
U = libgap.eval("Group(%s)" % strip(args.U_gens))
sizes = [int(libgap.Size(H)) for H in (S, T, U)]
print("target %s |G|=%d member orders %s structs %s"
      % (args.target, nG, sizes,
         [str(libgap.StructureDescription(H)) for H in (S, T, U)]), flush=True)

for H in (S, T, U):
    assert bool(libgap.IsSubgroup(G, H)), "member not inside G"
for A, B, nm in ((S, T, "S^T"), (S, U, "S^U"), (T, U, "T^U")):
    isz = int(libgap.Size(libgap.Intersection(A, B)))
    assert isz == 1, "nontrivial %s (size %d)" % (nm, isz)
gen = libgap.eval("Group(%s, %s, %s)"
                  % (strip(args.S_gens), strip(args.T_gens), strip(args.U_gens)))
print("pairwise trivial ok; <S,T,U> order %d (|G| = %d)"
      % (int(libgap.Size(gen)), nG), flush=True)

def index2_kernels(H):
    return [K for K in libgap.NormalSubgroups(H)
            if 2 * int(libgap.Size(K)) == int(libgap.Size(H))]

kS, kT, kU = index2_kernels(S), index2_kernels(T), index2_kernels(U)
print("index-2 kernels: %d x %d x %d" % (len(kS), len(kT), len(kU)), flush=True)

def char_map(H, K):
    ker = set(str(e) for e in libgap.Elements(K))
    return {str(e): (0 if str(e) in ker else 1) for e in libgap.Elements(H)}

S_el, T_el, U_el = (list(libgap.Elements(H)) for H in (S, T, U))
S_str = {str(e): e for e in S_el}
one = libgap.One(G)

hits = []
for (iS, KS), (iT, KT), (iU, KU) in itertools.product(
        enumerate(kS), enumerate(kT), enumerate(kU)):
    fS, fT, fU = char_map(S, KS), char_map(T, KT), char_map(U, KU)
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
    print(json.dumps({"combo": [int(iS), int(iT), int(iU)],
                      "violations": int(bad), "TPP": bool(bad == 0)}), flush=True)
    if bad == 0:
        hits.append((fS, fT, fU))

print("pair-arithmetic pass: %d/%d combos TPP (%.1fs)"
      % (len(hits), len(kS) * len(kT) * len(kU), time.time() - t0), flush=True)

if hits:
    fS, fT, fU = hits[0]
    m = int(libgap.LargestMovedPoint(G))
    tau = "(%d,%d)" % (m + 1, m + 2)
    def lift(el_list, f):
        out = []
        for g in el_list:
            gs = str(g)
            if f[gs] % 2 == 0:
                out.append(gs)
            else:
                out.append(tau if gs == "()" else gs + tau)
        return out
    Shat = PermutationGroup(lift(S_el, fS))
    That = PermutationGroup(lift(T_el, fT))
    Uhat = PermutationGroup(lift(U_el, fU))
    assert [Shat.order(), That.order(), Uhat.order()] == sizes
    TU = set()
    for t in That:
        for u in Uhat:
            TU.add(t * u)
    s_bad = [g for g in Shat if g in TU and not g.is_one()]
    tu_bad = [g for g in That if g in set(Uhat) and not g.is_one()]
    size = sizes[0] * sizes[1] * sizes[2]
    ok = len(s_bad) == 0 and len(tu_bad) == 0
    print(json.dumps({"raw_TPP": bool(ok), "triple_size": int(size),
                      "Cp_x_G_order": int(2 * nG),
                      "S^TU": int(len(s_bad)), "T^U": int(len(tu_bad)),
                      "elapsed": float(time.time() - t0)}), flush=True)
    if ok:
        print("*** KILL VERIFIED: TPP triple of size %d in C_2 x G, "
              "|G| = %d ***" % (int(size), nG), flush=True)
else:
    print("NO combo yields TPP: census eligibility NOT confirmed.", flush=True)
