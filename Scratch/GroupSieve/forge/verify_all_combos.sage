# Generalized reduction-free all-combos kill verifier (Pl15 kill protocol).
#
# Supersedes verify_kill_any.sage: adds trivial character (full group as
# kernel) to each member's character-choice list by default, so that k=2
# lifts (where one or more members use the trivial character) are tested
# alongside the k=3 case.  Reports per-combo twist count k in JSON output.
#
# Provenance: materialized from scratchpad copy that validated kills #4 and
# #5 (Im12.md "Amended kill census").  See friction log:
# /tmp/goof/friction/verify-kill-any-skips-trivial-characters.md
# and Cj2 section 0.
#
# The raw, reduction-free permutation TPP check (S cap TU = 1, T cap U = 1)
# is preserved: this tool is the kill protocol's trust anchor and must NOT
# depend on the Lemma M reduction chain.
#
# Usage:
#   sage verify_all_combos.sage -- --target "SymmetricGroup(6)" \
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
    """Return all index-2 normal subgroups of H (nontrivial characters)."""
    return [K for K in libgap.NormalSubgroups(H)
            if 2 * int(libgap.Size(K)) == int(libgap.Size(H))]

def all_kernel_choices(H):
    """Return list of (K, is_trivial) pairs: index-2 kernels + trivial character.

    The trivial character uses H itself as kernel (every element maps to 0).
    """
    choices = [(K, False) for K in index2_kernels(H)]
    choices.append((H, True))  # trivial character: kernel = full group
    return choices

chS = all_kernel_choices(S)
chT = all_kernel_choices(T)
chU = all_kernel_choices(U)
n_nontrivial = [sum(1 for _, triv in ch if not triv) for ch in (chS, chT, chU)]
print("kernel choices (nontrivial + trivial): %d x %d x %d (nontrivial: %d x %d x %d)"
      % (len(chS), len(chT), len(chU),
         n_nontrivial[0], n_nontrivial[1], n_nontrivial[2]), flush=True)

def char_map(H, K):
    """Map each element of H to 0 (in kernel) or 1 (not in kernel)."""
    ker = set(str(e) for e in libgap.Elements(K))
    return {str(e): (0 if str(e) in ker else 1) for e in libgap.Elements(H)}

S_el, T_el, U_el = (list(libgap.Elements(H)) for H in (S, T, U))
S_str = {str(e): e for e in S_el}
one = libgap.One(G)

hits = []
for (iS, (KS, trivS)), (iT, (KT, trivT)), (iU, (KU, trivU)) in itertools.product(
        enumerate(chS), enumerate(chT), enumerate(chU)):
    # Twist count k = number of nontrivial characters in this combo.
    k = sum(1 for triv in (trivS, trivT, trivU) if not triv)
    # k=0 means all trivial: the identity lift, never a kill.
    if k == 0:
        # Use int() wrappers to avoid Sage Integer JSON serialization errors.
        print(json.dumps({"combo": [int(iS), int(iT), int(iU)],
                          "k": int(k), "violations": int(0),
                          "TPP": True, "note": "all-trivial (identity lift)"}),
              flush=True)
        continue

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
                      "k": int(k), "violations": int(bad),
                      "TPP": bool(bad == 0)}), flush=True)
    if bad == 0:
        hits.append((fS, fT, fU, k))

print("pair-arithmetic pass: %d/%d combos TPP (%.1fs)"
      % (len(hits), len(chS) * len(chT) * len(chU), time.time() - t0), flush=True)

if hits:
    for hit_idx, (fS, fT, fU, k) in enumerate(hits):
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
        print(json.dumps({"hit": int(hit_idx), "k": int(k),
                          "raw_TPP": bool(ok), "triple_size": int(size),
                          "Cp_x_G_order": int(2 * nG),
                          "S^TU": int(len(s_bad)), "T^U": int(len(tu_bad)),
                          "elapsed": float(time.time() - t0)}), flush=True)
        if ok:
            print("*** KILL VERIFIED (k=%d): TPP triple of size %d in C_2 x G, "
                  "|G| = %d ***" % (k, int(size), nG), flush=True)
else:
    print("NO combo yields TPP: census eligibility NOT confirmed.", flush=True)
