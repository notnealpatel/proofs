# verify_witness.sage — Standalone witness verifier for A-side census.
#
# Given a claimed eligible configuration, reconstructs the explicit TPP
# triple in C_p x G as a permutation group and brute-checks
#   S_hat ∩ T_hat*U_hat = {1}  and  T_hat ∩ U_hat = {1}
# directly — no reliance on the Lemma M reduction chain.
#
# Model: a6-tight-verify.sage (the 1944-triple check).
#
# Usage:
#   sage verify_witness.sage -- --target "AlternatingGroup(6)" --p 2 \
#       --S-gens "(1,2,3),(4,5,6)" --T-gens "(1,5)(3,6),(1,3,4,6)(2,5)" \
#       --U-gens "(1,4)(5,6),(1,3,4)(2,5,6)" \
#       --S-untwisted  # f_S = 0 (untwisted slot)
#
#   Or pass a JSON config record on stdin:
#   echo '{"target":"AlternatingGroup(6)","p":2,"S_gens":[...],...}' | sage verify_witness.sage --stdin

import json
import sys
import argparse
import time

from sage.all import PermutationGroup, PermutationGroupElement, libgap


def parse_args():
    argv = [a for a in sys.argv[1:] if a != "--"]
    parser = argparse.ArgumentParser(description="Verify a TPP witness")
    parser.add_argument("--target", help="GAP constructor string")
    parser.add_argument("--p", type=int, help="Prime for B = C_p")
    parser.add_argument("--S-gens", dest="S_gens", help="Generators of S' (GAP notation)")
    parser.add_argument("--T-gens", dest="T_gens", help="Generators of T'")
    parser.add_argument("--U-gens", dest="U_gens", help="Generators of U'")
    parser.add_argument("--S-untwisted", dest="S_untwisted", action="store_true",
                        help="S' is untwisted (f_S = 0)")
    parser.add_argument("--T-untwisted", dest="T_untwisted", action="store_true",
                        help="T' is untwisted (f_T = 0)")
    parser.add_argument("--U-untwisted", dest="U_untwisted", action="store_true",
                        help="U' is untwisted (f_U = 0)")
    parser.add_argument("--stdin", action="store_true",
                        help="Read JSON config from stdin")
    return parser.parse_args(argv)


def unique_index_p_kernel(H, p):
    """Return the unique normal subgroup of index p in H.
    Error if not unique."""
    kernels = []
    order_H = int(libgap.Size(H))
    for K in libgap.NormalSubgroups(H):
        if int(libgap.Size(K)) * p == order_H:
            kernels.append(K)
    if len(kernels) == 0:
        raise ValueError("No normal subgroup of index %d in %s (order %d)"
                         % (p, libgap.StructureDescription(H), order_H))
    if len(kernels) == 1:
        return kernels[0]
    # Multiple kernels: return all, let caller choose
    raise ValueError("Multiple (%d) normal subgroups of index %d in %s"
                     % (len(kernels), p, libgap.StructureDescription(H)))


def make_character(H, p, untwisted=False):
    """Compute f: H -> Z_p (character = group homomorphism to C_p).
    For untwisted: f = 0.
    For twisted: use the unique index-p kernel."""
    elems = list(libgap.Elements(H))
    if untwisted:
        return {str(e): 0 for e in elems}

    ker = unique_index_p_kernel(H, p)
    ker_set = set(str(e) for e in libgap.Elements(ker))

    # Build character values: 0 for kernel, coset label for non-kernel.
    # For p=2: just 0/1.
    # For p=3: need proper coset structure.
    char_map = {}
    if p == 2:
        for e in elems:
            char_map[str(e)] = 0 if str(e) in ker_set else 1
    elif p == 3:
        # Compute coset representatives and assign labels 0, 1, 2
        # such that the map is a group homomorphism.
        # The quotient H/ker ~ C_3.
        q = libgap.NaturalHomomorphismByNormalSubgroup(H, ker)
        F = libgap.Image(q)
        # Map each element to its image in C_3
        # F is cyclic of order 3; pick a generator and compute logs
        fgen = libgap.MinimalGeneratingSet(F)[0]
        for e in elems:
            img = libgap.Image(q, e)
            # Find the exponent: img = fgen^exp
            for exp in range(3):
                if img == fgen ** exp:
                    char_map[str(e)] = exp
                    break
            else:
                raise RuntimeError("Failed to compute character value for %s" % str(e))
    else:
        raise ValueError("Unsupported prime %d" % p)

    # Verify it's a homomorphism
    for a in elems:
        for b in elems:
            ab = a * b
            val_a = char_map[str(a)]
            val_b = char_map[str(b)]
            val_ab = char_map[str(ab)]
            if (val_a + val_b) % p != val_ab:
                raise RuntimeError("Character is not a homomorphism at (%s, %s)" % (str(a), str(b)))

    return char_map


def verify_tpp(G_gap, S_gap, T_gap, U_gap, fS, fT, fU, p, n_G):
    """Build graph subgroups in C_p x G and check the TPP criterion.

    Uses the (n+1, n+2, ...) trick from a6-tight-verify.sage:
    C_p acts on p extra points {n+1, ..., n+p}.
    G acts on {1, ..., n} as a permutation group.
    C_p x G acts on {1, ..., n+p}."""

    t0 = time.time()
    n = n_G  # degree of G

    # Construct C_p acting on extra points
    if p == 2:
        tau_str = "(%d,%d)" % (n + 1, n + 2)
    elif p == 3:
        tau_str = "(%d,%d,%d)" % (n + 1, n + 2, n + 3)
    else:
        raise ValueError("Unsupported prime %d" % p)

    # Build C_p x G as a permutation group on n+p points
    G_gens_strs = [str(g) for g in libgap.GeneratorsOfGroup(G_gap)]
    Ghat_gens = G_gens_strs + [tau_str]
    Ghat = PermutationGroup(Ghat_gens)
    print("Ghat = C_%d x G, order %d (expected %d)" % (p, Ghat.order(), p * int(libgap.Size(G_gap))),
          flush=True)

    # Build graph subgroups: for each element g in X', lift to (tau^{f(g)}, g)
    def make_tau_power(val, p_val, n_val):
        """Return the permutation string for tau^val on the extra points."""
        if p_val == 2:
            if val % 2 == 0:
                return ""
            else:
                return "(%d,%d)" % (n_val + 1, n_val + 2)
        elif p_val == 3:
            if val % 3 == 0:
                return ""
            elif val % 3 == 1:
                return "(%d,%d,%d)" % (n_val + 1, n_val + 2, n_val + 3)
            else:
                return "(%d,%d,%d)" % (n_val + 1, n_val + 3, n_val + 2)
        return ""

    def lift_elements(H_gap, fH, p_val, n_val):
        """Lift all elements of H to C_p x G."""
        lifted = []
        for g in libgap.Elements(H_gap):
            gs = str(g)
            val = fH[gs]
            tau_part = make_tau_power(val, p_val, n_val)
            if gs == "()" and tau_part == "":
                lifted.append("()")
            elif gs == "()":
                lifted.append(tau_part)
            elif tau_part == "":
                lifted.append(gs)
            else:
                lifted.append(gs + tau_part)
        return lifted

    Sh_elems = lift_elements(S_gap, fS, p, n)
    Th_elems = lift_elements(T_gap, fT, p, n)
    Uh_elems = lift_elements(U_gap, fU, p, n)

    Shat = Ghat.subgroup(Sh_elems)
    That = Ghat.subgroup(Th_elems)
    Uhat = Ghat.subgroup(Uh_elems)

    print("Graph subgroup orders: S_hat=%d T_hat=%d U_hat=%d"
          % (Shat.order(), That.order(), Uhat.order()), flush=True)
    print("Expected orders: S=%d T=%d U=%d"
          % (int(libgap.Size(S_gap)), int(libgap.Size(T_gap)), int(libgap.Size(U_gap))),
          flush=True)

    assert Shat.order() == int(libgap.Size(S_gap)), \
        "S_hat order mismatch: %d != %d" % (Shat.order(), int(libgap.Size(S_gap)))
    assert That.order() == int(libgap.Size(T_gap)), \
        "T_hat order mismatch: %d != %d" % (That.order(), int(libgap.Size(T_gap)))
    assert Uhat.order() == int(libgap.Size(U_gap)), \
        "U_hat order mismatch: %d != %d" % (Uhat.order(), int(libgap.Size(U_gap)))

    # TPP check: S_hat ∩ (T_hat * U_hat) = {1} and T_hat ∩ U_hat = {1}
    print("Computing T_hat * U_hat products...", flush=True)
    TU_prods = set()
    for t in That:
        for u in Uhat:
            TU_prods.add(t * u)
    print("|T_hat * U_hat| = %d" % len(TU_prods), flush=True)

    S_set = set(Shat)
    S_inter_TU = [g for g in S_set if g in TU_prods and not g.is_one()]
    T_inter_U = [g for g in That if g in set(Uhat) and not g.is_one()]

    triple_size = Shat.order() * That.order() * Uhat.order()
    is_tpp = (len(S_inter_TU) == 0 and len(T_inter_U) == 0)

    elapsed = time.time() - t0
    result = {
        "TPP": bool(is_tpp),
        "triple_size": int(triple_size),
        "Ghat_order": int(Ghat.order()),
        "S_hat_order": int(Shat.order()),
        "T_hat_order": int(That.order()),
        "U_hat_order": int(Uhat.order()),
        "S_inter_TU_nontrivial": int(len(S_inter_TU)),
        "T_inter_U_nontrivial": int(len(T_inter_U)),
        "p": p,
        "elapsed_seconds": elapsed,
    }
    print(json.dumps(result), flush=True)
    return result


def main():
    args = parse_args()

    if args.stdin:
        config = json.load(sys.stdin)
        target_str = config["target"]
        p = config["p"]
        S_gens_str = config.get("S_gens")
        T_gens_str = config.get("T_gens")
        U_gens_str = config.get("U_gens")
        S_untwisted = config.get("S_untwisted", False)
        T_untwisted = config.get("T_untwisted", False)
        U_untwisted = config.get("U_untwisted", False)
    else:
        target_str = args.target
        p = args.p
        S_gens_str = args.S_gens
        T_gens_str = args.T_gens
        U_gens_str = args.U_gens
        S_untwisted = args.S_untwisted
        T_untwisted = args.T_untwisted
        U_untwisted = args.U_untwisted

    G = libgap.eval(target_str)
    n_G = int(G.NrMovedPoints())
    print("G = %s, |G| = %d, degree = %d" % (target_str, int(libgap.Size(G)), n_G), flush=True)

    # Parse subgroup generators
    def parse_gens(gens_str, G):
        """Parse generator strings and create subgroup."""
        gens = []
        for g_str in gens_str.split("),("):
            g_str = g_str.strip()
            if not g_str.startswith("("):
                g_str = "(" + g_str
            if not g_str.endswith(")"):
                g_str = g_str + ")"
            gens.append(libgap.eval(g_str))
        return libgap.Subgroup(G, gens)

    S = parse_gens(S_gens_str, G)
    T = parse_gens(T_gens_str, G)
    U = parse_gens(U_gens_str, G)

    print("S': order %d, structure %s" % (int(libgap.Size(S)), libgap.StructureDescription(S)),
          flush=True)
    print("T': order %d, structure %s" % (int(libgap.Size(T)), libgap.StructureDescription(T)),
          flush=True)
    print("U': order %d, structure %s" % (int(libgap.Size(U)), libgap.StructureDescription(U)),
          flush=True)

    # Build characters
    fS = make_character(S, p, untwisted=S_untwisted)
    fT = make_character(T, p, untwisted=T_untwisted)
    fU = make_character(U, p, untwisted=U_untwisted)

    # Verify TPP
    result = verify_tpp(G, S, T, U, fS, fT, fU, p, n_G)

    if result["TPP"]:
        print("VERIFIED: TPP triple of size %d in C_%d x G" % (result["triple_size"], p),
              flush=True)
    else:
        print("FAILED: NOT a TPP triple (S∩TU nontrivial: %d, T∩U nontrivial: %d)"
              % (result["S_inter_TU_nontrivial"], result["T_inter_U_nontrivial"]),
              flush=True)


if __name__ == "__main__":
    main()
