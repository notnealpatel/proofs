"""
export_tpp.sage -- Sage/GAP exporter for TPP subgroup search data.

Serializes per-target group data (Cayley table, subgroup conjugacy classes)
to JSONL files consumed by the Go TPP search engine (cmd/sieve/rho0).

USAGE:
  sage export_tpp.sage -- [--target-id ID] [--stretch] [--skip-ab] [--probe-products]
  sage export_tpp.sage -- --list

Output: one JSON file per target under forge/out/tpp-data/<id>.json
Plus a manifest at forge/out/tpp-data/manifest.json.

Library survey (GAP subgroup-lattice primitives):
  - ConjugacyClassesSubgroups(G): conjugacy classes of all subgroups.
    Cost: polynomial in |G| via cyclic extension (Cannon/Holt/Hulpke).
    For |G|=384, typically seconds.
  - WreathProduct(A, B): requires IsPermGroup on at least one arg.
  - DirectProduct(A, B): works on any group type.
  - Elements(H): enumerate all elements of a subgroup.
  - IsNormal(G, H): test normality of H in G.

Resumable: skips targets whose export file exists and validates
(non-empty JSON with matching order).

Pruning theory (citations from Murthy arXiv:2602.15796):
  - Neumann Obs 3.1: |S|(|T|+|U|-1) <= |G| for any TPP triple.
  - Murthy26 Prop 2.19(2): in a non-trivial triple, all members non-normal.
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

REPO_ROOT = Path("/home/exedev/p/proofs")
FORGE_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "forge"
OUT_DIR = FORGE_DIR / "out" / "tpp-data"


class SageEncoder(json.JSONEncoder):
    """JSON encoder that handles Sage Integer/RealNumber types."""
    def default(self, obj):
        if hasattr(obj, '__index__'):
            return int(obj)
        return super().default(obj)


PERM_GROUP_WHITELIST = {
    "A5":       lambda: libgap.AlternatingGroup(5),
    "S5":       lambda: libgap.SymmetricGroup(5),
    "A6":       lambda: libgap.AlternatingGroup(6),
    "S6":       lambda: libgap.SymmetricGroup(6),
    "A7":       lambda: libgap.AlternatingGroup(7),
    "PSL_2_11": lambda: libgap.PSL(2, 11),
    "M10":      lambda: libgap.MathieuGroup(10),
}


def build_manifest(stretch=False, probe_products=False):
    """Build the ordered target manifest."""
    targets = []

    # --- Regression anchors ---
    anchors = [
        ([24, 10], "1", "C3xD8"),
        ([24, 11], "1", "C3xQ8"),
        ([32, 49], "2", "ExSp(2,5)+"),
        ([32, 50], "1", "ExSp(2,5)-"),
        ([64, 226], "2", "D8:D8"),
    ]
    for (o, i), rho, desc in anchors:
        targets.append({
            "id": "%d_%d" % (o, i),
            "description": "[%d,%d] %s" % (o, i, desc),
            "constructor": ("SmallGroup", o, i),
            "expected_rho0": rho,
            "category": "regression_anchor",
        })

    # --- Kill-test controls (bare G, order <= 32) ---
    controls = [
        ([8, 3], "1", "D8"),
        ([8, 4], "1", "Q8"),
        ([12, 4], "4/3", "D12"),
        ([16, 3], "1", "C4^2:C2 a"),
        ([16, 4], "1", "C4^2:C2 b"),
        ([16, 6], "1", "C8:C2"),
        ([16, 11], "1", "C2xD8"),
        ([16, 12], "1", "C2xQ8"),
        ([16, 13], "1", "(C4xC2):C2"),
        ([27, 3], "1", "(C3xC3):C3"),
        ([27, 4], "1", "C9:C3"),
        ([32, 49], "2", "ExSp(2,5)+"),
        ([32, 50], "1", "ExSp(2,5)-"),
    ]
    for (o, i), rho, desc in controls:
        targets.append({
            "id": "ctrl_%d_%d" % (o, i),
            "description": "control [%d,%d] %s" % (o, i, desc),
            "constructor": ("SmallGroup", o, i),
            "expected_rho0": rho,
            "category": "kill_test_control",
        })

    # --- Kill-test products AxG ---
    abelian_factors = [
        ("C2", 2),
        ("C3", 3),
        ("C4", 4),
        ("C2xC2", 4),
    ]
    nonabelian_with_rho0 = [
        ([8, 3], "1", "D8"),
        ([8, 4], "1", "Q8"),
        ([12, 4], "4/3", "D12"),
        ([16, 3], "1", "C4^2:C2 a"),
        ([16, 6], "1", "C8:C2"),
        ([16, 11], "1", "C2xD8"),
        ([16, 12], "1", "C2xQ8"),
        ([16, 13], "1", "(C4xC2):C2"),
        ([27, 3], "1", "(C3xC3):C3"),
        ([27, 4], "1", "C9:C3"),
        ([32, 49], "2", "ExSp(2,5)+"),
        ([32, 50], "1", "ExSp(2,5)-"),
    ]
    for a_name, a_order in abelian_factors:
        for (o, i), rho, desc in nonabelian_with_rho0:
            prod_order = a_order * o
            if prod_order > 192:
                continue
            targets.append({
                "id": "prod_%s_%d_%d" % (a_name, o, i),
                "description": "%s x [%d,%d] %s (order %d)" % (a_name, o, i, desc, prod_order),
                "constructor": ("DirectProduct", a_name, a_order, o, i),
                "expected_rho0": rho,
                "category": "kill_test_product",
            })

    # Specific products
    targets.append({
        "id": "D8xD8",
        "description": "D8xD8 (order 64)",
        "constructor": ("DirectProductSmall", 8, 3, 8, 3),
        "expected_rho0": "2",
        "category": "kill_test_product",
    })
    targets.append({
        "id": "C2x32_49",
        "description": "C2x[32,49] (order 64)",
        "constructor": ("DirectProduct", "C2", 2, 32, 49),
        "expected_rho0": "2",
        "category": "kill_test_product",
    })
    targets.append({
        "id": "C3x32_49",
        "description": "C3x[32,49] (order 96)",
        "constructor": ("DirectProduct", "C3", 3, 32, 49),
        "expected_rho0": "2",
        "category": "kill_test_product",
    })

    # --- Lamplighters C2 wr Cn ---
    for n in [3, 4, 5, 6]:
        order = (2**n) * n
        targets.append({
            "id": "lamp_C2wrC%d" % n,
            "description": "C2 wr C%d (order %d)" % (n, order),
            "constructor": ("WreathProduct", 2, n),
            "expected_rho0": None,
            "category": "lamplighter",
        })

    # --- Stretch: C2 wr C7 (order 896) ---
    if stretch:
        targets.append({
            "id": "lamp_C2wrC7",
            "description": "C2 wr C7 (order 896)",
            "constructor": ("WreathProduct", 2, 7),
            "expected_rho0": None,
            "category": "lamplighter_stretch",
        })

    # --- Pl15 probe targets (permutation groups) ---
    pl15_probes = [
        ("A5",       60,   "AlternatingGroup(5)",   None),
        ("S5",       120,  "SymmetricGroup(5)",      None),
        ("A6",       360,  "AlternatingGroup(6)",    "27/10"),
        ("PSL_2_11", 660,  "PSL(2,11)",              None),
        ("M10",      720,  "MathieuGroup(10)",       None),
        ("S6",       720,  "SymmetricGroup(6)",      None),
        ("A7",       2520, "AlternatingGroup(7)",    None),
    ]
    for name, order, gap_desc, rho0 in pl15_probes:
        targets.append({
            "id": "pl15_%s" % name,
            "description": "%s (order %d, %s)" % (name, order, gap_desc),
            "constructor": ("PermGroup", name),
            "expected_rho0": rho0,
            "category": "pl15_probe",
        })

    # --- Pl15 product probes: C_p x PermGroup (behind --probe-products) ---
    if probe_products:
        cp_factors = [("C2", 2), ("C3", 3), ("C5", 5)]
        for name, order, gap_desc, rho0 in pl15_probes:
            for cp_name, cp_order in cp_factors:
                prod_order = cp_order * order
                targets.append({
                    "id": "pl15_%s_x_%s" % (cp_name, name),
                    "description": "%s x %s (order %d)" % (cp_name, name, prod_order),
                    "constructor": ("CpxPermGroup", cp_name, cp_order, name),
                    "expected_rho0": rho0,
                    "category": "pl15_probe",
                })

    return targets


def construct_group(spec):
    """Construct a GAP group from a manifest constructor spec."""
    kind = spec[0]
    if kind == "SmallGroup":
        return libgap.SmallGroup(spec[1], spec[2])
    elif kind == "DirectProduct":
        a_name, a_order, o, i = spec[1], spec[2], spec[3], spec[4]
        factor_map = {
            "C2": lambda: libgap.CyclicGroup(2),
            "C3": lambda: libgap.CyclicGroup(3),
            "C4": lambda: libgap.CyclicGroup(4),
            "C2xC2": lambda: libgap.DirectProduct(
                libgap.CyclicGroup(2), libgap.CyclicGroup(2)),
        }
        if a_name not in factor_map:
            raise ValueError("Unknown abelian factor: %s" % a_name)
        A = factor_map[a_name]()
        G = libgap.SmallGroup(o, i)
        return libgap.DirectProduct(A, G)
    elif kind == "DirectProductSmall":
        G1 = libgap.SmallGroup(spec[1], spec[2])
        G2 = libgap.SmallGroup(spec[3], spec[4])
        return libgap.DirectProduct(G1, G2)
    elif kind == "WreathProduct":
        base = libgap.CyclicGroup(libgap.IsPermGroup, spec[1])
        top = libgap.CyclicGroup(libgap.IsPermGroup, spec[2])
        return libgap.WreathProduct(base, top)
    elif kind == "PermGroup":
        name = spec[1]
        if name not in PERM_GROUP_WHITELIST:
            raise ValueError("Unknown PermGroup name: %s (whitelist: %s)" %
                             (name, ", ".join(sorted(PERM_GROUP_WHITELIST))))
        return PERM_GROUP_WHITELIST[name]()
    elif kind == "CpxPermGroup":
        cp_name, cp_order, perm_name = spec[1], spec[2], spec[3]
        if perm_name not in PERM_GROUP_WHITELIST:
            raise ValueError("Unknown PermGroup name: %s" % perm_name)
        A = libgap.CyclicGroup(cp_order)
        G = PERM_GROUP_WHITELIST[perm_name]()
        return libgap.DirectProduct(A, G)
    else:
        raise ValueError("Unknown constructor kind: %s" % kind)


def export_target(target, skip_ab=False):
    """Export a single target's group data to JSON.

    Returns the output path on success.
    If skip_ab=True, abelianization data is set to null instead of computed.
    """
    out_path = OUT_DIR / ("%s.json" % target["id"])

    # Resumable: skip if file exists and validates.
    # Accept both abelianization=null (--skip-ab) and abelianization=[...].
    if out_path.exists():
        try:
            with open(out_path) as f:
                data = json.load(f)
            if data.get("n") and data.get("n") > 0 and "abelianization" in data:
                print("  SKIP (already exported): %s" % out_path, flush=True)
                return out_path
        except (json.JSONDecodeError, KeyError):
            pass  # Re-export on invalid file

    t0 = time.time()
    G = construct_group(target["constructor"])
    n = int(G.Order())
    print("  Order: %d" % n, flush=True)

    # Enumerate elements and build index mapping.
    # Element 0 = identity.
    elts = list(G.Elements().AsList())
    identity = G.Identity()

    # Sort so identity is first.
    elt_to_idx = {}
    sorted_elts = [identity]
    for e in elts:
        if e != identity:
            sorted_elts.append(e)
    elts = sorted_elts
    assert len(elts) == n
    for i, e in enumerate(elts):
        elt_to_idx[e] = i
    assert elt_to_idx[identity] == 0

    # Cayley table: table[i*n + j] = index of elts[i]*elts[j].
    print("  Building Cayley table (%d x %d)..." % (n, n), flush=True)
    t_ct = time.time()
    table = [0] * (n * n)
    for i in range(n):
        if n > 60 and i % max(1, n // 10) == 0 and i > 0:
            print("    cayley: row %d/%d (%.1fs)..." % (i, n, time.time() - t_ct), flush=True)
        ei = elts[i]
        for j in range(n):
            prod = ei * elts[j]
            table[i * n + j] = elt_to_idx[prod]

    # Inverse table: inv[i] = index of elts[i]^{-1}.
    inv = [0] * n
    for i in range(n):
        inv[i] = elt_to_idx[elts[i].Inverse()]

    # Subgroup conjugacy classes.
    print("  Computing conjugacy classes of subgroups...", flush=True)
    t_sub = time.time()
    conj_classes = G.ConjugacyClassesSubgroups()
    classes_data = []
    total_subgroups = 0

    for ci, cl in enumerate(conj_classes):
        rep = cl.Representative()
        rep_elts = sorted([elt_to_idx[e] for e in rep.Elements().AsList()])
        is_normal = bool(libgap.IsNormal(G, rep))
        h_order = int(rep.Size())

        # All subgroups in this class
        all_in_class = list(cl.AsList())
        subgroups_in_class = []
        for si, H in enumerate(all_in_class):
            h_elts = sorted([elt_to_idx[e] for e in H.Elements().AsList()])
            subgroups_in_class.append({
                "elements": h_elts,
                "order": h_order,
                "class": ci,
                "is_rep": (si == 0),
                "is_normal": is_normal,
            })
        total_subgroups += len(subgroups_in_class)
        classes_data.append(subgroups_in_class)

    t_sub_elapsed = time.time() - t_sub
    n_classes = len(classes_data)
    print("  %d conjugacy classes, %d total subgroups (%.1fs)" %
          (n_classes, total_subgroups, t_sub_elapsed), flush=True)

    # Flatten subgroups list for serialization.
    subgroups = []
    for class_subs in classes_data:
        for s in class_subs:
            subgroups.append(s)

    # --- Abelianization data per subgroup (Fg5: lemma sweep) ---
    # For each subgroup H, compute:
    #   derived_order: |H'|
    #   abelian_invariants: AbelianInvariants(H/H') as sorted tuple
    #   exponent_vectors: map element_index -> exponent vector in H/H'
    #
    # Note: IndependentGeneratorExponents requires IsAbelian to be set
    # on the quotient group (the GAP filter must be stored). We call
    # IsAbelian(F) explicitly for this reason.
    #
    # --skip-ab: omit abelianization (dominant cost for large lattices).
    ab_data = None
    if skip_ab:
        print("  Abelianization: SKIPPED (--skip-ab)", flush=True)
    else:
        print("  Computing abelianization data...", flush=True)
        t_ab = time.time()
        ab_data = []
        for si, s in enumerate(subgroups):
            if total_subgroups > 200 and si % 100 == 0 and si > 0:
                print("    abelianization: %d/%d subgroups (%.1fs)..." %
                      (si, total_subgroups, time.time() - t_ab), flush=True)
            h_elts_idx = s["elements"]
            h_elts_gap = [elts[j] for j in h_elts_idx]

            # Reconstruct subgroup as GAP group from its elements.
            H = libgap.Group(h_elts_gap)
            D = libgap.DerivedSubgroup(H)
            q = libgap.NaturalHomomorphismByNormalSubgroup(H, D)
            F = libgap.Image(q)
            libgap.IsAbelian(F)  # store filter for IndependentGeneratorExponents

            d_order = int(libgap.Size(D))
            invs = [int(v) for v in libgap.AbelianInvariants(F)]

            # Exponent vectors: for each element index in H, the image
            # under the quotient map as IndependentGeneratorExponents.
            evecs = {}
            if len(invs) == 0:
                for idx in h_elts_idx:
                    evecs[str(idx)] = []
            else:
                for idx, g_elt in zip(h_elts_idx, h_elts_gap):
                    img = libgap.Image(q, g_elt)
                    ex = libgap.IndependentGeneratorExponents(F, img)
                    evecs[str(idx)] = [int(t) for t in ex]

            ab_data.append({
                "derived_order": d_order,
                "abelian_invariants": invs,
                "exponent_vectors": evecs,
            })
        t_ab_elapsed = time.time() - t_ab
        print("  Abelianization data computed (%.1fs)" % t_ab_elapsed, flush=True)

    result = {
        "id": target["id"],
        "description": target["description"],
        "category": target["category"],
        "expected_rho0": target.get("expected_rho0"),
        "n": n,
        "cayley_table": table,
        "inverse_table": inv,
        "n_conjugacy_classes": n_classes,
        "n_subgroups": total_subgroups,
        "subgroups": subgroups,
        "abelianization": ab_data,
    }

    # Atomic write: write to temp file then rename.
    tmp_path = out_path.with_suffix(".tmp")
    with open(tmp_path, "w") as f:
        json.dump(result, f, cls=SageEncoder)
    os.rename(str(tmp_path), str(out_path))

    elapsed = time.time() - t0
    print("  Exported: %s (%.1fs)" % (out_path, elapsed), flush=True)
    return out_path


def main(argv):
    parser = argparse.ArgumentParser(
        description="Export TPP group data for Go search engine")
    parser.add_argument("--target-id", type=str, default=None,
                        help="export only a specific target by ID")
    parser.add_argument("--list", action="store_true",
                        help="list all target IDs and exit")
    parser.add_argument("--stretch", action="store_true",
                        help="include stretch targets (C2 wr C7)")
    parser.add_argument("--skip-ab", action="store_true",
                        help="omit abelianization data (schema field present but null)")
    parser.add_argument("--probe-products", action="store_true",
                        help="include C_p x PermGroup product targets (pl15)")
    args = parser.parse_args(argv)

    manifest = build_manifest(stretch=args.stretch,
                              probe_products=args.probe_products)

    if args.list:
        for t in manifest:
            print("%s\t%s" % (t["id"], t["description"]))
        return

    OUT_DIR.mkdir(parents=True, exist_ok=True)

    if args.target_id:
        manifest = [t for t in manifest if t["id"] == args.target_id]
        if not manifest:
            print("ERROR: target '%s' not found." % args.target_id,
                  file=sys.stderr, flush=True)
            sys.exit(1)

    print("=" * 70, flush=True)
    print("export_tpp.sage -- TPP group data exporter", flush=True)
    print("Targets: %d" % len(manifest), flush=True)
    print("Output: %s" % OUT_DIR, flush=True)
    print("=" * 70, flush=True)
    print(flush=True)

    # Write manifest.
    manifest_data = []
    for t in manifest:
        manifest_data.append({
            "id": t["id"],
            "description": t["description"],
            "category": t["category"],
            "expected_rho0": t.get("expected_rho0"),
            "constructor": list(t["constructor"]),
        })

    errors = []
    for i, target in enumerate(manifest):
        print("[%d/%d] %s" % (i + 1, len(manifest), target["description"]),
              flush=True)
        try:
            export_target(target, skip_ab=args.skip_ab)
        except Exception as e:
            print("  ERROR: %s" % e, flush=True)
            errors.append((target["id"], str(e)))
        print(flush=True)

    # Write manifest file.
    manifest_path = OUT_DIR / "manifest.json"
    with open(manifest_path, "w") as f:
        json.dump(manifest_data, f, indent=2, cls=SageEncoder)
    print("Manifest written: %s" % manifest_path, flush=True)

    if errors:
        print("\nErrors:", flush=True)
        for tid, err in errors:
            print("  %s: %s" % (tid, err), flush=True)
        sys.exit(1)

    print("\nAll targets exported successfully.", flush=True)


main([a for a in sys.argv[1:] if a != "--"])
