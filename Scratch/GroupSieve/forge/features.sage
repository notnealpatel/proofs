"""
features.sage — Survivor feature census for TPP group sieve data.

Merged from census.sage (base-tier) and tier4.sage (deep-tier), built
on forge/forgelib.py for parallel sharded execution.

Library survey (GAP costs/semantics, mandatory per sieve-spec v1.2):

  DirectFactorsOfGroup(G):
    Returns the list of direct factors of G.  Cost: O(|G| log |G|) in
    practice; fast for small groups, ~0.1s at order 256.  Returns a
    list of GAP groups; length 1 means G is directly indecomposable.

  IdSmallGroup(G):
    Returns [order, idx] for G in the SmallGroups library.  Unavailable
    at some orders: order 512 (10.4M groups, enumeration incomplete in
    older GAP), order 1024 (not in library).  Guard with try/except.

  ConjugacyClassesSubgroups(G):
    Returns list of representatives, one per conjugacy class.  Cost is
    the dominant factor in deep-tier: minutes per group worst case at
    order 384-512.  NOT the same as LatticeSubgroups (which computes
    the full inclusion lattice — unnecessary and far more expensive).

  Normalizer(G, H):
    Returns N_G(H).  Fast after ConjugacyClassesSubgroups is done
    (the data it needs is already computed).

Two feature tiers:

  BASE tier (all SURVIVE + CAP records):
    - Nontrivial abelian direct factor (DirectFactorsOfGroup).
    - Nonabelian complement SmallGroup id (IdSmallGroup, guarded).
    - Extraspecial +/- type for T1c groups.
    - T3b caps as exact rational p^2/k (Murthy25 quantization).

  DEEP tier (--deep --top N, default N=50, ceiling-ranked):
    - snr: min |N_G(H)|/|H| over conjugacy classes of proper nontrivial
      subgroups (normalizer quality, BCGPU Thm 3.6).
    - m(G): minimal proper-subgroup index (descriptive; Nikolov-Pyber
      bound vacuous at these orders — caveat in record).
    - extraspecial type (same helper as base tier).
    - Per-feature timeouts with explicit *_timeout flags.

Modes:
  --toy            Orders <= 24 + bundled fixture, 2 workers, seconds.
  (default)        Base tier: all SURVIVE+CAP across all checkpoints/shards.
  --deep --top N   Deep tier: top-N survivors by ceiling descending.
  --dry-run        Print population, rate basis, projection per worker count.

Population notes (current stratum A):
  Base tier: ~88,185 SURVIVE+CAP at ~0.15 s/group => ~3.7 core-hours.
  Stratum B scaling: if Fg1 order-512 census lands, survivors grow to
  ~10.4M at similar per-group cost => ~440 core-hours, ~2h on 224 workers.
  Deep tier: top-N only (N <= 200); per-group cost dominated by
  ConjugacyClassesSubgroups — minutes worst case at order 384-512.

Input: legacy checkpoints/order_*.jsonl + checkpoints/stratum_b_512.jsonl
       + forge/out/cascade/*.jsonl (one loader for all three).
Output: forge/out/features/<tier>.shard<I>of<N>.jsonl

USAGE:
  sage features.sage -- --harness-only
  sage features.sage -- --toy
  sage features.sage -- --dry-run --workers 128
  sage features.sage -- --workers 4
  sage features.sage -- --shard 0/4
  sage features.sage -- --deep --top 100 --workers 4
  sage features.sage -- --deep --top 50 --shard 0/4
"""

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path("/home/exedev/p/proofs")

# forgelib lives in the forge/ directory; use absolute path because
# sage preparsing copies to a temp dir that breaks __file__-relative imports.
_FORGE_DIR = str(REPO_ROOT / "Scratch" / "GroupSieve" / "forge")
if _FORGE_DIR not in sys.path:
    sys.path.insert(0, _FORGE_DIR)
import forgelib
CHECKPOINT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "checkpoints"
CASCADE_OUT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "forge" / "out" / "cascade"
FEATURES_OUT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "forge" / "out" / "features"

# Rate assumptions for dry-run projections (seconds per group).
BASE_RATE = 1.0 / 0.15   # ~6.67 groups/s/core
DEEP_RATE = 1.0 / 30.0   # ~0.033 groups/s/core (conservative for deep tier)

# Default per-feature timeout for deep tier.
DEFAULT_DEEP_TIMEOUT = 60


# ---------------------------------------------------------------------------
# Input loading — unified across legacy checkpoints and forge cascade shards
# ---------------------------------------------------------------------------

def load_cascade_records():
    """Load all cascade records from forge shards + legacy checkpoints.

    Returns list of dicts, each with at least 'id', 'order', 'action', 'tier'.
    Deduplicates by id (forge shards take precedence over legacy).
    """
    records = []
    seen = set()

    # Forge cascade shards first (take precedence).
    if CASCADE_OUT_DIR.is_dir():
        for path in sorted(CASCADE_OUT_DIR.glob("cascade*.jsonl")):
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        rec = json.loads(line)
                        if rec.get("type"):
                            continue
                        gid = rec.get("id")
                        if gid:
                            key = tuple(gid)
                            if key not in seen:
                                records.append(rec)
                                seen.add(key)
                    except (json.JSONDecodeError, TypeError):
                        continue

    # Stratum-B shards.
    if CASCADE_OUT_DIR.is_dir():
        for path in sorted(CASCADE_OUT_DIR.glob("stratum_b*.jsonl")):
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        rec = json.loads(line)
                        if rec.get("type"):
                            continue
                        gid = rec.get("id")
                        if gid:
                            key = tuple(gid)
                            if key not in seen:
                                records.append(rec)
                                seen.add(key)
                    except (json.JSONDecodeError, TypeError):
                        continue

    # Legacy checkpoint files.
    if CHECKPOINT_DIR.is_dir():
        for path in sorted(CHECKPOINT_DIR.glob("order_*.jsonl")):
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        rec = json.loads(line)
                        if rec.get("type"):
                            continue
                        gid = rec.get("id")
                        if gid:
                            key = tuple(gid)
                            if key not in seen:
                                records.append(rec)
                                seen.add(key)
                    except (json.JSONDecodeError, TypeError):
                        continue

    # Legacy stratum-B file.
    sb_path = CHECKPOINT_DIR / "stratum_b_512.jsonl"
    if sb_path.exists():
        with open(sb_path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    if rec.get("type"):
                        continue
                    gid = rec.get("id")
                    if gid:
                        key = tuple(gid)
                        if key not in seen:
                            records.append(rec)
                            seen.add(key)
                except (json.JSONDecodeError, TypeError):
                    continue

    return records


def select_survivors(records, orders=None, strata=None):
    """Filter to SURVIVE and CAP records, optionally by order range/strata."""
    targets = []
    for rec in records:
        action = rec.get("action", "")
        if action != "SURVIVE" and not action.startswith("CAP"):
            continue
        order = rec.get("order", 0)
        if orders and order not in orders:
            continue
        if strata:
            in_stratum = False
            if "A" in strata and order <= 511:
                in_stratum = True
            if "B" in strata and order == 512:
                in_stratum = True
            if not in_stratum:
                continue
        targets.append(rec)
    targets.sort(key=lambda r: r["id"])
    return targets


def select_deep_targets(records, top_n):
    """Select top-N survivors by ceiling descending for deep-tier features."""
    candidates = []
    for rec in records:
        action = rec.get("action", "")
        if action != "SURVIVE" and not action.startswith("CAP"):
            continue
        ceiling = rec.get("ceiling", 0)
        if ceiling > 0:
            candidates.append(rec)
    candidates.sort(key=lambda r: (-r.get("ceiling", 0), r.get("order", 0),
                                    r["id"][1]))
    return candidates[:top_n]


# ---------------------------------------------------------------------------
# Toy-mode fixture (20 records for clean-tree testing)
# ---------------------------------------------------------------------------

TOY_FIXTURE = [
    {"id": [6, 1], "order": 6, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 3,
     "ceilings": {}, "ceiling": 2.449, "cd": [1, 2], "n_G": 2, "flags": []},
    {"id": [10, 1], "order": 10, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 5,
     "ceilings": {}, "ceiling": 3.162, "cd": [1, 2], "n_G": 2, "flags": []},
    {"id": [12, 1], "order": 12, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 2,
     "ceilings": {}, "ceiling": 2.449, "cd": [1, 2, 3], "n_G": 2, "flags": []},
    {"id": [12, 3], "order": 12, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": False, "derived_order": 4,
     "ceilings": {}, "ceiling": 3.464, "cd": [1, 3], "n_G": 3, "flags": []},
    {"id": [14, 1], "order": 14, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 7,
     "ceilings": {}, "ceiling": 3.742, "cd": [1, 2], "n_G": 2, "flags": []},
    {"id": [18, 1], "order": 18, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 3,
     "ceilings": {}, "ceiling": 2.449, "cd": [1, 2], "n_G": 2, "flags": []},
    {"id": [18, 3], "order": 18, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": False, "derived_order": 9,
     "ceilings": {}, "ceiling": 4.243, "cd": [1, 2], "n_G": 2, "flags": []},
    {"id": [18, 4], "order": 18, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": False, "derived_order": 9,
     "ceilings": {}, "ceiling": 4.243, "cd": [1, 2], "n_G": 2, "flags": []},
    {"id": [20, 1], "order": 20, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 5,
     "ceilings": {}, "ceiling": 2.828, "cd": [1, 2, 4], "n_G": 2, "flags": []},
    {"id": [20, 3], "order": 20, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 5,
     "ceilings": {}, "ceiling": 4.472, "cd": [1, 4], "n_G": 4, "flags": []},
    {"id": [21, 1], "order": 21, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 7,
     "ceilings": {}, "ceiling": 3.0, "cd": [1, 3], "n_G": 3, "flags": []},
    {"id": [22, 1], "order": 22, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 11,
     "ceilings": {}, "ceiling": 4.690, "cd": [1, 2], "n_G": 2, "flags": []},
    {"id": [24, 3], "order": 24, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": False, "derived_order": 8,
     "ceilings": {}, "ceiling": 3.464, "cd": [1, 2, 3], "n_G": 2, "flags": []},
    {"id": [24, 5], "order": 24, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 4,
     "ceilings": {}, "ceiling": 3.464, "cd": [1, 2, 3], "n_G": 2, "flags": []},
    {"id": [24, 12], "order": 24, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": False, "derived_order": 12,
     "ceilings": {}, "ceiling": 4.464, "cd": [1, 2, 3], "n_G": 2, "flags": []},
    {"id": [24, 13], "order": 24, "tier": "T2b", "action": "SURVIVE",
     "p_group": None, "derived_cyclic": True, "derived_order": 3,
     "ceilings": {}, "ceiling": 2.449, "cd": [1, 2, 3], "n_G": 2, "flags": []},
]


# ---------------------------------------------------------------------------
# Feature helpers
# ---------------------------------------------------------------------------

def extraspecial_type(G, p, order):
    """Determine extraspecial +/- type for a p-group G.

    Extra-special means |Z(G)| = p, G' = Z(G), G/Z(G) elementary abelian.

    For p odd: exponent p => + type, exponent p^2 => - type.
    For p = 2, order 2^(2n+1):
      + type has 2^(2n) + 2^n - 1 involutions  (D8 central products)
      - type has 2^(2n) - 2^n - 1 involutions  (Q8 factor)

    Cross-validated ground truth (n = (log2(order)-1)//2):
      [8,3]  D8:    5 involutions = 2^2+2^1-1 (n=1) => +
      [8,4]  Q8:    1 involution  = 2^2-2^1-1 (n=1) => -
      [32,49] D8*D8: 19 = 2^4+2^2-1  (n=2)          => +
      [32,50] D8*Q8: 11 = 2^4-2^2-1  (n=2)          => -

    Returns "+", "-", or None if not extra-special.
    """
    Z = libgap.Center(G)
    if int(Z.Size()) != p:
        return None
    D = libgap.DerivedSubgroup(G)
    if int(D.Size()) != p:
        return None
    if D != Z:
        return None
    if not libgap.IsElementaryAbelian(G.FactorGroup(Z)):
        return None
    # Confirmed extra-special.
    if p != 2:
        exp = int(libgap.Exponent(G))
        return "+" if exp == p else "-"
    # p = 2, order = 2^(2n+1).
    k = int(math.log2(order))   # k = 2n+1
    n = (k - 1) // 2
    num_inv = sum(1 for g in G.Elements() if int(g.Order()) == 2)
    plus_inv = 2**(2*n) + 2**n - 1
    minus_inv = 2**(2*n) - 2**n - 1
    if num_inv == plus_inv:
        return "+"
    elif num_inv == minus_inv:
        return "-"
    return None


def t3b_exact_rational(rec):
    """For T3b CAP records, extract exact rational p^2/k.

    Returns (p, k, "p^2/k") or (p, None, None) on mismatch.
    """
    flags = rec.get("flags", [])
    p = None
    for f in flags:
        if isinstance(f, str) and f.startswith("p="):
            # flags may be "p=2, ..." or "p=2"
            p_str = f.split(",")[0].strip()
            p = int(p_str[2:])
            break
    if p is None:
        return None, None, None
    cap_val = rec.get("ceilings", {}).get("T3b")
    if cap_val is None:
        return p, None, None
    # k = p^2 / cap_val; recover as exact rational and verify.
    k_approx = p * p / cap_val
    k = int(round(k_approx))
    if k <= 0:
        return p, None, None
    exact = Fraction(p * p, k)
    if abs(float(exact) - cap_val) < 1e-10:
        return p, k, "%d^2/%d" % (p, k)
    # Loud mismatch — emit error, don't silently accept.
    print("ERROR: T3b rational mismatch for %s: p=%d, cap=%.15g, "
          "k_approx=%.6f, exact=%s (%.15g)" % (
              rec["id"], p, cap_val, k_approx, exact, float(exact)),
          file=sys.stderr, flush=True)
    return p, None, None


# ---------------------------------------------------------------------------
# Base-tier feature extraction (one group)
# ---------------------------------------------------------------------------

def process_base(rec):
    """Compute base-tier features for one SURVIVE/CAP record.

    Returns a dict with all base-tier fields.
    """
    gid = rec["id"]
    order = rec["order"]

    G = libgap.SmallGroup(order, gid[1])

    result = {
        "id": gid,
        "order": order,
        "tier": rec.get("tier"),
        "action": rec.get("action"),
    }

    # 1. Direct factor decomposition.
    df = libgap.DirectFactorsOfGroup(G)
    n_factors = len(df)
    result["n_direct_factors"] = n_factors

    if n_factors > 1:
        abelian_factors = []
        nonabelian_factors = []
        for fac in df:
            f_order = int(fac.Size())
            if libgap.IsAbelian(fac):
                abelian_factors.append(f_order)
            else:
                try:
                    sid = [int(x) for x in libgap.IdSmallGroup(fac)]
                    nonabelian_factors.append(sid)
                except Exception:
                    nonabelian_factors.append([f_order, None])
        result["has_abelian_factor"] = len(abelian_factors) > 0
        if abelian_factors:
            result["abelian_factor_orders"] = sorted(abelian_factors)
        if nonabelian_factors:
            result["nonabelian_complements"] = nonabelian_factors
    else:
        result["has_abelian_factor"] = False

    # 2. Extraspecial type for T1c groups.
    if rec.get("tier") == "T1c":
        p_group = rec.get("p_group")
        if p_group:
            es = extraspecial_type(G, p_group, order)
            if es is not None:
                result["extraspecial_type"] = es

    # 3. T3b exact rational.
    if rec.get("tier") == "T3b" and str(rec.get("action", "")).startswith("CAP"):
        p, k, rational = t3b_exact_rational(rec)
        if rational:
            result["t3b_p"] = p
            result["t3b_k"] = k
            result["t3b_cap_rational"] = rational

    return result


# ---------------------------------------------------------------------------
# Deep-tier feature extraction (one group)
# ---------------------------------------------------------------------------

def compute_snr(G, order_G, timeout_sec):
    """Self-normalizing ratio: min |N_G(H)|/|H| over conjugacy classes
    of proper nontrivial subgroups H.

    Lower snr = H closer to self-normalizing = better for TPP (BCGPU Thm 3.6).
    Self-normalizing s=1 is optimal.

    Uses libgap directly (no Sage PermutationGroup conversion).
    Returns (snr_value, timed_out).
    """
    best_snr = None
    timed_out = False
    start = time.time()

    try:
        cc = libgap.ConjugacyClassesSubgroups(G)
        for cls in cc:
            if time.time() - start > timeout_sec:
                timed_out = True
                break
            H = libgap.Representative(cls)
            h_order = int(H.Size())
            if h_order == 1 or h_order == order_G:
                continue
            N_H = libgap.Normalizer(G, H)
            n_order = int(N_H.Size())
            ratio = Fraction(n_order, h_order)
            if best_snr is None or ratio < best_snr:
                best_snr = ratio
    except Exception as e:
        print("    snr error: %s" % e, file=sys.stderr, flush=True)
        timed_out = True

    return (float(best_snr) if best_snr is not None else None, timed_out)


def compute_m_G(G, order_G, timeout_sec):
    """m(G) = minimal index [G:H] over proper nontrivial subgroups H.

    Descriptive only; Nikolov-Pyber bound is vacuous at these orders —
    caveat recorded in the output.

    Uses libgap directly (no Sage PermutationGroup conversion).
    Returns (m_value, timed_out).
    """
    best_m = None
    timed_out = False
    start = time.time()

    try:
        cc = libgap.ConjugacyClassesSubgroups(G)
        for cls in cc:
            if time.time() - start > timeout_sec:
                timed_out = True
                break
            H = libgap.Representative(cls)
            h_order = int(H.Size())
            if h_order == 1 or h_order == order_G:
                continue
            idx = order_G // h_order
            if best_m is None or idx < best_m:
                best_m = idx
    except Exception as e:
        print("    m(G) error: %s" % e, file=sys.stderr, flush=True)
        timed_out = True

    return (int(best_m) if best_m is not None else None, timed_out)


def process_deep(rec, timeout_sec):
    """Compute deep-tier features for one SURVIVE/CAP record.

    Returns a dict with backward-compatible field names:
      id, order, tier, ceiling, n_G, cd, snr, m_G, extraspecial_type,
      snr_timeout, m_timeout, elapsed_s
    """
    gid = rec["id"]
    order = rec["order"]

    G = libgap.SmallGroup(order, gid[1])
    order_int = int(order)

    t0 = time.time()

    # snr (normalizer quality).
    snr_val, snr_timeout = compute_snr(G, order_int, timeout_sec)

    # m(G) (minimal proper-subgroup index).
    m_val, m_timeout = compute_m_G(G, order_int, timeout_sec)

    # Extraspecial type (for p-groups with cyclic derived of order p).
    es_type = None
    p_group = rec.get("p_group")
    if (p_group is not None and rec.get("derived_cyclic")
            and rec.get("derived_order") == p_group):
        es_type = extraspecial_type(G, int(p_group), order_int)

    elapsed = time.time() - t0

    return {
        "id": gid,
        "order": order,
        "tier": rec.get("tier"),
        "ceiling": rec.get("ceiling"),
        "n_G": rec.get("n_G"),
        "cd": rec.get("cd"),
        "snr": float(snr_val) if snr_val is not None else None,
        "m_G": int(m_val) if m_val is not None else None,
        "extraspecial_type": es_type,
        "snr_timeout": snr_timeout,
        "m_timeout": m_timeout,
        "nikolov_pyber_caveat": "vacuous at this order",
        "elapsed_s": round(float(elapsed), 2),
    }


# ---------------------------------------------------------------------------
# Shard worker: base tier
# ---------------------------------------------------------------------------

def run_shard_base(targets, shard_i, shard_n, out_dir, tag):
    """Process a deterministic slice of base-tier targets."""
    # Round-robin striping to spread order-correlated cost evenly.
    my_targets = targets[shard_i::shard_n]
    base_name = "base"
    shard_file = Path(out_dir) / forgelib.shard_filename(base_name, shard_i, shard_n)

    # Resume: load done-ids across ALL base shard files.
    done_ids = forgelib.load_done_ids(str(out_dir), "base*.jsonl")
    remaining = [r for r in my_targets if tuple(r["id"]) not in done_ids]

    print("%sBase tier shard: %d targets, %d done, %d remaining" % (
        tag, len(my_targets), len(my_targets) - len(remaining), len(remaining)),
        flush=True)
    if not remaining:
        print("%sNothing to do — shard complete." % tag, flush=True)
        return

    print("%sOutput: %s" % (tag, shard_file), flush=True)

    t_start = time.time()
    n_processed = 0
    n_errors = 0
    n_abelian = 0

    with open(str(shard_file), "a") as out:
        for i, rec in enumerate(remaining):
            try:
                result = process_base(rec)
                out.write(forgelib.dump_jsonl(result) + "\n")
                n_processed += 1
                if result.get("has_abelian_factor"):
                    n_abelian += 1
            except KeyboardInterrupt:
                print("\n%sInterrupted after %d groups — checkpoint saved." % (
                    tag, n_processed), flush=True)
                break
            except Exception as e:
                n_errors += 1
                err_rec = {"id": rec["id"], "error": str(e), "type": None}
                out.write(forgelib.dump_jsonl(err_rec) + "\n")
                if n_errors <= 5:
                    print("  %sERROR on %s: %s" % (tag, rec["id"], e),
                          file=sys.stderr, flush=True)

            # Progress.
            if (i + 1) % 500 == 0:
                elapsed = time.time() - t_start
                print("  %s%s" % (tag, forgelib.progress_line(
                    "base:%d/%d" % (shard_i, shard_n),
                    i + 1, len(remaining), elapsed)), flush=True)

            # Flush every 100 groups for resumability.
            if (i + 1) % 100 == 0:
                out.flush()

    elapsed = time.time() - t_start
    print("%sDone: %d processed, %d errors, %d with abelian factor, "
          "%.1f min elapsed." % (tag, n_processed, n_errors, n_abelian,
                                 elapsed / 60), flush=True)


# ---------------------------------------------------------------------------
# Shard worker: deep tier
# ---------------------------------------------------------------------------

def run_shard_deep(targets, shard_i, shard_n, out_dir, timeout_sec, tag):
    """Process a deterministic slice of deep-tier targets."""
    my_targets = targets[shard_i::shard_n]
    base_name = "deep"
    shard_file = Path(out_dir) / forgelib.shard_filename(base_name, shard_i, shard_n)

    # Resume: load done-ids across ALL deep shard files.
    done_ids = forgelib.load_done_ids(str(out_dir), "deep*.jsonl")
    remaining = [r for r in my_targets if tuple(r["id"]) not in done_ids]

    print("%sDeep tier shard: %d targets, %d done, %d remaining" % (
        tag, len(my_targets), len(my_targets) - len(remaining), len(remaining)),
        flush=True)
    if not remaining:
        print("%sNothing to do — shard complete." % tag, flush=True)
        return

    print("%sOutput: %s" % (tag, shard_file), flush=True)
    print("%sPer-feature timeout: %ds" % (tag, timeout_sec), flush=True)

    t_start = time.time()
    n_processed = 0
    n_timeout = 0
    n_errors = 0

    with open(str(shard_file), "a") as out:
        for i, rec in enumerate(remaining):
            gid = rec["id"]
            print("  %s[%d/%d] [%d,%d] (ceiling=%.4f) ..." % (
                tag, i + 1, len(remaining), gid[0], gid[1],
                rec.get("ceiling", 0)), end="", flush=True)

            try:
                result = process_deep(rec, timeout_sec)
                out.write(forgelib.dump_jsonl(result) + "\n")
                out.flush()
                n_processed += 1
                timed_out = result.get("snr_timeout") or result.get("m_timeout")
                if timed_out:
                    n_timeout += 1
                status = " TIMEOUT" if timed_out else ""
                print(" snr=%s m=%s es=%s (%.1fs)%s" % (
                    ("%.3f" % result["snr"] if result["snr"] is not None else "?"),
                    (str(result["m_G"]) if result["m_G"] is not None else "?"),
                    (result["extraspecial_type"] or "-"),
                    result["elapsed_s"], status), flush=True)
            except KeyboardInterrupt:
                print("\n%sInterrupted after %d groups — checkpoint saved." % (
                    tag, n_processed), flush=True)
                break
            except Exception as e:
                n_errors += 1
                err_rec = {"id": gid, "error": str(e), "type": None}
                out.write(forgelib.dump_jsonl(err_rec) + "\n")
                out.flush()
                print(" ERROR: %s" % e, flush=True)

    elapsed = time.time() - t_start
    print("%sDone: %d processed, %d timeouts, %d errors, "
          "%.1f min elapsed." % (tag, n_processed, n_timeout, n_errors,
                                 elapsed / 60), flush=True)


# ---------------------------------------------------------------------------
# Harness: extraspecial cross-validation
# ---------------------------------------------------------------------------

def run_extraspecial_harness(tag):
    """Brute-force cross-validate extraspecial type on known groups.

    Ground truth (n = (log2(order)-1)//2):
      [8,3]  D8  => +, 5 involutions  = 2^2+2^1-1 (n=1)
      [8,4]  Q8  => -, 1 involution   = 2^2-2^1-1 (n=1)
      [32,49]    => +, 19 involutions = 2^4+2^2-1 (n=2)
      [32,50]    => -, 11 involutions = 2^4-2^2-1 (n=2)
    """
    print("%s--- Extraspecial type harness ---" % tag, flush=True)
    test_cases = [
        ([8, 3], 2, "+", 5),
        ([8, 4], 2, "-", 1),
        ([32, 49], 2, "+", 19),
        ([32, 50], 2, "-", 11),
    ]
    ok = True
    for gid, p, expected_type, expected_inv in test_cases:
        G = libgap.SmallGroup(gid[0], gid[1])
        # Count involutions by brute force.
        actual_inv = sum(1 for g in G.Elements() if int(g.Order()) == 2)
        actual_type = extraspecial_type(G, p, gid[0])
        status = "OK" if (actual_type == expected_type
                          and actual_inv == expected_inv) else "FAIL"
        if status == "FAIL":
            ok = False
        print("%s  [%d,%d] p=%d: type=%s inv=%d (expected %s/%d) %s" % (
            tag, gid[0], gid[1], p, actual_type, actual_inv,
            expected_type, expected_inv, status), flush=True)
    if ok:
        print("%sExtraspecial harness: PASS" % tag, flush=True)
    else:
        print("%sExtraspecial harness: FAIL" % tag, file=sys.stderr,
              flush=True)
        sys.exit(1)
    return ok


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv):
    parser = argparse.ArgumentParser(
        description="Survivor feature census (base + deep tiers)")
    parser.add_argument("--toy", action="store_true",
                        help="Orders <= 24 + fixture, 2 workers, seconds")
    parser.add_argument("--deep", action="store_true",
                        help="Deep-tier features (snr, m_G) for top-N")
    parser.add_argument("--top", type=int, default=50,
                        help="Top-N survivors for deep tier (default 50)")
    parser.add_argument("--timeout", type=int, default=DEFAULT_DEEP_TIMEOUT,
                        help="Per-feature timeout in seconds (default %d)" %
                        DEFAULT_DEEP_TIMEOUT)
    parser.add_argument("--dry-run", action="store_true",
                        help="Print population, rate, projection; no compute")
    parser.add_argument("--harness-only", action="store_true",
                        help="Run cross-validation harness and exit")
    parser.add_argument("--workers", type=int, default=1,
                        help="Spawn N worker subprocesses")
    parser.add_argument("--shard", default=None, metavar="I/N",
                        help="Process the I-th of N deterministic slices")
    parser.add_argument("--orders", default=None,
                        help="Comma-separated order list or range (e.g. 2-64,128)")
    parser.add_argument("--strata", default=None,
                        help="Comma-separated strata filter (e.g. A,B)")
    parser.add_argument("--out-dir", default=str(FEATURES_OUT_DIR),
                        help="Output directory (default: forge/out/features)")
    args = parser.parse_args(argv)

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Parse optional order filter.
    order_set = None
    if args.orders:
        order_set = set()
        for part in args.orders.split(","):
            part = part.strip()
            if "-" in part:
                lo, hi = part.split("-", 1)
                for o in range(int(lo), int(hi) + 1):
                    order_set.add(o)
            else:
                order_set.add(int(part))

    strata_set = None
    if args.strata:
        strata_set = set(s.strip().upper() for s in args.strata.split(","))

    # --- Harness-only mode ---
    if args.harness_only:
        run_extraspecial_harness("")
        return 0

    # --- Toy mode ---
    if args.toy:
        tag = "[toy] "
        print("%s=== Toy mode ===" % tag, flush=True)
        run_extraspecial_harness(tag)

        # Load real records for orders <= 24, falling back to fixture.
        all_records = load_cascade_records()
        targets = select_survivors(all_records,
                                   orders=set(range(2, 25)))
        if len(targets) < 5:
            print("%sUsing bundled fixture (%d records)" % (
                tag, len(TOY_FIXTURE)), flush=True)
            targets = [r for r in TOY_FIXTURE
                       if r["action"] == "SURVIVE"
                       or r["action"].startswith("CAP")]
        else:
            print("%sUsing %d real records (orders <= 24)" % (
                tag, len(targets)), flush=True)

        print("%s--- Base tier ---" % tag, flush=True)
        toy_out = str(out_dir / "toy")
        Path(toy_out).mkdir(parents=True, exist_ok=True)
        run_shard_base(targets, 0, 1, toy_out, tag)

        # Deep tier on same set for exercise.
        print("%s--- Deep tier (all %d) ---" % (tag, len(targets)),
              flush=True)
        run_shard_deep(targets, 0, 1, toy_out, args.timeout, tag)

        print("%sToy mode complete." % tag, flush=True)
        return 0

    # --- Load input ---
    print("Loading cascade records...", flush=True)
    all_records = load_cascade_records()

    if args.deep:
        targets = select_deep_targets(all_records, args.top)
        tier_label = "deep (top %d)" % args.top
        rate = DEEP_RATE
    else:
        targets = select_survivors(all_records, orders=order_set,
                                   strata=strata_set)
        tier_label = "base"
        rate = BASE_RATE

    n_total = len(targets)
    print("Selected %d targets for %s tier" % (n_total, tier_label),
          flush=True)

    if n_total == 0:
        print("ERROR: no targets found. Check checkpoint data.", flush=True)
        return 1

    # --- Dry-run mode ---
    if args.dry_run:
        worker_counts = [1, 2, 4, 8, 16, 32, 64, 128, 224]
        print(forgelib.dry_run_table(
            n_total, rate, worker_counts,
            label="features.sage — %s tier" % tier_label), flush=True)
        if not args.deep:
            # Scaling note for stratum B.
            print("\nStratum-B scaling note: if order-512 census lands,",
                  flush=True)
            print("  survivors grow to ~10.4M at ~0.15 s/group =>"
                  " ~440 core-hours, ~2h on 224 workers.", flush=True)
        return 0

    # --- Multi-worker spawn ---
    if args.workers > 1 and not args.shard:
        extra = ["--out-dir", str(out_dir)]
        if args.deep:
            extra.extend(["--deep", "--top", str(args.top),
                          "--timeout", str(args.timeout)])
        if args.orders:
            extra.extend(["--orders", args.orders])
        if args.strata:
            extra.extend(["--strata", args.strata])
        pool = forgelib.WorkerPool(
            script=str(Path(__file__).resolve()),
            n_workers=args.workers,
            extra_args=extra,
        )
        return pool.run()

    # --- Single shard ---
    shard_i, shard_n = 0, 1
    if args.shard:
        shard_i, shard_n = (int(x) for x in args.shard.split("/"))
        if not 0 <= shard_i < shard_n:
            parser.error("--shard %s: need 0 <= I < N" % args.shard)
    tag = "[shard %d/%d] " % (shard_i, shard_n) if shard_n > 1 else ""

    if args.deep:
        run_shard_deep(targets, shard_i, shard_n, str(out_dir),
                       args.timeout, tag)
    else:
        run_shard_base(targets, shard_i, shard_n, str(out_dir), tag)

    return 0


# The sage CLI executes .sage files inside sage_globals(), not
# under __name__ == "__main__" — an if-guard would silently skip.
# Strip the "--" separator that `sage script.sage -- --flags` requires.
main([a for a in sys.argv[1:] if a != "--"])
