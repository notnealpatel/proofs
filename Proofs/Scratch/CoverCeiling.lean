/-
  Measuring the kernel-`decide` ceiling of `Erdos.Covering.covers_iff_forall_range`.

  The question this answers: `IsFixedDivisorSystem` discharges its coverage
  field by `decide` over `Finset.range L`, where `L` is a common multiple of
  the moduli.  Selfridge's certificate runs at `L = 36` with 7 classes.  How
  far does that scale?  The answer bounds every downstream lane — Brier
  (`L = 180`), Wilf (`L = 8640`), and the covering systems of the
  minimum-modulus literature (`L ≥ 10^14`).

  Test family: the dyadic cover of `ℤ` with lcm `2 ^ a`,

      (2 ^ j - 1  mod  2 ^ (j+1))   for j < a,   plus   (2 ^ a - 1  mod  2 ^ a).

  It is a genuine cover — the first class takes the evens, each later class
  takes half of what remains, and the final class closes the last residue.
  Class count is `a + 1`, so the work is `L · (a + 1)`.

  MEASURED (Lean 4.33.0-rc1, cold `lake env lean`, import baseline 5.33 s):

    | a  |      L | classes | wall     | net decide |
    |----|--------|---------|----------|------------|
    |  6 |     64 |       7 |   5.08 s |     ~0     |
    |  8 |    256 |       9 |   5.79 s |    0.46 s  |
    | 10 |   1024 |      11 |   6.95 s |    1.62 s  |
    | 12 |   4096 |      13 |  15.21 s |    9.88 s  |
    | 14 |  16384 |      15 |  97.68 s |   92.35 s  |
    | 16 |  65536 |      17 | OOM — KILLED BY THE KERNEL |

  ⚠ DO NOT RE-RUN THE `a = 16` CASE UNFENCED.  With the recursion limit
  lifted it exhausted system memory and the OOM killer took the whole
  session down.  The example is commented out below for that reason.  If it
  is ever retried, fence it first — `systemd-run --scope -p MemoryMax=…`;
  `ulimit -v` breaks Lean at startup and is not an option.

  THE CEILING IS MEMORY, NOT TIME.  `a = 14` (L = 16384) completes in 92 s;
  `a = 16` (L = 65536) does not complete at all.  So kernel `decide` on this
  shape tops out between L = 16384 and L = 65536, and the binding resource
  is the memory held by the reduction, not wall clock.

  Growth is superlinear in `L` — 4× in `L` from 4096 to 16384 cost 9.3× in
  time, so roughly `L ^ 1.6`, worse than the `L · |S|` work count predicts.
  That same superlinearity is what makes the memory wall arrive so abruptly.

  Three walls precede any notional "compute budget", in this order:
    * `maxHeartbeats` (default 200000) blocks from `a = 14`;
    * `maxRecDepth` blocks from `a = 16`;
    * system memory, which is fatal and unrecoverable.
  Note that `-DmaxRecDepth=` on the `lean` command line did NOT take effect
  for the `decide` here; the in-file `set_option` is the reliable route.

  CONSEQUENCES FOR THE LANES:
    * Brier (L = 180, ≤ 13 classes) — comfortably inside. Safe.
    * Wilf A083216 (L = 8640, 18 classes, work 155520) — between the
      last success (16384 · 15 = 245760 work, 92 s) and the OOM. Nominally
      inside on work count, but the margin is thin and the failure mode is
      fatal. Fence any attempt.
    * Minimum-modulus literature (Krukenberg m = 18 at L ≈ 4.75·10^14,
      Nielsen/Owens m = 40/42 at L ≈ 10^4495) — unreachable by this route
      by ~10 and ~4490 orders of magnitude respectively. A compositional
      certificate is the only path; brute-force range checking is not it.
-/

import Erdos.Covering.Basic

set_option maxHeartbeats 0
set_option maxRecDepth 20000000

open Erdos.Covering

-- a = 14, L = 16384, 15 classes — the LARGEST CASE THAT COMPLETES (92 s).
example : Covers {(0, 2), (1, 4), (3, 8), (7, 16), (15, 32), (31, 64), (63, 128),
    (127, 256), (255, 512), (511, 1024), (1023, 2048), (2047, 4096), (4095, 8192),
    (8191, 16384), (16383, 16384)} :=
  (covers_iff_forall_range 16384 (by decide) (by decide)).mpr (by decide)

-- a = 16, L = 65536, 17 classes — OOM.  DELIBERATELY COMMENTED OUT: running
-- this exhausted system memory and the kernel OOM killer terminated the
-- session.  Do not uncomment without a `systemd-run --scope -p MemoryMax=…`
-- fence.  This is the measurement, recorded as a disabled witness rather
-- than as a live check.
--
-- example : Covers {(0, 2), (1, 4), (3, 8), (7, 16), (15, 32), (31, 64), (63, 128),
--     (127, 256), (255, 512), (511, 1024), (1023, 2048), (2047, 4096), (4095, 8192),
--     (8191, 16384), (16383, 32768), (32767, 65536), (65535, 65536)} :=
--   (covers_iff_forall_range 65536 (by decide) (by decide)).mpr (by decide)
