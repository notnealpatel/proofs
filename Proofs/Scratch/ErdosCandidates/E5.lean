/-
  Erdős Problem #5 — limit points of normalized prime gaps.
  Status: open.  Tier B archive target (statement + sanity only).

  Verbatim statement (`goof erdos fetch 5`, pulled 2026-08-05):

    "Let $C\geq 0$. Is there an infinite sequence of $n_i$ such that
    \[\lim_{i\to \infty}\frac{p_{n_i+1}-p_{n_i}}{\log n_i}=C?\]"

  DB remarks: with S = set of limit points of (p_{n+1} − p_n)/log n,
  the problem asks whether S = [0, ∞].  Known: ∞ ∈ S (Westzynthius
  1931); 0 ∈ S (Goldston–Pintz–Yıldırım 2009); S has positive Lebesgue
  measure (Erdős 1955, Ricci 1956); S contains arbitrarily large finite
  numbers (Hildebrand–Maier 1988); [0, c] ⊆ S for some c > 0 (Pintz
  2016); ≥ 12.5% of [0,∞) (Banks–Freiberg–Maynard 2016); ≥ 1/3
  (Merikoski 2020), and S has bounded gaps.  Comment thread: the only
  explicitly known members of S are 0 and ∞ (even C = 1 is open!).

  OEIS anchor: A001223 (prime gaps: 1, 2, 2, 4, 2, 4, 2, 4, 6, 2, …).

  Mathlib inventory (leandoc 2026-08-05): `Nat.nth Nat.Prime` for p_n
  (0-indexed: `Nat.nth Nat.Prime 0 = 2`); `MapClusterPt` (Topology/
  Defs/Filter.lean) for limit points of a sequence along `atTop`;
  `Real.log`.  The ∞ endpoint is handled as a separate unboundedness
  statement rather than dragging the statement into `EReal`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E5

/-- The `n`-th prime, 0-indexed: `p 0 = 2, p 1 = 3, …`. -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The normalized prime gap `(p_{n+1} − p_n)/log n : ℝ`.  Subtraction
    is performed after casting (STYLE.md); `log 0 = log 1 = 0` junk at
    `n ≤ 1` is irrelevant to limit-point statements along `atTop`. -/
noncomputable def gap (n : ℕ) : ℝ :=
  ((p (n + 1) : ℝ) - (p n : ℝ)) / Real.log n

/-- Ground truth: `p 0 = 2`, `p 1 = 3`, `p 4 = 11`; first gaps
    (A001223): 1, 2, 2, 4, 2, ….  -- PROVABLE
    (`Nat.nth_count` / `Nat.count_eq` evaluation lemmas). -/
example : p 0 = 2 ∧ p 1 = 3 ∧ p 4 = 11 ∧ p 5 - p 4 = 2 := by
  sorry

/-- **Erdős #5 (OPEN)**: every `C ≥ 0` is a limit point of the
    normalized prime gaps — i.e. `S = [0, ∞]` (the finite part; the
    `∞` part is `westzynthius_unbounded` below and is a theorem).

    Source text: "Let $C\geq 0$. Is there an infinite sequence of
    $n_i$ such that $\lim (p_{n_i+1}-p_{n_i})/\log n_i = C$?"

    `MapClusterPt C atTop gap` is precisely "some subsequence of `gap`
    tends to `C`" (for the metrizable target ℝ, cluster points of a
    sequence = subsequential limits: `mapClusterPt_iff_frequently` +
    `TopologicalSpace.FirstCountableTopology` extraction).  Even C = 1
    is open (comment thread). -/
theorem erdos_5 (C : ℝ) (hC : 0 ≤ C) :
    MapClusterPt C Filter.atTop gap := by
  sorry

/-- **Westzynthius 1931** (the `∞ ∈ S` part), archived: the normalized
    gaps are unbounded — `limsup = ∞` stated as frequent exceedance of
    every bound.  A genuine (hard but classical) analytic target; the
    Erdős–Rankin method chain is not in Mathlib. -/
theorem westzynthius_unbounded (M : ℝ) :
    ∃ᶠ n in Filter.atTop, M < gap n := by
  sorry

/-- **Goldston–Pintz–Yıldırım 2009** (the `0 ∈ S` part), archived:
    `0` is a limit point — small gaps infinitely often at scale
    `o(log n)`.  Deep sieve theory; archive only. -/
theorem gpy_zero_cluster : MapClusterPt (0 : ℝ) Filter.atTop gap := by
  sorry

/-- **Merikoski 2020** (best density result), archived: at least 1/3 of
    `[0, T]` consists of limit points, for large `T`.  Stated via
    Lebesgue `volume` on the cluster-point set. -/
theorem merikoski_density :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ENNReal.ofReal (T / 3) ≤
        MeasureTheory.volume
          {C : ℝ | C ∈ Set.Icc 0 T ∧ MapClusterPt C Filter.atTop gap} := by
  sorry

/-- Sanity: the cluster-point set is closed (Weisenberg's remark in the
    DB: "clearly S is closed", which is why density in `[0,∞]` is
    equivalent to equality).  -- PROVABLE (cluster-point sets of a
    fixed filter are closed; `MapClusterPt` unfolds to `ClusterPt` of
    the pushforward, and the set of cluster points of any filter is
    closed — `isClosed_setOf_clusterPt` in Mathlib). -/
theorem clusterPt_set_closed :
    IsClosed {C : ℝ | MapClusterPt C Filter.atTop gap} := by
  sorry

/-- Computational sanity layer: normalized-gap values at moderate n are
    near small rationals — e.g. `gap` at the 4th prime (p₄ = 11,
    p₅ = 13) is `2 / log 4 ≈ 1.44`.  Bracketed to pin the def's
    orientation (numerator = forward difference, denominator = log of
    the INDEX n, not of p_n — a classic transcription hazard; the DB
    uses log n_i).  -- PROVABLE (interval arithmetic on log). -/
example : 1 < gap 4 ∧ gap 4 < 2 := by
  sorry

end ErdosCandidates.E5

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB exactly.
   - Denominator is log n (index), not log p_n -- matches DB formula
     "log n_i" and the file's explicit hazard note.  gap def uses
     Real.log n, correct.
   - p is 0-indexed via Nat.nth Nat.Prime, so p 0 = 2, p 4 = 11,
     p 5 = 13.  gap 4 = (13-11)/log 4 = 2/log 4 ~ 1.44; the bracket
     1 < gap 4 < 2 is correct.
   - A001223 prefix 1,2,2,4,2 matches (p1-p0=1, p2-p1=2, p3-p2=2,
     p4-p3=4, p5-p4=2).
   - MapClusterPt usage for subsequential limits is faithful to the
     "infinite sequence n_i with lim = C" formulation.
   - All attributed partial results (Westzynthius, GPY, Erdos/Ricci,
     Hildebrand-Maier, Pintz, BFM, Merikoski) match DB sections.
   - Merikoski "at least 1/3" and BFM "at least 12.5%" match DB.
   - "Even C=1 is open" matches Thomas Bloom's comment reply.
   - Weisenberg's "S is closed" remark matches DB text; the
     clusterPt_set_closed sanity lemma is well-motivated.
-/
