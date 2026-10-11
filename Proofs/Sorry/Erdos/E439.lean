/-
  Erdős Problem #439 — monochromatic pairs summing to a square.
  Status: proved (Khalfalah–Szemerédi 2006).  Tier D archive with
  finite-instance sanity layer.

  Verbatim statement (`goof erdos fetch 439`, pulled 2026-08-05):

    "Is it true that, in any finite colouring of the integers, there
    must be two integers $x\neq y$ of the same colour such that $x+y$
    is a square? What about a $k$th power?"

  DB remarks: question of Roth–Erdős–Sárközy–Sós [ESS89] (or
  Erdős–Silverman 1977 per [Er80c]).  ESS89 proved it for 2 or 3
  colors.  Equivalent: the graph on ℕ joining m, n when m + n is a
  square has chromatic number ℵ₀.  Khalfalah–Szemerédi [KhSz06]
  proved it in general, indeed for x + y = f(z) for any nonconstant
  f ∈ ℤ[z] with 2 ∣ f(z) for some z.

  Mathlib inventory: colorings as `ℕ → Fin K`; `IsSquare` on ℕ.
  The density-Ramsey proof is out of reach; the sanity layer is
  finite instances by decide.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E439

/-- `MonoSquarePair c`: two distinct positive integers of the same
    `c`-color summing to a perfect square.  (Positivity keeps the
    trivial x = 0, y = 0… x ≠ y already blocks the diagonal; we work
    on positive integers per the problem's "the integers" =
    {1, 2, …} convention in ESS89.) -/
def MonoSquarePair {K : ℕ} (c : ℕ → Fin K) : Prop :=
  ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ x ≠ y ∧ c x = c y ∧ IsSquare (x + y)

/-- **Erdős #439, Khalfalah–Szemerédi theorem** ([KhSz06]): every
    finite coloring of the positive integers has a monochromatic
    pair `x ≠ y` with `x + y` a perfect square.

    Archive rationale: the proof is density-Ramsey (Szemerédi-type
    machinery on the squares); out of formalization reach.  The
    finite-instance layer below is the sorry-free lane. -/
theorem khalfalah_szemeredi (K : ℕ) (hK : 1 ≤ K) (c : ℕ → Fin K) :
    MonoSquarePair c := by
  sorry

/-- **ESS89 (2 and 3 colors)**, archived separately — proved much
    earlier and possibly within reach of an elementary treatment:
    the 2-color case is a finite check on a suitable interval (see
    the finite instance below); the 3-color case is genuinely
    harder. -/
theorem ess_two_colors (c : ℕ → Fin 2) : MonoSquarePair c := by
  sorry

/-- **Finite 2-color instance (the decide target)**: there is an `N`
    such that every 2-coloring of `{1, …, N}` has a monochromatic
    pair summing to a square.  The minimal such `N` is known to be
    small (probe with sage/SAT: candidates suggest N well under 100;
    2^N colorings brute-force is out but SAT/decide on the derived
    hypergraph is fine).  Stated at N = 100 pending the probe;
    tighten after.  -- PROVABLE-in-principle (native_decide /
    SAT-replay). -/
theorem finite_instance_100 (c : ℕ → Fin 2) :
    ∃ x y : ℕ, 1 ≤ x ∧ x ≤ 100 ∧ 1 ≤ y ∧ y ≤ 100 ∧ x ≠ y ∧
      c x = c y ∧ IsSquare (x + y) := by
  sorry

/-- Sharpness floor: small intervals DO admit square-sum-free
    2-colorings — on `{1, …, 10}` the coloring {1,2,4,6,9} vs
    {3,5,7,8,10} works (review-corrected witness: no same-class pair
    sums to 4, 9, or 16; the earlier draft's {…,10} class broke at
    6 + 10 = 16).  Keeps `finite_instance_100`'s N honest (N = 10 is
    too small).  -- PROVABLE (decide on the explicit coloring). -/
theorem small_interval_escape :
    ∃ c : ℕ → Fin 2, ∀ x y : ℕ, 1 ≤ x → x ≤ 10 → 1 ≤ y → y ≤ 10 →
      x ≠ y → c x = c y → ¬ IsSquare (x + y) := by
  sorry

/-- **The k-th power generalization** (also resolved by [KhSz06] via
    the f(z) = z^k form when the parity condition holds — note
    x + y = z^k needs the KhSz "2 ∣ f(z) for some z" hypothesis,
    satisfied for all pure powers), archived. -/
theorem kth_power_version (k K : ℕ) (hk : 2 ≤ k) (hK : 1 ≤ K)
    (c : ℕ → Fin K) :
    ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ x ≠ y ∧ c x = c y ∧
      ∃ z : ℕ, x + y = z ^ k := by
  sorry

end ErdosCandidates.E439

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Verbatim statement matches `goof erdos fetch 439` exactly.
   - ESS89 / Khalfalah-Szemeredi attributions and the f(z) generalization with
     the 2 | f(z) parity condition all confirmed against the DB sections.
   - Positivity convention (1 <= x): the source says "the integers" but the DB
     reformulation uses N.  Restricting to positive integers is strictly
     stronger (fewer pairs), so the formalization is a valid upper bound on the
     original claim.  Defensible but not literally faithful to "the integers."
   - FLAG (docstring only, not statement): the small_interval_escape docstring
     suggests witness {1,2,4,6,9,10} vs {3,5,7,8}, but 6+10=16 is a perfect
     square, so both are in the same color -- the witness is wrong.  A correct
     2-coloring is {1,2,4,6,9} vs {3,5,7,8,10}.  The theorem statement itself
     (existentially quantified) is unaffected.
   - kth_power_version correctly uses z^k and matches the source's "What about
     a kth power?" question plus the KhSz06 general result.
-/
