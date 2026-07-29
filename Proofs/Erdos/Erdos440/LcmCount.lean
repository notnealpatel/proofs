/-
  Erdős Problem #440 — counting consecutive pairs with small lcm.

  Problem (https://www.erdosproblems.com/440): let A = {a₁ < a₂ < ⋯} ⊆ ℕ
  be an infinite set of positive integers and let A(x) count the indices i
  with lcm(aᵢ, aᵢ₊₁) ≤ x.  Is it true that A(x) ≪ x^{1/2}?

  Status: solved (positively).  Erdős and Szemerédi [ErSz80] proved
  A(x) ≤ (c + o(1))·x^{1/2} with the optimal constant
  c = Σ_{n≥1} 1/(n^{1/2}(n+1)) = Σ_{n≥1} (√n − √(n−1))/n ≈ 1.86, and that
  this constant is best possible.  Terence Tao (comment on the problem
  page, 2025-10-26) gave a short self-contained dyadic argument for
  A(x) ≪ x^{1/2}: if aᵢ ≥ k√x and lcm(aᵢ, aᵢ₊₁) ≤ x then
  gcd(aᵢ, aᵢ₊₁) ≥ k², hence aᵢ₊₁ − aᵢ ≥ k², so there are only
  O(2^{−m}√x) counted indices with aᵢ ≍ 2^m√x; summing the geometric
  series in m gives the bound.  A modern write-up of the optimal-constant
  finitary result is by R. van Doorn (see the problem page).

  THIS FILE formalizes the finitary, explicit-constant form of Tao's
  argument, for a sequence `a : ℕ → ℕ` (0-indexed) with `StrictMono a`
  and `1 ≤ a 0`:

  * `erdos440` (MAIN):  for every `x`,
        #{i ∈ [0,x) : lcm (a i) (a (i+1)) ≤ x} ≤ 5·√x
    where `√` is `Nat.sqrt` (no hypothesis on `x`; for `x = 0` both sides
    vanish).  Since every counted index automatically satisfies `i < x`
    (`good_carrier_stable`), the window `[0, x)` loses nothing: this is
    the full positive answer to #440 with the explicit constant C = 5.
  * `erdos440'` — the task-card form, `≤ 5·√x + 5` for `1 ≤ x`, a fortiori.
  * `good_carrier_stable` — carrier exhaustiveness: enlarging the index
    window `range x` to `range y`, `y ≥ x`, does not change the counted set.
  * `erdos440_sharp` — sharpness of the order √x: for `a i = i + 1`
    (i.e. A = ℕ) at least `√x − 1` indices are counted.  The √x order is
    attained; no claim is made about the constant (optimal ≈ 1.86, not
    chased here — internally the proof gives `4·√x + 2`, relaxed to 5·√x).

  HONEST CLAIM BOUNDARY.  We prove the explicit-constant finitary bound
  C = 5, not the Erdős–Szemerédi optimal constant, and we do not
  formalize the second half of #440 (how large can liminf A(x)/√x be).
  The hypothesis `1 ≤ a 0` (positivity) is essential to the method:
  `Nat.lcm 0 n = 0`, so an index with `a i = 0` is counted for free and
  the gcd·lcm identity degenerates.

  Method notes.  Everything is ℕ-elementary, using `Nat.sqrt` and
  `Nat.log 2` bookkeeping; no real numbers.  The gcd step is
  `Nat.gcd_mul_lcm` plus `x < (√x + 1)²`, phrased multiplicatively to
  avoid division.  Library survey (2026-07-12, local Mathlib): Mathlib
  has no counting lemma for "gap-separated" finite sets of naturals
  (closest hit: `Besicovitch.card_le_of_separated`), so the bucketing
  primitive `card_le_of_gap` below is proved from scratch by injecting
  into `range (W/g + 1)` via `i ↦ (v i − L)/g`.  SageMath kill-test of
  the exact statement (4 families: ℕ, evens, primes, an lcm-dense chain;
  x ≤ 2·10⁵): no violation of `count ≤ 5·√x`, worst ratio count/√x = 1.0.

  Axiom audit (2026-07-12, `#print axioms` via `lake env lean`):
  `erdos440`, `erdos440'`, `erdos440_sharp`, `good_carrier_stable`,
  `card_le_of_gap` all depend on exactly propext, Classical.choice,
  Quot.sound.  No `sorryAx`, no `native_decide`.

  References:
  [ErSz80] Erdős, P. and Szemerédi, E., "Remarks on a problem of the
           American Mathematical Monthly" (Hungarian), Mat. Lapok 28
           (1980), 121–124.
  [Tao25]  T. Tao, comment on erdosproblems.com/440, 2025-10-26.
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace Erdos440

-- ════════════════════════════════════════════════════════════════════
-- §1 THE COUNTING PRIMITIVE: GAP-SEPARATED SETS IN A WINDOW
-- ════════════════════════════════════════════════════════════════════

/-- **Counting primitive** (absent from Mathlib, cf. header): if the values
`v i`, `i ∈ S`, lie in the window `[L, L + W)` and any two distinct members
of `S` have values at least `g > 0` apart, then `S.card ≤ W / g + 1`.
Proof: `i ↦ (v i − L) / g` maps `S` injectively into `range (W / g + 1)`. -/
theorem card_le_of_gap {S : Finset ℕ} {v : ℕ → ℕ} {L W g : ℕ} (hg : 0 < g)
    (hlo : ∀ i ∈ S, L ≤ v i) (hhi : ∀ i ∈ S, v i < L + W)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, i < j → v i + g ≤ v j) :
    S.card ≤ W / g + 1 := by
  have key : ∀ i ∈ S, ∀ j ∈ S, i < j → (v i - L) / g ≠ (v j - L) / g := by
    intro i hi j hj hij heq
    have hL : L ≤ v i := hlo i hi
    have hgapij : v i + g ≤ v j := hgap i hi j hj hij
    have e3 : (v i - L) + g ≤ v j - L := by omega
    have e1 : (v j - L) / g * g ≤ v i - L := heq ▸ Nat.div_mul_le_self (v i - L) g
    have e2 : v j - L < (v j - L) / g * g + g := by
      conv_lhs => rw [← Nat.div_add_mod' (v j - L) g]
      exact Nat.add_lt_add_left (Nat.mod_lt _ hg) _
    have e4 : (v j - L) / g * g + g ≤ (v i - L) + g := Nat.add_le_add_right e1 g
    exact absurd (lt_of_lt_of_le (lt_of_lt_of_le e2 e4) e3) (lt_irrefl _)
  calc S.card ≤ (Finset.range (W / g + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun i => (v i - L) / g) ?_ ?_
        · intro i hi
          simp only [Finset.mem_coe] at hi
          simp only [Finset.mem_coe, Finset.mem_range]
          have h1 : v i - L ≤ W := by have := hhi i hi; omega
          exact Nat.lt_succ_of_le (Nat.div_le_div_right h1)
        · intro i hi j hj heq
          simp only [Finset.mem_coe] at hi hj
          rcases Nat.lt_trichotomy i j with h | h | h
          · exact absurd heq (key i hi j hj h)
          · exact h
          · exact absurd heq.symm (key j hj i hi h)
    _ = W / g + 1 := Finset.card_range _

-- ════════════════════════════════════════════════════════════════════
-- §2 THE COUNTED SET AND ITS BASIC BOUNDS
-- ════════════════════════════════════════════════════════════════════

/-- The counted ("good") indices below `x`: those `i < x` with
`lcm (a i) (a (i+1)) ≤ x`.  By `good_carrier_stable` the window `range x`
captures *every* index with small lcm, so `(good a x).card` is the
quantity `A(x)` of Erdős #440. -/
def good (a : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i => Nat.lcm (a i) (a (i + 1)) ≤ x

theorem mem_good {a : ℕ → ℕ} {x i : ℕ} :
    i ∈ good a x ↔ i < x ∧ Nat.lcm (a i) (a (i + 1)) ≤ x := by
  simp only [good, Finset.mem_filter, Finset.mem_range]

/-- A strictly increasing ℕ-sequence with `a 0 ≥ 1` satisfies `i + 1 ≤ a i`. -/
theorem add_one_le_apply {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0) (i : ℕ) :
    i + 1 ≤ a i := by
  induction i with
  | zero => exact h0
  | succ n ih => have h : a n < a (n + 1) := ha (Nat.lt_succ_self n); omega

/-- At a good index both terms are `≤ x`, and moreover `i + 2 ≤ x`
(the term `a (i+1)` divides the lcm and dominates `i + 2`). -/
theorem good_bounds {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0) {x i : ℕ}
    (hgood : Nat.lcm (a i) (a (i + 1)) ≤ x) :
    a i ≤ x ∧ a (i + 1) ≤ x ∧ i + 2 ≤ x := by
  have h1 : 0 < a i := by have := add_one_le_apply ha h0 i; omega
  have h2 : 0 < a (i + 1) := by have := add_one_le_apply ha h0 (i + 1); omega
  have hpos : 0 < Nat.lcm (a i) (a (i + 1)) := Nat.lcm_pos h1 h2
  have hl : a i ≤ Nat.lcm (a i) (a (i + 1)) :=
    Nat.le_of_dvd hpos (Nat.dvd_lcm_left _ _)
  have hr : a (i + 1) ≤ Nat.lcm (a i) (a (i + 1)) :=
    Nat.le_of_dvd hpos (Nat.dvd_lcm_right _ _)
  have h3 := add_one_le_apply ha h0 (i + 1)
  omega

/-- **Carrier exhaustiveness**: every index with `lcm (a i) (a (i+1)) ≤ x`
automatically satisfies `i < x`, so filtering any larger window
`range y`, `y ≥ x`, yields the same finite set.  This justifies stating
`erdos440` over the window `range x`. -/
theorem good_carrier_stable {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0)
    {x y : ℕ} (hxy : x ≤ y) :
    ((Finset.range y).filter fun i => Nat.lcm (a i) (a (i + 1)) ≤ x)
      = (Finset.range x).filter fun i => Nat.lcm (a i) (a (i + 1)) ≤ x := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    have := (good_bounds ha h0 h).2.2
    exact ⟨by omega, h⟩
  · rintro ⟨hi, h⟩
    exact ⟨by omega, h⟩

-- ════════════════════════════════════════════════════════════════════
-- §3 TAO'S GCD/GAP INEQUALITY
-- ════════════════════════════════════════════════════════════════════

/-- **Tao's key step** [Tao25]: if `i` is good for `x` and
`a i ≥ k·(√x + 1)`, then `gcd (a i) (a (i+1)) ≥ k²` — because
`gcd·lcm = a i · a (i+1) ≥ k²(√x+1)² > k²x ≥ k²·lcm` — and since the gcd
divides the positive difference, `a (i+1) ≥ a i + k²`.  (We use
`√x + 1` rather than `√x` because `Nat.sqrt` rounds down:
`x < (√x + 1)²` is what makes the multiplicative step go through.) -/
theorem gap_of_le {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0) {x i k : ℕ}
    (hgood : Nat.lcm (a i) (a (i + 1)) ≤ x)
    (hk : k * (Nat.sqrt x + 1) ≤ a i) :
    a i + k * k ≤ a (i + 1) := by
  have h1 : 0 < a i := by have := add_one_le_apply ha h0 i; omega
  have h2 : 0 < a (i + 1) := by have := add_one_le_apply ha h0 (i + 1); omega
  have hlpos : 0 < Nat.lcm (a i) (a (i + 1)) := Nat.lcm_pos h1 h2
  have hmono : a i < a (i + 1) := ha (Nat.lt_succ_self i)
  have hgcd : k * k ≤ Nat.gcd (a i) (a (i + 1)) := by
    have hxs : Nat.lcm (a i) (a (i + 1)) ≤ (Nat.sqrt x + 1) * (Nat.sqrt x + 1) :=
      le_trans hgood (Nat.le_of_lt (Nat.lt_succ_sqrt x))
    have key : k * k * Nat.lcm (a i) (a (i + 1))
        ≤ Nat.gcd (a i) (a (i + 1)) * Nat.lcm (a i) (a (i + 1)) := by
      calc k * k * Nat.lcm (a i) (a (i + 1))
          ≤ k * k * ((Nat.sqrt x + 1) * (Nat.sqrt x + 1)) := Nat.mul_le_mul le_rfl hxs
        _ = (k * (Nat.sqrt x + 1)) * (k * (Nat.sqrt x + 1)) := by ring
        _ ≤ a i * a (i + 1) := Nat.mul_le_mul hk (le_trans hk (Nat.le_of_lt hmono))
        _ = Nat.gcd (a i) (a (i + 1)) * Nat.lcm (a i) (a (i + 1)) :=
            (Nat.gcd_mul_lcm _ _).symm
    exact Nat.le_of_mul_le_mul_right key hlpos
  have hdvd : Nat.gcd (a i) (a (i + 1)) ∣ a (i + 1) - a i :=
    Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have hgap : Nat.gcd (a i) (a (i + 1)) ≤ a (i + 1) - a i :=
    Nat.le_of_dvd (by omega) hdvd
  omega

-- ════════════════════════════════════════════════════════════════════
-- §4 DYADIC BLOCKS
-- ════════════════════════════════════════════════════════════════════

/-- The `m`-th dyadic block of good indices:
`a i ∈ [2^m·(√x + 1), 2^{m+1}·(√x + 1))`. -/
def block (a : ℕ → ℕ) (x m : ℕ) : Finset ℕ :=
  (good a x).filter fun i =>
    2 ^ m * (Nat.sqrt x + 1) ≤ a i ∧ a i < 2 ^ (m + 1) * (Nat.sqrt x + 1)

theorem mem_block {a : ℕ → ℕ} {x m i : ℕ} :
    i ∈ block a x m ↔ i ∈ good a x
      ∧ 2 ^ m * (Nat.sqrt x + 1) ≤ a i ∧ a i < 2 ^ (m + 1) * (Nat.sqrt x + 1) := by
  simp only [block, Finset.mem_filter]

/-- In the `m`-th block, consecutive good indices are `4^m` apart in value
(`gap_of_le` with `k = 2^m`), and the block window has width `2^m(√x+1)`,
so the block holds at most `(√x + 1)/2^m + 1` indices. -/
theorem block_card_le {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0) (x m : ℕ) :
    (block a x m).card ≤ (Nat.sqrt x + 1) / 2 ^ m + 1 := by
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  have hEq : 2 ^ m * (Nat.sqrt x + 1) / (2 ^ m * 2 ^ m) = (Nat.sqrt x + 1) / 2 ^ m :=
    Nat.mul_div_mul_left _ _ h2m
  rw [← hEq]
  refine card_le_of_gap (v := a) (L := 2 ^ m * (Nat.sqrt x + 1))
    (Nat.mul_pos h2m h2m) ?_ ?_ ?_
  · intro i hi
    exact (mem_block.mp hi).2.1
  · intro i hi
    have h1 := (mem_block.mp hi).2.2
    have h2 : 2 ^ (m + 1) * (Nat.sqrt x + 1)
        = 2 ^ m * (Nat.sqrt x + 1) + 2 ^ m * (Nat.sqrt x + 1) := by
      rw [pow_succ]; ring
    omega
  · intro i hi j hj hij
    have hgood : Nat.lcm (a i) (a (i + 1)) ≤ x := (mem_good.mp (mem_block.mp hi).1).2
    have hstep : a i + 2 ^ m * 2 ^ m ≤ a (i + 1) :=
      gap_of_le ha h0 hgood (mem_block.mp hi).2.1
    have hmono : a (i + 1) ≤ a j := ha.monotone (by omega)
    omega

/-- Good indices with `a i ≤ √x` number at most `√x` (they satisfy
`i + 1 ≤ a i ≤ √x`). -/
theorem low_card_le {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0) (x : ℕ) :
    ((good a x).filter fun i => a i < Nat.sqrt x + 1).card ≤ Nat.sqrt x := by
  have hsub : ((good a x).filter fun i => a i < Nat.sqrt x + 1)
      ⊆ Finset.range (Nat.sqrt x) := by
    intro i hi
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := add_one_le_apply ha h0 i
    exact Finset.mem_range.mpr (by omega)
  calc ((good a x).filter fun i => a i < Nat.sqrt x + 1).card
      ≤ (Finset.range (Nat.sqrt x)).card := Finset.card_le_card hsub
    _ = Nat.sqrt x := Finset.card_range _

/-- **Dyadic covering**: every good index has either `a i ≤ √x`, or
`a i ∈ [2^m(√x+1), 2^{m+1}(√x+1))` for the scale
`m = log₂ (a i / (√x+1))`; since `a i ≤ x < (√x+1)²`, only scales
`m ≤ log₂ √x` occur. -/
theorem good_cover {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0) (x : ℕ) :
    good a x ⊆ ((good a x).filter fun i => a i < Nat.sqrt x + 1)
      ∪ (Finset.range (Nat.log 2 (Nat.sqrt x) + 1)).biUnion (block a x) := by
  intro i hi
  rcases Nat.lt_or_ge (a i) (Nat.sqrt x + 1) with hsmall | hbig
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hsmall⟩)
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ?_)
    have hgood : Nat.lcm (a i) (a (i + 1)) ≤ x := (mem_good.mp hi).2
    have hax : a i ≤ x := (good_bounds ha h0 hgood).1
    have hspos : 0 < Nat.sqrt x + 1 := by omega
    have hq1 : 1 ≤ a i / (Nat.sqrt x + 1) :=
      (Nat.le_div_iff_mul_le hspos).mpr (by omega)
    have hqs : a i / (Nat.sqrt x + 1) ≤ Nat.sqrt x := by
      have h1 : a i / (Nat.sqrt x + 1) < Nat.sqrt x + 1 :=
        (Nat.div_lt_iff_lt_mul hspos).mpr
          (lt_of_le_of_lt hax (Nat.lt_succ_sqrt x))
      omega
    refine ⟨Nat.log 2 (a i / (Nat.sqrt x + 1)), ?_, ?_⟩
    · refine Finset.mem_range.mpr ?_
      have := Nat.log_mono_right (b := 2) hqs
      omega
    · refine mem_block.mpr ⟨hi, ?_, ?_⟩
      · have h1 : 2 ^ Nat.log 2 (a i / (Nat.sqrt x + 1)) ≤ a i / (Nat.sqrt x + 1) :=
          Nat.pow_log_le_self 2 (by omega)
        exact (Nat.le_div_iff_mul_le hspos).mp h1
      · have h2 : a i / (Nat.sqrt x + 1)
            < 2 ^ (Nat.log 2 (a i / (Nat.sqrt x + 1)) + 1) :=
          Nat.lt_pow_succ_log_self (by omega) _
        exact (Nat.div_lt_iff_lt_mul hspos).mp h2

-- ════════════════════════════════════════════════════════════════════
-- §5 THE GEOMETRIC SERIES, IN ℕ-DIVISION
-- ════════════════════════════════════════════════════════════════════

/-- `∑_{m<N} n / 2^m ≤ 2n`: the geometric series bound survives
ℕ-division (each floor only loses).  Induction peeling `m = 0` and
halving `n`. -/
theorem sum_div_two_pow_le (N : ℕ) : ∀ n : ℕ,
    (∑ m ∈ Finset.range N, n / 2 ^ m) ≤ 2 * n := by
  induction N with
  | zero => intro n; simp
  | succ N ih =>
    intro n
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one]
    have hshift : (∑ m ∈ Finset.range N, n / 2 ^ (m + 1))
        = ∑ m ∈ Finset.range N, n / 2 / 2 ^ m :=
      Finset.sum_congr rfl fun m _ => by
        rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [hshift]
    have h1 := ih (n / 2)
    omega

-- ════════════════════════════════════════════════════════════════════
-- §6 ASSEMBLY AND MAIN THEOREMS
-- ════════════════════════════════════════════════════════════════════

/-- Assembly of the dyadic count: `A(x) ≤ 4·√x + 2` for `x ≥ 1`.
(low block ≤ √x) + (∑ blocks ≤ 2(√x+1) + #scales) with
#scales = log₂ √x + 1 ≤ √x. -/
theorem good_card_le {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 1 ≤ a 0) {x : ℕ}
    (hx : 0 < x) :
    (good a x).card ≤ 4 * Nat.sqrt x + 2 := by
  have h1 : (good a x).card
      ≤ ((good a x).filter fun i => a i < Nat.sqrt x + 1).card
        + ((Finset.range (Nat.log 2 (Nat.sqrt x) + 1)).biUnion (block a x)).card := by
    calc (good a x).card
        ≤ (((good a x).filter fun i => a i < Nat.sqrt x + 1)
            ∪ (Finset.range (Nat.log 2 (Nat.sqrt x) + 1)).biUnion (block a x)).card :=
          Finset.card_le_card (good_cover ha h0 x)
      _ ≤ _ := Finset.card_union_le _ _
  have h2 : ((Finset.range (Nat.log 2 (Nat.sqrt x) + 1)).biUnion (block a x)).card
      ≤ ∑ m ∈ Finset.range (Nat.log 2 (Nat.sqrt x) + 1), (block a x m).card :=
    Finset.card_biUnion_le
  have h3 : (∑ m ∈ Finset.range (Nat.log 2 (Nat.sqrt x) + 1), (block a x m).card)
      ≤ ∑ m ∈ Finset.range (Nat.log 2 (Nat.sqrt x) + 1), ((Nat.sqrt x + 1) / 2 ^ m + 1) :=
    Finset.sum_le_sum fun m _ => block_card_le ha h0 x m
  have h4 : (∑ m ∈ Finset.range (Nat.log 2 (Nat.sqrt x) + 1), ((Nat.sqrt x + 1) / 2 ^ m + 1))
      = (∑ m ∈ Finset.range (Nat.log 2 (Nat.sqrt x) + 1), (Nat.sqrt x + 1) / 2 ^ m)
        + (Nat.log 2 (Nat.sqrt x) + 1) := by
    rw [Finset.sum_add_distrib, ← Finset.card_eq_sum_ones, Finset.card_range]
  have h5 : (∑ m ∈ Finset.range (Nat.log 2 (Nat.sqrt x) + 1), (Nat.sqrt x + 1) / 2 ^ m)
      ≤ 2 * (Nat.sqrt x + 1) :=
    sum_div_two_pow_le (Nat.log 2 (Nat.sqrt x) + 1) (Nat.sqrt x + 1)
  have h6 : ((good a x).filter fun i => a i < Nat.sqrt x + 1).card ≤ Nat.sqrt x :=
    low_card_le ha h0 x
  have h7 : Nat.log 2 (Nat.sqrt x) < Nat.sqrt x := by
    have hs1 : 0 < Nat.sqrt x := Nat.sqrt_pos.mpr hx
    exact Nat.log_lt_self 2 (by omega)
  omega

/-- **Erdős Problem #440** (positive answer, explicit constant; finitary
form of [Tao25], first proved in [ErSz80]).  For a strictly increasing
sequence of positive integers `a`, the number of indices `i < x` with
`lcm (a i) (a (i+1)) ≤ x` is at most `5·√x`.  By `good_carrier_stable`
every index with small lcm satisfies `i < x`, so this bounds the full
count `A(x)`; the optimal constant (≈ 1.86, [ErSz80]) is not claimed. -/
theorem erdos440 (a : ℕ → ℕ) (ha : StrictMono a) (h0 : 1 ≤ a 0) (x : ℕ) :
    ((Finset.range x).filter fun i => Nat.lcm (a i) (a (i + 1)) ≤ x).card
      ≤ 5 * Nat.sqrt x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  show (good a x).card ≤ 5 * Nat.sqrt x
  rcases Nat.lt_or_ge x 9 with hx9 | hx9
  · -- tiny `x`: the crude bound `A(x) ≤ x` already wins
    have hcard : (good a x).card ≤ x := by
      calc (good a x).card ≤ (Finset.range x).card := Finset.card_filter_le _ _
        _ = x := Finset.card_range x
    have hs1 : 1 ≤ Nat.sqrt x := Nat.sqrt_pos.mpr hx
    rcases Nat.lt_or_ge x 4 with hx4 | hx4
    · omega
    · have hs2 : 2 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by omega)
      omega
  · -- main branch: `4√x + 2 ≤ 5√x` once `√x ≥ 3`
    have h := good_card_le ha h0 hx
    have hs3 : 3 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by omega)
    omega

/-- The task-card form of `erdos440`, with the (redundant) hypothesis
`1 ≤ x` and additive slack.  Immediate from `erdos440`. -/
theorem erdos440' (a : ℕ → ℕ) (ha : StrictMono a) (h0 : 1 ≤ a 0) (x : ℕ)
    (_hx : 1 ≤ x) :
    ((Finset.range x).filter fun i => Nat.lcm (a i) (a (i + 1)) ≤ x).card
      ≤ 5 * Nat.sqrt x + 5 := by
  have := erdos440 a ha h0 x
  omega

/-- **Sharpness of the √x order**: for the sequence `a i = i + 1` (that is,
`A = ℕ`), at least `√x − 1` indices are counted, since
`lcm (i+1) (i+2) ∣ (i+1)(i+2) ≤ x` whenever `i + 2 ≤ √x`.  So `erdos440`
is best possible up to the constant (which is ≈ 1.86 [ErSz80], not 5;
we do not claim constant optimality). -/
theorem erdos440_sharp (x : ℕ) :
    Nat.sqrt x - 1
      ≤ ((Finset.range x).filter fun i => Nat.lcm (i + 1) (i + 2) ≤ x).card := by
  have hsub : Finset.range (Nat.sqrt x - 1)
      ⊆ (Finset.range x).filter fun i => Nat.lcm (i + 1) (i + 2) ≤ x := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hs : i + 2 ≤ Nat.sqrt x := by omega
    have hsq : Nat.sqrt x * Nat.sqrt x ≤ x := Nat.sqrt_le x
    have hprod : (i + 1) * (i + 2) ≤ x :=
      calc (i + 1) * (i + 2) ≤ Nat.sqrt x * Nat.sqrt x :=
            Nat.mul_le_mul (by omega) hs
        _ ≤ x := hsq
    have hlcm : Nat.lcm (i + 1) (i + 2) ≤ (i + 1) * (i + 2) :=
      Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega))
        (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
    have hix : i < x := by
      have := Nat.sqrt_le_self x
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hix, le_trans hlcm hprod⟩
  calc Nat.sqrt x - 1 = (Finset.range (Nat.sqrt x - 1)).card :=
        (Finset.card_range _).symm
    _ ≤ _ := Finset.card_le_card hsub

end Erdos440
