/-
  Erdős Problem #542, first question — the Schinzel–Szekeres 31/30 bound.

  Problem (https://www.erdosproblems.com/542): let A ⊆ {1,…,n} be such that
  lcm(a,b) > n for all distinct a, b ∈ A.  Is Σ_{a∈A} 1/a ≤ 31/30?

  Status: solved (positively) by A. Schinzel and G. Szekeres [ScSz59].  The
  bound is sharp: A = {2,3,5} at n = 5 attains 31/30 (`erdos542_sharp`).

  THIS FILE formalizes the Schinzel–Szekeres theorem, UNCONDITIONALLY:

  * `erdos542` (MAIN): for EVERY n and every A ⊆ Finset.Icc 1 n with
    n < lcm(a,b) for all distinct a,b ∈ A,
        ∑ a ∈ A, (1 : ℚ)/a ≤ 31/30.
  * `erdos542_sharp`: {2,3,5} at n = 5 is a valid configuration with
    ∑ 1/a = 31/30 exactly — so 31/30 is the answer to the problem.
  * `erdos542_core`: the weight-system half — every n outside the seven
    exceptional values {13,19,20,31,32,61,62} (those where the majorant
    S n exceeds 31/30), via Lemma 1.
  * `sum_inv_le_S` (SS59 Lemma 1, reorganized): any valid A satisfies
    Σ 1/a ≤ S n, where S q := Σ_j c_j Σ_{⌊q/(j+1)⌋ < p ≤ ⌊q/j⌋} 1/p and the
    c_j are the 13 exact rational Schinzel–Szekeres weights (all other
    weights vanish), PROVIDED S q ≥ 1 for all 1 ≤ q ≤ n.
  * `one_le_S`: S q ≥ 1 for ALL q ≥ 1, and `S_le_of_not_exceptional`:
    S n ≤ 31/30 for n ∉ {13,19,20,31,32,61,62} — by exact rational
    computation (native_decide) for q ≤ 1200 and by directed log estimates
    for q ≥ 1201.
  * §6: the seven exceptional n, by explicit LP-dual packing certificates
    (`wE13`…`wE62`), each verified inside the KERNEL (`decide +kernel`, no
    native_decide): at these n the certified bound is in fact Σ 1/a ≤ ~1.

  Method notes (deviations from [ScSz59], mathematically equivalent):
  1. Lemma 1 is proved via a packing-certificate lemma (`packing_bound`):
     if w ≥ 0 and each a ∈ A has Σ_{m ≤ n, a ∣ m} w m ≥ 1/a, then
     Σ 1/a ≤ Σ_{m ≤ n} w m, because the multiple-sets {m ≤ n : a ∣ m} are
     pairwise disjoint (a common multiple m of a ≠ b has lcm(a,b) ≤ m ≤ n).
     Applying it to w m = Σ_j c_j·[m ∈ (⌊n/(j+1)⌋, ⌊n/j⌋]]·(1/m) and using
     the floor identity ⌊⌊n/a⌋/k⌋ = ⌊n/(ak)⌋ to reindex multiples of a in
     each block gives Σ_{m∈Mₐ} w m = (1/a)·S(⌊n/a⌋) ≥ 1/a.  This replaces
     the paper's Abel-summation bookkeeping.
  2. The finite verification is extended from the paper's q ≤ 365 up to
     q ≤ 1200 (native_decide, exact ℚ), which relaxes the tail estimate
     margin from the paper's ~7·10⁻⁵ to ~8·10⁻³: for q ≥ 1201 we use
       log((j+1)/j) − (j+1)/q ≤ Σ_{⌊q/(j+1)⌋<p≤⌊q/j⌋} 1/p
                              ≤ log((j+1)/j) + j/(q−j),
     (telescoped 1/(k+1) ≤ log(k+1) − log k ≤ 1/k), and 13 directed
     rational bounds on log((j+1)/j) from the artanh series
     (Real.sum_range_le_log_div / Real.log_div_le_sum_range_add, depth 5,
     x = 1/(2j+1)), giving 1 < c_lo − W₂/1201 ≤ S q ≤ c_up + W₁/1143 < 31/30
     with W₁ = Σ c_j·j ≈ 8.753, W₂ = Σ c_j·(j+1) ≈ 10.971.
  3. The seven exceptional n are settled by LP duality instead of the
     paper's hand case analysis: the fractional packing LP
     (max Σ x_a/a  s.t.  Σ_{a∣m} x_a ≤ 1 ∀ m ≤ n, x ≥ 0) has value
     EXACTLY 1 at each exceptional n (exact rational PPL solve, 2026-07-12),
     and any feasible dual vector is a `packing_bound` certificate.  The
     embedded tables are the PPL vertex solutions with unwieldy entries
     rounded UP onto a 10⁻⁶ grid (feasibility is preserved under rounding
     up; totals stay ≤ 1.0000054 < 31/30), re-verified twice: exactly in
     Sage, and in the Lean kernel by `decide +kernel`.

  native_decide AUDIT (`finite_check` below is the ONLY use in this file;
  the §6 certificate checks use kernel `decide`, not native): the decided
  proposition quantifies over q ∈ Finset.Icc 1 1200 with an exact-ℚ body
  built from computable structural defs (no Classical choice, no opaque
  Props); it was cross-checked against two independent exact-rational Sage
  computations (the planner's reconstruction in
  .tasks/f5exp/docs/erdos542-weights.md, and in-file #eval spot checks:
  S 5 = 31/30, S 1 = 1, and the exceptional set on [1,100]).

  Axiom audit (#print axioms, 2026-07-12): `erdos542` and everything
  through `finite_check` depend on {propext, Classical.choice, Quot.sound}
  plus finite_check's `Lean.ofReduceBool` (native_decide); the analytic
  layers (`packing_bound`, `sum_inv_le_S`, `S_le_tail`, `one_le_S_tail`,
  `erdos542_sharp`, `exceptional_bound`) use only the standard three.

  Weights provenance: .tasks/f5exp/docs/erdos542-weights.md — exact greedy
  reconstruction matching the paper's printed constant c = 1.017262… .

  References:
  [ScSz59] A. Schinzel, G. Szekeres, "Sur un problème de M. Paul Erdős",
           Acta Sci. Math. (Szeged) 20 (1959), 221–229.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Erdos542

-- ════════════════════════════════════════════════════════════════════
-- §1 THE SCHINZEL–SZEKERES WEIGHTS AND BLOCK SUMS
-- ════════════════════════════════════════════════════════════════════

/-- Support of the weight system: the 13 indices with nonzero weight. -/
def J : Finset ℕ := {1, 2, 3, 4, 6, 10, 15, 16, 22, 28, 35, 36, 58}

/-- The Schinzel–Szekeres weights (exact rationals, [ScSz59] §2;
values re-derived by the greedy rule, see the weights doc). -/
def c : ℕ → ℚ
  | 1 => 1
  | 2 => 1/2
  | 3 => 1/6
  | 4 => 1/6
  | 6 => 2/15
  | 10 => 31/420
  | 15 => 2021/45045
  | 16 => 2021/45045
  | 22 => 3565609/116396280
  | 28 => 148279331/6692786100
  | 35 => 17694671471/1504203675975
  | 36 => 104205434239/6016814703900
  | 58 => 77337724377074022791/13687446560419818786600
  | _ => 0

theorem c_nonneg (j : ℕ) : 0 ≤ c j := by
  unfold c
  split <;> norm_num

/-- The `j`-th harmonic block at level `q`:  Σ_{⌊q/(j+1)⌋ < p ≤ ⌊q/j⌋} 1/p. -/
def block (q j : ℕ) : ℚ := ∑ p ∈ Finset.Ioc (q / (j + 1)) (q / j), (1 : ℚ) / p

/-- The Schinzel–Szekeres majorant `S q = Σ_j c_j · block q j`. -/
def S (q : ℕ) : ℚ := ∑ j ∈ J, c j * block q j

/-- The seven exceptional levels where `S n > 31/30`. -/
def Exceptional : Finset ℕ := {13, 19, 20, 31, 32, 61, 62}

/-- Sum over the explicit support (helper to unfold `∑ j ∈ J`). -/
theorem sum_J {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ j ∈ J, f j
      = f 1 + (f 2 + (f 3 + (f 4 + (f 6 + (f 10 + (f 15 + (f 16 + (f 22 +
          (f 28 + (f 35 + (f 36 + f 58))))))))))) := by
  show ∑ j ∈ ({1, 2, 3, 4, 6, 10, 15, 16, 22, 28, 35, 36, 58} : Finset ℕ), f j = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- **Finite verification** (exact rational arithmetic, audited
native_decide — see file header): on 1 ≤ q ≤ 1200, `S q ≥ 1` always, and
`S q ≤ 31/30` outside the exceptional set. -/
theorem finite_check :
    ∀ q ∈ Finset.Icc 1 1200, 1 ≤ S q ∧ (q ∉ Exceptional → S q ≤ 31 / 30) := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- §2 THE PACKING-CERTIFICATE LEMMA
-- ════════════════════════════════════════════════════════════════════

/-- The multiples of `a` in `[1, n]`. -/
def multiples (n a : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (a ∣ ·)

/-- The lcm condition makes the multiple-sets pairwise disjoint: a common
multiple `m ≤ n` of `a ≠ b` would give `lcm a b ≤ m ≤ n`. -/
theorem multiples_pairwiseDisjoint {n : ℕ} {A : Finset ℕ}
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    (↑A : Set ℕ).PairwiseDisjoint (multiples n) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro m hma hmb
  simp only [multiples, Finset.mem_filter, Finset.mem_Icc] at hma hmb
  obtain ⟨⟨hm1, hmn⟩, hdvda⟩ := hma
  obtain ⟨-, hdvdb⟩ := hmb
  have hle : Nat.lcm a b ≤ m :=
    Nat.le_of_dvd (by omega) (Nat.lcm_dvd hdvda hdvdb)
  have := hlcm a ha b hb hab
  omega

/-- **Packing certificate bound**: if `w ≥ 0` and every `a ∈ A` is covered
(`1/a ≤ Σ_{m ∈ multiples n a} w m`), then `Σ_{a∈A} 1/a ≤ Σ_{m=1}^n w m`.
This is the LP-dual form of the disjointness of the multiple-sets. -/
theorem packing_bound {n : ℕ} {w : ℕ → ℚ} (hw : ∀ m, 0 ≤ w m)
    {A : Finset ℕ} (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b)
    (hcov : ∀ a ∈ A, (1 : ℚ) / a ≤ ∑ m ∈ multiples n a, w m) :
    ∑ a ∈ A, (1 : ℚ) / a ≤ ∑ m ∈ Finset.Icc 1 n, w m := by
  calc ∑ a ∈ A, (1 : ℚ) / a
      ≤ ∑ a ∈ A, ∑ m ∈ multiples n a, w m := Finset.sum_le_sum hcov
    _ = ∑ m ∈ A.biUnion (multiples n), w m :=
        (Finset.sum_biUnion (multiples_pairwiseDisjoint hlcm)).symm
    _ ≤ ∑ m ∈ Finset.Icc 1 n, w m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨a, -, hma⟩ := Finset.mem_biUnion.mp hm
          simp only [multiples, Finset.mem_filter] at hma
          exact hma.1
        · exact fun m _ _ => hw m

-- ════════════════════════════════════════════════════════════════════
-- §3 LEMMA 1: THE S-WEIGHTS COVER EVERY a
-- ════════════════════════════════════════════════════════════════════

/-- The certificate weight function realizing `S`:
`wS n m = Σ_j c_j · [m ∈ (⌊n/(j+1)⌋, ⌊n/j⌋]] · (1/m)`. -/
def wS (n m : ℕ) : ℚ :=
  ∑ j ∈ J, c j * (if m ∈ Finset.Ioc (n / (j + 1)) (n / j) then (1 : ℚ) / m else 0)

theorem wS_nonneg (n m : ℕ) : 0 ≤ wS n m :=
  Finset.sum_nonneg fun j _ => mul_nonneg (c_nonneg j) (by split <;> positivity)

/-- Each block is inside `[1, n]`. -/
theorem Ioc_subset_Icc {n j : ℕ} :
    Finset.Ioc (n / (j + 1)) (n / j) ⊆ Finset.Icc 1 n := by
  intro m hm
  rw [Finset.mem_Ioc] at hm
  rw [Finset.mem_Icc]
  exact ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hm.1,
    le_trans hm.2 (Nat.div_le_self n j)⟩

/-- The total certificate weight is exactly `S n`. -/
theorem sum_wS (n : ℕ) : ∑ m ∈ Finset.Icc 1 n, wS n m = S n := by
  unfold wS S block
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Ioc_subset_Icc]

/-- **Reindexing multiples into blocks**: the multiples of `a` inside the
`j`-th block of `[1, n]` are exactly `a * p` for `p` in the `j`-th block of
`[1, ⌊n/a⌋]`.  Uses `⌊⌊n/a⌋/k⌋ = ⌊n/(ak)⌋`. -/
theorem multiples_inter_Ioc {n a j : ℕ} (ha : 1 ≤ a) (hj : 1 ≤ j) :
    multiples n a ∩ Finset.Ioc (n / (j + 1)) (n / j)
      = (Finset.Ioc (n / a / (j + 1)) (n / a / j)).image (a * ·) := by
  ext m
  simp only [multiples, Finset.mem_inter, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨hm1, hmn⟩, p, rfl⟩, hlo, hhi⟩
    refine ⟨p, ⟨?_, ?_⟩, rfl⟩
    · rw [Nat.div_div_eq_div_mul,
        Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega) (by omega))]
      have h := (Nat.div_lt_iff_lt_mul (show 0 < j + 1 by omega)).mp hlo
      calc n < a * p * (j + 1) := h
        _ = p * (a * (j + 1)) := by ring
    · rw [Nat.div_div_eq_div_mul,
        Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))]
      have h := (Nat.le_div_iff_mul_le (show 0 < j by omega)).mp hhi
      calc p * (a * j) = a * p * j := by ring
        _ ≤ n := h
  · rintro ⟨p, ⟨hlo, hhi⟩, rfl⟩
    rw [Nat.div_div_eq_div_mul] at hlo hhi
    have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact Nat.not_lt_zero _ hlo)
    have key1 : a * p * j ≤ n := by
      have h := (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mp hhi
      calc a * p * j = p * (a * j) := by ring
        _ ≤ n := h
    refine ⟨⟨⟨?_, ?_⟩, ⟨p, rfl⟩⟩, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · calc a * p = a * p * 1 := by ring
        _ ≤ a * p * j := Nat.mul_le_mul_left _ (by omega)
        _ ≤ n := key1
    · rw [Nat.div_lt_iff_lt_mul (show 0 < j + 1 by omega)]
      have h := (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega) (show 0 < j + 1 by omega))).mp hlo
      calc n < p * (a * (j + 1)) := h
        _ = a * p * (j + 1) := by ring
    · rw [Nat.le_div_iff_mul_le (show 0 < j by omega)]
      exact key1

/-- Every `j ∈ J` is positive. -/
theorem J_pos : ∀ j ∈ J, 1 ≤ j := by decide

/-- **Coverage**: the certificate weight collected by the multiples of `a`
is exactly `(1/a) · S(⌊n/a⌋)`, so `≥ 1/a` whenever `S(⌊n/a⌋) ≥ 1`. -/
theorem cov_wS {n a : ℕ} (ha1 : 1 ≤ a) (hS1 : 1 ≤ S (n / a)) :
    (1 : ℚ) / a ≤ ∑ m ∈ multiples n a, wS n m := by
  have key : ∑ m ∈ multiples n a, wS n m = (1 / a : ℚ) * S (n / a) := by
    unfold wS S block
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, multiples_inter_Ioc ha1 (J_pos j hj),
      Finset.sum_image (fun p _ p' _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hp).1
    have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  rw [key]
  calc (1 : ℚ) / a = (1 / a) * 1 := (mul_one _).symm
    _ ≤ (1 / a) * S (n / a) := by
        apply mul_le_mul_of_nonneg_left hS1 (by positivity)

/-- **[ScSz59] Lemma 1** (packing form): if `S q ≥ 1` for all `1 ≤ q ≤ n`,
then any valid `A` has `Σ 1/a ≤ S n`. -/
theorem sum_inv_le_S {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b)
    (hS : ∀ q, 1 ≤ q → q ≤ n → 1 ≤ S q) :
    ∑ a ∈ A, (1 : ℚ) / a ≤ S n := by
  rw [← sum_wS n]
  refine packing_bound (wS_nonneg n) hlcm fun a haA => ?_
  obtain ⟨ha1, han⟩ := Finset.mem_Icc.mp (hA haA)
  exact cov_wS ha1
    (hS (n / a) ((Nat.one_le_div_iff (by omega)).mpr han) (Nat.div_le_self n a))

-- ════════════════════════════════════════════════════════════════════
-- §4 THE TAIL (q ≥ 1201): DIRECTED LOG ESTIMATES
-- ════════════════════════════════════════════════════════════════════

/-- Telescoped upper bound: for `1 ≤ u ≤ v`,
`Σ_{u < p ≤ v} 1/p ≤ log v − log u` (each `1/p ≤ log p − log (p−1)`). -/
theorem sum_Ioc_inv_le {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) :
    ∑ p ∈ Finset.Ioc u v, 1 / (p : ℝ) ≤ Real.log v - Real.log u := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v hv ih =>
    rw [Finset.sum_Ioc_succ_top hv]
    have hv0 : (0 : ℝ) < v := by
      have : 1 ≤ v := le_trans hu hv
      exact_mod_cast this
    have hstep : 1 / ((v : ℝ) + 1) ≤ Real.log ((v : ℝ) + 1) - Real.log v := by
      have h1 : Real.log ((v : ℝ) / ((v : ℝ) + 1)) ≤ (v : ℝ) / ((v : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hv0) (by positivity)] at h1
      have h2 : (v : ℝ) / ((v : ℝ) + 1) - 1 = -(1 / ((v : ℝ) + 1)) := by
        field_simp
        ring
      rw [h2] at h1
      linarith
    push_cast
    push_cast at ih
    linarith

/-- Telescoped lower bound: for `u ≤ v`,
`log (v+1) − log (u+1) ≤ Σ_{u < p ≤ v} 1/p` (each `1/p ≥ log (p+1) − log p`). -/
theorem le_sum_Ioc_inv {u v : ℕ} (huv : u ≤ v) :
    Real.log ((v : ℝ) + 1) - Real.log ((u : ℝ) + 1) ≤ ∑ p ∈ Finset.Ioc u v, 1 / (p : ℝ) := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v hv ih =>
    rw [Finset.sum_Ioc_succ_top hv]
    have hstep : Real.log ((v : ℝ) + 2) - Real.log ((v : ℝ) + 1) ≤ 1 / ((v : ℝ) + 1) := by
      have h1 : Real.log (((v : ℝ) + 2) / ((v : ℝ) + 1)) ≤ ((v : ℝ) + 2) / ((v : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h1
      have h2 : ((v : ℝ) + 2) / ((v : ℝ) + 1) - 1 = 1 / ((v : ℝ) + 1) := by
        field_simp
        ring
      rw [h2] at h1
      linarith
    push_cast
    push_cast at ih
    have hnorm : (v : ℝ) + 1 + 1 = (v : ℝ) + 2 := by ring
    rw [hnorm]
    linarith

/-- Block upper estimate for the tail:
`block q j ≤ log((j+1)/j) + j/(q−j)` for `1 ≤ j`, `j + 1 ≤ q`. -/
theorem block_le_log {q j : ℕ} (hj : 1 ≤ j) (hq : j + 1 ≤ q) :
    ((block q j : ℚ) : ℝ) ≤ Real.log (((j : ℝ) + 1) / j) + (j : ℝ) / ((q : ℝ) - j) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjq : (j : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hq
  have hqj_pos : (0 : ℝ) < (q : ℝ) - j := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have huv : q / (j + 1) ≤ q / j :=
    (Nat.le_div_iff_mul_le (by omega)).mpr
      (le_trans (Nat.mul_le_mul_left _ (by omega)) (Nat.div_mul_le_self q (j + 1)))
  have hu1 : 1 ≤ q / (j + 1) := (Nat.one_le_div_iff (by omega)).mpr hq
  have hcast : ((block q j : ℚ) : ℝ)
      = ∑ p ∈ Finset.Ioc (q / (j + 1)) (q / j), 1 / (p : ℝ) := by
    unfold block
    push_cast
    rfl
  rw [hcast]
  have h1 : ∑ p ∈ Finset.Ioc (q / (j + 1)) (q / j), 1 / (p : ℝ)
      ≤ Real.log (q / j : ℕ) - Real.log (q / (j + 1) : ℕ) := sum_Ioc_inv_le hu1 huv
  have hv0 : (0 : ℝ) < ((q / j : ℕ) : ℝ) := by
    have : 1 ≤ q / j := le_trans hu1 huv
    exact_mod_cast this
  have hu0 : (0 : ℝ) < ((q / (j + 1) : ℕ) : ℝ) := by exact_mod_cast hu1
  -- v ≤ q/j (real)
  have hlogv : Real.log ((q / j : ℕ) : ℝ) ≤ Real.log ((q : ℝ) / j) :=
    Real.log_le_log hv0 Nat.cast_div_le
  -- (q − j)/(j + 1) ≤ u (real)
  have hu_ge : ((q : ℝ) - j) / ((j : ℝ) + 1) ≤ ((q / (j + 1) : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : q + 1 ≤ (q / (j + 1) + 1) * (j + 1) :=
      Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self _))
    have h2R : (q : ℝ) + 1 ≤ (((q / (j + 1) : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) := by
      exact_mod_cast h2
    nlinarith [h2R]
  have hu_pos : (0 : ℝ) < ((q : ℝ) - j) / ((j : ℝ) + 1) := by positivity
  have hlogu : Real.log (((q : ℝ) - j) / ((j : ℝ) + 1))
      ≤ Real.log ((q / (j + 1) : ℕ) : ℝ) := Real.log_le_log hu_pos hu_ge
  have hexpand : Real.log ((q : ℝ) / j) - Real.log (((q : ℝ) - j) / ((j : ℝ) + 1))
      = Real.log (((j : ℝ) + 1) / j) + Real.log ((q : ℝ) / ((q : ℝ) - j)) := by
    rw [Real.log_div (ne_of_gt hq0) (ne_of_gt hj0),
      Real.log_div (ne_of_gt (by linarith : (0:ℝ) < (q : ℝ) - j)) (ne_of_gt (by positivity)),
      Real.log_div (ne_of_gt (by positivity)) (ne_of_gt hj0),
      Real.log_div (ne_of_gt hq0) (ne_of_gt hqj_pos)]
    ring
  have hlast : Real.log ((q : ℝ) / ((q : ℝ) - j)) ≤ (j : ℝ) / ((q : ℝ) - j) := by
    have h3 : Real.log ((q : ℝ) / ((q : ℝ) - j)) ≤ (q : ℝ) / ((q : ℝ) - j) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hq0 hqj_pos)
    have h4 : (q : ℝ) / ((q : ℝ) - j) - 1 = (j : ℝ) / ((q : ℝ) - j) := by
      field_simp
      ring
    linarith
  linarith

/-- Block lower estimate for the tail:
`log((j+1)/j) − (j+1)/q ≤ block q j` for `1 ≤ j`, `j + 1 ≤ q`. -/
theorem log_sub_le_block {q j : ℕ} (hj : 1 ≤ j) (hq : j + 1 ≤ q) :
    Real.log (((j : ℝ) + 1) / j) - ((j : ℝ) + 1) / q ≤ ((block q j : ℚ) : ℝ) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjq : (j : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hq
  have hq0 : (0 : ℝ) < q := by linarith
  have huv : q / (j + 1) ≤ q / j :=
    (Nat.le_div_iff_mul_le (by omega)).mpr
      (le_trans (Nat.mul_le_mul_left _ (by omega)) (Nat.div_mul_le_self q (j + 1)))
  have hcast : ((block q j : ℚ) : ℝ)
      = ∑ p ∈ Finset.Ioc (q / (j + 1)) (q / j), 1 / (p : ℝ) := by
    unfold block
    push_cast
    rfl
  rw [hcast]
  have h1 : Real.log (((q / j : ℕ) : ℝ) + 1) - Real.log (((q / (j + 1) : ℕ) : ℝ) + 1)
      ≤ ∑ p ∈ Finset.Ioc (q / (j + 1)) (q / j), 1 / (p : ℝ) := le_sum_Ioc_inv huv
  -- q/j ≤ v + 1 (real)
  have hv_ge : (q : ℝ) / j ≤ ((q / j : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hj0]
    have h2 : q + 1 ≤ (q / j + 1) * j :=
      Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self _))
    have h2R : (q : ℝ) + 1 ≤ (((q / j : ℕ) : ℝ) + 1) * (j : ℝ) := by exact_mod_cast h2
    linarith
  have hlogv : Real.log ((q : ℝ) / j) ≤ Real.log (((q / j : ℕ) : ℝ) + 1) :=
    Real.log_le_log (by positivity) hv_ge
  -- u + 1 ≤ (q + j + 1)/(j + 1) (real)
  have hu_le : ((q / (j + 1) : ℕ) : ℝ) + 1 ≤ ((q : ℝ) + (j : ℝ) + 1) / ((j : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have h3 : (q / (j + 1)) * (j + 1) ≤ q := Nat.div_mul_le_self q (j + 1)
    have h3R : ((q / (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast h3
    ring_nf
    ring_nf at h3R
    linarith
  have hlogu : Real.log (((q / (j + 1) : ℕ) : ℝ) + 1)
      ≤ Real.log (((q : ℝ) + (j : ℝ) + 1) / ((j : ℝ) + 1)) :=
    Real.log_le_log (by positivity) hu_le
  have hexpand : Real.log ((q : ℝ) / j)
        - Real.log (((q : ℝ) + (j : ℝ) + 1) / ((j : ℝ) + 1))
      = Real.log (((j : ℝ) + 1) / j)
        - Real.log (((q : ℝ) + (j : ℝ) + 1) / q) := by
    rw [Real.log_div (ne_of_gt hq0) (ne_of_gt hj0),
      Real.log_div (ne_of_gt (by positivity : (0:ℝ) < (q : ℝ) + (j : ℝ) + 1))
        (ne_of_gt (by positivity)),
      Real.log_div (ne_of_gt (by positivity)) (ne_of_gt hj0),
      Real.log_div (ne_of_gt (by positivity : (0:ℝ) < (q : ℝ) + (j : ℝ) + 1))
        (ne_of_gt hq0)]
    ring
  have hlast : Real.log (((q : ℝ) + (j : ℝ) + 1) / q) ≤ ((j : ℝ) + 1) / q := by
    have h3 : Real.log (((q : ℝ) + (j : ℝ) + 1) / q)
        ≤ ((q : ℝ) + (j : ℝ) + 1) / q - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h4 : ((q : ℝ) + (j : ℝ) + 1) / q - 1 = ((j : ℝ) + 1) / q := by
      field_simp
      ring
    linarith
  linarith

/-- Artanh-series lower bound for `log((j+1)/j)`, depth 5, `x = 1/(2j+1)`. -/
theorem log_ratio_lb (j : ℕ) (hj : 1 ≤ j) :
    2 * ∑ i ∈ Finset.range 5, (2 * (j : ℝ) + 1)⁻¹ ^ (2 * i + 1) / (2 * i + 1)
      ≤ Real.log (((j : ℝ) + 1) / j) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hx0 : (0 : ℝ) ≤ (2 * (j : ℝ) + 1)⁻¹ := by positivity
  have hx1 : (2 * (j : ℝ) + 1)⁻¹ < 1 := by
    rw [inv_eq_one_div, div_lt_one (by linarith)]
    linarith
  have key := Real.sum_range_le_log_div hx0 hx1 5
  have harg : (1 + (2 * (j : ℝ) + 1)⁻¹) / (1 - (2 * (j : ℝ) + 1)⁻¹)
      = ((j : ℝ) + 1) / j := by
    rw [inv_eq_one_div]
    field_simp
    ring
  rw [harg] at key
  linarith

/-- Artanh-series upper bound for `log((j+1)/j)`, depth 5, `x = 1/(2j+1)`. -/
theorem log_ratio_ub (j : ℕ) (hj : 1 ≤ j) :
    Real.log (((j : ℝ) + 1) / j)
      ≤ 2 * ((∑ i ∈ Finset.range 5, (2 * (j : ℝ) + 1)⁻¹ ^ (2 * i + 1) / (2 * i + 1))
          + (2 * (j : ℝ) + 1)⁻¹ ^ (2 * 5 + 1) / (1 - ((2 * (j : ℝ) + 1)⁻¹) ^ 2)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hx0 : (0 : ℝ) ≤ (2 * (j : ℝ) + 1)⁻¹ := by positivity
  have hx1 : (2 * (j : ℝ) + 1)⁻¹ < 1 := by
    rw [inv_eq_one_div, div_lt_one (by linarith)]
    linarith
  have key := Real.log_div_le_sum_range_add hx0 hx1 5
  have harg : (1 + (2 * (j : ℝ) + 1)⁻¹) / (1 - (2 * (j : ℝ) + 1)⁻¹)
      = ((j : ℝ) + 1) / j := by
    rw [inv_eq_one_div]
    field_simp
    ring
  rw [harg] at key
  linarith

/-- Packaged per-term upper bound for the tail sum: for `j ∈ J`-style data
(`γ = c j` as a literal, `U ≥` the depth-5 series-plus-remainder value),
`c j · block q j ≤ γ·U + (γ·j)·(q − 58)⁻¹`. -/
theorem tail_term_ub {q : ℕ} (hq : 1201 ≤ q) (j : ℕ) (hj : 1 ≤ j) (hj58 : j ≤ 58)
    (γ U : ℝ) (hγ : ((c j : ℚ) : ℝ) = γ) (hγ0 : 0 ≤ γ)
    (hU : 2 * ((∑ i ∈ Finset.range 5, (2 * (j : ℝ) + 1)⁻¹ ^ (2 * i + 1) / (2 * i + 1))
          + (2 * (j : ℝ) + 1)⁻¹ ^ (2 * 5 + 1) / (1 - ((2 * (j : ℝ) + 1)⁻¹) ^ 2)) ≤ U) :
    ((c j : ℚ) : ℝ) * ((block q j : ℚ) : ℝ) ≤ γ * U + (γ * j) * ((q : ℝ) - 58)⁻¹ := by
  have hqR : (1201 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hjR : (j : ℝ) ≤ 58 := by exact_mod_cast hj58
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have h1 : ((block q j : ℚ) : ℝ) ≤ Real.log (((j : ℝ) + 1) / j) + (j : ℝ) / ((q : ℝ) - j) :=
    block_le_log hj (by omega)
  have h2 : Real.log (((j : ℝ) + 1) / j) ≤ U := le_trans (log_ratio_ub j hj) hU
  have h3 : (j : ℝ) / ((q : ℝ) - j) ≤ (j : ℝ) / ((q : ℝ) - 58) := by
    gcongr
    linarith
  have h4 : ((block q j : ℚ) : ℝ) ≤ U + (j : ℝ) / ((q : ℝ) - 58) := by linarith
  calc ((c j : ℚ) : ℝ) * ((block q j : ℚ) : ℝ)
      = γ * ((block q j : ℚ) : ℝ) := by rw [hγ]
    _ ≤ γ * (U + (j : ℝ) / ((q : ℝ) - 58)) := mul_le_mul_of_nonneg_left h4 hγ0
    _ = γ * U + (γ * j) * ((q : ℝ) - 58)⁻¹ := by ring

/-- Packaged per-term lower bound for the tail sum. -/
theorem tail_term_lb {q : ℕ} (hq : 1201 ≤ q) (j : ℕ) (hj : 1 ≤ j) (hj58 : j ≤ 58)
    (γ L : ℝ) (hγ : ((c j : ℚ) : ℝ) = γ) (hγ0 : 0 ≤ γ)
    (hL : L ≤ 2 * ∑ i ∈ Finset.range 5, (2 * (j : ℝ) + 1)⁻¹ ^ (2 * i + 1) / (2 * i + 1)) :
    γ * L - (γ * ((j : ℝ) + 1)) * ((q : ℝ))⁻¹ ≤ ((c j : ℚ) : ℝ) * ((block q j : ℚ) : ℝ) := by
  have hqR : (1201 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : Real.log (((j : ℝ) + 1) / j) - ((j : ℝ) + 1) / q ≤ ((block q j : ℚ) : ℝ) :=
    log_sub_le_block hj (by omega)
  have h2 : L ≤ Real.log (((j : ℝ) + 1) / j) := le_trans hL (log_ratio_lb j hj)
  have h4 : L - ((j : ℝ) + 1) / q ≤ ((block q j : ℚ) : ℝ) := by linarith
  calc γ * L - (γ * ((j : ℝ) + 1)) * ((q : ℝ))⁻¹
      = γ * (L - ((j : ℝ) + 1) / q) := by ring
    _ ≤ γ * ((block q j : ℚ) : ℝ) := mul_le_mul_of_nonneg_left h4 hγ0
    _ = ((c j : ℚ) : ℝ) * ((block q j : ℚ) : ℝ) := by rw [hγ]

/-- Cast expansion of `S q` over the explicit support. -/
theorem S_cast_expand (q : ℕ) : ((S q : ℚ) : ℝ)
    = ((c 1 : ℚ) : ℝ) * ((block q 1 : ℚ) : ℝ)
      + ((c 2 : ℚ) : ℝ) * ((block q 2 : ℚ) : ℝ)
      + ((c 3 : ℚ) : ℝ) * ((block q 3 : ℚ) : ℝ)
      + ((c 4 : ℚ) : ℝ) * ((block q 4 : ℚ) : ℝ)
      + ((c 6 : ℚ) : ℝ) * ((block q 6 : ℚ) : ℝ)
      + ((c 10 : ℚ) : ℝ) * ((block q 10 : ℚ) : ℝ)
      + ((c 15 : ℚ) : ℝ) * ((block q 15 : ℚ) : ℝ)
      + ((c 16 : ℚ) : ℝ) * ((block q 16 : ℚ) : ℝ)
      + ((c 22 : ℚ) : ℝ) * ((block q 22 : ℚ) : ℝ)
      + ((c 28 : ℚ) : ℝ) * ((block q 28 : ℚ) : ℝ)
      + ((c 35 : ℚ) : ℝ) * ((block q 35 : ℚ) : ℝ)
      + ((c 36 : ℚ) : ℝ) * ((block q 36 : ℚ) : ℝ)
      + ((c 58 : ℚ) : ℝ) * ((block q 58 : ℚ) : ℝ) := by
  unfold S
  push_cast
  rw [sum_J]
  ring

/-- **Tail upper bound**: `S q ≤ 31/30` for `q ≥ 1201`. -/
theorem S_le_tail {q : ℕ} (hq : 1201 ≤ q) : S q ≤ 31 / 30 := by
  have hqR : (1201 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  suffices h : ((S q : ℚ) : ℝ) ≤ ((31 / 30 : ℚ) : ℝ) by exact_mod_cast h
  have hcast : ((31 / 30 : ℚ) : ℝ) = 31 / 30 := by norm_num
  rw [hcast]
  have hinv : ((q : ℝ) - 58)⁻¹ ≤ 1 / 1143 := by
    rw [inv_eq_one_div]
    gcongr
    linarith
  have b1 := tail_term_ub hq 1 (by norm_num) (by norm_num)
    1 (1732897/2500000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b2 := tail_term_ub hq 2 (by norm_num) (by norm_num)
    (1/2) (1013663/2500000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b3 := tail_term_ub hq 3 (by norm_num) (by norm_num)
    (1/6) (2876821/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b4 := tail_term_ub hq 4 (by norm_num) (by norm_num)
    (1/6) (557859/2500000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b6 := tail_term_ub hq 6 (by norm_num) (by norm_num)
    (2/15) (1541507/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b10 := tail_term_ub hq 10 (by norm_num) (by norm_num)
    (31/420) (476551/5000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b15 := tail_term_ub hq 15 (by norm_num) (by norm_num)
    (2021/45045) (322693/5000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b16 := tail_term_ub hq 16 (by norm_num) (by norm_num)
    (2021/45045) (606247/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b22 := tail_term_ub hq 22 (by norm_num) (by norm_num)
    (3565609/116396280) (222259/5000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b28 := tail_term_ub hq 28 (by norm_num) (by norm_num)
    (148279331/6692786100) (175457/5000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b35 := tail_term_ub hq 35 (by norm_num) (by norm_num)
    (17694671471/1504203675975) (281709/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b36 := tail_term_ub hq 36 (by norm_num) (by norm_num)
    (104205434239/6016814703900) (27399/1000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b58 := tail_term_ub hq 58 (by norm_num) (by norm_num)
    (77337724377074022791/13687446560419818786600) (34189/2000000)
    (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [S_cast_expand]
  linarith [b1, b2, b3, b4, b6, b10, b15, b16, b22, b28, b35, b36, b58, hinv]

/-- **Tail lower bound**: `1 ≤ S q` for `q ≥ 1201`. -/
theorem one_le_S_tail {q : ℕ} (hq : 1201 ≤ q) : 1 ≤ S q := by
  have hqR : (1201 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  suffices h : ((1 : ℚ) : ℝ) ≤ ((S q : ℚ) : ℝ) by exact_mod_cast h
  have hcast : ((1 : ℚ) : ℝ) = 1 := by norm_num
  rw [hcast]
  have hinv : ((q : ℝ))⁻¹ ≤ 1 / 1201 := by
    rw [inv_eq_one_div]
    gcongr
  have b1 := tail_term_lb hq 1 (by norm_num) (by norm_num)
    1 (346573/500000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b2 := tail_term_lb hq 2 (by norm_num) (by norm_num)
    (1/2) (4054651/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b3 := tail_term_lb hq 3 (by norm_num) (by norm_num)
    (1/6) (143841/500000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b4 := tail_term_lb hq 4 (by norm_num) (by norm_num)
    (1/6) (446287/2000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b6 := tail_term_lb hq 6 (by norm_num) (by norm_num)
    (2/15) (770753/5000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b10 := tail_term_lb hq 10 (by norm_num) (by norm_num)
    (31/420) (953101/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b15 := tail_term_lb hq 15 (by norm_num) (by norm_num)
    (2021/45045) (129077/2000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b16 := tail_term_lb hq 16 (by norm_num) (by norm_num)
    (2021/45045) (303123/5000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b22 := tail_term_lb hq 22 (by norm_num) (by norm_num)
    (3565609/116396280) (444517/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b28 := tail_term_lb hq 28 (by norm_num) (by norm_num)
    (148279331/6692786100) (350913/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b35 := tail_term_lb hq 35 (by norm_num) (by norm_num)
    (17694671471/1504203675975) (70427/2500000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b36 := tail_term_lb hq 36 (by norm_num) (by norm_num)
    (104205434239/6016814703900) (273989/10000000) (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  have b58 := tail_term_lb hq 58 (by norm_num) (by norm_num)
    (77337724377074022791/13687446560419818786600) (2671/156250)
    (by norm_num [c]) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [S_cast_expand]
  linarith [b1, b2, b3, b4, b6, b10, b15, b16, b22, b28, b35, b36, b58, hinv]

-- ════════════════════════════════════════════════════════════════════
-- §5 ASSEMBLY
-- ════════════════════════════════════════════════════════════════════

/-- `S q ≥ 1` for every `q ≥ 1`. -/
theorem one_le_S {q : ℕ} (hq : 1 ≤ q) : 1 ≤ S q := by
  rcases Nat.lt_or_ge 1200 q with h | h
  · exact one_le_S_tail (by omega)
  · exact (finite_check q (Finset.mem_Icc.mpr ⟨hq, h⟩)).1

/-- `S n ≤ 31/30` for every `n ≥ 1` outside the exceptional set. -/
theorem S_le_of_not_exceptional {n : ℕ} (hn : n ∉ Exceptional) (hn1 : 1 ≤ n) :
    S n ≤ 31 / 30 := by
  rcases Nat.lt_or_ge 1200 n with h | h
  · exact S_le_tail (by omega)
  · exact (finite_check n (Finset.mem_Icc.mpr ⟨hn1, h⟩)).2 hn

/-- **Erdős Problem #542, first question** ([ScSz59], core form): if
`A ⊆ {1, …, n}` has `lcm(a,b) > n` for all distinct `a, b ∈ A`, and `n` is
not one of the seven exceptional values `{13,19,20,31,32,61,62}` (where the
majorant `S n` exceeds `31/30` and [ScSz59] verify directly), then
`Σ_{a∈A} 1/a ≤ 31/30`.  Sharp at `n = 5`, `A = {2,3,5}` (`erdos542_sharp`). -/
theorem erdos542_core (n : ℕ) (hn : n ∉ Exceptional) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ∑ a ∈ A, (1 : ℚ) / a ≤ 31 / 30 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have hA0 : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
    rw [hA0, Finset.sum_empty]
    norm_num
  · exact le_trans
      (sum_inv_le_S hA hlcm fun q h1 _ => one_le_S h1)
      (S_le_of_not_exceptional hn hn1)

-- ════════════════════════════════════════════════════════════════════
-- §6 THE SEVEN EXCEPTIONAL LEVELS: LP-DUAL CERTIFICATES
-- ════════════════════════════════════════════════════════════════════

/-
For each exceptional `n`, the fractional relaxation of the packing problem
(max Σ x_a/a subject to Σ_{a ∣ m} x_a ≤ 1 for every m ≤ n, x ≥ 0) has value
EXACTLY 1, so an explicit dual certificate `w : ℕ → ℚ≥0` exists with
`Σ_{a ∣ m ≤ n} w m ≥ 1/a` for every `a ∈ [1,n]` and `Σ w ≈ 1 ≤ 31/30`.
The tables below are the exact PPL vertex solutions, rounded UP onto a
10⁻⁶ grid where the exact entries were unwieldy (rounding up preserves
feasibility; the total stays ≤ 1.0000054 < 31/30).  Each `by decide` below
re-verifies the certificate in the kernel, so the tables carry no trust
burden.  Note the certified bound at the exceptional levels is Σ 1/a ≤ 1,
strictly better than 31/30 — consistent with [ScSz59]'s remark that the
extremal configurations live at n = 5 and n = 11 only.
-/

/-- Certificate application: a nonnegative weight table covering every
`a ∈ [1, n]` with total ≤ 31/30 bounds every valid `A`. -/
theorem exceptional_bound {n : ℕ} (w : ℕ → ℚ) (hw : ∀ m, 0 ≤ w m)
    (hcov : ∀ a ∈ Finset.Icc 1 n, (1 : ℚ) / a ≤ ∑ m ∈ multiples n a, w m)
    (hsum : ∑ m ∈ Finset.Icc 1 n, w m ≤ 31 / 30)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ∑ a ∈ A, (1 : ℚ) / a ≤ 31 / 30 :=
  le_trans (packing_bound hw hlcm fun a ha => hcov a (hA ha)) hsum

/-- Dual certificate for `n = 13` (total `≈ 1.0000024`). -/
def wE13 : ℕ → ℚ
  | 4 => 15489/500000
  | 5 => 391/5000
  | 6 => 641/5000
  | 7 => 1/7
  | 8 => 1/8
  | 9 => 1/9
  | 10 => 121801/1000000
  | 11 => 1/11
  | 12 => 94023/1000000
  | 13 => 1/13
  | _ => 0

/-- Dual certificate for `n = 19` (total `≈ 1.0000015`). -/
def wE19 : ℕ → ℚ
  | 5 => 13251/1000000
  | 6 => 3349/200000
  | 7 => 1/14
  | 8 => 1/16
  | 9 => 1/18
  | 10 => 3321/31250
  | 11 => 1/11
  | 12 => 1/8
  | 13 => 1/13
  | 14 => 1/14
  | 15 => 40239/500000
  | 16 => 1/16
  | 17 => 1/17
  | 18 => 1/18
  | 19 => 1/19
  | _ => 0

/-- Dual certificate for `n = 20` (total `≈ 1.0000019`). -/
def wE20 : ℕ → ℚ
  | 5 => 13251/1000000
  | 6 => 14603/250000
  | 7 => 1/14
  | 8 => 1/16
  | 9 => 1/18
  | 10 => 3517/62500
  | 11 => 1/11
  | 12 => 1/12
  | 13 => 1/13
  | 14 => 1/14
  | 15 => 40239/500000
  | 16 => 1/16
  | 17 => 1/17
  | 18 => 1/18
  | 19 => 1/19
  | 20 => 1/20
  | _ => 0

/-- Dual certificate for `n = 31` (total `≈ 1.0000031`). -/
def wE31 : ℕ → ℚ
  | 7 => 3991/1000000
  | 9 => 1/54
  | 10 => 10831/500000
  | 11 => 1/22
  | 12 => 15763/500000
  | 13 => 1/26
  | 14 => 27767/500000
  | 15 => 9449/200000
  | 16 => 1/16
  | 17 => 1/17
  | 18 => 1/18
  | 19 => 1/19
  | 20 => 57761/1000000
  | 21 => 1/21
  | 22 => 1/22
  | 23 => 1/23
  | 24 => 1/16
  | 25 => 1/25
  | 26 => 1/26
  | 27 => 1/27
  | 28 => 1/28
  | 29 => 1/29
  | 30 => 1/30
  | 31 => 1/31
  | _ => 0

/-- Dual certificate for `n = 32` (total `≈ 1.0000031`). -/
def wE32 : ℕ → ℚ
  | 7 => 3991/1000000
  | 9 => 1/54
  | 10 => 10831/500000
  | 11 => 1/22
  | 12 => 15763/500000
  | 13 => 1/26
  | 14 => 27767/500000
  | 15 => 9449/200000
  | 16 => 1/32
  | 17 => 1/17
  | 18 => 1/18
  | 19 => 1/19
  | 20 => 57761/1000000
  | 21 => 1/21
  | 22 => 1/22
  | 23 => 1/23
  | 24 => 1/16
  | 25 => 1/25
  | 26 => 1/26
  | 27 => 1/27
  | 28 => 1/28
  | 29 => 1/29
  | 30 => 1/30
  | 31 => 1/31
  | 32 => 1/32
  | _ => 0

/-- Dual certificate for `n = 61` (total `≈ 1.0000053`). -/
def wE61 : ℕ → ℚ
  | 9 => 2633/1000000
  | 13 => 3561/1000000
  | 14 => 111/31250
  | 15 => 441/40000
  | 17 => 1/102
  | 18 => 10721/500000
  | 19 => 1/114
  | 20 => 3097/250000
  | 21 => 1/42
  | 22 => 1/44
  | 23 => 1/46
  | 24 => 209/20000
  | 25 => 1/50
  | 26 => 28491/1000000
  | 27 => 1/54
  | 28 => 26211/1000000
  | 29 => 1/58
  | 30 => 129/7700
  | 31 => 1/31
  | 32 => 1/32
  | 33 => 1/33
  | 34 => 1/34
  | 35 => 1/35
  | 36 => 1/36
  | 37 => 1/37
  | 38 => 1/38
  | 39 => 1/39
  | 40 => 17097/500000
  | 41 => 1/41
  | 42 => 1/42
  | 43 => 1/43
  | 44 => 1/44
  | 45 => 1/45
  | 46 => 1/46
  | 47 => 1/47
  | 48 => 1/32
  | 49 => 1/49
  | 50 => 1/50
  | 51 => 1/51
  | 52 => 1/52
  | 53 => 1/53
  | 54 => 1/54
  | 55 => 1/55
  | 56 => 1/56
  | 57 => 1/57
  | 58 => 1/58
  | 59 => 1/59
  | 60 => 1/60
  | 61 => 1/61
  | _ => 0

/-- Dual certificate for `n = 62` (total `≈ 1.0000042`). -/
def wE62 : ℕ → ℚ
  | 9 => 2567/1000000
  | 13 => 1/78
  | 14 => 111/31250
  | 15 => 5529/500000
  | 17 => 1/102
  | 18 => 5377/250000
  | 19 => 1/114
  | 20 => 3097/250000
  | 21 => 1/42
  | 22 => 1/44
  | 23 => 1/46
  | 24 => 1/96
  | 25 => 1/50
  | 26 => 1/52
  | 27 => 1/54
  | 28 => 26211/1000000
  | 29 => 1/58
  | 30 => 16721/1000000
  | 31 => 1/62
  | 32 => 1/32
  | 33 => 1/33
  | 34 => 1/34
  | 35 => 1/35
  | 36 => 1/36
  | 37 => 1/37
  | 38 => 1/38
  | 39 => 1/39
  | 40 => 23/672
  | 41 => 1/41
  | 42 => 1/42
  | 43 => 1/43
  | 44 => 1/44
  | 45 => 1/45
  | 46 => 1/46
  | 47 => 1/47
  | 48 => 1/32
  | 49 => 1/49
  | 50 => 1/50
  | 51 => 1/51
  | 52 => 1/52
  | 53 => 1/53
  | 54 => 1/54
  | 55 => 1/55
  | 56 => 1/56
  | 57 => 1/57
  | 58 => 1/58
  | 59 => 1/59
  | 60 => 1/60
  | 61 => 1/61
  | 62 => 1/62
  | _ => 0

/-- **Erdős Problem #542, first question — unconditional form**: for EVERY
`n` and every `A ⊆ {1, …, n}` with `lcm(a,b) > n` for all distinct
`a, b ∈ A`, the reciprocal sum is at most `31/30`.  Combines
`erdos542_core` with the seven kernel-checked dual certificates. -/
theorem erdos542 (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ∑ a ∈ A, (1 : ℚ) / a ≤ 31 / 30 := by
  by_cases hn : n ∈ Exceptional
  · simp only [Exceptional, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact exceptional_bound wE13 (fun m => by unfold wE13; split <;> norm_num)
        (by decide +kernel) (by decide +kernel) hA hlcm
    · exact exceptional_bound wE19 (fun m => by unfold wE19; split <;> norm_num)
        (by decide +kernel) (by decide +kernel) hA hlcm
    · exact exceptional_bound wE20 (fun m => by unfold wE20; split <;> norm_num)
        (by decide +kernel) (by decide +kernel) hA hlcm
    · exact exceptional_bound wE31 (fun m => by unfold wE31; split <;> norm_num)
        (by decide +kernel) (by decide +kernel) hA hlcm
    · exact exceptional_bound wE32 (fun m => by unfold wE32; split <;> norm_num)
        (by decide +kernel) (by decide +kernel) hA hlcm
    · exact exceptional_bound wE61 (fun m => by unfold wE61; split <;> norm_num)
        (by decide +kernel) (by decide +kernel) hA hlcm
    · exact exceptional_bound wE62 (fun m => by unfold wE62; split <;> norm_num)
        (by decide +kernel) (by decide +kernel) hA hlcm
  · exact erdos542_core n hn A hA hlcm

/-- **Sharpness**: at `n = 5` the set `{2, 3, 5}` is valid and attains
`31/30` exactly. -/
theorem erdos542_sharp :
    ({2, 3, 5} : Finset ℕ) ⊆ Finset.Icc 1 5
    ∧ (∀ a ∈ ({2, 3, 5} : Finset ℕ), ∀ b ∈ ({2, 3, 5} : Finset ℕ),
        a ≠ b → 5 < Nat.lcm a b)
    ∧ ∑ a ∈ ({2, 3, 5} : Finset ℕ), (1 : ℚ) / a = 31 / 30 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num

end Erdos542
