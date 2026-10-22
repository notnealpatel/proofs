/-
# A222955 — Wiseman: a binary word is counted iff it has the same sum of
# positions of 1's as its reverse

Gus Wiseman's conjecture in OEIS A222955 (January 7, 2023) characterizes
the counted binary words by equality of the position sums of their 1's
with those of their reverses, equivalently by equality of partial-sum totals.
For `n ≥ 2`, the least-squares numerator is
`∑ i x_i - (n+1)/2 ∑ x_i = (∑ i x_i - ∑ (n+1-i) x_i) / 2`.

## Modelling

* The array is `A : Fin n → Fin 1 → Fin 2` (`n` rows, one column, entries
  `0..1`).  Row `r` is the one-point sequence `j ↦ A r j`; the column is the
  `n`-point sequence `i ↦ A i 0`.  A sequence `y_1..y_m` is placed at the
  points `(k, y_k)`, `k = 1..m` (0-indexed `i : Fin m` sits at abscissa
  `i + 1`).
* `lsSlope` is the textbook least-squares slope
  `∑ (t_k - t̄)(y_k - ȳ) / ∑ (t_k - t̄)^2`.  Its denominator vanishes exactly
  when `m ≤ 1`; `ZeroSlope` therefore states the entry's convention explicitly
  (`m ≤ 1 ∨ lsSlope y = 0`) instead of relying on Lean's `x / 0 = 0`.
* The word of `A` is its column `i ↦ A i 0`; positions are 1-based, so the
  "sum of positions of 1's" is `posSum w = ∑ i, (i + 1) * w i`, and the reverse
  word is `w ∘ Fin.rev`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A222955BinaryWordCounted

open Finset

/-! ## Definition layer -/

/-- The least-squares slope of the points `(k, y_k)`, `k = 1..m`, where the
0-indexed `i : Fin m` is placed at abscissa `i + 1`:
`∑ (t_k - t̄)(y_k - ȳ) / ∑ (t_k - t̄)^2`.  For `m ≤ 1` the denominator is `0`
and the value is Lean's junk `0`; `ZeroSlope` guards that case explicitly. -/
def lsSlope {m : ℕ} (y : Fin m → ℚ) : ℚ :=
  let tbar : ℚ := (∑ i : Fin m, (((i : ℕ) : ℚ) + 1)) / m
  let ybar : ℚ := (∑ i : Fin m, y i) / m
  (∑ i : Fin m, (((i : ℕ) : ℚ) + 1 - tbar) * (y i - ybar)) /
    ∑ i : Fin m, (((i : ℕ) : ℚ) + 1 - tbar) ^ 2

/-- A sequence `y_1..y_m` least-squares fits a zero-slope line, with the
entry's convention that a single point (and, degenerately, the empty
sequence) has zero slope. -/
def ZeroSlope {m : ℕ} (y : Fin m → ℚ) : Prop :=
  m ≤ 1 ∨ lsSlope y = 0

instance {m : ℕ} (y : Fin m → ℚ) : Decidable (ZeroSlope y) := by
  unfold ZeroSlope; infer_instance

/-- An `n X 1` `0..1` array is counted by A222955 when every row and every
column least-squares fits a zero-slope straight line. -/
def Counted {n : ℕ} (A : Fin n → Fin 1 → Fin 2) : Prop :=
  (∀ r : Fin n, ZeroSlope (fun j : Fin 1 => ((A r j : ℕ) : ℚ))) ∧
    ∀ c : Fin 1, ZeroSlope (fun i : Fin n => ((A i c : ℕ) : ℚ))

instance {n : ℕ} (A : Fin n → Fin 1 → Fin 2) : Decidable (Counted A) := by
  unfold Counted; infer_instance

/-- `a n` is the A222955 term: the number of counted `n X 1` `0..1` arrays. -/
def a (n : ℕ) : ℕ :=
  (univ.filter (fun A : Fin n → Fin 1 → Fin 2 => Counted A)).card

/-- Sum of the (1-based) positions of the 1's of a binary word. -/
def posSum {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ i : Fin n, ((i : ℕ) + 1) * (w i : ℕ)

/-- Sum of the partial sums `∑_{k=1}^{n} (w_1 + ... + w_k)` of a binary word. -/
def partialSumTotal {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ k : Fin n, ∑ i ∈ univ.filter (fun i : Fin n => i ≤ k), (w i : ℕ)

/-! ## Examples -/

-- The first DATA terms `2, 2, 4, 4, 8` straight from the slope definition.
example : a 1 = 2 := by decide
example : a 2 = 2 := by decide +kernel
example : a 3 = 4 := by decide +kernel
example : a 4 = 4 := by decide +kernel
example : a 5 = 8 := by decide +kernel
example : a 6 = 8 := by decide +kernel
example : a 7 = 20 := by decide +kernel
example : a 8 = 18 := by decide +kernel

-- `posSum` and `partialSumTotal` on the word `1101`: positions `1 + 2 + 4 = 7`;
-- partial sums `1, 2, 2, 3` total `8`.
example : posSum (n := 4) ![1, 1, 0, 1] = 7 := by decide
example : partialSumTotal (n := 4) ![1, 1, 0, 1] = 8 := by decide

/-! ## Algebra of the least-squares slope -/

/-- `∑_{i<m} (i + 1) = m (m + 1) / 2` over `ℚ`. -/
theorem sum_fin_succ_cast (m : ℕ) : ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    push_cast
    ring

/-- For `m ≥ 2` points `(k,y_k)`, the least-squares slope vanishes iff
`∑ k y_k = ∑ (m+1-k) y_k`, the position-weighted sum of the reversed sequence. -/
theorem lsSlope_eq_zero_iff {m : ℕ} (hm : 2 ≤ m) (y : Fin m → ℚ) :
    lsSlope y = 0 ↔
      ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) * y i =
        ∑ i : Fin m, (((Fin.rev i : ℕ) : ℚ) + 1) * y i := by
  have hm2 : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have htbar : (∑ i : Fin m, (((i : ℕ) : ℚ) + 1)) / m = (m + 1) / 2 := by
    rw [sum_fin_succ_cast]
    field_simp
  -- the denominator is positive: the first abscissa `1` differs from the mean
  have hden : 0 < ∑ i : Fin m, (((i : ℕ) : ℚ) + 1 - (m + 1) / 2) ^ 2 := by
    have hpos : 0 < ((((⟨0, by omega⟩ : Fin m) : ℕ) : ℚ) + 1 - ((m : ℚ) + 1) / 2) ^ 2 := by
      simp only [Nat.cast_zero]
      nlinarith
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨_, Finset.mem_univ _, hpos⟩
  -- centred abscissae sum to zero
  have hcen : ∑ i : Fin m, (((i : ℕ) : ℚ) + 1 - (m + 1) / 2) = 0 := by
    rw [Finset.sum_sub_distrib, sum_fin_succ_cast, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the numerator is `∑ t_k y_k - t̄ ∑ y_k`
  have hnum : ∑ i : Fin m, (((i : ℕ) : ℚ) + 1 - (m + 1) / 2) * (y i - (∑ j : Fin m, y j) / m)
      = ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) * y i - (m + 1) / 2 * ∑ i : Fin m, y i := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcen, zero_mul, sub_zero]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- the reversed weights are `m + 1 - t_k`
  have hrev : ∑ i : Fin m, (((Fin.rev i : ℕ) : ℚ) + 1) * y i
      = (m + 1) * ∑ i : Fin m, y i - ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) * y i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi : (Fin.rev i : ℕ) + (i : ℕ) + 1 = m := by
      rw [Fin.val_rev]
      omega
    have hiq : ((Fin.rev i : ℕ) : ℚ) = m - 1 - i := by
      have hcast := congrArg (fun k : ℕ => (k : ℚ)) hi
      push_cast at hcast
      linarith
    rw [hiq]
    ring
  unfold lsSlope
  simp only [htbar]
  rw [div_eq_zero_iff, hnum, hrev]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hden.ne'
  · intro h
    left
    linarith

/-! ## Reversal bookkeeping on words -/

/-- The position sum of the reversed word, reindexed: position `i` of `w`
contributes with weight `rev i + 1 = n - i`. -/
theorem posSum_comp_rev {n : ℕ} (w : Fin n → Fin 2) :
    posSum (w ∘ Fin.rev) = ∑ i : Fin n, (((Fin.rev i : Fin n) : ℕ) + 1) * (w i : ℕ) := by
  unfold posSum
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin n => (((Fin.rev i : Fin n) : ℕ) + 1) * (w i : ℕ))]
  simp only [Fin.revPerm_apply, Fin.rev_rev, Function.comp_apply]

/-- The sum of partial sums of a word equals the position sum of its reverse. -/
theorem partialSumTotal_eq_posSum_comp_rev {n : ℕ} (w : Fin n → Fin 2) :
    partialSumTotal w = posSum (w ∘ Fin.rev) := by
  rw [posSum_comp_rev]
  unfold partialSumTotal
  rw [Finset.sum_comm' (t' := univ) (s' := fun i => univ.filter (fun k : Fin n => i ≤ k))]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Fin.val_rev, Finset.filter_le_eq_Ici, Fin.card_Ici]
    omega
  · intro k i
    simp

/-! ## The conjecture -/

/-- Wiseman's conjecture (OEIS A222955, January 7, 2023), position-sum form:
an `n × 1` binary array has zero-slope least-squares fits in every row
and column iff its word has the same sum of positions of 1's as its reverse.
For `n ≤ 1`, both sides hold trivially. -/
theorem counted_iff_posSum_eq_posSum_reverse {n : ℕ} (A : Fin n → Fin 1 → Fin 2) :
    Counted A ↔ posSum (fun i => A i 0) = posSum (fun i => A (Fin.rev i) 0) := by
  have hrows : ∀ r : Fin n, ZeroSlope (fun j : Fin 1 => ((A r j : ℕ) : ℚ)) :=
    fun _ => Or.inl le_rfl
  have hcol : Counted A ↔ ZeroSlope (fun i : Fin n => ((A i 0 : ℕ) : ℚ)) := by
    refine ⟨fun h => h.2 0, fun h => ⟨hrows, fun c => ?_⟩⟩
    rwa [Subsingleton.elim c 0]
  rw [hcol]
  set w : Fin n → Fin 2 := fun i => A i 0 with hw
  change ZeroSlope (fun i : Fin n => ((w i : ℕ) : ℚ)) ↔ posSum w = posSum (w ∘ Fin.rev)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `n ≤ 1`: the column is a single point (or empty) and reversal is trivial
    have hsub : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    have hrevw : w ∘ Fin.rev = w := funext fun i => congrArg w (Subsingleton.elim _ _)
    exact ⟨fun _ => by rw [hrevw], fun _ => Or.inl (by omega)⟩
  · have hnot : ¬ n ≤ 1 := by omega
    unfold ZeroSlope
    rw [or_iff_right hnot, lsSlope_eq_zero_iff hn, posSum_comp_rev]
    unfold posSum
    rw [← Nat.cast_inj (R := ℚ)]
    push_cast
    rfl

/-- **Wiseman's conjecture (A222955), second ("equivalently") form.**

An `n X 1` `0..1` array is counted iff its word has the same sum of partial
sums as its reverse. -/
theorem counted_iff_partialSumTotal_eq_partialSumTotal_reverse {n : ℕ}
    (A : Fin n → Fin 1 → Fin 2) :
    Counted A ↔
      partialSumTotal (fun i => A i 0) = partialSumTotal (fun i => A (Fin.rev i) 0) := by
  rw [counted_iff_posSum_eq_posSum_reverse]
  have hl : partialSumTotal (fun i => A i 0) = posSum (fun i => A (Fin.rev i) 0) :=
    partialSumTotal_eq_posSum_comp_rev _
  have hr : partialSumTotal (fun i => A (Fin.rev i) 0) = posSum (fun i => A i 0) := by
    rw [partialSumTotal_eq_posSum_comp_rev]
    congr 1
    funext i
    simp only [Function.comp_apply, Fin.rev_rev]
  rw [hl, hr]
  exact eq_comm

/-- Counting corollary: `a n` equals the number of binary words of length `n`
with the same sum of positions of 1's as their reverse. -/
theorem a_eq_card_posSum_eq_reverse (n : ℕ) :
    a n = (univ.filter (fun w : Fin n → Fin 2 => posSum w = posSum (w ∘ Fin.rev))).card := by
  unfold a
  let e : (Fin n → Fin 1 → Fin 2) ≃ (Fin n → Fin 2) :=
    Equiv.arrowCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) (Fin 2))
  refine Finset.card_bij (fun A _ => e A) ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact (counted_iff_posSum_eq_posSum_reverse A).mp hA
  · intro A _ B _ hAB
    exact e.injective hAB
  · intro w hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [counted_iff_posSum_eq_posSum_reverse]
    have hcol : (fun i => e.symm w i 0) = w := by
      funext i
      rfl
    have hcolr : (fun i => e.symm w (Fin.rev i) 0) = w ∘ Fin.rev := by
      funext i
      rfl
    rw [hcol, hcolr]
    exact hw

/-- At `n = 3` the word `101` is counted and the
word `100` is not, so both sides of the equivalence take both truth values. -/
example : Counted (n := 3) (fun i _ => ![1, 0, 1] i) ∧
    ¬ Counted (n := 3) (fun i _ => ![1, 0, 0] i) := by
  decide +kernel

end Candidates.A222955BinaryWordCounted
