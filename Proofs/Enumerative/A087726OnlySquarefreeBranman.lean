/-
Square-zero matrices over ZMod n (OEIS A087726; Ben Branman, Mar 22 2013).

For nonzero n, the number of 2×2 matrices X with X²=0 is n² iff n is squarefree;
for nonsquarefree n it is strictly larger.
Trace-zero matrices !![a,b;c,-a] give a parameter count. A prime square dividing n
makes a fiber inequality strict; for squarefree n the ring is reduced and all
comparisons are equalities.
The squarefree direction is recorded by Eric M. Schmidt (Mar 23 2013);
the entry also gives Robert Israel's prime-power formula (Jun 10 2015)
and Manfred Scheucher's proof reference for its k=1 case (Jun 10 2015).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A087726OnlySquarefreeBranman

open Finset

/-! ## Definition layer -/

/-- `a087726 n` (OEIS A087726): the number of matrices `X ∈ M_2(ℤ/nℤ)` with
`X ^ 2 = 0`.  The entry has offset `1`, so `n ≥ 1` is carried as `[NeZero n]`
(which also makes `ZMod n` finite). -/
def a087726 (n : ℕ) [NeZero n] : ℕ :=
  Fintype.card {X : Matrix (Fin 2) (Fin 2) (ZMod n) // X ^ 2 = 0}

-- Examples against the OEIS DATA line `1, 4, 9, 28, 25, 36, ...`.
example : a087726 1 = 1 := by decide
example : a087726 2 = 4 := by decide
example : a087726 3 = 9 := by decide
example : a087726 4 = 28 := by decide
example : a087726 5 = 25 := by decide
example : a087726 6 = 36 := by decide

/-- Auxiliary count: the number of triples `(a, b, c)` over `ℤ/nℤ` with
`a ^ 2 + b * c = 0`, i.e. the number of trace-zero square-zero matrices
`!![a, b; c, -a]`. -/
def tripleCount (n : ℕ) [NeZero n] : ℕ :=
  Fintype.card {v : ZMod n × ZMod n × ZMod n // v.1 ^ 2 + v.2.1 * v.2.2 = 0}

/-- Auxiliary count: the fibre size `#{c | b * c = r}` of multiplication by `b`
on `ℤ/nℤ`. -/
def fiberCount {n : ℕ} [NeZero n] (b r : ZMod n) : ℕ := #{c : ZMod n | b * c = r}

/-! ## Ring-theoretic helpers -/

/-- A finite reduced commutative ring is von Neumann regular: every `b` has the
form `b = b ^ 2 * x`. -/
theorem exists_eq_sq_mul {R : Type*} [CommRing R] [Finite R] [IsReduced R] (b : R) :
    ∃ x, b = b ^ 2 * x := by
  have key : ∀ i k : ℕ, b ^ (i + 1) = b ^ (i + 1 + (k + 1)) → ∃ x, b = b ^ 2 * x := by
    intro i k hik
    have h2 : b ^ (i + 1) * (1 - b ^ (k + 1)) = 0 := by
      rw [mul_sub, mul_one, ← pow_add, ← hik, sub_self]
    have hnil : (b - b ^ (k + 2)) ^ (i + 1) = 0 := by
      rw [show b - b ^ (k + 2) = b * (1 - b ^ (k + 1)) by ring, mul_pow,
        pow_succ (1 - b ^ (k + 1)) i, mul_comm ((1 - b ^ (k + 1)) ^ i), ← mul_assoc, h2,
        zero_mul]
    have hzero : b - b ^ (k + 2) = 0 := IsReduced.eq_zero _ ⟨i + 1, hnil⟩
    exact ⟨b ^ k, by linear_combination hzero⟩
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => b ^ (k + 1))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
    exact key i k (h.trans (by ring))
  · obtain ⟨k, rfl⟩ : ∃ k, i = j + (k + 1) := ⟨i - j - 1, by omega⟩
    exact key j k (h.symm.trans (by ring))

/-- In a finite reduced commutative ring, principal ideals are radical in the
form needed here: if `-a ^ 2 ∈ bR` then `a ∈ bR`. -/
theorem exists_mul_eq_of_mul_eq_neg_sq {R : Type*} [CommRing R] [Finite R] [IsReduced R]
    (a b c : R) (h : b * c = -a ^ 2) : ∃ t, b * t = a := by
  obtain ⟨x, hx⟩ := exists_eq_sq_mul b
  have he : a ^ 2 * (b * x) = a ^ 2 := by linear_combination (b * x - 1) * h + c * hx
  have hsq : (a - a * (b * x)) ^ 2 = 0 := by linear_combination (-1 : R) * he - a ^ 2 * x * hx
  have hzero : a - a * (b * x) = 0 := IsReduced.eq_zero _ ⟨2, hsq⟩
  exact ⟨x * a, by linear_combination -hzero⟩

/-- If `n` is not squarefree, then over `ℤ/nℤ` there are `a, b` with
`-a ^ 2 ∈ bR` but `a ∉ bR` (take `p ^ 2 ∣ n`, `a = p`, `b = p * p`). -/
theorem exists_witness_of_not_squarefree {n : ℕ} [NeZero n] (hn : ¬ Squarefree n) :
    ∃ a b : ZMod n, (∀ t, b * t ≠ a) ∧ ∃ c, b * c = -a ^ 2 := by
  rw [Nat.squarefree_iff_prime_squarefree] at hn
  push Not at hn
  obtain ⟨p, hp, hpn⟩ := hn
  refine ⟨(p : ZMod n), (p : ZMod n) * p, ?_, -1, by ring⟩
  intro t ht
  have hcast : (((p : ℤ) * p * (t.val : ℤ) - p : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ht, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
  have hpp : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) * p * (t.val : ℤ) - p :=
    (Int.natCast_dvd_natCast.mpr hpn).trans hcast
  have hpp' : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) := by
    have h1 : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) * p * (t.val : ℤ) :=
      ⟨(t.val : ℤ), by push_cast; ring⟩
    have h2 := dvd_sub h1 hpp
    simpa using h2
  have hdvd : p * p ∣ p := Int.natCast_dvd_natCast.mp hpp'
  have hle : p * p ≤ p := Nat.le_of_dvd hp.pos hdvd
  have h2 := hp.two_le
  nlinarith

/-! ## Fibre counting -/

/-- The fibres of `c ↦ b * c` partition `ℤ/nℤ`: `∑ r, #{c | b * c = r} = n`. -/
theorem sum_fiberCount {n : ℕ} [NeZero n] (b : ZMod n) : ∑ r, fiberCount b r = n := by
  unfold fiberCount
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun c : ZMod n => b * c) (s := univ)
    (t := univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  simp [ZMod.card]

/-- A fibre is nonempty exactly over the range of `c ↦ b * c`. -/
theorem fiberCount_pos_iff {n : ℕ} [NeZero n] (b r : ZMod n) :
    0 < fiberCount b r ↔ ∃ c, b * c = r := by
  unfold fiberCount
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp

/-- A fibre outside the range of `c ↦ b * c` is empty. -/
theorem fiberCount_eq_zero {n : ℕ} [NeZero n] (b r : ZMod n) (h : ¬ ∃ c, b * c = r) :
    fiberCount b r = 0 := by
  by_contra hne
  exact h ((fiberCount_pos_iff b r).mp (Nat.pos_of_ne_zero hne))

/-- Two fibres over points of the range of `c ↦ b * c` have the same size
(they are translates of each other). -/
theorem fiberCount_eq_of_mem {n : ℕ} [NeZero n] (b r s : ZMod n) (hr : ∃ c, b * c = r)
    (hs : ∃ c, b * c = s) : fiberCount b r = fiberCount b s := by
  unfold fiberCount
  obtain ⟨t, rfl⟩ := hr
  obtain ⟨t', rfl⟩ := hs
  refine Finset.card_nbij' (fun c => c + (t' - t)) (fun c => c - (t' - t)) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
    linear_combination hc
  · intro c hc
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
    linear_combination hc
  · intro c _
    ring
  · intro c _
    ring

/-- Pointwise comparison: `#{c | b * c = a} ≤ #{c | b * c = -a ^ 2}`. -/
theorem fiberCount_le {n : ℕ} [NeZero n] (b a : ZMod n) :
    fiberCount b a ≤ fiberCount b (-a ^ 2) := by
  by_cases ha : ∃ t, b * t = a
  · obtain ⟨t, ht⟩ := ha
    exact (fiberCount_eq_of_mem b a (-a ^ 2) ⟨t, ht⟩
      ⟨-(t * a), by rw [← ht]; ring⟩).le
  · rw [fiberCount_eq_zero b a ha]
    exact Nat.zero_le _

/-- The triple count as a double sum of fibre sizes:
`N(n) = ∑_a ∑_b #{c | b * c = -a ^ 2}`. -/
theorem tripleCount_eq {n : ℕ} [NeZero n] :
    tripleCount n = ∑ a : ZMod n, ∑ b : ZMod n, fiberCount b (-a ^ 2) := by
  unfold tripleCount fiberCount
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => if_congr ?_ rfl rfl
  exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

/-- `n ^ 2 = ∑_a ∑_b #{c | b * c = a}`. -/
theorem sq_eq_sum_fiberCount {n : ℕ} [NeZero n] :
    n ^ 2 = ∑ a : ZMod n, ∑ b : ZMod n, fiberCount b a := by
  rw [Finset.sum_comm]
  simp only [sum_fiberCount, sum_const, card_univ, ZMod.card, smul_eq_mul, sq]

/-- Lower bound: `n ^ 2 ≤ N(n)` for every `n ≥ 1`. -/
theorem sq_le_tripleCount (n : ℕ) [NeZero n] : n ^ 2 ≤ tripleCount n := by
  rw [sq_eq_sum_fiberCount, tripleCount_eq]
  exact sum_le_sum fun a _ => sum_le_sum fun b _ => fiberCount_le b a

/-- Strict lower bound: if some `a ∉ bR` has `-a ^ 2 ∈ bR`, then `n ^ 2 < N(n)`. -/
theorem sq_lt_tripleCount {n : ℕ} [NeZero n] (a₀ b₀ : ZMod n) (ha : ∀ t, b₀ * t ≠ a₀)
    (hc : ∃ c, b₀ * c = -a₀ ^ 2) : n ^ 2 < tripleCount n := by
  rw [sq_eq_sum_fiberCount, tripleCount_eq]
  have hstrict : fiberCount b₀ a₀ < fiberCount b₀ (-a₀ ^ 2) := by
    rw [fiberCount_eq_zero b₀ a₀ (fun ⟨t, ht⟩ => ha t ht)]
    exact (fiberCount_pos_iff b₀ (-a₀ ^ 2)).mpr hc
  refine sum_lt_sum (fun a _ => sum_le_sum fun b _ => fiberCount_le b a)
    ⟨a₀, mem_univ _, ?_⟩
  exact sum_lt_sum (fun b _ => fiberCount_le b a₀) ⟨b₀, mem_univ _, hstrict⟩

/-- Equality: if `-a ^ 2 ∈ bR → a ∈ bR` for all `a, b`, then `N(n) = n ^ 2`. -/
theorem tripleCount_eq_sq {n : ℕ} [NeZero n]
    (h : ∀ a b : ZMod n, (∃ c, b * c = -a ^ 2) → ∃ t, b * t = a) : tripleCount n = n ^ 2 := by
  rw [sq_eq_sum_fiberCount, tripleCount_eq]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases hc : ∃ c, b * c = -a ^ 2
  · exact (fiberCount_eq_of_mem b a (-a ^ 2) (h a b hc) hc).symm
  · have ha : ¬ ∃ t, b * t = a := fun ⟨t, ht⟩ => hc ⟨-(t * a), by rw [← ht]; ring⟩
    rw [fiberCount_eq_zero b _ hc, fiberCount_eq_zero b _ ha]

/-! ## Matrix helpers -/

/-- The four entry equations of `X ^ 2 = 0` for a `2 × 2` matrix. -/
theorem entries_of_sq_eq_zero {R : Type*} [CommRing R] {X : Matrix (Fin 2) (Fin 2) R}
    (h : X ^ 2 = 0) :
    X 0 0 * X 0 0 + X 0 1 * X 1 0 = 0 ∧ X 0 0 * X 0 1 + X 0 1 * X 1 1 = 0 ∧
      X 1 0 * X 0 0 + X 1 1 * X 1 0 = 0 ∧ X 1 0 * X 0 1 + X 1 1 * X 1 1 = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

/-- Over a reduced commutative ring a square-zero `2 × 2` matrix has trace zero:
`(tr X) ^ 3` is a combination of the entry equations. -/
theorem trace_eq_zero_of_sq_eq_zero {R : Type*} [CommRing R] [IsReduced R]
    {X : Matrix (Fin 2) (Fin 2) R} (h : X ^ 2 = 0) : X 1 1 = -X 0 0 := by
  obtain ⟨e1, e2, -, e4⟩ := entries_of_sq_eq_zero h
  have ht : (X 0 0 + X 1 1) ^ 3 = 0 := by
    linear_combination (X 0 0 + 3 * X 1 1) * e1 + (3 * X 0 0 + X 1 1) * e4 - 4 * X 1 0 * e2
  have hz : X 0 0 + X 1 1 = 0 := IsReduced.eq_zero _ ⟨3, ht⟩
  linear_combination hz

/-- `!![a, b; c, -a] ^ 2 = 0` whenever `a ^ 2 + b * c = 0`. -/
theorem traceless_sq_eq_zero {R : Type*} [CommRing R] (a b c : R) (h : a ^ 2 + b * c = 0) :
    (!![a, b; c, -a]) ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, sq, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_two, mul_neg, neg_mul, neg_neg, Matrix.zero_apply] <;>
    first | linear_combination h | ring

/-- `N(n) ≤ a(n)`: trace-zero solutions inject into all solutions. -/
theorem tripleCount_le (n : ℕ) [NeZero n] : tripleCount n ≤ a087726 n := by
  refine Fintype.card_le_of_injective
    (fun v => ⟨!![v.1.1, v.1.2.1; v.1.2.2, -v.1.1], traceless_sq_eq_zero _ _ _ v.2⟩) ?_
  rintro ⟨⟨a, b, c⟩, hv⟩ ⟨⟨a', b', c'⟩, hw⟩ hvw
  have hX := congrArg Subtype.val hvw
  have h00 := congrFun (congrFun hX 0) 0
  have h01 := congrFun (congrFun hX 0) 1
  have h10 := congrFun (congrFun hX 1) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10
  simp [h00, h01, h10]

/-- `a(n) ≤ N(n)` when `ℤ/nℤ` is reduced: every solution has trace zero, so it is
determined by its entries `(X₀₀, X₀₁, X₁₀)`. -/
theorem le_tripleCount {n : ℕ} [NeZero n] [IsReduced (ZMod n)] : a087726 n ≤ tripleCount n := by
  refine Fintype.card_le_of_injective
    (fun X => ⟨(X.1 0 0, X.1 0 1, X.1 1 0), by
      obtain ⟨e1, -, -, -⟩ := entries_of_sq_eq_zero X.2
      linear_combination e1⟩) ?_
  rintro ⟨X, hX⟩ ⟨Y, hY⟩ hXY
  simp only [Subtype.mk.injEq, Prod.mk.injEq] at hXY
  obtain ⟨h00, h01, h10⟩ := hXY
  have h11 : X 1 1 = Y 1 1 := by
    rw [trace_eq_zero_of_sq_eq_zero hX, trace_eq_zero_of_sq_eq_zero hY, h00]
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-! ## The conjecture -/

/-- For nonzero `n`, the square-zero matrix count is `n²` iff `n` is squarefree. -/
theorem a087726_eq_sq_iff_squarefree (n : ℕ) [NeZero n] :
    a087726 n = n ^ 2 ↔ Squarefree n := by
  constructor
  · intro h
    by_contra hsq
    obtain ⟨a, b, ha, hc⟩ := exists_witness_of_not_squarefree hsq
    have hlt := sq_lt_tripleCount a b ha hc
    have hle := tripleCount_le n
    omega
  · intro hsq
    haveI : IsReduced (ZMod n) := isReduced_zmod.mpr (Or.inl hsq)
    have hrad : ∀ a b : ZMod n, (∃ c, b * c = -a ^ 2) → ∃ t, b * t = a :=
      fun a b ⟨c, hc⟩ => exists_mul_eq_of_mul_eq_neg_sq a b c hc
    have hN := tripleCount_eq_sq hrad
    exact le_antisymm (le_tripleCount.trans hN.le) (hN.symm.le.trans (tripleCount_le n))

/-- The non-squarefree half in strict form: if `n ≥ 1` is not squarefree then
`n ^ 2 < a(n)`. -/
theorem sq_lt_a087726_of_not_squarefree (n : ℕ) [NeZero n] (hn : ¬ Squarefree n) :
    n ^ 2 < a087726 n := by
  obtain ⟨a, b, ha, hc⟩ := exists_witness_of_not_squarefree hn
  exact (sq_lt_tripleCount a b ha hc).trans_le (tripleCount_le n)

/-! ## Sanity layer -/

-- Both sides of the equivalence occur: `n = 6` (squarefree, `a = 36 = 6^2`) and
-- `n = 4` (not squarefree, `a = 28 ≠ 16`); the theorem recovers `¬ Squarefree 4`.
example : a087726 6 = 6 ^ 2 ∧ Squarefree 6 :=
  ⟨by decide, (a087726_eq_sq_iff_squarefree 6).mp (by decide)⟩

example : ¬ Squarefree 4 := fun h =>
  absurd ((a087726_eq_sq_iff_squarefree 4).mpr h) (by decide)

end Candidates.A087726OnlySquarefreeBranman
