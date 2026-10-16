import BilinearComplexity.BooleanRank
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators
namespace BilinearComplexity.BooleanRankProbability

/-- The actual Bernoulli entry weight, with one represented by Boolean true. -/
noncomputable def entryWeight (p : ℝ) (b : BoolSemiring) : ℝ :=
  if b = 1 then p else 1 - p

example (p : ℝ) : entryWeight p 0 = 1 - p := by simp [entryWeight]
example (p : ℝ) : entryWeight p 1 = p := by simp [entryWeight]

/-- Explicit iid weight on an actual Boolean matrix. -/
noncomputable def matrixWeight {m n : ℕ} (p : ℝ) (A : BoolMatrix m n) : ℝ :=
  ∏ i, ∏ j, entryWeight p (A i j)

example (p : ℝ) : matrixWeight p (0 : BoolMatrix 1 1) = 1 - p := by
  simp [matrixWeight, entryWeight]
example (p : ℝ) : matrixWeight p (fun _ _ => 1 : BoolMatrix 1 1) = p := by
  simp [matrixWeight, entryWeight]

/-- The two actual Boolean entries have total weight one. -/
theorem sum_entryWeight (p : ℝ) : ∑ b : BoolSemiring, entryWeight p b = 1 := by
  change (∑ b : Bool, if b = true then p else 1 - p) = 1
  simp

/-- A finite product law factors any coordinatewise cylinder, without enumeration. -/
theorem cylinder_factor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (w : ι → κ → ℝ) (P : ι → κ → Prop) [∀ i, DecidablePred (P i)] :
    (∑ x : ι → κ, if ∀ i, P i (x i) then ∏ i, w i (x i) else 0) =
      ∏ i, ∑ b : κ, if P i b then w i b else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.prod_ite_zero, Finset.mem_univ, forall_const]

/-- The explicit matrix weights sum to one, for all rectangular shapes. -/
theorem sum_matrixWeight (m n : ℕ) (p : ℝ) :
    ∑ A : BoolMatrix m n, matrixWeight p A = 1 := by
  unfold matrixWeight
  rw [← Fintype.prod_sum (fun (_ : Fin m) (r : Fin n → BoolSemiring) =>
    ∏ j, entryWeight p (r j))]
  have hrow : (∑ r : Fin n → BoolSemiring, ∏ j, entryWeight p (r j)) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (b : BoolSemiring) => entryWeight p b)]
    simp [sum_entryWeight]
  simp [hrow]

/-- In the intended open parameter range every actual matrix has nonnegative weight. -/
theorem matrixWeight_nonneg {m n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (A : BoolMatrix m n) : 0 ≤ matrixWeight p A := by
  apply Finset.prod_nonneg
  intro i hi
  apply Finset.prod_nonneg
  intro j hj
  unfold entryWeight
  split_ifs
  · exact le_of_lt hp
  · exact sub_nonneg.mpr (le_of_lt hp1)

/-- Fixing any set of entries in one column to a common Boolean value has
mass equal to the corresponding Bernoulli weight raised to the set cardinality. -/
theorem fixed_entries_mass {m : ℕ} (p : ℝ) (S : Finset (Fin m)) (b : BoolSemiring) :
    (∑ x : Fin m → BoolSemiring,
      if ∀ k ∈ S, x k = b then ∏ k, entryWeight p (x k) else 0) =
      (entryWeight p b) ^ S.card := by
  have hc : (∑ x : Fin m → BoolSemiring,
      if ∀ k ∈ S, x k = b then ∏ k, entryWeight p (x k) else 0) =
      ∏ k : Fin m, ∑ a : BoolSemiring,
        if k ∈ S → a = b then entryWeight p a else 0 := by
    convert cylinder_factor
      (fun (_ : Fin m) (a : BoolSemiring) => entryWeight p a)
      (fun k a => k ∈ S → a = b) using 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  rw [hc]
  have hs (k : Fin m) :
      (∑ a : BoolSemiring, if k ∈ S → a = b then entryWeight p a else 0) =
        if k ∈ S then entryWeight p b else 1 := by
    by_cases hk : k ∈ S
    · simp [hk]
    · simp [hk, sum_entryWeight]
  simp_rw [hs]
  rw [Finset.prod_ite_mem]
  simp

/-- In one actual column, all rows in `U` are dominated by a distinct pivot
with total weight `p + (1-p)^(U.card+1)`. The two disjoint cases are a one
at the pivot, or zeros at the pivot and throughout `U`. -/
theorem dominated_column_mass {m : ℕ} (p : ℝ) (r : Fin m)
    (U : Finset (Fin m)) (hrU : r ∉ U) :
    (∑ x : Fin m → BoolSemiring,
      if ∀ i ∈ U, x i = 1 → x r = 1 then ∏ k, entryWeight p (x k) else 0) =
      p + (1 - p) ^ (U.card + 1) := by
  have hsplit (x : Fin m → BoolSemiring) :
      (if ∀ i ∈ U, x i = 1 → x r = 1 then ∏ k, entryWeight p (x k) else 0) =
        (if x r = 1 then ∏ k, entryWeight p (x k) else 0) +
        (if ∀ i ∈ insert r U, x i = 0 then ∏ k, entryWeight p (x k) else 0) := by
    by_cases h1 : x r = 1
    · simp [h1]
    · have h0 : x r = 0 := (BoolSemiring.eq_zero_or_eq_one (x r)).resolve_right h1
      have he : (∀ i ∈ U, x i = 1 → x r = 1) ↔
          (∀ i ∈ insert r U, x i = 0) := by
        constructor
        · intro h i hi
          rcases Finset.mem_insert.mp hi with hir | hiU
          · simpa only [hir] using h0
          · exact (BoolSemiring.eq_zero_or_eq_one (x i)).resolve_right
              (fun hi1 => h1 (h i hiU hi1))
        · intro hz i hi hi1
          have hi0 : x i = 0 := hz i (Finset.mem_insert_of_mem hi)
          rw [hi1] at hi0
          exact False.elim ((by decide : (1 : BoolSemiring) ≠ 0) hi0)
      simp only [if_neg h1, zero_add]
      simp only [he]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have h_one : (∑ x : Fin m → BoolSemiring,
      if x r = 1 then ∏ k, entryWeight p (x k) else 0) = p := by
    simpa [entryWeight] using fixed_entries_mass p {r} 1
  have h_zero : (∑ x : Fin m → BoolSemiring,
      if ∀ i ∈ insert r U, x i = 0 then ∏ k, entryWeight p (x k) else 0) =
      (1-p)^(U.card+1) := by
    simpa [entryWeight, Finset.card_insert_of_notMem hrU] using
      fixed_entries_mass p (insert r U) 0
  rw [h_one, h_zero]

/-- Any actual matrix event expressed independently in each column factors
under the explicit product weights. The change of variables is matrix transpose. -/
theorem matrix_column_cylinder {m n : ℕ} (p : ℝ)
    (P : Fin n → (Fin m → BoolSemiring) → Prop) [∀ j, DecidablePred (P j)] :
    (∑ A : BoolMatrix m n,
      if ∀ j, P j (fun i => A i j) then matrixWeight p A else 0) =
      ∏ j, ∑ x : Fin m → BoolSemiring,
        if P j x then ∏ i, entryWeight p (x i) else 0 := by
  calc
    _ = ∑ B : BoolMatrix n m,
        if ∀ j, P j (B j) then ∏ j, ∏ i, entryWeight p (B j i) else 0 := by
      apply Fintype.sum_equiv (Equiv.functionSwap (Fin m) (Fin n) (fun _ _ => BoolSemiring))
      intro A
      change (if ∀ j, P j (fun i => A i j) then
        ∏ i, ∏ j, entryWeight p (A i j) else 0) =
        (if ∀ j, P j (fun i => A i j) then ∏ j, ∏ i, entryWeight p (A i j) else 0)
      split_ifs
      · exact Finset.prod_comm
      · rfl
    _ = _ := by
      convert cylinder_factor
        (fun (_ : Fin n) (x : Fin m → BoolSemiring) => ∏ i, entryWeight p (x i)) P using 1
      apply Finset.sum_congr rfl
      intro B hB
      split_ifs <;> rfl

/-- Boolean entry domination is exactly the order induced by Boolean OR:
adding the dominated entry to the dominating entry leaves it unchanged. -/
theorem entry_domination_iff_or (a b : BoolSemiring) :
    (a = 1 → b = 1) ↔ a + b = b := by
  rcases BoolSemiring.eq_zero_or_eq_one a with ha | ha
  · simp [ha]
  · rcases BoolSemiring.eq_zero_or_eq_one b with hb | hb
    · simp [ha, hb]
    · have hor : (1 : BoolSemiring) + 1 = 1 := rfl
      simp [ha, hb, hor]

/-- The actual iid Bernoulli weighted mass of every row in `U` being
bitwise dominated by a distinct pivot row is `(p + (1-p)^(U.card+1))^n`.
This polynomial identity holds for all real `p`; in `0 < p < 1` the
normalized nonnegative matrix weights give precisely the Bernoulli law. -/
theorem dominated_rows_mass {m n : ℕ} (p : ℝ) (r : Fin m)
    (U : Finset (Fin m)) (hrU : r ∉ U) :
    (∑ A : BoolMatrix m n,
      if ∀ i ∈ U, ∀ j, A i j = 1 → A r j = 1 then matrixWeight p A else 0) =
      (p + (1 - p) ^ (U.card + 1)) ^ n := by
  have he (A : BoolMatrix m n) :
      (∀ i ∈ U, ∀ j, A i j = 1 → A r j = 1) ↔
        (∀ j, ∀ i ∈ U, A i j = 1 → A r j = 1) := by
    constructor
    · intro h j i hi
      exact h i hi j
    · intro h i hi j
      exact h j i hi
  calc
    _ = ∑ A : BoolMatrix m n,
        if ∀ j, ∀ i ∈ U, A i j = 1 → A r j = 1 then matrixWeight p A else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      simp only [he]
    _ = ∏ _ : Fin n, ∑ x : Fin m → BoolSemiring,
        if ∀ i ∈ U, x i = 1 → x r = 1 then ∏ k, entryWeight p (x k) else 0 := by
      convert matrix_column_cylinder p
        (fun (_ : Fin n) (x : Fin m → BoolSemiring) => ∀ i ∈ U, x i = 1 → x r = 1) using 1
    _ = _ := by simp [dominated_column_mass p r U hrU]

example {m n : ℕ} (p : ℝ) (r : Fin m) :
    (∑ A : BoolMatrix m n,
      if ∀ i ∈ (∅ : Finset (Fin m)), ∀ j, A i j = 1 → A r j = 1
      then matrixWeight p A else 0) = 1 := by
  have hadd : p + (1 - p) = 1 := by rw [add_comm, sub_add_cancel]
  simpa [hadd] using dominated_rows_mass (n := n) p r ∅ (by simp)

example {m : ℕ} (p : ℝ) (r : Fin m) (U : Finset (Fin m)) (hrU : r ∉ U) :
    (∑ A : BoolMatrix m 0,
      if ∀ i ∈ U, ∀ j, A i j = 1 → A r j = 1 then matrixWeight p A else 0) = 1 := by
  simpa using dominated_rows_mass (n := 0) p r U hrU

example : 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
    (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) ∧
    ({1} : Finset (Fin 2)).Nonempty ∧ Nonempty (BoolMatrix 2 1) := by
  refine ⟨by norm_num, by norm_num, by decide, ?_, ⟨0⟩⟩
  exact ⟨1, by simp⟩

example : Nonempty (BoolMatrix 1 1) := ⟨0⟩
end BilinearComplexity.BooleanRankProbability
