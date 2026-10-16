import BilinearComplexity.BooleanRankProbability
import BilinearComplexity.BooleanRankCounting
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
namespace BilinearComplexity.BooleanRankProbability

/-- The total iid weight of matrices with deficient displayed-row OR rank. -/
noncomputable def deficitMass (p : ℝ) (n : ℕ) : ℝ :=
  ∑ A : BoolMatrix n n, if boolRowRank A < n then matrixWeight p A else 0

example (p : ℝ) : deficitMass p 0 = 0 := by simp [deficitMass]

/-- Deficient matrices have nonnegative total weight in the Bernoulli range. -/
theorem deficitMass_nonneg (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ deficitMass p n := by
  apply Finset.sum_nonneg
  intro A hA
  split_ifs
  · exact matrixWeight_nonneg p hp hp1 A
  · exact le_rfl

/-- The deficient event has mass at most one. -/
theorem deficitMass_le_one (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) :
    deficitMass p n ≤ 1 := by
  rw [← sum_matrixWeight n n p]
  apply Finset.sum_le_sum
  intro A hA
  split_ifs
  · exact le_rfl
  · exact matrixWeight_nonneg p hp hp1 A

/-- The probability of a pivot entry equalling the OR of a disjoint set of entries. -/
theorem or_column_mass {m : ℕ} (p : ℝ) (i : Fin m)
    (T : Finset (Fin m)) (hi : i ∉ T) :
    (∑ x : Fin m → BoolSemiring,
      if x i = ∑ j ∈ T, x j then ∏ j, entryWeight p (x j) else 0) =
      p + (1 - 2 * p) * (1 - p) ^ T.card := by
  classical
  have hz (x : Fin m → BoolSemiring) :
      (∑ j ∈ T, x j) = 0 ↔ ∀ j ∈ T, x j = 0 := by
    constructor
    · intro h j hj
      rcases BoolSemiring.eq_zero_or_eq_one (x j) with hj0 | hj1
      · exact hj0
      · have hone : (∑ j ∈ T, x j) = 1 :=
          (BoolSemiring.sum_eq_one_iff T x).mpr ⟨j, hj, hj1⟩
        rw [h] at hone
        exact False.elim ((by decide : (0 : BoolSemiring) ≠ 1) hone)
    · intro h
      exact Finset.sum_eq_zero h
  have hsplit (x : Fin m → BoolSemiring) :
      (if x i = ∑ j ∈ T, x j then ∏ j, entryWeight p (x j) else 0) =
      (if x i = 1 then ∏ j, entryWeight p (x j) else 0) -
      (if ∀ j ∈ T, x j = 0 then ∏ j, entryWeight p (x j) else 0) +
      2 * (if ∀ j ∈ insert i T, x j = 0 then ∏ j, entryWeight p (x j) else 0) := by
    rcases BoolSemiring.eq_zero_or_eq_one (x i) with hxi | hxi <;>
      rcases BoolSemiring.eq_zero_or_eq_one (∑ j ∈ T, x j) with hs | hs
    all_goals have ht := hz x
    all_goals simp only [Finset.mem_insert, forall_eq_or_imp] 
    all_goals simp [hxi, ← ht, hs] <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hone : (∑ x : Fin m → BoolSemiring,
      if x i = 1 then ∏ j, entryWeight p (x j) else 0) = p := by
    simpa [entryWeight] using fixed_entries_mass p {i} 1
  rw [hone, fixed_entries_mass, fixed_entries_mass]
  simp only [entryWeight, show (0 : BoolSemiring) ≠ 1 by decide, if_false,
    Finset.card_insert_of_notMem hi, pow_succ]
  ring

/-- Exact iid mass of an actual displayed row being the OR of the rows in `T`. -/
theorem row_eq_rowsSum_mass {m n : ℕ} (p : ℝ) (i : Fin m)
    (T : Finset (Fin m)) (hi : i ∉ T) :
    (∑ A : BoolMatrix m n, if A i = rowsSum A T then matrixWeight p A else 0) =
      (p + (1 - 2 * p) * (1 - p) ^ T.card) ^ n := by
  classical
  have he (A : BoolMatrix m n) :
      A i = rowsSum A T ↔ ∀ j, A i j = ∑ k ∈ T, A k j := by
    exact funext_iff
  simp_rw [he]
  have hc := matrix_column_cylinder (m := m) (n := n) p
    (fun (_ : Fin n) (x : Fin m → BoolSemiring) => x i = ∑ k ∈ T, x k)
  rw [hc]
  simp [or_column_mass p i T hi]

example : 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 ∧ 1 ≤ (1 : ℕ) ∧ 1+1 ≤ (2 : ℕ) ∧
    Nonempty (BoolMatrix 2 2) := by
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨0⟩⟩

private theorem mass_cover {α β : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (E : α → Prop) (s : Finset β) (F : β → α → Prop)
    [DecidablePred E] [∀ b, DecidablePred (F b)]
    (hc : ∀ a, E a → ∃ b ∈ s, F b a) :
    (∑ a, if E a then w a else 0) ≤ ∑ b ∈ s, ∑ a, if F b a then w a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases he : E a
  · obtain ⟨b, hb, hF⟩ := hc a he
    rw [if_pos he]
    have hsingle := Finset.single_le_sum
      (f := fun b => if F b a then w a else 0)
      (fun b _ => by split_ifs; exact hw a; exact le_refl 0) hb
    simpa only [if_pos hF] using hsingle
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun b _ => by split_ifs; exact hw a; exact le_refl 0)

private theorem mass_or {α : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (E F : α → Prop) [DecidablePred E] [DecidablePred F] :
    (∑ a, if E a ∨ F a then w a else 0) ≤
      (∑ a, if E a then w a else 0) + ∑ a, if F a then w a else 0 := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  by_cases he : E a <;> by_cases hf : F a <;> simp [he, hf, hw a]

/-- The finite two-scale weighted union bound for the actual displayed-row OR deficit. -/
theorem deficitMass_le_twoScale (p : ℝ) (n K : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (_hK : 1 ≤ K) (_hn : K + 1 ≤ n) :
    deficitMass p n ≤
      (n : ℝ) * (∑ k ∈ Finset.range K, (Nat.choose (n-1) k : ℝ) *
        (p + (1-2*p)*(1-p)^k)^n) +
      (n : ℝ) * (Nat.choose (n-1) K : ℝ) * (p+(1-p)^(K+1))^n := by
  classical
  let S := fun (i : Fin n) k => (Finset.univ.erase i).powersetCard k
  let E := fun (i : Fin n) (T : Finset (Fin n)) (A : BoolMatrix n n) =>
    A i = rowsSum A T
  let D := fun (i : Fin n) (T : Finset (Fin n)) (A : BoolMatrix n n) =>
    ∀ j ∈ T, ∀ c, A j c = 1 → A i c = 1
  let small := fun (i : Fin n) (A : BoolMatrix n n) =>
    ∃ k ∈ Finset.range K, ∃ T ∈ S i k, E i T A
  let large := fun (i : Fin n) (A : BoolMatrix n n) => ∃ T ∈ S i K, D i T A
  have hw := matrixWeight_nonneg (m := n) (n := n) p hp hp1
  have hmem (i : Fin n) (k : ℕ) (T : Finset (Fin n)) (hT : T ∈ S i k) :
      i ∉ T ∧ T.card = k := by
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
    exact ⟨fun hi => (Finset.mem_erase.mp (hsub hi)).1 rfl, hcard⟩
  have hsmall (i : Fin n) :
      (∑ A : BoolMatrix n n, if small i A then matrixWeight p A else 0) ≤
      ∑ k ∈ Finset.range K, (Nat.choose (n-1) k : ℝ) *
        (p+(1-2*p)*(1-p)^k)^n := by
    refine (mass_cover _ hw (small i) (Finset.range K)
      (fun k A => ∃ T ∈ S i k, E i T A) (fun _ h => h)).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    refine (mass_cover _ hw (fun A => ∃ T ∈ S i k, E i T A) (S i k)
      (E i) (fun _ h => h)).trans_eq ?_
    have hterm (T : Finset (Fin n)) (hT : T ∈ S i k) :
        (∑ A : BoolMatrix n n, if E i T A then matrixWeight p A else 0) =
        (p+(1-2*p)*(1-p)^k)^n := by
      obtain ⟨hi, hcard⟩ := hmem i k T hT
      simpa only [E, hcard] using row_eq_rowsSum_mass (n := n) p i T hi
    rw [Finset.sum_congr rfl hterm]
    simp [S]
  have hlarge (i : Fin n) :
      (∑ A : BoolMatrix n n, if large i A then matrixWeight p A else 0) ≤
      (Nat.choose (n-1) K : ℝ) * (p+(1-p)^(K+1))^n := by
    refine (mass_cover _ hw (large i) (S i K) (D i) (fun _ h => h)).trans_eq ?_
    have hterm (T : Finset (Fin n)) (hT : T ∈ S i K) :
        (∑ A : BoolMatrix n n, if D i T A then matrixWeight p A else 0) =
        (p+(1-p)^(K+1))^n := by
      obtain ⟨hi, hcard⟩ := hmem i K T hT
      simpa only [D, hcard] using dominated_rows_mass (n := n) p i T hi
    rw [Finset.sum_congr rfl hterm]
    simp [S]
  have hcover (A : BoolMatrix n n) (hA : boolRowRank A < n) :
      ∃ i ∈ (Finset.univ : Finset (Fin n)), small i A ∨ large i A := by
    obtain ⟨i, hcase⟩ := boolRowRank_lt_witness_dichotomy A K hA
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hsub (T : Finset (Fin n)) (hi : i ∉ T) : T ⊆ Finset.univ.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun hji => hi (hji ▸ hj), Finset.mem_univ j⟩
    rcases hcase with ⟨T, hi, hcard, heq⟩ | ⟨T, hi, hcard, hdom⟩
    · exact Or.inl ⟨T.card, Finset.mem_range.mpr hcard, T,
        Finset.mem_powersetCard.mpr ⟨hsub T hi, rfl⟩, heq⟩
    · exact Or.inr ⟨T, Finset.mem_powersetCard.mpr ⟨hsub T hi, hcard⟩, hdom⟩
  refine (mass_cover _ hw (fun A : BoolMatrix n n => boolRowRank A < n)
    Finset.univ (fun i A => small i A ∨ large i A) hcover).trans ?_
  calc
    _ ≤ ∑ i : Fin n,
        ((∑ k ∈ Finset.range K, (Nat.choose (n-1) k : ℝ) *
          (p+(1-2*p)*(1-p)^k)^n) +
          (Nat.choose (n-1) K : ℝ) * (p+(1-p)^(K+1))^n) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (mass_or _ hw (small i) (large i)).trans (add_le_add (hsmall i) (hlarge i))
    _ = _ := by simp [mul_assoc]

private theorem or_base_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    0 ≤ p + (1-2*p)*(1-p)^k ∧ p + (1-2*p)*(1-p)^k ≤ max p (1-p) := by
  let t := (1-p)^k
  have ht0 : 0 ≤ t := pow_nonneg (by linarith) k
  have ht1 : t ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hs0 : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hnon := add_nonneg (mul_nonneg hp.le hs0) (mul_nonneg (by linarith : 0 ≤ 1-p) ht0)
  have ha := mul_le_mul_of_nonneg_right (le_max_left p (1-p)) hs0
  have hb := mul_le_mul_of_nonneg_right (le_max_right p (1-p)) ht0
  constructor <;> dsimp [t] at * <;> nlinarith

/-- Bounding each small OR cylinder by the larger Bernoulli atom gives a factored union bound. -/
theorem deficitMass_le_twoScale_max (p : ℝ) (n K : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hK : 1 ≤ K) (hn : K + 1 ≤ n) :
    deficitMass p n ≤
      (n : ℝ) * (∑ k ∈ Finset.range K, (Nat.choose (n-1) k : ℝ)) *
        (max p (1-p))^n +
      (n : ℝ) * (Nat.choose (n-1) K : ℝ) * (p+(1-p)^(K+1))^n := by
  refine (deficitMass_le_twoScale p n K hp hp1 hK hn).trans ?_
  have hs : (∑ k ∈ Finset.range K, (Nat.choose (n-1) k : ℝ) *
      (p+(1-2*p)*(1-p)^k)^n) ≤
      ∑ k ∈ Finset.range K, (Nat.choose (n-1) k : ℝ) * (max p (1-p))^n := by
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨h0, hle⟩ := or_base_bounds p hp hp1 k
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle n) (Nat.cast_nonneg _)
  rw [← Finset.sum_mul] at hs
  exact add_le_add (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)) le_rfl

end BilinearComplexity.BooleanRankProbability
