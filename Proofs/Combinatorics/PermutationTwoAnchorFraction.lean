import Combinatorics.PermutationTwoAnchorKernel

set_option autoImplicit false

namespace PermutationTwoAnchorKernel

open PermutationBoundaryStandardization PermutationEndpointCounting

attribute [local instance] Classical.propDecidable

/-- Distinct prescribed positions and labels leave precisely `(n-2)!` permutations. -/
theorem card_fixedTwo {n : ℕ} (p q a b : Fin n) (hpq : p ≠ q) (hab : a ≠ b) :
    Fintype.card (FixedTwo p q a b) = (n - 2).factorial := by
  classical
  let e : Fin 2 ↪ Fin n := ⟨![p, q], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let f : Fin 2 ↪ Fin n := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let E : {π : Equiv.Perm (Fin n) // ∀ i, π (e i) = f i} ≃ FixedTwo p q a b :=
    Equiv.subtypeEquivRight (fun π => by
      change (∀ i : Fin 2, π (![p, q] i) = ![a, b] i) ↔ _
      rw [Fin.forall_fin_two]
      rfl)
  exact (Fintype.card_congr E).symm.trans (card_completion e f)

/-- Partition an actual two-anchor event by its standardized permutation, retaining
only increasing endpoint ranks, and count each full fiber by its binomial weight. -/
theorem card_standardized_event {n L : ℕ} (e : Fin L ↪ Fin n)
    (i j : Fin L) (a b : Fin n) (hab : a < b) (P : Equiv.Perm (Fin L) → Prop) :
    Fintype.card {π : FixedTwo (e i) (e j) a b // P (standardize e π.val)} =
      (∑ σ : {σ : Equiv.Perm (Fin L) // P σ ∧ σ i < σ j},
        Nat.choose a.val (σ.val i).val *
        Nat.choose (b.val - a.val - 1) ((σ.val j).val - (σ.val i).val - 1) *
        Nat.choose (n - 1 - b.val) (L - 1 - (σ.val j).val)) * (n - L).factorial := by
  classical
  have hRank (π : FixedTwo (e i) (e j) a b) :
      standardize e π.val i < standardize e π.val j := by
    apply (standardize_lt_iff e π.val i j).mpr
    rw [π.property.1, π.property.2]
    exact hab
  let E : (Σ σ : {σ : Equiv.Perm (Fin L) // P σ ∧ σ i < σ j},
      {π : FixedTwo (e i) (e j) a b // standardize e π.val = σ.val}) ≃
      {π : FixedTwo (e i) (e j) a b // P (standardize e π.val)} :=
    { toFun := fun z => ⟨z.2.val, z.2.property.symm ▸ z.1.property.1⟩
      invFun := fun x => ⟨⟨standardize e x.val.val, x.property, hRank x.val⟩,
        ⟨x.val, rfl⟩⟩
      left_inv := by rintro ⟨⟨σ, hσ⟩, ⟨π, hπ⟩⟩; cases hπ; rfl
      right_inv := by intro x; rfl }
  rw [← Fintype.card_congr E, Fintype.card_sigma, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact card_standardizedFiber_binomial e i j a b σ.val hab σ.property.2

example : Fintype.card (FixedTwo (0 : Fin 2) 1 0 1) = 1 := by
  simpa using card_fixedTwo (0 : Fin 2) 1 0 1 (by decide) (by decide)

/-- The descending-factorial denominator of the actual truncated kernel is positive,
including the boundary case `K=2`. -/
theorem kernel_denominator_pos (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n) :
    0 < (n - 2).descFactorial (2 * K - 2 - 2) := by
  exact Nat.descFactorial_pos.mpr (by omega)

/-- The actual endpoint-conditioned truncated avoidance fraction is the guarded
sum of three-binomial weights divided by the positive descending factorial.
The event excludes exactly overlap lengths `2 ≤ k < K`, and the rank guard is explicit. -/
theorem shortAvoid_twoAnchor_fraction (K n : ℕ) (hK : 2 ≤ K)
    (hn : 2 * K - 2 ≤ n) (a b : Fin n) (hab : a < b) :
    (Fintype.card {π : FixedTwo (⟨0, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ a b //
      ShortAvoid K π.val} : ℝ) /
      Fintype.card (FixedTwo (⟨0, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ a b) =
    ((∑ σ : {σ : Equiv.Perm (Fin (2 * K - 2)) // ShortAvoid K σ ∧
        σ ⟨0, by omega⟩ < σ ⟨2 * K - 2 - 1, by omega⟩},
      Nat.choose a.val (σ.val ⟨0, by omega⟩).val *
        Nat.choose (b.val - a.val - 1)
          ((σ.val ⟨2 * K - 2 - 1, by omega⟩).val - (σ.val ⟨0, by omega⟩).val - 1) *
        Nat.choose (n - 1 - b.val)
          (2 * K - 2 - 1 - (σ.val ⟨2 * K - 2 - 1, by omega⟩).val) : ℕ) : ℝ) /
      (n - 2).descFactorial (2 * K - 2 - 2) := by
  classical
  let L := 2 * K - 2
  let i : Fin L := ⟨0, by dsimp [L]; omega⟩
  let j : Fin L := ⟨L - 1, by dsimp [L]; omega⟩
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  let e := boundaryEmbedding K n hK hn
  have hep : e i = p := by
    apply Fin.ext
    change (if 0 < K - 1 then 0 else n - (K - 1) + (0 - (K - 1))) = 0
    rw [if_pos (by omega)]
  have heq : e j = q := by
    apply Fin.ext
    change (if L - 1 < K - 1 then L - 1
      else n - (K - 1) + (L - 1 - (K - 1))) = n - 1
    dsimp [L]
    rw [if_neg (by omega)]
    omega
  let S := ∑ σ : {σ : Equiv.Perm (Fin L) // ShortAvoid K σ ∧ σ i < σ j},
    Nat.choose a.val (σ.val i).val *
      Nat.choose (b.val - a.val - 1) ((σ.val j).val - (σ.val i).val - 1) *
      Nat.choose (n - 1 - b.val) (L - 1 - (σ.val j).val)
  have hc := card_standardized_event e i j a b hab (ShortAvoid K)
  have hevent : Fintype.card {π : FixedTwo (e i) (e j) a b //
      ShortAvoid K (standardize e π.val)} =
      Fintype.card {π : FixedTwo (e i) (e j) a b // ShortAvoid K π.val} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun π => shortAvoid_standardize_iff K n hK hn π.val)
  rw [hevent, hep, heq] at hc
  have hcount : Fintype.card {π : FixedTwo p q a b // ShortAvoid K π.val} =
      S * (n - L).factorial := hc
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = n - 1 at hv
    omega
  change (Fintype.card {π : FixedTwo p q a b // ShortAvoid K π.val} : ℝ) /
    Fintype.card (FixedTwo p q a b) = (S : ℝ) / (n - 2).descFactorial (L - 2)
  rw [hcount, card_fixedTwo p q a b hpq hab.ne, Nat.cast_mul]
  have hsub : n - 2 - (L - 2) = n - L := by dsimp [L]; omega
  have hf := Nat.factorial_mul_descFactorial (n := n - 2) (k := L - 2) (by dsimp [L]; omega)
  rw [hsub] at hf
  have hfR : ((n - L).factorial : ℝ) * (n - 2).descFactorial (L - 2) =
      ((n - 2).factorial : ℝ) := by exact_mod_cast hf
  rw [← hfR, mul_comm ((n - L).factorial : ℝ) _]
  exact mul_div_mul_right _ _ (by exact_mod_cast Nat.factorial_ne_zero (n - L))

example : (boundaryEmbedding 2 3 (by decide) (by decide) ⟨1, by decide⟩).val = 2 := rfl
example : (boundaryEmbedding 3 5 (by decide) (by decide) ⟨2, by decide⟩).val = 3 := rfl

example : Nonempty {π : FixedTwo (0 : Fin 2) 1 0 1 // ShortAvoid 2 π.val} := by
  refine ⟨⟨⟨Equiv.refl _, rfl, rfl⟩, ?_⟩⟩
  intro k hk hkK
  omega

end PermutationTwoAnchorKernel
