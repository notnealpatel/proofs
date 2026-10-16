import Combinatorics.PermutationOrderCounting
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false

open scoped BigOperators

namespace PermutationSixMarginal

/-- Any two injections of the same finite list differ by a permutation of labels. -/
theorem exists_label_permutation {n k : ℕ} (a b : Fin k ↪ Fin n) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, π (a i) = b i := by
  classical
  let e := (Equiv.ofInjective a a.injective).symm.trans (Equiv.ofInjective b b.injective)
  refine ⟨e.extendSubtype, ?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem e (a i) ⟨i, rfl⟩]
  change ((e ((Equiv.ofInjective a a.injective) i)) : Fin n) = b i
  simp [e]

/-- Relabeling a fixed injective position list does not change its unnormalized marginal. -/
theorem sum_perm_embedding_eq {n k : ℕ} (a b : Fin k ↪ Fin n)
    (f : (Fin k ↪ Fin n) → ℝ) :
    (∑ π : Equiv.Perm (Fin n), f (a.trans π.toEmbedding)) =
      ∑ π : Equiv.Perm (Fin n), f (b.trans π.toEmbedding) := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_label_permutation a b
  let e : Equiv.Perm (Equiv.Perm (Fin n)) :=
    { toFun := fun π => ρ.trans π
      invFun := fun π => ρ.symm.trans π
      left_inv := by intro π; ext i; simp
      right_inv := by intro π; ext i; simp }
  have he (π : Equiv.Perm (Fin n)) :
      a.trans (e π).toEmbedding = b.trans π.toEmbedding := by
    apply Function.Embedding.ext
    intro i
    change π (ρ (a i)) = π (b i)
    exact congrArg π (hρ i)
  calc
    _ = ∑ π : Equiv.Perm (Fin n), f (a.trans (e π).toEmbedding) :=
      (Equiv.sum_comp e _).symm
    _ = _ := by simp_rw [he]

/-- The actual permutation marginal on an injective list is uniform over all injections. -/
theorem uniform_embedding_marginal {n k : ℕ} (a : Fin k ↪ Fin n)
    (f : (Fin k ↪ Fin n) → ℝ) :
    (∑ π : Equiv.Perm (Fin n), f (a.trans π.toEmbedding)) /
        (Nat.factorial n : ℝ) =
      (∑ b : Fin k ↪ Fin n, f b) / (Fintype.card (Fin k ↪ Fin n) : ℝ) := by
  classical
  have hcard : (Fintype.card (Fin k ↪ Fin n) : ℝ) ≠ 0 := by
    letI : Nonempty (Fin k ↪ Fin n) := ⟨a⟩
    exact_mod_cast Fintype.card_ne_zero
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  apply (div_eq_div_iff hfac hcard).mpr
  have he (π : Equiv.Perm (Fin n)) :
      (∑ b : Fin k ↪ Fin n, f (b.trans π.toEmbedding)) = ∑ b : Fin k ↪ Fin n, f b := by
    let e : Equiv.Perm (Fin k ↪ Fin n) :=
      { toFun := fun b => b.trans π.toEmbedding
        invFun := fun b => b.trans π.symm.toEmbedding
        left_inv := by intro b; ext i; simp
        right_inv := by intro b; ext i; simp }
    exact Equiv.sum_comp e f
  calc
    _ = ∑ b : Fin k ↪ Fin n, ∑ π : Equiv.Perm (Fin n),
        f (a.trans π.toEmbedding) := by simp [mul_comm]
    _ = ∑ b : Fin k ↪ Fin n, ∑ π : Equiv.Perm (Fin n),
        f (b.trans π.toEmbedding) := by
      apply Finset.sum_congr rfl
      intro b _
      exact sum_perm_embedding_eq a b f
    _ = ∑ π : Equiv.Perm (Fin n), ∑ b : Fin k ↪ Fin n,
        f (b.trans π.toEmbedding) := Finset.sum_comm
    _ = _ := by simp_rw [he]; simp [Fintype.card_perm, mul_comm]

/-- A subset together with a permutation of its sorted labels parametrizes injections uniquely. -/
theorem sorted_pattern_bijective (n k : ℕ) :
    Function.Bijective (fun x : {s : Finset (Fin n) // s.card = k} × Equiv.Perm (Fin k) =>
      x.2.toEmbedding.trans (x.1.val.orderEmbOfFin x.1.property).toEmbedding) := by
  classical
  constructor
  · rintro ⟨s, σ⟩ ⟨t, τ⟩ h
    have hr : s = t := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← Finset.range_orderEmbOfFin s.val s.property,
        ← Finset.range_orderEmbOfFin t.val t.property]
      have he := congrArg (fun b : Fin k ↪ Fin n => Set.range b) h
      simpa only [Function.Embedding.coe_trans, Equiv.coe_toEmbedding,
        RelEmbedding.coe_toEmbedding, Set.range_comp, Equiv.range_eq_univ,
        Set.image_univ] using he
    subst t
    have hp : σ = τ := by
      apply Equiv.ext
      intro i
      apply (s.val.orderEmbOfFin s.property).injective
      exact congrArg (fun b : Fin k ↪ Fin n => b i) h
    exact Prod.ext rfl hp
  · intro b
    let s : {s : Finset (Fin n) // s.card = k} :=
      ⟨Finset.univ.map b, by simp⟩
    let e : Fin k ≃ s.val := Equiv.ofBijective
      (fun i => ⟨b i, by simp [s]⟩) (by
        constructor
        · intro i j hij
          exact b.injective (congrArg Subtype.val hij)
        · intro x
          have hx : x.val ∈ Finset.univ.map b := x.property
          obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
          exact ⟨i, Subtype.ext hi⟩)
    let σ : Equiv.Perm (Fin k) := e.trans (s.val.orderIsoOfFin s.property).symm.toEquiv
    refine ⟨(s, σ), ?_⟩
    apply Function.Embedding.ext
    intro i
    change (s.val.orderEmbOfFin s.property) (σ i) = b i
    change ((s.val.orderIsoOfFin s.property) (σ i)).val = (e i).val
    exact congrArg Subtype.val ((s.val.orderIsoOfFin s.property).apply_symm_apply (e i))

/-- The injection sum splits into a uniform subset and an independent relative permutation. -/
theorem sum_embedding_eq_sum_sorted_pattern {n k : ℕ}
    (f : (Fin k ↪ Fin n) → ℝ) :
    (∑ b : Fin k ↪ Fin n, f b) =
      ∑ s : {s : Finset (Fin n) // s.card = k}, ∑ σ : Equiv.Perm (Fin k),
        f (σ.toEmbedding.trans (s.val.orderEmbOfFin s.property).toEmbedding) := by
  classical
  let e := Equiv.ofBijective _ (sorted_pattern_bijective n k)
  rw [← Equiv.sum_comp e f, Fintype.sum_prod_type]
  rfl

/-- Uniform permutations induce independent uniform sorted subsets and relative patterns. -/
theorem uniform_sorted_pattern_marginal {n k : ℕ} (a : Fin k ↪ Fin n)
    (f : (Fin k ↪ Fin n) → ℝ) :
    (∑ π : Equiv.Perm (Fin n), f (a.trans π.toEmbedding)) /
        (Nat.factorial n : ℝ) =
      (∑ s : {s : Finset (Fin n) // s.card = k}, ∑ σ : Equiv.Perm (Fin k),
        f (σ.toEmbedding.trans (s.val.orderEmbOfFin s.property).toEmbedding)) /
      ((Fintype.card {s : Finset (Fin n) // s.card = k} : ℝ) * Nat.factorial k) := by
  classical
  have hc := Fintype.card_congr (Equiv.ofBijective _ (sorted_pattern_bijective n k))
  have hc' : Fintype.card (Fin k ↪ Fin n) =
      Fintype.card {s : Finset (Fin n) // s.card = k} * Nat.factorial k := by
    simpa only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] using hc.symm
  rw [uniform_embedding_marginal a f, sum_embedding_eq_sum_sorted_pattern f, hc',
    Nat.cast_mul]

/-- The six boundary positions are the first three followed by the last three, in order. -/
def sixPositions {n : ℕ} (hn : 6 ≤ n) : Fin 6 ↪ Fin n where
  toFun i := ⟨if i.val < 3 then i.val else n - 6 + i.val, by split_ifs <;> omega⟩
  inj' := by
    intro i j hij
    have hv := congrArg Fin.val hij
    dsimp at hv
    split_ifs at hv <;> apply Fin.ext <;> omega

/-- Evaluation of the six boundary positions as natural numbers. -/
theorem sixPositions_apply {n : ℕ} (hn : 6 ≤ n) (i : Fin 6) :
    (sixPositions hn i).val = if i.val < 3 then i.val else n - 6 + i.val := rfl

/-- The boundary-position embedding agrees with the intended six indices. -/
theorem sixPositions_values {n : ℕ} (hn : 6 ≤ n) :
    (sixPositions hn 0).val = 0 ∧ (sixPositions hn 1).val = 1 ∧
    (sixPositions hn 2).val = 2 ∧ (sixPositions hn 3).val = n - 3 ∧
    (sixPositions hn 4).val = n - 2 ∧ (sixPositions hn 5).val = n - 1 := by
  simp only [sixPositions_apply]
  norm_num
  omega

example : sixPositions (n := 6) (by omega) = Function.Embedding.refl _ := by
  apply Function.Embedding.ext
  intro i
  apply Fin.ext
  simp [sixPositions]

/-- The actual first-three/last-three labels have the uniform subset and independent S6 law. -/
theorem six_boundary_uniform {n : ℕ} (hn : 6 ≤ n)
    (f : (Fin 6 → Fin n) → ℝ) :
    (∑ π : Equiv.Perm (Fin n), f (fun i => π (sixPositions hn i))) /
        (Nat.factorial n : ℝ) =
      (∑ s : {s : Finset (Fin n) // s.card = 6}, ∑ σ : Equiv.Perm (Fin 6),
        f (fun i => s.val.orderEmbOfFin s.property (σ i))) /
      ((Fintype.card {s : Finset (Fin n) // s.card = 6} : ℝ) * 720) := by
  simpa only [show Nat.factorial 6 = 720 from rfl, Nat.cast_ofNat,
    Function.Embedding.coe_trans, Equiv.coe_toEmbedding, RelEmbedding.coe_toEmbedding,
    Function.comp_def] using
    uniform_sorted_pattern_marginal (sixPositions hn) (fun b => f b)

example : Nonempty (Fin 6 ↪ Fin 6) := ⟨Function.Embedding.refl _⟩

end PermutationSixMarginal
