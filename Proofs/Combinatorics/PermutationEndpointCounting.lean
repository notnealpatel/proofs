import Combinatorics.PermutationOrderCounting

set_option autoImplicit false

namespace PermutationEndpointCounting

open PermutationOrderCounting

attribute [local instance] Classical.propDecidable

/-- Actual permutations with two prescribed position/label equations. -/
abbrev FixedTwo {n : ℕ} (p q m l : Fin n) :=
  {π : Equiv.Perm (Fin n) // π p = m ∧ π q = l}

/-- Actual permutations in the two-endpoint fiber whose blocks have the same order. -/
abbrev AgreementTwo {n t : ℕ} (p q m l : Fin n) (a b : Fin t ↪ Fin n) :=
  {π : Equiv.Perm (Fin n) // (π p = m ∧ π q = l) ∧ SameOrder π a b}

example {n : ℕ} (p q m l : Fin n) (π : FixedTwo p q m l) :
    π.val p = m ∧ π.val q = l := π.property

example {n t : ℕ} (p q m l : Fin n) (a b : Fin t ↪ Fin n)
    (π : AgreementTwo p q m l a b) :
    (π.val p = m ∧ π.val q = l) ∧ SameOrder π.val a b := π.property

/-- Distinct positions and distinct labels give an inhabited two-endpoint fiber. -/
theorem fixedTwo_nonempty {n : ℕ} (p q m l : Fin n)
    (hpq : p ≠ q) (hml : m ≠ l) : Nonempty (FixedTwo p q m l) := by
  classical
  let σ : Equiv.Perm (Fin n) := Equiv.swap p m
  have hσp : σ p = m := Equiv.swap_apply_left p m
  have hσq : σ q ≠ m := by
    intro h
    have he : q = p := σ.injective (h.trans hσp.symm)
    exact hpq he.symm
  refine ⟨⟨σ.trans (Equiv.swap (σ q) l), ?_, ?_⟩⟩
  · change Equiv.swap (σ q) l (σ p) = m
    rw [hσp]
    exact Equiv.swap_apply_of_ne_of_ne hσq.symm hml
  · exact Equiv.swap_apply_left (σ q) l

example : Nonempty (FixedTwo (0 : Fin 2) 1 1 0) :=
  fixedTwo_nonempty 0 1 1 0 (by decide) (by decide)

/-- Supported shuffling of the first block preserves both endpoint labels. -/
noncomputable def shuffleAgreementTwo {n t : ℕ} (p q m l : Fin n)
    (a b : Fin t ↪ Fin n) (hp : p ∉ Set.range a) (hq : q ∉ Set.range a) :
    AgreementTwo p q m l a b × Equiv.Perm (Fin t) → FixedTwo p q m l :=
  fun x => ⟨(blockPerm a x.2).trans x.1.val, by
    simpa only [Equiv.trans_apply, blockPerm_apply_of_notMem a x.2 p hp,
      blockPerm_apply_of_notMem a x.2 q hq] using x.1.property.1⟩

example {n t : ℕ} (p q m l : Fin n) (a b : Fin t ↪ Fin n)
    (hp : p ∉ Set.range a) (hq : q ∉ Set.range a)
    (x : AgreementTwo p q m l a b × Equiv.Perm (Fin t)) :
    (shuffleAgreementTwo p q m l a b hp hq x).val =
      (blockPerm a x.2).trans x.1.val := rfl

/-- Restrict the adopted shuffle bijection to the second prescribed-label equation. -/
theorem shuffleAgreementTwo_bijective {n t : ℕ} (p q m l : Fin n)
    (a b : Fin t ↪ Fin n) (hp : p ∉ Set.range a) (hq : q ∉ Set.range a)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    Function.Bijective (shuffleAgreementTwo p q m l a b hp hq) := by
  have hbij := shuffleAgreement_bijective p m a b hp hab
  constructor
  · rintro ⟨π, σ⟩ ⟨ρ, τ⟩ he
    have he' : shuffleAgreement p m a b hp (⟨π.val, π.property.1.1, π.property.2⟩, σ) =
        shuffleAgreement p m a b hp (⟨ρ.val, ρ.property.1.1, ρ.property.2⟩, τ) := by
      apply Subtype.ext
      exact congrArg (fun x : FixedTwo p q m l => x.val) he
    have hi := hbij.1 he'
    have hπρ : π = ρ := Subtype.ext (congrArg (fun x => x.1.val) hi)
    exact Prod.ext hπρ (congrArg (fun x : Agreement p m a b × Equiv.Perm (Fin t) => x.2) hi)
  · intro γ
    obtain ⟨⟨π, σ⟩, he⟩ := hbij.2 ⟨γ.val, γ.property.1⟩
    have hq' : π.val q = l := by
      have hval := congrArg (fun x : FixedFirst p m => x.val q) he
      change π.val (blockPerm a σ q) = γ.val q at hval
      rw [blockPerm_apply_of_notMem a σ q hq] at hval
      exact hval.trans γ.property.2
    refine ⟨(⟨π.val, ⟨π.property.1, hq'⟩, π.property.2⟩, σ), ?_⟩
    apply Subtype.ext
    exact congrArg (fun x : FixedFirst p m => x.val) he

/-- Exact two-endpoint conditional counting; only the reordered block avoids the endpoints. -/
theorem card_agreementTwo_mul_factorial {n t : ℕ} (p q m l : Fin n)
    (a b : Fin t ↪ Fin n) (hp : p ∉ Set.range a) (hq : q ∉ Set.range a)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    Fintype.card (AgreementTwo p q m l a b) * Nat.factorial t =
      Fintype.card (FixedTwo p q m l) := by
  have hc := Fintype.card_of_bijective
    (shuffleAgreementTwo_bijective p q m l a b hp hq hab)
  simpa only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] using hc

/-- On a nonempty distinct-endpoint fiber, the exact real agreement fraction is `1 / t!`. -/
theorem agreementTwo_fraction {n t : ℕ} (p q m l : Fin n)
    (a b : Fin t ↪ Fin n) (hpq : p ≠ q) (hml : m ≠ l)
    (hp : p ∉ Set.range a) (hq : q ∉ Set.range a)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    (Fintype.card (AgreementTwo p q m l a b) : ℝ) /
      Fintype.card (FixedTwo p q m l) = 1 / (Nat.factorial t : ℝ) := by
  letI : Nonempty (FixedTwo p q m l) := fixedTwo_nonempty p q m l hpq hml
  have hF : (Fintype.card (FixedTwo p q m l) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card (FixedTwo p q m l) ≠ 0)
  have hT : (Nat.factorial t : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  apply (div_eq_div_iff hF hT).mpr
  have hc : (Fintype.card (AgreementTwo p q m l a b) : ℝ) * Nat.factorial t =
      Fintype.card (FixedTwo p q m l) := by
    exact_mod_cast card_agreementTwo_mul_factorial p q m l a b hp hq hab
  simpa using hc

example :
    (Fintype.card (AgreementTwo (0 : Fin 2) 1 0 1
      (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 2) Function.Embedding.ofIsEmpty) : ℝ) /
      Fintype.card (FixedTwo (0 : Fin 2) 1 0 1) = 1 := by
  simpa using agreementTwo_fraction (0 : Fin 2) 1 0 1
    (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 2)
    (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 2) (by decide) (by decide)
    (by simp) (by simp) (by simp)

example {n : ℕ} (p q m l : Fin n) (a b : Fin 1 ↪ Fin n)
    (hpq : p ≠ q) (hml : m ≠ l) (hp : p ∉ Set.range a) (hq : q ∉ Set.range a)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    (Fintype.card (AgreementTwo p q m l a b) : ℝ) /
      Fintype.card (FixedTwo p q m l) = 1 := by
  simpa using agreementTwo_fraction p q m l a b hpq hml hp hq hab

example : ∃ a b : Fin 2 ↪ Fin 4,
    (0 : Fin 4) ∉ Set.range a ∧ (1 : Fin 4) ∉ Set.range a ∧
    Disjoint (Set.range a) (Set.range b) ∧
    (0 : Fin 4) ∈ Set.range b ∧ (1 : Fin 4) ∈ Set.range b ∧
    Nonempty (AgreementTwo (0 : Fin 4) 1 0 1 a b) := by
  let a : Fin 2 ↪ Fin 4 := ⟨fun i => ⟨i.val + 2, by omega⟩, by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change i.val + 2 = j.val + 2 at hv
    omega⟩
  let b : Fin 2 ↪ Fin 4 := ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin 4 => x.val) hij)⟩
  refine ⟨a, b, ?_, ?_, ?_, ⟨0, rfl⟩, ⟨1, rfl⟩, ?_⟩
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 2 = 0 at hv
    omega
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 2 = 1 at hv
    omega
  · apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val + 2 at hv
    omega
  · refine ⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, ?_⟩⟩
    intro i j
    change i.val + 2 < j.val + 2 ↔ i.val < j.val
    omega

end PermutationEndpointCounting
