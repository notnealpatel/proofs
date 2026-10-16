import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

set_option autoImplicit false

namespace PermutationOrderCounting

/-- Two actual position blocks have the same pairwise strict comparisons of labels. -/
def SameOrder {n t : ℕ} (π : Equiv.Perm (Fin n))
    (a b : Fin t ↪ Fin n) : Prop :=
  ∀ i j, π (a i) < π (a j) ↔ π (b i) < π (b j)

example {n t : ℕ} (π : Equiv.Perm (Fin n)) (a b : Fin t ↪ Fin n) :
    SameOrder π a b ↔ ∀ i j, π (a i) < π (a j) ↔ π (b i) < π (b j) := Iff.rfl

/-- The fiber of the prescribed label at the prescribed position. -/
abbrev FixedFirst {n : ℕ} (p m : Fin n) := {π : Equiv.Perm (Fin n) // π p = m}

example : Nonempty (FixedFirst (0 : Fin 1) 0) := ⟨⟨Equiv.refl _, rfl⟩⟩

/-- Every fixed-position fiber is inhabited, including when position and label differ. -/
theorem fixedFirst_nonempty {n : ℕ} (p m : Fin n) : Nonempty (FixedFirst p m) := by
  exact ⟨⟨Equiv.swap p m, Equiv.swap_apply_left p m⟩⟩

/-- Distinct finite lists admit a reordering matching every comparison of a second list. -/
theorem exists_matching_reordering {n t : ℕ} (f g : Fin t ↪ Fin n) :
    ∃ σ : Equiv.Perm (Fin t), ∀ i j, f (σ i) < f (σ j) ↔ g i < g j := by
  classical
  let ef := Equiv.ofInjective f f.injective
  let eg := Equiv.ofInjective g g.injective
  let of' := Fintype.orderIsoFinOfCardEq (Set.range f)
    ((Fintype.card_congr ef).symm.trans (Fintype.card_fin t))
  let og := Fintype.orderIsoFinOfCardEq (Set.range g)
    ((Fintype.card_congr eg).symm.trans (Fintype.card_fin t))
  let σ : Equiv.Perm (Fin t) :=
    ((eg.trans og.symm.toEquiv).trans of'.toEquiv).trans ef.symm
  refine ⟨σ, ?_⟩
  intro i j
  have hf (k : Fin t) : ef (σ k) = of' (og.symm (eg k)) := by simp [σ]
  change (ef (σ i)).val < (ef (σ j)).val ↔ (eg i).val < (eg j).val
  rw [hf i, hf j]
  exact of'.lt_iff_lt.trans og.symm.lt_iff_lt

/-- A strictly increasing permutation of a finite ordinal is the identity. -/
theorem perm_eq_refl_of_strictMono {t : ℕ} (σ : Equiv.Perm (Fin t))
    (hσ : StrictMono σ) : σ = Equiv.refl _ := by
  have hi : StrictMono σ.symm := by
    intro i j hij
    apply lt_of_not_ge
    intro hji
    have hc := hσ.monotone hji
    simp only [Equiv.apply_symm_apply] at hc
    exact (not_le_of_gt hij) hc
  ext i
  apply le_antisymm
  · have hh := hi.id_le (σ i)
    simpa using hh
  · exact hσ.id_le i

/-- A fiber at position zero is equivalent to the permutations of the remaining positions. -/
noncomputable def fixedZeroEquiv (k : ℕ) (m : Fin (k + 1)) :
    FixedFirst (0 : Fin (k + 1)) m ≃ Equiv.Perm (Fin k) where
  toFun π := (Equiv.Perm.decomposeFin π.val).2
  invFun σ := ⟨Equiv.Perm.decomposeFin.symm (m, σ), by simp⟩
  left_inv π := by
    apply Subtype.ext
    have hz : (Equiv.Perm.decomposeFin π.val).1 = m := by
      have hh := Equiv.Perm.decomposeFin_symm_apply_zero
        (Equiv.Perm.decomposeFin π.val).1 (Equiv.Perm.decomposeFin π.val).2
      have hzero : π.val 0 = (Equiv.Perm.decomposeFin π.val).1 := by
        simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using hh
      exact hzero.symm.trans π.property
    have hp : (m, (Equiv.Perm.decomposeFin π.val).2) =
        Equiv.Perm.decomposeFin π.val := Prod.ext hz.symm rfl
    change Equiv.Perm.decomposeFin.symm _ = _
    rw [hp, Equiv.symm_apply_apply]
  right_inv σ := by simp

example (k : ℕ) (m : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) :
    (fixedZeroEquiv k m).symm σ =
      ⟨Equiv.Perm.decomposeFin.symm (m, σ), by simp⟩ := rfl

/-- Swapping the distinguished position with zero identifies the two prescribed-label fibers. -/
def fixedFirstEquivZero (k : ℕ) (p m : Fin (k + 1)) :
    FixedFirst p m ≃ FixedFirst (0 : Fin (k + 1)) m where
  toFun π := ⟨(Equiv.swap 0 p).trans π.val, by simpa using π.property⟩
  invFun π := ⟨(Equiv.swap 0 p).trans π.val, by simpa using π.property⟩
  left_inv π := by apply Subtype.ext; ext i; simp
  right_inv π := by apply Subtype.ext; ext i; simp

example (k : ℕ) (p m : Fin (k + 1)) (π : FixedFirst p m) :
    (fixedFirstEquivZero k p m π).val = (Equiv.swap 0 p).trans π.val := rfl

/-- A prescribed-label fiber has exactly `(n - 1)!` elements; existence of `p` excludes `n = 0`. -/
theorem card_fixedFirst {n : ℕ} (p m : Fin n) :
    Fintype.card (FixedFirst p m) = Nat.factorial (n - 1) := by
  classical
  cases n with
  | zero => exact Fin.elim0 p
  | succ k =>
    rw [Fintype.card_congr ((fixedFirstEquivZero k p m).trans (fixedZeroEquiv k m)),
      Fintype.card_perm, Fintype.card_fin]
    rfl

/-- Extend a permutation of block indices to positions, fixing every position off the block. -/
noncomputable def blockPerm {n t : ℕ} (a : Fin t ↪ Fin n)
    (σ : Equiv.Perm (Fin t)) : Equiv.Perm (Fin n) := by
  classical
  exact σ.extendDomain (Equiv.ofInjective a a.injective)

/-- The supported position permutation acts on the block by the given index permutation. -/
@[simp] theorem blockPerm_apply {n t : ℕ} (a : Fin t ↪ Fin n)
    (σ : Equiv.Perm (Fin t)) (i : Fin t) : blockPerm a σ (a i) = a (σ i) := by
  classical
  exact Equiv.Perm.extendDomain_apply_image σ (Equiv.ofInjective a a.injective) i

/-- Positions outside the block are fixed by the supported permutation. -/
theorem blockPerm_apply_of_notMem {n t : ℕ} (a : Fin t ↪ Fin n)
    (σ : Equiv.Perm (Fin t)) (x : Fin n) (hx : x ∉ Set.range a) :
    blockPerm a σ x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.ofInjective a a.injective) hx

example {n t : ℕ} (a : Fin t ↪ Fin n) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    blockPerm a σ (a i) = a (σ i) := blockPerm_apply a σ i

/-- An index permutation preserving the comparisons of an injective list is identity. -/
theorem perm_eq_refl_of_comparisons {n t : ℕ} (f : Fin t ↪ Fin n)
    (σ : Equiv.Perm (Fin t))
    (h : ∀ i j, f (σ i) < f (σ j) ↔ f i < f j) : σ = Equiv.refl _ := by
  classical
  let ef := Equiv.ofInjective f f.injective
  let of' := Fintype.orderIsoFinOfCardEq (Set.range f)
    ((Fintype.card_congr ef).symm.trans (Fintype.card_fin t))
  let r : Equiv.Perm (Fin t) := ef.trans of'.symm.toEquiv
  have hr (i j : Fin t) : r i < r j ↔ f i < f j := of'.symm.lt_iff_lt
  let q := (r.symm.trans σ).trans r
  have hq : StrictMono q := by
    intro i j hij
    apply (hr _ _).mpr
    apply (h _ _).mpr
    apply (hr _ _).mp
    simpa using hij
  have heq := perm_eq_refl_of_strictMono q hq
  apply Equiv.ext
  intro i
  apply r.injective
  have hi := congrArg (fun e : Equiv.Perm (Fin t) => e (r i)) heq
  simpa [q] using hi

/-- The comparison-matching reordering of two injective lists is unique. -/
theorem matching_reordering_unique {n t : ℕ} (f g : Fin t ↪ Fin n)
    (σ τ : Equiv.Perm (Fin t))
    (hσ : ∀ i j, f (σ i) < f (σ j) ↔ g i < g j)
    (hτ : ∀ i j, f (τ i) < f (τ j) ↔ g i < g j) : σ = τ := by
  have hq : σ.symm.trans τ = Equiv.refl _ :=
    perm_eq_refl_of_comparisons f (σ.symm.trans τ) (by
      intro i j
      exact (hτ (σ.symm i) (σ.symm j)).trans (by simpa using
        (hσ (σ.symm i) (σ.symm j)).symm))
  apply Equiv.ext
  intro i
  have hi := congrArg (fun e : Equiv.Perm (Fin t) => e (σ i)) hq
  simpa using hi.symm

/-- Disjointness makes every position in the second block fixed by first-block reorderings. -/
theorem blockPerm_apply_right {n t : ℕ} (a b : Fin t ↪ Fin n)
    (hab : Disjoint (Set.range a) (Set.range b)) (σ : Equiv.Perm (Fin t))
    (i : Fin t) : blockPerm a σ (b i) = b i := by
  apply blockPerm_apply_of_notMem
  intro hi
  exact Set.disjoint_left.mp hab hi ⟨i, rfl⟩

/-- Undoing a block reordering recovers comparison agreement with the unchanged second block. -/
theorem matching_inverse {n t : ℕ} (π : Equiv.Perm (Fin n)) (a b : Fin t ↪ Fin n)
    (hab : Disjoint (Set.range a) (Set.range b)) (hπ : SameOrder π a b)
    (σ : Equiv.Perm (Fin t)) :
    ∀ i j, ((blockPerm a σ).trans π) (a (σ.symm i)) <
      ((blockPerm a σ).trans π) (a (σ.symm j)) ↔
      ((blockPerm a σ).trans π) (b i) < ((blockPerm a σ).trans π) (b j) := by
  intro i j
  simpa only [Equiv.trans_apply, blockPerm_apply, Equiv.apply_symm_apply,
    blockPerm_apply_right a b hab] using hπ i j

attribute [local instance] Classical.propDecidable

/-- Permutations in the prescribed-label fiber whose two blocks agree in order. -/
abbrev Agreement {n t : ℕ} (p m : Fin n) (a b : Fin t ↪ Fin n) :=
  {π : Equiv.Perm (Fin n) // π p = m ∧ SameOrder π a b}

example {n t : ℕ} (p m : Fin n) (a b : Fin t ↪ Fin n) (π : Agreement p m a b) :
    π.val p = m ∧ SameOrder π.val a b := π.property

/-- Reorder the first block of an agreeing permutation, remaining in the prescribed-label fiber. -/
noncomputable def shuffleAgreement {n t : ℕ} (p m : Fin n) (a b : Fin t ↪ Fin n)
    (hp : p ∉ Set.range a) : Agreement p m a b × Equiv.Perm (Fin t) → FixedFirst p m :=
  fun x => ⟨(blockPerm a x.2).trans x.1.val, by
    simpa only [Equiv.trans_apply, blockPerm_apply_of_notMem a x.2 p hp]
      using x.1.property.1⟩

example {n t : ℕ} (p m : Fin n) (a b : Fin t ↪ Fin n) (hp : p ∉ Set.range a)
    (x : Agreement p m a b × Equiv.Perm (Fin t)) :
    (shuffleAgreement p m a b hp x).val = (blockPerm a x.2).trans x.1.val := rfl

/-- The supported reordering map is bijective: each fiber permutation has a unique agreeing origin. -/
theorem shuffleAgreement_bijective {n t : ℕ} (p m : Fin n) (a b : Fin t ↪ Fin n)
    (hp : p ∉ Set.range a) (hab : Disjoint (Set.range a) (Set.range b)) :
    Function.Bijective (shuffleAgreement p m a b hp) := by
  constructor
  · rintro ⟨π, σ⟩ ⟨ρ, τ⟩ heq
    have he : (blockPerm a σ).trans π.val = (blockPerm a τ).trans ρ.val :=
      congrArg Subtype.val heq
    let γ := (blockPerm a σ).trans π.val
    let f : Fin t ↪ Fin n := a.trans γ.toEmbedding
    let g : Fin t ↪ Fin n := b.trans γ.toEmbedding
    have hσ : ∀ i j, f (σ.symm i) < f (σ.symm j) ↔ g i < g j :=
      matching_inverse π.val a b hab π.property.2 σ
    have hτ : ∀ i j, f (τ.symm i) < f (τ.symm j) ↔ g i < g j := by
      change ∀ i j, γ (a (τ.symm i)) < γ (a (τ.symm j)) ↔ γ (b i) < γ (b j)
      dsimp only [γ]
      rw [he]
      exact matching_inverse ρ.val a b hab ρ.property.2 τ
    have hst : σ = τ := by
      have hi := matching_reordering_unique f g σ.symm τ.symm hσ hτ
      exact congrArg Equiv.symm hi
    subst τ
    have hπρ : π = ρ := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      have hi := congrArg (fun e : Equiv.Perm (Fin n) => e ((blockPerm a σ).symm i)) he
      simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hi
    exact Prod.ext hπρ rfl
  · intro γ
    let f : Fin t ↪ Fin n := a.trans γ.val.toEmbedding
    let g : Fin t ↪ Fin n := b.trans γ.val.toEmbedding
    obtain ⟨σ, hσ⟩ := exists_matching_reordering f g
    let π := (blockPerm a σ).trans γ.val
    have hπ : SameOrder π a b := by
      intro i j
      have hij : γ.val (a (σ i)) < γ.val (a (σ j)) ↔ γ.val (b i) < γ.val (b j) := hσ i j
      simpa only [π, Equiv.trans_apply, blockPerm_apply,
        blockPerm_apply_right a b hab] using hij
    have hfix : π p = m := by
      simpa only [π, Equiv.trans_apply, blockPerm_apply_of_notMem a σ p hp] using γ.property
    refine ⟨(⟨π, hfix, hπ⟩, σ.symm), ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change γ.val (blockPerm a σ (blockPerm a σ.symm x)) = γ.val x
    by_cases hx : x ∈ Set.range a
    · obtain ⟨i, rfl⟩ := hx
      simp
    · rw [blockPerm_apply_of_notMem a σ.symm x hx,
        blockPerm_apply_of_notMem a σ x hx]

/-- Exact counting on the fixed-label fiber: agreement count times `t!` is the fiber size.
Only the reordered block must avoid the distinguished position; thus the stated result also
covers the requested case when both disjoint blocks avoid it. -/
theorem card_agreement_mul_factorial {n t : ℕ} (p m : Fin n) (a b : Fin t ↪ Fin n)
    (hp : p ∉ Set.range a) (hab : Disjoint (Set.range a) (Set.range b)) :
    Fintype.card (Agreement p m a b) * Nat.factorial t = Fintype.card (FixedFirst p m) := by
  have hc := Fintype.card_of_bijective (shuffleAgreement_bijective p m a b hp hab)
  simpa only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] using hc

/-- The fraction of the fixed-label fiber with matching orders is exactly `1 / t!`. -/
theorem agreement_fraction {n t : ℕ} (p m : Fin n) (a b : Fin t ↪ Fin n)
    (hp : p ∉ Set.range a) (hab : Disjoint (Set.range a) (Set.range b)) :
    (Fintype.card (Agreement p m a b) : ℝ) / Fintype.card (FixedFirst p m) =
      1 / (Nat.factorial t : ℝ) := by
  have hT : (Nat.factorial t : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have hF : (Fintype.card (FixedFirst p m) : ℝ) ≠ 0 := by
    rw [card_fixedFirst p m]
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  apply (div_eq_div_iff hF hT).mpr
  have hc : (Fintype.card (Agreement p m a b) : ℝ) * Nat.factorial t =
      Fintype.card (FixedFirst p m) := by
    exact_mod_cast card_agreement_mul_factorial p m a b hp hab
  simpa using hc

example : ∃ a b : Fin 2 ↪ Fin 5,
    (0 : Fin 5) ∉ Set.range a ∧ (0 : Fin 5) ∉ Set.range b ∧
    Disjoint (Set.range a) (Set.range b) ∧ SameOrder (Equiv.refl _) a b := by
  let a : Fin 2 ↪ Fin 5 := ⟨fun i => ⟨i.val + 1, by omega⟩, by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp at hv
    omega⟩
  let b : Fin 2 ↪ Fin 5 := ⟨fun i => ⟨i.val + 3, by omega⟩, by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp at hv
    omega⟩
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = 0 at hv
    omega
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 3 = 0 at hv
    omega
  · apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + 3 = i.val + 1 at hv
    omega
  · intro i j
    change i.val + 1 < j.val + 1 ↔ i.val + 3 < j.val + 3
    omega

end PermutationOrderCounting
