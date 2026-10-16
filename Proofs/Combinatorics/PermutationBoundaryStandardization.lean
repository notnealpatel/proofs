import Combinatorics.PermutationOverlapBound

set_option autoImplicit false

namespace PermutationBoundaryStandardization

open PermutationOrderCounting

attribute [local instance] Classical.propDecidable

/-- The ranks of an injective finite list, in increasing label order. -/
noncomputable def rank {n t : ℕ} (f : Fin t ↪ Fin n) : Equiv.Perm (Fin t) := by
  classical
  let ef := Equiv.ofInjective f f.injective
  let of' := Fintype.orderIsoFinOfCardEq (Set.range f)
    ((Fintype.card_congr ef).symm.trans (Fintype.card_fin t))
  exact ef.trans of'.symm.toEquiv

/-- Rank preserves and reflects every strict comparison. -/
theorem rank_lt_iff {n t : ℕ} (f : Fin t ↪ Fin n) (i j : Fin t) :
    rank f i < rank f j ↔ f i < f j := by
  classical
  exact (Fintype.orderIsoFinOfCardEq (Set.range f)
    ((Fintype.card_congr (Equiv.ofInjective f f.injective)).symm.trans
      (Fintype.card_fin t))).symm.lt_iff_lt

/-- A permutation of ranks is uniquely determined by its comparisons. -/
theorem rank_unique {n t : ℕ} (f : Fin t ↪ Fin n) (σ : Equiv.Perm (Fin t))
    (hσ : ∀ i j, σ i < σ j ↔ f i < f j) : rank f = σ := by
  let q := (rank f).symm.trans σ
  have hq : StrictMono q := by
    intro i j hij
    apply (hσ _ _).mpr
    apply (rank_lt_iff f _ _).mp
    simpa using hij
  have he := perm_eq_refl_of_strictMono q hq
  apply Equiv.ext
  intro i
  have hi := congrArg (fun p : Equiv.Perm (Fin t) => p (rank f i)) he
  simpa [q] using hi.symm

example (t : ℕ) : rank (Function.Embedding.refl (Fin t)) = Equiv.refl _ := by
  apply rank_unique
  intro i j
  rfl

/-- Standardize the labels seen at the embedded positions. -/
noncomputable def standardize {n t : ℕ} (e : Fin t ↪ Fin n)
    (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin t) := rank (e.trans π.toEmbedding)

/-- Standardization has exactly the comparisons of the embedded labels. -/
theorem standardize_lt_iff {n t : ℕ} (e : Fin t ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (i j : Fin t) :
    standardize e π i < standardize e π j ↔ π (e i) < π (e j) :=
  rank_lt_iff _ i j

example (t : ℕ) : standardize (Function.Embedding.refl (Fin t)) (Equiv.refl _) =
    Equiv.refl _ := by
  apply rank_unique
  intro i j
  rfl

/-- Position reordering acts on ranks by composition on their input. -/
theorem standardize_reorder {n t : ℕ} (e : Fin t ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (α : Equiv.Perm (Fin t)) :
    standardize e ((blockPerm e α).trans π) = α.trans (standardize e π) := by
  apply rank_unique
  intro i j
  simpa only [Equiv.trans_apply, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, blockPerm_apply] using standardize_lt_iff e π (α i) (α j)

/-- The minimum embedded label has rank zero. -/
theorem standardize_zero {n t : ℕ} [NeZero n] [NeZero t]
    (e : Fin t ↪ Fin n) (he : e 0 = 0) (π : FixedFirst (0 : Fin n) 0) :
    standardize e π.val 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  by_contra h
  have hpos : 0 < standardize e π.val 0 := lt_of_not_ge h
  obtain ⟨i, hi⟩ := (standardize e π.val).surjective 0
  have hlt : standardize e π.val i < standardize e π.val 0 := by simpa [hi] using hpos
  have hc := (standardize_lt_iff e π.val i 0).mp hlt
  rw [he, π.property] at hc
  exact (not_lt_of_ge (Fin.zero_le _)) hc

/-- Standardization restricted to permutations fixing the minimum first label. -/
noncomputable def fixedStandardize {n t : ℕ} [NeZero n] [NeZero t]
    (e : Fin t ↪ Fin n) (he : e 0 = 0) :
    FixedFirst (0 : Fin n) 0 → FixedFirst (0 : Fin t) 0 :=
  fun π => ⟨standardize e π.val, standardize_zero e he π⟩

example {n t : ℕ} [NeZero n] [NeZero t] (e : Fin t ↪ Fin n)
    (he : e 0 = 0) (π : FixedFirst (0 : Fin n) 0) :
    (fixedStandardize e he π).val = standardize e π.val := rfl

/-- Reorder embedded positions while keeping the distinguished minimum fixed. -/
noncomputable def reorderFixed {n t : ℕ} [NeZero n] [NeZero t]
    (e : Fin t ↪ Fin n) (he : e 0 = 0)
    (α : FixedFirst (0 : Fin t) 0) (π : FixedFirst (0 : Fin n) 0) :
    FixedFirst (0 : Fin n) 0 :=
  ⟨(blockPerm e α.val).trans π.val, by
    change π.val (blockPerm e α.val 0) = 0
    have hb : blockPerm e α.val 0 = 0 := by
      calc
        blockPerm e α.val 0 = blockPerm e α.val (e 0) := congrArg _ he.symm
        _ = e (α.val 0) := blockPerm_apply e α.val 0
        _ = 0 := by rw [α.property, he]
    rw [hb, π.property]⟩

example {n t : ℕ} [NeZero n] [NeZero t] (e : Fin t ↪ Fin n)
    (he : e 0 = 0) (α : FixedFirst (0 : Fin t) 0)
    (π : FixedFirst (0 : Fin n) 0) :
    (reorderFixed e he α π).val = (blockPerm e α.val).trans π.val := rfl

/-- Supported position reordering is injective on the fixed-first fiber. -/
theorem reorderFixed_injective {n t : ℕ} [NeZero n] [NeZero t]
    (e : Fin t ↪ Fin n) (he : e 0 = 0) (α : FixedFirst (0 : Fin t) 0) :
    Function.Injective (reorderFixed e he α) := by
  intro π τ h
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hi := congrArg (fun x : FixedFirst (0 : Fin n) 0 =>
    x.val ((blockPerm e α.val).symm i)) h
  simpa only [reorderFixed, Equiv.trans_apply, Equiv.apply_symm_apply] using hi

/-- Any two rank fibers have equal cardinality, by supported position reordering. -/
theorem card_fixedStandardize_fiber {n t : ℕ} [NeZero n] [NeZero t]
    (e : Fin t ↪ Fin n) (he : e 0 = 0)
    (ρ σ : FixedFirst (0 : Fin t) 0) :
    Nat.card {π // fixedStandardize e he π = ρ} =
      Nat.card {π // fixedStandardize e he π = σ} := by
  classical
  suffices hinj : ∀ ρ σ : FixedFirst (0 : Fin t) 0,
      Nat.card {π // fixedStandardize e he π = ρ} ≤
        Nat.card {π // fixedStandardize e he π = σ} from
    le_antisymm (hinj ρ σ) (hinj σ ρ)
  intro ρ σ
  let α : FixedFirst (0 : Fin t) 0 := ⟨σ.val.trans ρ.val.symm, by
    simp only [Equiv.trans_apply, σ.property]
    exact ρ.val.injective (by simpa using ρ.property.symm)⟩
  let g : {π // fixedStandardize e he π = ρ} →
      {π // fixedStandardize e he π = σ} := fun π =>
    ⟨reorderFixed e he α π.val, by
      apply Subtype.ext
      change standardize e ((blockPerm e α.val).trans π.val.val) = σ.val
      rw [standardize_reorder]
      have hr : standardize e π.val.val = ρ.val := congrArg Subtype.val π.property
      rw [hr]
      apply Equiv.ext
      intro i
      exact ρ.val.apply_symm_apply (σ.val i)⟩
  apply Nat.card_le_card_of_injective g
  intro π τ h
  apply Subtype.ext
  exact reorderFixed_injective e he α (congrArg Subtype.val h)

private theorem card_preimage_uniform {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (c : ℕ) (hc : ∀ y, Fintype.card {x // f x = y} = c)
    (P : Y → Prop) :
    Fintype.card {x // P (f x)} = c * Fintype.card {y // P y} := by
  classical
  let E : (Σ y : {y // P y}, {x // f x = y.val}) ≃ {x // P (f x)} :=
    { toFun := fun z => ⟨z.2.val, z.2.property.symm ▸ z.1.property⟩
      invFun := fun x => ⟨⟨f x.val, x.property⟩, ⟨x.val, rfl⟩⟩
      left_inv := by rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩; cases hx; rfl
      right_inv := by intro x; rfl }
  rw [← Fintype.card_congr E, Fintype.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-- Uniform nonempty finite fibers preserve the fraction of every event. -/
theorem fraction_preimage_uniform {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] (f : X → Y)
    (hu : ∀ y z, Fintype.card {x // f x = y} = Fintype.card {x // f x = z})
    (P : Y → Prop) :
    (Fintype.card {x // P (f x)} : ℝ) / Fintype.card X =
      (Fintype.card {y // P y} : ℝ) / Fintype.card Y := by
  classical
  let y₀ := f (Classical.choice (inferInstance : Nonempty X))
  let c := Fintype.card {x // f x = y₀}
  have hc (y : Y) : Fintype.card {x // f x = y} = c := hu y y₀
  have ht : Fintype.card X = c * Fintype.card Y := by
    have h := card_preimage_uniform f c hc (fun _ => True)
    simpa using h
  have hp := card_preimage_uniform f c hc P
  have hx : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty X)).ne'
  have hy : (Fintype.card Y : ℝ) ≠ 0 := by
    have : 0 < Fintype.card Y := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨y₀⟩
    exact_mod_cast this.ne'
  apply (div_eq_div_iff hx hy).mpr
  have ht' : (Fintype.card X : ℝ) = c * Fintype.card Y := by exact_mod_cast ht
  have hp' : (Fintype.card {x // P (f x)} : ℝ) = c * Fintype.card {y // P y} := by
    exact_mod_cast hp
  rw [ht', hp']
  ring

private theorem fraction_preimage_uniform_nat {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] (f : X → Y)
    (hu : ∀ y z, Nat.card {x // f x = y} = Nat.card {x // f x = z})
    (P : Y → Prop) :
    (Nat.card {x // P (f x)} : ℝ) / Nat.card X =
      (Nat.card {y // P y} : ℝ) / Nat.card Y := by
  classical
  have hu' (y z : Y) : Fintype.card {x // f x = y} = Fintype.card {x // f x = z} := by
    simpa only [Nat.card_eq_fintype_card] using hu y z
  simpa only [Nat.card_eq_fintype_card] using fraction_preimage_uniform f hu' P

/-- Embed the first and last `K-1` positions into a permutation of length `n`. -/
def boundaryEmbedding (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n) :
    Fin (2 * K - 2) ↪ Fin n where
  toFun i := ⟨if i.val < K - 1 then i.val else n - (K - 1) + (i.val - (K - 1)), by
    split_ifs <;> omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change (if i.val < K - 1 then i.val else n - (K - 1) + (i.val - (K - 1))) =
      (if j.val < K - 1 then j.val else n - (K - 1) + (j.val - (K - 1))) at hv
    split_ifs at hv <;> omega

example : (boundaryEmbedding 4 9 (by decide) (by decide) ⟨3, by decide⟩).val = 6 := rfl
example : (boundaryEmbedding 4 6 (by decide) (by decide) ⟨0, by decide⟩).val = 0 := rfl

/-- The boundary embedding sends the first position to the first position. -/
theorem boundaryEmbedding_zero (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n)
    [NeZero n] [NeZero (2 * K - 2)] : boundaryEmbedding K n hK hn 0 = 0 := by
  apply Fin.ext
  change (if 0 < K - 1 then 0 else n - (K - 1) + (0 - (K - 1))) = 0
  rw [if_pos (by omega)]

/-- Every position of a short prefix is embedded without change. -/
theorem boundaryEmbedding_prefix (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n)
    {k : ℕ} (hk : k < K) (i : Fin k) :
    boundaryEmbedding K n hK hn ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ := by
  apply Fin.ext
  change (if i.val < K - 1 then i.val else n - (K - 1) + (i.val - (K - 1))) = i.val
  rw [if_pos (by omega)]

/-- Every position of a short suffix is embedded in the corresponding suffix. -/
theorem boundaryEmbedding_suffix (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n)
    {k : ℕ} (hk : k < K) (i : Fin k) :
    boundaryEmbedding K n hK hn ⟨i.val + (2 * K - 2 - k), by omega⟩ =
      ⟨i.val + (n - k), by omega⟩ := by
  apply Fin.ext
  change (if i.val + (2 * K - 2 - k) < K - 1 then i.val + (2 * K - 2 - k)
    else n - (K - 1) + (i.val + (2 * K - 2 - k) - (K - 1))) = i.val + (n - k)
  rw [if_neg (by omega)]
  omega

/-- Actual prefix/suffix overlap is unchanged by boundary standardization. -/
theorem overlap_standardize_iff (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n)
    {k : ℕ} (hk : k < K) (hkn : k < n) (hkL : k < 2 * K - 2)
    (π : Equiv.Perm (Fin n)) :
    PermutationOverlapBound.Overlap hkL (standardize (boundaryEmbedding K n hK hn) π) ↔
      PermutationOverlapBound.Overlap hkn π := by
  let e := boundaryEmbedding K n hK hn
  have hp (i j : Fin k) :
      standardize e π ⟨i.val, by omega⟩ < standardize e π ⟨j.val, by omega⟩ ↔
        π ⟨i.val, by omega⟩ < π ⟨j.val, by omega⟩ := by
    rw [standardize_lt_iff]
    simp only [e, boundaryEmbedding_prefix K n hK hn hk]
  have hs (i j : Fin k) :
      standardize e π ⟨i.val + (2 * K - 2 - k), by omega⟩ <
        standardize e π ⟨j.val + (2 * K - 2 - k), by omega⟩ ↔
      π ⟨i.val + (n - k), by omega⟩ < π ⟨j.val + (n - k), by omega⟩ := by
    rw [standardize_lt_iff]
    simp only [e, boundaryEmbedding_suffix K n hK hn hk]
  constructor
  · intro H i j
    exact (hp i j).symm.trans ((H i j).trans (hs i j))
  · intro H i j
    exact (hp i j).trans ((H i j).trans (hs i j).symm)

/-- Avoid every actual overlap of length at least two and strictly below `K`. -/
def ShortAvoid {n : ℕ} (K : ℕ) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, 2 ≤ k → k < K → ∀ hkn : k < n, ¬ PermutationOverlapBound.Overlap hkn π

example (π : Equiv.Perm (Fin 1)) : ShortAvoid 4 π := by
  intro k hk _ hkn
  omega

/-- Short avoidance is exactly the preimage of short avoidance on the boundary. -/
theorem shortAvoid_standardize_iff (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n)
    (π : Equiv.Perm (Fin n)) :
    ShortAvoid K (standardize (boundaryEmbedding K n hK hn) π) ↔ ShortAvoid K π := by
  constructor
  · intro H k hk hkK hkn ho
    exact H k hk hkK (by omega)
      ((overlap_standardize_iff K n hK hn hkK hkn (by omega) π).mpr ho)
  · intro H k hk hkK hkL ho
    exact H k hk hkK (by omega)
      ((overlap_standardize_iff K n hK hn hkK (by omega) hkL π).mp ho)

/-- For minimum first label, the exact truncated avoidance fraction depends only on
its boundary of length `2*K-2`, not on the full length `n`. -/
theorem shortAvoid_fraction (K n : ℕ) (hK : 2 ≤ K) (hn : 2 * K - 2 ≤ n) :
    (Fintype.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) ⟨0, by omega⟩ //
      ShortAvoid K π.val} : ℝ) /
      Fintype.card (FixedFirst (⟨0, by omega⟩ : Fin n) ⟨0, by omega⟩) =
    (Fintype.card {π : FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩ //
      ShortAvoid K π.val} : ℝ) /
      Fintype.card (FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (2 * K - 2) := ⟨by omega⟩
  have hzN : (⟨0, by omega⟩ : Fin n) = 0 := by apply Fin.ext; simp
  have hzL : (⟨0, by omega⟩ : Fin (2 * K - 2)) = 0 := by apply Fin.ext; simp
  rw [hzN, hzL]
  simp only [← Nat.card_eq_fintype_card]
  letI : Nonempty (FixedFirst (0 : Fin n) 0) := fixedFirst_nonempty 0 0
  let e := boundaryEmbedding K n hK hn
  have he : e 0 = 0 := boundaryEmbedding_zero K n hK hn
  have hu (ρ σ : FixedFirst (0 : Fin (2 * K - 2)) 0) :
      Nat.card {π : FixedFirst (0 : Fin n) 0 // fixedStandardize e he π = ρ} =
      Nat.card {π : FixedFirst (0 : Fin n) 0 // fixedStandardize e he π = σ} :=
    card_fixedStandardize_fiber e he ρ σ
  have h := fraction_preimage_uniform_nat
    (X := FixedFirst (0 : Fin n) 0)
    (Y := FixedFirst (0 : Fin (2 * K - 2)) 0)
    (fixedStandardize e he) hu (fun π => ShortAvoid K π.val)
  have hc : Nat.card {π : FixedFirst (0 : Fin n) 0 //
      ShortAvoid K (fixedStandardize e he π).val} =
      Nat.card {π : FixedFirst (0 : Fin n) 0 // ShortAvoid K π.val} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun π => shortAvoid_standardize_iff K n hK hn π.val)
  rw [hc] at h
  exact h

example : 4 ≤ (4 : ℕ) ∧ 2 * 4 - 2 ≤ (9 : ℕ) ∧
    Nonempty (FixedFirst (0 : Fin 9) 0) ∧ Nonempty (FixedFirst (0 : Fin 6) 0) :=
  ⟨by decide, by decide, fixedFirst_nonempty 0 0, fixedFirst_nonempty 0 0⟩

example : ∃ π : FixedFirst (0 : Fin 6) 0, ShortAvoid 4 π.val := by
  refine ⟨⟨Equiv.swap 1 5, by decide⟩, ?_⟩
  intro k hk hkK hkn
  have hcases : k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl
  · intro ho
    have hp : (Equiv.swap (1 : Fin 6) 5) 0 < (Equiv.swap (1 : Fin 6) 5) 1 := by decide
    have hn : ¬ (Equiv.swap (1 : Fin 6) 5) 4 < (Equiv.swap (1 : Fin 6) 5) 5 := by decide
    exact hn ((ho (0 : Fin 2) 1).mp hp)
  · intro ho
    have hp : (Equiv.swap (1 : Fin 6) 5) 0 < (Equiv.swap (1 : Fin 6) 5) 2 := by decide
    have hn : ¬ (Equiv.swap (1 : Fin 6) 5) 3 < (Equiv.swap (1 : Fin 6) 5) 5 := by decide
    exact hn ((ho (0 : Fin 3) 2).mp hp)

end PermutationBoundaryStandardization
