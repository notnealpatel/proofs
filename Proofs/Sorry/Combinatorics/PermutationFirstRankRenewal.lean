import Combinatorics.PermutationFixedFirstLimit

set_option autoImplicit false

namespace PermutationFirstRankRenewal

open PermutationOrderCounting PermutationBoundaryStandardization
open PermutationOverlapBound PermutationFixedFirstLimit

attribute [local instance] Classical.propDecidable

/-- The first `k` positions, embedded in a permutation of length `n`. -/
def prefixEmbedding {n k : ℕ} (h : k ≤ n) : Fin k ↪ Fin n :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) hij⟩

example : prefixEmbedding (by decide : 2 ≤ 4) (1 : Fin 2) = (1 : Fin 4) := rfl

/-- The last `k` positions, embedded in a permutation of length `n`. -/
def suffix {n k : ℕ} (h : k ≤ n) : Fin k ↪ Fin n :=
  ⟨fun i => ⟨i.val + (n - k), by omega⟩, by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change i.val + (n - k) = j.val + (n - k) at hv
    omega⟩

example : suffix (by decide : 2 ≤ 4) (0 : Fin 2) = (2 : Fin 4) := rfl

/-- Earliest nontrivial overlap occurs at length `k`. -/
def Earliest {n k : ℕ} (hkn : k < n) (π : Equiv.Perm (Fin n)) : Prop :=
  Overlap hkn π ∧ ∀ ell, 2 ≤ ell → ell < k → ∀ he : ell < n, ¬ Overlap he π

example : Earliest (by decide : 2 < 4) (Equiv.refl _) := by
  constructor
  · intro i j
    change i.val < j.val ↔ i.val + (4 - 2) < j.val + (4 - 2)
    omega
  · intro ell he hl
    omega

/-- Avoiding standardized permutations with prescribed rank at the first position. -/
noncomputable def rowCount (k : ℕ) (hk : 0 < k) (r : Fin k) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin k) // σ ⟨0, hk⟩ = r ∧ FullAvoid σ}

example (r : Fin 2) : rowCount 2 (by decide) r =
    Nat.card (FixedFirst (0 : Fin 2) r) := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun σ => by
    constructor
    · exact And.left
    · intro h
      refine ⟨h, ?_⟩
      intro ell he hl
      omega)

/-- Under length-`k` overlap, shorter actual overlaps are precisely overlaps of the
standardized prefix. This does not assume disjointness of the shorter blocks. -/
theorem overlap_prefix_iff {n k ell : ℕ} (hkn : k < n) (hel : ell < k)
    (π : Equiv.Perm (Fin n)) (ho : Overlap hkn π) :
    Overlap hel (standardize (prefixEmbedding (Nat.le_of_lt hkn)) π) ↔
      Overlap (lt_trans hel hkn) π := by
  have hp (i j : Fin ell) :
      standardize (prefixEmbedding (Nat.le_of_lt hkn)) π ⟨i.val, by omega⟩ <
        standardize (prefixEmbedding (Nat.le_of_lt hkn)) π ⟨j.val, by omega⟩ ↔
      π ⟨i.val, by omega⟩ < π ⟨j.val, by omega⟩ :=
    standardize_lt_iff _ π _ _
  have hs (i j : Fin ell) :
      standardize (prefixEmbedding (Nat.le_of_lt hkn)) π ⟨i.val + (k - ell), by omega⟩ <
        standardize (prefixEmbedding (Nat.le_of_lt hkn)) π ⟨j.val + (k - ell), by omega⟩ ↔
      π ⟨i.val + (n - ell), by omega⟩ < π ⟨j.val + (n - ell), by omega⟩ := by
    rw [standardize_lt_iff]
    have hh := ho (⟨i.val + (k - ell), by omega⟩ : Fin k)
      (⟨j.val + (k - ell), by omega⟩ : Fin k)
    have hadd : k - ell + (n - k) = n - ell := by omega
    change π ⟨i.val + (k - ell), by omega⟩ <
      π ⟨j.val + (k - ell), by omega⟩ ↔ _
    simpa only [Fin.val_mk, Nat.add_assoc, hadd] using hh
  constructor
  · intro H i j
    exact (hp i j).symm.trans ((H i j).trans (hs i j))
  · intro H i j
    exact (hp i j).trans ((H i j).trans (hs i j).symm)

/-- Actual earliest overlap is agreement of the two length-`k` blocks together
with full avoidance of the standardized prefix. -/
theorem earliest_iff {n k : ℕ} (hkn : k < n) (π : Equiv.Perm (Fin n)) :
    Earliest hkn π ↔ Overlap hkn π ∧
      FullAvoid (standardize (prefixEmbedding (Nat.le_of_lt hkn)) π) := by
  constructor
  · rintro ⟨ho, hm⟩
    refine ⟨ho, ?_⟩
    intro ell he hel hs
    exact hm ell he hel (lt_trans hel hkn) ((overlap_prefix_iff hkn hel π ho).mp hs)
  · rintro ⟨ho, ha⟩
    refine ⟨ho, ?_⟩
    intro ell he hel hen hs
    exact ha ell he hel ((overlap_prefix_iff hkn hel π ho).mpr hs)

/-- Disjoint suffix reordering leaves every label of the prefixEmbedding unchanged. -/
theorem prefix_shuffle {n t : ℕ} (a b : Fin t ↪ Fin n)
    (hab : Disjoint (Set.range a) (Set.range b))
    (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin t)) :
    standardize b ((blockPerm a σ).trans π) = standardize b π := by
  apply rank_unique
  intro i j
  simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.trans_apply, blockPerm_apply_right a b hab] using
    (standardize_lt_iff b π i j)

/-- The shuffle bijection restricts to any predicate of the unchanged prefix
pattern. Thus matching the suffix costs exactly `t!`, even after prefixEmbedding selection. -/
theorem card_agreement_prefix_mul_factorial {n t : ℕ} (p m : Fin n)
    (a b : Fin t ↪ Fin n) (hp : p ∉ Set.range a)
    (hab : Disjoint (Set.range a) (Set.range b))
    (P : Equiv.Perm (Fin t) → Prop) :
    Nat.card {π : Agreement p m a b // P (standardize b π.val)} * t.factorial =
      Nat.card {π : FixedFirst p m // P (standardize b π.val)} := by
  classical
  let e := Equiv.ofBijective (shuffleAgreement p m a b hp)
    (shuffleAgreement_bijective p m a b hp hab)
  let er := e.subtypeEquiv (p := fun x => P (standardize b x.1.val))
    (q := fun π => P (standardize b π.val)) (by
      intro x
      change P (standardize b x.1.val) ↔
        P (standardize b ((blockPerm a x.2).trans x.1.val))
      rw [prefix_shuffle a b hab])
  let ep : ({π : Agreement p m a b // P (standardize b π.val)} ×
      Equiv.Perm (Fin t)) ≃
      {x : Agreement p m a b × Equiv.Perm (Fin t) // P (standardize b x.1.val)} :=
    { toFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
      invFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hc := Nat.card_congr (ep.trans er)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_fin] using hc

/-- Exact row-only conditional count identity. The hypergeometric prefixEmbedding count
and its connection to the paid shuffle/earliest bridges remain unpaid here. -/
theorem earliest_fraction {n k : ℕ} (hk : 2 ≤ k) (hn : 2 * k ≤ n) (j : Fin n) :
    (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) j //
      Earliest (by omega : k < n) π.val} : ℝ) /
      Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) j) =
    (∑ r : Fin k, (rowCount k (by omega) r : ℝ) *
      (Nat.choose j.val r.val : ℝ) *
      (Nat.choose (n - 1 - j.val) (k - 1 - r.val) : ℝ)) /
      ((Nat.choose (n - 1) (k - 1) : ℝ) *
        (Nat.factorial (k - 1) : ℝ) * (Nat.factorial k : ℝ)) := by
  sorry

example : 2 ≤ (2 : ℕ) ∧ 2 * 2 ≤ (4 : ℕ) ∧
    Nonempty (FixedFirst (0 : Fin 4) 0) :=
  ⟨by decide, by decide, fixedFirst_nonempty _ _⟩

end PermutationFirstRankRenewal
