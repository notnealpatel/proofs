import Combinatorics.PermutationFixedFirstLimit
import Combinatorics.PermutationSixMarginal

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

/-- Sorting a chosen label set and then assigning a pattern recovers exactly that pattern. -/
theorem rank_sorted_pattern {n k : ℕ} (s : Finset (Fin n)) (hs : s.card = k)
    (σ : Equiv.Perm (Fin k)) :
    rank (σ.toEmbedding.trans (s.orderEmbOfFin hs).toEmbedding) = σ := by
  apply rank_unique
  intro i j
  exact (s.orderEmbOfFin hs).lt_iff_lt.symm

/-- For a specified pattern, every sorted label set whose label at the first rank is
`j` gives exactly one injective prefix with first label `j`, and all such prefixes arise. -/
noncomputable def fixedPatternEquiv {n k : ℕ} (z : Fin k) (j : Fin n)
    (σ : Equiv.Perm (Fin k)) :
    {s : {s : Finset (Fin n) // s.card = k} //
      s.val.orderEmbOfFin s.property (σ z) = j} ≃
    {b : Fin k ↪ Fin n // b z = j ∧ rank b = σ} := by
  classical
  let e := Equiv.ofBijective _ (PermutationSixMarginal.sorted_pattern_bijective n k)
  refine Equiv.ofBijective (fun s =>
    (⟨σ.toEmbedding.trans (s.val.val.orderEmbOfFin s.val.property).toEmbedding,
      s.property, rank_sorted_pattern _ _ σ⟩ :
      {b : Fin k ↪ Fin n // b z = j ∧ rank b = σ})) ?_
  constructor
  · intro s t h
    have he : e (s.val, σ) = e (t.val, σ) := congrArg Subtype.val h
    exact Subtype.ext (congrArg Prod.fst (e.injective he))
  · intro b
    obtain ⟨⟨s, τ⟩, h⟩ := e.surjective b.val
    have hr : τ = σ := by
      have hh := congrArg rank h
      change rank (τ.toEmbedding.trans (s.val.orderEmbOfFin s.property).toEmbedding) =
        rank b.val at hh
      rw [rank_sorted_pattern, b.property.2] at hh
      exact hh
    subst τ
    have hz : s.val.orderEmbOfFin s.property (σ z) = j := by
      exact (congrArg (fun f : Fin k ↪ Fin n => f z) h).trans b.property.1
    refine ⟨⟨s, hz⟩, ?_⟩
    exact Subtype.ext h

example {n k : ℕ} (z : Fin k) (j : Fin n) (σ : Equiv.Perm (Fin k))
    (s : {s : Finset (Fin n) // s.card = k})
    (hs : s.val.orderEmbOfFin s.property (σ z) = j) :
    ((fixedPatternEquiv z j σ) ⟨s, hs⟩).val =
      σ.toEmbedding.trans (s.val.orderEmbOfFin s.property).toEmbedding := rfl

example : Nonempty {s : {s : Finset (Fin 4) // s.card = 2} //
    s.val.orderEmbOfFin s.property ((Equiv.refl (Fin 2)) 0) = (0 : Fin 4)} := by
  let s : {s : Finset (Fin 4) // s.card = 2} := ⟨{0, 1}, by decide⟩
  refine ⟨⟨s, ?_⟩⟩
  change s.val.orderEmbOfFin s.property ⟨0, by decide⟩ = 0
  rw [Finset.orderEmbOfFin_zero s.property (by decide)]
  apply le_antisymm _ (Fin.zero_le _)
  exact Finset.min'_le _ _ (by simp [s])

/-- The number of fixed-first injective prefixes of a prescribed pattern is exactly
the number of label sets having the fixed label at that pattern's first rank. -/
theorem card_fixed_pattern {n k : ℕ} (z : Fin k) (j : Fin n)
    (σ : Equiv.Perm (Fin k)) :
    Nat.card {b : Fin k ↪ Fin n // b z = j ∧ rank b = σ} =
      Nat.card {s : {s : Finset (Fin n) // s.card = k} //
        s.val.orderEmbOfFin s.property (σ z) = j} :=
  (Nat.card_congr (fixedPatternEquiv z j σ)).symm

/-- For separated prefix and suffix blocks, counting earliest overlap reduces exactly
to counting avoiding prefix patterns, with a suffix-pattern factor of `k!`. -/
theorem card_earliest_mul_factorial {n k : ℕ} (hk : 2 ≤ k)
    (hn : 2 * k ≤ n) (j : Fin n) :
    Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) j //
      Earliest (by omega : k < n) π.val} * k.factorial =
    Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) j //
      FullAvoid (standardize (prefixEmbedding (by omega : k ≤ n)) π.val)} := by
  let a := suffix (by omega : k ≤ n)
  let b := prefixEmbedding (by omega : k ≤ n)
  let p : Fin n := ⟨0, by omega⟩
  have hp : p ∉ Set.range a := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = 0 at hv
    omega
  have hab : Disjoint (Set.range a) (Set.range b) := by
    rw [Set.disjoint_left]
    rintro x ⟨i, rfl⟩ ⟨l, hl⟩
    have hv := congrArg Fin.val hl
    change l.val = i.val + (n - k) at hv
    have hi := l.isLt
    omega
  have hs (π : Equiv.Perm (Fin n)) :
      SameOrder π a b ↔ Overlap (by omega : k < n) π := by
    constructor
    · intro h i l
      exact (h i l).symm
    · intro h i l
      exact (h i l).symm
  let e : {π : FixedFirst p j // Earliest (by omega : k < n) π.val} ≃
      {π : Agreement p j a b // FullAvoid (standardize b π.val)} :=
    { toFun := fun π =>
        ⟨⟨π.val.val, π.val.property, (hs π.val.val).mpr π.property.1⟩,
          ((earliest_iff (by omega) π.val.val).mp π.property).2⟩
      invFun := fun π =>
        ⟨⟨π.val.val, π.val.property.1⟩,
          (earliest_iff (by omega) π.val.val).mpr
            ⟨(hs π.val.val).mp π.val.property.2, π.property⟩⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  rw [Nat.card_congr e]
  exact card_agreement_prefix_mul_factorial p j a b hp hab FullAvoid

/-- Exact row-only conditional count identity. The numerical count of label sets with
specified first rank, the prefix completion count, and their aggregation remain unpaid. -/
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
