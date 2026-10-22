/-
# Lev–Nagy–Pach: sum-full sets are not zero-sum-free

V. F. Lev, J. Nagy and P. P. Pach, *Sum-full sets are not zero-sum-free*,
arXiv:2101.02586, Theorem 1 and Lemma 1 (Section 2). The theorem solves
Problem 1 of T. Banakh and A. Ravsky, *Zero-sum subsets of decomposable
sets in Abelian groups*, arXiv:1903.03577 (Algebra Discrete Math. 30, 2020),
going back to G. Zaimi, MathOverflow question 16857 (2010).

A finite nonempty subset `A` of an abelian group with `A ⊆ A+A` has a
nonempty zero-sum subset; the two summands may coincide. The proof follows
the paper's matrix induction: an integer matrix with diagonal entries at
least -1, nonnegative off-diagonal entries and row sums 1 has a nonempty
set of rows summing to a nonzero zero-one vector. Lemma 1 is indexed by
a finite set rather than `Fin n`. The second proof for elementary abelian
3-groups (Section 3) is not formalized.
-/
import Mathlib

set_option autoImplicit false

open scoped Pointwise

namespace LevNagyPach

/-! ## Definitions -/

/-- A finset `A` of an additive commutative group is *sum-full* if every element
of `A` is a sum `b + c` of two (not necessarily distinct) elements of `A`;
equivalently `A ⊆ A + A` (see `isSumFull_iff_subset_add`). -/
def IsSumFull {G : Type*} [AddCommGroup G] (A : Finset G) : Prop :=
  ∀ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, b + c = a

/-- A finset `A` of an additive commutative group is *zero-sum-free* if no
nonempty subset of `A` has sum `0`. -/
def IsZeroSumFree {G : Type*} [AddCommGroup G] (A : Finset G) : Prop :=
  ∀ Z ⊆ A, Z.Nonempty → ∑ z ∈ Z, z ≠ 0

/-- The class `𝓜` of Lev–Nagy–Pach, on the rows and columns indexed by a finset
`S`: every diagonal entry is at least `-1`, every off-diagonal entry is
nonnegative, and every row sums to `1`. -/
structure IsLNPMatrix {ι : Type*} (S : Finset ι) (M : ι → ι → ℤ) : Prop where
  diag : ∀ i ∈ S, -1 ≤ M i i
  offDiag : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 0 ≤ M i j
  rowSum : ∀ i ∈ S, ∑ j ∈ S, M i j = 1

/-- A set `I ⊆ S` of rows of `M` whose sum (restricted to the columns in `S`) is
a nonzero zero-one vector. -/
def IsZeroOneRowSystem {ι : Type*} (S : Finset ι) (M : ι → ι → ℤ) (I : Finset ι) :
    Prop :=
  I ⊆ S ∧ (∀ j ∈ S, ∑ i ∈ I, M i j = 0 ∨ ∑ i ∈ I, M i j = 1) ∧
    ∃ j ∈ S, ∑ i ∈ I, M i j = 1

/-! ## Examples -/

/-- Sum-fullness agrees with the pointwise inclusion `A ⊆ A + A`. -/
theorem isSumFull_iff_subset_add {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) : IsSumFull A ↔ A ⊆ A + A := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, c, hc, hbc⟩ := h a ha
    exact Finset.mem_add.mpr ⟨b, hb, c, hc, hbc⟩
  · intro h a ha
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.mem_add.mp (h ha)
    exact ⟨b, hb, c, hc, hbc⟩

example : IsSumFull ({1, 2} : Finset (ZMod 3)) := by
  unfold IsSumFull; decide
example : IsSumFull ({1, -1, 2, -2} : Finset ℤ) := by
  unfold IsSumFull; decide
example : ¬ IsSumFull ({1, 2} : Finset ℤ) := by
  unfold IsSumFull; decide
example : ¬ IsZeroSumFree ({1, -1, 2, -2} : Finset ℤ) := by
  intro h
  exact h {1, -1} (by decide) (by decide) (by decide)

/-- The matrix of the sum-full set `{1, 2} ⊆ ℤ/3` built from `1 = 2 + 2`,
`2 = 1 + 1`, indexed by `Fin 2`: it lies in the class. -/
example : IsLNPMatrix (Finset.univ : Finset (Fin 2)) ![![-1, 2], ![2, -1]] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

example : ¬ IsLNPMatrix (Finset.univ : Finset (Fin 2)) ![![-2, 3], ![0, 1]] := by
  intro h
  exact absurd (h.diag 0 (by decide)) (by decide)

example : IsZeroOneRowSystem (Finset.univ : Finset (Fin 2)) ![![-1, 2], ![2, -1]]
    Finset.univ := by
  refine ⟨Finset.subset_univ _, ?_, ?_⟩ <;> decide

/-! ## Elementary facts about nonnegative integer sums -/

/-- If nonnegative integers indexed by `T` sum to `1`, then exactly one of them
is `1` and all the others vanish. -/
theorem exists_eq_one_of_sum_eq_one {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (f : ι → ℤ) (hnn : ∀ x ∈ T, 0 ≤ f x) (hsum : ∑ x ∈ T, f x = 1) :
    ∃ a ∈ T, f a = 1 ∧ ∀ x ∈ T, x ≠ a → f x = 0 := by
  have hex : ∃ a ∈ T, f a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact absurd hsum (by norm_num)
  obtain ⟨a, haT, hane⟩ := hex
  have hsplit : f a + ∑ x ∈ T.erase a, f x = 1 := by
    rw [Finset.add_sum_erase T f haT]; exact hsum
  have hrest : 0 ≤ ∑ x ∈ T.erase a, f x :=
    Finset.sum_nonneg fun x hx => hnn x (Finset.mem_of_mem_erase hx)
  have hfa_pos : 0 < f a := lt_of_le_of_ne (hnn a haT) (Ne.symm hane)
  have hfa : f a = 1 := by omega
  refine ⟨a, haT, hfa, fun x hxT hxa => ?_⟩
  have hzero : ∑ x ∈ T.erase a, f x = 0 := by omega
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    fun y hy => hnn y (Finset.mem_of_mem_erase hy)).mp hzero
  exact hall x (Finset.mem_erase.mpr ⟨hxa, hxT⟩)

/-- In a matrix of the class, every partial column sum over a set of rows
`I ⊆ S` is at least `-1`: only the diagonal entry can be negative. -/
theorem IsLNPMatrix.neg_one_le_colSum {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {M : ι → ι → ℤ} (hM : IsLNPMatrix S M) {I : Finset ι} (hI : I ⊆ S) {j : ι}
    (hj : j ∈ S) : -1 ≤ ∑ i ∈ I, M i j := by
  by_cases hjI : j ∈ I
  · rw [← Finset.add_sum_erase I _ hjI]
    have hrest : 0 ≤ ∑ i ∈ I.erase j, M i j :=
      Finset.sum_nonneg fun i hi =>
        hM.offDiag i (hI (Finset.mem_of_mem_erase hi)) j hj (Finset.ne_of_mem_erase hi)
    have hd := hM.diag j hj
    omega
  · have hnn : 0 ≤ ∑ i ∈ I, M i j :=
      Finset.sum_nonneg fun i hi =>
        hM.offDiag i (hI hi) j hj (fun hij => hjI (hij ▸ hi))
    omega

/-! ## The cases of the induction for Lemma 1 -/

/-- Case 1 of the proof of Lemma 1: if some diagonal entry `M i i` is
nonnegative, the single row `i` is a nonzero zero-one vector. -/
theorem IsLNPMatrix.isZeroOneRowSystem_singleton {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {M : ι → ι → ℤ} (hM : IsLNPMatrix S M) {i : ι} (hi : i ∈ S)
    (hii : 0 ≤ M i i) : IsZeroOneRowSystem S M {i} := by
  have hnn : ∀ j ∈ S, 0 ≤ M i j := fun j hj => by
    by_cases hij : i = j
    · exact hij ▸ hii
    · exact hM.offDiag i hi j hj hij
  obtain ⟨a, haS, ha1, ha0⟩ := exists_eq_one_of_sum_eq_one S (M i) hnn (hM.rowSum i hi)
  refine ⟨Finset.singleton_subset_iff.mpr hi, fun j hj => ?_, a, haS, ?_⟩
  · rw [Finset.sum_singleton]
    by_cases hja : j = a
    · exact Or.inr (hja ▸ ha1)
    · exact Or.inl (ha0 j hj hja)
  · rw [Finset.sum_singleton]; exact ha1

/-- The sum of all entries of a matrix of the class is `|S|`. -/
theorem IsLNPMatrix.sum_colSum {ι : Type*} {S : Finset ι} {M : ι → ι → ℤ}
    (hM : IsLNPMatrix S M) : ∑ j ∈ S, ∑ i ∈ S, M i j = S.card := by
  rw [Finset.sum_comm, Finset.sum_congr rfl hM.rowSum]
  simp

/-- Case 2 of the proof of Lemma 1: if every column sum is at least `1`, then
all column sums are `1` and the system of all rows works. -/
theorem IsLNPMatrix.isZeroOneRowSystem_univ {ι : Type*} {S : Finset ι}
    {M : ι → ι → ℤ} (hM : IsLNPMatrix S M) (hS : S.Nonempty)
    (hcol : ∀ j ∈ S, 1 ≤ ∑ i ∈ S, M i j) : IsZeroOneRowSystem S M S := by
  have htot : ∑ j ∈ S, (∑ i ∈ S, M i j - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hM.sum_colSum]
    simp
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    fun j hj => sub_nonneg.mpr (hcol j hj)).mp htot
  have hone : ∀ j ∈ S, ∑ i ∈ S, M i j = 1 := fun j hj => by
    have h := hall j hj
    omega
  obtain ⟨j0, hj0⟩ := hS
  exact ⟨subset_rfl, fun j hj => Or.inr (hone j hj), j0, hj0, hone j0 hj0⟩

/-- Case 3a of the proof of Lemma 1: if column `k` vanishes off the diagonal,
deleting row and column `k` stays in the class. -/
theorem IsLNPMatrix.erase {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {M : ι → ι → ℤ} (hM : IsLNPMatrix S M) {k : ι} (hk : k ∈ S)
    (hcolk : ∀ i ∈ S, i ≠ k → M i k = 0) : IsLNPMatrix (S.erase k) M where
  diag i hi := hM.diag i (Finset.mem_of_mem_erase hi)
  offDiag i hi j hj hij :=
    hM.offDiag i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij
  rowSum i hi := by
    have h := hM.rowSum i (Finset.mem_of_mem_erase hi)
    rw [← Finset.add_sum_erase S _ hk,
      hcolk i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi), zero_add] at h
    exact h

/-- Case 3a, lifting step: a solution for `S.erase k` is a solution for `S`
when column `k` vanishes off the diagonal. -/
theorem IsZeroOneRowSystem.of_erase {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {M : ι → ι → ℤ} {k : ι} (hk : k ∈ S) (hcolk : ∀ i ∈ S, i ≠ k → M i k = 0)
    {I : Finset ι} (hI : IsZeroOneRowSystem (S.erase k) M I) :
    IsZeroOneRowSystem S M I := by
  obtain ⟨hIS, hcol, j0, hj0, hj01⟩ := hI
  refine ⟨hIS.trans (Finset.erase_subset k S), fun j hj => ?_,
    j0, Finset.mem_of_mem_erase hj0, hj01⟩
  by_cases hjk : j = k
  · subst hjk
    refine Or.inl (Finset.sum_eq_zero fun i hi => ?_)
    exact hcolk i (Finset.mem_of_mem_erase (hIS hi)) (Finset.ne_of_mem_erase (hIS hi))
  · exact hcol j (Finset.mem_erase.mpr ⟨hjk, hj⟩)

/-- The matrix obtained from `M` by adding column `k₂` into column `k₃` (the
paper's `M'`, before deleting the rows and columns `k₁, k₂`). -/
def addColumn {ι : Type*} [DecidableEq ι] (M : ι → ι → ℤ) (k₂ k₃ : ι) : ι → ι → ℤ :=
  fun i j => M i j + if j = k₃ then M i k₂ else 0

/-- Column sums of `addColumn` away from the target column `k₃`. -/
theorem sum_addColumn_of_ne {ι : Type*} [DecidableEq ι] (M : ι → ι → ℤ) (k₂ k₃ : ι)
    (I : Finset ι) {j : ι} (hj : j ≠ k₃) :
    ∑ i ∈ I, addColumn M k₂ k₃ i j = ∑ i ∈ I, M i j := by
  simp [addColumn, hj]

/-- Column sum of `addColumn` at the target column `k₃`. -/
theorem sum_addColumn_self {ι : Type*} [DecidableEq ι] (M : ι → ι → ℤ) (k₂ k₃ : ι)
    (I : Finset ι) :
    ∑ i ∈ I, addColumn M k₂ k₃ i k₃ = ∑ i ∈ I, M i k₃ + ∑ i ∈ I, M i k₂ := by
  simp [addColumn, Finset.sum_add_distrib]

/-- Case 3b of the proof of Lemma 1, reduction step: if column `k₁` vanishes on
the rows outside `{k₁, k₂}`, then adding column `k₂` into a column
`k₃ ∉ {k₁, k₂}` and deleting rows and columns `k₁, k₂` stays in the class. -/
theorem IsLNPMatrix.addColumn_erase {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {M : ι → ι → ℤ} (hM : IsLNPMatrix S M)
    {k₁ k₂ k₃ : ι} (hk₁ : k₁ ∈ S) (hk₂ : k₂ ∈ S.erase k₁)
    (hk₃ : k₃ ∈ (S.erase k₁).erase k₂)
    (hcol : ∀ i ∈ (S.erase k₁).erase k₂, M i k₁ = 0) :
    IsLNPMatrix ((S.erase k₁).erase k₂) (addColumn M k₂ k₃) where
  diag i hi := by
    have hiS : i ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hik₂ : i ≠ k₂ := Finset.ne_of_mem_erase hi
    have hnn : 0 ≤ M i k₂ := hM.offDiag i hiS k₂ (Finset.mem_of_mem_erase hk₂) hik₂
    have hd := hM.diag i hiS
    simp only [addColumn]
    split_ifs <;> omega
  offDiag i hi j hj hij := by
    have hiS : i ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hjS : j ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)
    have hik₂ : i ≠ k₂ := Finset.ne_of_mem_erase hi
    have hnn : 0 ≤ M i k₂ := hM.offDiag i hiS k₂ (Finset.mem_of_mem_erase hk₂) hik₂
    have hij' := hM.offDiag i hiS j hjS hij
    simp only [addColumn]
    split_ifs <;> omega
  rowSum i hi := by
    have hiS : i ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have h := hM.rowSum i hiS
    rw [← Finset.add_sum_erase S _ hk₁, ← Finset.add_sum_erase _ _ hk₂, hcol i hi] at h
    simp only [addColumn, Finset.sum_add_distrib, Finset.sum_ite_eq', hk₃, if_true]
    omega

/-- Case 3b of the proof of Lemma 1, lifting step: with all diagonal entries
`-1`, column `k₁` supported on `{k₁, k₂}` with `M k₂ k₁ = 1`, and row `k₂`
supported on `{k₁, k₂, k₃}` with `M k₂ k₃ = 1`, a solution `I` for the
contracted matrix gives a solution for `M`: either `I` itself or `I ∪ {k₂}`,
according to the sign of `σ₃ = ∑_{i ∈ I} M i k₃`. -/
theorem IsZeroOneRowSystem.of_addColumn_erase {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {M : ι → ι → ℤ} (hM : IsLNPMatrix S M)
    {k₁ k₂ k₃ : ι} (hk₁ : k₁ ∈ S) (hk₂ : k₂ ∈ S.erase k₁)
    (hk₃ : k₃ ∈ (S.erase k₁).erase k₂)
    (hcol : ∀ i ∈ (S.erase k₁).erase k₂, M i k₁ = 0)
    (hk₂k₁ : M k₂ k₁ = 1) (hk₂k₂ : M k₂ k₂ = -1) (hk₂k₃ : M k₂ k₃ = 1)
    (hrow : ∀ j ∈ (S.erase k₁).erase k₂, j ≠ k₃ → M k₂ j = 0)
    {I : Finset ι} (hI : IsZeroOneRowSystem ((S.erase k₁).erase k₂) (addColumn M k₂ k₃) I) :
    ∃ J, IsZeroOneRowSystem S M J := by
  obtain ⟨hIS', hcolI, j₀, hj₀, hj₀1⟩ := hI
  have hS'S : (S.erase k₁).erase k₂ ⊆ S :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hIS : I ⊆ S := hIS'.trans hS'S
  have hk₂S : k₂ ∈ S := Finset.mem_of_mem_erase hk₂
  have hk₃S : k₃ ∈ S := hS'S hk₃
  have hk₂k₁ne : k₂ ≠ k₁ := Finset.ne_of_mem_erase hk₂
  have hk₃k₂ : k₃ ≠ k₂ := Finset.ne_of_mem_erase hk₃
  have hk₃k₁ : k₃ ≠ k₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk₃)
  have hk₂I : k₂ ∉ I := fun h => Finset.ne_of_mem_erase (hIS' h) rfl
  -- column `k₁` vanishes on `I`
  have hσ₁ : ∑ i ∈ I, M i k₁ = 0 := Finset.sum_eq_zero fun i hi => hcol i (hIS' hi)
  -- `σ₂ ≥ 0` because `k₂ ∉ I`
  have hσ₂ : 0 ≤ ∑ i ∈ I, M i k₂ :=
    Finset.sum_nonneg fun i hi =>
      hM.offDiag i (hIS hi) k₂ hk₂S (fun h => hk₂I (h ▸ hi))
  have hσ₃ : -1 ≤ ∑ i ∈ I, M i k₃ := hM.neg_one_le_colSum hIS hk₃S
  have hσ₂₃ := hcolI k₃ hk₃
  rw [sum_addColumn_self] at hσ₂₃
  -- the columns of `S` outside `{k₁, k₂, k₃}` lie in the contracted index set
  have hmem : ∀ j ∈ S, j ≠ k₁ → j ≠ k₂ → j ∈ (S.erase k₁).erase k₂ := fun j hj h1 h2 =>
    Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hj⟩⟩
  by_cases hsign : 0 ≤ ∑ i ∈ I, M i k₃
  · -- `I` itself works
    refine ⟨I, hIS, fun j hj => ?_, ?_⟩
    · by_cases h1 : j = k₁
      · exact Or.inl (h1 ▸ hσ₁)
      by_cases h2 : j = k₂
      · subst h2; omega
      by_cases h3 : j = k₃
      · subst h3; omega
      have h := hcolI j (hmem j hj h1 h2)
      rwa [sum_addColumn_of_ne M k₂ k₃ I h3] at h
    · by_cases h3 : j₀ = k₃
      · subst h3
        rw [sum_addColumn_self] at hj₀1
        by_cases h2 : ∑ i ∈ I, M i k₂ = 1
        · exact ⟨k₂, hk₂S, h2⟩
        · exact ⟨j₀, hk₃S, by omega⟩
      · rw [sum_addColumn_of_ne M k₂ k₃ I h3] at hj₀1
        exact ⟨j₀, hS'S hj₀, hj₀1⟩
  · -- `σ₃ = -1`, and `insert k₂ I` works
    have hσ₃' : ∑ i ∈ I, M i k₃ = -1 := by omega
    refine ⟨insert k₂ I, Finset.insert_subset hk₂S hIS, fun j hj => ?_,
      k₁, hk₁, ?_⟩
    · rw [Finset.sum_insert hk₂I]
      by_cases h1 : j = k₁
      · subst h1; omega
      by_cases h2 : j = k₂
      · subst h2; omega
      by_cases h3 : j = k₃
      · subst h3; omega
      have h := hcolI j (hmem j hj h1 h2)
      rw [sum_addColumn_of_ne M k₂ k₃ I h3] at h
      rw [hrow j (hmem j hj h1 h2) h3, zero_add]
      exact h
    · rw [Finset.sum_insert hk₂I, hk₂k₁, hσ₁]; rfl

/-! ## Lemma 1 -/

/-- **Lev–Nagy–Pach, Lemma 1** (arXiv:2101.02586).  Let `M` be an integer matrix
on a nonempty finite index set `S` whose diagonal entries are `≥ -1`, whose
off-diagonal entries are `≥ 0`, and whose rows sum to `1`.  Then some system
of rows `I ⊆ S` sums to a nonzero zero-one vector: every column sum
`∑ i ∈ I, M i j` (`j ∈ S`) is `0` or `1`, and at least one is `1`. -/
theorem lemma_1 {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    (M : ι → ι → ℤ) (hM : IsLNPMatrix S M) : ∃ I, IsZeroOneRowSystem S M I := by
  induction S using Finset.strongInduction generalizing M with
  | H S ih =>
  -- Case 1: a nonnegative diagonal entry.
  by_cases h1 : ∃ i ∈ S, 0 ≤ M i i
  · obtain ⟨i, hi, hii⟩ := h1
    exact ⟨{i}, hM.isZeroOneRowSystem_singleton hi hii⟩
  push Not at h1
  have hdiag : ∀ i ∈ S, M i i = -1 := fun i hi => by
    have h := hM.diag i hi
    have h' := h1 i hi
    omega
  -- Case 2: every column sum is at least `1`.
  by_cases h2 : ∀ j ∈ S, 1 ≤ ∑ i ∈ S, M i j
  · exact ⟨S, hM.isZeroOneRowSystem_univ hS h2⟩
  push Not at h2
  obtain ⟨k₁, hk₁, hk₁sum⟩ := h2
  -- the off-diagonal part of column `k₁` sums to `0` or `1`
  have hoffsum : ∑ i ∈ S, M i k₁ = -1 + ∑ i ∈ S.erase k₁, M i k₁ := by
    rw [← Finset.add_sum_erase S _ hk₁, hdiag k₁ hk₁]
  have hoffnn : ∀ i ∈ S.erase k₁, 0 ≤ M i k₁ := fun i hi =>
    hM.offDiag i (Finset.mem_of_mem_erase hi) k₁ hk₁ (Finset.ne_of_mem_erase hi)
  have hoff0 : 0 ≤ ∑ i ∈ S.erase k₁, M i k₁ := Finset.sum_nonneg hoffnn
  by_cases h3 : ∑ i ∈ S.erase k₁, M i k₁ = 0
  · -- Case 3a: column `k₁` vanishes off the diagonal.
    have hcolk : ∀ i ∈ S, i ≠ k₁ → M i k₁ = 0 := fun i hi hik =>
      (Finset.sum_eq_zero_iff_of_nonneg hoffnn).mp h3 i (Finset.mem_erase.mpr ⟨hik, hi⟩)
    have hne : (S.erase k₁).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hrow := hM.rowSum k₁ hk₁
      rw [← Finset.add_sum_erase S _ hk₁, hemp, Finset.sum_empty, hdiag k₁ hk₁] at hrow
      omega
    obtain ⟨I, hI⟩ := ih (S.erase k₁) (Finset.erase_ssubset hk₁) hne M (hM.erase hk₁ hcolk)
    exact ⟨I, hI.of_erase hk₁ hcolk⟩
  · -- Case 3b: column `k₁` has exactly one off-diagonal `1`, in row `k₂`.
    have h3' : ∑ i ∈ S.erase k₁, M i k₁ = 1 := by omega
    obtain ⟨k₂, hk₂, hk₂k₁, hcol'⟩ := exists_eq_one_of_sum_eq_one _ _ hoffnn h3'
    have hk₂S : k₂ ∈ S := Finset.mem_of_mem_erase hk₂
    have hcol : ∀ i ∈ (S.erase k₁).erase k₂, M i k₁ = 0 := fun i hi =>
      hcol' i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
    -- row `k₂` has exactly one further `1`, in a column `k₃ ∉ {k₁, k₂}`
    have hrowsum : ∑ j ∈ (S.erase k₁).erase k₂, M k₂ j = 1 := by
      have h := hM.rowSum k₂ hk₂S
      rw [← Finset.add_sum_erase S _ hk₁, ← Finset.add_sum_erase _ _ hk₂, hk₂k₁,
        hdiag k₂ hk₂S] at h
      omega
    have hrownn : ∀ j ∈ (S.erase k₁).erase k₂, 0 ≤ M k₂ j := fun j hj =>
      hM.offDiag k₂ hk₂S j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))
        (Ne.symm (Finset.ne_of_mem_erase hj))
    obtain ⟨k₃, hk₃, hk₂k₃, hrow⟩ := exists_eq_one_of_sum_eq_one _ _ hrownn hrowsum
    have hssub : (S.erase k₁).erase k₂ ⊂ S :=
      (Finset.erase_ssubset hk₂).trans (Finset.erase_ssubset hk₁)
    obtain ⟨I, hI⟩ := ih _ hssub ⟨k₃, hk₃⟩ (addColumn M k₂ k₃)
      (hM.addColumn_erase hk₁ hk₂ hk₃ hcol)
    exact hI.of_addColumn_erase hM hk₁ hk₂ hk₃ hcol hk₂k₁ (hdiag k₂ hk₂S) hk₂k₃ hrow

/-! ## Theorem 1 -/

/-- The representation matrix of a sum-full set: given a choice `a = b a + c a`,
the row of `a` is `e_{b a} + e_{c a} - e_a`. -/
def reprMatrix {G : Type*} [DecidableEq G] (b c : G → G) : G → G → ℤ :=
  fun a x => (if x = b a then 1 else 0) + (if x = c a then 1 else 0) - if x = a then 1 else 0

/-- The representation matrix of a sum-full set lies in the Lev–Nagy–Pach
class. -/
theorem isLNPMatrix_reprMatrix {G : Type*} [DecidableEq G] (A : Finset G) (b c : G → G)
    (hb : ∀ a ∈ A, b a ∈ A) (hc : ∀ a ∈ A, c a ∈ A) : IsLNPMatrix A (reprMatrix b c) where
  diag a _ := by
    simp only [reprMatrix]
    split_ifs <;> omega
  offDiag a _ x _ hax := by
    simp only [reprMatrix, if_neg (Ne.symm hax)]
    split_ifs <;> omega
  rowSum a ha := by
    simp only [reprMatrix, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (hb a ha), if_pos (hc a ha), if_pos ha]
    norm_num

/-- Every row of the representation matrix is orthogonal to the vector of
elements: `∑ x ∈ A, M a x • x = b a + c a - a = 0`. -/
theorem sum_reprMatrix_smul {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G)
    (b c : G → G) (hb : ∀ a ∈ A, b a ∈ A) (hc : ∀ a ∈ A, c a ∈ A)
    (hbc : ∀ a ∈ A, b a + c a = a) {a : G} (ha : a ∈ A) :
    ∑ x ∈ A, reprMatrix b c a x • x = 0 := by
  simp only [reprMatrix, sub_smul, add_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (hb a ha), if_pos (hc a ha), if_pos ha, hbc a ha, sub_self]

/-- **Lev–Nagy–Pach, Theorem 1** (arXiv:2101.02586), solving Problem 1 of
Banakh–Ravsky (arXiv:1903.03577) and Zaimi's MathOverflow question 16857: if
`A` is a finite nonempty subset of an abelian group in which every element is
a sum of two (not necessarily distinct) elements of `A`, then `A` has a
nonempty subset with sum `0`. -/
theorem exists_zero_sum_of_isSumFull {G : Type*} [AddCommGroup G] (A : Finset G)
    (hA : A.Nonempty) (hfull : IsSumFull A) :
    ∃ Z ⊆ A, Z.Nonempty ∧ ∑ z ∈ Z, z = 0 := by
  classical
  have hrep : ∀ a : G, ∃ b c : G, a ∈ A → b ∈ A ∧ c ∈ A ∧ b + c = a := fun a => by
    by_cases ha : a ∈ A
    · obtain ⟨b, hb, c, hc, hbc⟩ := hfull a ha
      exact ⟨b, c, fun _ => ⟨hb, hc, hbc⟩⟩
    · exact ⟨a, a, fun h => absurd h ha⟩
  choose b c hbc using hrep
  have hb : ∀ a ∈ A, b a ∈ A := fun a ha => (hbc a ha).1
  have hc : ∀ a ∈ A, c a ∈ A := fun a ha => (hbc a ha).2.1
  have hsum : ∀ a ∈ A, b a + c a = a := fun a ha => (hbc a ha).2.2
  set M := reprMatrix b c with hMdef
  obtain ⟨I, hIA, hcol, j₀, hj₀, hj₀1⟩ :=
    lemma_1 A hA M (isLNPMatrix_reprMatrix A b c hb hc)
  set Z := A.filter (fun x => ∑ i ∈ I, M i x = 1) with hZdef
  refine ⟨Z, Finset.filter_subset _ _, ⟨j₀, Finset.mem_filter.mpr ⟨hj₀, hj₀1⟩⟩, ?_⟩
  -- the zero-one column-sum vector is orthogonal to the elements of `A`
  have horth : ∑ x ∈ A, (∑ i ∈ I, M i x) • x = 0 := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i hi => sum_reprMatrix_smul A b c hb hc hsum (hIA hi)
  have hsel : ∀ x ∈ A, (∑ i ∈ I, M i x) • x = if ∑ i ∈ I, M i x = 1 then x else 0 :=
    fun x hx => by
      rcases hcol x hx with h0 | h1
      · rw [h0, zero_smul, if_neg (by norm_num)]
      · rw [h1, one_smul, if_pos rfl]
  rw [Finset.sum_congr rfl hsel, ← Finset.sum_filter] at horth
  exact horth

/-- **Lev–Nagy–Pach, Theorem 1**, in the source's terminology: a finite,
nonempty, sum-full subset (`A ⊆ A + A`) of an abelian group is not
zero-sum-free. -/
theorem theorem_1 {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G)
    (hA : A.Nonempty) (hfull : A ⊆ A + A) : ¬ IsZeroSumFree A := by
  intro hfree
  obtain ⟨Z, hZA, hZ, hZsum⟩ :=
    exists_zero_sum_of_isSumFull A hA ((isSumFull_iff_subset_add A).mpr hfull)
  exact hfree Z hZA hZ hZsum

/-- Non-vacuity of `theorem_1`: the hypotheses hold jointly for `{1, 2} ⊆ ℤ/3`
(`1 = 2 + 2`, `2 = 1 + 1`). -/
example : ({1, 2} : Finset (ZMod 3)).Nonempty ∧
    ({1, 2} : Finset (ZMod 3)) ⊆ {1, 2} + {1, 2} :=
  ⟨⟨1, by decide⟩, (isSumFull_iff_subset_add _).mp (by unfold IsSumFull; decide)⟩

end LevNagyPach
