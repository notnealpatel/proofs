/-
  Erdős Problem #142 — fixed-size sampling supersaturation.

  The exact finite argument here is a double count over fixed-cardinality
  subsets.  It is a three-term, finite-set reparameterization of the random
  sparsening argument in Lemma 2.3 (source label `lem-supsat2`) of
  Balogh--Liu--Sharifzadeh,
  `The number of subsets of integers with no k-term arithmetic progression`
  (arXiv:1605.03172).  That lemma states that `|A| = K r_k(n)` and `K ≥ 2`
  imply `Γ_k(A) ≥ (K / 2)^k r_k(n)`.  Its proof samples a uniformly random
  subset of size `2 r_k(n)`; this file instead sums the deletion bound over
  every subset of a specified size and uses the exact binomial incidence
  count.

  These results are finite supersaturation infrastructure.  They do not prove
  the asymptotic assertion in Erdős Problem #142.
-/

import Erdos.Erdos142.ThreeAPCount

set_option autoImplicit false

open Finset

namespace Erdos142

/-- Restricting the ambient set restricts its canonical three-AP edges by
containment. -/
theorem threeAPEdges_subset_eq_filter {A B : Finset ℕ} (hBA : B ⊆ A) :
    threeAPEdges B = (threeAPEdges A).filter fun e => e ⊆ B := by
  ext e
  simp only [mem_threeAPEdges, mem_filter]
  constructor
  · intro he
    exact ⟨⟨he.1.trans hBA, he.2⟩, he.1⟩
  · intro he
    exact ⟨he.2, he.1.2⟩

/-- Exact fixed-size incidence double count: when `3 ≤ t ≤ A.card`, summing
the canonical three-AP count over all `t`-element subsets of `A` counts each
edge in exactly `choose (A.card - 3) (t - 3)` subsets. -/
theorem sum_threeAPCount_powersetCard (A : Finset ℕ) (t : ℕ) (ht : 3 ≤ t)
    (htA : t ≤ A.card) :
    ∑ B ∈ A.powersetCard t, threeAPCount B =
      threeAPCount A * Nat.choose (A.card - 3) (t - 3) := by
  classical
  calc
    ∑ B ∈ A.powersetCard t, threeAPCount B =
        ∑ B ∈ A.powersetCard t,
          ∑ e ∈ threeAPEdges A, if e ⊆ B then 1 else 0 := by
      apply sum_congr rfl
      intro B hB
      have hBA : B ⊆ A := (mem_powersetCard.mp hB).1
      rw [threeAPCount, threeAPEdges_subset_eq_filter hBA]
      simp
    _ = ∑ e ∈ threeAPEdges A,
          ∑ B ∈ A.powersetCard t, if e ⊆ B then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ e ∈ threeAPEdges A,
          Nat.choose (A.card - 3) (t - 3) := by
      apply sum_congr rfl
      intro e he
      have hedata := mem_threeAPEdges.mp he
      have heA : e ⊆ A := hedata.1
      have hecard : e.card = 3 := hedata.2.1
      calc
        (∑ B ∈ A.powersetCard t, if e ⊆ B then 1 else 0) =
            ((A.powersetCard t).filter fun B => e ⊆ B).card := by simp
        _ = Nat.choose (A.card - e.card) (t - e.card) :=
          card_filter_powersetCard_subset e A t heA (hecard.le.trans ht)
        _ = Nat.choose (A.card - 3) (t - 3) := by rw [hecard]
    _ = threeAPCount A * Nat.choose (A.card - 3) (t - 3) := by
      simp [threeAPCount]

/-- Fixed-size-sampling supersaturation, in subtraction-free form.  When
`3 ≤ t ≤ A.card`, every `t`-element sample of `A` satisfies the deletion bound
`t ≤ addRothNumber U` plus its progression count; summing over all samples
yields this exact binomial inequality. -/
theorem card_mul_choose_le_addRothNumber_mul_choose_add_threeAPCount_mul_choose
    {A U : Finset ℕ} (hAU : A ⊆ U) (t : ℕ) (ht : 3 ≤ t)
    (htA : t ≤ A.card) :
    t * Nat.choose A.card t ≤
      addRothNumber U * Nat.choose A.card t +
        threeAPCount A * Nat.choose (A.card - 3) (t - 3) := by
  have hpoint (B : Finset ℕ) (hB : B ∈ A.powersetCard t) :
      t ≤ addRothNumber U + threeAPCount B := by
    have hBcard : B.card = t := (mem_powersetCard.mp hB).2
    have hBU : B ⊆ U := (mem_powersetCard.mp hB).1.trans hAU
    rw [← hBcard]
    exact card_le_addRothNumber_add_threeAPCount hBU
  have hsum :
      ∑ B ∈ A.powersetCard t, t ≤
        ∑ B ∈ A.powersetCard t, (addRothNumber U + threeAPCount B) := by
    exact sum_le_sum fun B hB => hpoint B hB
  simp only [sum_add_distrib] at hsum
  rw [sum_threeAPCount_powersetCard A t ht htA] at hsum
  simpa only [sum_const, card_powersetCard, Nat.nsmul_eq_mul,
    Nat.mul_comm, Nat.mul_left_comm] using hsum

/-- The natural-subtraction form of fixed-size-sampling supersaturation.  If
`t ≤ addRothNumber U`, its left side is zero; otherwise it is the amount by
which every `t`-sample exceeds the extremal 3-AP-free size. -/
theorem sub_mul_choose_le_threeAPCount_mul_choose
    {A U : Finset ℕ} (hAU : A ⊆ U) (t : ℕ) (ht : 3 ≤ t)
    (htA : t ≤ A.card) :
    (t - addRothNumber U) * Nat.choose A.card t ≤
      threeAPCount A * Nat.choose (A.card - 3) (t - 3) := by
  have hmain :=
    card_mul_choose_le_addRothNumber_mul_choose_add_threeAPCount_mul_choose
      hAU t ht htA
  rw [Nat.sub_mul, Nat.sub_le_iff_le_add']
  exact hmain

/-- Ground-truth satisfiability check at the smallest nontrivial sample:
`A = U = {0,1,2}` and `t = 3` satisfy the hypotheses and both conclusions. -/
example :
    let A : Finset ℕ := {0, 1, 2}
    let U : Finset ℕ := {0, 1, 2}
    let t := 3
    A ⊆ U ∧ 3 ≤ t ∧ t ≤ A.card ∧
      t * Nat.choose A.card t ≤
        addRothNumber U * Nat.choose A.card t +
          threeAPCount A * Nat.choose (A.card - 3) (t - 3) ∧
      (t - addRothNumber U) * Nat.choose A.card t ≤
        threeAPCount A * Nat.choose (A.card - 3) (t - 3) := by
  dsimp only
  have hAU : ({0, 1, 2} : Finset ℕ) ⊆ {0, 1, 2} := Subset.rfl
  exact ⟨hAU, by omega, by decide,
    card_mul_choose_le_addRothNumber_mul_choose_add_threeAPCount_mul_choose
      hAU 3 (by omega) (by decide),
    sub_mul_choose_le_threeAPCount_mul_choose hAU 3 (by omega) (by decide)⟩

#check @threeAPEdges_subset_eq_filter
#check @sum_threeAPCount_powersetCard
#check @card_mul_choose_le_addRothNumber_mul_choose_add_threeAPCount_mul_choose
#check @sub_mul_choose_le_threeAPCount_mul_choose

#print axioms threeAPEdges_subset_eq_filter
#print axioms sum_threeAPCount_powersetCard
#print axioms card_mul_choose_le_addRothNumber_mul_choose_add_threeAPCount_mul_choose
#print axioms sub_mul_choose_le_threeAPCount_mul_choose

end Erdos142
