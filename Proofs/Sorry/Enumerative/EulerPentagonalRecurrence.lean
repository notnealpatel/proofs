/-
# Euler's pentagonal recurrence for the partition function

## Classical source

* L. Euler (1750; *De partitione numerorum*, Novi Comm. Acad. Sci. Petrop. 3, 1753):
  the pentagonal number theorem and its corollary for the partition function.
* G. E. Andrews, *The Theory of Partitions* (1976), Chapter 1: the pentagonal number
  theorem (Cor. 1.7) and the recurrence for `p(n)` (Cor. 1.8).
* OEIS A000041, formula field: `a(n) = Sum_{k ≠ 0} (-1)^(k+1) a(n - k(3k-1)/2)`.

## Informal statement (verbatim from the target spec)

For n ≥ 1, Σ_{k∈ℤ} (−1)^k p(n − k(3k−1)/2) = 0 (terms with negative argument omitted),
i.e. p(n) = p(n−1)+p(n−2)−p(n−5)−p(n−7)+…; equivalently (Σ p(n)X^n)·∏(1−X^i) = 1.

Date: 2026-10-21.

## Formalization notes

* `p(n)` is `Fintype.card (Nat.Partition n)` (Mathlib's partitions of `n`).
* `pentagonal : ℤ → ℕ` is Mathlib's `k(3k-1)/2` (`Mathlib.Combinatorics.Enumerative.Pentagonal`),
  and `PowerSeries.pentagonalSeries ℤ = ∏ (1 - X^(i+1))` is Mathlib's pentagonal number theorem
  (`PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`).
* "Terms with negative argument omitted" is the filter `pentagonal k ≤ n`, which also guards the
  natural subtraction `n - pentagonal k`. Every `k` with `pentagonal k ≤ n` lies in `[-n, n]`
  (`abs_le_natCast_pentagonal`), so the finite window `Icc (-n) n` loses no term.
* Mathlib absence: `Nat.Partition.GenFun` lists the unrestricted generating function of `p(n)`
  as a TODO; `leandoc` searches ("partition pentagonal recurrence", "partition generating function
  tprod one sub X pow inverse", "card Partition coefficient powerSeries product") found no
  recurrence or `p(n)` generating-function lemma.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.EulerPentagonalRecurrence

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

/-- Ground truth for the index window at `n = 5`: the surviving indices are `-1, 0, 1, 2`,
with pentagonal numbers `2, 0, 1, 5` (`pentagonal (-2) = 7 > 5`). -/
example : (Icc (-5 : ℤ) 5).filter (fun k ↦ pentagonal k ≤ 5) = {-1, 0, 1, 2} := by decide

/-- Ground truth for Mathlib's `pentagonal`: `1, 2, 5, 7` at `k = 1, -1, 2, -2`. -/
example : pentagonal 1 = 1 ∧ pentagonal (-1) = 2 ∧ pentagonal 2 = 5 ∧ pentagonal (-2) = 7 := by
  decide

/-- Every integer is bounded in absolute value by its (generalized) pentagonal number:
`|k| ≤ k(3k-1)/2`. -/
theorem abs_le_natCast_pentagonal (k : ℤ) : |k| ≤ (pentagonal k : ℤ) := by
  have h2 := two_mul_natCast_pentagonal k
  rcases le_or_gt k 0 with hk | hk
  · rw [abs_of_nonpos hk]
    nlinarith
  · rw [abs_of_pos hk]
    nlinarith

/-- **Euler's generating-function identity.** In `ℤ⟦X⟧`,
`(Σ_n p(n) X^n) · Σ_k (-1)^k X^{k(3k-1)/2} = 1`, i.e. by the pentagonal number theorem
`(Σ_n p(n) X^n) · ∏_{i ≥ 1} (1 - X^i) = 1`. -/
theorem partition_genFun_mul_pentagonalSeries :
    PowerSeries.mk (fun n ↦ (Fintype.card n.Partition : ℤ)) * pentagonalSeries ℤ = 1 := by
  have hP : HasProd (fun i : ℕ ↦ ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j))
      (PowerSeries.mk (fun n ↦ (Fintype.card n.Partition : ℤ))) := by
    have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ ↦ True)
    simpa [Nat.Partition.restricted] using h
  have hQ := PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ
  have hPQ := hP.mul hQ
  have hone : (fun i : ℕ ↦ (∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) * (1 - X ^ (i + 1))) =
      fun _ ↦ 1 := by
    funext i
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  rw [hone] at hPQ
  exact hPQ.unique hasProd_one

/-- **Euler's pentagonal recurrence.** For `n ≥ 1`,
`Σ_{k ∈ ℤ, k(3k-1)/2 ≤ n} (-1)^k p(n - k(3k-1)/2) = 0`; all such `k` lie in `[-n, n]`. -/
theorem partition_pentagonal_recurrence (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ (Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n),
      (-1 : ℤ) ^ k.natAbs * (Fintype.card (n - pentagonal k).Partition : ℤ) = 0 := by
  have hcoeff := congrArg (coeff n) partition_genFun_mul_pentagonalSeries
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff i (pentagonalSeries ℤ) *
      coeff j (PowerSeries.mk (fun n ↦ (Fintype.card n.Partition : ℤ)))), coeff_one,
    if_neg hn.ne'] at hcoeff
  rw [← hcoeff]
  refine Finset.sum_of_injOn pentagonal pentagonal_injective.injOn ?_ ?_ ?_
  · intro k hk
    simp only [coe_filter, Set.mem_ofPred_eq] at hk
    simp only [coe_range, Set.mem_Iio]
    omega
  · intro j hj hjk
    rw [coeff_pentagonalSeries_eq_zero ℤ, zero_mul]
    rintro ⟨k, rfl⟩
    apply hjk
    refine ⟨k, ?_, rfl⟩
    simp only [mem_range] at hj
    have hkn : pentagonal k ≤ n := by omega
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc]
    have habs := abs_le_natCast_pentagonal k
    have hkn' : (pentagonal k : ℤ) ≤ n := by exact_mod_cast hkn
    exact ⟨abs_le.mp (habs.trans hkn'), hkn⟩
  · intro k hk
    rw [coeff_mk, coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]

/-- **Euler's pentagonal recurrence, solved for `p(n)`.** For `n ≥ 1`,
`p(n) = Σ_{k ≠ 0, k(3k-1)/2 ≤ n} (-1)^(k+1) p(n - k(3k-1)/2)
      = p(n-1) + p(n-2) - p(n-5) - p(n-7) + p(n-12) + p(n-15) - ⋯`. -/
theorem card_partition_eq_sum_pentagonal (n : ℕ) (hn : 0 < n) :
    (Fintype.card n.Partition : ℤ) =
      ∑ k ∈ (Icc (-(n : ℤ)) n).filter (fun k ↦ k ≠ 0 ∧ pentagonal k ≤ n),
        (-1 : ℤ) ^ (k.natAbs + 1) * (Fintype.card (n - pentagonal k).Partition : ℤ) := by
  have hrec := partition_pentagonal_recurrence n hn
  have h0 : (0 : ℤ) ∈ (Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n) := by
    simp [pentagonal]
  have hset : (Icc (-(n : ℤ)) n).filter (fun k ↦ k ≠ 0 ∧ pentagonal k ≤ n) =
      ((Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n)).erase 0 := by
    ext k
    simp only [mem_filter, mem_erase]
    tauto
  rw [← Finset.add_sum_erase _ _ h0] at hrec
  have hp0 : pentagonal 0 = 0 := by decide
  rw [hset]
  simp only [Int.natAbs_zero, pow_zero, hp0, Nat.sub_zero, one_mul] at hrec
  simp only [pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib]
  linarith

end Candidates.EulerPentagonalRecurrence
