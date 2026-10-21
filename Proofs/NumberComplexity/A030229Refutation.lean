/-
# A030229 — Irwin: the inverse divisibility matrix has entry `-1` at `(a, 1)`

## OEIS source (retrieved with `oeis show A030229`, 2026-10-21)

```
NAME:     Numbers that are the product of an even number of distinct primes.
TERMS:    1,6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,57,58,62,65,69,74,77,
          82,85,86,87,91,93,94,95,106,111,115,118,119,122,123,129,133,134,...
COMMENT:  These are the positive integers k with moebius(k) = 1 (cf. A008683).
          - _N. J. A. Sloane_, May 18 2021
COMMENT (the conjecture):
  Conjecture: For the matrix M(i,j) = 1 if j|i and 0 otherwise,
  Inverse(M)(a,1) = -1, for any a in this sequence.
  - _Benedict W. J. Irwin_, Jul 26 2016
```

No later comment in the entry retracts or corrects the conjecture.

## Status

**False.** This module refutes it.  `M` is the zeta matrix of the divisibility
order, so its inverse is the Möbius matrix `M⁻¹(i,j) = μ(i/j)·[j ∣ i]`; the
`(a,1)` entry is `μ(a)`, which is `+1` (not `-1`) on every term of A030229.
The smallest counterexample is the first term `a = 1` (with the `1 × 1`
matrix `M = [1]`); the first nontrivial one is `a = 6`, where
`Inverse(M)(6,1) = μ(6) = 1`.  The stated value `-1` is correct exactly on the
complementary sequence A030059 (`μ(a) = -1`), so the comment was presumably
intended for A030059; that corrected form is proved below as
`divMatrix_inv_apply_zero_eq_neg_one_of_moebius_eq_neg_one`.

Computational evidence (Sage, exact `40 × 40` inverse over `ℚ`): column 1 of
the inverse equals `μ(a)` for all `a ≤ 40`, and the entry is `+1` at
`a = 1, 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39`.

## Formal conventions

Matrices are `n × n` over `ℚ`, indexed by `Fin n`; the Lean index `i` stands
for the OEIS row/column `i + 1`, so OEIS column `1` is `⟨0, _⟩`.  The inverse is
Mathlib's `Matrix.inv` (`⁻¹`), which is the genuine inverse here because
`det_divMatrix` shows the determinant is `1`.  The entry `(a, 1)` does not
depend on the size `n ≥ a` (`M` is lower triangular), and the conjecture is
stated for every size `n ≥ a`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A030229Refutation

open Matrix

/-! ## Definition layer -/

/-- Membership in A030229: `k` is a product of an even number of distinct
primes, i.e. `k` is squarefree and its number of prime factors (with
multiplicity, equal to the number of distinct primes for squarefree `k`) is
even.  `k = 1` is the empty product; `k = 0` is excluded since it is not
squarefree. -/
def InA030229 (k : ℕ) : Prop :=
  Squarefree k ∧ Even (ArithmeticFunction.cardFactors k)

/-- Sloane's characterization (first comment of A030229): `k` is in A030229
exactly when `μ(k) = 1`. -/
theorem inA030229_iff_moebius_eq_one (k : ℕ) :
    InA030229 k ↔ ArithmeticFunction.moebius k = 1 := by
  by_cases hk : Squarefree k
  · rw [InA030229, ArithmeticFunction.moebius_apply_of_squarefree hk,
      neg_one_pow_eq_one_iff_even (by decide)]
    simp [hk]
  · rw [InA030229, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hk]
    simp [hk]

/-- Irwin's matrix truncated to size `n`: `M(i,j) = 1` if `j ∣ i` and `0`
otherwise, for OEIS indices `1 ≤ i, j ≤ n` (Lean indices shifted by one). -/
def divMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => if (j.val + 1) ∣ (i.val + 1) then 1 else 0

/-! ## Ground truth -/

-- The `3 × 3` divisibility matrix: rows `1, 2, 3`.
example : divMatrix 3 = !![1, 0, 0; 1, 1, 0; 1, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

-- The first terms `1, 6, 10` of A030229 are members.
example : InA030229 1 := ⟨squarefree_one, by simp⟩

example : InA030229 6 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    simp [Nat.primeFactorsList_ofNat]
  · rw [ArithmeticFunction.cardFactors_apply]
    simp [Nat.primeFactorsList_ofNat]

example : InA030229 10 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    simp [Nat.primeFactorsList_ofNat]
  · rw [ArithmeticFunction.cardFactors_apply]
    simp [Nat.primeFactorsList_ofNat]

-- The gaps `2, 3, 4, 5` before the second term are non-members.
example : ¬ InA030229 2 := by
  rintro ⟨-, h⟩
  rw [ArithmeticFunction.cardFactors_apply] at h
  simp at h

example : ¬ InA030229 3 := by
  rintro ⟨-, h⟩
  rw [ArithmeticFunction.cardFactors_apply] at h
  simp [Nat.primeFactorsList_ofNat] at h

example : ¬ InA030229 4 := by
  rintro ⟨h, -⟩
  rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)] at h
  simp [Nat.primeFactorsList_ofNat] at h

example : ¬ InA030229 5 := by
  rintro ⟨-, h⟩
  rw [ArithmeticFunction.cardFactors_apply] at h
  simp [Nat.primeFactorsList_ofNat] at h

/-! ## The conjecture -/

/-- **Irwin's conjecture (A030229, Benedict W. J. Irwin, Jul 26 2016).**

Verbatim: "Conjecture: For the matrix M(i,j) = 1 if j|i and 0 otherwise,
Inverse(M)(a,1) = -1, for any a in this sequence."

Formally: for every size `n` and every OEIS index `a + 1 ≤ n` with `a + 1` in
A030229, the `(a + 1, 1)` entry of the inverse of the `n × n` divisibility
matrix is `-1`. -/
def Conjecture : Prop :=
  ∀ (n : ℕ) (a : Fin n), InA030229 (a.val + 1) → (divMatrix n)⁻¹ a ⟨0, a.pos⟩ = -1

/-! ## Möbius inversion for the divisibility matrix -/

/-- `∑_{d ∣ m} μ(d) = [m = 1]`, cast to `ℚ`. -/
theorem sum_divisors_moebius (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℚ) = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

/-- The divisibility matrix is lower unitriangular, so its determinant is `1`;
in particular `(divMatrix n)⁻¹` is a genuine inverse, not Mathlib's junk
value `0`. -/
theorem det_divMatrix (n : ℕ) : (divMatrix n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [divMatrix]
  · intro i j hij
    have hij' : i < j := hij
    have hndvd : ¬ (j.val + 1) ∣ (i.val + 1) := by
      intro hd
      have hle := Nat.le_of_dvd (Nat.succ_pos _) hd
      have hlt : i.val < j.val := hij'
      omega
    simp [divMatrix, hndvd]

/-- The divisibility matrix sends the Möbius vector `(μ(1), …, μ(n))` to the
first standard basis vector: `∑_{j ∣ i} μ(j) = [i = 1]`. -/
theorem divMatrix_mulVec_moebius (n : ℕ) (i : Fin n) :
    (divMatrix n *ᵥ fun j => (ArithmeticFunction.moebius (j.val + 1) : ℚ)) i =
      if i.val = 0 then 1 else 0 := by
  have hfilter : (Finset.range (n + 1)).filter (· ∣ i.val + 1) = (i.val + 1).divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, -⟩
      have hle := Nat.le_of_dvd (Nat.succ_pos _) hd
      have hi := i.isLt
      exact ⟨by omega, hd⟩
  have hsum : (divMatrix n *ᵥ fun j => (ArithmeticFunction.moebius (j.val + 1) : ℚ)) i =
      ∑ d ∈ Finset.range (n + 1),
        if d ∣ i.val + 1 then (ArithmeticFunction.moebius d : ℚ) else 0 := by
    rw [Finset.sum_range_succ']
    simp only [mulVec, dotProduct, divMatrix, of_apply, ite_mul, one_mul, zero_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k => if k + 1 ∣ i.val + 1 then
      (ArithmeticFunction.moebius (k + 1) : ℚ) else 0)]
    simp
  rw [hsum, ← Finset.sum_filter, hfilter, sum_divisors_moebius]
  simp

/-- **Column 1 of the inverse divisibility matrix is the Möbius function:**
`Inverse(M)(a, 1) = μ(a)` for every size `n ≥ a`. -/
theorem divMatrix_inv_apply_zero (n : ℕ) (a : Fin n) :
    (divMatrix n)⁻¹ a ⟨0, a.pos⟩ = ArithmeticFunction.moebius (a.val + 1) := by
  set M := divMatrix n with hM
  set w : Fin n → ℚ := fun j => (ArithmeticFunction.moebius (j.val + 1) : ℚ) with hw
  have hunit : IsUnit M.det := by
    rw [hM, det_divMatrix]
    exact isUnit_one
  have hMw : M *ᵥ w = Pi.single ⟨0, a.pos⟩ 1 := by
    funext i
    rw [hM, hw, divMatrix_mulVec_moebius, Pi.single_apply]
    simp only [Fin.ext_iff]
  have hcol : (M⁻¹ *ᵥ Pi.single ⟨0, a.pos⟩ 1) a = M⁻¹ a ⟨0, a.pos⟩ := by
    simp
  rw [← hcol, ← hMw, mulVec_mulVec, nonsing_inv_mul M hunit, one_mulVec]

/-! ## The refutation -/

/-- `μ(6) = μ(2) μ(3) = 1`, so `6` is in A030229. -/
theorem moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (m := 2) (n := 3) (by norm_num)
  rw [show (6 : ℕ) = 2 * 3 from rfl, hmul,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  norm_num

/-- The counterexample entry: for the `6 × 6` divisibility matrix,
`Inverse(M)(6, 1) = μ(6) = 1`. -/
theorem divMatrix_six_inv_apply : (divMatrix 6)⁻¹ 5 0 = 1 := by
  have h6 : (5 : Fin 6).val + 1 = 6 := rfl
  rw [show (0 : Fin 6) = ⟨0, (5 : Fin 6).pos⟩ from rfl, divMatrix_inv_apply_zero, h6,
    moebius_six]
  norm_num

-- The premise of the conjecture is satisfiable at the counterexample:
-- `6` is in A030229 and the row index `6` fits in the `6 × 6` matrix.
example : InA030229 ((5 : Fin 6).val + 1) :=
  (inA030229_iff_moebius_eq_one 6).mpr moebius_six

-- The degenerate first term also fails: `a = 1`, `M = [1]`, entry `1`.
example : (divMatrix 1)⁻¹ 0 0 = 1 := by
  rw [show (0 : Fin 1) = ⟨0, (0 : Fin 1).pos⟩ from rfl, divMatrix_inv_apply_zero]
  simp

/-- **Irwin's conjecture is false.**  Counterexample: `a = 6` (the second term
of A030229) with the `6 × 6` divisibility matrix, where
`Inverse(M)(6, 1) = μ(6) = 1 ≠ -1`.  In general `Inverse(M)(a, 1) = μ(a)`
(`divMatrix_inv_apply_zero`), which is `+1` on all of A030229; the author
probably intended the complementary sequence A030059 (`μ(a) = -1`). -/
theorem irwin_conjecture_false : ¬ Conjecture := by
  intro hconj
  have hmem : InA030229 ((5 : Fin 6).val + 1) :=
    (inA030229_iff_moebius_eq_one 6).mpr moebius_six
  have hneg := hconj 6 5 hmem
  rw [show (⟨0, (5 : Fin 6).pos⟩ : Fin 6) = 0 from rfl, divMatrix_six_inv_apply] at hneg
  norm_num at hneg

/-- **Corrected form (A030059).**  If `μ(a) = -1`, i.e. `a` is a product of an
odd number of distinct primes, then `Inverse(M)(a, 1) = -1` for every size
`n ≥ a`. -/
theorem divMatrix_inv_apply_zero_eq_neg_one_of_moebius_eq_neg_one (n : ℕ) (a : Fin n)
    (ha : ArithmeticFunction.moebius (a.val + 1) = -1) :
    (divMatrix n)⁻¹ a ⟨0, a.pos⟩ = -1 := by
  rw [divMatrix_inv_apply_zero, ha]
  norm_num

/-- **What actually holds on A030229.**  If `a` is in A030229 then
`Inverse(M)(a, 1) = 1` for every size `n ≥ a`. -/
theorem divMatrix_inv_apply_zero_eq_one_of_inA030229 (n : ℕ) (a : Fin n)
    (ha : InA030229 (a.val + 1)) :
    (divMatrix n)⁻¹ a ⟨0, a.pos⟩ = 1 := by
  rw [divMatrix_inv_apply_zero, (inA030229_iff_moebius_eq_one _).mp ha]
  norm_num

-- The corrected form is non-vacuous: `μ(2) = -1` with the `2 × 2` matrix.
example : (divMatrix 2)⁻¹ 1 ⟨0, (1 : Fin 2).pos⟩ = -1 :=
  divMatrix_inv_apply_zero_eq_neg_one_of_moebius_eq_neg_one 2 1
    (ArithmeticFunction.moebius_apply_prime Nat.prime_two)

end Candidates.A030229Refutation
