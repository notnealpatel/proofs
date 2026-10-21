/-
# A005329 — Layman: A005329 is the inverse binomial transform of A075272

## OEIS source (retrieved with `oeis show A005329`, `A075271`, `A075272`, 2026-10-21)

```
A005329  NAME:  a(n) = Product_{i=1..n} (2^i - 1). Also called 2-factorial numbers.
         TERMS: 1,1,3,21,315,9765,615195,78129765,19923090075,...
         COMMENT (the conjecture):
           Conjecture: this sequence is the inverse binomial transform of A075272
           or, equivalently, the inverse binomial transform of the BinomialMean
           transform of A075271. - _John W. Layman_, Sep 12 2002
A075271  NAME:  a(0) = 1 and, for n >= 1, (BM)a(n) = 2*a(n-1), where BM is the
                BinomialMean transform.
         TERMS: 1,3,17,211,5793,339491,41326513,...
         COMMENT: The BinomialMean transform BM is defined by
           (BM)a(n) = (M^n)a(0) where (M)a(n) is the mean (a(n) + a(n+1))/2, or,
           alternatively, by (BM)a(n) = (Sum_{k=0..n} binomial(n,k)*a(k))/(2^n).
A075272  NAME:  BinomialMean (BM) transform of A075271, which see for the
                definition of (BM).
         TERMS: 1,2,6,34,422,11586,678982,82653026,...
         COMMENT: Binomial transform of A005329. - _Vladimir Reshetnikov_, Nov 20 2015
```

## Status

Triage status: open (no proof in the entry; the A075272 comment asserts the
binomial-transform form without proof).  Checked numerically for `n ≤ 60`
(2026-10-21).  This module proves it: with `d = A005329` and `e` its binomial
transform, the relation `d(j) + d(j+1) = 2^(j+1) d(j)` gives
`Σ_k C(n,k) e(k+1) = 2^(n+1) e(n)`, which is exactly the recursion making
`e(m+1)/2` satisfy the defining relation of A075271; uniqueness of that
recursion closes the argument.  (Equivalently, on exponential generating
functions: `D + D' = 2 D(2x)`.)
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A005329LaymanBinomialTransform

open Finset

/-! ## Definitions -/

/-- **A005329**: `a(n) = Product_{i=1..n} (2^i - 1)`.  The natural subtraction
`2^i - 1` never truncates since `1 ≤ 2^i` (see `a005329_succ_add`). -/
def a005329 (n : ℕ) : ℕ := ∏ i ∈ Icc 1 n, (2 ^ i - 1)

/-- **A075271**, by the recursion solved out of its definition: `a(0) = 1` and
`(Sum_{k=0..n} C(n,k) a(k)) / 2^n = 2 a(n-1)` for `n ≥ 1`, i.e.
`a(n+1) = 2^(n+2) a(n) - Sum_{k=0..n} C(n+1,k) a(k)`.  The equivalence with the
entry's definition is `a075271_binomialMean_succ` together with
`eq_a075271_of_binomialMean`. -/
def a075271 : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 ^ (n + 2) * a075271 n - ∑ k : Fin (n + 1), ((n + 1).choose k : ℤ) * a075271 k

/-- The **BinomialMean transform** of the OEIS entries A075271/A075272:
`(BM)a(n) = (Sum_{k=0..n} binomial(n,k) a(k)) / 2^n`, taken in `ℚ` so that the
division is exact. -/
noncomputable def binomialMean (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (∑ k ∈ range (n + 1), (n.choose k : ℚ) * a k) / 2 ^ n

/-- **A075272**: the BinomialMean transform of A075271. -/
noncomputable def a075272 (n : ℕ) : ℚ := binomialMean (fun k => (a075271 k : ℚ)) n

/-- The **binomial transform** `(Ba)(n) = Sum_{k=0..n} C(n,k) a(k)` over `ℤ`. -/
def binomialTransform (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℤ) * a k

/-! ## Ground truth against the DATA lines -/

example : (List.range 6).map a005329 = [1, 1, 3, 21, 315, 9765] := by decide

/-- `A075271(0) = 1`. -/
theorem a075271_zero : a075271 0 = 1 := by rw [a075271]

/-- `A075271(1) = 3`. -/
theorem a075271_one : a075271 1 = 3 := by
  rw [a075271.eq_2]; simp [a075271_zero]

/-- `A075271(2) = 17`. -/
theorem a075271_two : a075271 2 = 17 := by
  rw [a075271.eq_2]; simp [Fin.sum_univ_succ, a075271_zero, a075271_one]

/-- `A075271(3) = 211`. -/
theorem a075271_three : a075271 3 = 211 := by
  rw [a075271.eq_2]; simp [Fin.sum_univ_succ, a075271_zero, a075271_one, a075271_two, Nat.choose]

example : a075271 4 = 5793 := by
  rw [a075271.eq_2]
  simp [Fin.sum_univ_succ, a075271_zero, a075271_one, a075271_two, a075271_three, Nat.choose]

example : a075272 0 = 1 ∧ a075272 1 = 2 ∧ a075272 2 = 6 ∧ a075272 3 = 34 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [a075272, binomialMean, sum_range_succ, Nat.choose, a075271_zero, a075271_one,
      a075271_two, a075271_three]

/-! ## Binomial-transform calculus -/

/-- Pascal step for the binomial transform:
`(Ba)(n+1) = (Ba)(n) + (B(a ∘ succ))(n)`. -/
theorem binomialTransform_succ (a : ℕ → ℤ) (n : ℕ) :
    binomialTransform a (n + 1) =
      binomialTransform a n + binomialTransform (fun k => a (k + 1)) n := by
  unfold binomialTransform
  rw [sum_range_succ' _ (n + 1)]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib]
  rw [sum_range_succ (fun k => ((n.choose (k + 1) : ℕ) : ℤ) * a (k + 1)) n,
    sum_range_succ' (fun k => ((n.choose k : ℕ) : ℤ) * a k) n]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
    Nat.cast_one]
  ring

/-- Weighted subset-of-subset count: for `j ≤ n`,
`Sum_k C(n,k) C(k,j) g(k) = C(n,j) Sum_{i ≤ n-j} C(n-j,i) g(j+i)`. -/
theorem sum_choose_mul_choose_mul (g : ℕ → ℤ) (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (k.choose j : ℤ) * g k =
      (n.choose j : ℤ) * ∑ i ∈ range (n - j + 1), ((n - j).choose i : ℤ) * g (j + i) := by
  rw [← sum_range_add_sum_Ico _ (show j ≤ n + 1 by omega)]
  have hlow : ∑ k ∈ range j, (n.choose k : ℤ) * (k.choose j : ℤ) * g k = 0 := by
    refine sum_eq_zero fun k hk => ?_
    rw [Nat.choose_eq_zero_of_lt (n := k) (k := j) (mem_range.mp hk)]
    simp
  rw [hlow, zero_add, sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have hmul : n.choose (j + i) * (j + i).choose j = n.choose j * (n - j).choose i := by
    rw [Nat.choose_mul (by omega : j ≤ j + i), Nat.add_sub_cancel_left]
  have hmulZ : (n.choose (j + i) : ℤ) * ((j + i).choose j : ℤ) =
      (n.choose j : ℤ) * ((n - j).choose i : ℤ) := by exact_mod_cast hmul
  rw [hmulZ, mul_assoc]

/-- Interchange of summation against a binomial transform:
`Sum_{k ≤ n} w(k) (Ba)(k) = Sum_{j ≤ n} (Sum_{k ≤ n} w(k) C(k,j)) a(j)`. -/
theorem sum_mul_binomialTransform (w a : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 1), w k * binomialTransform a k =
      ∑ j ∈ range (n + 1), (∑ k ∈ range (n + 1), w k * (k.choose j : ℤ)) * a j := by
  unfold binomialTransform
  have hext : ∀ k ∈ range (n + 1),
      w k * ∑ j ∈ range (k + 1), (k.choose j : ℤ) * a j =
        ∑ j ∈ range (n + 1), w k * ((k.choose j : ℤ) * a j) := by
    intro k hk
    rw [mul_sum]
    refine sum_subset (range_subset_range.mpr (by simpa using hk)) fun j _ hj => ?_
    rw [Nat.choose_eq_zero_of_lt (n := k) (k := j) (by simpa using hj)]
    simp
  rw [sum_congr rfl hext, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun k _ => by ring

/-- Iterated binomial transform: `(B(Ba))(n) = Sum_{j ≤ n} C(n,j) 2^(n-j) a(j)`. -/
theorem binomialTransform_binomialTransform (a : ℕ → ℤ) (n : ℕ) :
    binomialTransform (binomialTransform a) n =
      ∑ j ∈ range (n + 1), (n.choose j : ℤ) * 2 ^ (n - j) * a j := by
  rw [binomialTransform, sum_mul_binomialTransform]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  have hcount := sum_choose_mul_choose_mul (fun _ => 1) n j hjn
  simp only [mul_one] at hcount
  have hpow : ∑ i ∈ range (n - j + 1), ((n - j).choose i : ℤ) = 2 ^ (n - j) := by
    exact_mod_cast Nat.sum_range_choose (n - j)
  rw [hcount, hpow]

/-- Binomial inversion: `Sum_{k ≤ n} (-1)^(n+k) C(n,k) (Ba)(k) = a(n)`. -/
theorem sum_neg_one_pow_mul_binomialTransform (a : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ (n + k) * (n.choose k : ℤ) * binomialTransform a k = a n := by
  rw [sum_mul_binomialTransform, sum_range_succ]
  have hinner : ∀ j ∈ range (n + 1),
      ∑ k ∈ range (n + 1), (-1) ^ (n + k) * (n.choose k : ℤ) * (k.choose j : ℤ) =
        if j = n then 1 else 0 := by
    intro j hj
    have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hre := sum_choose_mul_choose_mul (fun k => (-1) ^ (n + k)) n j hjn
    have hsign : ∀ i ∈ range (n - j + 1),
        ((n - j).choose i : ℤ) * (-1) ^ (n + (j + i)) =
          (-1) ^ (n + j) * ((-1) ^ i * ((n - j).choose i : ℤ)) := by
      intro i _
      rw [← add_assoc, pow_add]; ring
    have halt := Int.alternating_sum_range_choose (n := n - j)
    calc ∑ k ∈ range (n + 1), (-1) ^ (n + k) * (n.choose k : ℤ) * (k.choose j : ℤ)
        = ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (k.choose j : ℤ) * (-1) ^ (n + k) :=
          sum_congr rfl fun k _ => by ring
      _ = (n.choose j : ℤ) * ((-1) ^ (n + j) *
            ∑ i ∈ range (n - j + 1), (-1) ^ i * ((n - j).choose i : ℤ)) := by
          rw [hre, sum_congr rfl hsign, ← mul_sum]
      _ = if j = n then 1 else 0 := by
          rw [halt]
          by_cases hjeq : j = n
          · subst hjeq
            simp [← two_mul, pow_mul]
          · have hne : n - j ≠ 0 := by omega
            simp [hne, hjeq]
  have hlow : ∑ j ∈ range n,
      (∑ k ∈ range (n + 1), (-1) ^ (n + k) * (n.choose k : ℤ) * (k.choose j : ℤ)) * a j = 0 := by
    refine sum_eq_zero fun j hj => ?_
    have hjn : j < n := mem_range.mp hj
    rw [hinner j (mem_range.mpr (by omega)), if_neg (by omega), zero_mul]
  rw [hlow, zero_add, hinner n (self_mem_range_succ n), if_pos rfl, one_mul]

/-! ## The load-bearing identity -/

/-- The recursion of A005329 in additive form:
`d(k) + d(k+1) = 2^(k+1) d(k)`, from `d(k+1) = (2^(k+1) - 1) d(k)`. -/
theorem a005329_succ_add (k : ℕ) :
    (a005329 k : ℤ) + a005329 (k + 1) = 2 ^ (k + 1) * a005329 k := by
  have hstep : a005329 (k + 1) = a005329 k * (2 ^ (k + 1) - 1) := by
    unfold a005329
    rw [prod_Icc_succ_top (by omega)]
  have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [hstep]
  push_cast [hpos]
  ring

/-- **Key identity.** With `e = B(A005329)`,
`Sum_{k ≤ n} C(n,k) e(k+1) = 2^(n+1) e(n)`. -/
theorem binomialTransform_shift_a005329 (n : ℕ) :
    binomialTransform (fun k => binomialTransform (fun j => (a005329 j : ℤ)) (k + 1)) n =
      2 ^ (n + 1) * binomialTransform (fun j => (a005329 j : ℤ)) n := by
  set d : ℕ → ℤ := fun j => (a005329 j : ℤ) with hd
  have hsplit : (fun k => binomialTransform d (k + 1)) =
      fun k => binomialTransform d k + binomialTransform (fun j => d (j + 1)) k :=
    funext fun k => binomialTransform_succ d k
  have hadd : binomialTransform (fun k => binomialTransform d k +
      binomialTransform (fun j => d (j + 1)) k) n =
      binomialTransform (binomialTransform d) n +
        binomialTransform (binomialTransform (fun j => d (j + 1))) n := by
    unfold binomialTransform
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hsplit, hadd, binomialTransform_binomialTransform, binomialTransform_binomialTransform,
    ← sum_add_distrib]
  unfold binomialTransform
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  have hpow : (2 : ℤ) ^ (n - j) * 2 ^ (j + 1) = 2 ^ (n + 1) := by
    rw [← pow_add]; congr 1; omega
  have hdj : d j + d (j + 1) = 2 ^ (j + 1) * d j := a005329_succ_add j
  calc (n.choose j : ℤ) * 2 ^ (n - j) * d j + (n.choose j : ℤ) * 2 ^ (n - j) * d (j + 1)
      = (n.choose j : ℤ) * (2 ^ (n - j) * 2 ^ (j + 1)) * d j := by
        linear_combination (n.choose j : ℤ) * 2 ^ (n - j) * hdj
    _ = 2 ^ (n + 1) * ((n.choose j : ℤ) * d j) := by rw [hpow]; ring

/-! ## A075271: recursion, defining relation, uniqueness -/

/-- The defining recursion of `a075271` with the sum over `range`. -/
theorem a075271_succ (n : ℕ) :
    a075271 (n + 1) = 2 ^ (n + 2) * a075271 n -
      ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * a075271 k := by
  rw [a075271.eq_2, Fin.sum_univ_eq_sum_range (fun k => ((n + 1).choose k : ℤ) * a075271 k)]

/-- Integer form of the A075271 relation:
`Sum_{k ≤ n+1} C(n+1,k) a(k) = 2^(n+1) · 2 a(n)`. -/
theorem binomialTransform_a075271_succ (n : ℕ) :
    binomialTransform a075271 (n + 1) = 2 ^ (n + 1) * (2 * a075271 n) := by
  unfold binomialTransform
  rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, a075271_succ]
  ring

/-- `a075271` satisfies the entry's definition: `(BM)a(n) = 2 a(n-1)` for `n ≥ 1`
(stated at `n + 1` to avoid natural subtraction). -/
theorem a075271_binomialMean_succ (n : ℕ) :
    binomialMean (fun k => (a075271 k : ℚ)) (n + 1) = 2 * a075271 n := by
  have h := binomialTransform_a075271_succ n
  unfold binomialTransform at h
  have hq : ∑ k ∈ range (n + 1 + 1), ((n + 1).choose k : ℚ) * (a075271 k : ℚ) =
      2 ^ (n + 1) * (2 * (a075271 n : ℚ)) := by exact_mod_cast h
  rw [binomialMean, hq]
  field_simp

/-- The entry's definition determines A075271: any rational sequence with
`c(0) = 1` and `(BM)c(n) = 2 c(n-1)` for `n ≥ 1` is `a075271`. -/
theorem eq_a075271_of_binomialMean (c : ℕ → ℚ) (h0 : c 0 = 1)
    (hrel : ∀ n, binomialMean c (n + 1) = 2 * c n) (n : ℕ) : c n = a075271 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [h0, a075271_zero, Int.cast_one]
    | succ m =>
      have hm := hrel m
      rw [binomialMean, div_eq_iff (by positivity), sum_range_succ, Nat.choose_self,
        Nat.cast_one, one_mul] at hm
      have hsum : ∑ k ∈ range (m + 1), ((m + 1).choose k : ℚ) * c k =
          ∑ k ∈ range (m + 1), ((m + 1).choose k : ℚ) * (a075271 k : ℚ) :=
        sum_congr rfl fun k hk => by rw [ih k (by simpa [Nat.lt_succ_iff] using hk)]
      rw [hsum, ih m (Nat.lt_succ_self m)] at hm
      rw [a075271_succ]
      push_cast
      linear_combination hm

/-! ## Layman's conjecture -/

/-- `2 · A075271(m) = e(m+1)` where `e` is the binomial transform of A005329. -/
theorem two_mul_a075271 (m : ℕ) :
    2 * a075271 m = binomialTransform (fun j => (a005329 j : ℤ)) (m + 1) := by
  set e : ℕ → ℤ := binomialTransform (fun j => (a005329 j : ℤ)) with he
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero =>
      rw [he]
      simp [binomialTransform, sum_range_succ, a005329, a075271]
    | succ m =>
      have hK := binomialTransform_shift_a005329 (m + 1)
      rw [← he] at hK
      unfold binomialTransform at hK
      rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at hK
      have hsum : ∑ k ∈ range (m + 1), ((m + 1).choose k : ℤ) * (2 * a075271 k) =
          ∑ k ∈ range (m + 1), ((m + 1).choose k : ℤ) * e (k + 1) :=
        sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk)]
      rw [a075271_succ, mul_sub, ← mul_assoc, mul_comm (2 : ℤ) (2 ^ (m + 2)), mul_assoc,
        ih m (Nat.lt_succ_self m), mul_sum]
      simp_rw [mul_left_comm (2 : ℤ)]
      rw [hsum]
      linear_combination -hK

/-- **Layman's conjecture (A005329, John W. Layman, Sep 12 2002), binomial form.**
A075272 (the BinomialMean transform of A075271) is the binomial transform of
A005329: `A075272(n) = Sum_{k=0..n} C(n,k) Product_{i=1..k} (2^i - 1)`.  This is
also the 2015 comment of Vladimir Reshetnikov on A075272. -/
theorem a075272_eq_sum_choose_mul_a005329 (n : ℕ) :
    a075272 n = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * a005329 k := by
  have hcast : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * a005329 k) =
      ((binomialTransform (fun j => (a005329 j : ℤ)) n : ℤ) : ℚ) := by
    simp [binomialTransform]
  rw [hcast]
  cases n with
  | zero =>
    simp [a075272, binomialMean, binomialTransform, a075271_zero, a005329]
  | succ m =>
    rw [a075272, a075271_binomialMean_succ, ← two_mul_a075271]
    push_cast
    ring

/-- **Layman's conjecture (A005329, John W. Layman, Sep 12 2002), verbatim form.**
"This sequence is the inverse binomial transform of A075272":
`A005329(n) = Sum_{k=0..n} (-1)^(n-k) C(n,k) A075272(k)`, with the sign written
`(-1)^(n+k)` (equal for `k ≤ n`) to avoid natural subtraction. -/
theorem a005329_eq_inverseBinomial_a075272 (n : ℕ) :
    (a005329 n : ℚ) = ∑ k ∈ range (n + 1), (-1) ^ (n + k) * (n.choose k : ℚ) * a075272 k := by
  have hinv := sum_neg_one_pow_mul_binomialTransform (fun j => (a005329 j : ℤ)) n
  have hq : (∑ k ∈ range (n + 1), (-1) ^ (n + k) * (n.choose k : ℚ) *
      ((binomialTransform (fun j => (a005329 j : ℤ)) k : ℤ) : ℚ)) = (a005329 n : ℚ) := by
    exact_mod_cast hinv
  rw [← hq]
  refine sum_congr rfl fun k _ => ?_
  rw [a075272_eq_sum_choose_mul_a005329]
  simp [binomialTransform]

end Candidates.A005329LaymanBinomialTransform
