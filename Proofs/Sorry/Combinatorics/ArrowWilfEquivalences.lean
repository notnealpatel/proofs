/-
# Arrow-Wilf equivalence of (12; 3→3) and (23; 1→1): the formula identity

## Source

Y. Zhou and Q. Yu (as listed on the arXiv record), "Arrow-Wilf equivalences and
enumerative results for short arrow patterns", arXiv:2609.29392.  Retrieved
2026-10-21 (`/tmp/claude/refs/2609.29392.tex`).

* Theorem 3.1 (`thm:12-33`): for `n ≥ 1`,
  `|S_n(12; 3→3)| = d_n + ∑_{m=1}^{n} ∑_{k=0}^{n-m} C(n-m,k) C(m+k-1,n-m) d_k`.
* Theorem 5.5 (`thm:23-11`, equation `equ:23-11`): for `n ≥ 1`,
  `|S_n(23; 1→1)| = d_n + d_{n-1}
      + ∑_{m=1}^{n-1} ∑_{r=0}^{m-1} C(m-1,r) C(n-m+r-1,r) r! d_{m-1-r}`.
  Here `d_n` is the `n`-th derangement number.
* Section 7 ("Final remarks and future directions"), verbatim:
  "We have computed the avoidance counts for the arrow patterns (12;3→3) and
  (23;1→1) and found that the resulting sequences agree for all values of n
  tested. This suggests that these two patterns may be arrow-Wilf-equivalent.
  However, the explicit formulas we obtained for the two sequences are quite
  different in form, and we have not been able to establish the equivalence by
  a direct bijection or by any other method. We leave this as an open problem."
  (A commented-out conjecture in Sec. 5 of the source also asserts
  `(12;3→3) ∼ (21;3→3) ∼ (23;1→1)`.)

## Status

The equivalence is posed as **open** in the paper.  This module proves the
reformulation the paper's own theorems reduce it to: the two printed formulas
`F1 n` and `F2 n` agree for every `n ≥ 1` (`arrow_formulas_agree`).  Combined
with the paper's Theorems 3.1 and 5.5 this gives `|S_n(12;3→3)| = |S_n(23;1→1)|`.
The arrow-pattern enumerations themselves (Foata's fundamental transformation
and arrow containment) are **not** formalized here; those two theorems are the
paper's results and remain unpaid premises of the combinatorial reading.

## Proof outline

The `m`-th summand of `F1 n` is `armL (n-m) (m-1)` and the `m`-th summand of
`F2 n` is `armR (m-1) (n-m)`, where
`armL j p = ∑_k C(j,k) C(p+k,j) d_k` and `armR j p = ∑_r C(j,r) p^(r) d_{j-r}`
(`p^(r)` is the rising factorial `Nat.ascFactorial p r`).  The extra `d_{n-1}`
of `F2` is `armR (n-1) 0`.  The two sums then match after reversing the
summation order, once `armL = armR` (`armL_eq_armR`).  For that, both sides have
binomial transform `∑_j C(N,j) X(j,p) = C(N+p,N) N!` in `j`: one uses the
identity `∑_k C(N,k) d_k = N!`, a Vandermonde convolution for `armL`, and the
hockey-stick identity for `armR`.  The binomial transform is injective, so
`armL = armR`.

## Computational evidence (2026-10-21, `/tmp/claude/a265/`)

Brute-force enumeration of both arrow-avoidance classes (Foata's `θ⁻¹` cycle
convention of the paper) gives `1, 2, 5, 17, 75, 412, 2707, 20657, 179237,
1740806` for `n = 1, …, 10`, equal for both patterns and to `F1 n`.  `F1 = F2`
was checked numerically for `n ≤ 44` and `armL = armR` for `j, p < 30`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.ArrowWilfEquivalences

open Finset

/-- Every permutation of `[N]` is a derangement of its non-fixed points:
`∑_k C(N,k) d_k = N!`. Proved from `d_{k+1} = (k+1) d_k - (-1)^k`. -/
theorem sum_choose_mul_numDerangements (N : ℕ) :
    ∑ k ∈ range (N + 1), N.choose k * numDerangements k = N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    have halt : ∑ k ∈ range (N + 1), ((-1 : ℤ) ^ k * ((N + 1).choose (k + 1) : ℤ)) = 1 := by
      have h0 := Int.alternating_sum_range_choose (n := N + 1)
      rw [if_neg (Nat.succ_ne_zero N), sum_range_succ'] at h0
      simp only [pow_succ, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one] at h0
      have h1 : ∑ k ∈ range (N + 1), ((-1 : ℤ) ^ k * ((N + 1).choose (k + 1) : ℤ))
          = -∑ k ∈ range (N + 1), ((-1 : ℤ) ^ k * (-1) * ((N + 1).choose (k + 1) : ℤ)) := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun k _ => by ring
      linarith
    have hterm : ∀ k ∈ range (N + 1),
        (((N + 1).choose (k + 1) * numDerangements (k + 1) : ℕ) : ℤ)
          = (N + 1 : ℤ) * ((N.choose k * numDerangements k : ℕ) : ℤ)
            - (-1 : ℤ) ^ k * ((N + 1).choose (k + 1) : ℤ) := by
      intro k _
      have hc : ((N + 1 : ℕ) : ℤ) * (N.choose k : ℤ) = ((N + 1).choose (k + 1) : ℤ) * (k + 1 : ℤ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq N k
      push_cast at hc ⊢
      rw [numDerangements_succ]
      linear_combination -(numDerangements k : ℤ) * hc
    have hz : ((∑ k ∈ range (N + 1 + 1), (N + 1).choose k * numDerangements k : ℕ) : ℤ)
        = (((N + 1).factorial : ℕ) : ℤ) := by
      rw [Nat.cast_sum, sum_range_succ', sum_congr rfl hterm, sum_sub_distrib, ← mul_sum,
        halt, ← Nat.cast_sum, ih, Nat.factorial_succ]
      simp
    exact_mod_cast hz

/-- Interchange of a nested binomial sum:
`∑_j C(N,j) ∑_{k≤j} C(j,k) G(k, j-k) = ∑_k ∑_{t≤N-k} C(N,k) C(N-k,t) G(k,t)`. -/
theorem binom_swap (N : ℕ) (G : ℕ → ℕ → ℕ) :
    ∑ j ∈ range (N + 1), ∑ k ∈ range (j + 1), N.choose j * j.choose k * G k (j - k)
      = ∑ k ∈ range (N + 1), ∑ t ∈ range (N - k + 1), N.choose k * (N - k).choose t * G k t := by
  let f : ℕ → ℕ → ℕ := fun k t => N.choose (k + t) * (k + t).choose k * G k t
  calc ∑ j ∈ range (N + 1), ∑ k ∈ range (j + 1), N.choose j * j.choose k * G k (j - k)
      = ∑ j ∈ range (N + 1), ∑ k ∈ range (j + 1), f k (j - k) := by
        refine sum_congr rfl fun j _ => sum_congr rfl fun k hk => ?_
        have hkj : k + (j - k) = j := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hk))
        simp only [f, hkj]
    _ = ∑ k ∈ range (N + 1), ∑ t ∈ range (N + 1 - k), f k t := sum_range_diag_flip (N + 1) f
    _ = _ := by
        refine sum_congr rfl fun k hk => ?_
        have hkN : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
        rw [show N + 1 - k = N - k + 1 by omega]
        refine sum_congr rfl fun t _ => ?_
        simp only [f]
        rw [Nat.choose_mul (Nat.le_add_right k t), Nat.add_sub_cancel_left]

/-- Shifted Vandermonde convolution: `∑_t C(a,t) C(b,c+t) = C(a+b, a+c)`. -/
theorem sum_choose_mul_choose_add (a b c : ℕ) :
    ∑ t ∈ range (a + 1), a.choose t * b.choose (c + t) = (a + b).choose (a + c) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    have hshift : ∑ t ∈ range (a + 1), a.choose (t + 1) * b.choose (c + (t + 1)) + b.choose c
        = (a + b).choose (a + c) := by
      rw [sum_range_succ (fun t => a.choose (t + 1) * b.choose (c + (t + 1))),
        Nat.choose_succ_self, zero_mul, add_zero, ← ih c,
        sum_range_succ' (fun t => a.choose t * b.choose (c + t))]
      simp
    rw [sum_range_succ']
    simp only [Nat.choose_succ_succ, add_mul, sum_add_distrib, Nat.choose_zero_right, one_mul,
      add_zero]
    have h1 : ∑ t ∈ range (a + 1), a.choose t * b.choose (c + (t + 1))
        = (a + b).choose (a + (c + 1)) := by
      rw [← ih (c + 1)]
      refine sum_congr rfl fun t _ => by rw [show c + (t + 1) = c + 1 + t by omega]
    rw [h1, add_assoc, hshift, show a + 1 + b = a + b + 1 by omega,
      show a + 1 + c = a + c + 1 by omega, Nat.choose_succ_succ, Nat.succ_eq_add_one,
      add_assoc a c 1, add_comm]

/-- Rising-factorial Vandermonde with second argument `1`:
`∑_r C(N,r) p^(r) (N-r)! = C(N+p,N) N!`. -/
theorem sum_choose_mul_ascFactorial_mul_factorial (N p : ℕ) :
    ∑ r ∈ range (N + 1), N.choose r * p.ascFactorial r * (N - r).factorial
      = (N + p).choose N * N.factorial := by
  rcases p with _ | q
  · rw [sum_range_succ']
    have hz : ∀ r ∈ range N, N.choose (r + 1) * (0 : ℕ).ascFactorial (r + 1)
        * (N - (r + 1)).factorial = 0 := by
      intro r _
      rw [Nat.zero_ascFactorial r, mul_zero, zero_mul]
    rw [sum_eq_zero hz]
    simp
  · have hterm : ∀ r ∈ range (N + 1), N.choose r * (q + 1).ascFactorial r * (N - r).factorial
        = N.factorial * (r + q).choose q := by
      intro r hr
      have hrN : r ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [Nat.ascFactorial_eq_factorial_mul_choose, ← Nat.choose_mul_factorial_mul_factorial hrN,
        add_comm q r, Nat.choose_symm_add]
      ring
    rw [sum_congr rfl hterm, ← mul_sum, Nat.sum_range_add_choose, mul_comm,
      show N + q + 1 = N + (q + 1) by omega, Nat.choose_symm_add]

/-- The binomial transform `f ↦ (N ↦ ∑_j C(N,j) f j)` is injective on `ℕ → ℕ`. -/
theorem eq_of_sum_choose_mul_eq (f g : ℕ → ℕ)
    (h : ∀ N, ∑ j ∈ range (N + 1), N.choose j * f j = ∑ j ∈ range (N + 1), N.choose j * g j)
    (n : ℕ) : f n = g n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := h n
    rw [sum_range_succ, sum_range_succ, Nat.choose_self, one_mul, one_mul,
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]] at hn
    exact Nat.add_left_cancel hn

/-- `armL j p = ∑_k C(j,k) C(p+k,j) d_k`; with `j = n-m`, `p = m-1` this is the
`m`-th summand of the formula of Theorem 3.1 of arXiv:2609.29392. -/
def armL (j p : ℕ) : ℕ :=
  ∑ k ∈ range (j + 1), j.choose k * (p + k).choose j * numDerangements k

/-- `armR j p = ∑_r C(j,r) p^(r) d_{j-r}` with `p^(r) = Nat.ascFactorial p r`; with
`j = m-1`, `p = n-m` this is the `m`-th summand of the formula of Theorem 5.5 of
arXiv:2609.29392 (since `C(p+r-1,r) r! = p^(r)` for `p ≥ 1`). -/
def armR (j p : ℕ) : ℕ :=
  ∑ r ∈ range (j + 1), j.choose r * p.ascFactorial r * numDerangements (j - r)

/-- Binomial transform of `armL` in `j`: `∑_j C(N,j) armL j p = C(N+p,N) N!`. -/
theorem sum_choose_mul_armL (N p : ℕ) :
    ∑ j ∈ range (N + 1), N.choose j * armL j p = (N + p).choose N * N.factorial := by
  calc ∑ j ∈ range (N + 1), N.choose j * armL j p
      = ∑ j ∈ range (N + 1), ∑ k ∈ range (j + 1), N.choose j * j.choose k *
          ((p + k).choose (k + (j - k)) * numDerangements k) := by
        refine sum_congr rfl fun j _ => ?_
        rw [armL, mul_sum]
        refine sum_congr rfl fun k hk => ?_
        rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        ring
    _ = ∑ k ∈ range (N + 1), ∑ t ∈ range (N - k + 1), N.choose k * (N - k).choose t *
          ((p + k).choose (k + t) * numDerangements k) :=
        binom_swap N fun k t => (p + k).choose (k + t) * numDerangements k
    _ = ∑ k ∈ range (N + 1), N.choose k * numDerangements k * (N + p).choose N := by
        refine sum_congr rfl fun k hk => ?_
        have hkN : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
        have hv := sum_choose_mul_choose_add (N - k) (p + k) k
        rw [show N - k + (p + k) = N + p by omega, show N - k + k = N by omega] at hv
        rw [← hv, mul_sum]
        refine sum_congr rfl fun t _ => by ring
    _ = (N + p).choose N * N.factorial := by
        rw [← sum_mul, sum_choose_mul_numDerangements, mul_comm]

/-- Binomial transform of `armR` in `j`: `∑_j C(N,j) armR j p = C(N+p,N) N!`. -/
theorem sum_choose_mul_armR (N p : ℕ) :
    ∑ j ∈ range (N + 1), N.choose j * armR j p = (N + p).choose N * N.factorial := by
  calc ∑ j ∈ range (N + 1), N.choose j * armR j p
      = ∑ j ∈ range (N + 1), ∑ r ∈ range (j + 1), N.choose j * j.choose r *
          (p.ascFactorial r * numDerangements (j - r)) := by
        refine sum_congr rfl fun j _ => ?_
        rw [armR, mul_sum]
        refine sum_congr rfl fun r _ => by ring
    _ = ∑ r ∈ range (N + 1), ∑ t ∈ range (N - r + 1), N.choose r * (N - r).choose t *
          (p.ascFactorial r * numDerangements t) :=
        binom_swap N fun r t => p.ascFactorial r * numDerangements t
    _ = ∑ r ∈ range (N + 1), N.choose r * p.ascFactorial r * (N - r).factorial := by
        refine sum_congr rfl fun r _ => ?_
        rw [← sum_choose_mul_numDerangements (N - r), mul_sum]
        refine sum_congr rfl fun t _ => by ring
    _ = (N + p).choose N * N.factorial := sum_choose_mul_ascFactorial_mul_factorial N p

/-- Two-parameter identity behind the formula agreement:
`∑_k C(j,k) C(p+k,j) d_k = ∑_r C(j,r) p^(r) d_{j-r}` for all `j p : ℕ`. -/
theorem armL_eq_armR (j p : ℕ) : armL j p = armR j p :=
  eq_of_sum_choose_mul_eq (fun j => armL j p) (fun j => armR j p)
    (fun N => (sum_choose_mul_armL N p).trans (sum_choose_mul_armR N p).symm) j

/-- The right-hand side of Theorem 3.1 (`thm:12-33`) of arXiv:2609.29392, the paper's
count of `|S_n(12; 3→3)|` for `n ≥ 1`:
`d_n + ∑_{m=1}^{n} ∑_{k=0}^{n-m} C(n-m,k) C(m+k-1,n-m) d_k`. -/
def F1 (n : ℕ) : ℕ :=
  numDerangements n + ∑ m ∈ Icc 1 n, ∑ k ∈ range (n - m + 1),
    (n - m).choose k * (m + k - 1).choose (n - m) * numDerangements k

/-- The right-hand side of Theorem 5.5 (`thm:23-11`) of arXiv:2609.29392, the paper's
count of `|S_n(23; 1→1)|` for `n ≥ 1`:
`d_n + d_{n-1} + ∑_{m=1}^{n-1} ∑_{r=0}^{m-1} C(m-1,r) C(n-m+r-1,r) r! d_{m-1-r}`.
For `1 ≤ m ≤ n-1` all natural subtractions here are exact. -/
def F2 (n : ℕ) : ℕ :=
  numDerangements n + numDerangements (n - 1) + ∑ m ∈ Ico 1 n, ∑ r ∈ range m,
    (m - 1).choose r * (n - m + r - 1).choose r * r.factorial * numDerangements (m - 1 - r)

/-! Ground truth: the common counts `1, 2, 5, 17, 75, 412` for `n = 1, …, 6`
(brute-force enumeration of both arrow-avoidance classes, 2026-10-21). -/
example : (List.range 6).map (fun i => F1 (i + 1)) = [1, 2, 5, 17, 75, 412] := by decide
example : (List.range 6).map (fun i => F2 (i + 1)) = [1, 2, 5, 17, 75, 412] := by decide

/-! Ground truth for the two summand families: `armL 2 1 = C(2,0)C(1,2)·1 + C(2,1)C(2,2)·0
+ C(2,2)C(3,2)·1 = 3` and `armR 2 1 = d_2 + 2·1·d_1 + 1·2·d_0 = 3`. -/
example : armL 2 1 = 3 := by decide
example : armR 2 1 = 3 := by decide
example : armL 3 2 = 32 := by decide
example : armR 3 2 = 32 := by decide

/-- `F1 (N+1) = d_{N+1} + ∑_{i ≤ N} armL (N-i) i` (reindexing `m = i+1`). -/
theorem F1_succ (N : ℕ) :
    F1 (N + 1) = numDerangements (N + 1) + ∑ i ∈ range (N + 1), armL (N - i) i := by
  rw [F1, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [armL, show N + 1 - (1 + i) = N - i by omega]
  refine sum_congr rfl fun k _ => ?_
  rw [show 1 + i + k - 1 = i + k by omega]

/-- `armR j 0 = d_j`, since `0^(r) = 0` for `r ≥ 1`. -/
theorem armR_zero_right (j : ℕ) : armR j 0 = numDerangements j := by
  rw [armR, sum_range_succ']
  have hz : ∀ r ∈ range j, j.choose (r + 1) * (0 : ℕ).ascFactorial (r + 1)
      * numDerangements (j - (r + 1)) = 0 := by
    intro r _
    rw [Nat.zero_ascFactorial r, mul_zero, zero_mul]
  rw [sum_eq_zero hz]
  simp

/-- `F2 (N+1) = d_{N+1} + ∑_{i ≤ N} armR i (N-i)`; the term `i = N` is the extra
`d_N` of the formula. -/
theorem F2_succ (N : ℕ) :
    F2 (N + 1) = numDerangements (N + 1) + ∑ i ∈ range (N + 1), armR i (N - i) := by
  rw [F2, sum_Ico_eq_sum_range, sum_range_succ, Nat.sub_self, armR_zero_right, Nat.add_sub_cancel,
    add_assoc,
    add_comm (numDerangements N)]
  congr 2
  refine sum_congr rfl fun i hi => ?_
  have hiN : i < N := mem_range.mp hi
  obtain ⟨q, hq⟩ : ∃ q, N - i = q + 1 := ⟨N - i - 1, by omega⟩
  rw [armR, show 1 + i - 1 = i by omega, hq, add_comm 1 i]
  refine sum_congr rfl fun r _ => ?_
  rw [Nat.ascFactorial_eq_factorial_mul_choose, show N + 1 - (i + 1) + r - 1 = q + r by omega]
  ring

/-- **Formula identity behind the open problem of arXiv:2609.29392, Sec. 7.**
For every `n ≥ 1` the paper's formula for `|S_n(12; 3→3)|` (Theorem 3.1) equals
its formula for `|S_n(23; 1→1)|` (Theorem 5.5).  Together with those two
(unformalized) theorems this gives the conjectured arrow-Wilf equivalence
`(12; 3→3) ∼ (23; 1→1)`. -/
theorem arrow_formulas_agree (n : ℕ) (hn : 1 ≤ n) : F1 n = F2 n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [F1_succ, F2_succ]
  congr 1
  rw [← sum_range_reflect (fun i => armR i (N - i)) (N + 1)]
  refine sum_congr rfl fun i hi => ?_
  have hiN : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [armL_eq_armR, show N + 1 - 1 - i = N - i by omega, show N - (N - i) = i by omega]

/-! Non-vacuity: the hypothesis `1 ≤ n` is satisfiable, e.g. at `n = 4`. -/
example : F1 4 = F2 4 := arrow_formulas_agree 4 (by norm_num)

end Candidates.ArrowWilfEquivalences
