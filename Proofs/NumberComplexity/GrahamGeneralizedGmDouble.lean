/-
# Generalised Graham function: `g_m(n) = 2n` only in the conjectured cases

## Source

arXiv 2504.19196 (v2, 8 May 2025), Sarah Adenwalla, "On a Generalisation of a
Function of Ron Graham's".  Definitions in Section 2 (Preliminaries); the statement
is the unnumbered Conjecture at the end of Section 4, stated after Corollary
`corollary:p`; the small cases `g_m(0..7)` are in the Appendix.

Definitions (verbatim):

```
A sequence of integers, a_1 ≤ a_2 ≤ … ≤ a_t, is a m-product sequence if there exists
R ∈ ℕ such that ∏_{i=1}^t a_i = R^m and no integer appears more than m-1 times in the
sequence.

For n ∈ ℕ, we say g_m(n) is the least integer s such that there exists an m-product
sequence starting at n and ending at s, that is n = a_1 ≤ … ≤ a_t = s.
```

Conjecture (verbatim):

```
For all m ≥ 2 and all n ∈ ℕ, we have g_m(n) = 2n if and only if:
  1. n is prime and (m,n) ≠ {(2,2),(2,3)}
  2. n = 0
  3. n = 4 for odd m > 3
  4. (m,n) = {(2,6),(3,6),(6,6)}.
```

## Status (recorded 2026-10-21)

The paper proves the 'if' direction (Corollary 4.11 with the Appendix) and the full
conjecture for even `m`; the 'only if' direction for odd `m` is left open there.
This module proves the 'only if' direction for every `m ≥ 2`
(`gm_eq_two_mul_imp`), completely.  The argument uses only the short
constructions the paper uses for `m = 2` and in the Appendix:

* (i)   `n = ab`, `1 < a < b`: `ab, (a(b+1))^{m-1}, ((a+1)b)^{m-1}, (a+1)(b+1)`;
* (ii)  `n = p²`, `m ≥ 3`: `p², (p(p+1))^{m-2}, (p+1)²`; even `m`: `(p²)^{m/2}`;
* (iii) `n = 6`, `m ∉ {2,3,6}`: `6^{6 mod m}, 8^{m-2}, 9^{m-3}`;
* valuation obstructions giving `g_2(2) > 4`, `g_2(3) > 6`, `g_3(4) > 8`.

Formalisation notes.  A sequence `a₁ ≤ ⋯ ≤ aₜ` is recorded as the multiset of its
terms (the order is forced).  "No integer appears more than `m-1` times" is written
`count a < m`, equivalent for `m ≥ 1`.  `g_m(n)` is `sInf` of the set of admissible
end points; that set is nonempty for `2 ≤ m` (`exists_isMProductSeqFromTo`), so `sInf`
is never at its junk value under the theorem's hypothesis `2 ≤ m`.
-/
import Mathlib

set_option autoImplicit false

namespace GrahamGeneralizedGmDouble

open Multiset

/-- An `m`-product sequence (arXiv 2504.19196, Definition in Section 2): a finite
nondecreasing sequence of naturals `a₁ ≤ ⋯ ≤ aₜ`, recorded as the multiset of its
terms, whose product is an `m`-th power `R ^ m` with `R ∈ ℕ`, and in which no integer
appears more than `m - 1` times (written `count a < m`). -/
def IsMProductSeq (m : ℕ) (A : Multiset ℕ) : Prop :=
  (∃ R : ℕ, A.prod = R ^ m) ∧ ∀ a : ℕ, A.count a < m

/-- `A` is an `m`-product sequence starting at `n` and ending at `s`, i.e.
`n = a₁ ≤ ⋯ ≤ aₜ = s`: both `n` and `s` occur and every term lies in `[n, s]`. -/
def IsMProductSeqFromTo (m n s : ℕ) (A : Multiset ℕ) : Prop :=
  IsMProductSeq m A ∧ n ∈ A ∧ s ∈ A ∧ ∀ a ∈ A, n ≤ a ∧ a ≤ s

/-- `g_m(n)` (arXiv 2504.19196, Section 2): the least integer `s` such that there is an
`m`-product sequence starting at `n` and ending at `s`. The defining set is nonempty for
`2 ≤ m` (`exists_isMProductSeqFromTo`). -/
noncomputable def gm (m n : ℕ) : ℕ :=
  sInf {s | ∃ A, IsMProductSeqFromTo m n s A}

/-! ## Basic API -/

/-- Any `m`-product sequence from `n` to `s` bounds `g_m(n) ≤ s`. -/
theorem gm_le {m n s : ℕ} {A : Multiset ℕ} (h : IsMProductSeqFromTo m n s A) : gm m n ≤ s :=
  Nat.sInf_le ⟨A, h⟩

/-- Construction lemma: four strictly increasing values `w < x < y < z` with
multiplicities `k₁, …, k₄ < m`, `k₁, k₄ > 0`, and product an `m`-th power, form an
`m`-product sequence from `w` to `z`. -/
theorem isMProductSeqFromTo_four {m w x y z k₁ k₂ k₃ k₄ R : ℕ}
    (hwx : w < x) (hxy : x < y) (hyz : y < z) (hk₁ : 0 < k₁) (hk₄ : 0 < k₄)
    (hk₁m : k₁ < m) (hk₂m : k₂ < m) (hk₃m : k₃ < m) (hk₄m : k₄ < m)
    (hprod : w ^ k₁ * x ^ k₂ * y ^ k₃ * z ^ k₄ = R ^ m) :
    IsMProductSeqFromTo m w z
      (replicate k₁ w + replicate k₂ x + replicate k₃ y + replicate k₄ z) := by
  refine ⟨⟨⟨R, ?_⟩, fun t => ?_⟩, ?_, ?_, fun t ht => ?_⟩
  · simpa only [prod_add, prod_replicate] using hprod
  · simp only [count_add, count_replicate]
    split_ifs <;> omega
  · simp [mem_add, mem_replicate, hk₁.ne']
  · simp [mem_add, mem_replicate, hk₄.ne']
  · simp only [mem_add, mem_replicate] at ht
    rcases ht with ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> omega

/-- Construction lemma: a single value `w` with multiplicity `0 < k < m` and `w ^ k` an
`m`-th power is an `m`-product sequence from `w` to `w`. -/
theorem isMProductSeqFromTo_one {m w k R : ℕ} (hk : 0 < k) (hkm : k < m)
    (hprod : w ^ k = R ^ m) : IsMProductSeqFromTo m w w (replicate k w) := by
  refine ⟨⟨⟨R, ?_⟩, fun t => ?_⟩, ?_, ?_, fun t ht => ?_⟩
  · simpa only [prod_replicate] using hprod
  · simp only [count_replicate]
    split_ifs <;> omega
  · simp [mem_replicate, hk.ne']
  · simp [mem_replicate, hk.ne']
  · rw [mem_replicate] at ht
    omega

/-- For `2 ≤ m` every `n` admits an `m`-product sequence starting at `n`:
`{0}` for `n = 0`, and `n, (n·2^m)^{m-1}` (product `(n·2^{m-1})^m`) for `n ≥ 1`. -/
theorem exists_isMProductSeqFromTo {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    ∃ s A, IsMProductSeqFromTo m n s A := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, _, isMProductSeqFromTo_one (R := 0) Nat.one_pos (by omega) (by simp)⟩
  · have h4 : 4 ≤ 2 ^ (k + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hz : n + 2 < n * 2 ^ (k + 1) := by nlinarith
    refine ⟨n * 2 ^ (k + 1), _, isMProductSeqFromTo_four (k₂ := 0) (k₃ := 0)
      (x := n + 1) (y := n + 2) (k₁ := 1) (k₄ := k + 1 - 1) (R := n * 2 ^ k)
      (by omega) (by omega) hz Nat.one_pos (by omega) (by omega) (by omega) (by omega)
      (by omega) ?_⟩
    rw [Nat.add_sub_cancel, pow_zero, pow_zero, mul_one, mul_one, mul_pow, mul_pow,
      ← pow_mul, ← pow_mul]
    ring

/-- For `2 ≤ m`, `g_m(n)` is attained by an `m`-product sequence from `n` to `g_m(n)`. -/
theorem gm_spec {m : ℕ} (hm : 2 ≤ m) (n : ℕ) : ∃ A, IsMProductSeqFromTo m n (gm m n) A := by
  obtain ⟨s, A, hA⟩ := exists_isMProductSeqFromTo hm n
  exact Nat.sInf_mem (s := {s | ∃ A, IsMProductSeqFromTo m n s A}) ⟨s, A, hA⟩

/-- For `2 ≤ m`, `n ≤ g_m(n)`: every sequence starting at `n` ends at some `s ≥ n`. -/
theorem le_gm {m : ℕ} (hm : 2 ≤ m) (n : ℕ) : n ≤ gm m n := by
  obtain ⟨A, hA⟩ := gm_spec hm n
  exact (hA.2.2.2 n hA.2.1).2

/-- Valuation obstruction: if every term of an `m`-product sequence `A` lies in `[n, S]`
with `0 < n`, then for every `p`, `m` divides `∑_{i ∈ [n,S]} count(i) · v_p(i)`, where
`v_p = Nat.factorization · p`. -/
theorem dvd_sum_count_mul_factorization {m n S : ℕ} {A : Multiset ℕ}
    (hA : IsMProductSeq m A) (hmem : ∀ a ∈ A, n ≤ a ∧ a ≤ S) (hn : 0 < n) (p : ℕ) :
    m ∣ ∑ i ∈ Finset.Icc n S, A.count i * i.factorization p := by
  classical
  obtain ⟨⟨R, hR⟩, -⟩ := hA
  have hprod : A.prod = ∏ i ∈ Finset.Icc n S, i ^ A.count i := by
    rw [Finset.prod_multiset_count]
    refine Finset.prod_subset (fun i hi => ?_) (fun i _ hi => ?_)
    · rw [Multiset.mem_toFinset] at hi
      exact Finset.mem_Icc.mpr (hmem i hi)
    · rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hi
      rw [hi, pow_zero]
  have hfac : (A.prod).factorization p = ∑ i ∈ Finset.Icc n S, A.count i * i.factorization p := by
    rw [hprod, Nat.factorization_prod (fun i hi => ?_), Finsupp.finsetSum_apply]
    · simp [Nat.factorization_pow]
    · exact pow_ne_zero _ (by have := (Finset.mem_Icc.mp hi).1; omega)
  rw [← hfac, hR, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  exact Dvd.intro _ rfl

/-! ## Upper-bound constructions -/

/-- `g_m(1) ≤ 1`: the one-term sequence `1` is an `m`-product sequence. -/
theorem gm_one_le {m : ℕ} (hm : 2 ≤ m) : gm m 1 ≤ 1 :=
  gm_le (isMProductSeqFromTo_one (R := 1) Nat.one_pos (by omega) (by simp))

/-- Construction (i): for `1 < a < b` the sequence `ab, (a(b+1))^{m-1}, ((a+1)b)^{m-1},
(a+1)(b+1)` has product `(ab(a+1)(b+1))^m`, so `g_m(ab) ≤ (a+1)(b+1)`. -/
theorem gm_mul_le {m a b : ℕ} (hm : 2 ≤ m) (ha : 1 < a) (hab : a < b) :
    gm m (a * b) ≤ (a + 1) * (b + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : a * b < a * (b + 1) := by nlinarith
  have h2 : a * (b + 1) < (a + 1) * b := by nlinarith
  have h3 : (a + 1) * b < (a + 1) * (b + 1) := by nlinarith
  refine gm_le (isMProductSeqFromTo_four (k₁ := 1) (k₂ := k + 1 - 1) (k₃ := k + 1 - 1)
    (k₄ := 1) (R := a * b * (a + 1) * (b + 1)) h1 h2 h3 Nat.one_pos Nat.one_pos
    (by omega) (by omega) (by omega) (by omega) ?_)
  rw [Nat.add_sub_cancel, pow_one, pow_one, pow_succ]
  simp only [mul_pow]
  ring

/-- Construction (ii): for `3 ≤ m` and `0 < p` the sequence `p², (p(p+1))^{m-2}, (p+1)²`
has product `(p(p+1))^m`, so `g_m(p²) ≤ (p+1)²`. -/
theorem gm_sq_le_succ_sq {m p : ℕ} (hm : 3 ≤ m) (hp : 0 < p) :
    gm m (p ^ 2) ≤ (p + 1) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 : p ^ 2 < p * (p + 1) := by nlinarith
  have h3 : p * (p + 1) + 1 < (p + 1) ^ 2 := by nlinarith
  refine gm_le (isMProductSeqFromTo_four (k₁ := 1) (k₂ := k + 2 - 2) (k₃ := 0)
    (k₄ := 1) (R := p * (p + 1)) h1 (Nat.lt_succ_self _) h3 Nat.one_pos Nat.one_pos
    (by omega) (by omega) (by omega) (by omega) ?_)
  rw [Nat.add_sub_cancel, pow_zero, mul_one, pow_add]
  simp only [mul_pow]
  ring

/-- For even `m > 0`, every square `q²` satisfies `g_m(q²) ≤ q²`, witnessed by
`(q²)^{m/2} = q^m`. -/
theorem gm_sq_le_of_even {m q : ℕ} (hm : Even m) (hm0 : 0 < m) : gm m (q ^ 2) ≤ q ^ 2 := by
  obtain ⟨r, rfl⟩ := hm
  refine gm_le (isMProductSeqFromTo_one (k := r) (R := q) (by omega) (by omega) ?_)
  rw [← pow_mul, two_mul]

/-- Construction (iii): for `4 ≤ m`, `m ≠ 6`, the sequence `6^{6 mod m}, 8^{m-2}, 9^{m-3}`
is an `m`-product sequence, so `g_m(6) ≤ 9`. -/
theorem gm_six_le {m : ℕ} (hm : 4 ≤ m) (hm6 : m ≠ 6) : gm m 6 ≤ 9 := by
  rcases (show m = 4 ∨ m = 5 ∨ 7 ≤ m by omega) with rfl | rfl | h7
  · exact gm_le (isMProductSeqFromTo_four (x := 7) (y := 8) (k₁ := 2) (k₂ := 0) (k₃ := 2)
      (k₄ := 1) (R := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · exact gm_le (isMProductSeqFromTo_four (x := 7) (y := 8) (k₁ := 1) (k₂ := 0) (k₃ := 3)
      (k₄ := 2) (R := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
    refine gm_le (isMProductSeqFromTo_four (x := 7) (y := 8) (k₁ := 6) (k₂ := 0)
      (k₃ := k + 5) (k₄ := k + 4) (R := 72) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
    rw [show (72 : ℕ) = 8 * 9 by norm_num, mul_pow, pow_add, pow_add, pow_add, pow_add]
    ring

/-! ## Valuation obstructions for the exceptional cases -/

/-- `v_p(p^k · r) = k` when `p` is prime and `p ∤ r`. -/
theorem factorization_prime_pow_mul {p k r : ℕ} (hp : p.Prime) (hr : ¬p ∣ r) :
    (p ^ k * r).factorization p = k := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hr0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hr,
    add_zero]

/-- No `2`-product sequence starting at `2` ends at some `s ≤ 5` (2-adic count). -/
theorem not_isMProductSeqFromTo_two_two {s : ℕ} {A : Multiset ℕ}
    (h : IsMProductSeqFromTo 2 2 s A) : 5 < s := by
  by_contra hs
  have hmem : ∀ a ∈ A, 2 ≤ a ∧ a ≤ 5 := fun a ha => ⟨(h.2.2.2 a ha).1, by
    have := (h.2.2.2 a ha).2; omega⟩
  have hd := dvd_sum_count_mul_factorization h.1 hmem (by norm_num) 2
  have hc2 : 0 < A.count 2 := Multiset.count_pos.mpr h.2.1
  have hc2' := h.1.2 2
  have v2 : (2 : ℕ).factorization 2 = 1 := by
    simpa using factorization_prime_pow_mul (k := 1) (r := 1) Nat.prime_two (by decide)
  have v3 : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have v4 : (4 : ℕ).factorization 2 = 2 := by
    simpa using factorization_prime_pow_mul (k := 2) (r := 1) Nat.prime_two (by decide)
  have v5 : (5 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  simp only [Finset.sum_Icc_succ_top, Nat.reduceLeDiff, Finset.Icc_self,
    Finset.sum_singleton, v2, v3, v4, v5] at hd
  omega

/-- No `2`-product sequence starting at `3` ends at some `s ≤ 7` (2-adic, then 3-adic). -/
theorem not_isMProductSeqFromTo_two_three {s : ℕ} {A : Multiset ℕ}
    (h : IsMProductSeqFromTo 2 3 s A) : 7 < s := by
  by_contra hs
  have hmem : ∀ a ∈ A, 3 ≤ a ∧ a ≤ 7 := fun a ha => ⟨(h.2.2.2 a ha).1, by
    have := (h.2.2.2 a ha).2; omega⟩
  have hd2 := dvd_sum_count_mul_factorization h.1 hmem (by norm_num) 2
  have hd3 := dvd_sum_count_mul_factorization h.1 hmem (by norm_num) 3
  have hc3 : 0 < A.count 3 := Multiset.count_pos.mpr h.2.1
  have hc3' := h.1.2 3
  have hc6' := h.1.2 6
  have u3 : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have u4 : (4 : ℕ).factorization 2 = 2 := by
    simpa using factorization_prime_pow_mul (k := 2) (r := 1) Nat.prime_two (by decide)
  have u5 : (5 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have u6 : (6 : ℕ).factorization 2 = 1 := by
    simpa using factorization_prime_pow_mul (k := 1) (r := 3) Nat.prime_two (by decide)
  have u7 : (7 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have w3 : (3 : ℕ).factorization 3 = 1 := by
    simpa using factorization_prime_pow_mul (k := 1) (r := 1) Nat.prime_three (by decide)
  have w4 : (4 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have w5 : (5 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have w6 : (6 : ℕ).factorization 3 = 1 := by
    simpa using factorization_prime_pow_mul (k := 1) (r := 2) Nat.prime_three (by decide)
  have w7 : (7 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  simp only [Finset.sum_Icc_succ_top, Nat.reduceLeDiff, Finset.Icc_self,
    Finset.sum_singleton, u3, u4, u5, u6, u7] at hd2
  simp only [Finset.sum_Icc_succ_top, Nat.reduceLeDiff, Finset.Icc_self,
    Finset.sum_singleton, w3, w4, w5, w6, w7] at hd3
  omega

/-- No `3`-product sequence starting at `4` ends at some `s ≤ 8` (3-adic, then 2-adic). -/
theorem not_isMProductSeqFromTo_three_four {s : ℕ} {A : Multiset ℕ}
    (h : IsMProductSeqFromTo 3 4 s A) : 8 < s := by
  by_contra hs
  have hmem : ∀ a ∈ A, 4 ≤ a ∧ a ≤ 8 := fun a ha => ⟨(h.2.2.2 a ha).1, by
    have := (h.2.2.2 a ha).2; omega⟩
  have hd2 := dvd_sum_count_mul_factorization h.1 hmem (by norm_num) 2
  have hd3 := dvd_sum_count_mul_factorization h.1 hmem (by norm_num) 3
  have hc4 : 0 < A.count 4 := Multiset.count_pos.mpr h.2.1
  have hc4' := h.1.2 4
  have hc6' := h.1.2 6
  have u4 : (4 : ℕ).factorization 2 = 2 := by
    simpa using factorization_prime_pow_mul (k := 2) (r := 1) Nat.prime_two (by decide)
  have u5 : (5 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have u6 : (6 : ℕ).factorization 2 = 1 := by
    simpa using factorization_prime_pow_mul (k := 1) (r := 3) Nat.prime_two (by decide)
  have u7 : (7 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have u8 : (8 : ℕ).factorization 2 = 3 := by
    simpa using factorization_prime_pow_mul (k := 3) (r := 1) Nat.prime_two (by decide)
  have w4 : (4 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have w5 : (5 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have w6 : (6 : ℕ).factorization 3 = 1 := by
    simpa using factorization_prime_pow_mul (k := 1) (r := 2) Nat.prime_three (by decide)
  have w7 : (7 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have w8 : (8 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  simp only [Finset.sum_Icc_succ_top, Nat.reduceLeDiff, Finset.Icc_self,
    Finset.sum_singleton, u4, u5, u6, u7, u8] at hd2
  simp only [Finset.sum_Icc_succ_top, Nat.reduceLeDiff, Finset.Icc_self,
    Finset.sum_singleton, w4, w5, w6, w7, w8] at hd3
  omega

/-- `g_2(2) > 4`, `g_2(3) > 6`, `g_3(4) > 8`: the three cases where `g_m(n) > 2n`. -/
theorem two_mul_lt_gm_exceptional {m n : ℕ} (h : (m = 2 ∧ (n = 2 ∨ n = 3)) ∨ (m = 3 ∧ n = 4)) :
    2 * n < gm m n := by
  rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨A, hA⟩ := gm_spec (m := 2) le_rfl 2
    have := not_isMProductSeqFromTo_two_two hA
    omega
  · obtain ⟨A, hA⟩ := gm_spec (m := 2) le_rfl 3
    have := not_isMProductSeqFromTo_two_three hA
    omega
  · obtain ⟨A, hA⟩ := gm_spec (m := 3) (by norm_num) 4
    have := not_isMProductSeqFromTo_three_four hA
    omega

/-! ## Ground truth from the paper's Appendix -/

/-- `g_m(0) = 0` (Appendix, item 0): the one-term sequence `0` has product `0 = 0^m`. -/
theorem gm_zero {m : ℕ} (hm : 2 ≤ m) : gm m 0 = 0 :=
  Nat.le_zero.mp (gm_le (isMProductSeqFromTo_one (R := 0) Nat.one_pos (by omega)
    (by rw [pow_one, zero_pow (by omega : m ≠ 0)])))

/-- `g_m(1) = 1` (Appendix, item 1). -/
example {m : ℕ} (hm : 2 ≤ m) : gm m 1 = 1 :=
  le_antisymm (gm_one_le hm) (le_gm hm 1)

/-- `g_2(2) = 6` (Appendix, item 2): `2 · 3 · 6 = 6²`. -/
example : gm 2 2 = 6 := by
  have hle : gm 2 2 ≤ 6 := gm_le (isMProductSeqFromTo_four (x := 3) (y := 4) (k₁ := 1)
    (k₂ := 1) (k₃ := 0) (k₄ := 1) (R := 6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))
  obtain ⟨A, hA⟩ := gm_spec (m := 2) le_rfl 2
  have hgt := not_isMProductSeqFromTo_two_two hA
  omega

/-- `g_2(3) = 8` (Appendix, item 3): `3 · 6 · 8 = 12²`. -/
example : gm 2 3 = 8 := by
  have hle : gm 2 3 ≤ 8 := gm_le (isMProductSeqFromTo_four (x := 6) (y := 7) (k₁ := 1)
    (k₂ := 1) (k₃ := 0) (k₄ := 1) (R := 12) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))
  obtain ⟨A, hA⟩ := gm_spec (m := 2) le_rfl 3
  have hgt := not_isMProductSeqFromTo_two_three hA
  omega

/-- `g_3(4) = 9` (Appendix, item 4): `4 · 6 · 9 = 6³`; the unique case `g_m(n) > 2n`
with `n ≥ 4`. -/
example : gm 3 4 = 9 := by
  have hle : gm 3 4 ≤ 9 := gm_le (isMProductSeqFromTo_four (x := 6) (y := 8) (k₁ := 1)
    (k₂ := 1) (k₃ := 0) (k₄ := 1) (R := 6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))
  obtain ⟨A, hA⟩ := gm_spec (m := 3) (by norm_num) 4
  have hgt := not_isMProductSeqFromTo_three_four hA
  omega

/-- `g_5(6) ≤ 9` via `6 · 8³ · 9² = 12⁵` (Appendix, item 6). -/
example : gm 5 6 ≤ 9 := gm_six_le (by norm_num) (by norm_num)

/-- Non-vacuity: the hypotheses `2 ≤ m` and `g_m(n) = 2n` of `gm_eq_two_mul_imp` hold
jointly at `(m, n) = (2, 0)`. -/
example : 2 ≤ 2 ∧ gm 2 0 = 2 * 0 := ⟨le_rfl, gm_zero le_rfl⟩

/-! ## Main theorem -/

/-- **'Only if' direction of the `g_m(n) = 2n` conjecture** (arXiv 2504.19196, Section 4,
the unnumbered Conjecture after Corollary `corollary:p`; open for odd `m` in the paper).
For every `m ≥ 2` and `n ∈ ℕ`, if `g_m(n) = 2n` then `n = 0`, or `n` is prime with
`(m, n) ∉ {(2,2), (2,3)}`, or `n = 4` with `m` odd and `m > 3`, or
`(m, n) ∈ {(2,6), (3,6), (6,6)}`. -/
theorem gm_eq_two_mul_imp {m n : ℕ} (hm : 2 ≤ m) (h : gm m n = 2 * n) :
    n = 0 ∨ (n.Prime ∧ ¬(m = 2 ∧ (n = 2 ∨ n = 3))) ∨ (n = 4 ∧ Odd m ∧ 3 < m) ∨
      (n = 6 ∧ (m = 2 ∨ m = 3 ∨ m = 6)) := by
  by_contra hcon
  have hn0 : n ≠ 0 := fun h0 => hcon (Or.inl h0)
  have hprime : n.Prime → m = 2 ∧ (n = 2 ∨ n = 3) := fun hp => by
    by_contra hex
    exact hcon (Or.inr (Or.inl ⟨hp, hex⟩))
  have h4 : n = 4 → Odd m → m ≤ 3 := fun hn4 hodd => by
    by_contra hlt
    exact hcon (Or.inr (Or.inr (Or.inl ⟨hn4, hodd, by omega⟩)))
  have h6 : n = 6 → ¬(m = 2 ∨ m = 3 ∨ m = 6) := fun hn6 hm6 =>
    hcon (Or.inr (Or.inr (Or.inr ⟨hn6, hm6⟩)))
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · have hle := gm_one_le hm
    omega
  by_cases hp : n.Prime
  · have hlt := two_mul_lt_gm_exceptional (Or.inl (hprime hp))
    omega
  -- `n` is composite: write `n = a * b` with `a = minFac n ≤ b`.
  have ha : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hp
  obtain ⟨b, hb⟩ := Nat.minFac_dvd n
  generalize n.minFac = a at ha hsq hb
  have ha2 : 2 ≤ a := ha.two_le
  have hab : a ≤ b := by
    by_contra hba
    push Not at hba
    have hlt : a * b < a * a := Nat.mul_lt_mul_of_pos_left hba (by omega)
    nlinarith
  rcases hab.lt_or_eq with hlt | heq
  · by_cases hn6 : n = 6
    · have hm6 := h6 hn6
      subst hn6
      have hle := gm_six_le (m := m) (by omega) (by omega)
      omega
    · have hle := gm_mul_le hm ha.one_lt hlt
      rw [← hb] at hle
      have hbig : (a + 1) * (b + 1) < 2 * (a * b) := by
        rcases (show a = 2 ∨ 3 ≤ a by omega) with ha' | ha'
        · rw [ha'] at hb hlt ⊢
          have hb4 : 4 ≤ b := by omega
          nlinarith
        · nlinarith
      omega
  · subst heq
    have hn : n = a ^ 2 := by rw [hb, sq]
    rcases Nat.even_or_odd m with he | ho
    · have hle := gm_sq_le_of_even (q := a) he (by omega)
      rw [← hn] at hle
      omega
    · rcases (show a = 2 ∨ 3 ≤ a by omega) with ha' | ha'
      · have hn4 : n = 4 := by rw [hn, ha']; norm_num
        have hm3 : m = 3 := by
          have hm3' := h4 hn4 ho
          obtain ⟨k, hk⟩ := ho
          omega
        have hlt := two_mul_lt_gm_exceptional (Or.inr ⟨hm3, hn4⟩)
        omega
      · have hm3 : 3 ≤ m := by obtain ⟨k, hk⟩ := ho; omega
        have hle := gm_sq_le_succ_sq hm3 (show 0 < a by omega)
        rw [← hn] at hle
        have hbig : (a + 1) ^ 2 < 2 * a ^ 2 := by nlinarith
        omega

end GrahamGeneralizedGmDouble
