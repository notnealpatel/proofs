/-
# A108866 — prime half of Ordowski's conjecture

## OEIS source (retrieved with `oeis show A108866`, 2026-10-21)

```
NAME:     Numerator of Sum_{k=1..n} 2^k/k.
TERMS:    0,2,4,20,32,256,416,4832,8192,42496,74752,1467392,2650112,62836736,
          115552256,42790912,79691776,2535587840,4766040064,170851041280, ...
KEYWORDS: nonn,frac
COMMENT (the conjecture):
  Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2)
  if and only if n is prime. See my formula below. Cf. A332786.
  - _Thomas Ordowski_, Mar 02 2020
FORMULA:
  a(n) = numerator(Sum_{k=1..n} (2^k-2)/k + Sum_{k=1..n} 2/k). This formula is
  a heuristic of my conjecture in the comments section. Cf. A330718.
  - _Thomas Ordowski_, Mar 02 2020
```

The prime half ("if n is prime then n² divides the numerator") is also stated
without proof in A330718 ("If p > 3 is prime, then p^2 | a(p)") and in A332786
("If p > 3 is a prime, then p^2 | a(p). Does the above statement follow from
Wolstenholme's theorem?").

## Target

Prime half only: for every prime `p ≥ 5`,
`p² ∣ numerator(-2/p + ∑_{k=1}^{p} 2^k/k)`.  The composite half ("only if") is
not addressed here.

## Status

Triage status: open (no proof located in the entries or the literature by the
triage).  Computation (exact rationals, 2026-10-21): the divisibility holds for
all 249 primes `5 ≤ p ≤ 1600`, and no composite `4 ≤ n ≤ 1600` satisfies it.

## Proof route (kernel-checked below)

1. `∑_{k=1}^{n} 2^k/k = H_n + ∑_{k=1}^{n} C(n,k)/k` (induction, Pascal, and
   `∑_{k=0}^{n} C(n,k)/(k+1) = (2^{n+1}-1)/(n+1)`).
2. At `n = p` the two `1/p` terms cancel `2/p`, so
   `-2/p + ∑_{k=1}^{p} 2^k/k = H_{p-1} + ∑_{k=1}^{p-1} C(p,k)/k`.
3. `C(p,k)/k = p·C(p-1,k-1)/k²` and `C(p-1,k-1) ≡ (-1)^(k-1) (mod p)`; the
   alternating sum `∑ (-1)^(k-1) k⁻²` vanishes mod `p` by pairing `k ↔ p-k`
   (`p` odd).  Hence the second sum is `p² · (integer)/((p-1)!)²`.
4. Wolstenholme's harmonic congruence `p² ∣ num H_{p-1}`
   (`NumberComplexity.Wolstenholme`) finishes; all denominators are coprime
   to `p`.  This answers A332786's question affirmatively.

Retrieval date: 2026-10-21.
-/
import Mathlib
import NumberComplexity.Wolstenholme

set_option autoImplicit false

namespace Candidates.A108866PrimeHalfOrdowski

open Finset

/-! ## Definitions mirroring the entry -/

/-- `A108866(n)`: the numerator (in lowest terms) of `∑_{k=1}^{n} 2^k/k`. -/
def a (n : ℕ) : ℤ := (∑ k ∈ Icc 1 n, (2 : ℚ) ^ k / (k : ℚ)).num

/-- Ordowski's quantity: the numerator (in lowest terms) of
`-2/n + ∑_{k=1}^{n} 2^k/k`. -/
def ordowskiNum (n : ℕ) : ℤ := ((∑ k ∈ Icc 1 n, (2 : ℚ) ^ k / (k : ℚ)) - 2 / (n : ℚ)).num

/-! ## Ground truth -/

example : a 0 = 0 := by simp [a]

example : a 1 = 2 := by
  rw [a, show (∑ k ∈ Icc (1 : ℕ) 1, (2 : ℚ) ^ k / (k : ℚ)) =
      ((2 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : a 2 = 4 := by
  rw [a, show (∑ k ∈ Icc (1 : ℕ) 2, (2 : ℚ) ^ k / (k : ℚ)) =
      ((4 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : a 3 = 20 := by
  rw [a, show (∑ k ∈ Icc (1 : ℕ) 3, (2 : ℚ) ^ k / (k : ℚ)) =
      ((20 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : a 4 = 32 := by
  rw [a, show (∑ k ∈ Icc (1 : ℕ) 4, (2 : ℚ) ^ k / (k : ℚ)) =
      ((32 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : a 5 = 256 := by
  rw [a, show (∑ k ∈ Icc (1 : ℕ) 5, (2 : ℚ) ^ k / (k : ℚ)) =
      ((256 : ℤ) : ℚ) / ((15 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : a 6 = 416 := by
  rw [a, show (∑ k ∈ Icc (1 : ℕ) 6, (2 : ℚ) ^ k / (k : ℚ)) =
      ((416 : ℤ) : ℚ) / ((15 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : a 7 = 4832 := by
  rw [a, show (∑ k ∈ Icc (1 : ℕ) 7, (2 : ℚ) ^ k / (k : ℚ)) =
      ((4832 : ℤ) : ℚ) / ((105 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

/-! Ordowski's quantity at small `n`: `p = 5` and `p = 7` (where even `7³` divides),
the boundary prime `p = 3` (`9 ∤ 6`), and the composite `n = 4`. -/

example : ordowskiNum 3 = 6 := by
  rw [ordowskiNum, show ((∑ k ∈ Icc (1 : ℕ) 3, (2 : ℚ) ^ k / (k : ℚ)) - 2 / ((3 : ℕ) : ℚ)) =
      ((6 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : ordowskiNum 4 = 61 := by
  rw [ordowskiNum, show ((∑ k ∈ Icc (1 : ℕ) 4, (2 : ℚ) ^ k / (k : ℚ)) - 2 / ((4 : ℕ) : ℚ)) =
      ((61 : ℤ) : ℚ) / ((6 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : ordowskiNum 5 = 50 := by
  rw [ordowskiNum, show ((∑ k ∈ Icc (1 : ℕ) 5, (2 : ℚ) ^ k / (k : ℚ)) - 2 / ((5 : ℕ) : ℚ)) =
      ((50 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

example : ordowskiNum 7 = 686 := by
  rw [ordowskiNum, show ((∑ k ∈ Icc (1 : ℕ) 7, (2 : ℚ) ^ k / (k : ℚ)) - 2 / ((7 : ℕ) : ℚ)) =
      ((686 : ℤ) : ℚ) / ((15 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

/-- The bound `5 ≤ p` is necessary: at `p = 3`, `9 ∤ 6`. -/
example : ¬ (3 : ℤ) ^ 2 ∣ ordowskiNum 3 := by
  rw [show ordowskiNum 3 = 6 by
    rw [ordowskiNum, show ((∑ k ∈ Icc (1 : ℕ) 3, (2 : ℚ) ^ k / (k : ℚ)) - 2 / ((3 : ℕ) : ℚ)) =
        ((6 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) by norm_num [Finset.sum_Icc_succ_top]]
    exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)]
  decide

/-! ## Proof -/

/-- Reindexing: `∑_{k=1}^{n} f k = ∑_{k=0}^{n-1} f (k+1)`. -/
theorem sum_Icc_one_eq_sum_range (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  rw [range_eq_Ico, sum_Ico_add' f 0 n 1]
  rfl

/-- `∑_{k=0}^{n} C(n,k)/(k+1) = (2^{n+1} - 1)/(n+1)`, from
`(n+1)·C(n,k) = (k+1)·C(n+1,k+1)` and `∑_k C(n+1,k) = 2^{n+1}`. -/
theorem sum_choose_succ_div (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n.choose k : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) =
      ((2 : ℚ) ^ (n + 1) - 1) / ((n + 1 : ℕ) : ℚ) := by
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hterm : ∀ k ∈ range (n + 1), ((n.choose k : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) =
      (((n + 1).choose (k + 1) : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) := by
    intro k _
    have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h := Nat.add_one_mul_choose_eq n k
    rw [div_eq_div_iff hk hn]
    exact_mod_cast (by rw [mul_comm]; linarith [h] : n.choose k * (n + 1) = (n + 1).choose (k + 1) * (k + 1))
  rw [sum_congr rfl hterm, ← sum_div]
  congr 1
  have hs := Nat.sum_range_choose (n + 1)
  rw [sum_range_succ'] at hs
  have hs' : ((∑ k ∈ range (n + 1), (n + 1).choose (k + 1) : ℕ) : ℚ) + 1 = 2 ^ (n + 1) := by
    exact_mod_cast (by simpa using hs)
  push_cast at hs' ⊢
  linarith

/-- Range form of the identity `∑_{k=1}^{n} 2^k/k = H_n + ∑_{k=1}^{n} C(n,k)/k`. -/
theorem sum_two_pow_div_eq (n : ℕ) :
    ∑ k ∈ range n, (2 : ℚ) ^ (k + 1) / ((k + 1 : ℕ) : ℚ) =
      harmonic n + ∑ k ∈ range n, ((n.choose (k + 1) : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpascal : ∑ k ∈ range (n + 1), (((n + 1).choose (k + 1) : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) =
        ∑ k ∈ range (n + 1), ((n.choose k : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) +
          ∑ k ∈ range n, ((n.choose (k + 1) : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) := by
      have hext : ∑ k ∈ range n, ((n.choose (k + 1) : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) =
          ∑ k ∈ range (n + 1), ((n.choose (k + 1) : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) := by
        rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_div, add_zero]
      rw [hext, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.choose_succ_succ', Nat.cast_add, add_div]
    rw [hpascal, sum_choose_succ_div, sum_range_succ, ih, harmonic_succ]
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
    ring

/-- If `q = A/D` with `D ≠ 0`, `m ∣ A` and `m` coprime to `D`, then `m` divides the
numerator of `q` in lowest terms. -/
theorem dvd_num_of_eq_div (q : ℚ) (A D m : ℤ) (hD : D ≠ 0) (hq : q = (A : ℚ) / (D : ℚ))
    (hm : m ∣ A) (hcop : IsCoprime m D) : m ∣ q.num := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hden0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hcross : q.num * D = A * (q.den : ℤ) := by
    have h : (q.num : ℚ) / (q.den : ℚ) = (A : ℚ) / (D : ℚ) := by rw [Rat.num_div_den, hq]
    rw [div_eq_div_iff hden0 hD'] at h
    exact_mod_cast h
  have hdvd : m ∣ q.num * D := by rw [hcross]; exact Dvd.dvd.mul_right hm _
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- For an odd prime `p`, `∑_{k=1}^{p-1} (-1)^(k-1) k⁻² = 0` in `ZMod p`: the reflection
`k ↦ p - k` negates every term because `p` is odd. -/
theorem sum_neg_one_pow_mul_inv_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ k ∈ Ico 1 p, (-1 : ZMod p) ^ (k - 1) * ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  haveI := Fact.mk hp
  set s := ∑ k ∈ Ico 1 p, (-1 : ZMod p) ^ (k - 1) * ((k : ZMod p)⁻¹) ^ 2 with hs
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hrefl : s = ∑ k ∈ Ico 1 p, (-1 : ZMod p) ^ (p - k - 1) * (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 := by
    rw [hs]
    apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
    · intro k hk; simp only [mem_Ico] at hk ⊢; omega
    · intro k hk; simp only [mem_Ico] at hk ⊢; omega
    · intro k hk; simp only [mem_Ico] at hk; omega
    · intro k hk; simp only [mem_Ico] at hk; omega
    · intro k hk
      simp only [mem_Ico] at hk
      rw [show p - (p - k) = k by omega]
  have hneg : ∀ k ∈ Ico 1 p, (-1 : ZMod p) ^ (p - k - 1) * (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 =
      -((-1 : ZMod p) ^ (k - 1) * ((k : ZMod p)⁻¹) ^ 2) := by
    intro k hk
    simp only [mem_Ico] at hk
    have hcast : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
      rw [Nat.cast_sub hk.2.le, ZMod.natCast_self, zero_sub]
    have hpow : (-1 : ZMod p) ^ (p - k - 1) = -(-1 : ZMod p) ^ (k - 1) := by
      obtain ⟨m, hm⟩ := hodd
      have he : p - k - 1 + (k - 1) = 2 * (m - 1) + 1 := by omega
      have h1 : (-1 : ZMod p) ^ (p - k - 1) * (-1 : ZMod p) ^ (k - 1) = -1 := by
        rw [← pow_add, he, pow_succ, pow_mul]; simp
      have h2 : (-1 : ZMod p) ^ (k - 1) * (-1 : ZMod p) ^ (k - 1) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      linear_combination (-1 : ZMod p) ^ (k - 1) * h1 - (-1 : ZMod p) ^ (p - k - 1) * h2
    rw [hcast, hpow, inv_neg, neg_sq]
    ring
  have hss : s = -s := by
    calc s = _ := hrefl
      _ = -s := by rw [sum_congr rfl hneg, sum_neg_distrib]
  have h2s : (2 : ZMod p) * s = 0 := by linear_combination hss
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact hp2 this
  exact (mul_eq_zero.mp h2s).resolve_left h20

/-- **Identity.** `∑_{k=1}^{n} 2^k/k = H_n + ∑_{k=1}^{n} C(n,k)/k` in `ℚ`. -/
theorem sum_Icc_two_pow_div (n : ℕ) :
    ∑ k ∈ Icc 1 n, (2 : ℚ) ^ k / (k : ℚ) =
      harmonic n + ∑ k ∈ Icc 1 n, ((n.choose k : ℕ) : ℚ) / (k : ℚ) := by
  rw [sum_Icc_one_eq_sum_range, sum_Icc_one_eq_sum_range]
  exact sum_two_pow_div_eq n

/-- For an odd prime `p`, `p ∣ ∑_{k=1}^{p-1} C(p-1,k-1)·((p-1)!/k)²`: modulo `p` the sum is
`((p-1)!)² ∑ (-1)^(k-1) k⁻² = 0`. -/
theorem dvd_sum_choose_mul_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ ∑ k ∈ Ico 1 p, (p - 1).choose (k - 1) * ((p - 1).factorial / k) ^ 2 := by
  haveI := Fact.mk hp
  set N := (p - 1).factorial with hN
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
  have hterm : ∀ k ∈ Ico 1 p, (((p - 1).choose (k - 1) * (N / k) ^ 2 : ℕ) : ZMod p) =
      (N : ZMod p) ^ 2 * ((-1 : ZMod p) ^ (k - 1) * ((k : ZMod p)⁻¹) ^ 2) := by
    intro k hk
    have hk' := mem_Ico.mp hk
    have hk0 : (k : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd hk'.1 hd
      omega
    have hdvd : k ∣ N := Nat.dvd_factorial hk'.1 (by omega)
    have hNk : ((N / k : ℕ) : ZMod p) = (N : ZMod p) * (k : ZMod p)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hk0, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    rw [Nat.cast_mul, Nat.cast_pow, NumberComplexity.Wolstenholme.choose_pred_cast_zmod hp (k - 1) (by omega), hNk]
    ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_neg_one_pow_mul_inv_sq hp hp2, mul_zero]

/-- **Prime half of Ordowski's conjecture (A108866, Thomas Ordowski, Mar 02 2020;
also stated in A330718 and A332786).**  For every prime `p ≥ 5`, `p²` divides the numerator
(in lowest terms) of `-2/p + ∑_{k=1}^{p} 2^k/k`.  Proof: the quantity equals
`H_{p-1} + ∑_{k=1}^{p-1} C(p,k)/k`; the second sum is `p²·(integer)/((p-1)!)²` and
Wolstenholme gives `p² ∣ num H_{p-1}`. -/
theorem sq_dvd_num_sum_two_pow_div_sub {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ ((∑ k ∈ Icc 1 p, (2 : ℚ) ^ k / (k : ℚ)) - 2 / (p : ℚ)).num := by
  set N := (p - 1).factorial with hN
  set S := ∑ k ∈ Ico 1 p, N / k with hS
  set C := ∑ k ∈ Ico 1 p, (p - 1).choose (k - 1) * (N / k) ^ 2 with hC
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hIcc : Icc 1 p = Ico 1 (p + 1) := by ext k; simp only [mem_Icc, mem_Ico]; omega
  have hharm : harmonic p = harmonic (p - 1) + 1 / (p : ℚ) := by
    have h := harmonic_succ (p - 1)
    rw [show p - 1 + 1 = p by have := hp.pos; omega] at h
    rw [h, one_div]
  have hchoose : ∑ k ∈ Ico 1 p, ((p.choose k : ℕ) : ℚ) / (k : ℚ) = (p : ℚ) * (C : ℚ) / (N : ℚ) ^ 2 := by
    rw [hC, Nat.cast_sum, mul_sum, sum_div]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_Ico.mp hk
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hdvd : k ∣ N := Nat.dvd_factorial hk'.1 (by omega)
    have hNk : ((N / k : ℕ) : ℚ) * (k : ℚ) = (N : ℚ) := by exact_mod_cast Nat.div_mul_cancel hdvd
    have hkc : (k : ℚ) * ((p.choose k : ℕ) : ℚ) = (p : ℚ) * (((p - 1).choose (k - 1) : ℕ) : ℚ) := by
      have h := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
      rw [show p - 1 + 1 = p by omega, show k - 1 + 1 = k by omega] at h
      exact_mod_cast (by rw [h, mul_comm] : k * p.choose k = p * (p - 1).choose (k - 1))
    rw [div_eq_div_iff hk0 (pow_ne_zero 2 hN0), ← hNk]
    push_cast
    linear_combination (((N / k : ℕ) : ℚ)) ^ 2 * (k : ℚ) * hkc
  have hT : (∑ k ∈ Icc 1 p, (2 : ℚ) ^ k / (k : ℚ)) - 2 / (p : ℚ) =
      ((N * S + p * C : ℕ) : ℤ) / (((N ^ 2 : ℕ) : ℤ) : ℚ) := by
    rw [sum_Icc_two_pow_div, hharm, hIcc, sum_Ico_succ_top (by omega), Nat.choose_self,
      hchoose, NumberComplexity.Wolstenholme.harmonic_eq_sum_div_factorial hp, ← hN, ← hS]
    push_cast
    field_simp
    ring
  have hSdvd : p ^ 2 ∣ S := NumberComplexity.Wolstenholme.sq_dvd_sum_factorial_div hp h5
  have hCdvd : p ∣ C := dvd_sum_choose_mul_sq hp (by omega)
  have hAdvd : p ^ 2 ∣ N * S + p * C :=
    dvd_add (Dvd.dvd.mul_left hSdvd N) (by rw [pow_two]; exact Nat.mul_dvd_mul_left p hCdvd)
  have hcop : Nat.Coprime (p ^ 2) (N ^ 2) := by
    apply Nat.Coprime.pow
    rw [Nat.Prime.coprime_iff_not_dvd hp, Nat.Prime.dvd_factorial hp]
    omega
  refine dvd_num_of_eq_div _ _ _ _ ?_ hT ?_ ?_
  · exact_mod_cast (pow_pos (Nat.factorial_pos (p - 1)) 2).ne'
  · exact_mod_cast hAdvd
  · rw [← Nat.cast_pow]; exact Nat.isCoprime_iff_coprime.mpr hcop

/-- **Prime half of Ordowski's conjecture**, stated with the entry-level definition:
for every prime `p ≥ 5`, `p² ∣ ordowskiNum p`. -/
theorem sq_dvd_ordowskiNum {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ ordowskiNum p :=
  sq_dvd_num_sum_two_pow_div_sub hp h5

/-- Non-vacuity: the hypotheses hold at `p = 5`, where `ordowskiNum 5 = 50 = 2·5²`. -/
example : (5 : ℤ) ^ 2 ∣ ordowskiNum 5 := sq_dvd_ordowskiNum (by norm_num) le_rfl

end Candidates.A108866PrimeHalfOrdowski
