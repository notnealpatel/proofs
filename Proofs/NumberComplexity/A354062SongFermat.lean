/-
# A354062 — Song: Fermat-number divisibility of `Li_{-2^n}(1/3)` (refuted)

Jianing Song's conjecture in OEIS A354062 (2022):
`a(n)=Li_{-2^n}(1/3)=Σ_{k≥1} k^(2^n)/3^k` should be divisible by
`F_k=2^(2^k)+1` for `n ≥ 2^max(k,1)`. The entry starts at `n=2`.

* `not_songConjecture`: the conjecture is false.  For every
  integer `z` with `a 32 = z`, `641 ∤ z`, hence `F_5 = 641 · 6700417 ∤ z`
  (`not_641_dvd_of_a_eq`, and more generally `not_641_dvd_of_seven_le`
  for every `n ≥ 7`).
* `fermatNumber_dvd_of_prime`: the true part, for every prime Fermat number
  `F_k` (`k ≥ 1`) and every `n ≥ 2^k`, any integer value of `a n` is divisible
  by `F_k` (this covers `F_1, …, F_4`).

Method.  Newton's forward-difference formula gives
`k^m = ∑_{j ≤ m} C(k,j) d(m,j)` with `d(m,j) = j! S(m,j)`, and
`∑_k C(k,j) 3^{-k} = 3 / 2^{j+1}`, so
`2^{m+1} · ∑_{k≥0} k^m/3^k = 3 · N(m)` with `N(m) = ∑_j d(m,j) 2^{m-j} ∈ ℤ`.
Modulo an odd prime `p`, `d(m,j) ≡ 0` for `j ≥ p` (the `p`-th forward
difference of a `p`-periodic function vanishes in characteristic `p`) and
`∑_{j<p} d(m,j) 2^{p-1-j} ≡ ∑_{i<p} i^m 3^{p-1-i}`
(using `(-1)^t C(i+t,i) ≡ C(p-1-i,t)`), whence
`2^p · a ≡ 3 · ∑_{i<p} i^m 3^{p-1-i} (mod p)`.  For `p = 641`, `m = 2^32`
the right-hand sum is `≡ 43`, evaluated by `decide +kernel`.

## Definitional fidelity

* `a n` is the real series `∑_{k ≥ 1} k^(2^n) / 3^k` of the FORMULA line,
  written as a `tsum` over `k + 1`, `k : ℕ`; it is summable
  (`hasSum_a`), so the `tsum` is not the junk value.
* "a(n) is divisible by F_k" is formalized as "a(n) is an integer `z` with
  `F_k ∣ z`".  The refutation is stronger than the negation of that: it
  shows *no* integer equal to `a 32` is divisible by `641`, so it does not
  depend on integrality (Aloff's theorem is not formalized here).
* `Nat.fermatNumber k = 2 ^ 2 ^ k + 1` is Mathlib's Fermat number.
-/
import Mathlib

set_option autoImplicit false

open Finset fwdDiff

namespace Candidates.A354062SongFermat

/-! ## Definitions -/

/-- `a n = Li_{-2^n}(1/3) = ∑_{k ≥ 1} k^(2^n) / 3^k` (A354062, FORMULA line). -/
noncomputable def a (n : ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 ^ n) / 3 ^ (k + 1)

/-- Song's conjecture (A354062): for every `k ≥ 0` and every `n ≥ 2^max(k,1)`,
`a n` is an integer divisible by the Fermat number `F_k = 2^2^k + 1`. -/
def SongConjecture : Prop :=
  ∀ k n : ℕ, 2 ^ max k 1 ≤ n → ∃ z : ℤ, a n = z ∧ (Nat.fermatNumber k : ℤ) ∣ z

/-- `d m j = ∑_{i ≤ j} (-1)^(j-i) C(j,i) i^m`, the `j`-th forward difference of
`r ↦ r^m` at `0` (equal to `j! S(m,j)`). -/
def d (m j : ℕ) : ℤ := ∑ i ∈ range (j + 1), (-1) ^ (j - i) * (j.choose i : ℤ) * (i : ℤ) ^ m

/-- `N m = ∑_{j ≤ m} d(m,j) 2^(m-j)`; `2^(m+1) ∑_{k≥0} k^m/3^k = 3 N m`. -/
def N (m : ℕ) : ℤ := ∑ j ∈ range (m + 1), d m j * 2 ^ (m - j)

/-! ## Newton expansion and the real series -/


/-- `d m j` is the `j`-th forward difference of `r ↦ r^m` at `0` (over `ℤ`, step `1`). -/
lemma d_eq_fwdDiff (m j : ℕ) : d m j = (Δ_[(1:ℤ)])^[j] (fun r : ℤ => r ^ m) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [d, mul_assoc]

/-- `d m j = 0` for `j > m` (`j! S(m,j) = 0`). -/
lemma d_eq_zero_of_lt {m j : ℕ} (h : m < j) : d m j = 0 := by
  rw [d_eq_fwdDiff, fwdDiff_iter_pow_eq_zero_of_lt h]
  rfl

/-- Newton's forward-difference expansion: `k^m = ∑_{j ≤ m} C(k,j) d(m,j)`. -/
lemma pow_eq_sum_choose_mul_d (m k : ℕ) :
    (k : ℤ) ^ m = ∑ j ∈ range (m + 1), (k.choose j : ℤ) * d m j := by
  have h := shift_eq_sum_fwdDiff_iter (h := (1:ℤ)) (fun r : ℤ => r ^ m) k 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  rw [h]
  have hk : ∑ j ∈ range (k + 1), (k.choose j : ℤ) * (Δ_[(1:ℤ)])^[j] (fun r : ℤ => r ^ m) 0
      = ∑ j ∈ range (k + m + 1), (k.choose j : ℤ) * d m j := by
    rw [← Finset.sum_subset (range_subset_range.2 (by omega : k + 1 ≤ k + m + 1))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [d_eq_fwdDiff]
    · intro j _ hj
      simp only [mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [hk, ← Finset.sum_subset (range_subset_range.2 (by omega : m + 1 ≤ k + m + 1))]
  intro j _ hj
  simp only [mem_range, not_lt] at hj
  rw [d_eq_zero_of_lt (by omega), mul_zero]

/-- `∑_{k ≥ 0} C(k,j) 3^{-k} = 3 / 2^(j+1)`. -/
lemma hasSum_choose_mul_third (j : ℕ) :
    HasSum (fun k : ℕ => (k.choose j : ℝ) * (1 / 3 : ℝ) ^ k) (3 / 2 ^ (j + 1)) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) j (r := 1 / 3) (by norm_num)
  have h2 := h.mul_left ((1 / 3 : ℝ) ^ j)
  rw [← hasSum_nat_add_iff' j]
  have hz : ∑ i ∈ range j, ((i.choose j : ℕ) : ℝ) * (1 / 3 : ℝ) ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Nat.choose_eq_zero_of_lt (mem_range.1 hi)]; simp
  rw [hz, sub_zero]
  have hf : (fun n : ℕ => (((n + j).choose j : ℕ) : ℝ) * (1 / 3 : ℝ) ^ (n + j))
      = fun n : ℕ => (1 / 3 : ℝ) ^ j * ((((n + j).choose j : ℕ) : ℝ) * (1 / 3 : ℝ) ^ n) := by
    funext n
    rw [pow_add]; ring
  have hv : (3 : ℝ) / 2 ^ (j + 1) = (1 / 3 : ℝ) ^ j * (1 / (1 - 1 / 3) ^ (j + 1)) := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, div_pow, div_pow, one_pow, pow_succ, pow_succ]
    field_simp
  rw [hf, hv]
  exact h2


/-! ## Reduction modulo a prime -/


/-- In characteristic `p` (odd prime), the `p`-th forward difference of the
`p`-periodic function `i ↦ (i : ZMod p)^m` vanishes. -/
lemma fwdDiff_iter_prime_eq_zero (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (Δ_[(1:ℕ)])^[p] (fun i : ℕ => ((i : ZMod p)) ^ m) = 0 := by
  funext y
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [fwdDiff_iter_eq_sum_shift, sum_range_succ,
    show range p = range (p - 1 + 1) by rw [Nat.sub_add_cancel hp1], sum_range_succ']
  have hmid : ∑ k ∈ range (p - 1), ((-1 : ℤ) ^ (p - (k + 1)) * (p.choose (k + 1) : ℤ)) •
      ((((y + (k + 1) • 1 : ℕ)) : ZMod p) ^ m) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk' : k + 1 < p := by have hk0 := mem_range.1 hk; omega
    have hdvd : (p.choose (k + 1) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2
        ((Fact.out : p.Prime).dvd_choose_self (by omega) hk')
    rw [zsmul_eq_mul]
    push_cast
    rw [hdvd]; ring
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  rw [hmid]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, one_smul,
    Nat.sub_zero, Nat.choose_zero_right, smul_eq_mul, hodd.neg_one_pow, zero_add]
  push_cast
  simp

/-- The image of `d m j` in `ZMod p` is the `j`-th forward difference of `i ↦ (i : ZMod p)^m`. -/
lemma d_cast_eq_fwdDiff (p m j : ℕ) :
    (d m j : ZMod p) = (Δ_[(1:ℕ)])^[j] (fun i : ℕ => ((i : ZMod p)) ^ m) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [d, mul_assoc, zsmul_eq_mul]

/-- `d m j ≡ 0 (mod p)` for an odd prime `p ≤ j`. -/
lemma d_cast_eq_zero (p m j : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hj : p ≤ j) :
    (d m j : ZMod p) = 0 := by
  rw [d_cast_eq_fwdDiff, show j = (j - p) + p by omega, Function.iterate_add_apply,
    fwdDiff_iter_prime_eq_zero p m hp2]
  have h0 : (Δ_[(1:ℕ)]) (0 : ℕ → ZMod p) = 0 := by
    funext y; simp [fwdDiff]
  rw [Function.iterate_fixed h0]
  rfl

/-- `(-1)^t C(i+t, i) ≡ C(p-1-i, t) (mod p)` whenever `i + t < p`. -/
lemma choose_neg_one_pow_cast (p i : ℕ) [Fact p.Prime] :
    ∀ t : ℕ, i + t < p →
      ((-1 : ZMod p) ^ t * ((i + t).choose i : ℕ) : ZMod p) = ((p - 1 - i).choose t : ℕ) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hunit : ((t + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    apply mul_left_cancel₀ hunit
    have e1 : ((i + (t + 1)).choose i) * (t + 1) = ((i + t).choose i) * (i + t + 1) := by
      have h := Nat.choose_mul_succ_eq (i + t) i
      rw [show i + t + 1 - i = t + 1 by omega] at h
      rw [show i + (t + 1) = i + t + 1 by omega]
      exact h.symm
    have e2 : ((p - 1 - i).choose (t + 1)) * (t + 1) = ((p - 1 - i).choose t) * (p - 1 - i - t) :=
      Nat.choose_succ_right_eq _ _
    have e1' : (((i + (t + 1)).choose i : ℕ) : ZMod p) * ((t : ZMod p) + 1)
        = (((i + t).choose i : ℕ) : ZMod p) * ((i : ZMod p) + t + 1) := by
      have h := congrArg (Nat.cast : ℕ → ZMod p) e1
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h
    have e2' : (((p - 1 - i).choose (t + 1) : ℕ) : ZMod p) * ((t : ZMod p) + 1)
        = (((p - 1 - i).choose t : ℕ) : ZMod p) * ((p - 1 - i - t : ℕ) : ZMod p) := by
      have h := congrArg (Nat.cast : ℕ → ZMod p) e2
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h
    have e3 : ((p - 1 - i - t : ℕ) : ZMod p) + ((i : ZMod p) + t + 1) = 0 := by
      have h : (((p - 1 - i - t) + (i + t + 1) : ℕ) : ZMod p) = 0 := by
        rw [show (p - 1 - i - t) + (i + t + 1) = p by omega]
        exact ZMod.natCast_self p
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h
    push_cast
    linear_combination (-1 : ZMod p) ^ (t + 1) * e1' - e2' - ((i : ZMod p) + t + 1) * ih'
      - (((p - 1 - i).choose t : ℕ) : ZMod p) * e3

/-- `∑_{i ≤ j < p} (-1)^(j-i) C(j,i) 2^(p-1-j) ≡ 3^(p-1-i) (mod p)` for `i < p`. -/
lemma inner_sum_eq (p i : ℕ) [Fact p.Prime] (hi : i < p) :
    ∑ j ∈ Ico i p, (-1 : ZMod p) ^ (j - i) * ((j.choose i : ℕ) : ZMod p) * 2 ^ (p - 1 - j)
      = 3 ^ (p - 1 - i) := by
  rw [sum_Ico_eq_sum_range, show (3 : ZMod p) = 1 + 2 by norm_num, add_pow,
    show p - i = p - 1 - i + 1 by omega]
  refine sum_congr rfl fun k hk => ?_
  have hk' : i + k < p := by have hk0 := mem_range.1 hk; omega
  rw [show i + k - i = k by omega, choose_neg_one_pow_cast p i k hk', one_pow, one_mul,
    show p - 1 - (i + k) = p - 1 - i - k by omega]
  ring

/-- `∑_{j<p} d(m,j) 2^(p-1-j) ≡ ∑_{i<p} i^m 3^(p-1-i) (mod p)`. -/
lemma sum_d_mul_two_pow (p m : ℕ) [Fact p.Prime] :
    ∑ j ∈ range p, (d m j : ZMod p) * 2 ^ (p - 1 - j)
      = ∑ i ∈ range p, (i : ZMod p) ^ m * 3 ^ (p - 1 - i) := by
  have hL : ∑ j ∈ range p, (d m j : ZMod p) * 2 ^ (p - 1 - j)
      = ∑ j ∈ Ico 0 p, ∑ i ∈ Ico 0 (j + 1),
          (i : ZMod p) ^ m * ((-1 : ZMod p) ^ (j - i) * ((j.choose i : ℕ) : ZMod p)
            * 2 ^ (p - 1 - j)) := by
    rw [← range_eq_Ico]
    refine sum_congr rfl fun j _ => ?_
    rw [← range_eq_Ico, d]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hL, ← sum_Ico_Ico_comm, ← range_eq_Ico]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_sum, inner_sum_eq p i (mem_range.1 hi)]


/-! ## The integer identity `2^(m+1) · ∑ k^m/3^k = 3 N(m)` -/

/-- `∑_{k ≥ 0} k^m / 3^k = 3 N(m) / 2^(m+1)`. -/
lemma hasSum_pow_div_three_pow (m : ℕ) :
    HasSum (fun k : ℕ => (k : ℝ) ^ m / 3 ^ k) (3 * N m / 2 ^ (m + 1)) := by
  have h := hasSum_sum (s := range (m + 1)) fun j _ =>
    (hasSum_choose_mul_third j).mul_right (d m j : ℝ)
  have hf : (fun k : ℕ => (k : ℝ) ^ m / 3 ^ k)
      = fun k : ℕ => ∑ j ∈ range (m + 1), (k.choose j : ℝ) * (1 / 3 : ℝ) ^ k * (d m j : ℝ) := by
    funext k
    have hk := congrArg (Int.cast : ℤ → ℝ) (pow_eq_sum_choose_mul_d m k)
    push_cast at hk
    rw [hk, div_eq_mul_one_div, one_div_pow, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    ring
  have hv : (3 : ℝ) * N m / 2 ^ (m + 1) = ∑ j ∈ range (m + 1), 3 / 2 ^ (j + 1) * (d m j : ℝ) := by
    rw [N]
    push_cast
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have h2 : (2 : ℝ) ^ (m + 1) = 2 ^ (m - j) * 2 ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h2]
    field_simp
  rw [hf, hv]
  exact h

/-- `a n = 3 N(2^n) / 2^(2^n+1)`, with the series summable. -/
lemma hasSum_a (n : ℕ) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ (2 ^ n) / 3 ^ (k + 1))
      ((3 : ℝ) * N (2 ^ n) / 2 ^ (2 ^ n + 1)) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_pow_div_three_pow (2 ^ n))
  have h0 : (2 ^ n : ℕ) ≠ 0 := by positivity
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_pow h0, zero_div, sub_zero,
    Nat.cast_add, Nat.cast_one] at h
  exact h

/-- `a n = 3 N(2^n) / 2^(2^n+1)`. -/
lemma a_eq (n : ℕ) : a n = (3 : ℝ) * N (2 ^ n) / 2 ^ (2 ^ n + 1) := (hasSum_a n).tsum_eq

/-- If `a n = z` with `z ∈ ℤ`, then `2^(2^n+1) z = 3 N(2^n)`. -/
lemma two_pow_mul_eq_of_a_eq (n : ℕ) (z : ℤ) (hz : a n = z) :
    2 ^ (2 ^ n + 1) * z = 3 * N (2 ^ n) := by
  rw [a_eq] at hz
  have h2 : (2 : ℝ) ^ (2 ^ n + 1) ≠ 0 := by positivity
  have h : ((2 ^ (2 ^ n + 1) * z : ℤ) : ℝ) = ((3 * N (2 ^ n) : ℤ) : ℝ) := by
    push_cast
    rw [← hz]
    field_simp
  exact_mod_cast h

/-! ## The congruence `2^p · a ≡ 3 ∑_{i<p} i^m 3^(p-1-i) (mod p)` -/

/-- A natural number not divisible by `p` has nonzero image in `ZMod p`. -/
lemma natCast_ne_zero_of_not_dvd (p n : ℕ) (h : ¬ p ∣ n) : (n : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.natCast_eq_zero_iff]

/-- `2^(p-1-m) N(m) ≡ 2^(m+1-p) ∑_{i<p} i^m 3^(p-1-i) (mod p)` for an odd prime `p`
(one of the two exponents is `0`). -/
lemma N_cast_eq (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (p - 1 - m) * (N m : ZMod p)
      = 2 ^ (m + 1 - p) * ∑ i ∈ range p, (i : ZMod p) ^ m * 3 ^ (p - 1 - i) := by
  rw [← sum_d_mul_two_pow, N, mul_sum, Int.cast_sum, mul_sum]
  push_cast
  rcases le_or_gt p (m + 1) with hpm | hpm
  · rw [← sum_subset (range_subset_range.2 hpm)]
    · refine sum_congr rfl fun j hj => ?_
      have hjp := mem_range.1 hj
      rw [show p - 1 - m = 0 by omega, show m - j = (m + 1 - p) + (p - 1 - j) by omega,
        pow_add]
      ring
    · intro j _ hj
      rw [d_cast_eq_zero p m j hp2 (by simpa using hj), zero_mul, mul_zero]
  · rw [← sum_subset (range_subset_range.2 hpm.le)]
    · refine sum_congr rfl fun j hj => ?_
      have hjm := mem_range.1 hj
      rw [show m + 1 - p = 0 by omega, show p - 1 - j = (p - 1 - m) + (m - j) by omega,
        pow_add]
      ring
    · intro j _ hj
      have hj' : m < j := by simpa using hj
      rw [d_eq_zero_of_lt hj', Int.cast_zero, zero_mul, mul_zero]

/-- **Key congruence.** If `a n = z ∈ ℤ` and `p` is an odd prime, then
`2^p z ≡ 3 ∑_{i<p} i^(2^n) 3^(p-1-i) (mod p)`. -/
lemma two_pow_mul_cast_eq (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (z : ℤ) (hz : a n = z) :
    (2 : ZMod p) ^ p * z = 3 * ∑ i ∈ range p, (i : ZMod p) ^ (2 ^ n) * 3 ^ (p - 1 - i) := by
  have h := congrArg (Int.cast : ℤ → ZMod p) (two_pow_mul_eq_of_a_eq n z hz)
  push_cast at h
  have hN := N_cast_eq p (2 ^ n) hp2
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h2' := natCast_ne_zero_of_not_dvd p 2 fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 hd)
    exact_mod_cast h2'
  have hpow : (2 : ZMod p) ^ (p - 1 - 2 ^ n) * 2 ^ (2 ^ n + 1)
      = 2 ^ (2 ^ n + 1 - p) * 2 ^ p := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  apply mul_left_cancel₀ (pow_ne_zero (2 ^ n + 1 - p) h2)
  linear_combination (2 : ZMod p) ^ (p - 1 - 2 ^ n) * h + 3 * hN - (z : ZMod p) * hpow

/-- For a prime `p ∉ {2, 3}` and `a n = z ∈ ℤ`: `p ∣ z ↔ ∑_{i<p} i^(2^n) 3^(p-1-i) ≡ 0`. -/
lemma dvd_iff_sum_eq_zero (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (z : ℤ)
    (hz : a n = z) :
    (p : ℤ) ∣ z ↔ ∑ i ∈ range p, (i : ZMod p) ^ (2 ^ n) * 3 ^ (p - 1 - i) = 0 := by
  have hkey := two_pow_mul_cast_eq p n hp2 z hz
  have hprime : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h2' := natCast_ne_zero_of_not_dvd p 2 fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 hd)
    exact_mod_cast h2'
  have h3 : (3 : ZMod p) ≠ 0 := by
    have h3' := natCast_ne_zero_of_not_dvd p 3 fun hd =>
      hp3 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).1 hd)
    exact_mod_cast h3'
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hz0
    rw [hz0, mul_zero] at hkey
    exact (mul_eq_zero.1 hkey.symm).resolve_left h3
  · intro hs
    rw [hs, mul_zero] at hkey
    exact (mul_eq_zero.1 hkey).resolve_left (pow_ne_zero p h2)

/-! ## Examples -/

example : N 4 = 160 := by decide +kernel

/-- Examples: `a 2 = 15`, the first listed term. -/
lemma a_two : a 2 = 15 := by
  rw [a_eq, show N (2 ^ 2) = 160 by decide +kernel]
  norm_num

/-- Examples: `a 3 = 17295`, the second listed term. -/
lemma a_three : a 3 = 17295 := by
  rw [a_eq, show N (2 ^ 3) = 2951680 by decide +kernel]
  norm_num


/-! ## Refutation at `p = 641`, a prime factor of `F_5` -/

/-- Fermat's little theorem in exponent form: in `ZMod p`, `x^e = x^f` whenever
`e ≡ f (mod p-1)` and `e, f ≥ 1`. -/
lemma pow_eq_pow_of_mod_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) {e f : ℕ} (he : 0 < e)
    (hf : 0 < f) (hef : e % (p - 1) = f % (p - 1)) : x ^ e = x ^ f := by
  by_cases hx : x = 0
  · rw [hx, zero_pow he.ne', zero_pow hf.ne']
  · rw [← Nat.div_add_mod e (p - 1), ← Nat.div_add_mod f (p - 1), pow_add, pow_add, pow_mul,
      pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_pow, hef]

/-- For `n ≥ 7`, `2^n mod 640` is one of `128, 256, 512, 384`. -/
lemma two_pow_mod_640 (n : ℕ) (hn : 7 ≤ n) :
    2 ^ n % 640 = 128 ∨ 2 ^ n % 640 = 256 ∨ 2 ^ n % 640 = 512 ∨ 2 ^ n % 640 = 384 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
    rw [pow_succ]
    omega

/-- Kernel-checked residues: `∑_{i<641} i^r 3^(640-i) ≢ 0 (mod 641)` for
`r ∈ {128, 256, 512, 384}` (the values are `48, 43, 145, 355`). -/
lemma sum_641_ne_zero (r : ℕ) (hr : r = 128 ∨ r = 256 ∨ r = 512 ∨ r = 384) :
    ∑ i ∈ range 641, (i : ZMod 641) ^ r * 3 ^ (641 - 1 - i) ≠ 0 := by
  have hcast : ∑ i ∈ range 641, (i : ZMod 641) ^ r * 3 ^ (641 - 1 - i)
      = ((∑ i ∈ range 641, i ^ r * 3 ^ (640 - i) : ℕ) : ZMod 641) := by
    push_cast
    rfl
  rw [hcast, Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel

/-- For every `n ≥ 7`, no integer equal to `a n` is divisible by `641`. -/
theorem not_641_dvd_of_seven_le (n : ℕ) (hn : 7 ≤ n) (z : ℤ) (hz : a n = z) :
    ¬ (641 : ℤ) ∣ z := by
  haveI : Fact (Nat.Prime 641) := ⟨by norm_num⟩
  have hiff := dvd_iff_sum_eq_zero 641 n (by norm_num) (by norm_num) z hz
  push_cast at hiff
  rw [hiff]
  have hpow : ∀ i : ℕ, (i : ZMod 641) ^ (2 ^ n) = (i : ZMod 641) ^ (2 ^ n % 640) := fun i => by
    have hr := two_pow_mod_640 n hn
    exact pow_eq_pow_of_mod_eq 641 _ (by positivity) (by omega) (by simp)
  simp_rw [hpow]
  exact sum_641_ne_zero _ (two_pow_mod_640 n hn)

/-- `F_5 = 641 · 6700417` does not divide any integer equal to `a 32`. -/
theorem not_fermatNumber_five_dvd (z : ℤ) (hz : a 32 = z) :
    ¬ (Nat.fermatNumber 5 : ℤ) ∣ z := by
  have hF : (641 : ℤ) ∣ (Nat.fermatNumber 5 : ℤ) := ⟨6700417, by norm_num [Nat.fermatNumber]⟩
  exact fun hdvd => not_641_dvd_of_seven_le 32 (by norm_num) z hz (hF.trans hdvd)

/-- **Song's conjecture (A354062) is false.**  The case `k = 5`, `n = 32`
(`n = 2^max(5,1)`) fails: `a 32` is not an integer divisible by `F_5`. -/
theorem not_songConjecture : ¬ SongConjecture := by
  intro h
  obtain ⟨z, hz, hdvd⟩ := h 5 32 (by norm_num)
  exact not_fermatNumber_five_dvd z hz hdvd


/-! ## The true part: prime Fermat numbers -/

/-- If `p ≥ 5` is prime and `p - 1 ∣ 2^n`, then `p` divides every integer equal to `a n`. -/
theorem prime_dvd_of_sub_one_dvd (p n : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hdvd : p - 1 ∣ 2 ^ n)
    (z : ℤ) (hz : a n = z) : (p : ℤ) ∣ z := by
  rw [dvd_iff_sum_eq_zero p n (by omega) (by omega) z hz]
  obtain ⟨c, hc⟩ := hdvd
  have hprime : p.Prime := Fact.out
  have hterm : ∀ i ∈ range (p - 1),
      ((i + 1 : ℕ) : ZMod p) ^ (2 ^ n) * 3 ^ (p - 1 - (i + 1)) = 3 ^ (p - 2 - i) := by
    intro i hi
    have hi' := mem_range.1 hi
    have hne : ((i + 1 : ℕ) : ZMod p) ≠ 0 :=
      natCast_ne_zero_of_not_dvd p (i + 1) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one hne, one_pow, one_mul,
      show p - 1 - (i + 1) = p - 2 - i by omega]
  have h0 : (2 ^ n : ℕ) ≠ 0 := by positivity
  rw [show range p = range (p - 1 + 1) by rw [Nat.sub_add_cancel (by omega : 1 ≤ p)],
    sum_range_succ']
  rw [sum_congr rfl hterm, Nat.cast_zero, zero_pow h0, zero_mul, add_zero]
  have hrefl : ∑ i ∈ range (p - 1), (3 : ZMod p) ^ (p - 2 - i) = ∑ i ∈ range (p - 1), 3 ^ i := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    congr 1
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h2' := natCast_ne_zero_of_not_dvd p 2 (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    exact_mod_cast h2'
  have h3 : (3 : ZMod p) ≠ 0 := by
    have h3' := natCast_ne_zero_of_not_dvd p 3 (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    exact_mod_cast h3'
  have hgeom := geom_sum_mul (3 : ZMod p) (p - 1)
  rw [ZMod.pow_card_sub_one_eq_one h3, sub_self, show (3 : ZMod p) - 1 = 2 by norm_num] at hgeom
  rw [hrefl]
  exact (mul_eq_zero.1 hgeom).resolve_right h2

/-- **True part of Song's conjecture.** If the Fermat number `F_k` (`k ≥ 1`) is prime,
then for every `n ≥ 2^k`, `F_k` divides every integer equal to `a n`.  This covers
`F_1, …, F_4 = 5, 17, 257, 65537`. -/
theorem fermatNumber_dvd_of_prime (k n : ℕ) (hk : 1 ≤ k) (hprime : (Nat.fermatNumber k).Prime)
    (hn : 2 ^ k ≤ n) (z : ℤ) (hz : a n = z) : (Nat.fermatNumber k : ℤ) ∣ z := by
  haveI : Fact (Nat.fermatNumber k).Prime := ⟨hprime⟩
  have h4 : 4 ≤ 2 ^ 2 ^ k := by
    calc 4 = 2 ^ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  refine prime_dvd_of_sub_one_dvd _ n (by rw [Nat.fermatNumber]; omega) ?_ z hz
  rw [Nat.fermatNumber, Nat.add_sub_cancel]
  exact Nat.pow_dvd_pow 2 hn

/-- Non-vacuity of `fermatNumber_dvd_of_prime`: at `k = 1`, `n = 2`, `z = a 2 = 15`,
all hypotheses hold and `F_1 = 5 ∣ 15`. -/
example : (Nat.fermatNumber 1 : ℤ) ∣ 15 :=
  fermatNumber_dvd_of_prime 1 2 le_rfl (by norm_num [Nat.fermatNumber]) (by norm_num) 15
    (by rw [a_two]; norm_num)

end Candidates.A354062SongFermat
