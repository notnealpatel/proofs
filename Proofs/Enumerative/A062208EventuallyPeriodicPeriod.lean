/-
# A062208 — Bala: congruences mod 60 and eventual periodicity with period dividing φ(k)

## OEIS source (retrieved with `oeis show A062208`, 2026-10-21)

```
NAME:     a(n) = Sum_{m>=0} binomial(m,3)^n*2^(-m-1).
TERMS:    1,1,63,16081,10681263,14638956721,35941784497263,143743469278461361,...
KEYWORDS: nonn,easy
COMMENT:  Number of alignments of n strings of length 3.
COMMENT (the conjecture):
  Conjectures: a(2*n) = 3 (mod 60) and a(2*n+1) = 1 (mod 60); for fixed k, the
  sequence a(n) (mod k) eventually becomes periodic with exact period a divisor of
  phi(k), where phi(k) is Euler's totient function A000010. - _Peter Bala_, Feb 04 2018
FORMULA:  a(n) = Sum_{k = 3..3*n} Sum_{i = 0..k} (-1)^(k-i)*binomial(k,i)*
          binomial(i,3)^n. Row sums of A299041. - _Peter Bala_, Feb 04 2018
```

## Status

Triage: open (no proof in the entry; no proof located in the literature by the triage).
The triage noted an Aug 2026 CUP Open Engage preprint (not peer reviewed) proving eventual
period `φ(k)` for weighted Stirling transforms and "two conjectures of Bala"; whether it
covers this sequence was not determined.

## Formalization

* `a n` is the entry's series, as a real `tsum`.
* `b n` is Bala's finite formula (summed over `j ≤ 3n`, which also gives `b 0 = 1`).
* `a_eq_b`: the series converges to `b n` (Newton's forward-difference expansion of
  `m ↦ C(m,3)^n` plus `∑_m C(m,j)/2^(m+1) = 1`).
* The even congruence `a(2n) ≡ 3` needs `n ≥ 1`: `a 0 = 1` (`not_a_zero_mod_sixty`).
* "Exact period a divisor of `φ k`" is stated as: there is a positive eventual period `p`
  dividing every positive eventual period, and `p ∣ φ k`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A062208EventuallyPeriodicPeriod

open Finset

/-- `delta n j` is the `j`-th forward difference at `0` of `m ↦ C(m,3)^n`. -/
def delta (n j : ℕ) : ℤ :=
  ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * (j.choose i : ℤ) * ((i.choose 3 : ℤ) ^ n)

/-- Bala's finite formula `b n = ∑_{j ≤ 3n} ∑_{i ≤ j} (-1)^(j-i) C(j,i) C(i,3)^n`. -/
def b (n : ℕ) : ℤ := ∑ j ∈ range (3 * n + 1), delta n j

/-- Ground truth `b 0 = 1` (first listed term). -/
lemma b_zero : b 0 = 1 := by decide
/-- Ground truth `b 1 = 1`. -/
lemma b_one : b 1 = 1 := by decide
/-- Ground truth `b 2 = 63`. -/
lemma b_two : b 2 = 63 := by decide
/-- Ground truth `b 3 = 16081`. -/
lemma b_three : b 3 = 16081 := by decide
/-- Ground truth `b 4 = 10681263`. -/
lemma b_four : b 4 = 10681263 := by decide
/-- Ground truth `b 5 = 14638956721`. -/
lemma b_five : b 5 = 14638956721 := by decide

/-- The function `m ↦ C(m,3)^n` on `ℕ`. -/
def g (n : ℕ) (m : ℕ) : ℤ := (m.choose 3 : ℤ) ^ n

/-- `delta n j` is the iterated forward difference `Δ^j (g n)` at `0`. -/
lemma delta_eq_fwdDiff (n j : ℕ) : delta n j = (fwdDiff 1)^[j] (g n) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [delta, g]

/-- Higher differences vanish: `delta n j = 0` for `3 n < j`. -/
lemma delta_eq_zero {n j : ℕ} (hj : 3 * n < j) : delta n j = 0 := by
  have hdeg : ((descPochhammer ℤ 3) ^ n).natDegree < j := by
    have h1 := Polynomial.natDegree_pow_le (p := descPochhammer ℤ 3) (n := n)
    rw [descPochhammer_natDegree] at h1
    omega
  have hzero := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at hzero
  have hval : ∀ i : ℕ, ((descPochhammer ℤ 3) ^ n).eval ((0:ℤ) + (i : ℕ) • (1:ℤ)) =
      6 ^ n * (i.choose 3 : ℤ) ^ n := by
    intro i
    rw [Polynomial.eval_pow]
    simp only [nsmul_eq_mul, mul_one, zero_add]
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    rw [mul_pow]
    norm_num [Nat.factorial]
  simp only [hval] at hzero
  have h6 : (6 : ℤ) ^ n * delta n j = 0 := by
    rw [delta, mul_sum, ← hzero]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    ring
  rcases mul_eq_zero.mp h6 with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · exact h

/-- Truncation independence: summing `delta n j` beyond `j = 3 n` adds nothing. -/
lemma sum_delta_eq_b {n J : ℕ} (hJ : 3 * n ≤ J) :
    ∑ j ∈ range (J + 1), delta n j = b n := by
  symm
  apply sum_subset
  · intro j hj
    simp only [mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [mem_range, not_lt] at hj
    exact delta_eq_zero (by omega)

/-- Newton's forward-difference expansion: `C(m,3)^n = ∑_{j ≤ 3n} C(m,j) · delta n j`. -/
lemma choose_pow_eq_sum (n m : ℕ) :
    (m.choose 3 : ℤ) ^ n = ∑ j ∈ range (3 * n + 1), (m.choose j : ℤ) * delta n j := by
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) (g n) m 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at h
  simp only [← delta_eq_fwdDiff] at h
  have h1 : ∑ j ∈ range (m + 1), (m.choose j : ℤ) * delta n j =
      ∑ j ∈ range (m + 3 * n + 1), (m.choose j : ℤ) * delta n j := by
    apply sum_subset
    · intro j hj
      simp only [mem_range] at hj ⊢
      omega
    · intro j _ hj
      simp only [mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have h2 : ∑ j ∈ range (3 * n + 1), (m.choose j : ℤ) * delta n j =
      ∑ j ∈ range (m + 3 * n + 1), (m.choose j : ℤ) * delta n j := by
    apply sum_subset
    · intro j hj
      simp only [mem_range] at hj ⊢
      omega
    · intro j _ hj
      simp only [mem_range, not_lt] at hj
      rw [delta_eq_zero (by omega), mul_zero]
  rw [h2, ← h1, ← h]
  rfl

/-- If `x^(n+P) ≡ x^n (mod k)` for every integer `x`, then `b (n+P) ≡ b n (mod k)`. -/
lemma b_dvd_sub_of_pow {k n P : ℕ} (hpow : ∀ x : ℤ, (k : ℤ) ∣ x ^ (n + P) - x ^ n) :
    (k : ℤ) ∣ b (n + P) - b n := by
  rw [← sum_delta_eq_b (n := n) (J := 3 * (n + P)) (by omega), b, ← sum_sub_distrib]
  refine dvd_sum fun j _ => ?_
  rw [delta, delta, ← sum_sub_distrib]
  refine dvd_sum fun i _ => ?_
  rw [← mul_sub]
  exact Dvd.dvd.mul_left (hpow _) _

/-- Euler-type power congruence: for `n` at least every prime exponent of `k`,
`x^(n + φ k) ≡ x^n (mod k)`. -/
lemma dvd_pow_add_totient_sub {k n : ℕ} (hk : 0 < k) (hn : ∀ p : ℕ, k.factorization p ≤ n)
    (x : ℤ) : (k : ℤ) ∣ x ^ (n + k.totient) - x ^ n := by
  rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p j hp hpj
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  have hjle : j ≤ n := by
    have := (hp.pow_dvd_iff_le_factorization hk.ne').mp hpj
    exact this.trans (hn p)
  rw [pow_add, ← mul_sub_one]
  push_cast
  by_cases hpx : (p : ℤ) ∣ x
  · refine Dvd.dvd.mul_right ?_ _
    exact (pow_dvd_pow_of_dvd hpx j).trans (pow_dvd_pow x hjle)
  · refine Dvd.dvd.mul_left ?_ _
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime x (((p ^ j : ℕ) : ℤ)) := by
      have h1 : IsCoprime (p : ℤ) x := (hpr.irreducible.coprime_iff_not_dvd).mpr hpx
      push_cast
      exact (h1.symm.pow_right)
    obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hpj
    have hu := ZMod.pow_totient (ZMod.unitOfIsCoprime x hcop)
    have hx : ((x ^ k.totient - 1 : ℤ) : ZMod (p ^ j)) = 0 := by
      have hx1 : ((x : ZMod (p ^ j))) ^ (p ^ j).totient = 1 := by
        have h2 := congrArg (fun u : (ZMod (p ^ j))ˣ => (u : ZMod (p ^ j))) hu
        simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfIsCoprime, Units.val_one] at h2
        exact h2
      push_cast
      rw [hc, pow_mul, hx1, one_pow, sub_self]
    have hne : NeZero (p ^ j) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx
    exact_mod_cast this

/-- The basic summation `∑_{m ≥ 0} C(m,j) / 2^(m+1) = 1`. -/
lemma hasSum_choose_div_two_pow (j : ℕ) :
    HasSum (fun m : ℕ => (m.choose j : ℝ) / 2 ^ (m + 1)) 1 := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) j (r := 1 / 2)
    (by norm_num)
  rw [← hasSum_nat_add_iff' j]
  have hz : ∑ i ∈ range j, (i.choose j : ℝ) / 2 ^ (i + 1) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]
    simp
  rw [hz, sub_zero]
  have h2 := h.mul_right ((1 / 2) ^ (j + 1))
  have hval : (1 : ℝ) / (1 - 1 / 2) ^ (j + 1) * (1 / 2) ^ (j + 1) = 1 := by
    field_simp
    norm_num
  rw [hval] at h2
  have hf : (fun m : ℕ => ((m + j).choose j : ℝ) / 2 ^ (m + j + 1)) =
      fun m => ((m + j).choose j : ℝ) * (1 / 2) ^ m * (1 / 2) ^ (j + 1) := by
    funext m
    rw [pow_add, pow_add, one_div_pow, one_div_pow]
    field_simp
    ring
  rw [hf]
  exact h2

/-- The sequence A062208 as defined in the entry:
`a(n) = ∑_{m ≥ 0} C(m,3)^n · 2^(-m-1)`. -/
noncomputable def a (n : ℕ) : ℝ := ∑' m : ℕ, (m.choose 3 : ℝ) ^ n / 2 ^ (m + 1)

/-- The defining series of `a n` converges to Bala's finite sum `b n`. -/
lemma hasSum_a (n : ℕ) :
    HasSum (fun m : ℕ => (m.choose 3 : ℝ) ^ n / 2 ^ (m + 1)) (b n : ℝ) := by
  have hterm : ∀ m : ℕ, (m.choose 3 : ℝ) ^ n / 2 ^ (m + 1) =
      ∑ j ∈ range (3 * n + 1), (delta n j : ℝ) * ((m.choose j : ℝ) / 2 ^ (m + 1)) := by
    intro m
    have h := congrArg (fun z : ℤ => (z : ℝ)) (choose_pow_eq_sum n m)
    simp only [Int.cast_pow, Int.cast_natCast, Int.cast_sum, Int.cast_mul] at h
    rw [h, sum_div]
    refine sum_congr rfl fun j _ => ?_
    ring
  simp only [hterm]
  have hb : (b n : ℝ) = ∑ j ∈ range (3 * n + 1), (delta n j : ℝ) * 1 := by
    simp [b]
  rw [hb]
  exact hasSum_sum fun j _ => (hasSum_choose_div_two_pow j).mul_left _

/-- Bridge: the series value equals Bala's finite formula, so `a n` is an integer. -/
theorem a_eq_b (n : ℕ) : a n = b n := (hasSum_a n).tsum_eq

/-- Ground truth: the first terms listed in the entry. -/
example : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 63 ∧ a 3 = 16081 ∧ a 4 = 10681263 ∧
    a 5 = 14638956721 := by
  simp only [a_eq_b, b_zero, b_one, b_two, b_three, b_four, b_five]
  norm_num

/-- Carmichael-type power congruence modulo `60`: `x^(n+4) ≡ x^n (mod 60)` for `2 ≤ n`. -/
lemma sixty_dvd_pow_add_four_sub {n : ℕ} (hn : 2 ≤ n) (x : ℤ) :
    (60 : ℤ) ∣ x ^ (n + 4) - x ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have key : ∀ y : ZMod 60, y ^ 6 - y ^ 2 = 0 := by decide
  have h6 : (60 : ℤ) ∣ x ^ 6 - x ^ 2 := by
    have hz : ((x ^ 6 - x ^ 2 : ℤ) : ZMod 60) = 0 := by
      push_cast
      exact key (x : ZMod 60)
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 60).mp hz
  have hfac : x ^ (m + 2 + 4) - x ^ (m + 2) = x ^ m * (x ^ 6 - x ^ 2) := by ring
  rw [hfac]
  exact h6.mul_left _

/-- Residues of `b n` modulo `60` for `2 ≤ n`: `3` for even `n`, `1` for odd `n`. -/
lemma b_emod_sixty {n : ℕ} (hn : 2 ≤ n) : b n % 60 = if n % 2 = 0 then 3 else 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hsmall : n < 6
    · interval_cases n <;> simp [b_two, b_three, b_four, b_five]
    · have hstep : (60 : ℤ) ∣ b (n - 4 + 4) - b (n - 4) :=
        b_dvd_sub_of_pow (k := 60) (fun x => sixty_dvd_pow_add_four_sub (by omega) x)
      rw [Nat.sub_add_cancel (by omega)] at hstep
      have hmod : b (n - 4) % 60 = b n % 60 := Int.modEq_iff_dvd.mpr hstep
      rw [← hmod, ih (n - 4) (by omega) (by omega)]
      have hpar : (n - 4) % 2 = n % 2 := by omega
      rw [hpar]

/-- Integer-valuedness of the entry's series: `a n = b n` is an integer. -/
theorem a_isInt (n : ℕ) : ∃ z : ℤ, a n = z := ⟨b n, a_eq_b n⟩

/-- Bala's first congruence (even indices): `a(2n) ≡ 3 (mod 60)` for `n ≥ 1`. -/
theorem a_two_mul_mod_sixty {n : ℕ} (hn : 1 ≤ n) : ∃ z : ℤ, a (2 * n) = 60 * z + 3 := by
  have h := Int.emod_add_mul_ediv (b (2 * n)) 60
  rw [b_emod_sixty (by omega), if_pos (by omega)] at h
  refine ⟨b (2 * n) / 60, ?_⟩
  rw [a_eq_b]
  exact_mod_cast (by omega : b (2 * n) = 60 * (b (2 * n) / 60) + 3)

/-- Bala's second congruence (odd indices): `a(2n+1) ≡ 1 (mod 60)` for every `n ≥ 0`. -/
theorem a_two_mul_add_one_mod_sixty (n : ℕ) : ∃ z : ℤ, a (2 * n + 1) = 60 * z + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by rw [a_eq_b, b_one]; norm_num⟩
  · have h := Int.emod_add_mul_ediv (b (2 * n + 1)) 60
    rw [b_emod_sixty (by omega), if_neg (by omega)] at h
    refine ⟨b (2 * n + 1) / 60, ?_⟩
    rw [a_eq_b]
    exact_mod_cast (by omega : b (2 * n + 1) = 60 * (b (2 * n + 1) / 60) + 1)

/-- Boundary: the even-index congruence fails at `n = 0`, since `a 0 = 1`. -/
theorem not_a_zero_mod_sixty : ¬ ∃ z : ℤ, a 0 = 60 * z + 3 := by
  rintro ⟨z, hz⟩
  rw [a_eq_b, b_zero] at hz
  have hz' : (1 : ℤ) = 60 * z + 3 := by exact_mod_cast hz
  omega

/-- Explicit form of the periodicity claim: if every prime exponent of `k` is at most `n`,
then `a (n + φ k) ≡ a n (mod k)`. -/
theorem a_add_totient_sub_mem {k n : ℕ} (hk : 0 < k) (hn : ∀ p : ℕ, k.factorization p ≤ n) :
    ∃ z : ℤ, a (n + k.totient) - a n = k * z := by
  obtain ⟨z, hz⟩ := b_dvd_sub_of_pow (dvd_pow_add_totient_sub hk hn)
  refine ⟨z, ?_⟩
  rw [a_eq_b, a_eq_b]
  exact_mod_cast hz

/-- `q` is an eventual period of `a (mod k)`: from some index on, `a (n + q) ≡ a n (mod k)`,
i.e. `a (n + q) - a n` is an integer multiple of `k`. -/
def IsEventualPeriodMod (k q : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z : ℤ, a (n + q) - a n = k * z

/-- Eventual periodicity with period `φ k`, starting at `n = k`. -/
theorem isEventualPeriodMod_totient {k : ℕ} (hk : 0 < k) : IsEventualPeriodMod k k.totient := by
  refine ⟨k, fun n hn => a_add_totient_sub_mem hk fun p => ?_⟩
  exact ((Nat.factorization_lt p hk.ne').le).trans hn

/-- Eventual periods are closed under subtraction. -/
lemma IsEventualPeriodMod.sub {k p q : ℕ} (hp : IsEventualPeriodMod k p)
    (hq : IsEventualPeriodMod k q) (hpq : p ≤ q) : IsEventualPeriodMod k (q - p) := by
  obtain ⟨N₁, h₁⟩ := hp
  obtain ⟨N₂, h₂⟩ := hq
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨z₁, hz₁⟩ := h₁ (n + (q - p)) (by omega)
  obtain ⟨z₂, hz₂⟩ := h₂ n (by omega)
  have hidx : n + (q - p) + p = n + q := by omega
  rw [hidx] at hz₁
  refine ⟨z₂ - z₁, ?_⟩
  push_cast
  linarith

/-- Eventual periods are closed under reduction modulo another eventual period. -/
lemma IsEventualPeriodMod.mod {k p q : ℕ} (hp : IsEventualPeriodMod k p)
    (hq : IsEventualPeriodMod k q) : IsEventualPeriodMod k (q % p) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · rwa [hp0, Nat.mod_zero]
    · by_cases hlt : q < p
      · rwa [Nat.mod_eq_of_lt hlt]
      · have hle : p ≤ q := not_lt.mp hlt
        rw [Nat.mod_eq_sub_mod hle]
        exact ih (q - p) (by omega) (hp.sub hq hle)

/-- **Exact period form.** For `k ≥ 1`, the residues `a n mod k` have an exact eventual
period `p` (positive, and dividing every positive eventual period), and `p ∣ φ k`. -/
theorem exists_exact_period {k : ℕ} (hk : 0 < k) :
    ∃ p : ℕ, 0 < p ∧ p ∣ k.totient ∧ IsEventualPeriodMod k p ∧
      ∀ q : ℕ, 0 < q → IsEventualPeriodMod k q → p ∣ q := by
  classical
  have hex : ∃ q : ℕ, 0 < q ∧ IsEventualPeriodMod k q :=
    ⟨k.totient, Nat.totient_pos.mpr hk, isEventualPeriodMod_totient hk⟩
  obtain ⟨hpos, hper⟩ := Nat.find_spec hex
  have hdvd : ∀ q : ℕ, 0 < q → IsEventualPeriodMod k q → Nat.find hex ∣ q := by
    intro q _ hq
    have hmod := hper.mod hq
    have hlt : q % Nat.find hex < Nat.find hex := Nat.mod_lt _ hpos
    by_contra hnd
    have hne : 0 < q % Nat.find hex := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
    exact Nat.find_min hex hlt ⟨hne, hmod⟩
  exact ⟨Nat.find hex, hpos, hdvd _ (Nat.totient_pos.mpr hk) (isEventualPeriodMod_totient hk),
    hper, hdvd⟩

/-- Non-vacuity of `IsEventualPeriodMod`: `1` is not an eventual period modulo `60`
(the residues alternate between `3` and `1`). -/
theorem not_isEventualPeriodMod_sixty_one : ¬ IsEventualPeriodMod 60 1 := by
  rintro ⟨N, hN⟩
  obtain ⟨z, hz⟩ := hN (2 * (N + 1)) (by omega)
  rw [a_eq_b, a_eq_b] at hz
  have hz' : b (2 * (N + 1) + 1) - b (2 * (N + 1)) = 60 * z := by exact_mod_cast hz
  have h1 := b_emod_sixty (n := 2 * (N + 1) + 1) (by omega)
  have h2 := b_emod_sixty (n := 2 * (N + 1)) (by omega)
  rw [if_neg (by omega)] at h1
  rw [if_pos (by omega)] at h2
  omega

/-- **Bala's conjecture (A062208, Peter Bala, Feb 04 2018).**

Verbatim: "Conjectures: a(2*n) = 3 (mod 60) and a(2*n+1) = 1 (mod 60); for fixed k, the
sequence a(n) (mod k) eventually becomes periodic with exact period a divisor of phi(k)."

Here `a n = ∑_{m ≥ 0} C(m,3)^n / 2^(m+1)`. The statement records: every `a n` is an integer;
`a(2n) ≡ 3 (mod 60)` for `n ≥ 1` (it fails at `n = 0`); `a(2n+1) ≡ 1 (mod 60)` for all `n`;
and for each `k ≥ 1` the residues mod `k` have an exact eventual period dividing `φ k`. -/
theorem a062208_conjecture :
    (∀ n : ℕ, ∃ z : ℤ, a n = z) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a (2 * n) = 60 * z + 3) ∧
    (∀ n : ℕ, ∃ z : ℤ, a (2 * n + 1) = 60 * z + 1) ∧
    (∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ k.totient ∧ IsEventualPeriodMod k p ∧
      ∀ q : ℕ, 0 < q → IsEventualPeriodMod k q → p ∣ q) :=
  ⟨a_isInt, fun _ hn => a_two_mul_mod_sixty hn, a_two_mul_add_one_mod_sixty,
    fun _ hk => exists_exact_period hk⟩

end Candidates.A062208EventuallyPeriodicPeriod
