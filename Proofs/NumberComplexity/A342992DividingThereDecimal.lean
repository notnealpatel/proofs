/-
# A342992 — every multiple-of-no-5 number has a multiple with only prime digits

## OEIS source (retrieved with `oeis show A342992`, 2026-10-21)

```
NAME:     Smallest k such that k*n contains only prime digits, or 0 if no such
          k exists.
TERMS:    2,1,1,8,1,12,1,4,3,0,2,6,4,18,5,2,15,4,3,0,12,1,1,3,1,2,1,9,8,0,12,
          1,1,8,1,2,1,14,7,0,13,6,54,8,5,7,5,49,15,0,5,1,1,43,1,42,1,4,43,0,...
KEYWORDS: nonn,base
COMMENT:  a(n) is 0 when n is divisible by 10, but when a(n) = 0, n is not
          always divisible by 10. For example, for n = 625, 1875, 3125,
          4375, ... a(n) = 0 because no such k has been found yet for these
          numbers.
COMMENT (the conjecture, unattributed in the entry):
          Conjecture: a(n) > 0 for all n that are not divisible by 5.
COMMENT:  a(625*k) = 0 for k > 0 as the last four digits of (625*k), i.e.,
          (625*k) mod 10000 always contains a nonprime digit.
          - _David A. Corneth_, Apr 21 2021
```

## Status

Triage: open (still printed as a conjecture; the entry gives no proof and the
triage found none in the literature).  Computational re-validation
(2026-10-21): for every `n ≤ 20000` with `5 ∤ n` a multiple of `n` with all
decimal digits in `{2, 3}` exists (residue BFS), and the definition below
reproduces the first 40 listed terms.

## Result in this file

The conjecture is **proved** here, in the stronger form that the digits can
be taken from `{2, 3}`:

* write `n = 2^e * m` with `m` odd (so `gcd(m, 10) = 1`);
* `block`: there is an `(e+1)`-digit string `X` over `{2, 3}` with
  `2^(e+1) ∣ X` (prepend a digit chosen by parity);
* `repeat_block`: the `j`-fold concatenation `R_j` of `X` satisfies
  `R_j * y + X = X * (y + 1)^j` with `y + 1 = 10^(e+1)`;
* with `M = m * y` (coprime to `10`) and `j = φ(M)`, Euler gives
  `M ∣ (y + 1)^j - 1`, so `m ∣ R_j / X`, hence `n ∣ R_j`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A342992DividingThereDecimal

/-! ## Definition layer -/

/-- `m` "contains only prime digits": every decimal digit of `m` is prime
(equivalently lies in `{2, 3, 5, 7}`). -/
def OnlyPrimeDigits (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d.Prime

instance (m : ℕ) : Decidable (OnlyPrimeDigits m) := by
  unfold OnlyPrimeDigits
  infer_instance

open Classical in
/-- A342992: the smallest `k ≥ 1` such that `k * n` contains only prime digits,
or `0` if no such `k` exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ OnlyPrimeDigits (k * n) then Nat.find h else 0

/-- `a n` is positive exactly when some positive multiple `k * n` has only
prime digits. -/
theorem a_pos_iff (n : ℕ) : 0 < a n ↔ ∃ k, 0 < k ∧ OnlyPrimeDigits (k * n) := by
  classical
  constructor
  · intro hpos
    by_contra hnone
    have hzero : a n = 0 := by
      unfold a
      rw [dif_neg hnone]
    omega
  · intro hex
    unfold a
    rw [dif_pos hex]
    exact (Nat.find_spec hex).1

/-- Characterization of `a n = k` by minimality, used for the ground-truth
checks against the DATA line. -/
theorem a_eq_of_minimal (n k : ℕ) (hk : 0 < k) (hP : OnlyPrimeDigits (k * n))
    (hmin : ∀ j < k, 0 < j → ¬ OnlyPrimeDigits (j * n)) : a n = k := by
  classical
  have hex : ∃ k, 0 < k ∧ OnlyPrimeDigits (k * n) := ⟨k, hk, hP⟩
  unfold a
  rw [dif_pos hex, Nat.find_eq_iff]
  refine ⟨⟨hk, hP⟩, ?_⟩
  intro j hj hjP
  exact hmin j hj hjP.1 hjP.2

/-- No positive multiple of `10` has only prime digits (its last digit is `0`),
so `a (10 * t) = 0` for `t > 0`.  (The guard matters: `Nat.digits 10 0 = []`,
so `0` vacuously has only prime digits and `a 0 = 1`; the entry starts at
`n = 1`.) -/
theorem a_ten_mul (t : ℕ) (ht : 0 < t) : a (10 * t) = 0 := by
  classical
  by_contra hne
  obtain ⟨k, hk, hP⟩ := (a_pos_iff (10 * t)).mp (Nat.pos_of_ne_zero hne)
  have hpos : 0 < k * (10 * t) := by positivity
  have hdig : Nat.digits 10 (k * (10 * t)) = 0 :: Nat.digits 10 (k * t) := by
    rw [Nat.digits_def' (by norm_num) hpos]
    congr 2
    · rw [show k * (10 * t) = 10 * (k * t) by ring]
      simp
    · rw [show k * (10 * t) = 10 * (k * t) by ring]
      simp
  exact Nat.not_prime_zero (hP 0 (by rw [hdig]; simp))

/-! ## Ground truth against the DATA line `2,1,1,8,1,12,1,4,3,0,…` -/

example : a 1 = 2 := a_eq_of_minimal 1 2 (by norm_num) (by decide) (by decide)
example : a 2 = 1 := a_eq_of_minimal 2 1 (by norm_num) (by decide) (by decide)
example : a 3 = 1 := a_eq_of_minimal 3 1 (by norm_num) (by decide) (by decide)
example : a 4 = 8 := a_eq_of_minimal 4 8 (by norm_num) (by decide) (by decide)
example : a 5 = 1 := a_eq_of_minimal 5 1 (by norm_num) (by decide) (by decide)
example : a 6 = 12 := a_eq_of_minimal 6 12 (by norm_num) (by decide) (by decide)
example : a 7 = 1 := a_eq_of_minimal 7 1 (by norm_num) (by decide) (by decide)
example : a 8 = 4 := a_eq_of_minimal 8 4 (by norm_num) (by decide) (by decide)
example : a 9 = 3 := a_eq_of_minimal 9 3 (by norm_num) (by decide) (by decide)
example : a 10 = 0 := by simpa using a_ten_mul 1 (by norm_num)
example : a 14 = 18 := a_eq_of_minimal 14 18 (by norm_num) (by decide) (by decide)

/-! ## The proof -/

/-- For every `e` there is a string of exactly `e` decimal digits, each `2` or
`3`, whose value is divisible by `2^e`. -/
theorem block (e : ℕ) : ∃ L : List ℕ, L.length = e ∧ (∀ d ∈ L, d = 2 ∨ d = 3) ∧
    2 ^ e ∣ Nat.ofDigits 10 L := by
  induction e with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ e ih =>
    obtain ⟨L, hlen, hdig, q, hq⟩ := ih
    obtain ⟨v, hv⟩ : Odd (5 ^ e) := Odd.pow (by decide)
    have key : ∀ d : ℕ, Nat.ofDigits 10 (L ++ [d]) = 2 ^ e * (q + 5 ^ e * d) := by
      intro d
      rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hq, hlen,
        show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
      ring
    rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨L ++ [2], by simp [hlen], ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.mp hd with h | h
        · exact hdig d h
        · left
          simpa using h
      · rw [key, pow_succ, hv, hr]
        exact ⟨r + 2 * v + 1, by ring⟩
    · refine ⟨L ++ [3], by simp [hlen], ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.mp hd with h | h
        · exact hdig d h
        · right
          simpa using h
      · rw [key, pow_succ, hv, hr]
        exact ⟨r + 3 * v + 2, by ring⟩

/-- Concatenating `j` copies of a digit string `L` over `{2, 3}`: with
`10 ^ L.length = y + 1`, the value `R` of the concatenation satisfies
`R * y + X = X * (y + 1) ^ j`, where `X` is the value of `L`
(the geometric-sum identity, free of subtraction). -/
theorem repeat_block (L : List ℕ) (hdig : ∀ d ∈ L, d = 2 ∨ d = 3) (y : ℕ)
    (hy : 10 ^ L.length = y + 1) (j : ℕ) :
    ∃ R : List ℕ, R.length = L.length * j ∧ (∀ d ∈ R, d = 2 ∨ d = 3) ∧
      Nat.ofDigits 10 R * y + Nat.ofDigits 10 L = Nat.ofDigits 10 L * (y + 1) ^ j := by
  induction j with
  | zero => exact ⟨[], by simp, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨R, hlen, hdigR, hR⟩ := ih
    refine ⟨L ++ R, by simp [hlen]; ring, ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with h | h
      · exact hdig d h
      · exact hdigR d h
    · rw [Nat.ofDigits_append, hy, pow_succ]
      linear_combination (y + 1) * hR

/-- A nonempty digit string over `{2, 3}` is the decimal expansion of its value. -/
theorem digits_ofDigits_two_three (R : List ℕ) (hdig : ∀ d ∈ R, d = 2 ∨ d = 3) :
    Nat.digits 10 (Nat.ofDigits 10 R) = R := by
  refine Nat.digits_ofDigits 10 (by norm_num) R ?_ ?_
  · intro d hd
    rcases hdig d hd with h | h <;> omega
  · intro hne
    rcases hdig _ (List.getLast_mem hne) with h | h <;> omega

/-- **Stronger form (proved).** For every positive `n` with `5 ∤ n` there is
`k ≥ 1` such that every decimal digit of `k * n` is `2` or `3`. -/
theorem exists_mul_digits_two_three (n : ℕ) (hn : 0 < n) (h5 : ¬ 5 ∣ n) :
    ∃ k, 0 < k ∧ ∀ d ∈ Nat.digits 10 (k * n), d = 2 ∨ d = 3 := by
  obtain ⟨e, m, hmodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  -- the 2-power block
  obtain ⟨L, hlen, hdig, hdvd⟩ := block (e + 1)
  set c := Nat.ofDigits 10 L with hc
  have hc2 : 2 ^ e ∣ c := (pow_dvd_pow 2 (Nat.le_succ e)).trans hdvd
  -- y + 1 = 10 ^ (e + 1)
  set y := 10 ^ (e + 1) - 1 with hydef
  have hten : 10 ≤ 10 ^ (e + 1) := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hy1 : 10 ^ (e + 1) = y + 1 := by omega
  have hypos : 0 < y := by omega
  -- coprimality of 10 ^ (e + 1) with M = m * y
  have hm5 : ¬ 5 ∣ m := fun h => h5 (h.trans (dvd_mul_left m _))
  have hcop10 : Nat.Coprime 10 m := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num]
    exact Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (Nat.odd_iff.mp hmodd |> fun h => by omega))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hm5)
  have hcopm : Nat.Coprime (y + 1) m := by
    rw [← hy1]
    exact Nat.Coprime.pow_left _ hcop10
  have hcopy : Nat.Coprime (y + 1) y := by simp
  set M := m * y with hM
  have hcopM : Nat.Coprime (y + 1) M := Nat.Coprime.mul_right hcopm hcopy
  have hmpos : 0 < m := hmodd.pos
  have hMpos : 0 < M := Nat.mul_pos hmpos hypos
  -- Euler: (y + 1) ^ φ(M) = M * t + 1
  set j := Nat.totient M with hj
  have hjpos : 0 < j := Nat.totient_pos.mpr hMpos
  have hmod : (y + 1) ^ j ≡ 1 [MOD M] := Nat.ModEq.pow_totient hcopM
  obtain ⟨t, ht⟩ : M ∣ (y + 1) ^ j - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp hmod.symm
  have hpow : (y + 1) ^ j = M * t + 1 := by
    have h1 : 1 ≤ (y + 1) ^ j := Nat.one_le_pow _ _ (by omega)
    omega
  -- the concatenation of j copies of the block
  obtain ⟨R, hRlen, hRdig, hR⟩ := repeat_block L hdig y (by rw [hlen]; exact hy1) j
  have hRval : Nat.ofDigits 10 R = c * m * t := by
    rw [hpow, hM] at hR
    have hmul : Nat.ofDigits 10 R * y = (c * m * t) * y := by
      have h := hR
      rw [← hc] at h
      nlinarith [h]
    exact Nat.eq_of_mul_eq_mul_right hypos hmul
  have hndvd : 2 ^ e * m ∣ Nat.ofDigits 10 R := by
    rw [hRval]
    exact Dvd.dvd.mul_right (mul_dvd_mul hc2 (dvd_refl m)) t
  have hRdigits : Nat.digits 10 (Nat.ofDigits 10 R) = R :=
    digits_ofDigits_two_three R hRdig
  have hRne : R ≠ [] := by
    intro h
    rw [h, List.length_nil] at hRlen
    rw [hlen] at hRlen
    have : 0 < (e + 1) * j := Nat.mul_pos (by omega) hjpos
    omega
  have hRpos : 0 < Nat.ofDigits 10 R := by
    rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 R) with h | h
    · rw [h, Nat.digits_zero] at hRdigits
      exact absurd hRdigits.symm hRne
    · exact h
  refine ⟨Nat.ofDigits 10 R / (2 ^ e * m), ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hRpos hndvd) (by positivity)
  · rw [Nat.div_mul_cancel hndvd, hRdigits]
    exact hRdig

/-- **A342992 conjecture (proved).** Verbatim: "Conjecture: a(n) > 0 for all n
that are not divisible by 5."  Equivalently: for every positive integer `n`
with `5 ∤ n` there is `k ≥ 1` such that every decimal digit of `k * n` is
prime (lies in `{2, 3, 5, 7}`). -/
theorem exists_mul_onlyPrimeDigits (n : ℕ) (hn : 0 < n) (h5 : ¬ 5 ∣ n) :
    ∃ k, 0 < k ∧ OnlyPrimeDigits (k * n) := by
  obtain ⟨k, hk, hdig⟩ := exists_mul_digits_two_three n hn h5
  refine ⟨k, hk, fun d hd => ?_⟩
  rcases hdig d hd with h | h
  · rw [h]
    exact Nat.prime_two
  · rw [h]
    exact Nat.prime_three

/-- **A342992 conjecture, sequence form (proved).** `a(n) > 0` for every
positive `n` not divisible by `5`. -/
theorem a_pos (n : ℕ) (hn : 0 < n) (h5 : ¬ 5 ∣ n) : 0 < a n :=
  (a_pos_iff n).mpr (exists_mul_onlyPrimeDigits n hn h5)

/-! ## Sanity layer -/

-- The hypotheses are jointly satisfiable (`n = 1`, `n = 4`), and the
-- conclusion is not vacuous: `k * n ≥ 1` so its digit list is nonempty.
example : 0 < a 1 := a_pos 1 (by norm_num) (by decide)
example : 0 < a 4 := a_pos 4 (by norm_num) (by decide)

-- The `5 ∤ n` guard is load-bearing: `a 10 = 0`.
example : ¬ (0 < a 10) := by simpa using a_ten_mul 1 (by norm_num)

end Candidates.A342992DividingThereDecimal
