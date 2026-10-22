/-
# A373725 — 4p² − 1 is a term when p ≠ 3 and 2p − 1 are prime

OEIS A373725, Amiram Eldar: if `p ≠ 3` and `2p-1` are prime, then
`4p²-1` and `4p²` have the same maximal factorial-divisibility exponent
(A011776). A011776 sets `a(1) = 1`; for `n > 1` it is the largest
`e` with `n^e ∣ n!`.

`p = 2` gives `k = 15`, checked by `decide`.  For `p ≥ 5` put `q = 2p − 1`
(prime) and `m = q + 2 = 2p + 1`, so `4p² − 1 = q·m` and `3 ∣ m`.

* `e(4p²) = 2p + 2`: `v_p((4p²)!) = 4p + 4` (Legendre, `p³ > 4p²`) and
  `v_2((4p²)!) ≥ 2p² ≥ 4p + 4`.
* `e(qm) = q + 3 = 2p + 2`: `v_q((qm)!) = m + 1` (Legendre, `q² ≤ qm < 2q²`),
  and `m² ∣ m!` (as `m = 3t` with `3 < t`), hence `m^(2q) ∣ (m!)^q ∣ (qm)!`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A373725MaxPrimeAlso

open Finset

/-! ## Definitions -/

/-- OEIS A011776: `a(1) = 1`, and for `n > 1`, `a(n)` is the largest `e` with
`n ^ e ∣ n!`.  The search bound `n` is sound because `n ^ e ∣ n!` forces
`e ≤ n` (see `pow_dvd_factorial_iff_le_A011776`).  The value at `0` is outside
the OEIS offset and is set to `1` by convention. -/
def A011776 (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else Nat.findGreatest (fun e => n ^ e ∣ n.factorial) n

/-- Membership in OEIS A373725: `k` is a term iff `A011776 k = A011776 (k + 1)`
(the entry has offset 1, so terms are positive). -/
def IsA373725 (k : ℕ) : Prop := 0 < k ∧ A011776 k = A011776 (k + 1)

instance : DecidablePred IsA373725 := fun _ => instDecidableAnd

/-! ## Examples -/

example : (List.range 20).map (fun i => A011776 (i + 1)) =
    [1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3, 1, 4, 1, 4] := by decide

example : (List.range 64).filter (fun k => decide (IsA373725 k)) =
    [1, 2, 3, 4, 8, 9, 15, 27, 63] := by decide

/-- Bridge: for `2 ≤ n`, `n ^ e ∣ n!` holds exactly for `e ≤ A011776 n`,
so `A011776 n` is the maximal exponent of the OEIS definition. -/
theorem pow_dvd_factorial_iff_le_A011776 {n : ℕ} (hn : 2 ≤ n) (e : ℕ) :
    n ^ e ∣ n.factorial ↔ e ≤ A011776 n := by
  have hA : A011776 n = Nat.findGreatest (fun e => n ^ e ∣ n.factorial) n := by
    simp only [A011776, if_neg (by omega : ¬ n ≤ 1)]
  rw [hA]
  constructor
  · intro h
    have hle : n ^ e ≤ n ^ n :=
      (Nat.le_of_dvd (Nat.factorial_pos n) h).trans (Nat.factorial_le_pow n)
    exact Nat.le_findGreatest (P := fun e => n ^ e ∣ n.factorial)
      ((Nat.pow_le_pow_iff_right (by omega)).mp hle) h
  · intro h
    have hmax := Nat.findGreatest_spec (P := fun e => n ^ e ∣ n.factorial)
      (Nat.zero_le n) (by simp)
    exact (Nat.pow_dvd_pow n h).trans hmax

/-- `A011776 n = e` as soon as `n ^ e ∣ n!` and `¬ n ^ (e + 1) ∣ n!`, for `2 ≤ n`. -/
theorem A011776_eq_of_dvd_of_not_dvd {n e : ℕ} (hn : 2 ≤ n)
    (hd : n ^ e ∣ n.factorial) (hnd : ¬ n ^ (e + 1) ∣ n.factorial) :
    A011776 n = e := by
  have h1 := (pow_dvd_factorial_iff_le_A011776 hn e).mp hd
  have h2 : ¬ e + 1 ≤ A011776 n := fun h =>
    hnd ((pow_dvd_factorial_iff_le_A011776 hn (e + 1)).mpr h)
  omega

/-! ## Legendre helpers -/

/-- Lower Legendre bound: if `r ≤ ⌊n/p⌋ + ⌊n/p²⌋` for a prime `p`, then `p ^ r ∣ n!`. -/
theorem prime_pow_dvd_factorial_of_le {p n r : ℕ} (hp : p.Prime)
    (h : r ≤ n / p + n / p ^ 2) : p ^ r ∣ n.factorial := by
  rw [hp.pow_dvd_factorial_iff (b := Nat.log p n + 3) (by omega)]
  have hsub : Ico 1 3 ⊆ Ico 1 (Nat.log p n + 3) := Finset.Ico_subset_Ico_right (by omega)
  have h3 : ∑ i ∈ Ico 1 3, n / p ^ i = n / p + n / p ^ 2 := by
    simp [Finset.sum_Ico_succ_top]
  calc r ≤ ∑ i ∈ Ico 1 3, n / p ^ i := h3 ▸ h
    _ ≤ ∑ i ∈ Ico 1 (Nat.log p n + 3), n / p ^ i :=
      Finset.sum_le_sum_of_subset hsub

/-- Upper Legendre bound: if `0 < n < p³` for a prime `p` and
`⌊n/p⌋ + ⌊n/p²⌋ < r`, then `¬ p ^ r ∣ n!`. -/
theorem not_prime_pow_dvd_factorial_of_lt {p n r : ℕ} (hp : p.Prime) (hn0 : n ≠ 0)
    (hn : n < p ^ 3) (h : n / p + n / p ^ 2 < r) : ¬ p ^ r ∣ n.factorial := by
  rw [hp.pow_dvd_factorial_iff (b := 3) (Nat.log_lt_of_lt_pow hn0 hn)]
  have h3 : ∑ i ∈ Ico 1 3, n / p ^ i = n / p + n / p ^ 2 := by
    simp [Finset.sum_Ico_succ_top]
  omega

/-- `(m!) ^ j ∣ (j * m)!`. -/
theorem factorial_pow_dvd_factorial_mul (m j : ℕ) :
    m.factorial ^ j ∣ (j * m).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/-- If `m = 3 t` with `3 < t`, then `m ^ 2 ∣ m!`. -/
theorem sq_dvd_factorial_of_three_mul {t : ℕ} (ht : 3 < t) :
    (3 * t) ^ 2 ∣ (3 * t).factorial := by
  have h3 : 3 ∣ (t - 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have ht' : 3 * t ∣ t.factorial := by
    rw [← Nat.mul_factorial_pred (by omega : t ≠ 0), mul_comm 3 t]
    exact Nat.mul_dvd_mul_left t h3
  have hm : 3 * t ∣ (3 * t - 1).factorial :=
    ht'.trans (Nat.factorial_dvd_factorial (by omega))
  rw [sq, ← Nat.mul_factorial_pred (by omega : 3 * t ≠ 0)]
  exact Nat.mul_dvd_mul_left _ hm

/-! ## The two exponents -/

/-- For a prime `p ≥ 5`, `A011776 (4 p²) = 2 p + 2`. -/
theorem A011776_four_mul_sq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    A011776 (4 * p ^ 2) = 2 * p + 2 := by
  have hpos : 0 < p := hp.pos
  have hsq : 25 ≤ p ^ 2 := by nlinarith
  have hn2 : 2 ≤ 4 * p ^ 2 := by omega
  have hsplit : ∀ a : ℕ, (4 * p ^ 2) ^ a = 2 ^ (2 * a) * p ^ (2 * a) := by
    intro a
    rw [pow_mul, pow_mul, ← mul_pow]
    norm_num
  have hdivp : 4 * p ^ 2 / p = 4 * p :=
    Nat.div_eq_of_eq_mul_left hpos (by ring)
  have hdivp2 : 4 * p ^ 2 / p ^ 2 = 4 := Nat.mul_div_cancel _ (by positivity)
  apply A011776_eq_of_dvd_of_not_dvd hn2
  · -- lower bound: `2 ^ (4p+4) * p ^ (4p+4) ∣ (4p²)!`
    rw [hsplit]
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (hcop.pow _ _)
    · apply prime_pow_dvd_factorial_of_le Nat.prime_two
      have h2 : 4 * p ^ 2 / 2 = 2 * p ^ 2 := by omega
      have h5p : 5 * p ≤ p ^ 2 := by nlinarith
      rw [h2]
      omega
    · apply prime_pow_dvd_factorial_of_le hp
      rw [hdivp, hdivp2]
      omega
  · -- upper bound: `¬ p ^ (4p+6) ∣ (4p²)!`
    intro h
    have hpd : p ^ (2 * (2 * p + 2 + 1)) ∣ (4 * p ^ 2) ^ (2 * p + 2 + 1) := by
      rw [hsplit]
      exact Dvd.intro_left _ rfl
    refine not_prime_pow_dvd_factorial_of_lt hp (by omega) ?_ ?_ (hpd.trans h)
    · have hp3 : p ^ 3 = p * p ^ 2 := by ring
      rw [hp3]
      nlinarith
    · rw [hdivp, hdivp2]
      omega

/-- For a prime `q ≥ 9` with `3 ∣ q + 2`, `A011776 (q (q + 2)) = q + 3`. -/
theorem A011776_mul_add_two {q : ℕ} (hq : q.Prime) (h9 : 9 ≤ q) (h3 : 3 ∣ q + 2) :
    A011776 (q * (q + 2)) = q + 3 := by
  have hqpos : 0 < q := hq.pos
  have hk2 : 2 ≤ q * (q + 2) := by nlinarith
  have hdivq : q * (q + 2) / q = q + 2 := Nat.mul_div_cancel_left _ hqpos
  have hdivq2 : q * (q + 2) / q ^ 2 = 1 :=
    Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  apply A011776_eq_of_dvd_of_not_dvd hk2
  · -- lower bound: `q ^ (q+3) * (q+2) ^ (q+3) ∣ (q (q+2))!`
    rw [mul_pow]
    have hcop : Nat.Coprime q (q + 2) := by
      rw [add_comm]
      exact Nat.coprime_add_self_right.mpr
        ((Nat.coprime_primes hq Nat.prime_two).mpr (by omega))
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (hcop.pow _ _)
    · apply prime_pow_dvd_factorial_of_le hq
      rw [hdivq, hdivq2]
    · obtain ⟨t, ht⟩ := h3
      have ht3 : 3 < t := by omega
      have hm : ((q + 2) ^ 2) ^ q ∣ (q * (q + 2)).factorial := by
        rw [ht]
        exact (pow_dvd_pow_of_dvd (sq_dvd_factorial_of_three_mul ht3) q).trans
          (factorial_pow_dvd_factorial_mul _ _)
      rw [← pow_mul] at hm
      exact (Nat.pow_dvd_pow _ (by omega)).trans hm
  · -- upper bound: `¬ q ^ (q+4) ∣ (q (q+2))!`
    intro h
    have hqd : q ^ (q + 3 + 1) ∣ (q * (q + 2)) ^ (q + 3 + 1) :=
      pow_dvd_pow_of_dvd (Nat.dvd_mul_right q (q + 2)) _
    refine not_prime_pow_dvd_factorial_of_lt hq (by omega) ?_ ?_ (hqd.trans h)
    · have hq3 : q ^ 3 = q * q ^ 2 := by ring
      rw [hq3]
      exact Nat.mul_lt_mul_of_pos_left (by nlinarith) hqpos
    · rw [hdivq, hdivq2]
      omega

/-! ## The conjecture -/

/-- **Eldar's conjecture (A373725, entry by Amiram Eldar, 2024).**

Equality form: for every prime `p ≠ 3` with `2p − 1` prime,
`A011776 (4p² − 1) = A011776 (4p²)`.  The natural subtractions are harmless:
`p ≥ 2`, so `2p − 1 ≥ 3` and `4p² − 1 ≥ 15`. -/
theorem A011776_four_mul_sq_sub_one_eq {p : ℕ} (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (h3 : p ≠ 3) : A011776 (4 * p ^ 2 - 1) = A011776 (4 * p ^ 2) := by
  have h2 := hp.two_le
  rcases Nat.lt_or_ge p 5 with hlt | h5
  · -- `p ∈ {2, 4}` after excluding `3`; `4` is not prime
    interval_cases p
    · decide
    · exact absurd h3 (by norm_num)
    · exact absurd hp (by norm_num)
  · set q := 2 * p - 1 with hqdef
    have hq1 : q + 1 = 2 * p := by omega
    have h3p : ¬ 3 ∣ p := fun h =>
      h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    have h3q : ¬ 3 ∣ q := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h
      omega
    have h3m : 3 ∣ q + 2 := by
      rw [Nat.dvd_iff_mod_eq_zero] at h3p h3q ⊢
      have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases hmod with hmod | hmod <;> omega
    have h4 : 4 * p ^ 2 = q * (q + 2) + 1 := by
      rw [show 4 * p ^ 2 = (2 * p) ^ 2 by ring, ← hq1]
      ring
    rw [h4, Nat.add_sub_cancel, A011776_mul_add_two hq (by omega) h3m,
      ← h4, A011776_four_mul_sq hp h5]
    omega

/-- **Membership form of the A373725 conjecture.** For every prime `p ≠ 3` with
`2p − 1` prime, `4p² − 1` is a term of A373725. -/
theorem four_mul_sq_sub_one_mem {p : ℕ} (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (h3 : p ≠ 3) : IsA373725 (4 * p ^ 2 - 1) := by
  have h2 := hp.two_le
  have hsq : 4 ≤ p ^ 2 := by nlinarith
  refine ⟨by omega, ?_⟩
  rw [Nat.sub_add_cancel (by omega)]
  exact A011776_four_mul_sq_sub_one_eq hp hq h3

/-- Non-vacuity: the hypotheses hold jointly at `p = 7` (`2p − 1 = 13`), giving
the term `195`. -/
example : IsA373725 (4 * 7 ^ 2 - 1) :=
  four_mul_sq_sub_one_mem (by norm_num) (by norm_num) (by norm_num)

end Candidates.A373725MaxPrimeAlso
