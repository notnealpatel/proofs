/-
# A177680 — Dale: every term after the first is a multiple of 5

## OEIS source (retrieved with `oeis show A177680`, 2026-10-21)

```
NAME:     Numbers n such that 6n and 12n are both the average of twin prime pairs.
TERMS:    1,5,110,135,355,425,555,565,975,1045,1755,5530,6935,7355,8925,9240,
          9555,10640,10850,11730,11830,12045,12350,12460,13130,13445,13655,
          14590,15540,17050,19245,20795,22330,22825,26070,26910,28075,30585,30805
FORMULA:  a(n)=A066388(n)/6.
COMMENT (the conjecture):
  Conjecture: all terms but the first term are multiples of 5.
  - _Harvey P. Dale_, Sep 26 2017
```

## Status

Listed as a conjecture in the entry; triage found no proof in the entry or the
literature ("open").  It is an elementary residue argument modulo 5: for
`n ≡ 1, 2, 3, 4 (mod 5)` respectively `5 ∣ 6n-1`, `5 ∣ 12n+1`, `5 ∣ 12n-1`,
`5 ∣ 6n+1`, and each of these numbers exceeds 5 once `n > 1`.  Proved below.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A177680PrimeMultiple

/-- `n` is a term of OEIS A177680: `n` is positive and both `6n` and `12n` are
averages of twin prime pairs, i.e. `6n-1`, `6n+1`, `12n-1`, `12n+1` are all
prime.  The positivity guard keeps the natural subtractions off their junk
value. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ (6 * n - 1).Prime ∧ (6 * n + 1).Prime ∧ (12 * n - 1).Prime ∧
    (12 * n + 1).Prime

instance : DecidablePred IsTerm := fun n => by
  unfold IsTerm
  infer_instance

/-! ## Ground truth against the listed terms -/

example : IsTerm 1 := by unfold IsTerm; norm_num
example : IsTerm 5 := by unfold IsTerm; norm_num
example : IsTerm 110 := by unfold IsTerm; norm_num
example : IsTerm 135 := by unfold IsTerm; norm_num
example : ¬ IsTerm 2 := by unfold IsTerm; norm_num
example : ¬ IsTerm 10 := by unfold IsTerm; norm_num

/-- A prime divisible by `5` equals `5`. -/
theorem five_dvd_prime_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ∣ p) : p = 5 :=
  ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5).symm

/-- **A177680, Dale's conjecture (Sep 26 2017).**  Every term `n > 1` of
A177680 (so `6n±1` and `12n±1` are all prime) is a multiple of 5. -/
theorem five_dvd_of_isTerm {n : ℕ} (hn : 1 < n) (h : IsTerm n) : 5 ∣ n := by
  obtain ⟨_, h6m, h6p, h12m, h12p⟩ := h
  have hr : n % 5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases hmod : n % 5
  · exact Nat.dvd_of_mod_eq_zero hmod
  · have h5 : 5 ∣ 6 * n - 1 := by omega
    have heq := five_dvd_prime_eq h6m h5
    omega
  · have h5 : 5 ∣ 12 * n + 1 := by omega
    have heq := five_dvd_prime_eq h12p h5
    omega
  · have h5 : 5 ∣ 12 * n - 1 := by omega
    have heq := five_dvd_prime_eq h12m h5
    omega
  · have h5 : 5 ∣ 6 * n + 1 := by omega
    have heq := five_dvd_prime_eq h6p h5
    omega

/-- Non-vacuity: the hypotheses of `five_dvd_of_isTerm` hold jointly at
`n = 5`, the second listed term. -/
example : 1 < 5 ∧ IsTerm 5 := ⟨by norm_num, by unfold IsTerm; norm_num⟩

end Candidates.A177680PrimeMultiple
