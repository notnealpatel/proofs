/-
# A029797 — refutation of Greathouse's "eventually consecutive" conjecture

## OEIS source (retrieved 2026-10-21 with `oeis show A029797`; offset
checked against the live entry, `%O 1,3`)

```
A029797   Numbers k such that k^2 and k^3 have the same set of digits.
TERMS:    0,1,10,100,146,1000,1203,1460,7652,8077,8751,8965,10000,10406,
          11914,12030,12057,12586,12768,12961,13055,14202,14600,14625,16221,
          19350,20450,21539,22040,22175,23682,24071,25089,25201,25708,26653,
          26981
OFFSET:   1
COMMENT:  Conjecture: there exists some m and N for which a(n) = m + n for all
          n >= N. [_Charles R Greathouse IV_, Jun 28 2011]
COMMENT:  This conjecture is false. If the conjecture is true then for some N
          we would have k is in the sequence if k >= n. But 10^e + 1 (A062397)
          is not in the sequence for any integer e >= 0.
          - _David A. Corneth_, Nov 13 2023
```

No later comment withdraws Corneth's refutation.

## Status

This module refutes Greathouse's conjecture (kernel-checked).  If
`a(n) = m + n` for all `n ≥ N`, then every integer `k ≥ a(N)` lies in the
sequence.  The witness used here is `k = 2 * 10^e` (rather than Corneth's
`10^e + 1`): `k^2 = 4 * 10^(2e)` has digit set `{0, 4}` (or `{4}`), while
`k^3 = 8 * 10^(3e)` has digit set `{0, 8}` (or `{8}`), so `4` separates them.
A Python recheck (2026-10-21) confirms the 37 listed terms and that neither
`2 * 10^e` nor `10^e + 1` lies in the sequence for `0 ≤ e < 40`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A029797Refutation

/-! ## Definition layer -/

/-- `k` belongs to A029797: the decimal digit sets of `k^2` and `k^3`
coincide (`Nat.digits 10 0 = []`, so `k = 0` qualifies, as in the entry). -/
def IsA029797 (k : ℕ) : Prop :=
  (Nat.digits 10 (k ^ 2)).toFinset = (Nat.digits 10 (k ^ 3)).toFinset

/-- `IsA029797` is decided by comparing the two finite digit sets. -/
instance : DecidablePred IsA029797 := fun k =>
  inferInstanceAs
    (Decidable ((Nat.digits 10 (k ^ 2)).toFinset = (Nat.digits 10 (k ^ 3)).toFinset))

/-- The sequence A029797 with the OEIS offset `1`: `a n` is the `n`-th member
(meaningful for `1 ≤ n`; the conjecture below only uses such `n`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsA029797 (n - 1)

/-! ## Ground truth against the listed terms -/

example : IsA029797 0 := by decide
example : IsA029797 1 := by decide
example : IsA029797 10 := by decide
example : IsA029797 146 := by decide
example : IsA029797 1203 := by decide
example : IsA029797 7652 := by decide
example : ¬ IsA029797 2 := by decide
example : ¬ IsA029797 11 := by decide
example : ¬ IsA029797 145 := by decide

/-- `a 1 = 0`, the first listed term. -/
example : a 1 = 0 := Nat.nth_zero_of_zero (p := IsA029797) (by decide)

/-- `a 3 = 10`, the third listed term (`10` is preceded by exactly two members). -/
example : a 3 = 10 := by
  have hc : Nat.count IsA029797 10 = 2 := by decide
  rw [a, show 3 - 1 = Nat.count IsA029797 10 from hc.symm]
  exact Nat.nth_count (p := IsA029797) (by decide)

/-- `a 5 = 146`, the fifth listed term. -/
example : a 5 = 146 := by
  have hc : Nat.count IsA029797 146 = 4 := by decide
  rw [a, show 5 - 1 = Nat.count IsA029797 146 from hc.symm]
  exact Nat.nth_count (p := IsA029797) (by decide)

/-! ## The conjecture -/

/-- **Greathouse's conjecture (A029797, Jun 28 2011).**  Verbatim:
"Conjecture: there exists some m and N for which a(n) = m + n for all n >= N."

The shift `m` is an integer (the comparison is made in `ℤ`), and the
`1 ≤ n` hypothesis keeps `a n` on its OEIS domain (offset `1`); it only
weakens the conjecture, so refuting this form is the stronger statement. -/
def Conjecture : Prop :=
  ∃ m : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → (a n : ℤ) = m + n

/-! ## Digit-set lemmas -/

/-- Every power of ten is in the sequence (A011557 is a subsequence). -/
theorem isA029797_ten_pow (j : ℕ) : IsA029797 (10 ^ j) := by
  unfold IsA029797
  have h2 : (10 ^ j) ^ 2 = 10 ^ (2 * j) * 1 := by ring
  have h3 : (10 ^ j) ^ 3 = 10 ^ (3 * j) * 1 := by ring
  rw [h2, h3, Nat.digits_base_pow_mul (by norm_num) (by norm_num),
    Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
  ext d
  simp only [List.mem_toFinset, List.mem_append, List.mem_replicate]
  constructor <;> rintro (⟨hj, hd⟩ | hd) <;>
    first
    | exact Or.inr hd
    | exact Or.inl ⟨by omega, hd⟩

/-- The sequence is infinite. -/
theorem setOf_isA029797_infinite : (Set.ofPred IsA029797).Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  have hmem : 10 ^ B ∈ Set.ofPred IsA029797 := isA029797_ten_pow B
  have hle : 10 ^ B ≤ B := hB hmem
  have hlt : B < 10 ^ B := Nat.lt_pow_self (by norm_num)
  omega

/-- `2 * 10^e` is never in the sequence: `4` is a digit of its square
`4 * 10^(2e)` but not of its cube `8 * 10^(3e)`. -/
theorem not_isA029797_two_mul_ten_pow (e : ℕ) : ¬ IsA029797 (2 * 10 ^ e) := by
  unfold IsA029797
  have h2 : (2 * 10 ^ e) ^ 2 = 10 ^ (2 * e) * 4 := by ring
  have h3 : (2 * 10 ^ e) ^ 3 = 10 ^ (3 * e) * 8 := by ring
  rw [h2, h3, Nat.digits_base_pow_mul (by norm_num) (by norm_num),
    Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
  intro h
  have h4 : 4 ∈ (List.replicate (2 * e) 0 ++ Nat.digits 10 4).toFinset := by simp
  rw [h] at h4
  simp [List.mem_replicate] at h4

/-! ## The refutation -/

/-- **Greathouse's conjecture is false.**  If `a n = m + n` for all `n ≥ N`,
then consecutive terms differ by `1` from `a N` on, so every `k ≥ a (max N 1)`
is in the sequence; but `k = 2 * 10^e` (with `e = a (max N 1)`) is not,
since `k^2 = 4 * 10^(2e)` contains the digit `4` and `k^3 = 8 * 10^(3e)` does
not.  (Corneth's witness `10^e + 1` works equally.)  The intended statement was
presumably a density claim (almost all `k` are in the sequence), which this
module does not address. -/
theorem greathouse_false : ¬ Conjecture := by
  rintro ⟨m, N, hN⟩
  set N' := max N 1 with hN'
  have hstep : ∀ j : ℕ, a (N' + j) = a N' + j := by
    intro j
    have h1 := hN (N' + j) (by omega) (by omega)
    have h0 := hN N' (by omega) (by omega)
    push_cast at h1
    omega
  have hall : ∀ k : ℕ, a N' ≤ k → IsA029797 k := by
    intro k hk
    have hk' : k = a (N' + (k - a N')) := by rw [hstep]; omega
    rw [hk', a]
    exact Nat.nth_mem_of_infinite setOf_isA029797_infinite _
  have hbig : a N' ≤ 2 * 10 ^ (a N') := by
    have hlt : a N' < 10 ^ a N' := Nat.lt_pow_self (by norm_num)
    omega
  exact not_isA029797_two_mul_ten_pow (a N') (hall _ hbig)

end Candidates.A029797Refutation
