/-
# A352742 — Bělohoubek: no term is a multiple of 5 (refuted, minimality open)

## OEIS source (retrieved 2026-10-21 with `oeis show A352742` and the live
## entry https://oeis.org/A352742)

```
NAME:     a(n) is the smallest number > 1 that is not divisible by 10 but is
          divisible by the n-th power of the sum of its digits.
OFFSET:   1
TERMS:    2,81,512,2401,11101212,34012224,612220032,20047612231936,
          3904305912313344,7800803212802061312,1025300207121086650406,
          213780015477322248820322,14076019706120526112710656,
          2670419511272061205254504361,2759031540715333904109053133443,
          10530400808911150200350000010411
COMMENT:  a(n+1) >= a(n).
COMMENT:  When A072408(n) is not multiple of 10 then a(n) <= A072408(n).
COMMENT:  a(n) = m * k^n where m is a positive integer and k is the sum of
          digits of a(n).
COMMENT (the conjecture):
          Conjecture: No term is a multiple of 5.
COMMENT (later):
          a(28) = 265^28, disproving the above conjecture.
          - _Charles R Greathouse IV_, Apr 02 2022
AUTHOR:   _Nicolas Bělohoubek_, Mar 31 2022
KEYWORDS: nonn,base
```

The conjecture comment carries no separate signature; it belongs to the
entry's author, Nicolas Bělohoubek (Mar 31 2022).  The later comment by
Greathouse already records its refutation; this module formalizes that
refutation.

## Status (partial)

`265^28 = 70938903323020164041464952207191804150246813586391508579254150390625`
has digit sum `265`, is not divisible by `10`, is divisible by `265^28`, and
is divisible by `5`.  All of this is kernel-checked below.  What remains open
is the **minimality** of `265^28` among the `n = 28` candidates, i.e. that no
`m` with `1 < m < 265^28` is not divisible by `10` and divisible by the 28th
power of its digit sum.  It is isolated as the single `sorry`
`not_isCandidate_28_of_lt`.  `conjecture_false_of_minimal` proves the
refutation from that residual with no `sorry`.

Re-validation (python, 2026-10-21): the witness properties above hold; for
every digit sum `s ∈ [156, 264]` all `15785965` multiples of `s^28` below
`265^28` were enumerated and none has digit sum `s` and a nonzero last digit.
Digit sums `s ≤ 155` were not searched: there the number of multiples of
`s^28` below `265^28` exceeds `3.3 · 10^6` per value of `s` (about `10^34`
for `s = 11`), so the minimality check needs a digit-structured search that
was not carried out, and is far beyond kernel reduction.  Greathouse's
comment is the only source for the minimality.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A352742Refutation

/-! ## Definition layer -/

/-- The sum of the base-10 digits of `m` (Mathlib's `Nat.digits`). -/
def digitSum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- `m` is admissible for the `n`-th term of A352742: `m > 1`, `m` is not
divisible by `10`, and `m` is divisible by the `n`-th power of its digit sum. -/
def IsCandidate (n m : ℕ) : Prop := 1 < m ∧ ¬ 10 ∣ m ∧ digitSum m ^ n ∣ m

/-- `IsCandidate n m` is decidable (all three clauses are). -/
instance decidableIsCandidate (n m : ℕ) : Decidable (IsCandidate n m) := by
  unfold IsCandidate
  infer_instance

/-- `a` is the `n`-th term of A352742: the least admissible `m`. -/
def IsTerm (n a : ℕ) : Prop := IsLeast {m | IsCandidate n m} a

/-- Membership plus a decidable bounded check of all smaller values gives a term. -/
theorem isTerm_of_forall_lt {n a : ℕ} (ha : IsCandidate n a)
    (hlt : ∀ k < a, ¬ IsCandidate n k) : IsTerm n a :=
  ⟨ha, fun k hk => le_of_not_gt fun hka => hlt k hka hk⟩

/-! ## Ground truth: the first four listed terms `2, 81, 512, 2401` -/

example : digitSum 2401 = 7 ∧ digitSum 512 = 8 ∧ digitSum 81 = 9 := by decide

example : IsTerm 1 2 := isTerm_of_forall_lt (by decide) (by decide)

example : IsTerm 2 81 := isTerm_of_forall_lt (by decide) (by decide +kernel)

example : IsTerm 3 512 := isTerm_of_forall_lt (by decide) (by decide +kernel)

example : IsTerm 4 2401 := isTerm_of_forall_lt (by decide) (by decide +kernel)

-- The fifth term `11101212` satisfies the predicate (digit sum `9`, `9^5 ∣ m`);
-- its minimality is not checked here.
example : IsCandidate 5 11101212 := by decide +kernel

/-! ## The conjecture -/

/-- **Bělohoubek's conjecture (A352742, Nicolas Bělohoubek, Mar 31 2022).**

Verbatim: "Conjecture: No term is a multiple of 5."

Formalized over the OEIS offset `n ≥ 1`: whenever `a` is the least number
`> 1` that is not divisible by `10` and is divisible by the `n`-th power of
its digit sum, `5` does not divide `a`.  Stating it through `IsLeast` (rather
than `sInf`, whose junk value `0` is a multiple of `5`) keeps the claim off
junk values; for an `n` without admissible numbers the clause is vacuous,
matching "no term". -/
def Conjecture : Prop := ∀ n : ℕ, 1 ≤ n → ∀ a : ℕ, IsTerm n a → ¬ 5 ∣ a

/-! ## The witness `265^28` -/

/-- `265^28` has digit sum `265`. -/
theorem digitSum_265_pow_28 : digitSum (265 ^ 28) = 265 := by decide +kernel

/-- `265^28` is admissible for `n = 28`: it exceeds `1`, ends in the digit `5`,
and is divisible by the 28th power of its digit sum `265`. -/
theorem isCandidate_28_265_pow_28 : IsCandidate 28 (265 ^ 28) := by
  refine ⟨by norm_num, by decide +kernel, ?_⟩
  rw [digitSum_265_pow_28]

/-- `265^28` is a multiple of `5`. -/
theorem five_dvd_265_pow_28 : 5 ∣ 265 ^ 28 :=
  (show 5 ∣ 265 by norm_num).trans (dvd_pow_self 265 (by norm_num))

/-- Any admissible `m < 265^28` for `n = 28` has digit sum below `265`
(since `digitSum m ^ 28 ∣ m` and `0 < m`). -/
theorem digitSum_lt_265_of_isCandidate {m : ℕ} (hm : IsCandidate 28 m)
    (hlt : m < 265 ^ 28) : digitSum m < 265 := by
  obtain ⟨h1, -, hdvd⟩ := hm
  have hle : digitSum m ^ 28 ≤ m := Nat.le_of_dvd (by omega) hdvd
  exact lt_of_pow_lt_pow_left₀ 28 (by norm_num) (hle.trans_lt hlt)

/-! ## The refutation -/

/-- **Conditional refutation (kernel-checked).**  If no `m` with
`1 < m < 265^28` is admissible for `n = 28`, then `a(28) = 265^28`
(Greathouse's value), which is a multiple of `5`, so the conjecture is
false. -/
theorem conjecture_false_of_minimal
    (hmin : ∀ m : ℕ, 1 < m → m < 265 ^ 28 → ¬ IsCandidate 28 m) : ¬ Conjecture := by
  intro hconj
  have hterm : IsTerm 28 (265 ^ 28) :=
    isTerm_of_forall_lt isCandidate_28_265_pow_28 fun k hk hck => hmin k hck.1 hk hck
  exact hconj 28 (by norm_num) (265 ^ 28) hterm five_dvd_265_pow_28

/-- **Residual (open here): minimality of `265^28` at `n = 28`.**  No `m`
with `1 < m < 265^28` is not divisible by `10` and divisible by the 28th power
of its digit sum.  Asserted by Greathouse (OEIS A352742, Apr 02 2022);
checked here by python only for digit sums in `[156, 264]`. -/
theorem not_isCandidate_28_of_lt (m : ℕ) (h1 : 1 < m) (hm : m < 265 ^ 28) :
    ¬ IsCandidate 28 m := by
  sorry

/-- **Bělohoubek's conjecture is false**: `a(28) = 265^28` (Greathouse,
Apr 02 2022) is a multiple of `5`.  The proof depends on the `sorry`-backed
minimality residual `not_isCandidate_28_of_lt`; the rest is kernel-checked
in `conjecture_false_of_minimal`.  No corrected form is evident: the author
seems to have extrapolated from the sixteen listed terms, none of which ends
in `0` or `5`. -/
theorem conjecture_false : ¬ Conjecture :=
  conjecture_false_of_minimal not_isCandidate_28_of_lt

end Candidates.A352742Refutation
