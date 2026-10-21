/-
# A137098 — Dale: terms after 2 and 5 end in 7

## OEIS source (retrieved with `oeis show A137098`, 2026-10-21)

```
NAME:     Numbers k such that k and k^2 use only the digits 2, 4, 5, 7 and 9.
TERMS:    2,5,7,27,77,477,527,977,2227,5477,7227,7277,22977,49727,49777,54277,
          97977,99727,99777,229727,274727,495477,499227,499277,724727,774227,...
COMMENT (the conjecture):
  Conjecture: the last digit of all terms except the first two is 7.
  - _Harvey P. Dale_, Jan 18 2016
```

## Status

Triage status: open (no proof in the entry or the literature as far as the
triage could tell).  The claim is settled here by a residue argument: the last
three decimal digits of `k` and `k^2` are functions of `k % 1000`, and a finite
check over the 1000 residues shows that a term `k ≥ 10` must end in `7`.
Informally: `k` ends in `2`, `5` or `7` since `k^2` must end in an allowed digit;
if `k = 10a + 2` with `a ≥ 1` the tens digit of `k^2` is `4a mod 10 ∈ {0,6,8}`;
if `k = 10a + 5` with `a ≥ 1` the hundreds digit of `k^2` is
`a(a+1) mod 10 ∈ {0,6}`.  Brute force over all `5^9` candidates `k < 10^9`
(68 terms) is consistent.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A137098BothUseDecimal

/-! ## Definition layer -/

/-- The allowed decimal digits `{2, 4, 5, 7, 9}`. -/
def allowedDigits : Finset ℕ := {2, 4, 5, 7, 9}

/-- `n` uses only the decimal digits `2, 4, 5, 7, 9`: every entry of the
base-10 digit list `Nat.digits 10 n` lies in `allowedDigits`. -/
def UsesAllowed (n : ℕ) : Prop := ∀ d ∈ Nat.digits 10 n, d ∈ allowedDigits

/-- `UsesAllowed n` is decidable (a bounded check over the digit list). -/
instance (n : ℕ) : Decidable (UsesAllowed n) := by
  unfold UsesAllowed; infer_instance

/-- A137098: positive `k` such that `k` and `k^2` use only the digits
`2, 4, 5, 7, 9`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ UsesAllowed k ∧ UsesAllowed (k ^ 2)

/-! ## Ground truth: the first listed terms and some non-terms -/

example : IsTerm 2 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [UsesAllowed, allowedDigits]
example : IsTerm 5 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [UsesAllowed, allowedDigits]
example : IsTerm 7 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [UsesAllowed, allowedDigits]
example : IsTerm 27 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [UsesAllowed, allowedDigits]
example : IsTerm 477 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [UsesAllowed, allowedDigits]
example : ¬ IsTerm 22 := by
  simp [IsTerm, UsesAllowed, allowedDigits]
example : ¬ IsTerm 4 := by
  simp [IsTerm, UsesAllowed, allowedDigits]

/-! ## Digit extraction -/

/-- If all decimal digits of `n` are allowed and `10^i ≤ n`, then the `i`-th
decimal digit `n / 10^i % 10` is allowed. -/
theorem digit_mem_of_usesAllowed {n : ℕ} (h : UsesAllowed n) (i : ℕ)
    (hi : 10 ^ i ≤ n) : n / 10 ^ i % 10 ∈ allowedDigits := by
  induction i generalizing n with
  | zero =>
    have hn : 0 < n := lt_of_lt_of_le (pow_pos (by norm_num) 0) hi
    have hd := Nat.digits_def' (by norm_num : 1 < 10) hn
    simpa using h (n % 10) (by rw [hd]; exact List.mem_cons_self ..)
  | succ i ih =>
    have hn : 0 < n := lt_of_lt_of_le (pow_pos (by norm_num) (i + 1)) hi
    have hd := Nat.digits_def' (by norm_num : 1 < 10) hn
    have htail : UsesAllowed (n / 10) := fun d hd' =>
      h d (by rw [hd]; exact List.mem_cons_of_mem _ hd')
    have hi' : 10 ^ i ≤ n / 10 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      simpa [pow_succ] using hi
    have key := ih htail hi'
    rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at key

/-! ## The residue checks -/

/-- Finite check over residues mod 100: if the units and tens digits of `r`
and the last two digits of `r^2` are all allowed, then `r` ends in `5` or `7`.
(A residue ending in `2` fails at the tens digit of `r^2`.) -/
theorem residue_check_mod100 : ∀ r : ℕ, r < 100 →
    (r % 10 ∈ allowedDigits ∧ r / 10 ∈ allowedDigits ∧
    r ^ 2 % 100 % 10 ∈ allowedDigits ∧ r ^ 2 % 100 / 10 ∈ allowedDigits) →
    r % 10 = 5 ∨ r % 10 = 7 := by
  decide

/-- For an allowed digit `t`, the digit `(t^2 + t) mod 10` is not allowed
(it is `0` or `6`). -/
theorem hundreds_check : ∀ t : ℕ, t < 10 → t ∈ allowedDigits →
    (t ^ 2 + t) % 10 ∉ allowedDigits := by
  decide

/-- If `k = 10a + 5` then the hundreds digit of `k^2 = 100 a (a+1) + 25` is
`(a^2 + a) mod 10`, which depends only on the last digit of `a`. -/
theorem hundreds_digit_sq_of_mod_ten_eq_five (k : ℕ) (h5 : k % 10 = 5) :
    k ^ 2 / 100 % 10 = ((k / 10 % 10) ^ 2 + k / 10 % 10) % 10 := by
  set a := k / 10 with ha
  have hk : k = 10 * a + 5 := by omega
  have hsq : k ^ 2 = 100 * (a ^ 2 + a) + 25 := by rw [hk]; ring
  have hdiv : k ^ 2 / 100 = a ^ 2 + a := by rw [hsq]; omega
  rw [hdiv, Nat.add_mod, Nat.pow_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mod_mod]

/-- The tens digit of `k^2` depends only on `k mod 100`. -/
theorem tens_digit_sq (k : ℕ) : k ^ 2 / 10 % 10 = (k % 100) ^ 2 % 100 / 10 := by
  rw [← Nat.pow_mod]; omega

/-- The units digit of `k^2` depends only on `k mod 100`. -/
theorem units_digit_sq (k : ℕ) : k ^ 2 % 10 = (k % 100) ^ 2 % 100 % 10 := by
  rw [← Nat.pow_mod]; omega

/-! ## The conjecture -/

/-- **Dale's conjecture (A137098, Harvey P. Dale, Jan 18 2016).**

Verbatim: "Conjecture: the last digit of all terms except the first two is 7."
The terms are the positive `k` such that `k` and `k^2` use only the digits
`2, 4, 5, 7, 9`; the first two terms are `2` and `5`, so the claim is that every
term `k` with `7 < k` satisfies `k ≡ 7 (mod 10)`. -/
theorem last_digit_seven (k : ℕ) (hk : 7 < k) (h : IsTerm k) : k % 10 = 7 := by
  obtain ⟨-, hk1, hk2⟩ := h
  -- units digits of `k` and `k^2`
  have d0 : k % 10 ∈ allowedDigits := by
    simpa using digit_mem_of_usesAllowed hk1 0 (by omega)
  have e0 : k ^ 2 % 10 ∈ allowedDigits := by
    simpa using digit_mem_of_usesAllowed hk2 0 (Nat.one_le_pow _ _ (by omega))
  -- `k = 8` and `k = 9` are excluded by the units digits
  have hk10 : 10 ≤ k := by
    by_contra hlt
    interval_cases k <;> simp [allowedDigits] at d0 e0
  -- tens digits of `k` and `k^2`, hundreds digit of `k^2`
  have d1 : k / 10 % 10 ∈ allowedDigits := by
    simpa using digit_mem_of_usesAllowed hk1 1 (by simpa using hk10)
  have e1 : k ^ 2 / 10 % 10 ∈ allowedDigits := by
    simpa using digit_mem_of_usesAllowed hk2 1 (by nlinarith)
  have e2 : k ^ 2 / 100 % 10 ∈ allowedDigits := by
    simpa using digit_mem_of_usesAllowed hk2 2 (by nlinarith)
  -- reduce to the residue `k mod 100`
  have h57 : k % 10 = 5 ∨ k % 10 = 7 := by
    have hr := residue_check_mod100 (k % 100) (Nat.mod_lt _ (by norm_num))
      ⟨by rwa [Nat.mod_mod_of_dvd _ (by norm_num : 10 ∣ 100)],
       by rwa [show k % 100 / 10 = k / 10 % 10 by omega],
       by rwa [units_digit_sq] at e0,
       by rwa [tens_digit_sq] at e1⟩
    rwa [Nat.mod_mod_of_dvd _ (by norm_num : 10 ∣ 100)] at hr
  rcases h57 with h5 | h7
  · -- a term ending in `5` has a forbidden hundreds digit in its square
    rw [hundreds_digit_sq_of_mod_ten_eq_five k h5] at e2
    exact absurd e2 (hundreds_check (k / 10 % 10) (Nat.mod_lt _ (by norm_num)) d1)
  · exact h7

end Candidates.A137098BothUseDecimal
