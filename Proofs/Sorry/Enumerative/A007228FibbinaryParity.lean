/-
# A007228 — Bala: parity of `3 * binomial(4n, n) / (n + 1)`

## OEIS source (pulled with `oeis show A007228`, retrieved 2026-10-21)

```
NAME:     a(n) = 3*binomial(4*n,n)/(n+1).
TERMS:    3,6,28,165,1092,7752,57684,444015,3506100,28242984,231180144,...
COMMENT (the conjecture):
  Conjecture: for n >= 1, a(n) is odd iff n = 4*A263133(k) + 3 for some k.
  - _Peter Bala_, Mar 13 2023
```

Cross-reference (`oeis show A263133`):

```
NAME:     Numbers m such that binomial(4*m + 3, m) is odd.
TERMS:    0,1,2,3,5,7,10,11,15,21,23,31,42,43,47,63,85,87,95,127,...
```

## Status

Triage status: open (the entry gives no proof; no proof was located in the
literature by the triage).  Numerically confirmed for `1 ≤ n ≤ 6000`
(`python3`, exact integers).  This module proves the conjecture.

## Proof outline

* `a n + C(4n, n+1) = 3 C(4n, n)` (from `C(4n,n+1)(n+1) = C(4n,n)(3n)`), so
  `a n ≡ C(4n,n) + C(4n,n+1) = C(4n+1, n+1) (mod 2)`.
* Lucas's theorem at `p = 2` (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`)
  evaluates the parity of `C(4n+1, n+1)` according to `n mod 4`:
  `n ≡ 1, 2` gives an even factor `C(0,1) = 0`; `n = 4m` with `m ≥ 1` reduces to
  `C(8m, 2m)`, even since `C(4k, k)` is even for `k ≥ 1`; `n = 4m + 3` reduces to
  `C(4m+3, m+1) = 3 C(4m+3, m)`.
* The guard `n ≥ 1` is load-bearing: `a 0 = 3` is odd but `0` is not of the
  form `4m + 3`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A007228FibbinaryParity

/-- OEIS A007228: `a(n) = 3 * binomial(4n, n) / (n + 1)` (natural-number division;
the division is exact, see `a_add_choose_succ`; offset 0). -/
def a (n : ℕ) : ℕ := 3 * (4 * n).choose n / (n + 1)

example : a 0 = 3 := by decide
example : a 1 = 6 := by decide
example : a 2 = 28 := by decide
example : a 3 = 165 := by decide
example : a 4 = 1092 := by decide
example : a 5 = 7752 := by decide

/-- OEIS A263133 membership: `m` such that `binomial(4m + 3, m)` is odd. -/
def IsA263133 (m : ℕ) : Prop := Odd ((4 * m + 3).choose m)

example : IsA263133 0 := by unfold IsA263133; decide
example : IsA263133 1 := by unfold IsA263133; decide
example : IsA263133 2 := by unfold IsA263133; decide
example : IsA263133 3 := by unfold IsA263133; decide
example : ¬ IsA263133 4 := by unfold IsA263133; decide
example : IsA263133 5 := by unfold IsA263133; decide
example : ¬ IsA263133 6 := by unfold IsA263133; decide

/-- Lucas's theorem, one step at `p = 2`:
`C(N, K) ≡ C(N mod 2, K mod 2) · C(N / 2, K / 2) (mod 2)`. -/
theorem choose_mod_two (N K : ℕ) :
    N.choose K % 2 = ((N % 2).choose (K % 2) * (N / 2).choose (K / 2)) % 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-- `a(n) + C(4n, n+1) = 3 C(4n, n)`; in particular the division defining `a`
is exact and `a(n) = 3 C(4n,n) - C(4n,n+1)`. -/
theorem a_add_choose_succ (n : ℕ) :
    a n + (4 * n).choose (n + 1) = 3 * (4 * n).choose n := by
  have hrel : (4 * n).choose (n + 1) * (n + 1) = (4 * n).choose n * (3 * n) := by
    rw [Nat.choose_succ_right_eq]
    congr 1
    omega
  have hle : (4 * n).choose (n + 1) ≤ 3 * (4 * n).choose n := by
    have h1 : (4 * n).choose (n + 1) * (n + 1) ≤ 3 * (4 * n).choose n * (n + 1) := by
      rw [hrel]; nlinarith [Nat.zero_le ((4 * n).choose n)]
    exact Nat.le_of_mul_le_mul_right h1 (Nat.succ_pos n)
  have hdiv : 3 * (4 * n).choose n = (n + 1) * (3 * (4 * n).choose n - (4 * n).choose (n + 1)) := by
    rw [Nat.mul_sub, mul_comm (n + 1) ((4 * n).choose (n + 1)), hrel]
    have hexp : (n + 1) * (3 * (4 * n).choose n) =
        3 * (4 * n).choose n + (4 * n).choose n * (3 * n) := by ring
    omega
  have ha : a n = 3 * (4 * n).choose n - (4 * n).choose (n + 1) := by
    unfold a
    rw [hdiv, Nat.mul_div_cancel_left _ (Nat.succ_pos n), ← hdiv]
  omega

/-- `a(n) ≡ C(4n+1, n+1) (mod 2)`. -/
theorem a_mod_two (n : ℕ) : a n % 2 = (4 * n + 1).choose (n + 1) % 2 := by
  have h := a_add_choose_succ n
  have hpas : (4 * n + 1).choose (n + 1) = (4 * n).choose n + (4 * n).choose (n + 1) :=
    Nat.choose_succ_succ _ _
  omega

/-- For `k ≥ 1`, `C(4k, k)` is even. -/
theorem choose_four_mul_self_even (k : ℕ) (hk : 1 ≤ k) : (4 * k).choose k % 2 = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [choose_mod_two]
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      have hj1 : 1 ≤ j := by omega
      have e1 : 4 * (j + j) % 2 = 0 := by omega
      have e2 : (j + j) % 2 = 0 := by omega
      have e3 : 4 * (j + j) / 2 = 4 * j := by omega
      have e4 : (j + j) / 2 = j := by omega
      rw [e1, e2, e3, e4, Nat.choose_zero_right, one_mul]
      exact ih j (by omega) hj1
    · subst hj
      have e1 : 4 * (2 * j + 1) % 2 = 0 := by omega
      have e2 : (2 * j + 1) % 2 = 1 := by omega
      rw [e1, e2]
      simp

/-- For `n ≥ 1`, `C(4n+1, n+1)` is odd iff `n = 4m + 3` with `C(4m+3, m)` odd. -/
theorem choose_odd_iff (n : ℕ) (hn : 1 ≤ n) :
    (4 * n + 1).choose (n + 1) % 2 = 1 ↔
      ∃ m, (4 * m + 3).choose m % 2 = 1 ∧ n = 4 * m + 3 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  interval_cases r
  · -- n = 4m with m ≥ 1
    have hm : 1 ≤ m := by omega
    have hzero : (4 * (4 * m + 0) + 1).choose (4 * m + 0 + 1) % 2 = 0 := by
      rw [choose_mod_two]
      have e1 : (4 * (4 * m + 0) + 1) % 2 = 1 := by omega
      have e2 : (4 * m + 0 + 1) % 2 = 1 := by omega
      have e3 : (4 * (4 * m + 0) + 1) / 2 = 4 * (2 * m) := by omega
      have e4 : (4 * m + 0 + 1) / 2 = 2 * m := by omega
      rw [e1, e2, e3, e4, Nat.choose_self, one_mul]
      exact choose_four_mul_self_even (2 * m) (by omega)
    constructor
    · intro h; omega
    · rintro ⟨m', -, hm'⟩; omega
  · -- n = 4m + 1
    have hzero : (4 * (4 * m + 1) + 1).choose (4 * m + 1 + 1) % 2 = 0 := by
      rw [choose_mod_two]
      have e1 : (4 * (4 * m + 1) + 1) % 2 = 1 := by omega
      have e2 : (4 * m + 1 + 1) % 2 = 0 := by omega
      have e3 : (4 * (4 * m + 1) + 1) / 2 = 2 * (4 * m + 1) := by omega
      have e4 : (4 * m + 1 + 1) / 2 = 2 * m + 1 := by omega
      rw [e1, e2, e3, e4, Nat.choose_zero_right, one_mul, choose_mod_two]
      have e5 : 2 * (4 * m + 1) % 2 = 0 := by omega
      have e6 : (2 * m + 1) % 2 = 1 := by omega
      rw [e5, e6]
      simp
    constructor
    · intro h; omega
    · rintro ⟨m', -, hm'⟩; omega
  · -- n = 4m + 2
    have hzero : (4 * (4 * m + 2) + 1).choose (4 * m + 2 + 1) % 2 = 0 := by
      rw [choose_mod_two]
      have e1 : (4 * (4 * m + 2) + 1) % 2 = 1 := by omega
      have e2 : (4 * m + 2 + 1) % 2 = 1 := by omega
      have e3 : (4 * (4 * m + 2) + 1) / 2 = 2 * (4 * m + 2) := by omega
      have e4 : (4 * m + 2 + 1) / 2 = 2 * m + 1 := by omega
      rw [e1, e2, e3, e4, Nat.choose_self, one_mul, choose_mod_two]
      have e5 : 2 * (4 * m + 2) % 2 = 0 := by omega
      have e6 : (2 * m + 1) % 2 = 1 := by omega
      rw [e5, e6]
      simp
    constructor
    · intro h; omega
    · rintro ⟨m', -, hm'⟩; omega
  · -- n = 4m + 3: reduce to `C(4m+3, m+1) = 3 C(4m+3, m)`
    have hred : (4 * (4 * m + 3) + 1).choose (4 * m + 3 + 1) % 2 =
        (4 * m + 3).choose (m + 1) % 2 := by
      rw [choose_mod_two]
      have e1 : (4 * (4 * m + 3) + 1) % 2 = 1 := by omega
      have e2 : (4 * m + 3 + 1) % 2 = 0 := by omega
      have e3 : (4 * (4 * m + 3) + 1) / 2 = 2 * (4 * m + 3) := by omega
      have e4 : (4 * m + 3 + 1) / 2 = 2 * (m + 1) := by omega
      rw [e1, e2, e3, e4, Nat.choose_zero_right, one_mul, choose_mod_two]
      have e5 : 2 * (4 * m + 3) % 2 = 0 := by omega
      have e6 : 2 * (m + 1) % 2 = 0 := by omega
      have e7 : 2 * (4 * m + 3) / 2 = 4 * m + 3 := by omega
      have e8 : 2 * (m + 1) / 2 = m + 1 := by omega
      rw [e5, e6, e7, e8, Nat.choose_zero_right, one_mul]
    have hthree : (4 * m + 3).choose (m + 1) = 3 * (4 * m + 3).choose m := by
      have hrel := Nat.choose_succ_right_eq (4 * m + 3) m
      have e : 4 * m + 3 - m = 3 * (m + 1) := by omega
      rw [e] at hrel
      have hrel' : (4 * m + 3).choose (m + 1) * (m + 1) =
          3 * (4 * m + 3).choose m * (m + 1) := by rw [hrel]; ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) hrel'
    rw [hred, hthree]
    constructor
    · intro h
      exact ⟨m, by omega, rfl⟩
    · rintro ⟨m', hodd, hm'⟩
      have hmm : m' = m := by omega
      subst hmm
      omega

/-- **Bala's conjecture (A007228, Peter Bala, Mar 13 2023), proved.**

Verbatim: "Conjecture: for n >= 1, a(n) is odd iff n = 4*A263133(k) + 3 for
some k."  Here `a n = 3 * C(4n, n) / (n + 1)` and `A263133` is the set of `m`
with `C(4m + 3, m)` odd (`IsA263133`).  The guard `1 ≤ n` is from the source and
is necessary (`a 0 = 3` is odd). -/
theorem a_odd_iff (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ m, IsA263133 m ∧ n = 4 * m + 3 := by
  rw [Nat.odd_iff, a_mod_two, choose_odd_iff n hn]
  simp only [IsA263133, Nat.odd_iff]

/-- The guard `1 ≤ n` in `a_odd_iff` is necessary: `a 0 = 3` is odd, yet `0` is
not of the form `4m + 3`. -/
theorem a_zero_odd_not_form : Odd (a 0) ∧ ¬ ∃ m, IsA263133 m ∧ 0 = 4 * m + 3 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨m, -, hm⟩
  omega

-- Non-vacuity: both sides of `a_odd_iff` occur (`a 3 = 165` odd, `a 1 = 6` even).
example : Odd (a 3) ∧ ∃ m, IsA263133 m ∧ 3 = 4 * m + 3 := ⟨by decide, 0, by unfold IsA263133; decide, rfl⟩
example : ¬ Odd (a 1) := by decide

end Candidates.A007228FibbinaryParity
