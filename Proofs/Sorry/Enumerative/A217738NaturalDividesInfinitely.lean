/-
# A217738 — indices k with k(k+1) | F(k): divisibility by 12, infinitude

## OEIS source (retrieved with `oeis show A217738` and the live entry,
## 2026-10-21)

```
NAME:     Numbers k such that Fibonacci(k) is divisible by k*(k+1).
TERMS:    60,108,180,240,540,600,660,768,1008,1200,1320,1620,1800,1860,2160,
          2520,2688,2736,3000,3060,3300,3360,3528,3888,4200,4800,4860,...
KEYWORDS: nonn
AUTHOR:   Alex Ratushnyak, Mar 22 2013
COMMENT:  Indices of 0's in A217737.
COMMENT (the conjecture, unsigned, so attributed to the entry author
         Alex Ratushnyak, Mar 22 2013):
  Conjectures: the sequence is infinite; all terms are divisible by 12.
PROGRAM:  Select[Range[10000],Divisible[Fibonacci[#],#(#+1)]&]
          (* Harvey P. Dale, Aug 14 2014 *)
```

## Status

Triage: open; the entry carries no proof and the triage found none in the
literature.

* (a) "all terms are divisible by 12" is proved below
  (`twelve_dvd_of_mul_succ_dvd_fib`) by a two-step `Nat.fib_gcd` argument:
  `2 = F(3)` divides `F(k)` forces `3 ∣ k`, and then `3 = F(4)` divides
  `F(k)` forces `4 ∣ k`.
* (b) "the sequence is infinite" stays open (`infinite_setOf`, one `sorry`).
  Computation (2026-10-21, fast-doubling `F(k) mod k(k+1)`): 195 terms with
  `k ≤ 100000`, all divisible by 12.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A217738NaturalDividesInfinitely

/-! ## Definition layer -/

/-- Membership predicate of A217738: `k` is a positive integer and
`k * (k + 1)` divides the Fibonacci number `F(k)` (Mathlib's `Nat.fib`,
`F(0) = 0`, `F(1) = 1`). The Mathematica program enumerates `Range[10000]`,
so the offset starts at `k = 1`; the guard `0 < k` excludes the degenerate
`0 * 1 ∣ F(0) = 0`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ k * (k + 1) ∣ Nat.fib k

/-- `IsTerm` is decidable (divisibility on `ℕ`), used by the ground-truth `decide` checks. -/
instance (k : ℕ) : Decidable (IsTerm k) := by
  unfold IsTerm
  infer_instance

/-! ## Ground truth against the DATA line -/

-- `Nat.fib` matches A000045 at the values the proof uses.
example : Nat.fib 1 = 1 ∧ Nat.fib 2 = 1 ∧ Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 := by
  decide

-- The first listed terms are terms.
example : IsTerm 60 ∧ IsTerm 108 ∧ IsTerm 180 ∧ IsTerm 240 := by decide

-- No positive `k < 60` is a term, so `60` is the first term, as listed.
example : ∀ k < 60, ¬ IsTerm k := by decide

-- Between consecutive listed terms there are no others (window `61 … 107`).
example : ∀ k ∈ Finset.Ioo 60 108, ¬ IsTerm k := by decide

/-! ## Part (a): every term is divisible by 12 -/

/-- If `2 = F(3)` divides `F(k)` then `3 ∣ k`: `F(gcd 3 k) = gcd(F 3, F k) = 2`,
and among the divisors `1, 3` of `3` only `F(3) = 2`. -/
theorem three_dvd_of_two_dvd_fib {k : ℕ} (h : 2 ∣ Nat.fib k) : 3 ∣ k := by
  have hg : Nat.fib (Nat.gcd 3 k) = 2 := by
    rw [Nat.fib_gcd, show Nat.fib 3 = 2 by decide]
    exact Nat.gcd_eq_left h
  have hd : Nat.gcd 3 k ∣ 3 := Nat.gcd_dvd_left 3 k
  have hle : Nat.gcd 3 k ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  have h3 : Nat.gcd 3 k = 3 := by
    interval_cases hgk : Nat.gcd 3 k <;> simp_all [Nat.fib]
  rw [← h3]
  exact Nat.gcd_dvd_right 3 k

/-- If `3 = F(4)` divides `F(k)` then `4 ∣ k`: `F(gcd 4 k) = gcd(F 4, F k) = 3`,
and among the divisors `1, 2, 4` of `4` only `F(4) = 3`. -/
theorem four_dvd_of_three_dvd_fib {k : ℕ} (h : 3 ∣ Nat.fib k) : 4 ∣ k := by
  have hg : Nat.fib (Nat.gcd 4 k) = 3 := by
    rw [Nat.fib_gcd, show Nat.fib 4 = 3 by decide]
    exact Nat.gcd_eq_left h
  have hd : Nat.gcd 4 k ∣ 4 := Nat.gcd_dvd_left 4 k
  have hle : Nat.gcd 4 k ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have h4 : Nat.gcd 4 k = 4 := by
    interval_cases hgk : Nat.gcd 4 k <;> simp_all [Nat.fib]
  rw [← h4]
  exact Nat.gcd_dvd_right 4 k

/-- **A217738, conjecture (a)** (Alex Ratushnyak, Mar 22 2013: "all terms are
divisible by 12"), in the form "for every natural `k`, if `k (k + 1)` divides
`F(k)` then `12 ∣ k`". Proof: `k (k + 1)` is even, so `2 ∣ F(k)` and `3 ∣ k`;
then `3 ∣ k (k + 1) ∣ F(k)`, so `4 ∣ k`; `3` and `4` are coprime. -/
theorem twelve_dvd_of_mul_succ_dvd_fib (k : ℕ) (h : k * (k + 1) ∣ Nat.fib k) :
    12 ∣ k := by
  have h2 : 2 ∣ Nat.fib k := (Nat.even_mul_succ_self k).two_dvd.trans h
  have h3 : 3 ∣ k := three_dvd_of_two_dvd_fib h2
  have h3fib : 3 ∣ Nat.fib k := (h3.mul_right (k + 1)).trans h
  have h4 : 4 ∣ k := four_dvd_of_three_dvd_fib h3fib
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 3) (n := 4) (by norm_num) h3 h4

/-- Conjecture (a) restated on the sequence predicate: every term of A217738
is divisible by 12. -/
theorem twelve_dvd_of_isTerm {k : ℕ} (hk : IsTerm k) : 12 ∣ k :=
  twelve_dvd_of_mul_succ_dvd_fib k hk.2

/-! ## Part (b): infinitude (open) -/

/-- **A217738, conjecture (b)** (Alex Ratushnyak, Mar 22 2013: "the sequence is
infinite"): infinitely many positive `k` satisfy `k (k + 1) ∣ F(k)`. Open. -/
theorem infinite_setOf : {k : ℕ | IsTerm k}.Infinite := by
  -- Remaining goal: `{k : ℕ | IsTerm k}.Infinite`. No proof known; triage: 68 of the
  -- 72 terms up to 20000 have `k + 1` prime, so a proof would plausibly need
  -- infinitely many primes `p` with `(p - 1) (p) ∣ F(p - 1)`.
  sorry

-- Satisfiability of the hypothesis of (a) at a genuine term.
example : 60 * (60 + 1) ∣ Nat.fib 60 ∧ 12 ∣ 60 :=
  ⟨by decide, twelve_dvd_of_mul_succ_dvd_fib 60 (by decide)⟩

end Candidates.A217738NaturalDividesInfinitely
