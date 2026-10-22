/-
# A113610: digit-sum valleys do not force twin primes

OEIS A113610, Amarnath Murthy (Nov 09 2005); program by Zak Seidov
(Nov 13 2009). The sequence sums decimal digits of the composites strictly
between consecutive one-based primes.
The literal conjecture fails at `n = 12`: `27 > 6 < 27`, but the relevant
primes are `37, 41`. The index-shifted reading also fails, at `n = 21`:
`65 > 27 < 70`, with relevant primes `79, 83`.
Neither theorem asserts that its counterexample is the smallest.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A113610Refutation

/-! ## Definitions -/

/-- The OEIS `prime(n)` with offset 1: `oeisPrime 1 = 2`, `oeisPrime 2 = 3`. -/
noncomputable def oeisPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Sum of the base-10 digits of `m`. -/
def digitSum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- The sum of the base-10 digits of the integers `p < m < q` that are
composite (`1 < m` and `m` not prime). -/
def compositeDigitSumBetween (p q : ℕ) : ℕ :=
  ∑ m ∈ (Finset.Ioo p q).filter (fun m => 1 < m ∧ ¬ m.Prime), digitSum m

/-- OEIS A113610: `a(n)` is the sum of the digits of all composite numbers
strictly between `prime(n)` and `prime(n+1)` (offset 1). -/
noncomputable def a (n : ℕ) : ℕ :=
  compositeDigitSumBetween (oeisPrime n) (oeisPrime (n + 1))

/-! ## Evaluation bridge -/

/-- If `p` is prime and exactly `n - 1` primes lie below `p`, then `p` is the
`n`-th prime in OEIS indexing. -/
theorem oeisPrime_eq_of_count {p n : ℕ} (hp : p.Prime)
    (hcount : Nat.count Nat.Prime p + 1 = n) : oeisPrime n = p := by
  subst hcount
  simp only [oeisPrime, Nat.add_sub_cancel]
  exact Nat.nth_count hp

/-- Evaluate `a n` once the two bounding primes are identified by counting. -/
theorem a_eq_of_count {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : Nat.count Nat.Prime p + 1 = n) (hqn : Nat.count Nat.Prime q + 1 = n + 1) :
    a n = compositeDigitSumBetween p q := by
  rw [a, oeisPrime_eq_of_count hp hpn, oeisPrime_eq_of_count hq hqn]

/-! ## Example: the first 14 listed terms -/

example : oeisPrime 1 = 2 := oeisPrime_eq_of_count (by norm_num) (by decide)
example : oeisPrime 12 = 37 := oeisPrime_eq_of_count (by norm_num) (by decide)
example : digitSum 1234 = 10 := by decide
example : a 1 = 0 := by rw [a_eq_of_count (p := 2) (q := 3) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 2 = 4 := by rw [a_eq_of_count (p := 3) (q := 5) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 3 = 6 := by rw [a_eq_of_count (p := 5) (q := 7) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 4 = 18 := by rw [a_eq_of_count (p := 7) (q := 11) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 5 = 3 := by rw [a_eq_of_count (p := 11) (q := 13) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 6 = 18 := by rw [a_eq_of_count (p := 13) (q := 17) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 7 = 9 := by rw [a_eq_of_count (p := 17) (q := 19) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 8 = 9 := by rw [a_eq_of_count (p := 19) (q := 23) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 9 = 40 := by rw [a_eq_of_count (p := 23) (q := 29) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 10 = 3 := by rw [a_eq_of_count (p := 29) (q := 31) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 11 = 35 := by rw [a_eq_of_count (p := 31) (q := 37) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 12 = 27 := by rw [a_eq_of_count (p := 37) (q := 41) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 13 = 6 := by rw [a_eq_of_count (p := 41) (q := 43) (by norm_num) (by norm_num) (by decide) (by decide)]; decide
example : a 14 = 27 := by rw [a_eq_of_count (p := 43) (q := 47) (by norm_num) (by norm_num) (by decide) (by decide)]; decide

/-! ## The conjecture -/

/-- **Murthy's conjecture (A113610, Amarnath Murthy, Nov 09 2005).**

Verbatim: "Conjecture: For n > 9 if a(n) > a(n+1) < a(n+2) then prime(n) and
prime(n+1) form a twin prime pair."

Since `prime(n)` and `prime(n+1)` are primes, "form a twin prime pair" means
`prime(n+1) = prime(n) + 2`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 9 < n → a (n + 1) < a n → a (n + 1) < a (n + 2) →
    oeisPrime (n + 1) = oeisPrime n + 2

/-- The index-shifted conjecture associates a valley at `a(n+1)` with
the prime pair `prime(n+1), prime(n+2)`. -/
def ShiftedConjecture : Prop :=
  ∀ n : ℕ, 9 < n → a (n + 1) < a n → a (n + 1) < a (n + 2) →
    oeisPrime (n + 2) = oeisPrime (n + 1) + 2

/-! ## Refutations -/

/-- The literal conjecture fails at `n = 12`: `a(12) = 27`, `a(13) = 6`,
`a(14) = 27`, but `prime(12) = 37` and `prime(13) = 41` are not twins.
The shifted conjecture is refuted separately in `shiftedConjecture_false`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have h37 : oeisPrime 12 = 37 := oeisPrime_eq_of_count (by norm_num) (by decide)
  have h41 : oeisPrime 13 = 41 := oeisPrime_eq_of_count (by norm_num) (by decide)
  have ha12 : a 12 = 27 := by
    rw [a_eq_of_count (p := 37) (q := 41) (by norm_num) (by norm_num) (by decide) (by decide)]
    decide
  have ha13 : a 13 = 6 := by
    rw [a_eq_of_count (p := 41) (q := 43) (by norm_num) (by norm_num) (by decide) (by decide)]
    decide
  have ha14 : a 14 = 27 := by
    rw [a_eq_of_count (p := 43) (q := 47) (by norm_num) (by norm_num) (by decide) (by decide)]
    decide
  have htwin := hconj 12 (by norm_num) (by rw [ha12, ha13]; norm_num)
    (by rw [ha13, ha14]; norm_num)
  rw [h37, h41] at htwin
  norm_num at htwin

/-- **The index-shifted reading is false too.** Counterexample `n = 21`: the
primes `prime(21..24) = 73, 79, 83, 89` give `a(21) = 65 > a(22) = 27 < a(23) = 70`,
but `prime(22) = 79` and `prime(23) = 83` are not twin primes. -/
theorem shiftedConjecture_false : ¬ ShiftedConjecture := by
  intro hconj
  have h79 : oeisPrime 22 = 79 := oeisPrime_eq_of_count (by norm_num) (by decide)
  have h83 : oeisPrime 23 = 83 := oeisPrime_eq_of_count (by norm_num) (by decide)
  have ha21 : a 21 = 65 := by
    rw [a_eq_of_count (p := 73) (q := 79) (by norm_num) (by norm_num) (by decide) (by decide)]
    decide
  have ha22 : a 22 = 27 := by
    rw [a_eq_of_count (p := 79) (q := 83) (by norm_num) (by norm_num) (by decide) (by decide)]
    decide
  have ha23 : a 23 = 70 := by
    rw [a_eq_of_count (p := 83) (q := 89) (by norm_num) (by norm_num) (by decide) (by decide)]
    decide
  have htwin := hconj 21 (by norm_num) (by rw [ha21, ha22]; norm_num)
    (by rw [ha22, ha23]; norm_num)
  rw [h79, h83] at htwin
  norm_num at htwin

end Candidates.A113610Refutation
