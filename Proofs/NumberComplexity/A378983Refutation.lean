/-
# A378983 — Karttunen: the square-or-twice-square terms are exactly A202274

## OEIS source (retrieved with `oeis show A378983` and the live entry, 2026-10-21)

```
NAME:     Numbers k such that (A003961(k)-2*k) divides (A003961(k)-(1+sigma(k))),
          where A003961 is fully multiplicative with a(prime(i)) = prime(i+1),
          and sigma is the sum of divisors function.
TERMS:    1,2,3,4,5,8,10,11,15,16,17,25,26,29,32,33,35,39,41,57,59,64,71,93,
          101,107,125,128,137,149,161,179,191,197,227,239,256,269,281,311,347,
          419,431,461,512,521,569,599,617,641,659,782,809,821,827,857,881,1019,
          1024,1030,1031,1034,1049,1054,1061,1091,1151
COMMENT (the only comment; the conjecture):
  Conjecture: A202274 gives all terms of A028982 that occur in this sequence.
AUTHOR:   Antti Karttunen, Dec 13 2024
```

The comment is unsigned, so it is the author's (Antti Karttunen, Dec 13 2024).
The entry has no later comment retracting it.  Cross-referenced entries:

* A003961: completely multiplicative with `a(prime(k)) = prime(k+1)`.
* A028982: squares and twice squares (positive terms).
* A202274: numbers `k` for which `sigma(k) = 2^m - 1` for some `m`.

## Status

**False.**  This module refutes the conjecture with `k = 970225`:

* `k = 5^2 · 197^2 = 985^2`, a square, so `k ∈ A028982`;
* `A003961(k) = 7^2 · 199^2 = 1393^2 = 1940449`, so `A003961(k) - 2k = -1`
  (the Pell identity `1393^2 - 2 · 985^2 = -1`), which divides everything,
  so `k ∈ A378983`;
* `sigma(k) = 31 · 39007 = 1209217` and `sigma(k) + 1 = 1209218 = 2 · 604609`
  is not a power of two, so `k ∉ A202274`.

Computational evidence (Sage, 2026-10-21): the definitions below reproduce all
67 listed terms of A378983; among the 53982 squares and twice squares up to
`10^9`, the only one where A378983 membership and A202274 membership disagree
is `970225`.  (The triage scan to `10^12` reported no further disagreement.)
The b-file (`n ≤ 20000`) ends below `970225`.

## Formal conventions

* `nextPrime p` is the least prime `> p`; on primes it is `prime(i) ↦
  prime(i+1)`.  `a003961 n` is `∏ p^e ∥ n, nextPrime(p)^e` via
  `Nat.factorization`, so `a003961 1 = 1` and (junk) `a003961 0 = 1`.
* Divisibility is in `ℤ`, with both naturals cast before subtracting.
  `A003961(k)` is odd, so `A003961(k) - 2k ≠ 0` and the `0 ∣ x` convention
  never matters.
* All three sets are restricted to positive `k`; this guard is load-bearing
  for A202274, since `σ 1 0 = 0 = 2^0 - 1`.  A202274's condition is stated as
  `σ 1 k + 1 = 2^m`, avoiding `ℕ` subtraction.
-/
import Mathlib

set_option autoImplicit false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Candidates.A378983Refutation

/-! ## Definition layer -/

/-- The least prime strictly greater than `p`; on the `i`-th prime it returns
the `(i+1)`-th prime. -/
def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- A003961: the completely multiplicative function with
`a(prime(i)) = prime(i+1)`, i.e. `n = ∏ p^e ↦ ∏ nextPrime(p)^e`. -/
def a003961 (n : ℕ) : ℕ := n.factorization.prod fun p e => nextPrime p ^ e

/-- A378983 membership: `k ≥ 1` and
`(A003961(k) - 2k) ∣ (A003961(k) - (1 + σ(k)))` in `ℤ`. -/
def IsA378983 (k : ℕ) : Prop :=
  0 < k ∧ ((a003961 k : ℤ) - 2 * k) ∣ ((a003961 k : ℤ) - (1 + σ 1 k))

/-- A028982 membership: `k ≥ 1` is a square or twice a square. -/
def IsA028982 (k : ℕ) : Prop := 0 < k ∧ (IsSquare k ∨ ∃ m : ℕ, k = 2 * m ^ 2)

/-- A202274 membership: `k ≥ 1` and `σ(k) = 2^m - 1` for some `m`, written as
`σ(k) + 1 = 2^m`. -/
def IsA202274 (k : ℕ) : Prop := 0 < k ∧ ∃ m : ℕ, σ 1 k + 1 = 2 ^ m

/-- Membership in A378983 is decidable (used only for the ground-truth checks). -/
instance (k : ℕ) : Decidable (IsA378983 k) := by
  unfold IsA378983
  infer_instance

/-! ## Basic lemmas -/

/-- `A003961(m · n) = A003961(m) · A003961(n)` for nonzero `m, n`. -/
theorem a003961_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    a003961 (m * n) = a003961 m * a003961 n := by
  unfold a003961
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- `A003961(p^e) = nextPrime(p)^e` for prime `p`. -/
theorem a003961_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    a003961 (p ^ e) = nextPrime p ^ e := by
  unfold a003961
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (pow_zero _)

/-- To identify `nextPrime p`: a prime `q > p` with no prime strictly between. -/
theorem nextPrime_eq {p q : ℕ} (hpq : p < q) (hq : q.Prime)
    (hgap : ∀ n, p < n → n < q → ¬ n.Prime) : nextPrime p = q := by
  unfold nextPrime
  rw [Nat.find_eq_iff]
  exact ⟨⟨hpq, hq⟩, fun n hn hprime => hgap n hprime.1 hn hprime.2⟩

/-- The prime after `5` is `7`. -/
theorem nextPrime_five : nextPrime 5 = 7 :=
  nextPrime_eq (by norm_num) (by norm_num) fun n hlo hhi => by
    obtain rfl : n = 6 := by omega
    norm_num

/-- The prime after `19` is `23`. -/
theorem nextPrime_nineteen : nextPrime 19 = 23 :=
  nextPrime_eq (by norm_num) (by norm_num) fun n hlo hhi => by
    interval_cases n <;> norm_num

/-- The prime after `37` is `41`. -/
theorem nextPrime_thirtyseven : nextPrime 37 = 41 :=
  nextPrime_eq (by norm_num) (by norm_num) fun n hlo hhi => by
    interval_cases n <;> norm_num

/-- The prime after `197` is `199`. -/
theorem nextPrime_197 : nextPrime 197 = 199 :=
  nextPrime_eq (by norm_num) (by norm_num) fun n hlo hhi => by
    obtain rfl : n = 198 := by omega
    norm_num

/-! ## Ground truth -/

-- `A003961(1..10) = 1, 3, 5, 9, 7, 15, 11, 27, 25, 21` (OEIS A003961).
example : (List.range 10).map (fun n => a003961 (n + 1)) =
    [1, 3, 5, 9, 7, 15, 11, 27, 25, 21] := by
  decide +kernel

/-- `19 ∉ A378983`: `A003961(19) - 38 = -15` does not divide `23 - 21 = 2`. -/
theorem not_isA378983_nineteen : ¬ IsA378983 19 := by
  rintro ⟨-, hdvd⟩
  have hf : a003961 19 = 23 := by
    rw [← pow_one 19, a003961_prime_pow (by norm_num), nextPrime_nineteen, pow_one]
  have hs : σ 1 19 = 20 := by decide +kernel
  rw [hf, hs] at hdvd
  norm_num at hdvd

/-- `37 ∉ A378983`: `A003961(37) - 74 = -33` does not divide `41 - 39 = 2`. -/
theorem not_isA378983_thirtyseven : ¬ IsA378983 37 := by
  rintro ⟨-, hdvd⟩
  have hf : a003961 37 = 41 := by
    rw [← pow_one 37, a003961_prime_pow (by norm_num), nextPrime_thirtyseven, pow_one]
  have hs : σ 1 37 = 38 := by decide +kernel
  rw [hf, hs] at hdvd
  norm_num at hdvd

/-- `38 ∉ A378983`: `A003961(38) - 76 = -7` does not divide `69 - 61 = 8`. -/
theorem not_isA378983_thirtyeight : ¬ IsA378983 38 := by
  rintro ⟨-, hdvd⟩
  have hf : a003961 38 = 69 := by
    rw [show (38 : ℕ) = 2 ^ 1 * 19 ^ 1 by norm_num, a003961_mul (by norm_num) (by norm_num),
      a003961_prime_pow (by norm_num), a003961_prime_pow (by norm_num),
      nextPrime_nineteen]
    have h2 : nextPrime 2 = 3 := by decide +kernel
    rw [h2]
    norm_num
  have hs : σ 1 38 = 60 := by decide +kernel
  rw [hf, hs] at hdvd
  norm_num at hdvd

-- The terms of A378983 below `42` are exactly the listed
-- `1, 2, 3, 4, 5, 8, 10, 11, 15, 16, 17, 25, 26, 29, 32, 33, 35, 39, 41`.
-- (`19`, `37`, `38` go through the lemmas above: kernel evaluation of
-- `nextPrime 19` and `nextPrime 37` by `decide` is very slow.)
example (k : ℕ) (hk : k < 42) :
    IsA378983 k ↔ k ∈ [1, 2, 3, 4, 5, 8, 10, 11, 15, 16, 17, 25, 26, 29, 32, 33, 35, 39, 41] := by
  interval_cases k
  all_goals first
    | exact iff_of_false not_isA378983_nineteen (by decide)
    | exact iff_of_false not_isA378983_thirtyseven (by decide)
    | exact iff_of_false not_isA378983_thirtyeight (by decide)
    | decide +kernel

/-! ## The conjecture -/

/-- **Karttunen's conjecture (A378983, Antti Karttunen, Dec 13 2024).**

Verbatim: "Conjecture: A202274 gives all terms of A028982 that occur in this
sequence."

Formalized: a natural number is a square-or-twice-square term of A378983 if
and only if it is a term of A202274. -/
def Conjecture : Prop :=
  ∀ k : ℕ, IsA028982 k ∧ IsA378983 k ↔ IsA202274 k

/-! ## Refutation -/

/-- `970225 = 5^2 · 197^2`. -/
theorem witness_eq : (970225 : ℕ) = 5 ^ 2 * 197 ^ 2 := by norm_num

/-- `A003961(970225) = 7^2 · 199^2 = 1940449`. -/
theorem a003961_witness : a003961 970225 = 1940449 := by
  rw [witness_eq, a003961_mul (by norm_num) (by norm_num),
    a003961_prime_pow (by norm_num), a003961_prime_pow (by norm_num),
    nextPrime_five, nextPrime_197]
  norm_num

/-- `σ(970225) = σ(5^2) · σ(197^2) = 31 · 39007 = 1209217`. -/
theorem sigma_witness : σ 1 970225 = 1209217 := by
  rw [witness_eq, isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num)]
  simp [Finset.sum_range_succ]

/-- `970225 = 985^2` is a square, hence in A028982. -/
theorem isA028982_witness : IsA028982 970225 :=
  ⟨by norm_num, Or.inl ⟨985, by norm_num⟩⟩

/-- `970225 ∈ A378983`: here `A003961(k) - 2k = -1`. -/
theorem isA378983_witness : IsA378983 970225 := by
  refine ⟨by norm_num, ?_⟩
  rw [a003961_witness]
  have hunit : ((1940449 : ℕ) : ℤ) - 2 * ((970225 : ℕ) : ℤ) = -1 := by norm_num
  rw [hunit]
  exact isUnit_neg_one.dvd

/-- `970225 ∉ A202274`: `σ(970225) + 1 = 1209218` lies strictly between
`2^20` and `2^21`. -/
theorem not_isA202274_witness : ¬ IsA202274 970225 := by
  rintro ⟨-, m, hm⟩
  rw [sigma_witness] at hm
  rcases Nat.lt_or_ge m 21 with hlt | hge
  · have hle : 2 ^ m ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hle : 2 ^ 21 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    omega

/-- **Karttunen's A378983 conjecture is false.**

Counterexample: `k = 970225 = 985^2 = 5^2 · 197^2`.  It is a square, and
`A003961(k) = 1393^2` with `1393^2 - 2 · 985^2 = -1` (a Pell coincidence), so
`-1 ∣ A003961(k) - (1 + σ(k))` puts `k` in A378983.  But
`σ(k) + 1 = 1209218 = 2 · 604609` is not a power of two, so `k ∉ A202274`.
The same mechanism admits `25` (`A003961(25) - 50 = -1`), where it happens
that `σ(25) = 31` is a Mersenne number.  The conjecture was probably
extrapolated from the b-file range `n ≤ 20000`, which ends below `970225`;
no corrected form is evident beyond excluding such `-1` coincidences. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  exact not_isA202274_witness
    ((hconj 970225).mp ⟨isA028982_witness, isA378983_witness⟩)

end Candidates.A378983Refutation
