/-
# A018804 — Ordowski: `n ∣ P(n) + 1` characterizes the primes

Thomas Ordowski's conjecture in OEIS A018804 (2014), with Varun Vejalla's
counterexample (2025). Pillai's function is `P(n) = Σ_{k=1}^n gcd(k,n)`;
Vladeta Jovovic's divisor-sum formula (2001) gives its multiplicativity.

At `n = 3 · 37 · 43 · 42307 · 116341 = 23492890653051`, the prime factors
are pairwise coprime and `P(n) = 610815156979325`, so `P(n)+1 = 26n`
although `n` is composite. The implication from primality to divisibility remains true:
`P(p)+1 = 2p` for prime `p`.

The convention `pillai 0 = 0` is an empty sum; the conjecture uses `1 < n`.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Candidates.A018804Refutation

/-! ## Definitions -/

/-- A018804, Pillai's arithmetical function: `P(n) = ∑_{k=1}^{n} gcd(k, n)`. -/
def pillai (n : ℕ) : ℕ := ∑ k ∈ Icc 1 n, Nat.gcd k n

/-! ## Examples -/

-- `P(1..19) = 1, 3, 5, 8, 9, 15, 13, 20, 21, 27, 21, 40, 25, 39, 45, 48, 33, 63, 37`
-- (the first 19 listed terms of A018804).
example : (List.range 19).map (fun i => pillai (i + 1)) =
    [1, 3, 5, 8, 9, 15, 13, 20, 21, 27, 21, 40, 25, 39, 45, 48, 33, 63, 37] := by
  decide

/-! ## Pillai's function as a Dirichlet convolution -/

/-- Reindexing the defining sum over `k ∈ [0, n)`: `P(n) = ∑_{k<n} gcd(n, k)`
(the terms `k = 0` and `k = n` both contribute `n`). -/
theorem pillai_eq_sum_range (n : ℕ) : pillai n = ∑ k ∈ range n, Nat.gcd n k := by
  have hset : range (n + 1) = insert 0 (Icc 1 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  have hnot : 0 ∉ Icc 1 n := by simp
  have hsum : ∑ k ∈ range (n + 1), Nat.gcd n k =
      Nat.gcd n 0 + ∑ k ∈ Icc 1 n, Nat.gcd n k := by
    rw [hset, sum_insert hnot]
  rw [sum_range_succ, Nat.gcd_zero_right, Nat.gcd_self, add_comm] at hsum
  simp only [pillai, Nat.gcd_comm _ n]
  omega

/-- Jovovic's formula: `P(n) = ∑_{d ∣ n} d · φ(n / d)`, by grouping `k` according
to `gcd(n, k) = d`. -/
theorem pillai_eq_sum_divisors (n : ℕ) :
    pillai n = ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [pillai]
  rw [pillai_eq_sum_range,
    ← sum_fiberwise_of_maps_to (s := range n) (t := n.divisors) (g := fun k => Nat.gcd n k)
      (fun x _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩)]
  refine sum_congr rfl fun d hd => ?_
  rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd),
    sum_congr rfl (g := fun _ => d) (fun x hx => (mem_filter.1 hx).2), sum_const,
    smul_eq_mul, mul_comm]

/-- Euler's totient as an arithmetic function. -/
def totientArith : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

/-- Euler's totient is multiplicative. -/
theorem isMultiplicative_totientArith : totientArith.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  exact ⟨Nat.totient_one, fun {_ _} _ _ hmn => Nat.totient_mul hmn⟩

/-- `P = id ∗ φ` as arithmetic functions. -/
theorem pillai_eq_id_mul_totient (n : ℕ) :
    pillai n = (ArithmeticFunction.id * totientArith) n := by
  rw [ArithmeticFunction.mul_apply, pillai_eq_sum_divisors,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.id a * totientArith b)]
  rfl

/-- `P` is multiplicative: `P(m n) = P(m) P(n)` for coprime `m, n`. -/
theorem pillai_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    pillai (m * n) = pillai m * pillai n := by
  simp only [pillai_eq_id_mul_totient]
  exact (ArithmeticFunction.isMultiplicative_id.mul
    isMultiplicative_totientArith).map_mul_of_coprime h

/-- For a prime `p`, `P(p) = 2p - 1` (Jehn's remark in the entry). -/
theorem pillai_prime {p : ℕ} (hp : p.Prime) : pillai p = 2 * p - 1 := by
  rw [pillai_eq_sum_divisors, hp.divisors, sum_pair hp.one_lt.ne, Nat.div_one,
    Nat.div_self hp.pos, Nat.totient_prime hp, Nat.totient_one, one_mul, mul_one]
  have htwo : 2 ≤ p := hp.two_le
  omega

/-! ## The conjecture -/

/-- **Ordowski's conjecture (A018804, Thomas Ordowski, 2014).**

Formalized: for every `n > 1`, `n ∣ P(n) + 1` if and only if `n` is prime,
where `P` is Pillai's function `pillai`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 < n → (n ∣ pillai n + 1 ↔ n.Prime)

/-! ## The true direction -/

/-- The direction Ordowski's conjecture gets right: every prime `p` divides
`P(p) + 1 = 2p`. -/
theorem dvd_pillai_add_one_of_prime {p : ℕ} (hp : p.Prime) : p ∣ pillai p + 1 := by
  have htwo : 2 ≤ p := hp.two_le
  have hval : pillai p + 1 = p * 2 := by
    rw [pillai_prime hp]
    omega
  rw [hval]
  exact dvd_mul_right p 2

/-! ## Refutation -/

/-- The counterexample value: `P(3 · 37 · 43 · 42307 · 116341)
= 5 · 73 · 85 · 84613 · 232681 = 610815156979325`. -/
theorem pillai_counterexample :
    pillai (3 * 37 * 43 * 42307 * 116341) = 610815156979325 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp37 : Nat.Prime 37 := by norm_num
  have hp43 : Nat.Prime 43 := by norm_num
  have hp42307 : Nat.Prime 42307 := by norm_num
  have hp116341 : Nat.Prime 116341 := by norm_num
  rw [pillai_mul_of_coprime (by norm_num), pillai_mul_of_coprime (by norm_num),
    pillai_mul_of_coprime (by norm_num), pillai_mul_of_coprime (by norm_num),
    pillai_prime hp3, pillai_prime hp37, pillai_prime hp43, pillai_prime hp42307,
    pillai_prime hp116341]

/-- **Ordowski's conjecture is false** (counterexample of Varun Vejalla,
recorded in A018804, 2025).

The composite `n = 3 · 37 · 43 · 42307 · 116341 = 23492890653051` satisfies
`P(n) + 1 = 610815156979326 = 26 · n`, so `n ∣ P(n) + 1` although `n` is not
prime. The implication from primality to divisibility holds; see
`dvd_pillai_add_one_of_prime`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hiff := hconj (3 * 37 * 43 * 42307 * 116341) (by norm_num)
  rw [pillai_counterexample] at hiff
  have hdvd : 3 * 37 * 43 * 42307 * 116341 ∣ 610815156979325 + 1 := by norm_num
  have hnp : ¬ Nat.Prime (3 * 37 * 43 * 42307 * 116341) := by norm_num
  exact hnp (hiff.1 hdvd)

end Candidates.A018804Refutation
