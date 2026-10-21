/-
# A322327 — Schulte: `A005361(n) * k^omega(n)` is multiplicative for every `k`

## OEIS source (retrieved with `oeis show A322327` and https://oeis.org/A322327, 2026-10-21)

```
NAME:     a(n) = A005361(n) * A034444(n).
TERMS:    1,2,2,4,2,4,2,6,4,4,2,8,2,4,4,8,2,8,2,8,4,4,2,12,4,4,6,8,2,8,...
AUTHOR:   Werner Schulte, Dec 03 2018
COMMENT (the conjecture; the comment carries no signature of its own, so it is
the author's, Werner Schulte, Dec 03 2018):
  Conjecture: Let k be some fixed integer and a_k(n) = A005361(n) * k^A001221(n)
  for n > 0 with 0^0 = 1. Then a_k(n) is multiplicative with a_k(p^e) = k*e for
  prime p and e > 0. For k = 0 see A000007 (offset 1), for k = 1 see A005361,
  for k = 2 see this sequence, for k = 3 see A226602 (offset 1), and for k = 4
  see A322328.
FORMULA:  Multiplicative with a(p^e) = 2*e for prime p and e > 0.
```

## Status

Triage literature status: "open" (no proof in the entry), tractability
"trivial": the claim is immediate from the multiplicativity of the product of
exponents `A005361` and of `k^omega`.  This file proves it.

## Definitions

* `A005361 n = ∏ p ∈ n.primeFactors, n.factorization p` (product of exponents in
  the prime factorization; `A005361 1 = 1` as an empty product).
* `A001221 = ω` is Mathlib's `ArithmeticFunction.cardDistinctFactors`.
* `ak k n = A005361 n * k ^ cardDistinctFactors n` in `ℤ`; Lean's `0 ^ 0 = 1` matches the entry's
  convention.  The sequence has offset 1; the arithmetic function `akFun k`
  sends `0` to `0`, as `ArithmeticFunction` requires, and agrees with `ak k` on
  `n > 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A322327AnyFixedOmega

open ArithmeticFunction

/-- OEIS A005361: the product of the exponents in the prime factorization of
`n` (`1` for `n = 1`). -/
def A005361 (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, n.factorization p

/-- Schulte's `a_k(n) = A005361(n) * k ^ A001221(n)`, with `A001221 = ω`. -/
def ak (k : ℤ) (n : ℕ) : ℤ := (A005361 n : ℤ) * k ^ cardDistinctFactors n

/-- `a_k` packaged as an arithmetic function (value `0` at `0`, `ak k n` for
`n > 0`). -/
def akFun (k : ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else ak k n, if_pos rfl⟩

/-! ## Ground truth -/

example : A005361 1 = 1 := by decide +kernel
example : A005361 8 = 3 := by decide +kernel
example : A005361 72 = 6 := by decide +kernel

example : (List.range 30).map (fun i => ak 2 (i + 1)) =
    [1, 2, 2, 4, 2, 4, 2, 6, 4, 4, 2, 8, 2, 4, 4, 8, 2, 8, 2, 8, 4, 4, 2, 12, 4, 4, 6, 8,
      2, 8] := by
  decide +kernel

/-! ## The product of exponents is multiplicative -/

/-- `A005361` is multiplicative on coprime arguments. -/
theorem A005361_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    A005361 (m * n) = A005361 m * A005361 n := by
  have hfac : (m * n).factorization = m.factorization + n.factorization :=
    Nat.factorization_mul_of_coprime h
  have hdisj : Disjoint m.primeFactors n.primeFactors := h.disjoint_primeFactors
  have hm : ∀ p ∈ m.primeFactors, (m * n).factorization p = m.factorization p := by
    intro p hp
    have hpn : p ∉ n.primeFactors := Finset.disjoint_left.mp hdisj hp
    have hzero : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    rw [hfac, Finsupp.add_apply, hzero, add_zero]
  have hn : ∀ p ∈ n.primeFactors, (m * n).factorization p = n.factorization p := by
    intro p hp
    have hpm : p ∉ m.primeFactors := Finset.disjoint_right.mp hdisj hp
    have hzero : m.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    rw [hfac, Finsupp.add_apply, hzero, zero_add]
  unfold A005361
  rw [h.primeFactors_mul, Finset.prod_union hdisj, Finset.prod_congr rfl hm,
    Finset.prod_congr rfl hn]

/-- `A005361 (p ^ e) = e` for a prime `p` and `e ≠ 0`. -/
theorem A005361_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    A005361 (p ^ e) = e := by
  unfold A005361
  rw [Nat.primeFactors_prime_pow he hp, Finset.prod_singleton, hp.factorization_pow,
    Finsupp.single_eq_same]

/-! ## Multiplicativity of `a_k` -/

/-- `a_k(1) = 1`. -/
theorem ak_one (k : ℤ) : ak k 1 = 1 := by
  simp [ak, A005361]

/-- `a_k` is multiplicative on coprime arguments. -/
theorem ak_mul_of_coprime (k : ℤ) {m n : ℕ} (h : m.Coprime n) :
    ak k (m * n) = ak k m * ak k n := by
  unfold ak
  rw [A005361_mul_of_coprime h, cardDistinctFactors_mul h, pow_add]
  push_cast
  ring

/-- `a_k(p ^ e) = k * e` for a prime `p` and `e > 0`. -/
theorem ak_prime_pow (k : ℤ) {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ak k (p ^ e) = k * e := by
  unfold ak
  rw [A005361_prime_pow hp he.ne', cardDistinctFactors_apply_prime_pow hp he.ne', pow_one,
    mul_comm]

/-- `akFun k` agrees with `ak k` on positive arguments. -/
theorem akFun_apply_of_pos (k : ℤ) {n : ℕ} (hn : 0 < n) : akFun k n = ak k n := by
  simp [akFun, hn.ne']

/-! ## The conjecture -/

/-- **Schulte's conjecture (A322327, Werner Schulte, Dec 03 2018).**

Verbatim: "Conjecture: Let k be some fixed integer and a_k(n) = A005361(n) *
k^A001221(n) for n > 0 with 0^0 = 1. Then a_k(n) is multiplicative with
a_k(p^e) = k*e for prime p and e > 0."

For every integer `k`, the arithmetic function `n ↦ A005361(n) * k ^ ω(n)`
(`n > 0`) is multiplicative and takes the value `k * e` at `p ^ e` for every
prime `p` and every `e > 0`. -/
theorem schulte_conjecture (k : ℤ) :
    (akFun k).IsMultiplicative ∧
      ∀ p e : ℕ, p.Prime → 0 < e → akFun k (p ^ e) = k * e := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [akFun_apply_of_pos k Nat.one_pos, ak_one]
  · intro m n h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [akFun]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [akFun]
    rw [akFun_apply_of_pos k (Nat.mul_pos hm hn), akFun_apply_of_pos k hm,
      akFun_apply_of_pos k hn, ak_mul_of_coprime k h]
  · intro p e hp he
    rw [akFun_apply_of_pos k (Nat.pow_pos hp.pos), ak_prime_pow k hp he]

/-- Sequence form of Schulte's conjecture (offset 1): `a_k(1) = 1`,
`a_k(m n) = a_k(m) a_k(n)` for coprime `m, n > 0`, and `a_k(p ^ e) = k * e` for
prime `p` and `e > 0`. -/
theorem schulte_conjecture_seq (k : ℤ) :
    ak k 1 = 1 ∧
      (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → ak k (m * n) = ak k m * ak k n) ∧
      ∀ p e : ℕ, p.Prime → 0 < e → ak k (p ^ e) = k * e :=
  ⟨ak_one k, fun _ _ _ _ h => ak_mul_of_coprime k h, fun _ _ hp he => ak_prime_pow k hp he⟩

/-- Non-vacuity: the prime-power clause instantiated at `k = 3`, `p = 2`, `e = 3`. -/
example : akFun 3 (2 ^ 3) = 9 := by
  rw [(schulte_conjecture 3).2 2 3 Nat.prime_two (by norm_num)]
  norm_num

end Candidates.A322327AnyFixedOmega
