/-
# A390088 — the integers with no prime-digit base are exactly 0, 1, 4, 6, 9

The unsigned conjecture in OEIS A390088, an entry by Felix Huber (2025).
The least base with only prime digits is zero exactly at `0,1,4,6,9`.
For other values, use the two-digit witnesses `2b+2=(22)_b` (`b ≥ 3`) and
`2b+3=(23)_b` (`b ≥ 4`), base `p+1` for prime `p`, and a finite check
for `n ≤ 10`.

## Definitional fidelity

`a` mirrors the PARI program exactly: it searches the bases `b = 2, …, n + 1`
(the list `List.range' 2 n`) and returns the first one in which every digit of
`n` (Mathlib `Nat.digits`, least significant first) is prime, else `0`.  For
`n = 0` the search range is empty, so `a 0 = 0`, matching the entry's term
`a(0) = 0` (the representation of `0` is the non-prime digit `0`; note that
`Nat.digits b 0 = []`).  Bases `b > n + 1` give the same single digit `n` as
`b = n + 1`; `a_eq_zero_iff_not_exists` checks that the bounded search agrees
with the unbounded "no base `b > 1`" reading for `n > 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A390088BaseDigitsPrime

/-- OEIS A390088: `a n` is the least base `b > 1` in which all digits of `n`
are prime, or `0` if there is none.  Mirrors the PARI program: the bases
searched are `2, …, n + 1`. -/
def a (n : ℕ) : ℕ :=
  ((List.range' 2 n).find? (fun b => (Nat.digits b n).all (fun d => decide d.Prime))).getD 0

/-- Examples: the first 30 terms of A390088. -/
example : (List.range 30).map a =
    [0, 0, 3, 4, 0, 6, 0, 8, 3, 0, 4, 4, 5, 5, 4, 4, 7, 5, 5, 7, 6, 6, 10, 6, 7, 9, 3, 8,
      13, 8] := by
  decide

/-- If some base `b` with `2 ≤ b ≤ n + 1` writes `n` with prime digits only,
then `a n ≠ 0`. -/
theorem a_ne_zero_of_base {n b : ℕ} (hb2 : 2 ≤ b) (hbn : b ≤ n + 1)
    (hprime : ∀ d ∈ Nat.digits b n, d.Prime) : a n ≠ 0 := by
  unfold a
  set p : ℕ → Bool := fun c => (Nat.digits c n).all (fun d => decide d.Prime) with hp
  have hmem : b ∈ List.range' 2 n := by
    rw [List.mem_range']
    exact ⟨b - 2, by omega, by omega⟩
  have hpb : p b = true := by
    simp only [hp, List.all_eq_true, decide_eq_true_eq]
    exact hprime
  cases hfind : (List.range' 2 n).find? p with
  | none =>
    exact absurd hpb (List.find?_eq_none.mp hfind b hmem)
  | some c =>
    have hc : c ∈ List.range' 2 n := List.mem_of_find?_eq_some hfind
    rw [List.mem_range'] at hc
    simp only [Option.getD_some]
    omega

/-- If `a n ≠ 0` then some base `b > 1` writes `n` with prime digits only. -/
theorem exists_base_of_a_ne_zero {n : ℕ} (h : a n ≠ 0) :
    ∃ b, 1 < b ∧ ∀ d ∈ Nat.digits b n, d.Prime := by
  unfold a at h
  cases hfind : (List.range' 2 n).find?
      (fun b => (Nat.digits b n).all (fun d => decide d.Prime)) with
  | none => simp only [hfind, Option.getD_none, ne_eq, not_true_eq_false] at h
  | some c =>
    have hc : c ∈ List.range' 2 n := List.mem_of_find?_eq_some hfind
    have hpc := List.find?_some hfind
    rw [List.mem_range'] at hc
    simp only [List.all_eq_true, decide_eq_true_eq] at hpc
    exact ⟨c, by omega, hpc⟩

/-- Even witness: for `b ≥ 3`, `2b + 2` is written `22` in base `b`. -/
theorem digits_two_mul_add_two {b : ℕ} (hb : 3 ≤ b) : Nat.digits b (2 * b + 2) = [2, 2] := by
  rw [Nat.digits_def' (by omega) (by omega)]
  have hmod : (2 * b + 2) % b = 2 := by
    rw [Nat.mul_comm, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : (2 * b + 2) / b = 2 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
  rw [hmod, hdiv, Nat.digits_of_lt b 2 (by omega) (by omega)]

/-- Odd witness: for `b ≥ 4`, `2b + 3` is written `23` in base `b`
(digit list `[3, 2]`, least significant first). -/
theorem digits_two_mul_add_three {b : ℕ} (hb : 4 ≤ b) : Nat.digits b (2 * b + 3) = [3, 2] := by
  rw [Nat.digits_def' (by omega) (by omega)]
  have hmod : (2 * b + 3) % b = 3 := by
    rw [Nat.mul_comm, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : (2 * b + 3) / b = 2 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
  rw [hmod, hdiv, Nat.digits_of_lt b 2 (by omega) (by omega)]

/-- Every `n ≥ 11` has a prime-digit base, hence `a n ≠ 0`. -/
theorem a_ne_zero_of_eleven_le {n : ℕ} (hn : 11 ≤ n) : a n ≠ 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `n = 2 (k - 1) + 2`, base `k - 1 ≥ 5`
    have hn' : n = 2 * (k - 1) + 2 := by omega
    refine a_ne_zero_of_base (b := k - 1) (by omega) (by omega) ?_
    rw [hn', digits_two_mul_add_two (by omega)]
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hd
    rw [hd]
    exact Nat.prime_two
  · -- `n = 2 (k - 1) + 3`, base `k - 1 ≥ 4`
    have hn' : n = 2 * (k - 1) + 3 := by omega
    refine a_ne_zero_of_base (b := k - 1) (by omega) (by omega) ?_
    rw [hn', digits_two_mul_add_three (by omega)]
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd
    · rw [hd]; exact Nat.prime_three
    · rw [hd]; exact Nat.prime_two

/-- **A390088 conjecture** (OEIS comment, entry by Felix Huber, 2025):
exactly the values `k = 0, 1, 4, 6, 9` satisfy `a(k) = 0`, i.e. every other
`k ≥ 0` has a base `b > 1` in which all its digits are prime. -/
theorem a_eq_zero_iff (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 4, 6, 9} : Finset ℕ) := by
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> decide
  · have hS : n ∉ ({0, 1, 4, 6, 9} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact iff_of_false (a_ne_zero_of_eleven_le hn) hS

/-- The bounded search in `a` agrees with the unbounded reading: for `n > 0`,
`a n = 0` iff no base `b > 1` at all writes `n` with prime digits only. -/
theorem a_eq_zero_iff_not_exists {n : ℕ} (hn : 0 < n) :
    a n = 0 ↔ ¬ ∃ b, 1 < b ∧ ∀ d ∈ Nat.digits b n, d.Prime := by
  constructor
  · rintro h0 ⟨b, hb, hprime⟩
    rcases Nat.lt_or_ge (n + 1) b with hbig | hsmall
    · -- for `b > n + 1` the only digit is `n`, as in base `n + 1`
      have hdig : Nat.digits b n = [n] := Nat.digits_of_lt b n (by omega) (by omega)
      have hnp : n.Prime := hprime n (by rw [hdig]; exact List.mem_singleton_self n)
      refine a_ne_zero_of_base (b := n + 1) (by omega) le_rfl ?_ h0
      rw [Nat.digits_of_lt (n + 1) n (by omega) (by omega)]
      intro d hd
      rw [List.mem_singleton.mp hd]
      exact hnp
    · exact a_ne_zero_of_base (by omega) hsmall hprime h0
  · intro hnone
    by_contra h0
    exact hnone (exists_base_of_a_ne_zero h0)

/-- **A390088 conjecture, digit form**: a positive integer `k` has a base
`b > 1` in which all its digits are prime iff `k ∉ {1, 4, 6, 9}`
(`k = 0`, whose representation is the digit `0`, is the remaining exception). -/
theorem exists_prime_digit_base_iff {n : ℕ} (hn : 0 < n) :
    (∃ b, 1 < b ∧ ∀ d ∈ Nat.digits b n, d.Prime) ↔ n ∉ ({1, 4, 6, 9} : Finset ℕ) := by
  rw [← not_iff_not, not_not, ← a_eq_zero_iff_not_exists hn, a_eq_zero_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

end Candidates.A390088BaseDigitsPrime
