/-
Least factorial containing lcm(1,…,n) (OEIS A094802; Jon Perry, Jun 11 2004).

For n≥5 the least positive k such that every integer 1,…,n divides k!
is the largest prime at most n. The theorem includes prime and composite
corollaries. The boundary n=4 is exceptional: a(4)=4.
The proof uses Bertrand's postulate and a factorization argument.
-/
import Mathlib

set_option autoImplicit false

open Nat

namespace Candidates.A094802LeastLcmEquals

/-! ## Definition layer -/

/-- The defining property of A094802: `k` is positive and every `j` with
`1 ≤ j ≤ n` divides `k!`.  Positivity mirrors the Maple program's search
`for k from 1`, which gives `a(1) = 1` rather than `0`. -/
def AllDvdFactorial (n k : ℕ) : Prop :=
  0 < k ∧ ∀ j ∈ Finset.Icc 1 n, j ∣ k !

/-- `AllDvdFactorial n k` is decidable (a bounded check over `Finset.Icc 1 n`). -/
instance (n k : ℕ) : Decidable (AllDvdFactorial n k) := by
  unfold AllDvdFactorial
  infer_instance

/-- Some `k` (namely `max n 1`) has the defining property. -/
theorem exists_allDvdFactorial (n : ℕ) : ∃ k, AllDvdFactorial n k :=
  ⟨max n 1, lt_max_of_lt_right Nat.one_pos, fun j hj => by
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
    exact Nat.dvd_factorial hj1 (le_max_of_le_left hjn)⟩

/-- **A094802.** `a n` is the smallest positive `k` such that each of
`1, 2, …, n` divides `k!`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.find (exists_allDvdFactorial n)

/-! ## Examples against the DATA line -/

example : a 1 = 1 := by rw [a, Nat.find_eq_iff]; decide
example : a 2 = 2 := by rw [a, Nat.find_eq_iff]; decide
example : a 3 = 3 := by rw [a, Nat.find_eq_iff]; decide
example : a 4 = 4 := by rw [a, Nat.find_eq_iff]; decide
example : a 5 = 5 := by rw [a, Nat.find_eq_iff]; decide
example : a 6 = 5 := by rw [a, Nat.find_eq_iff]; decide
example : a 7 = 7 := by rw [a, Nat.find_eq_iff]; decide
example : a 8 = 7 := by rw [a, Nat.find_eq_iff]; decide
example : a 9 = 7 := by rw [a, Nat.find_eq_iff]; decide
example : a 10 = 7 := by rw [a, Nat.find_eq_iff]; decide
example : a 11 = 11 := by rw [a, Nat.find_eq_iff]; decide
example : a 12 = 11 := by rw [a, Nat.find_eq_iff]; decide

-- The guard `5 ≤ n` is key: `a 4 = 4` is not prime.
example : ¬ (a 4).Prime := by
  have h4 : a 4 = 4 := by rw [a, Nat.find_eq_iff]; decide
  rw [h4]
  decide

/-! ## Proof -/

/-- If `0 < a < b ≤ m` then `a * b ∣ m!`. -/
theorem mul_dvd_factorial_of_lt {x y m : ℕ} (hx : 0 < x) (hxy : x < y) (hym : y ≤ m) :
    x * y ∣ m ! := by
  obtain ⟨c, rfl⟩ : ∃ c, y = c + 1 := ⟨y - 1, by omega⟩
  have hxc : x ∣ c ! := Nat.dvd_factorial hx (by omega)
  have hstep : x * (c + 1) ∣ (c + 1) ! := by
    rw [Nat.factorial_succ, mul_comm x]
    exact Nat.mul_dvd_mul_left (c + 1) hxc
  exact hstep.trans (Nat.factorial_dvd_factorial hym)

/-- **Key bridge.** Let `P` be the largest prime `≤ n`, with `5 ≤ n`.  Then every
`j` with `1 ≤ j ≤ n` divides `P!`.  For `j ≤ P` this is immediate; for
`P < j ≤ n`, Bertrand gives `n < 2P`, and `j` is composite, `j = a * b` with
`a = minFac j ≤ b < P`; the square case `a = b` uses `2a ≤ P`. -/
theorem dvd_factorial_largest_prime {n P : ℕ} (hn : 5 ≤ n) (hP : P.Prime)
    (hmax : ∀ q, q.Prime → q ≤ n → q ≤ P) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    j ∣ P ! := by
  rcases le_or_gt j P with hjP | hPj
  · exact Nat.dvd_factorial hj1 hjP
  -- Bertrand: `n < 2 * P`.
  have h2P : n < 2 * P := by
    obtain ⟨q, hq, hPq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul P hP.ne_zero
    by_contra hcon
    have hqP : q ≤ P := hmax q hq (by omega)
    omega
  have h5P : 5 ≤ P := hmax 5 Nat.prime_five hn
  -- `j` is composite.
  have hjnp : ¬ j.Prime := fun hj => by
    have hjP' : j ≤ P := hmax j hj hjn
    omega
  set x := j.minFac with hx
  have hxpos : 0 < x := Nat.minFac_pos j
  have hx2 : 2 ≤ x := (Nat.minFac_prime (by omega)).two_le
  have hsq : x ^ 2 ≤ j := Nat.minFac_sq_le_self (by omega) hjnp
  obtain ⟨y, hy⟩ : x ∣ j := Nat.minFac_dvd j
  have hxy : x ≤ y := by nlinarith
  have hyP : y < P := by nlinarith
  rcases lt_or_eq_of_le hxy with hlt | heq
  · rw [hy]
    exact mul_dvd_factorial_of_lt hxpos hlt hyP.le
  · -- Square case `j = x * x`
    subst heq
    have h2x : 2 * x ≤ P := by
      by_contra hcon
      have hx3 : 3 ≤ x := by nlinarith
      have h7 : 7 ≤ P := hmax 7 (by norm_num) (by nlinarith)
      nlinarith
    have hdvd : x * (2 * x) ∣ P ! := mul_dvd_factorial_of_lt hxpos (by omega) h2x
    rw [hy]
    exact (Nat.mul_dvd_mul_left x (Dvd.intro_left 2 rfl)).trans hdvd

/-- For `5 ≤ n`, if `P` is the largest prime `≤ n` then `a n = P`. -/
theorem a_eq_of_largest_prime {n P : ℕ} (hn : 5 ≤ n) (hP : P.Prime) (hPn : P ≤ n)
    (hmax : ∀ q, q.Prime → q ≤ n → q ≤ P) : a n = P := by
  have hPprop : AllDvdFactorial n P := ⟨hP.pos, fun j hj => by
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
    exact dvd_factorial_largest_prime hn hP hmax hj1 hjn⟩
  apply le_antisymm
  · exact Nat.find_min' (exists_allDvdFactorial n) hPprop
  · have hspec := (Nat.find_spec (exists_allDvdFactorial n)).2 P
      (Finset.mem_Icc.mpr ⟨hP.one_le, hPn⟩)
    exact (hP.dvd_factorial).mp hspec

/-- **A094802 conjecture (Jon Perry, Jun 11 2004), proved.**  For `n ≥ 5`, `a n`
is the largest prime `≤ n`: it is prime, at most `n`, and every prime `q ≤ n`
satisfies `q ≤ a n`. -/
theorem a_eq_largest_prime (n : ℕ) (hn : 5 ≤ n) :
    (a n).Prime ∧ a n ≤ n ∧ ∀ q, q.Prime → q ≤ n → q ≤ a n := by
  set P := Nat.findGreatest Nat.Prime n with hPdef
  have hP : P.Prime := Nat.findGreatest_spec (P := Nat.Prime) (by omega : 2 ≤ n) Nat.prime_two
  have hPn : P ≤ n := Nat.findGreatest_le n
  have hmax : ∀ q, q.Prime → q ≤ n → q ≤ P := fun q hq hqn => Nat.le_findGreatest hqn hq
  rw [a_eq_of_largest_prime hn hP hPn hmax]
  exact ⟨hP, hPn, hmax⟩

/-- Prime branch: for prime `n ≥ 5`, `a n = n`. -/
theorem a_eq_self_of_prime (n : ℕ) (hn : 5 ≤ n) (hnp : n.Prime) : a n = n :=
  a_eq_of_largest_prime hn hnp le_rfl (fun _ _ hqn => hqn)

/-- Composite branch: for composite `n ≥ 5`, `a n` is the previous
prime, i.e. a prime `< n` with no prime strictly between it and `n`. -/
theorem a_of_not_prime (n : ℕ) (hn : 5 ≤ n) (hnp : ¬ n.Prime) :
    (a n).Prime ∧ a n < n ∧ ∀ q, q.Prime → a n < q → n ≤ q := by
  obtain ⟨hpr, hle, hmax⟩ := a_eq_largest_prime n hn
  refine ⟨hpr, lt_of_le_of_ne hle (fun h => hnp (h ▸ hpr)), fun q hq hlt => ?_⟩
  by_contra hcon
  have hqa : q ≤ a n := hmax q hq (by omega)
  omega

end Candidates.A094802LeastLcmEquals
