/-
# A093454 — the finiteness conjecture for `lcm(next n numbers)/n!` is false

The finiteness conjecture in OEIS A093454; Robert G. Wilson v's program
(2004) defines the block of 'next n numbers' as
`{n(n-1)/2+1, …, n(n+1)/2}`. The sequence floors its lcm divided by `n!`.

The conjecture is false. The 2-adic valuation of `n!` is at
least `⌊n/2⌋`, while a power of `2` divides the lcm of a block only if it
divides one of its elements, all of which are at most `n(n+1)/2 < 2^⌊n/2⌋`
for `n ≥ 14`.  Hence `L(n)/n!` is a non-integer for every `n ≥ 14`, and in
fact for every `n ≥ 1` outside `{1, 2, 3, 4, 6}` (`factorial_dvd_L_iff`),
which matches Wilson's computational observation.  The conjecture is read as
"`L(n)/n!` is a non-integer for only finitely many indices `n ≥ 1`";
the classification also shows the reading was the opposite of the truth.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A093454Refutation

/-! ## Definitions -/

/-- The "next `n` numbers": the block `{n(n-1)/2 + 1, ..., n(n+1)/2}`.
Both divisions are exact since a product of consecutive integers is even; at
`n = 0` the block is empty. -/
def block (n : ℕ) : Finset ℕ := Finset.Icc (n * (n - 1) / 2 + 1) (n * (n + 1) / 2)

/-- `L(n)`, the least common multiple of the block of the next `n` numbers. -/
def L (n : ℕ) : ℕ := (block n).lcm id

/-- The OEIS sequence A093454: `a(n) = ⌊L(n) / n!⌋`. -/
def a (n : ℕ) : ℕ := L n / n.factorial

/-! ### Examples against the listed terms -/

example : block 6 = {16, 17, 18, 19, 20, 21} := by decide
example : L 5 = 60060 := by decide
example : a 1 = 1 := by decide
example : a 2 = 3 := by decide
example : a 3 = 10 := by decide
example : a 4 = 105 := by decide
example : a 5 = 500 := by decide
example : a 6 = 2261 := by decide
example : a 7 = 24667 := by decide
example : a 8 = 42028 := by decide
example : a 9 = 1230782 := by decide
example : a 10 = 20311562 := by decide
example : a 11 = 4439826 := by decide
example : a 12 = 359052299 := by decide
example : a 21 = 137309505871357313 := by decide

/-! ## The conjecture -/

/-- The A093454 finiteness conjecture: only finitely many indices `n ≥ 1`
have `L(n)/n!` nonintegral, with the quotient taken in `ℚ`. -/
def Conjecture : Prop :=
  {n : ℕ | 1 ≤ n ∧ ¬ ∃ k : ℤ, (L n : ℚ) / (n.factorial : ℚ) = k}.Finite

/-! ## Arithmetic lemmas -/

/-- For `d ≠ 0`, the rational `m / d` is an integer iff `d ∣ m`. -/
theorem exists_int_div_eq_iff_dvd {m d : ℕ} (hd : d ≠ 0) :
    (∃ k : ℤ, (m : ℚ) / (d : ℚ) = k) ↔ d ∣ m := by
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  constructor
  · rintro ⟨k, hk⟩
    have hmq : (m : ℚ) = (k * d : ℤ) := by
      rw [div_eq_iff hdq] at hk
      push_cast
      exact hk
    have hmz : (m : ℤ) = k * d := by exact_mod_cast hmq
    have hdz : (d : ℤ) ∣ (m : ℤ) := ⟨k, by rw [hmz, mul_comm]⟩
    exact Int.natCast_dvd_natCast.mp hdz
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    push_cast
    field_simp

/-- A positive power of a prime dividing the lcm of a finite set of nonzero
naturals divides one of its elements. -/
theorem exists_mem_pow_dvd_of_pow_dvd_lcm {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (s : Finset ℕ) (hs : ∀ x ∈ s, x ≠ 0) (hdvd : p ^ k ∣ s.lcm id) :
    ∃ x ∈ s, p ^ k ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hone : p ^ k = 1 := Nat.dvd_one.mp (by simpa using hdvd)
    exact absurd hone (Nat.one_lt_pow hk.ne' hp.one_lt).ne'
  | insert b t hb ih =>
    have hb0 : b ≠ 0 := hs b (Finset.mem_insert_self b t)
    have ht0 : ∀ x ∈ t, x ≠ 0 := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hlcm0 : t.lcm id ≠ 0 := by
      intro h
      obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h
      exact ht0 x hx hx0
    rw [Finset.lcm_insert] at hdvd
    have hdvd' : p ^ k ∣ Nat.lcm b (t.lcm id) := hdvd
    rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hb0 hlcm0),
      Nat.factorization_lcm hb0 hlcm0, Finsupp.sup_apply, le_sup_iff] at hdvd'
    rcases hdvd' with hle | hle
    · exact ⟨b, Finset.mem_insert_self b t, (hp.pow_dvd_iff_le_factorization hb0).mpr hle⟩
    · obtain ⟨x, hx, hpx⟩ :=
        ih ht0 ((hp.pow_dvd_iff_le_factorization hlcm0).mpr hle)
      exact ⟨x, Finset.mem_insert_of_mem hx, hpx⟩

/-- `2^m ∣ (2m)!`. -/
theorem two_pow_dvd_factorial_two_mul (m : ℕ) : 2 ^ m ∣ (2 * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfac : (2 * (m + 1)).factorial = (2 * (m + 1)) * ((2 * m + 1) * (2 * m).factorial) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [hfac, pow_succ, mul_comm (2 ^ m) 2]
    exact mul_dvd_mul (Dvd.intro (m + 1) rfl) (Dvd.dvd.mul_left ih _)

/-- `(2m+1)(m+1) < 2^m` for `m ≥ 7`. -/
theorem bound_lt_two_pow {m : ℕ} (hm : 7 ≤ m) : (2 * m + 1) * (m + 1) < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    nlinarith

/-- Membership in the block: `n(n-1)/2 + 1 ≤ x ≤ n(n+1)/2`. -/
theorem mem_block_iff {n x : ℕ} :
    x ∈ block n ↔ n * (n - 1) / 2 + 1 ≤ x ∧ x ≤ n * (n + 1) / 2 := Finset.mem_Icc

/-- `L(n)/n!` is a non-integer for every `n ≥ 14`. -/
theorem not_factorial_dvd_L {n : ℕ} (hn : 14 ≤ n) : ¬ n.factorial ∣ L n := by
  intro hdvd
  set m := n / 2 with hm_def
  have hm7 : 7 ≤ m := by omega
  have hn_le : n ≤ 2 * m + 1 := by omega
  have h2m : 2 ^ m ∣ L n :=
    (two_pow_dvd_factorial_two_mul m).trans
      ((Nat.factorial_dvd_factorial (by omega)).trans hdvd)
  have hpos : ∀ x ∈ block n, x ≠ 0 := fun x hx => by
    have := (mem_block_iff.mp hx).1
    omega
  obtain ⟨x, hx, hpx⟩ :=
    exists_mem_pow_dvd_of_pow_dvd_lcm Nat.prime_two (by omega) (block n) hpos h2m
  have hx_le : x ≤ n * (n + 1) / 2 := (mem_block_iff.mp hx).2
  have htop : n * (n + 1) / 2 ≤ (2 * m + 1) * (m + 1) := by
    apply Nat.div_le_of_le_mul
    have : n * (n + 1) ≤ (2 * m + 1) * (2 * m + 1 + 1) := Nat.mul_le_mul hn_le (by omega)
    nlinarith
  have hx_ge : 2 ^ m ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero (hpos x hx)) hpx
  have hlt := bound_lt_two_pow hm7
  omega

/-! ## The refutation and the corrected classification -/

/-- **Classification (corrected form).** For `n ≥ 1`, `L(n)/n!` is an integer
exactly when `n ∈ {1, 2, 3, 4, 6}`; the cases `n ≤ 13` are checked by kernel
`decide`, the rest by `not_factorial_dvd_L`. -/
theorem factorial_dvd_L_iff {n : ℕ} (hn : 1 ≤ n) :
    n.factorial ∣ L n ↔ n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases lt_or_ge n 14 with hlt | hge
  · interval_cases n <;> decide
  · have hnot : n ∉ ({1, 2, 3, 4, 6} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact iff_of_false (not_factorial_dvd_L hge) hnot

/-- **Refutation of the A093454 conjecture.** `L(n)/n!` is a non-integer for
every `n ≥ 14` (indeed for every `n ≥ 1` except `1, 2, 3, 4, 6`), so the set of
indices with a non-integer quotient is infinite; e.g. `n = 5` (`L(5)/5! =
60060/120 = 500.5`) and every `n ≥ 7` are counterexample indices.  The
author's computation (only `1, 2, 3, 4, 6` give integers) suggests the intended
claim was the reverse: only finitely many quotients are integers. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hfin
  refine (Set.infinite_of_forall_exists_gt fun a => ?_) hfin
  refine ⟨a + 14, ⟨by omega, ?_⟩, by omega⟩
  rw [exists_int_div_eq_iff_dvd (Nat.factorial_ne_zero _)]
  exact not_factorial_dvd_L (by omega)

/-- The corrected (reversed) statement: only finitely many indices `n ≥ 1` have
`L(n)/n!` an integer, namely `1, 2, 3, 4, 6`. -/
theorem integer_indices_eq :
    {n : ℕ | 1 ≤ n ∧ ∃ k : ℤ, (L n : ℚ) / (n.factorial : ℚ) = k} = {1, 2, 3, 4, 6} := by
  ext n
  simp only [Set.mem_ofPred_eq, exists_int_div_eq_iff_dvd (Nat.factorial_ne_zero n)]
  constructor
  · rintro ⟨hn, hdvd⟩
    simpa using (factorial_dvd_L_iff hn).mp hdvd
  · intro hn
    have hn' : n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by simpa using hn
    have h1 : 1 ≤ n := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn'
      omega
    exact ⟨h1, (factorial_dvd_L_iff h1).mpr hn'⟩

end Candidates.A093454Refutation
