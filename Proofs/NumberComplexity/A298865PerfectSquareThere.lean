/-
# A298865 — Kimberling: unique difference-of-squares representations

Clark Kimberling's conjecture in OEIS A298865 characterizes positive
nonsquares with a unique representation `x²-y² = n`, `x > y ≥ 0`, as the
primes and four times primes, except for `2`. Representations correspond
to factorizations into two factors of the same parity.

## Formalization choices

* `A298865 n` mirrors the NAME: `n` is a prime or `n = 4 * p` for a prime `p`.
* `IsDiffSqPair n (x, y)` mirrors the comment: `y < x` and `x^2 - y^2 = n`,
  with the subtraction taken in `ℤ` after casting (no truncation).
* "except for the first term" removes `2`, the first term, so the conjectured
  set is `A298865 n ∧ n ≠ 2` among positive nonsquares.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A298865PerfectSquareThere

/-- Membership in A298865: `n` is a prime `p` or a product `4 * p` with `p` prime. -/
def A298865 (n : ℕ) : Prop := n.Prime ∨ ∃ p : ℕ, p.Prime ∧ n = 4 * p

/-- The pair `q = (x, y)` represents `n` as a difference of squares with
`x > y ≥ 0`: `y < x` and `x^2 - y^2 = n` (subtraction in `ℤ`). -/
def IsDiffSqPair (n : ℕ) (q : ℕ × ℕ) : Prop :=
  q.2 < q.1 ∧ (q.1 : ℤ) ^ 2 - (q.2 : ℤ) ^ 2 = n

/-- Decidable reformulation of `A298865`, used for the example. -/
theorem a298865_iff (n : ℕ) : A298865 n ↔ n.Prime ∨ (4 ∣ n ∧ (n / 4).Prime) := by
  unfold A298865
  constructor
  · rintro (hp | ⟨p, hp, rfl⟩)
    · exact Or.inl hp
    · refine Or.inr ⟨dvd_mul_right 4 p, ?_⟩
      rwa [Nat.mul_div_cancel_left p (by norm_num)]
  · rintro (hp | ⟨h4, hp⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨n / 4, hp, (Nat.mul_div_cancel' h4).symm⟩

/-! ## Examples -/

-- The definition reproduces every listed term (all terms `< 194`).
set_option maxRecDepth 20000 in
example : (Finset.range 194).filter (fun n => n.Prime ∨ (4 ∣ n ∧ (n / 4).Prime)) =
    {2, 3, 5, 7, 8, 11, 12, 13, 17, 19, 20, 23, 28, 29, 31, 37, 41, 43, 44, 47, 52, 53,
     59, 61, 67, 68, 71, 73, 76, 79, 83, 89, 92, 97, 101, 103, 107, 109, 113, 116, 124,
     127, 131, 137, 139, 148, 149, 151, 157, 163, 164, 167, 172, 173, 179, 181, 188,
     191, 193} := by
  decide

-- `8 = 3^2 - 1^2`, and `15` has the two pairs `(4, 1)` and `(8, 7)`.
example : IsDiffSqPair 8 (3, 1) := by norm_num [IsDiffSqPair]
example : IsDiffSqPair 15 (4, 1) ∧ IsDiffSqPair 15 (8, 7) := by norm_num [IsDiffSqPair]

/-! ## Helper lemmas -/

/-- The `ℤ`-subtraction form of a pair is the additive `ℕ` identity `y^2 + n = x^2`. -/
theorem isDiffSqPair_iff (n : ℕ) (q : ℕ × ℕ) :
    IsDiffSqPair n q ↔ q.2 < q.1 ∧ q.2 ^ 2 + n = q.1 ^ 2 := by
  unfold IsDiffSqPair
  constructor
  · rintro ⟨hlt, h⟩
    refine ⟨hlt, ?_⟩
    have h' : ((q.2 ^ 2 + n : ℕ) : ℤ) = ((q.1 ^ 2 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h'
  · rintro ⟨hlt, h⟩
    refine ⟨hlt, ?_⟩
    have h' : ((q.2 ^ 2 + n : ℕ) : ℤ) = ((q.1 ^ 2 : ℕ) : ℤ) := by rw [h]
    push_cast at h'
    linarith

/-- Every factorization `n = a * (a + 2k)` with `0 < a` yields the pair `(a + k, k)`. -/
theorem isDiffSqPair_mk (a k : ℕ) (ha : 0 < a) :
    IsDiffSqPair (a * (a + 2 * k)) (a + k, k) := by
  rw [isDiffSqPair_iff]
  exact ⟨by simp only; omega, by simp only; ring⟩

/-- Every pair `(x, y)` comes from a factorization `n = d * (d + 2y)` with
`d = x - y > 0`. -/
theorem exists_factor_of_isDiffSqPair {n x y : ℕ} (h : IsDiffSqPair n (x, y)) :
    ∃ d : ℕ, 0 < d ∧ x = y + d ∧ n = d * (d + 2 * y) := by
  rw [isDiffSqPair_iff] at h
  obtain ⟨hlt, heq⟩ := h
  simp only at hlt heq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  refine ⟨d + 1, by omega, by omega, ?_⟩
  have hsum : y ^ 2 + n = y ^ 2 + (d + 1) * (d + 1 + 2 * y) := by
    rw [heq]; ring
  omega

/-- If `n` is even and has a pair, then `4 ∣ n` (both factors must be even). -/
theorem four_dvd_of_even_of_isDiffSqPair {n x y : ℕ} (hn : Even n)
    (h : IsDiffSqPair n (x, y)) : 4 ∣ n := by
  obtain ⟨d, -, -, hnd⟩ := exists_factor_of_isDiffSqPair h
  rcases Nat.even_or_odd d with ⟨a, rfl⟩ | hd
  · exact ⟨a * (a + y), by rw [hnd]; ring⟩
  · exfalso
    have hodd : Odd (d * (d + 2 * y)) :=
      hd.mul (hd.add_even ⟨y, by ring⟩)
    rw [← hnd] at hodd
    exact Nat.not_even_iff_odd.mpr hodd hn

/-- Two different factorizations `n = a * (a + 2k) = c * (c + 2j)` with `a ≠ c`
give two different pairs, so the pair is not unique. -/
theorem not_existsUnique_of_two_factorizations {n a k c j : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hac : a ≠ c) (hn₁ : n = a * (a + 2 * k)) (hn₂ : n = c * (c + 2 * j)) :
    ¬ ∃! q : ℕ × ℕ, IsDiffSqPair n q := by
  rintro ⟨q, -, huniq⟩
  have h₁ := huniq (a + k, k) (hn₁ ▸ isDiffSqPair_mk a k ha)
  have h₂ := huniq (c + j, j) (hn₂ ▸ isDiffSqPair_mk c j hc)
  rw [← h₂, Prod.mk.injEq] at h₁
  omega

/-- A composite nonsquare `m > 1` factors as `m = a * (a + k)` with `1 < a` and `0 < k`. -/
theorem exists_proper_factorization {m : ℕ} (hm : 1 < m) (hnp : ¬ m.Prime)
    (hsq : ¬ IsSquare m) : ∃ a k : ℕ, 1 < a ∧ 0 < k ∧ m = a * (a + k) := by
  set a := m.minFac with ha_def
  have hap : a.Prime := Nat.minFac_prime (by omega)
  have ha1 : 1 < a := hap.one_lt
  obtain ⟨c, hc⟩ : a ∣ m := Nat.minFac_dvd m
  have hsq_le : a ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
  have hac : a ≤ c := by
    rw [hc, pow_two] at hsq_le
    exact Nat.le_of_mul_le_mul_left hsq_le (by omega)
  have hne : a ≠ c := by
    rintro rfl
    exact hsq ⟨a, hc⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hac
  exact ⟨a, k, ha1, by omega, by rw [hc, hk]⟩

/-- Odd primes have exactly one pair, namely `((p + 1) / 2, (p - 1) / 2)`. -/
theorem existsUnique_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃! q : ℕ × ℕ, IsDiffSqPair p q := by
  obtain ⟨j, hj⟩ : Odd p := hp.odd_of_ne_two hp2
  refine ⟨(1 + j, j), ?_, ?_⟩
  · have hpj : p = 1 * (1 + 2 * j) := by omega
    rw [hpj]
    exact isDiffSqPair_mk 1 j one_pos
  · rintro ⟨x, y⟩ h
    obtain ⟨d, hd0, hx, hpd⟩ := exists_factor_of_isDiffSqPair h
    rcases hp.eq_one_or_self_of_dvd d ⟨d + 2 * y, hpd⟩ with rfl | rfl
    · simp only [Prod.mk.injEq]
      omega
    · exfalso
      have h1 : d + 2 * y = 1 := by
        have : d * (d + 2 * y) = d * 1 := by rw [← hpd, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hd0 this
      have := hp.two_le
      omega

/-- `4 * p` with `p` prime has exactly one pair, namely `(p + 1, p - 1)`. -/
theorem existsUnique_of_four_mul_prime {p : ℕ} (hp : p.Prime) :
    ∃! q : ℕ × ℕ, IsDiffSqPair (4 * p) q := by
  have hp2 := hp.two_le
  refine ⟨(2 + (p - 1), p - 1), ?_, ?_⟩
  · have hpj : 4 * p = 2 * (2 + 2 * (p - 1)) := by omega
    rw [hpj]
    exact isDiffSqPair_mk 2 (p - 1) two_pos
  · rintro ⟨x, y⟩ h
    obtain ⟨d, hd0, hx, hpd⟩ := exists_factor_of_isDiffSqPair h
    rcases Nat.even_or_odd d with ⟨a, rfl⟩ | hd
    · have hap : p = a * (a + y) := by
        have : 4 * p = 4 * (a * (a + y)) := by rw [hpd]; ring
        omega
      have ha0 : 0 < a := by omega
      rcases hp.eq_one_or_self_of_dvd a ⟨a + y, hap⟩ with rfl | rfl
      · simp only [Prod.mk.injEq]
        omega
      · exfalso
        have h1 : a + y = 1 := by
          have : a * (a + y) = a * 1 := by rw [← hap, mul_one]
          exact Nat.eq_of_mul_eq_mul_left ha0 this
        omega
    · exfalso
      have hodd : Odd (d * (d + 2 * y)) := hd.mul (hd.add_even ⟨y, by ring⟩)
      rw [← hpd] at hodd
      exact Nat.not_even_iff_odd.mpr hodd ⟨2 * p, by ring⟩

/-- Forward direction: a unique pair forces `n` to be an odd prime or `4 * p`. -/
theorem a298865_of_existsUnique {n : ℕ} (hpos : 0 < n) (hsq : ¬ IsSquare n)
    (hu : ∃! q : ℕ × ℕ, IsDiffSqPair n q) : A298865 n ∧ n ≠ 2 := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hsq ⟨1, rfl⟩
  rcases Nat.even_or_odd n with hev | hodd
  · -- even case: `n = 4 * m` and `m` must be prime
    obtain ⟨⟨x, y⟩, hxy⟩ := hu.exists
    obtain ⟨m, rfl⟩ := four_dvd_of_even_of_isDiffSqPair hev hxy
    refine ⟨Or.inr ⟨m, ?_, rfl⟩, by omega⟩
    by_contra hnp
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hsq ⟨2, rfl⟩
    have hmsq : ¬ IsSquare m := by
      rintro ⟨r, rfl⟩
      exact hsq ⟨2 * r, by ring⟩
    obtain ⟨a, k, ha1, -, hm⟩ := exists_proper_factorization (by omega) hnp hmsq
    refine not_existsUnique_of_two_factorizations (a := 2 * a) (k := k) (c := 2)
      (j := m - 1) (by omega) two_pos (by omega) ?_ ?_ hu
    · rw [hm]; ring
    · omega
  · -- odd case: `n` must be prime
    have hn2 : n ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    refine ⟨Or.inl ?_, hn2⟩
    by_contra hnp
    obtain ⟨a, k, ha1, -, hn⟩ := exists_proper_factorization (by omega) hnp hsq
    have hao : Odd a := Odd.of_dvd_nat hodd ⟨a + k, hn⟩
    have hako : Odd (a + k) := Odd.of_dvd_nat hodd ⟨a, by rw [hn, mul_comm]⟩
    obtain ⟨k', hk'⟩ : Even k := (Nat.odd_add.mp hako).mp hao
    obtain ⟨j, hj⟩ := hodd
    refine not_existsUnique_of_two_factorizations (a := a) (k := k') (c := 1) (j := j)
      (by omega) one_pos (by omega) ?_ ?_ hu
    · rw [hn, hk']; ring
    · omega

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A298865, Clark Kimberling).**

For every positive nonsquare `n`, there is exactly one pair `(x, y)` of naturals
with `y < x` and `x^2 - y^2 = n` if and only if `n` is a term of A298865 other
than the first term `2`, i.e. `n` is an odd prime or `n = 4 * p` with `p` prime. -/
theorem a298865_conjecture (n : ℕ) (hpos : 0 < n) (hsq : ¬ IsSquare n) :
    (∃! q : ℕ × ℕ, IsDiffSqPair n q) ↔ A298865 n ∧ n ≠ 2 := by
  refine ⟨a298865_of_existsUnique hpos hsq, ?_⟩
  rintro ⟨hp | ⟨p, hp, rfl⟩, hn2⟩
  · exact existsUnique_of_prime hp hn2
  · exact existsUnique_of_four_mul_prime hp

/-! ## Non-vacuity and boundary checks -/

-- The hypotheses are jointly satisfiable (`n = 3`), and both sides hold there.
example : 0 < 3 ∧ ¬ IsSquare (3 : ℕ) ∧ A298865 3 ∧ (3 : ℕ) ≠ 2 := by
  refine ⟨by norm_num, ?_, Or.inl Nat.prime_three, by norm_num⟩
  rintro ⟨r, hr⟩
  have hr2 : r < 2 := by nlinarith
  interval_cases r <;> omega

-- The exclusion of the first term is load-bearing: `2` is a term but has no pair.
example : A298865 2 ∧ ¬ ∃ q : ℕ × ℕ, IsDiffSqPair 2 q := by
  refine ⟨Or.inl Nat.prime_two, ?_⟩
  rintro ⟨⟨x, y⟩, h⟩
  have h4 := four_dvd_of_even_of_isDiffSqPair even_two h
  omega

-- The nonsquare hypothesis is load-bearing: `4` has the unique pair `(2, 0)`
-- but is not a term.
example : (∃! q : ℕ × ℕ, IsDiffSqPair 4 q) ∧ ¬ A298865 4 := by
  refine ⟨⟨(2, 0), by norm_num [IsDiffSqPair], ?_⟩, ?_⟩
  · rintro ⟨x, y⟩ h
    obtain ⟨d, hd0, hx, hpd⟩ := exists_factor_of_isDiffSqPair h
    have hd : d ∣ 4 := ⟨d + 2 * y, hpd⟩
    have hd4 : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> simp only [Prod.mk.injEq] <;> omega
  · rw [a298865_iff]
    decide

end Candidates.A298865PerfectSquareThere
