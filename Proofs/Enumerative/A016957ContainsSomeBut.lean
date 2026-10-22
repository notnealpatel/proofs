/-
# A016957: Rascoe's abundance-index identity

OEIS A016957, John Tyler Rascoe (Jul 09 2022), with A088827, A186421,
A186423 and A186424; Bruno Berselli's square characterization of A186424
(Apr 29 2016).
The sequence `6n + 4` contains some but not all positive even numbers with
odd abundance. For every zero-based index `n`, membership is equivalent to
`n + 1` being an odd term of the partial sums A186423.
Abundance is taken in `ℤ`, and the index condition avoids truncated subtraction.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A016957ContainsSomeBut

open ArithmeticFunction Finset

/-! ## Definitions -/

/-- A016957: `a(n) = 6n + 4`. -/
def A016957 (n : ℕ) : ℕ := 6 * n + 4

/-- The abundance `σ(k) - 2k` of `k`, taken in `ℤ` so that deficient numbers
have negative abundance rather than a truncated value. -/
def abundance (k : ℕ) : ℤ := (sigma 1 k : ℤ) - 2 * (k : ℤ)

/-- A088827 membership: `k` is a positive even number with odd abundance. -/
def IsA088827 (k : ℕ) : Prop := 0 < k ∧ Even k ∧ Odd (abundance k)

instance (k : ℕ) : Decidable (IsA088827 k) := by
  unfold IsA088827 abundance; infer_instance

/-- A186421: even numbers interleaved with repeated odd numbers; the entry's
formula `a(n) = n` for even `n`, `a(n) = 2⌊n/4⌋ + 1` for odd `n`. -/
def A186421 (n : ℕ) : ℕ := if n % 2 = 0 then n else 2 * (n / 4) + 1

/-- A186423: partial sums `A186423(n) = ∑_{i=0}^{n} A186421(i)`. -/
def A186423 (n : ℕ) : ℕ := ∑ i ∈ range (n + 1), A186421 i

/-- A186424 membership: `m` is an odd term of A186423. -/
def IsA186424 (m : ℕ) : Prop := (∃ i, A186423 i = m) ∧ Odd m

/-! ## Examples -/

-- A016957 data line.
example : (List.range 8).map A016957 = [4, 10, 16, 22, 28, 34, 40, 46] := by decide

-- A186421 data line.
example : (List.range 16).map A186421 =
    [0, 1, 2, 1, 4, 3, 6, 3, 8, 5, 10, 5, 12, 7, 14, 7] := by decide

-- A186423 data line.
example : (List.range 12).map A186423 = [0, 1, 3, 4, 8, 11, 17, 20, 28, 33, 43, 48] := by
  decide

-- A088827 data line: its members below `40` are exactly `2, 4, 8, 16, 18, 32, 36`.
example : ∀ k < 40, IsA088827 k ↔ k ∈ ({2, 4, 8, 16, 18, 32, 36} : Finset ℕ) := by decide

-- A186424 data line: `1, 3, 11, 17` are terms, witnessed at A186423 indices `1, 2, 5, 6`.
example : IsA186424 1 ∧ IsA186424 3 ∧ IsA186424 11 ∧ IsA186424 17 :=
  ⟨⟨⟨1, by decide⟩, by decide⟩, ⟨⟨2, by decide⟩, by decide⟩,
    ⟨⟨5, by decide⟩, by decide⟩, ⟨⟨6, by decide⟩, by decide⟩⟩

/-! ## Parity of `σ` -/

/-- For even `p`, the geometric sum `∑_{i ≤ n} p^i` is odd. -/
theorem odd_geom_sum_of_even {p : ℕ} (hp : Even p) (n : ℕ) :
    Odd (∑ i ∈ range (n + 1), p ^ i) := by
  rw [sum_range_succ']
  have h : Even (∑ i ∈ range n, p ^ (i + 1)) :=
    Finset.even_sum _ (fun i _ => hp.pow_of_ne_zero (Nat.succ_ne_zero i))
  simpa using h.add_one

/-- For odd `p`, the geometric sum `∑_{i ≤ n} p^i` is odd iff `n` is even. -/
theorem odd_geom_sum_iff_of_odd {p : ℕ} (hp : Odd p) (n : ℕ) :
    Odd (∑ i ∈ range (n + 1), p ^ i) ↔ Even n := by
  rw [← ZMod.natCast_eq_one_iff_odd]
  have h1 : (p : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).mpr hp
  push_cast
  simp only [h1, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [show ((n + 1 : ℕ) : ZMod 2) = (n : ZMod 2) + 1 by push_cast; ring]
  rw [add_eq_right, ZMod.natCast_eq_zero_iff_even]

/-- Every nonzero square has odd divisor sum. -/
theorem odd_sigma_sq : ∀ t : ℕ, t ≠ 0 → Odd (sigma 1 (t ^ 2)) := by
  intro t
  induction t using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp
  | prime_pow p n hp _ =>
    intro _
    rw [← pow_mul, sigma_one_apply_prime_pow hp]
    rcases hp.eq_two_or_odd' with h2 | hodd
    · exact odd_geom_sum_of_even (h2 ▸ even_two) _
    · exact (odd_geom_sum_iff_of_odd hodd _).mpr ⟨n, by ring⟩
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [mul_pow, isMultiplicative_sigma.map_mul_of_coprime (hab.pow 2 2), Nat.odd_mul]
    exact ⟨iha (by omega), ihb (by omega)⟩

/-- A number with odd divisor sum has the form `2^e · s²`. -/
theorem exists_two_pow_mul_sq_of_odd_sigma :
    ∀ k : ℕ, Odd (sigma 1 k) → ∃ e s : ℕ, k = 2 ^ e * s ^ 2 := by
  intro k
  induction k using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; simp at h
  | one => intro _; exact ⟨0, 1, by norm_num⟩
  | prime_pow p n hp _ =>
    intro hs
    rcases hp.eq_two_or_odd' with h2 | hodd
    · exact ⟨n, 1, by rw [h2]; ring⟩
    · rw [sigma_one_apply_prime_pow hp, odd_geom_sum_iff_of_odd hodd] at hs
      obtain ⟨m, hm⟩ := hs
      exact ⟨0, p ^ m, by rw [hm]; ring⟩
  | coprime a b _ _ hab iha ihb =>
    intro hs
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, Nat.odd_mul] at hs
    obtain ⟨e, s, hes⟩ := iha hs.1
    obtain ⟨f, r, hfr⟩ := ihb hs.2
    exact ⟨e + f, s * r, by rw [hes, hfr]; ring⟩

/-- In `ZMod 3`, twice a square is never `1`. -/
theorem two_mul_sq_ne_one_zmod_three : ∀ x : ZMod 3, 2 * x ^ 2 ≠ 1 := by decide

/-- A number `≡ 1 (mod 3)` with odd divisor sum is a perfect square. -/
theorem exists_sq_of_odd_sigma_of_mod_three {k : ℕ} (hs : Odd (sigma 1 k))
    (hk : k % 3 = 1) : ∃ t : ℕ, k = t ^ 2 := by
  obtain ⟨e, s, rfl⟩ := exists_two_pow_mul_sq_of_odd_sigma k hs
  rcases Nat.even_or_odd e with ⟨f, rfl⟩ | ⟨f, rfl⟩
  · exact ⟨2 ^ f * s, by ring⟩
  · exfalso
    have h3 : ((2 ^ (2 * f + 1) * s ^ 2 : ℕ) : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, hk, Nat.cast_one]
    push_cast at h3
    rw [pow_succ, pow_mul] at h3
    have h4 : ((2 : ZMod 3) ^ 2) = 1 := by decide
    rw [h4, one_pow, one_mul] at h3
    exact two_mul_sq_ne_one_zmod_three _ h3

/-- The abundance `σ(k) - 2k` is odd iff `σ(k)` is odd. -/
theorem odd_abundance_iff (k : ℕ) : Odd (abundance k) ↔ Odd (sigma 1 k) := by
  unfold abundance
  rw [Int.odd_sub, Int.odd_coe_nat]
  have h : Even (2 * (k : ℤ)) := even_two_mul _
  simp only [h, iff_true]

/-- `6n + 4` lies in A088827 iff it is a perfect square. -/
theorem isA088827_A016957_iff (n : ℕ) :
    IsA088827 (A016957 n) ↔ ∃ t : ℕ, A016957 n = t ^ 2 := by
  unfold IsA088827 A016957
  rw [odd_abundance_iff]
  constructor
  · rintro ⟨_, _, hs⟩
    exact exists_sq_of_odd_sigma_of_mod_three hs (by omega)
  · rintro ⟨t, ht⟩
    refine ⟨by omega, ⟨3 * n + 2, by ring⟩, ?_⟩
    rw [ht]
    refine odd_sigma_sq t ?_
    rintro rfl
    simp at ht

/-! ## Closed forms of A186423 -/

/-- `A186423(4k+3) = 6k² + 10k + 4`. -/
theorem A186423_four_mul_add_three (k : ℕ) :
    A186423 (4 * k + 3) = 6 * k ^ 2 + 10 * k + 4 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : 4 * (k + 1) + 3 + 1 = 4 * k + 3 + 1 + 1 + 1 + 1 + 1 := by ring
    rw [A186423, h, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
      ← A186423, ih]
    simp only [A186421]
    have e1 : (4 * k + 3 + 1) % 2 = 0 := by omega
    have e2 : (4 * k + 3 + 1 + 1) % 2 = 1 := by omega
    have e3 : (4 * k + 3 + 1 + 1 + 1) % 2 = 0 := by omega
    have e4 : (4 * k + 3 + 1 + 1 + 1 + 1) % 2 = 1 := by omega
    have d2 : (4 * k + 3 + 1 + 1) / 4 = k + 1 := by omega
    have d4 : (4 * k + 3 + 1 + 1 + 1 + 1) / 4 = k + 1 := by omega
    simp only [e1, e2, e3, e4, d2, d4, if_true, one_ne_zero, if_false]
    ring

/-- One step of the partial sums: `A186423(n+1) = A186423(n) + A186421(n+1)`. -/
theorem A186423_succ (n : ℕ) : A186423 (n + 1) = A186423 n + A186421 (n + 1) := by
  rw [A186423, sum_range_succ, ← A186423]

/-- `A186423(4k) = 6k² + 2k`. -/
theorem A186423_four_mul (k : ℕ) : A186423 (4 * k) = 6 * k ^ 2 + 2 * k := by
  cases k with
  | zero => decide
  | succ k =>
    have h : 4 * (k + 1) = 4 * k + 3 + 1 := by ring
    have e : (4 * k + 3 + 1) % 2 = 0 := by omega
    rw [h, A186423_succ, A186423_four_mul_add_three, A186421, if_pos e]
    ring

/-- `A186423(4k+1) = 6k² + 4k + 1`. -/
theorem A186423_four_mul_add_one (k : ℕ) :
    A186423 (4 * k + 1) = 6 * k ^ 2 + 4 * k + 1 := by
  have e : ¬ (4 * k + 1) % 2 = 0 := by omega
  have d : (4 * k + 1) / 4 = k := by omega
  rw [A186423_succ, A186423_four_mul, A186421, if_neg e, d]
  ring

/-- `A186423(4k+2) = 6k² + 8k + 3`. -/
theorem A186423_four_mul_add_two (k : ℕ) :
    A186423 (4 * k + 2) = 6 * k ^ 2 + 8 * k + 3 := by
  have e : (4 * k + 2) % 2 = 0 := by omega
  rw [A186423_succ, A186423_four_mul_add_one, A186421, if_pos e]
  ring

/-- Berselli's description of A186424 at `m = n + 1`: `n + 1` is an odd term of
A186423 iff `6(n + 1) - 2 = 6n + 4` is a perfect square. -/
theorem isA186424_succ_iff (n : ℕ) :
    IsA186424 (n + 1) ↔ ∃ t : ℕ, 6 * n + 4 = t ^ 2 := by
  constructor
  · rintro ⟨⟨i, hi⟩, hodd⟩
    obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ i = 4 * k + r := ⟨i / 4, i % 4, by omega, by omega⟩
    obtain ⟨j, hj⟩ := hodd
    interval_cases r
    · rw [Nat.add_zero, A186423_four_mul] at hi
      generalize k ^ 2 = q at hi
      omega
    · rw [A186423_four_mul_add_one] at hi
      exact ⟨6 * k + 2, by nlinarith [hi]⟩
    · rw [A186423_four_mul_add_two] at hi
      exact ⟨6 * k + 4, by nlinarith [hi]⟩
    · rw [A186423_four_mul_add_three] at hi
      generalize k ^ 2 = q at hi
      omega
  · rintro ⟨t, ht⟩
    have hmod : (t % 6) ^ 2 % 6 = 4 := by
      rw [← Nat.pow_mod, ← ht]; omega
    have hr : t % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have ht' : t = 6 * (t / 6) + t % 6 := (Nat.div_add_mod t 6).symm
    generalize t / 6 = q at ht'
    generalize t % 6 = r at hmod hr ht'
    subst ht'
    interval_cases r
    · norm_num at hmod
    · norm_num at hmod
    · refine ⟨⟨4 * q + 1, ?_⟩, ⟨3 * q ^ 2 + 2 * q, ?_⟩⟩
      · rw [A186423_four_mul_add_one]; nlinarith [ht]
      · nlinarith [ht]
    · norm_num at hmod
    · refine ⟨⟨4 * q + 2, ?_⟩, ⟨3 * q ^ 2 + 4 * q + 1, ?_⟩⟩
      · rw [A186423_four_mul_add_two]; nlinarith [ht]
      · nlinarith [ht]
    · norm_num at hmod

/-! ## The conjecture -/

/-- Rascoe's A016957 conjecture: some but not all positive even numbers of
odd abundance occur as `6n+4`, and occurrence is equivalent to `n+1` being
an A186424 term. All A186424 terms are positive, so this expresses the
source index set `{A186424(k)-1}` without truncated subtraction. -/
theorem rascoe_conjecture :
    (∃ n, IsA088827 (A016957 n)) ∧
      (∃ k, IsA088827 k ∧ ∀ n, A016957 n ≠ k) ∧
      (∀ n, IsA088827 (A016957 n) ↔ IsA186424 (n + 1)) := by
  refine ⟨⟨0, by decide⟩, ⟨2, by decide, fun n => by unfold A016957; omega⟩, fun n => ?_⟩
  rw [isA088827_A016957_iff, isA186424_succ_iff]
  rfl

/-- The intersection of A016957 with A088827 is infinite: `6n + 4` lies in
A088827 for `n = 6k² + 4k` (where `6n + 4 = (6k + 2)²`) for every `k`. -/
theorem infinite_setOf_isA088827_A016957 :
    {n : ℕ | IsA088827 (A016957 n)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ⟨6 * (a + 1) ^ 2 + 4 * (a + 1), ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, isA088827_A016957_iff]
    exact ⟨6 * (a + 1) + 2, by unfold A016957; ring⟩
  · nlinarith

end Candidates.A016957ContainsSomeBut
