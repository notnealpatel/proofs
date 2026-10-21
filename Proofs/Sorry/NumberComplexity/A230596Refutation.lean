/-
# A230596 — refutation of Sun's conjecture (ii)

## OEIS source (retrieved with `oeis show A230596` and the live entry, 2026-10-21)

```
NAME:     Number of ways to write n = x + y + z with 0 < x <= y <= z such that
          x*y*z is a triangular number, and that x is a triangular number of
          the form (p^2 - 1)/8 with p an odd prime.
TERMS:    0,0,1,0,1,1,0,2,1,1,2,2,1,1,2,2,4,1,1,2,3,2,5,1,3,3,3,3,2,8,1,4,...
COMMENT:  Conjecture: (i) a(n) > 0 except for n = 1, 2, 4, 7.
COMMENT:  (ii) For any integer n > 7, there are positive integers x, y, z with
          x + y + z = n such that x*y*z is a triangular number and x is among
          1, 2, 3, 4, 5, 6.
AUTHOR:   _Zhi-Wei Sun_, Oct 24 2013
```

No later comment or edit in the entry retracts the conjecture.

## Status

This module **refutes** part (ii).  Part (i) is a separate claim and is not
touched here (it still holds at the counterexample below:
`1366924 = 15 + 246694 + 1120215` with `15 = (11^2 - 1)/8` and
`15 * 246694 * 1120215 = T(2879324)`).

The counterexample is `n = 1366924`.  For `1 ≤ x ≤ 6` put `N = n - x` and
`D_x = 2 x N^2 + 1`.  A solution `x * y * z = m (m + 1) / 2` with `y + z = N`
gives, with `s = 2 m + 1`,
`s^2 + 2 x (y - z)^2 = 2 x N^2 + 1 = 1^2 + 2 x N^2`.
All six `D_x` are prime (Lucas certificates below), and a prime has at most one
representation `a^2 + k b^2` with `k ≥ 2` (up to signs); the second
representation `1^2 + 2 x N^2` then forces `s N = ± (y - z)`, impossible since
`|y - z| < N ≤ s N`.

Computational evidence (Python brute force over all `x ≤ 6`, `y`; not
formalized): part (ii) also fails at `n = 611992`, which the triage reports as
the least failure (minimality rests on a class-group reduction and was not
independently re-checked).  `n = 1366924` is used because every `D_x` is prime
there, so no separate argument is needed.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A230596Refutation

/-! ## Definition layer -/

/-- `t` is a triangular number `m (m + 1) / 2` (OEIS A000217, `m ≥ 0`), stated
without division as `2 t = m (m + 1)` (`m (m + 1)` is always even). -/
def IsTriangular (t : ℕ) : Prop := ∃ m : ℕ, 2 * t = m * (m + 1)

/-- A witness `m` of a triangular number satisfies `m ≤ t`. -/
theorem le_of_two_mul_eq {t m : ℕ} (h : 2 * t = m * (m + 1)) : m ≤ t := by
  nlinarith

/-- `IsTriangular t` is decided by a bounded search `m < t + 1`. -/
theorem isTriangular_iff_bounded (t : ℕ) :
    IsTriangular t ↔ ∃ m, m < t + 1 ∧ 2 * t = m * (m + 1) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, Nat.lt_succ_of_le (le_of_two_mul_eq hm), hm⟩
  · rintro ⟨m, -, hm⟩
    exact ⟨m, hm⟩

instance (t : ℕ) : Decidable (IsTriangular t) :=
  decidable_of_iff _ (isTriangular_iff_bounded t).symm

/-- Ground truth: the triangular numbers below `30` are `0, 1, 3, 6, 10, 15, 21, 28`
(OEIS A000217). -/
example : (List.range 30).filter (fun t => decide (IsTriangular t)) =
    [0, 1, 3, 6, 10, 15, 21, 28] := by
  decide

/-- `x` has the form `(p^2 - 1)/8` for an odd prime `p`, stated without
division as `8 x + 1 = p^2` (for odd `p`, `8 ∣ p^2 - 1`). -/
def IsOddPrimeForm (x : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 * x + 1 = p ^ 2

/-- `IsOddPrimeForm x` is decided by a bounded search `p < 8 x + 2`; the cheap
equation is tested before primality. -/
theorem isOddPrimeForm_iff_bounded (x : ℕ) :
    IsOddPrimeForm x ↔ ∃ p, p < 8 * x + 2 ∧ 8 * x + 1 = p ^ 2 ∧ Odd p ∧ p.Prime := by
  constructor
  · rintro ⟨p, hp, hodd, hx⟩
    refine ⟨p, ?_, hx, hodd, hp⟩
    nlinarith [hp.two_le]
  · rintro ⟨p, -, hx, hodd, hp⟩
    exact ⟨p, hp, hodd, hx⟩

instance (x : ℕ) : Decidable (IsOddPrimeForm x) :=
  decidable_of_iff _ (isOddPrimeForm_iff_bounded x).symm

/-- Ground truth: the values `(p^2 - 1)/8` (`p` an odd prime) below `50` are
`1, 3, 6, 15, 21, 36, 45` (`p = 3, 5, 7, 11, 13, 17, 19`). -/
example : (List.range 50).filter (fun x => decide (IsOddPrimeForm x)) =
    [1, 3, 6, 15, 21, 36, 45] := by
  decide +kernel

/-- OEIS A230596: the number of `(x, y)` with `0 < x ≤ y ≤ z`, `x + y + z = n`,
`x * y * z` triangular and `x = (p^2 - 1)/8` for an odd prime `p`, where
`z = n - x - y` (the guard `x + 2 y ≤ n` makes the subtraction exact and
gives `y ≤ z`). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun q : ℕ × ℕ =>
    q.1 ≤ q.2 ∧ q.1 + 2 * q.2 ≤ n ∧ IsOddPrimeForm q.1 ∧
      IsTriangular (q.1 * q.2 * (n - q.1 - q.2))).card

/-- Ground truth: the first twenty-four terms of A230596 (offset 1). -/
example : (List.range 24).map (fun n => a (n + 1)) =
    [0, 0, 1, 0, 1, 1, 0, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 5, 1] := by
  decide +kernel

/-! ## The conjecture -/

/-- **Sun's conjecture (ii) (A230596, Zhi-Wei Sun, Oct 24 2013).**

Verbatim: "(ii) For any integer n > 7, there are positive integers x, y, z
with x + y + z = n such that x*y*z is a triangular number and x is among 1, 2,
3, 4, 5, 6." -/
def Conjecture : Prop :=
  ∀ n : ℕ, 7 < n → ∃ x y z : ℕ, 0 < x ∧ x ≤ 6 ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
    IsTriangular (x * y * z)

/-- Non-vacuity of the conjecture's shape: it holds at `n = 8`
(`8 = 1 + 2 + 5`, `1 * 2 * 5 = 10 = T(4)`). -/
example : ∃ x y z : ℕ, 0 < x ∧ x ≤ 6 ∧ 0 < y ∧ 0 < z ∧ x + y + z = 8 ∧
    IsTriangular (x * y * z) :=
  ⟨1, 2, 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ⟨4, by norm_num⟩⟩

/-- Part (i) is not refuted here: at `n = 1366924` it is witnessed by
`x = 15 = (11^2 - 1)/8`, `y = 246694`, `z = 1120215`, `x y z = T(2879324)`. -/
example : IsOddPrimeForm 15 ∧ 15 + 246694 + 1120215 = 1366924 ∧
    IsTriangular (15 * 246694 * 1120215) :=
  ⟨⟨11, by norm_num, by decide, by norm_num⟩, by norm_num, ⟨2879324, by norm_num⟩⟩

/-! ## Uniqueness of the representation `1 + k N^2` of a prime -/

/-- If a prime `D` equals both `s^2 + k b^2` and `1 + k N^2` with `k ≥ 2`, then
`s N ≠ ± b` forces a contradiction once `1 ≤ s` and `|b| < N`: the two
representations would have to coincide up to sign. -/
theorem false_of_two_reps {k s b N D : ℤ} (hk : 2 ≤ k) (hD : Prime D)
    (h1 : s ^ 2 + k * b ^ 2 = D) (h2 : 1 + k * N ^ 2 = D) (hs : 1 ≤ s) (hb : |b| < N) :
    False := by
  have hDpos : 0 < D := by nlinarith
  have hfac : (s * N - b) * (s * N + b) = D * (N ^ 2 - b ^ 2) := by
    linear_combination N ^ 2 * h1 - b ^ 2 * h2
  have hid1 : D ^ 2 = (s + k * b * N) ^ 2 + k * (s * N - b) ^ 2 := by
    linear_combination (-(1 + k * N ^ 2)) * h1 - D * h2
  have hid2 : D ^ 2 = (s - k * b * N) ^ 2 + k * (s * N + b) ^ 2 := by
    linear_combination (-(1 + k * N ^ 2)) * h1 - D * h2
  -- A multiple `t` of `D` with `k t^2 ≤ D^2` and `k ≥ 2` vanishes.
  have hzero : ∀ t c : ℤ, D ^ 2 = c ^ 2 + k * t ^ 2 → D ∣ t → t = 0 := by
    intro t c hsum hdvd
    obtain ⟨q, rfl⟩ := hdvd
    by_contra hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hq (mul_zero D)
    have hq1 : 1 ≤ q ^ 2 := by
      have hpos := pow_pos (abs_pos.mpr hq0) 2
      rw [sq_abs] at hpos
      omega
    nlinarith [sq_nonneg c, sq_nonneg D]
  have hbN := abs_lt.mp hb
  rcases hD.dvd_or_dvd (hfac ▸ dvd_mul_right D _) with hminus | hplus
  · have ht := hzero _ _ hid1 hminus
    nlinarith
  · have ht := hzero _ _ hid2 hplus
    nlinarith

/-- If `2 x (y + z)^2 + 1` is prime (`x, y, z > 0`), then `x y z` is not
triangular. -/
theorem not_isTriangular_of_prime {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hprime : (2 * x * (y + z) ^ 2 + 1).Prime) : ¬ IsTriangular (x * y * z) := by
  rintro ⟨m, hm⟩
  have hmZ : (2 : ℤ) * (x * y * z) = m * (m + 1) := by exact_mod_cast hm
  have hDZ : Prime ((2 * x * (y + z) ^ 2 + 1 : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hprime
  push_cast at hDZ
  refine false_of_two_reps (k := 2 * x) (s := 2 * m + 1) (b := (y : ℤ) - z)
    (N := (y : ℤ) + z) ?_ hDZ ?_ ?_ ?_ ?_
  · have hx1 : (1 : ℤ) ≤ x := by exact_mod_cast hx
    linarith
  · linear_combination (-4) * hmZ
  · ring
  · have hm0 : (0 : ℤ) ≤ m := Int.natCast_nonneg m
    linarith
  · have hy1 : (0 : ℤ) < y := by exact_mod_cast hy
    have hz1 : (0 : ℤ) < z := by exact_mod_cast hz
    rw [abs_lt]
    constructor <;> linarith

/-! ## Primality certificates -/

/-- A prime dividing `∏ pᵢ ^ eᵢ` (all `pᵢ` prime) is one of the `pᵢ`. -/
theorem prime_dvd_prod_pow {q : ℕ} (hq : q.Prime) : ∀ (l : List (ℕ × ℕ)),
    (∀ e ∈ l, e.1.Prime) → q ∣ (l.map fun e => e.1 ^ e.2).prod → ∃ e ∈ l, q = e.1 := by
  intro l
  induction l with
  | nil =>
    intro _ hdvd
    simp only [List.map_nil, List.prod_nil] at hdvd
    exact absurd hdvd hq.not_dvd_one
  | cons e l ih =>
    intro hl hdvd
    simp only [List.map_cons, List.prod_cons] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with he | hrest
    · refine ⟨e, List.mem_cons_self, ?_⟩
      exact (Nat.prime_dvd_prime_iff_eq hq (hl e List.mem_cons_self)).mp
        (hq.dvd_of_dvd_pow he)
    · obtain ⟨e', he', hqe'⟩ := ih (fun e' he' => hl e' (List.mem_cons_of_mem e he')) hrest
      exact ⟨e', List.mem_cons_of_mem e he', hqe'⟩

/-- Lucas's test with `p - 1` given by an explicit prime factorization `l`. -/
theorem prime_of_lucas_list (p : ℕ) (a : ZMod p) (l : List (ℕ × ℕ))
    (hl : (l.map fun e => e.1 ^ e.2).prod = p - 1) (hprime : ∀ e ∈ l, e.1.Prime)
    (ha : a ^ (p - 1) = 1) (hd : ∀ e ∈ l, a ^ ((p - 1) / e.1) ≠ 1) : p.Prime := by
  refine lucas_primality p a ha ?_
  intro q hq hdvd
  rw [← hl] at hdvd
  obtain ⟨e, he, rfl⟩ := prime_dvd_prod_pow hq l hprime hdvd
  exact hd e he

/-- `D_1 = 2 * 1366923^2 + 1` is prime; `D_1 - 1 = 2 * 3^2 * 53^2 * 8597^2`,
witness `2`. -/
theorem prime_D1 : Nat.Prime 3736956975859 := by
  refine prime_of_lucas_list 3736956975859 2 [(2, 1), (3, 2), (53, 2), (8597, 2)]
    (by norm_num) (by simp only [List.mem_cons, List.not_mem_nil]; norm_num)
    (by reduce_mod_char) ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

/-- `D_2 = 4 * 1366922^2 + 1` is prime; `D_2 - 1 = 2^4 * 683461^2`, witness `3`. -/
theorem prime_D2 : Nat.Prime 7473903016337 := by
  refine prime_of_lucas_list 7473903016337 3 [(2, 4), (683461, 2)]
    (by norm_num) (by simp only [List.mem_cons, List.not_mem_nil]; norm_num)
    (by reduce_mod_char) ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> (reduce_mod_char; decide)

/-- `D_3 = 6 * 1366921^2 + 1` is prime; `D_3 - 1 = 2 * 3 * 1366921^2`,
witness `3`. -/
theorem prime_D3 : Nat.Prime 11210838121447 := by
  refine prime_of_lucas_list 11210838121447 3 [(2, 1), (3, 1), (1366921, 2)]
    (by norm_num) (by simp only [List.mem_cons, List.not_mem_nil]; norm_num)
    (by reduce_mod_char) ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> (reduce_mod_char; decide)

/-- `D_4 = 8 * 1366920^2 + 1` is prime; `D_4 - 1 = 2^9 * 3^4 * 5^2 * 3797^2`,
witness `7`. -/
theorem prime_D4 : Nat.Prime 14947762291201 := by
  refine prime_of_lucas_list 14947762291201 7 [(2, 9), (3, 4), (5, 2), (3797, 2)]
    (by norm_num) (by simp only [List.mem_cons, List.not_mem_nil]; norm_num)
    (by reduce_mod_char) ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

/-- `D_5 = 10 * 1366919^2 + 1` is prime; `D_5 - 1 = 2 * 5 * 17^2 * 80407^2`,
witness `2`. -/
theorem prime_D5 : Nat.Prime 18684675525611 := by
  refine prime_of_lucas_list 18684675525611 2 [(2, 1), (5, 1), (17, 2), (80407, 2)]
    (by norm_num) (by simp only [List.mem_cons, List.not_mem_nil]; norm_num)
    (by reduce_mod_char) ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

/-- `D_6 = 12 * 1366918^2 + 1` is prime;
`D_6 - 1 = 2^4 * 3 * 7^2 * 163^2 * 599^2`, witness `11`. -/
theorem prime_D6 : Nat.Prime 22421577824689 := by
  refine prime_of_lucas_list 22421577824689 11
    [(2, 4), (3, 1), (7, 2), (163, 2), (599, 2)]
    (by norm_num) (by simp only [List.mem_cons, List.not_mem_nil]; norm_num)
    (by reduce_mod_char) ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

/-- For every `1 ≤ x ≤ 6`, `D_x = 2 x (1366924 - x)^2 + 1` is prime. -/
theorem prime_D {x : ℕ} (hx : 0 < x) (hx6 : x ≤ 6) :
    (2 * x * (1366924 - x) ^ 2 + 1).Prime := by
  interval_cases x
  · exact prime_D1
  · exact prime_D2
  · exact prime_D3
  · exact prime_D4
  · exact prime_D5
  · exact prime_D6

/-! ## The refutation -/

/-- `n = 1366924` admits no decomposition `x + y + z` with `x ∈ {1, …, 6}`,
`y, z > 0` and `x y z` triangular. -/
theorem no_decomposition_1366924 (x y z : ℕ) (hx : 0 < x) (hx6 : x ≤ 6) (hy : 0 < y)
    (hz : 0 < z) (hsum : x + y + z = 1366924) : ¬ IsTriangular (x * y * z) := by
  have hN : y + z = 1366924 - x := by omega
  apply not_isTriangular_of_prime hx hy hz
  rw [hN]
  exact prime_D hx hx6

/-- **Sun's A230596 conjecture (ii) is false.**  The witness is
`n = 1366924`: for each `x ∈ {1, …, 6}` the number `2 x (n - x)^2 + 1` is
prime, and `x y z = T(m)` with `y + z = n - x` would give a second
representation `(2m+1)^2 + 2x(y-z)^2` of that prime besides
`1 + 2x(n-x)^2`.  (A brute-force search also finds the smaller failure
`n = 611992`.)  The author presumably extrapolated from a search far below
these values; heuristically (Schinzel's Hypothesis H) failures recur
infinitely often. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨x, y, z, hx, hx6, hy, hz, hsum, htri⟩ := hconj 1366924 (by norm_num)
  exact no_decomposition_1366924 x y z hx hx6 hy hz hsum htri

end Candidates.A230596Refutation
