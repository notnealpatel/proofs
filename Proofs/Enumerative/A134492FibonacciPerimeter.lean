/-
# A134492 — Huber: Fibonacci Pythagorean perimeters are exactly `F(6n)` (FALSE)

## OEIS source (retrieved with `oeis show A134492`, 2026-10-21)

```
NAME:     a(n) = Fibonacci(6*n).
TERMS:    0,8,144,2584,46368,832040,14930352,267914296,4807526976,...
COMMENT (the conjecture):
  Conjecture: For n >= 2, the terms of this sequence are exactly those
  Fibonacci numbers which are the sum of the three numbers of a Pythagorean
  triple (checked up to F(80)). - _Felix Huber_, Nov 03 2023
FORMULA (used here, in the form F(3m) = 5 F(m)^3 + 3 F(m) for even m):
  a(n) = Fibonacci(3*n) * Lucas(3*n). - _Amiram Eldar_, Jan 11 2022
```

## Status

Triage status: **false**.  No proof or refutation was found in the entry or
the literature; the triage found the counterexample
`F(45) = 1134903170 = 344191945 + 320443248 + 470267977` with
`344191945^2 + 320443248^2 = 470267977^2`, contradicting "checked up to
F(80)".  Re-validated here (python, 2026-10-21): among `j < 80`, `F(j)` is a
Pythagorean perimeter exactly for `j ∈ {12, 18, …, 78}` (multiples of 6) and
`j ∈ {45, 57, 63, 69, 75}` (not multiples of 6).

## Results in this file (all kernel-checked, no `sorry`)

* `not_huberConjecture` — the conjecture, as stated, is false (witness `F(45)`).
* `exists_not_dvd_isPythagoreanPerimeter_fib` — the failing direction in
  explicit form: some `F(j)` with `6 ∤ j` is a perimeter.
* `isPythagoreanPerimeter_fib_six_mul` — the true direction: `F(6n)` is a
  Pythagorean perimeter for every `n ≥ 2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A134492FibonacciPerimeter

/-- `p` is the perimeter of a Pythagorean triple: `p = a + b + c` for positive
integers `a, b, c` with `a ^ 2 + b ^ 2 = c ^ 2` (positivity of `c` follows). -/
def IsPythagoreanPerimeter (p : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a + b + c = p

/-- **Cassini's identity** over `ℤ`, indexed from `0`:
`F(n) F(n+2) - F(n+1)^2 = (-1)^(n+1)`. -/
theorem cassini_int (n : ℕ) :
    ((Nat.fib n : ℤ) * Nat.fib (n + 2) - (Nat.fib (n + 1) : ℤ) ^ 2) = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      exact_mod_cast Nat.fib_add_two
    have h2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two
    have hsign : ((-1 : ℤ)) ^ (k + 1 + 1) = -(-1) ^ (k + 1) := by ring
    rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at *
    rw [hsign, ← ih, h1]
    linear_combination -(Nat.fib (k + 2) : ℤ) * h2

/-- Cassini's identity at an even middle index `2t + 2`:
`F(2t+1) F(2t+3) = F(2t+2)^2 + 1`. -/
theorem cassini_even (t : ℕ) :
    (Nat.fib (2 * t + 1) : ℤ) * Nat.fib (2 * t + 3) = (Nat.fib (2 * t + 2) : ℤ) ^ 2 + 1 := by
  have h := cassini_int (2 * t + 1)
  have hsign : ((-1 : ℤ)) ^ (2 * t + 1 + 1) = 1 := by
    rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul]; norm_num
  rw [hsign, show 2 * t + 1 + 2 = 2 * t + 3 by ring, show 2 * t + 1 + 1 = 2 * t + 2 by ring] at h
  linear_combination h

/-- Triplication at an even index: `F(6t+6) = x (5 x^2 + 3)` with `x = F(2t+2)`
(the `m` even case of `F(3m) = 5 F(m)^3 + 3 (-1)^m F(m)`). -/
theorem fib_six_mul_add_six (t : ℕ) :
    (Nat.fib (6 * t + 6) : ℤ) =
      Nat.fib (2 * t + 2) * (5 * (Nat.fib (2 * t + 2) : ℤ) ^ 2 + 3) := by
  have e1 : Nat.fib (6 * t + 6) =
      Nat.fib (2 * t + 2) * Nat.fib (4 * t + 3) + Nat.fib (2 * t + 3) * Nat.fib (4 * t + 4) := by
    have := Nat.fib_add (2 * t + 2) (4 * t + 3)
    rw [show 2 * t + 2 + (4 * t + 3) + 1 = 6 * t + 6 by ring,
      show 4 * t + 3 + 1 = 4 * t + 4 by ring, show 2 * t + 2 + 1 = 2 * t + 3 by ring] at this
    exact this
  have e2 : Nat.fib (4 * t + 3) = Nat.fib (2 * t + 2) ^ 2 + Nat.fib (2 * t + 1) ^ 2 := by
    have := Nat.fib_two_mul_add_one (2 * t + 1)
    rw [show 2 * (2 * t + 1) + 1 = 4 * t + 3 by ring, show 2 * t + 1 + 1 = 2 * t + 2 by ring]
      at this
    exact this
  have e3 : Nat.fib (4 * t + 4) =
      Nat.fib (2 * t + 2) * Nat.fib (2 * t + 1) + Nat.fib (2 * t + 3) * Nat.fib (2 * t + 2) := by
    have := Nat.fib_add (2 * t + 2) (2 * t + 1)
    rw [show 2 * t + 2 + (2 * t + 1) + 1 = 4 * t + 4 by ring,
      show 2 * t + 2 + 1 = 2 * t + 3 by ring, show 2 * t + 1 + 1 = 2 * t + 2 by ring] at this
    exact this
  have e4 : Nat.fib (2 * t + 3) = Nat.fib (2 * t + 1) + Nat.fib (2 * t + 2) := by
    have := Nat.fib_add_two (n := 2 * t + 1)
    rw [show 2 * t + 1 + 2 = 2 * t + 3 by ring, show 2 * t + 1 + 1 = 2 * t + 2 by ring] at this
    exact this
  have hc := cassini_even t
  have e1' : (Nat.fib (6 * t + 6) : ℤ) =
      Nat.fib (2 * t + 2) * Nat.fib (4 * t + 3) + Nat.fib (2 * t + 3) * Nat.fib (4 * t + 4) := by
    exact_mod_cast e1
  have e2' : (Nat.fib (4 * t + 3) : ℤ) = Nat.fib (2 * t + 2) ^ 2 + Nat.fib (2 * t + 1) ^ 2 := by
    exact_mod_cast e2
  have e3' : (Nat.fib (4 * t + 4) : ℤ) =
      Nat.fib (2 * t + 2) * Nat.fib (2 * t + 1) + Nat.fib (2 * t + 3) * Nat.fib (2 * t + 2) := by
    exact_mod_cast e3
  have e4' : (Nat.fib (2 * t + 3) : ℤ) = Nat.fib (2 * t + 1) + Nat.fib (2 * t + 2) := by
    exact_mod_cast e4
  rw [e1', e2', e3', e4']
  rw [e4'] at hc
  linear_combination 3 * (Nat.fib (2 * t + 2) : ℤ) * hc

/-- The Lucas square identity at an even index: with `L = F(2t+1) + F(2t+3)`
(the Lucas number `L(2t+2)`), `L^2 = 5 F(2t+2)^2 + 4`. -/
theorem lucas_sq (t : ℕ) :
    (Nat.fib (2 * t + 1) + Nat.fib (2 * t + 3)) ^ 2 = 5 * Nat.fib (2 * t + 2) ^ 2 + 4 := by
  have e4 : Nat.fib (2 * t + 3) = Nat.fib (2 * t + 1) + Nat.fib (2 * t + 2) := by
    have := Nat.fib_add_two (n := 2 * t + 1)
    rw [show 2 * t + 1 + 2 = 2 * t + 3 by ring, show 2 * t + 1 + 1 = 2 * t + 2 by ring] at this
    exact this
  have hc := cassini_even t
  have e4' : (Nat.fib (2 * t + 3) : ℤ) = Nat.fib (2 * t + 1) + Nat.fib (2 * t + 2) := by
    exact_mod_cast e4
  have key : ((Nat.fib (2 * t + 1) : ℤ) + Nat.fib (2 * t + 3)) ^ 2 =
      5 * (Nat.fib (2 * t + 2) : ℤ) ^ 2 + 4 := by
    rw [e4'] at hc ⊢
    linear_combination 4 * hc
  exact_mod_cast key

/-- **Perimeter construction.** If `x ≥ 2` and `L^2 = 5 x^2 + 4`, then
`x (5 x^2 + 3) = x (L - 1)(L + 1)` is a Pythagorean perimeter.  For odd
`L = 2m + 1` use the Euclid triple with parameters `(m, 1)` scaled by `2x`;
for even `L = 2t` (forcing `x = 2u`) use parameters `(2t - 1, 2)` scaled by
`u`. -/
theorem isPythagoreanPerimeter_of_sq_eq (x L : ℕ) (hx : 2 ≤ x) (hL : L ^ 2 = 5 * x ^ 2 + 4) :
    IsPythagoreanPerimeter (x * (5 * x ^ 2 + 3)) := by
  rcases Nat.even_or_odd L with ⟨t, rfl⟩ | ⟨m, rfl⟩
  · -- `L = 2t`: then `x = 2u` and `t ^ 2 = 5 u ^ 2 + 1`.
    rcases Nat.even_or_odd x with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · have ht : t ^ 2 = 5 * u ^ 2 + 1 := by nlinarith
      have hu : 1 ≤ u := by omega
      have ht3 : 3 ≤ t := by nlinarith
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
      refine ⟨u * (2 * s + 1) * (2 * s + 5), 4 * u * (2 * s + 3), u * ((2 * s + 3) ^ 2 + 4),
        by positivity, by positivity, by ring, ?_⟩
      have hst : (2 * s + 3) * (2 * s + 5) = 20 * u ^ 2 + 3 := by nlinarith
      calc u * (2 * s + 1) * (2 * s + 5) + 4 * u * (2 * s + 3) + u * ((2 * s + 3) ^ 2 + 4)
          = 2 * u * ((2 * s + 3) * (2 * s + 5)) := by ring
        _ = (u + u) * (5 * (u + u) ^ 2 + 3) := by rw [hst]; ring
    · exfalso
      have h2 : 4 * (t ^ 2) = 20 * (u ^ 2 + u) + 9 := by nlinarith
      omega
  · -- `L = 2m + 1`: then `4 m (m + 1) = 5 x ^ 2 + 3`.
    have hm : 4 * (m * (m + 1)) = 5 * x ^ 2 + 3 := by nlinarith
    have hm2 : 2 ≤ m := by nlinarith
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
    refine ⟨2 * x * (r + 1) * (r + 3), 4 * x * (r + 2), 2 * x * ((r + 2) ^ 2 + 1),
      by positivity, by positivity, by ring, ?_⟩
    calc 2 * x * (r + 1) * (r + 3) + 4 * x * (r + 2) + 2 * x * ((r + 2) ^ 2 + 1)
        = x * (4 * ((r + 2) * (r + 2 + 1))) := by ring
      _ = x * (5 * x ^ 2 + 3) := by rw [hm]

/-- **The true half of the conjecture.** For every `n ≥ 2`, `F(6n)` is the
perimeter of a Pythagorean triple. -/
theorem isPythagoreanPerimeter_fib_six_mul (n : ℕ) (hn : 2 ≤ n) :
    IsPythagoreanPerimeter (Nat.fib (6 * n)) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have hfib : Nat.fib (6 * (t + 1)) = Nat.fib (2 * t + 2) * (5 * Nat.fib (2 * t + 2) ^ 2 + 3) := by
    have h := fib_six_mul_add_six t
    rw [show 6 * (t + 1) = 6 * t + 6 by ring]
    exact_mod_cast h
  have hx : 2 ≤ Nat.fib (2 * t + 2) := by
    have h4 : Nat.fib 4 ≤ Nat.fib (2 * t + 2) := Nat.fib_mono (by omega)
    have h4' : Nat.fib 4 = 3 := by decide
    omega
  rw [hfib]
  exact isPythagoreanPerimeter_of_sq_eq _ _ hx (lucas_sq t)

/-- `F(45) = 1134903170` is a Pythagorean perimeter, witnessed by
`(344191945, 320443248, 470267977)`.  Since `45` is not a multiple of `6`,
this is the counterexample to Huber's conjecture. -/
theorem isPythagoreanPerimeter_fib_45 : IsPythagoreanPerimeter (Nat.fib 45) := by
  refine ⟨344191945, 320443248, 470267977, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [show Nat.fib 45 = 1134903170 by decide]

/-- **Huber's conjecture (A134492, Felix Huber, Nov 03 2023)**, as a
proposition.

Verbatim: "Conjecture: For n >= 2, the terms of this sequence are exactly
those Fibonacci numbers which are the sum of the three numbers of a
Pythagorean triple (checked up to F(80))."

Formally: a natural number `x` is both a Fibonacci number and a Pythagorean
perimeter iff `x = F(6n)` for some `n ≥ 2`.  The `n ≥ 2` guard is from the
source and is needed: `F(6) = 8` is not a perimeter. -/
def HuberConjecture : Prop :=
  ∀ x : ℕ, ((∃ j, Nat.fib j = x) ∧ IsPythagoreanPerimeter x) ↔
    ∃ n, 2 ≤ n ∧ Nat.fib (6 * n) = x

/-- **Huber's conjecture is false.** `F(45)` is a Fibonacci Pythagorean
perimeter but `F(45) ≠ F(6n)` for every `n ≥ 2` (Fibonacci is injective on
indices `≥ 2`, and `6 ∤ 45`). -/
theorem not_huberConjecture : ¬ HuberConjecture := by
  intro h
  obtain ⟨n, hn, hfib⟩ := (h (Nat.fib 45)).mp ⟨⟨45, rfl⟩, isPythagoreanPerimeter_fib_45⟩
  have hidx : 6 * n - 2 = 43 := by
    apply Nat.fib_add_two_strictMono.injective
    simp only
    rw [show 6 * n - 2 + 2 = 6 * n by omega]
    exact hfib
  omega

/-- The failing direction of the conjecture in explicit form: some Fibonacci
number `F(j)` with `6 ∤ j` is a Pythagorean perimeter (namely `j = 45`). -/
theorem exists_not_dvd_isPythagoreanPerimeter_fib :
    ∃ j : ℕ, ¬ 6 ∣ j ∧ IsPythagoreanPerimeter (Nat.fib j) :=
  ⟨45, by norm_num, isPythagoreanPerimeter_fib_45⟩

/-- The direction of the conjecture that does hold: every `F(6n)` with `n ≥ 2`
is a Fibonacci Pythagorean perimeter. -/
theorem huberConjecture_mpr (x : ℕ) (h : ∃ n, 2 ≤ n ∧ Nat.fib (6 * n) = x) :
    (∃ j, Nat.fib j = x) ∧ IsPythagoreanPerimeter x := by
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨⟨6 * n, rfl⟩, isPythagoreanPerimeter_fib_six_mul n hn⟩

/-! ## Sanity layer -/

-- Ground truth: the first listed terms `0, 8, 144, 2584, 46368` of A134492.
example : Nat.fib (6 * 0) = 0 ∧ Nat.fib (6 * 1) = 8 ∧ Nat.fib (6 * 2) = 144 ∧
    Nat.fib (6 * 3) = 2584 ∧ Nat.fib (6 * 4) = 46368 := by decide

-- Ground truth for the perimeter predicate: `12 = 3 + 4 + 5` is a perimeter.
example : IsPythagoreanPerimeter 12 := ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, rfl⟩

-- Ground truth: `144 = F(12) = 36 + 48 + 60` is a perimeter, so the conjecture's
-- left-hand side is satisfiable.
example : (∃ j, Nat.fib j = 144) ∧ IsPythagoreanPerimeter 144 :=
  ⟨⟨12, by decide⟩, 36, 48, 60, by norm_num, by norm_num, by norm_num, rfl⟩

-- The `n ≥ 2` guard is load-bearing: `F(6) = 8` is not a perimeter.
example : ¬ IsPythagoreanPerimeter 8 := by
  rintro ⟨a, b, c, ha, hb, h, hs⟩
  have hc : c = 8 - a - b := by omega
  have ha8 : a ≤ 8 := by omega
  have hb8 : b ≤ 8 := by omega
  subst hc
  interval_cases a <;> interval_cases b <;> norm_num at h

end Candidates.A134492FibonacciPerimeter
