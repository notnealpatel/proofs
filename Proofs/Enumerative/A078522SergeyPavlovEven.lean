/-
# A078522 — Sergey Pavlov: scaled areas of Pythagorean triples with legs differing by an even v

## OEIS source (re-pulled with `oeis show A078522`, retrieved 2026-10-21)

```
NAME:     Numbers k such that (k+1)*(2*k+1) is a perfect square.
TERMS:    0,24,840,28560,970224,32959080,1119638520,38034750624,1292061882720,...
COMMENT (context, Sergey Pavlov, Mar 14 2017):
  The sequence of areas k(n)*q(n)/2, of the ordered Pythagorean triples
  (k(n), q(n) = k(n) + 2, c(n)) with k(1)=0, q(1)=2, c(1)=0, a(1)=0, and
  k(2)=6, q(2)=8, c(2)=10, a(2)=24 (conjectured).
COMMENT (the conjecture, Sergey Pavlov, Mar 14 2017):
  Conjecture: let f(n) be a sequence of form x(n)*y(n)/2, of the ordered
  Pythagorean triples (x(n), y(n) = x(n) + v, z(n)) with x(1)=0, y(1)=v,
  z(1)=0, f(1)=0, where v is an even number. Then there exists such subset
  p(i) that p(1) = 0, p(2) = 24*(v/2)^2, for any i > 2,
  p(i) = 34*p(i-1) - p(i-2) + 24*(v/2)^2, and any p(i) is a term of the
  above sequence f(n) (see also the first formula by _Benoit Cloitre_ in the
  Formula section).
FORMULA (Benoit Cloitre, Jan 19 2003):
  a(1) = 0, a(2) = 24; for n > 2, a(n) = 34*a(n-1) - a(n-2) + 24.
```

## Status

Triage: "open" (no proof recorded in the entry); the triage notes the claim
is the `(v/2)^2`-scaling of the `v = 2` family.  This module proves it.

## Formalization choices

* `p` is indexed from `0`: `pavlov v i` is the entry's `p(i+1)`.  It is
  `ℤ`-valued so the recurrence has no truncated subtraction.
* `v/2` is `ℕ`-division guarded by `Even v`; `0 < v` excludes the degenerate
  `v = 0` (legs equal), where `p ≡ 0` is not a subsequence.
* The terms of `f` are the areas `x(x+v)/2` of the Pythagorean triples
  `(x, x+v, z)` with `x ≥ 0` (the entry starts at `x = 0`; its `z(1) = 0` is a
  slip, since `0^2 + v^2 = v^2` forces `z = v`).  We state "`a` is a term of
  `f`" as `2 * a = x * (x + v)` for some triple, avoiding division.  The areas
  are strictly increasing in `x`, so `f` is the increasing enumeration of this
  set; "`p` is a subset (subsequence) of `f`" is rendered as `StrictMono p`
  together with membership of every `p i` in the area set.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A078522SergeyPavlovEven

/-- Pavlov's sequence for an even leg difference `v` (0-indexed):
`p 0 = 0`, `p 1 = 24 (v/2)^2`, `p (n+2) = 34 p (n+1) - p n + 24 (v/2)^2`. -/
def pavlov (v : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 24 * ((v / 2 : ℕ) : ℤ) ^ 2
  | n + 2 => 34 * pavlov v (n + 1) - pavlov v n + 24 * ((v / 2 : ℕ) : ℤ) ^ 2

/-- The set of terms of Pavlov's `f`: areas `x (x + v) / 2` of Pythagorean
triples `(x, x + v, z)` with natural legs, written without division as
`2 a = x (x + v)`. -/
def areas (v : ℕ) : Set ℤ :=
  {a | ∃ x z : ℕ, x ^ 2 + (x + v) ^ 2 = z ^ 2 ∧ 2 * a = (x : ℤ) * ((x + v : ℕ) : ℤ)}

/-! ## Ground truth -/

/-- For `v = 2`, `pavlov` reproduces the listed terms of A078522. -/
example : (List.range 6).map (pavlov 2) = [0, 24, 840, 28560, 970224, 32959080] := by
  decide

/-- For `v = 4`, `pavlov` is `4` times A078522. -/
example : (List.range 4).map (pavlov 4) = [0, 96, 3360, 114240] := by decide

/-- `24` is an area for `v = 2` (triple `(6, 8, 10)`); `96` for `v = 4`
(triple `(12, 16, 20)`). -/
example : (24 : ℤ) ∈ areas 2 ∧ (96 : ℤ) ∈ areas 4 :=
  ⟨⟨6, 10, by norm_num, by norm_num⟩, ⟨12, 20, by norm_num, by norm_num⟩⟩

/-! ## The base family `v = 2` -/

/-- Pythagorean triples `(k, k + 2, c)` generated from `(0, 2)` by the
automorphism `(k, c) ↦ (3k + 2c + 2, 4k + 3c + 4)`. -/
def triple : ℕ → ℕ × ℕ
  | 0 => (0, 2)
  | n + 1 => (3 * (triple n).1 + 2 * (triple n).2 + 2, 4 * (triple n).1 + 3 * (triple n).2 + 4)

/-- The generated triples: `(0,2)`, `(6,10)`, `(40,58)`, `(238,338)`. -/
example : (List.range 4).map triple = [(0, 2), (6, 10), (40, 58), (238, 338)] := by decide

/-- Each `triple n = (k, c)` satisfies `k^2 + (k+2)^2 = c^2`. -/
theorem triple_pyth (n : ℕ) :
    (triple n).1 ^ 2 + ((triple n).1 + 2) ^ 2 = (triple n).2 ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [triple]
    nlinarith [ih]

/-- Cloitre's base sequence `a = pavlov 2` satisfies `2 a n = k_n (k_n + 2)`. -/
theorem two_mul_pavlov_two (n : ℕ) :
    2 * pavlov 2 n = ((triple n).1 : ℤ) * ((triple n).1 + 2) ∧
    2 * pavlov 2 (n + 1) = ((triple (n + 1)).1 : ℤ) * ((triple (n + 1)).1 + 2) := by
  induction n with
  | zero => refine ⟨rfl, ?_⟩; decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hp : ((triple n).1 : ℤ) ^ 2 + ((triple n).1 + 2) ^ 2 = ((triple n).2 : ℤ) ^ 2 := by
      exact_mod_cast triple_pyth n
    have hrec : pavlov 2 (n + 2) = 34 * pavlov 2 (n + 1) - pavlov 2 n + 24 := by
      simp only [pavlov, Nat.reduceDiv, Nat.cast_one, one_pow, mul_one]
    rw [hrec]
    simp only [triple] at ih ⊢
    push_cast at ih ⊢
    linear_combination 34 * ih.2 - ih.1 + 8 * hp

/-- Scaling: `pavlov v n = (v/2)^2 * pavlov 2 n`. -/
theorem pavlov_eq_mul (v n : ℕ) :
    pavlov v n = ((v / 2 : ℕ) : ℤ) ^ 2 * pavlov 2 n ∧
    pavlov v (n + 1) = ((v / 2 : ℕ) : ℤ) ^ 2 * pavlov 2 (n + 1) := by
  induction n with
  | zero =>
    refine ⟨by simp [pavlov], ?_⟩
    simp only [pavlov, Nat.reduceDiv, Nat.cast_one, one_pow, mul_one]
    ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : pavlov v (n + 2) =
        34 * pavlov v (n + 1) - pavlov v n + 24 * ((v / 2 : ℕ) : ℤ) ^ 2 := rfl
    have hrec2 : pavlov 2 (n + 2) = 34 * pavlov 2 (n + 1) - pavlov 2 n + 24 := by
      simp only [pavlov, Nat.reduceDiv, Nat.cast_one, one_pow, mul_one]
    rw [hrec, hrec2, ih.1, ih.2]
    ring

/-- `pavlov 2` is strictly increasing (and nonnegative). -/
theorem pavlov_two_strictMono : StrictMono (pavlov 2) := by
  have key : ∀ n, 0 ≤ pavlov 2 n ∧ pavlov 2 n < pavlov 2 (n + 1) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      refine ⟨ih.1.trans ih.2.le, ?_⟩
      have hrec : pavlov 2 (n + 2) = 34 * pavlov 2 (n + 1) - pavlov 2 n + 24 := by
        simp only [pavlov, Nat.reduceDiv, Nat.cast_one, one_pow, mul_one]
      rw [hrec]
      linarith [ih.1, ih.2]
  exact strictMono_nat_of_lt_succ fun n => (key n).2

/-! ## The conjecture -/

/-- **Pavlov's conjecture (A078522, Sergey Pavlov, Mar 14 2017).**
For an even `v > 0`, the sequence `p(1) = 0`, `p(2) = 24 (v/2)^2`,
`p(i) = 34 p(i-1) - p(i-2) + 24 (v/2)^2` (here `pavlov v`, indexed from `0`)
is a strictly increasing subsequence of the areas `x (x+v)/2` of Pythagorean
triples `(x, x+v, z)`: every `p(i)` is such an area. -/
theorem pavlov_conjecture (v : ℕ) (hv : Even v) (hv0 : 0 < v) :
    StrictMono (pavlov v) ∧ ∀ i, pavlov v i ∈ areas v := by
  obtain ⟨m, rfl⟩ := hv
  have hm : (m + m) / 2 = m := by omega
  have hm0 : (0 : ℤ) < (m : ℤ) ^ 2 := by
    have : 0 < m := by omega
    positivity
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [(pavlov_eq_mul (m + m) a).1, (pavlov_eq_mul (m + m) b).1, hm]
    exact mul_lt_mul_of_pos_left (pavlov_two_strictMono hab) hm0
  · intro i
    refine ⟨m * (triple i).1, m * (triple i).2, ?_, ?_⟩
    · have h := triple_pyth i
      calc (m * (triple i).1) ^ 2 + (m * (triple i).1 + (m + m)) ^ 2
          = m ^ 2 * ((triple i).1 ^ 2 + ((triple i).1 + 2) ^ 2) := by ring
        _ = (m * (triple i).2) ^ 2 := by rw [h]; ring
    · rw [(pavlov_eq_mul (m + m) i).1, hm]
      have h2 := (two_mul_pavlov_two i).1
      push_cast
      linear_combination (m : ℤ) ^ 2 * h2

/-- Non-vacuity: the hypotheses are jointly satisfied at `v = 2`. -/
example : StrictMono (pavlov 2) ∧ ∀ i, pavlov 2 i ∈ areas 2 :=
  pavlov_conjecture 2 even_two two_pos

end Candidates.A078522SergeyPavlovEven
