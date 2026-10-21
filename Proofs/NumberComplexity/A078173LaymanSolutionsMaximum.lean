/-
# A078173 — Layman: maxima of `t` and `s` over solutions of `r*s*t = n*(r+s+t)`

## OEIS source (retrieved 2026-10-21 with `oeis show A078173`, cross-checked
against https://oeis.org/A078173)

```
NAME:     a(n) = max(min(r,s,t)), where the maximum is taken over all positive
          integer solutions of the Diophantine equation r*s*t = n * (r+s+t).
TERMS:    1,2,3,2,3,3,3,4,4,4,4,6,3,5,5,6,4,6,5,6,7,4,5,6,5,7,9,7,6,6,...
KEYWORDS: nonn
AUTHOR:   John W. Layman, Nov 20 2002
COMMENT (the conjecture, the entry's only comment):
  Conjecture: max(t) = n*(n+2) and max(s) = 2*n, where the maxima are taken
  over all positive integer solutions r<=s<=t of the above Diophantine
  equation.
```

The comment carries no separate signature; it is part of the original
submission by John W. Layman, Nov 20 2002.

## Status

Triage: open (stated only as a conjecture in the entry; no proof found in the
entry or the literature).  Brute force confirms both maxima for `1 ≤ n ≤ 120`.
This file proves both claims for every `n ≥ 1`.

## Argument

Write `d = r*s - n`.  The equation forces `n < r*s`, and then
`t * d = n * (r + s) ≤ n * (r*s + 1) = n * (n + d + 1)`, whence
`t ≤ n * (n + 2)`; equality at `(1, n+1, n*(n+2))`.  From `s ≤ t` one gets
`r*s^2 ≤ n*r + 2*n*s`, and `s ≥ 2*n+1` would give
`r*s^2 ≥ 2*n*r*s + r*s > 2*n*s + n*r`; equality at `(1, 2*n, 2*n+1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A078173LaymanSolutionsMaximum

/-! ## Definition layer -/

/-- The ordered positive solutions of Layman's equation: triples `(r, s, t)` of
positive integers with `r ≤ s ≤ t` and `r*s*t = n*(r+s+t)`.  Positivity of `s`
and `t` follows from `0 < r ≤ s ≤ t`. -/
def solutions (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {p | 0 < p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.1 * p.2.1 * p.2.2 = n * (p.1 + p.2.1 + p.2.2)}

/-! ## Ground truth: membership witnesses realising `a(1), a(2), a(3) = 1, 2, 3`

Each listed triple has `min = r` equal to the corresponding first term. -/

example : ((1, 2, 3) : ℕ × ℕ × ℕ) ∈ solutions 1 := by
  simp only [solutions, Set.mem_ofPred_eq]; decide
example : ((2, 2, 4) : ℕ × ℕ × ℕ) ∈ solutions 2 := by
  simp only [solutions, Set.mem_ofPred_eq]; decide
example : ((3, 3, 3) : ℕ × ℕ × ℕ) ∈ solutions 3 := by
  simp only [solutions, Set.mem_ofPred_eq]; decide
example : ((1, 1, 1) : ℕ × ℕ × ℕ) ∉ solutions 1 := by
  simp only [solutions, Set.mem_ofPred_eq]; decide

/-! ## Helper lemmas -/

/-- On a solution with `0 < n`, the product `r*s` strictly exceeds `n`. -/
theorem lt_mul_of_mem {n r s t : ℕ} (hn : 0 < n) (h : (r, s, t) ∈ solutions n) :
    n < r * s := by
  simp only [solutions, Set.mem_ofPred_eq] at h
  obtain ⟨hr, hrs, hst, heq⟩ := h
  by_contra hle
  push Not at hle
  have ht : 0 < t := by omega
  have h1 : r * s * t ≤ n * t := Nat.mul_le_mul_right t hle
  have h2 : n * t < n * (r + s + t) := by
    apply Nat.mul_lt_mul_of_pos_left _ hn
    omega
  omega

/-- **Bound on `t`.** Every solution has `t ≤ n*(n+2)`. -/
theorem le_of_mem_t {n r s t : ℕ} (hn : 0 < n) (h : (r, s, t) ∈ solutions n) :
    t ≤ n * (n + 2) := by
  have hlt := lt_mul_of_mem hn h
  simp only [solutions, Set.mem_ofPred_eq] at h
  obtain ⟨hr, hrs, hst, heq⟩ := h
  obtain ⟨d, hd⟩ : ∃ d, r * s = n + d + 1 := ⟨r * s - n - 1, by omega⟩
  -- `r + s ≤ r*s + 1` since `(r-1)*(s-1) ≥ 0`.
  have hsum : r + s ≤ r * s + 1 := by nlinarith
  -- `t * (d+1) = n * (r + s)`.
  have htd : t * (d + 1) = n * (r + s) := by
    have : r * s * t = (n + d + 1) * t := by rw [hd]
    nlinarith
  by_contra hcon
  push Not at hcon
  have h3 : (n * (n + 2) + 1) * (d + 1) ≤ t * (d + 1) := Nat.mul_le_mul_right _ hcon
  have h4 : n * (r + s) ≤ n * (n + d + 2) := Nat.mul_le_mul_left n (by omega)
  nlinarith [Nat.zero_le (n * n * d), Nat.zero_le (n * d)]

/-- **Bound on `s`.** Every solution has `s ≤ 2*n`. -/
theorem le_of_mem_s {n r s t : ℕ} (hn : 0 < n) (h : (r, s, t) ∈ solutions n) :
    s ≤ 2 * n := by
  have hlt := lt_mul_of_mem hn h
  simp only [solutions, Set.mem_ofPred_eq] at h
  obtain ⟨hr, hrs, hst, heq⟩ := h
  -- `r*s*s ≤ n*r + 2*n*s`, from `(t - s)*(r*s - n) ≥ 0`.
  have hkey : (r * s * s : ℤ) ≤ n * r + 2 * n * s := by
    have heqZ : (r * s * t : ℤ) = n * (r + s + t) := by exact_mod_cast heq
    have hprod : (0 : ℤ) ≤ ((t : ℤ) - s) * ((r : ℤ) * s - n) := by
      apply mul_nonneg
      · have : (s : ℤ) ≤ t := by exact_mod_cast hst
        linarith
      · have : (n : ℤ) < r * s := by exact_mod_cast hlt
        linarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have hs : (2 * n + 1 : ℤ) ≤ s := by exact_mod_cast hcon
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have h5 : (r * s * (2 * n + 1) : ℤ) ≤ r * s * s :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h6 : (1 * (n * s) : ℤ) ≤ r * (n * s) := mul_le_mul_of_nonneg_right hr1 (by positivity)
  have h7 : (r * (2 * n + 1) : ℤ) ≤ r * s := mul_le_mul_of_nonneg_left hs (by positivity)
  nlinarith

/-- The triple `(1, n+1, n*(n+2))` is a solution for every `n ≥ 1`. -/
theorem mem_t_witness {n : ℕ} (hn : 0 < n) : (1, n + 1, n * (n + 2)) ∈ solutions n := by
  simp only [solutions, Set.mem_ofPred_eq]
  refine ⟨Nat.one_pos, by omega, by nlinarith, by ring⟩

/-- The triple `(1, 2*n, 2*n+1)` is a solution for every `n ≥ 1`. -/
theorem mem_s_witness {n : ℕ} (hn : 0 < n) : (1, 2 * n, 2 * n + 1) ∈ solutions n := by
  simp only [solutions, Set.mem_ofPred_eq]
  refine ⟨Nat.one_pos, by omega, by omega, by ring⟩

/-! ## Ground truth for the sequence values `a(1) = 1` and `a(2) = 2`

The entry's `a(n)` is the maximum of `min(r,s,t) = r` over `solutions n`. -/

/-- `a(1) = 1`: the largest `r` over `solutions 1` is `1`. -/
example : IsGreatest ((fun p : ℕ × ℕ × ℕ => p.1) '' solutions 1) 1 := by
  refine ⟨⟨(1, 2, 3), by simp only [solutions, Set.mem_ofPred_eq]; decide, rfl⟩, ?_⟩
  rintro _ ⟨⟨r, s, t⟩, hp, rfl⟩
  have hs := le_of_mem_s Nat.one_pos hp
  simp only [solutions, Set.mem_ofPred_eq] at hp ⊢
  obtain ⟨hr, hrs, hst, heq⟩ := hp
  interval_cases s <;> interval_cases r <;> omega

/-- `a(2) = 2`: the largest `r` over `solutions 2` is `2`. -/
example : IsGreatest ((fun p : ℕ × ℕ × ℕ => p.1) '' solutions 2) 2 := by
  refine ⟨⟨(2, 2, 4), by simp only [solutions, Set.mem_ofPred_eq]; decide, rfl⟩, ?_⟩
  rintro _ ⟨⟨r, s, t⟩, hp, rfl⟩
  have hs := le_of_mem_s two_pos hp
  simp only [solutions, Set.mem_ofPred_eq] at hp ⊢
  obtain ⟨hr, hrs, hst, heq⟩ := hp
  interval_cases s <;> interval_cases r <;> omega

/-! ## The conjecture -/

/-- **Layman's conjecture, `t` part (A078173, John W. Layman, Nov 20 2002).**
For every `n ≥ 1`, the maximum of `t` over all positive integer solutions
`r ≤ s ≤ t` of `r*s*t = n*(r+s+t)` is `n*(n+2)`. -/
theorem isGreatest_t {n : ℕ} (hn : 0 < n) :
    IsGreatest ((fun p : ℕ × ℕ × ℕ => p.2.2) '' solutions n) (n * (n + 2)) := by
  refine ⟨⟨_, mem_t_witness hn, rfl⟩, ?_⟩
  rintro _ ⟨⟨r, s, t⟩, hp, rfl⟩
  exact le_of_mem_t hn hp

/-- **Layman's conjecture, `s` part (A078173, John W. Layman, Nov 20 2002).**
For every `n ≥ 1`, the maximum of `s` over all positive integer solutions
`r ≤ s ≤ t` of `r*s*t = n*(r+s+t)` is `2*n`. -/
theorem isGreatest_s {n : ℕ} (hn : 0 < n) :
    IsGreatest ((fun p : ℕ × ℕ × ℕ => p.2.1) '' solutions n) (2 * n) := by
  refine ⟨⟨_, mem_s_witness hn, rfl⟩, ?_⟩
  rintro _ ⟨⟨r, s, t⟩, hp, rfl⟩
  exact le_of_mem_s hn hp

/-- **Layman's conjecture (A078173, John W. Layman, Nov 20 2002).**
Verbatim: "Conjecture: max(t) = n*(n+2) and max(s) = 2*n, where the maxima are
taken over all positive integer solutions r<=s<=t of the above Diophantine
equation."  Here the equation is `r*s*t = n*(r+s+t)` and `n ≥ 1`. -/
theorem layman_conjecture {n : ℕ} (hn : 0 < n) :
    IsGreatest ((fun p : ℕ × ℕ × ℕ => p.2.2) '' solutions n) (n * (n + 2)) ∧
      IsGreatest ((fun p : ℕ × ℕ × ℕ => p.2.1) '' solutions n) (2 * n) :=
  ⟨isGreatest_t hn, isGreatest_s hn⟩

end Candidates.A078173LaymanSolutionsMaximum
