/-
# A000384 — Chu: minimal basis pair for `{0, …, 2·a(n)}` has size `2n`

## OEIS source (retrieved with `oeis show A000384`, 2026-10-21)

```
NAME:     Hexagonal numbers: a(n) = n*(2*n-1).
TERMS:    0,1,6,15,28,45,66,91,120,153,190,231,276,325,378,435,496,561,630,...
COMMENT (the conjecture):
  Conjecture: For n>0, min{k such that there exist subsets A,B of
  {0,1,2,...,a(n)} such that |A|=|B|=k and A+B={0,1,2,...,2*a(n)}} = 2*n.
  - _Michael Chu_, Mar 09 2022
```

## Status

Triage status: open (no proof in the entry or the literature as far as the
triage could tell).  An elementary argument settles it, and this module
kernel-checks it:

* lower bound: `|A + B| ≤ |A|·|B| = k²` must reach `2N + 1 = 4n² - 2n + 1`,
  which exceeds `(2n - 1)²`, so `2n ≤ k`;
* upper bound: `B = {0, n, 2n, …, (2n-1)n}` and
  `A = {0, …, n-1} ∪ {N-n+1, …, N}` (with `N = n(2n-1)`) give
  `A + B = {0, …, 2N}`.
-/
import Mathlib

set_option autoImplicit false

open Pointwise

namespace Candidates.A000384MinimumThereExactly

/-- The hexagonal number `a(n) = n(2n - 1)` (OEIS A000384).  The natural-number
subtraction is harmless: for `n = 0` the product is `0` either way. -/
def hexagonal (n : ℕ) : ℕ := n * (2 * n - 1)

example : hexagonal 0 = 0 := rfl
example : hexagonal 1 = 1 := rfl
example : hexagonal 2 = 6 := rfl
example : hexagonal 3 = 15 := rfl
example : hexagonal 4 = 28 := rfl
example : hexagonal 5 = 45 := rfl

/-- The set of admissible sizes in Chu's comment: those `k` for which there are
`A, B ⊆ {0, …, N}` with `|A| = |B| = k` and `A + B = {0, …, 2N}`. -/
def admissibleSizes (N : ℕ) : Set ℕ :=
  {k | ∃ A B : Finset ℕ, A ⊆ Finset.range (N + 1) ∧ B ⊆ Finset.range (N + 1) ∧
    A.card = k ∧ B.card = k ∧ A + B = Finset.range (2 * N + 1)}

/-- Sanity check of the definition at `N = 1` (`n = 1`): `A = B = {0, 1}`
works with `k = 2`. -/
example : 2 ∈ admissibleSizes 1 :=
  ⟨{0, 1}, {0, 1}, by decide, by decide, rfl, rfl, by decide⟩

/-- Lower bound: any admissible size for `N = a(n)` with `1 ≤ n` is at least
`2n`, since `|A + B| ≤ |A|·|B|`. -/
theorem two_mul_le_of_mem_admissibleSizes (n : ℕ) (hn : 1 ≤ n) (k : ℕ)
    (hk : k ∈ admissibleSizes (hexagonal n)) : 2 * n ≤ k := by
  obtain ⟨A, B, -, -, hA, hB, hAB⟩ := hk
  have hcard : 2 * hexagonal n + 1 ≤ k * k := by
    have h := Finset.card_add_le (s := A) (t := B)
    rw [hAB, Finset.card_range, hA, hB] at h
    exact h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hhex : hexagonal (m + 1) = (m + 1) * (2 * m + 1) := by
    unfold hexagonal
    congr 1
  rw [hhex] at hcard
  by_contra hlt
  have hk : k ≤ 2 * m + 1 := by omega
  have hsq : k * k ≤ (2 * m + 1) * (2 * m + 1) := Nat.mul_le_mul hk hk
  nlinarith

/-- Upper bound: `2n` is admissible for `N = a(n)` with `1 ≤ n`, witnessed by
`A = {0, …, n-1} ∪ {N-n+1, …, N}` and `B = {0, n, 2n, …, (2n-1)n}`. -/
theorem two_mul_mem_admissibleSizes (n : ℕ) (hn : 1 ≤ n) :
    2 * n ∈ admissibleSizes (hexagonal n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set N := hexagonal (m + 1) with hNdef
  have hN : N = (m + 1) * (2 * m + 1) := by
    rw [hNdef]
    unfold hexagonal
    congr 1
  -- linear consequences of `N = (m+1)(2m+1)` used below
  have hN1 : 2 * (m + 1) ≤ N + 1 := by rw [hN]; nlinarith
  have hN2 : N + 1 + m = (m + 1) * (2 * (m + 1)) := by rw [hN]; ring
  let A : Finset ℕ := Finset.range (m + 1) ∪ Finset.Icc (N + 1 - (m + 1)) N
  let B : Finset ℕ := (Finset.range (2 * (m + 1))).image (fun i => (m + 1) * i)
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [A, Finset.mem_union, Finset.mem_range, Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  · intro x hx
    simp only [B, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range]
    have hle : (m + 1) * i ≤ (m + 1) * (2 * m + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · have hdisj : Disjoint (Finset.range (m + 1)) (Finset.Icc (N + 1 - (m + 1)) N) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_range] at hx
      rw [Finset.mem_Icc] at hx'
      omega
    simp only [A]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range, Nat.card_Icc]
    omega
  · simp only [B]
    rw [Finset.card_image_of_injective _ (mul_right_injective₀ (by omega)),
      Finset.card_range]
  · ext x
    rw [Finset.mem_add, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simp only [A, Finset.mem_union, Finset.mem_range, Finset.mem_Icc] at ha
      simp only [B, Finset.mem_image, Finset.mem_range] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      have hle : (m + 1) * i ≤ (m + 1) * (2 * m + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · intro hx
      -- every `y < (m+1)·2(m+1)` is `y % (m+1) + (m+1)·(y / (m+1))` with
      -- quotient below `2(m+1)`
      have hdecomp : ∀ y, y < (m + 1) * (2 * (m + 1)) →
          y % (m + 1) < m + 1 ∧ y / (m + 1) < 2 * (m + 1) ∧
            y % (m + 1) + (m + 1) * (y / (m + 1)) = y := fun y hy =>
        ⟨Nat.mod_lt _ (by omega), (Nat.div_lt_iff_lt_mul (by omega)).2 (by linarith),
          Nat.mod_add_div y (m + 1)⟩
      have hmemB : ∀ i, i < 2 * (m + 1) → (m + 1) * i ∈ B := fun i hi => by
        simp only [B, Finset.mem_image, Finset.mem_range]
        exact ⟨i, hi, rfl⟩
      by_cases hsmall : x < N + 1 - (m + 1)
      · obtain ⟨hr, hq, hsum⟩ := hdecomp x (by omega)
        refine ⟨x % (m + 1), ?_, (m + 1) * (x / (m + 1)), hmemB _ hq, hsum⟩
        simp only [A, Finset.mem_union, Finset.mem_range]
        exact Or.inl hr
      · set y := x - (N + 1 - (m + 1)) with hy
        obtain ⟨hr, hq, hsum⟩ := hdecomp y (by omega)
        refine ⟨N + 1 - (m + 1) + y % (m + 1), ?_, (m + 1) * (y / (m + 1)),
          hmemB _ hq, by omega⟩
        simp only [A, Finset.mem_union, Finset.mem_Icc]
        exact Or.inr ⟨by omega, by omega⟩

/-- **Chu's conjecture (A000384, Michael Chu, Mar 09 2022).**

Verbatim: "Conjecture: For n>0, min{k such that there exist subsets A,B of
{0,1,2,...,a(n)} such that |A|=|B|=k and A+B={0,1,2,...,2*a(n)}} = 2*n."

Formal reading: for `1 ≤ n` and `N = a(n) = n(2n-1)`, `2n` is the least `k`
for which there are `A, B ⊆ {0, …, N}` with `|A| = |B| = k` and
`A + B = {0, …, 2N}`. -/
theorem chu_conjecture (n : ℕ) (hn : 1 ≤ n) :
    IsLeast (admissibleSizes (hexagonal n)) (2 * n) :=
  ⟨two_mul_mem_admissibleSizes n hn, fun k hk => two_mul_le_of_mem_admissibleSizes n hn k hk⟩

end Candidates.A000384MinimumThereExactly
