/-
# A173102 — Hurt: the ceiling double sum counts `x + y = z` in `{1, …, 3n}`

## OEIS source (pulled with `oeis show A173102`, retrieved 2026-10-21)

```
NAME:     Number of partitions x + y = z with {x,y,z} in {1,2,3,..,3*n} and
          z > y >= x.
TERMS:    2,9,20,36,56,81,110,144,182,225,272,324,380,441,506,576,650,729,812,
          900,992,1089,1190,1296,1406,1521,1640,1764,1892,2025,...
OFFSET:   1
FORMULA (the conjecture):
  Conjecture: a(n) = Sum_{j=1..n} Sum_{i=1..n} ceiling((i+j-n+3)/2).
  - _Wesley Ivan Hurt_, Mar 12 2015
FORMULA (context): From _Chai Wah Wu_, Mar 03 2020: a(n) = (9*n^2-1)/4 if n
  is odd and a(n) = 9*n^2/4 if n is even, proved in the entry via
  a(n) = Sum_{z = 2..3*n} floor(z/2).
```

## Status

Triage: open (Hurt's double-sum form has no proof in the entry; Wu's closed
form is proved there).  Python re-check (2026-10-21): the triple count, Hurt's
double sum (exact rational ceilings) and `floor(9 n^2 / 4)` agree for
`0 ≤ n < 80` (brute-force triple count for `n < 60`).

## Proof outline (all kernel-checked below)

* `⌈m / 2⌉ = ⌊(m + 1) / 2⌋` for `m : ℤ` (`ceil_half`), so after reindexing
  both sides become sums of `F n c = ∑_{i<n} ⌊(i + c + 1) / 2⌋`.
* `F (2k) c = k² + k c` and `F (2k+1) c = k² + k c + k + ⌊(c+1)/2⌋`.
* Fibering the triples over `z` gives `a n = ∑_{z=1}^{3n} ⌊z/2⌋ = F (3n) 0`
  (Wu's argument); Hurt's sum is `∑_{j<n} F n (j + 5 - n)`.
* Both sides equal `9k²` for `n = 2k` and `9k² + 9k + 2` for `n = 2k + 1`.

Ceilings in the statement are taken in `ℚ` of the integer `i + j - n + 3`
(casts to `ℤ` happen before the subtraction); for `n ≥ 6` some arguments are
negative and the true ceiling is used.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A173102HurtCeilCounts

open Finset

/-- `F n c = ∑_{i<n} ⌊(i + c + 1)/2⌋` (integer floor division). -/
def F (n : ℕ) (c : ℤ) : ℤ := ∑ i ∈ range n, ((i : ℤ) + c + 1) / 2

/-- `F (2k) c = k² + k c`. -/
lemma F_even (k : ℕ) (c : ℤ) : F (2 * k) c = (k : ℤ) * k + k * c := by
  induction k with
  | zero => simp [F]
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [F, h2, sum_range_succ, sum_range_succ, ← F, ih]
    push_cast
    have hdiv : ((2 * (k : ℤ)) + c + 1) / 2 + ((2 * (k : ℤ) + 1) + c + 1) / 2
        = 2 * k + c + 1 := by omega
    linear_combination hdiv

/-- `F (2k+1) c = k² + k c + k + ⌊(c + 1)/2⌋`. -/
lemma F_odd (k : ℕ) (c : ℤ) : F (2 * k + 1) c = (k : ℤ) * k + k * c + k + (c + 1) / 2 := by
  rw [F, sum_range_succ, ← F, F_even]
  push_cast
  have hdiv : (2 * (k : ℤ) + c + 1) / 2 = k + (c + 1) / 2 := by omega
  rw [hdiv]; ring

/-- Reindex a sum over `{1, …, n}` as a sum over `range n`. -/
lemma sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Icc 1 n, f i = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- For an integer `m`, `⌈m / 2⌉ = ⌊(m + 1) / 2⌋` (ceiling taken in `ℚ`). -/
lemma ceil_half (m : ℤ) : ⌈(m : ℚ) / 2⌉ = (m + 1) / 2 := by
  obtain ⟨q, hq | hq⟩ := Int.even_or_odd' m
  · have h1 : (m + 1) / 2 = q := by omega
    rw [h1, hq]; push_cast; simp
  · have h1 : (m + 1) / 2 = q + 1 := by omega
    rw [h1, hq, Int.ceil_eq_iff]; push_cast; constructor <;> linarith

/-- Twice the Gauss sum `∑_{j<n} j`, in `ℤ`. -/
lemma two_mul_sum_range_cast (n : ℕ) : 2 * ∑ j ∈ range n, (j : ℤ) = n * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

/-- The number of triples `(x, y, z)` with `1 ≤ x ≤ y < z ≤ N` and `x + y = z`. -/
def tripleCount (N : ℕ) : ℕ :=
  #{t ∈ Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N | t.1 + t.2.1 = t.2.2 ∧ t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2}

/-- Wu's fibering over `z`: `tripleCount N = ∑_{z=1}^{N} ⌊z/2⌋`. -/
lemma tripleCount_eq_sum (N : ℕ) : tripleCount N = ∑ z ∈ Icc 1 N, z / 2 := by
  rw [tripleCount, card_eq_sum_card_fiberwise (f := fun t => t.2.2) (t := Icc 1 N)]
  · refine sum_congr rfl fun z hz => ?_
    have hz' : 1 ≤ z ∧ z ≤ N := mem_Icc.mp hz
    have hfib : ({t ∈ {t ∈ Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N |
          t.1 + t.2.1 = t.2.2 ∧ t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2} | t.2.2 = z} : Finset (ℕ × ℕ × ℕ))
        = (Icc 1 (z / 2)).image (fun x => (x, z - x, z)) := by
      ext ⟨x, y, w⟩
      simp only [mem_filter, mem_product, mem_Icc, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hw1, hw2⟩⟩, hs, hxy, hyw⟩, hwz⟩
        exact ⟨x, ⟨hx1, by omega⟩, rfl, by omega, by omega⟩
      · rintro ⟨a, ⟨ha1, ha2⟩, rfl, rfl, rfl⟩
        omega
    have hinj : Function.Injective (fun x : ℕ => (x, z - x, z)) := fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact h.1
    rw [hfib, card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  · intro t ht
    simp only [coe_filter, mem_product, mem_Icc, Set.mem_ofPred_eq] at ht
    simp only [coe_Icc, Set.mem_Icc]
    omega

/-- Hurt's double sum `∑_{j=1..n} ∑_{i=1..n} ⌈(i + j - n + 3)/2⌉`, computed in `ℤ`/`ℚ`. -/
def hurtSum (n : ℕ) : ℤ :=
  ∑ j ∈ Icc 1 n, ∑ i ∈ Icc 1 n, ⌈(((i : ℤ) + j - n + 3 : ℤ) : ℚ) / 2⌉

/-- Hurt's double sum, reindexed: `hurtSum n = ∑_{j<n} F n (j + 5 - n)`. -/
lemma hurtSum_eq (n : ℕ) : hurtSum n = ∑ j ∈ range n, F n ((j : ℤ) + 5 - n) := by
  rw [hurtSum, sum_Icc_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_Icc_eq_sum_range, F]
  refine sum_congr rfl fun i _ => ?_
  rw [ceil_half]
  congr 1
  push_cast
  ring

/-- `tripleCount (3n) = F (3n) 0`, in `ℤ`. -/
lemma tripleCount_three_mul (n : ℕ) : (tripleCount (3 * n) : ℤ) = F (3 * n) 0 := by
  rw [tripleCount_eq_sum, sum_Icc_eq_sum_range, F]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  omega

/-- Hurt's double sum at even `n = 2k` equals `9k²`. -/
lemma hurtSum_even (k : ℕ) : hurtSum (2 * k) = 9 * ((k : ℤ) * k) := by
  have hS := two_mul_sum_range_cast (2 * k)
  set S := ∑ j ∈ range (2 * k), (j : ℤ) with hSdef
  have hS' : S = k * (2 * k - 1) := by push_cast at hS; linarith
  rw [hurtSum_eq]
  have hterm : ∀ j ∈ range (2 * k), F (2 * k) ((j : ℤ) + 5 - ((2 * k : ℕ) : ℤ))
      = (k * k + k * (5 - 2 * k) : ℤ) + k * j := fun j _ => by
    rw [F_even]; push_cast; ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_const, card_range, ← mul_sum, ← hSdef, hS',
    nsmul_eq_mul]
  push_cast
  ring

/-- Hurt's double sum at odd `n = 2k + 1` equals `9k² + 9k + 2`. -/
lemma hurtSum_odd (k : ℕ) : hurtSum (2 * k + 1) = 9 * ((k : ℤ) * k) + 9 * k + 2 := by
  have hS := two_mul_sum_range_cast (2 * k + 1)
  set S := ∑ j ∈ range (2 * k + 1), (j : ℤ) with hSdef
  have hS' : S = k * (2 * k + 1) := by push_cast at hS; linarith
  rw [hurtSum_eq]
  have hterm : ∀ j ∈ range (2 * k + 1), F (2 * k + 1) ((j : ℤ) + 5 - ((2 * k + 1 : ℕ) : ℤ))
      = ((k * k + k * (4 - 2 * k) + k : ℤ) + k * j) + ((j : ℤ) + (4 - 2 * k) + 1) / 2 :=
    fun j _ => by
      rw [F_odd]
      push_cast
      have hc : ((j : ℤ) + 5 - (2 * k + 1) + 1) / 2 = ((j : ℤ) + (4 - 2 * k) + 1) / 2 := by
        congr 1; ring
      rw [hc]; ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, sum_const, card_range, ← mul_sum,
    ← hSdef, hS', nsmul_eq_mul, ← F, F_odd]
  have hd : ((4 - 2 * (k : ℤ)) + 1) / 2 = 2 - k := by omega
  rw [hd]
  push_cast
  ring

/-- `a(n)` of A173102: the number of solutions of `x + y = z` with
`x, y, z ∈ {1, …, 3n}` and `z > y ≥ x`. -/
def a (n : ℕ) : ℕ := tripleCount (3 * n)

/-- **Hurt's conjecture (A173102, Wesley Ivan Hurt, Mar 12 2015).**

Verbatim: "Conjecture: a(n) = Sum_{j=1..n} Sum_{i=1..n} ceiling((i+j-n+3)/2)."

Here `a n` counts the solutions of `x + y = z` with `1 ≤ x ≤ y < z ≤ 3n`
(the entry's definition) and `hurtSum n` is the double sum with exact rational
ceilings.  Stated for every `n : ℕ`; the entry's offset is `1`, and at `n = 0`
both sides are `0`. -/
theorem a_eq_hurtSum (n : ℕ) : (a n : ℤ) = hurtSum n := by
  rw [a, tripleCount_three_mul]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [hurtSum_even, show 3 * (2 * k) = 2 * (3 * k) by ring, F_even]
    push_cast
    ring
  · rw [hurtSum_odd, show 3 * (2 * k + 1) = 2 * (3 * k + 1) + 1 by ring, F_odd]
    push_cast
    ring_nf

/-- Wu's closed form (proved in the entry, re-derived here):
`4 a(n) + (n mod 2) = 9 n²`, i.e. `a(n) = ⌊9n²/4⌋`. -/
theorem four_mul_a_add_mod_two (n : ℕ) : 4 * a n + n % 2 = 9 * n ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hmod : 2 * k % 2 = 0 := by omega
    rw [hmod]
    zify
    rw [a, tripleCount_three_mul, show 3 * (2 * k) = 2 * (3 * k) by ring, F_even]
    push_cast
    ring
  · have hmod : (2 * k + 1) % 2 = 1 := by omega
    rw [hmod]
    zify
    rw [a, tripleCount_three_mul, show 3 * (2 * k + 1) = 2 * (3 * k + 1) + 1 by ring, F_odd]
    push_cast
    ring_nf

/-! ## Ground truth against the listed terms `2, 9, 20, 36, …` -/

example : a 1 = 2 := by decide
example : a 2 = 9 := by decide
set_option maxRecDepth 20000 in
example : a 3 = 20 := by decide
set_option maxRecDepth 20000 in
example : a 4 = 36 := by decide
example : hurtSum 1 = 2 := by norm_num [hurtSum, Int.ceil_eq_iff]
example : hurtSum 2 = 9 := by norm_num [hurtSum, Finset.sum_Icc_succ_top, Int.ceil_eq_iff]
example : hurtSum 3 = 20 := by norm_num [hurtSum, Finset.sum_Icc_succ_top, Int.ceil_eq_iff]
example : hurtSum 4 = 36 := by norm_num [hurtSum, Finset.sum_Icc_succ_top, Int.ceil_eq_iff]
-- `n = 7`: some ceiling arguments are negative (`i + j - 4 < 0` at `i = j = 1`).
example : hurtSum 7 = 110 := by norm_num [hurtSum, Finset.sum_Icc_succ_top, Int.ceil_eq_iff]

end Candidates.A173102HurtCeilCounts
