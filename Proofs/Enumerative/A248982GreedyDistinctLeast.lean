/-
# A248982 — greedy distinct sequence with Fibonacci running averages

## OEIS source (retrieved with `oeis show A248982`, 2026-10-21)

```
NAME:     Sequence of distinct least positive numbers such that the average of
          the first n terms is a Fibonacci number.
TERMS:    1,3,2,6,13,5,26,8,53,93,21,177,34,328,55,599,89,1079,144,1924,233,
          3401,377,5969,610,10412,987,18067,1597,31207,2584,53688,4181,92037,...
FORMULA:  Conjecture: a(n) = 2*a(n-2)+a(n-4)-2*a(n-6)-a(n-8) for n > 17.
          - _Colin Barker_, Oct 19 2014
FORMULA:  Conjecture: For n > 4, a(2*n+1) = A000045(n+3).
```

Fried's refined form (arXiv:2410.07237, J. Integer Seq.): for `n ≥ 10`,
`a(n) = n*F(n/2+3) - (n-1)*F(n/2+2)` when `n` is even and
`a(n) = F((n+1)/2+2)` when `n` is odd.

## Status (triage)

Open as far as the triage could tell: Fried reduced the problem to showing
that the even-index values are never Fibonacci numbers and states that he
could not prove this; a claimed resolution (arXiv:2509.26138) is withdrawn.

## Proof outline (this file)

Put `b i = F(i+2) + 2 i F(i+1)`.  From `n = 10` on, the running sum is
`s_n = n F(⌊n/2⌋+3)`.  At an odd step the least admissible average is
`F(j+3)`, giving the value `F(j+3)`; at an even step the average `F(j+3)`
would repeat the previous term, so the next average is `F(j+4)`, giving
`b (j+1)`.  Freshness of `F(j+3)` needs `b i` never to be a Fibonacci number
(`b_ne_fib`), proved with `F(m) = F(s) F(i+1) + F(s+1) F(i+2)` and
`gcd(F(i+1), F(i+2)) = 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A248982GreedyDistinctLeast

open Nat

/-! ## Definitions -/

/-- `Valid prev v`: `v` is an admissible next term after the terms `prev`:
`v` is positive, not among `prev`, and the average of `prev ++ [v]` is a
Fibonacci number, i.e. `sum prev + v = (length prev + 1) * F(m)` for some `m`. -/
def Valid (prev : List ℕ) (v : ℕ) : Prop :=
  0 < v ∧ v ∉ prev ∧ ∃ m, prev.sum + v = (prev.length + 1) * fib m

/-- Some admissible next term always exists. -/
theorem exists_valid (prev : List ℕ) : ∃ v, Valid prev v := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * prev.sum < fib m :=
    ⟨2 * prev.sum + 2, by have := le_fib_add_one (2 * prev.sum + 2); omega⟩
  have hle : fib m ≤ (prev.length + 1) * fib m := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨(prev.length + 1) * fib m - prev.sum, by omega, ?_, ⟨m, by omega⟩⟩
  intro hmem
  have := List.le_sum_of_mem hmem
  omega

open Classical in
/-- The greedy choice: the least admissible next term after `prev`. -/
noncomputable def step (prev : List ℕ) : ℕ := Nat.find (exists_valid prev)

/-- `terms k` is the list `[a(1), ..., a(k)]` of the first `k` greedy terms. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | k + 1 => terms k ++ [step (terms k)]

/-- OEIS A248982 (offset 1): `a(n)` is the least positive integer, distinct
from `a(1), ..., a(n-1)`, such that `(a(1) + ... + a(n)) / n` is a Fibonacci
number.  (`a 0` is a junk value equal to `a 1`.) -/
noncomputable def a (n : ℕ) : ℕ := step (terms (n - 1))

/-! ## Basic API -/

/-- Characterisation of the greedy choice. -/
theorem step_eq_iff (prev : List ℕ) (v : ℕ) :
    step prev = v ↔ Valid prev v ∧ ∀ w < v, ¬ Valid prev w := by
  classical
  unfold step
  convert Nat.find_eq_iff (exists_valid prev) using 1

/-- The greedy choice is admissible. -/
theorem step_valid (prev : List ℕ) : Valid prev (step prev) :=
  ((step_eq_iff prev _).mp rfl).1

/-- `terms k` has length `k`. -/
theorem length_terms (k : ℕ) : (terms k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [terms, ih]

/-- `a (k + 1)` is the greedy choice after `terms k`. -/
theorem a_succ (k : ℕ) : a (k + 1) = step (terms k) := rfl

/-- Bounded form of `Valid`, used for finite checks: if `sum + v < F(K)` then
only indices `m < K` can occur. -/
theorem valid_iff_bounded (prev : List ℕ) (v K : ℕ) (hK : prev.sum + v < fib K) :
    Valid prev v ↔
      0 < v ∧ v ∉ prev ∧ ∃ m < K, prev.sum + v = (prev.length + 1) * fib m := by
  unfold Valid
  refine ⟨fun ⟨h1, h2, m, hm⟩ => ⟨h1, h2, m, ?_, hm⟩,
    fun ⟨h1, h2, m, _, hm⟩ => ⟨h1, h2, m, hm⟩⟩
  by_contra hmK
  have h1 : fib K ≤ fib m := fib_mono (by omega)
  have h2 : fib m ≤ (prev.length + 1) * fib m := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Finite certificate for one greedy step. -/
theorem step_eq_of_bounded (prev : List ℕ) (v K : ℕ) (hK : prev.sum + v < fib K)
    (hv : 0 < v ∧ v ∉ prev ∧ ∃ m < K, prev.sum + v = (prev.length + 1) * fib m)
    (hmin : ∀ w < v,
      ¬ (0 < w ∧ w ∉ prev ∧ ∃ m < K, prev.sum + w = (prev.length + 1) * fib m)) :
    step prev = v := by
  rw [step_eq_iff]
  refine ⟨(valid_iff_bounded prev v K hK).mpr hv, fun w hw => ?_⟩
  rw [valid_iff_bounded prev w K (by omega)]
  exact hmin w hw

/-! ## The first ten terms -/

/-- The first ten terms `1, 3, 2, 6, 13, 5, 26, 8, 53, 93`. -/
theorem terms_ten : terms 10 = [1, 3, 2, 6, 13, 5, 26, 8, 53, 93] := by
  have h1 : terms 1 = [1] := by
    rw [terms, terms, step_eq_of_bounded [] 1 4 (by decide) (by decide) (by decide)]; rfl
  have h2 : terms 2 = [1, 3] := by
    rw [terms, h1, step_eq_of_bounded [1] 3 6 (by decide) (by decide) (by decide)]; rfl
  have h3 : terms 3 = [1, 3, 2] := by
    rw [terms, h2, step_eq_of_bounded [1, 3] 2 6 (by decide) (by decide) (by decide)]; rfl
  have h4 : terms 4 = [1, 3, 2, 6] := by
    rw [terms, h3, step_eq_of_bounded [1, 3, 2] 6 8 (by decide) (by decide) (by decide)]; rfl
  have h5 : terms 5 = [1, 3, 2, 6, 13] := by
    rw [terms, h4, step_eq_of_bounded [1, 3, 2, 6] 13 10 (by decide) (by decide)
      (by decide)]; rfl
  have h6 : terms 6 = [1, 3, 2, 6, 13, 5] := by
    rw [terms, h5, step_eq_of_bounded [1, 3, 2, 6, 13] 5 10 (by decide) (by decide)
      (by decide)]; rfl
  have h7 : terms 7 = [1, 3, 2, 6, 13, 5, 26] := by
    rw [terms, h6, step_eq_of_bounded [1, 3, 2, 6, 13, 5] 26 12 (by decide) (by decide)
      (by decide)]; rfl
  have h8 : terms 8 = [1, 3, 2, 6, 13, 5, 26, 8] := by
    rw [terms, h7, step_eq_of_bounded [1, 3, 2, 6, 13, 5, 26] 8 12 (by decide)
      (by decide) (by decide)]; rfl
  have h9 : terms 9 = [1, 3, 2, 6, 13, 5, 26, 8, 53] := by
    rw [terms, h8, step_eq_of_bounded [1, 3, 2, 6, 13, 5, 26, 8] 53 13 (by decide)
      (by decide) (by decide)]; rfl
  rw [terms, h9, step_eq_of_bounded [1, 3, 2, 6, 13, 5, 26, 8, 53] 93 15 (by decide)
    (by decide) (by decide)]; rfl

/-! ## Fibonacci lemmas -/

/-- The even-index closed form `b i = F(i+2) + 2 i F(i+1)`
(`= 2i F(i+3) - (2i-1) F(i+2)`). -/
def b (i : ℕ) : ℕ := fib (i + 2) + 2 * i * fib (i + 1)

/-- `2 i < F(i+2)` for `i ≥ 5`. -/
theorem two_mul_lt_fib (i : ℕ) (hi : 5 ≤ i) : 2 * i < fib (i + 2) := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ i hi ih =>
    have h2 : 2 ≤ fib (i + 1) := by
      have h3 : fib 3 = 2 := by decide
      have : fib 3 ≤ fib (i + 1) := fib_mono (by omega)
      omega
    rw [show i + 1 + 2 = i + 1 + 2 by rfl, fib_add_two]
    rw [show i + 1 + 1 = i + 2 by rfl] at *
    omega

/-- **Key lemma.** For `i ≥ 5`, `b i = F(i+2) + 2 i F(i+1)` is not a Fibonacci
number. -/
theorem b_ne_fib (i m : ℕ) (hi : 5 ≤ i) : b i ≠ fib m := by
  intro h
  unfold b at h
  have hF1 : 0 < fib (i + 1) := fib_pos.mpr (by omega)
  have hlt : 2 * i < fib (i + 2) := two_mul_lt_fib i hi
  -- `m ≥ i + 3`, since `b i > F(i+2)`.
  have hm : i + 3 ≤ m := by
    by_contra hm
    have : fib m ≤ fib (i + 2) := fib_mono (by omega)
    have : 0 < 2 * i * fib (i + 1) := Nat.mul_pos (by omega) hF1
    omega
  obtain ⟨s, rfl⟩ : ∃ s, m = s + (i + 1) + 1 := ⟨m - (i + 2), by omega⟩
  have hs : 1 ≤ s := by omega
  rw [fib_add s (i + 1)] at h
  -- `h : F(i+2) + 2 i F(i+1) = F(s) F(i+1) + F(s+1) F(i+2)`
  have hs1 : 1 ≤ fib (s + 1) := fib_pos.mpr (by omega)
  obtain ⟨u, hu⟩ : ∃ u, fib (s + 1) = u + 1 := ⟨fib (s + 1) - 1, by omega⟩
  rw [hu] at h
  have key : u * fib (i + 2) + fib s * fib (i + 1) = 2 * i * fib (i + 1) := by
    have : (u + 1) * fib (i + 2) = u * fib (i + 2) + fib (i + 2) := by ring
    rw [this] at h
    linarith
  rcases Nat.eq_zero_or_pos u with hu0 | hu0
  · -- `u = 0`: then `F(s+1) = 1` and `F(s) = 2 i`, impossible
    subst hu0
    have hfs : fib s = 2 * i := by
      have := key
      simp only [zero_mul, zero_add] at this
      exact Nat.eq_of_mul_eq_mul_right hF1 this
    have hs2 : s + 1 < 3 := by
      by_contra hcon
      have h3 : fib 3 = 2 := by decide
      have : fib 3 ≤ fib (s + 1) := fib_mono (by omega)
      omega
    obtain rfl : s = 1 := by omega
    simp only [fib_one] at hfs
    omega
  · -- `u > 0`: coprimality gives `F(i+1) ∣ u`, so `F(i+2) ≤ 2 i`
    have hdvd : fib (i + 1) ∣ u * fib (i + 2) := by
      have h1 : fib (i + 1) ∣ u * fib (i + 2) + fib s * fib (i + 1) := by
        rw [key]; exact Dvd.intro_left _ rfl
      exact (Nat.dvd_add_left (Dvd.intro_left _ rfl)).mp h1
    have hcop : Nat.Coprime (fib (i + 1)) (fib (i + 2)) := fib_coprime_fib_succ (i + 1)
    have hdu : fib (i + 1) ∣ u := hcop.dvd_of_dvd_mul_right hdvd
    have hule : fib (i + 1) ≤ u := Nat.le_of_dvd hu0 hdu
    have h3 : fib (i + 1) * fib (i + 2) ≤ 2 * i * fib (i + 1) := by
      calc fib (i + 1) * fib (i + 2) ≤ u * fib (i + 2) := Nat.mul_le_mul_right _ hule
        _ ≤ 2 * i * fib (i + 1) := by omega
    have h4 : fib (i + 2) ≤ 2 * i := by
      rw [mul_comm] at h3
      exact Nat.le_of_mul_le_mul_right h3 hF1
    omega

/-- `b` is strictly increasing. -/
theorem b_strictMono : StrictMono b := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  unfold b
  have h1 : fib (i + 2) ≤ fib (i + 1 + 2) := fib_mono (by omega)
  have h2 : fib (i + 1) ≤ fib (i + 1 + 1) := fib_mono (by omega)
  have h3 : 0 < fib (i + 1 + 1) := fib_pos.mpr (by omega)
  have h4 : 2 * i * fib (i + 1) ≤ 2 * i * fib (i + 1 + 1) := Nat.mul_le_mul_left _ h2
  have h5 : 2 * i * fib (i + 1 + 1) < 2 * (i + 1) * fib (i + 1 + 1) :=
    Nat.mul_lt_mul_of_pos_right (by omega) h3
  omega

/-- `F(j+3) < b (j+1)`. -/
theorem fib_lt_b_succ (j : ℕ) : fib (j + 3) < b (j + 1) := by
  unfold b
  have h : 0 < fib (j + 1 + 1) := fib_pos.mpr (by omega)
  have : 0 < 2 * (j + 1) * fib (j + 1 + 1) := Nat.mul_pos (by omega) h
  rw [show j + 1 + 2 = j + 3 by rfl]
  omega

/-! ## The inductive invariant -/

/-- The first nine terms, which do not follow the eventual pattern. -/
def base : List ℕ := [1, 3, 2, 6, 13, 5, 26, 8, 53]

/-- Invariant of `L = terms (2j)` for `j ≥ 5`: length `2j`, sum `2j F(j+3)`,
and every entry is a base term, some `b i` with `5 ≤ i ≤ j`, or some `F(i+3)`
with `5 ≤ i < j`. -/
def Inv (j : ℕ) (L : List ℕ) : Prop :=
  L.length = 2 * j ∧ L.sum = 2 * j * fib (j + 3) ∧
    ∀ x ∈ L, x ∈ base ∨ (∃ i, 5 ≤ i ∧ i ≤ j ∧ x = b i) ∨
      (∃ i, 5 ≤ i ∧ i < j ∧ x = fib (i + 3))

/-- For `j ≥ 5`, `F(j+3)` is not one of the base terms. -/
theorem fib_not_mem_base (j : ℕ) (hj : 5 ≤ j) : fib (j + 3) ∉ base := by
  rcases (show j = 5 ∨ j = 6 ∨ 7 ≤ j by omega) with rfl | rfl | hj7
  · decide
  · decide
  · have h10 : fib 10 ≤ fib (j + 3) := fib_mono (by omega)
    have h55 : fib 10 = 55 := by decide
    intro hmem
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega

/-- Base terms are below `b 5 = 93`. -/
theorem lt_of_mem_base (x : ℕ) (hx : x ∈ base) : x < 93 := by
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

/-- **Odd step.** If `Inv j L` with `j ≥ 5`, the greedy choice after `L` is
`F(j+3)`. -/
theorem step_odd (j : ℕ) (hj : 5 ≤ j) (L : List ℕ) (hL : Inv j L) :
    step L = fib (j + 3) := by
  obtain ⟨hlen, hsum, hmem⟩ := hL
  have hA : fib (j + 2) = fib j + fib (j + 1) := fib_add_two
  have hB : fib (j + 3) = fib (j + 1) + fib (j + 2) := fib_add_two
  have hjle : fib j ≤ fib (j + 1) := fib_le_fib_succ
  have hpos : 0 < fib (j + 1) := fib_pos.mpr (by omega)
  rw [step_eq_iff]
  refine ⟨⟨fib_pos.mpr (by omega), ?_, j + 3, by rw [hsum, hlen]; ring⟩, ?_⟩
  · intro hx
    rcases hmem _ hx with h | ⟨i, hi5, _, hi⟩ | ⟨i, _, hij, hi⟩
    · exact fib_not_mem_base j hj h
    · exact b_ne_fib i (j + 3) hi5 hi.symm
    · have : fib (i + 3) < fib (j + 3) := (fib_lt_fib (by omega)).mpr (by omega)
      omega
  · rintro w hw ⟨_, _, m, hm⟩
    rw [hsum, hlen] at hm
    have hmlt : m < j + 3 := by
      by_contra hcon
      have h1 : fib (j + 3) ≤ fib m := fib_mono (by omega)
      have h2 : (2 * j + 1) * fib (j + 3) ≤ (2 * j + 1) * fib m := Nat.mul_le_mul_left _ h1
      nlinarith
    have hfm : fib m ≤ fib (j + 2) := fib_mono (by omega)
    have h3 : (2 * j + 1) * fib m ≤ (2 * j + 1) * fib (j + 2) := Nat.mul_le_mul_left _ hfm
    have h4 : 2 * fib (j + 1) < 2 * j * fib (j + 1) := by nlinarith
    nlinarith

/-- **Even step.** If `Inv j L` with `j ≥ 5`, then after `L ++ [F(j+3)]` the
greedy choice is `b (j+1)`. -/
theorem step_even (j : ℕ) (hj : 5 ≤ j) (L : List ℕ) (hL : Inv j L) :
    step (L ++ [fib (j + 3)]) = b (j + 1) := by
  obtain ⟨hlen, hsum, hmem⟩ := hL
  have hA : fib (j + 2) = fib j + fib (j + 1) := fib_add_two
  have hB : fib (j + 3) = fib (j + 1) + fib (j + 2) := fib_add_two
  have hC : fib (j + 4) = fib (j + 2) + fib (j + 3) := fib_add_two
  have hjle : fib j ≤ fib (j + 1) := fib_le_fib_succ
  have hpos : 0 < fib (j + 1) := fib_pos.mpr (by omega)
  have hb : b (j + 1) = fib (j + 3) + 2 * (j + 1) * fib (j + 2) := rfl
  have hsum' : (L ++ [fib (j + 3)]).sum = (2 * j + 1) * fib (j + 3) := by
    rw [List.sum_append, hsum, List.sum_singleton]; ring
  have hlen' : (L ++ [fib (j + 3)]).length = 2 * j + 1 := by simp [hlen]
  have hb5 : b 5 ≤ b (j + 1) := b_strictMono.monotone (by omega)
  have hb5' : b 5 = 93 := by decide
  rw [step_eq_iff]
  refine ⟨⟨by have := fib_lt_b_succ j; omega, ?_, j + 4, ?_⟩, ?_⟩
  · -- every earlier term is smaller than `b (j+1)`
    intro hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · rcases hmem _ hx with h | ⟨i, _, hij, hi⟩ | ⟨i, _, hij, hi⟩
      · have := lt_of_mem_base _ h
        omega
      · have : b i < b (j + 1) := b_strictMono (by omega)
        omega
      · have h1 : fib (i + 3) ≤ fib (j + 3) := fib_mono (by omega)
        have h2 := fib_lt_b_succ j
        omega
    · have := fib_lt_b_succ j
      omega
  · rw [hsum', hlen', hb, hC, hB]; ring
  · rintro w hw ⟨hw0, hwL, m, hm⟩
    rw [hsum', hlen'] at hm
    have hlt : (2 * j + 1 + 1) * fib m < (2 * j + 1 + 1) * fib (j + 4) := by
      have : (2 * j + 1) * fib (j + 3) + b (j + 1) = (2 * j + 1 + 1) * fib (j + 4) := by
        rw [hb, hC, hB]; ring
      omega
    have hmlt : m < j + 4 := by
      by_contra hcon
      have h1 : fib (j + 4) ≤ fib m := fib_mono (by omega)
      have h2 := Nat.mul_le_mul_left (2 * j + 1 + 1) h1
      omega
    have hmge : j + 3 ≤ m := by
      by_contra hcon
      have hfm : fib m ≤ fib (j + 2) := fib_mono (by omega)
      have h3 : (2 * j + 1 + 1) * fib m ≤ (2 * j + 1 + 1) * fib (j + 2) :=
        Nat.mul_le_mul_left _ hfm
      have h4 : fib (j + 2) ≤ (2 * j + 1) * fib (j + 1) := by nlinarith
      nlinarith
    obtain rfl : m = j + 3 := by omega
    have hw' : w = fib (j + 3) := by nlinarith
    exact hwL (by rw [hw']; simp)

/-- Advancing the invariant by two greedy steps. -/
theorem inv_succ (j : ℕ) (hj : 5 ≤ j) (L : List ℕ) (hL : Inv j L) :
    Inv (j + 1) (L ++ [fib (j + 3)] ++ [b (j + 1)]) := by
  obtain ⟨hlen, hsum, hmem⟩ := hL
  have hB : fib (j + 3) = fib (j + 1) + fib (j + 2) := fib_add_two
  have hC : fib (j + 4) = fib (j + 2) + fib (j + 3) := fib_add_two
  have hb : b (j + 1) = fib (j + 3) + 2 * (j + 1) * fib (j + 2) := rfl
  refine ⟨by simp only [List.length_append, List.length_singleton, hlen]; ring, ?_, ?_⟩
  · simp only [List.sum_append, hsum, List.sum_singleton]
    rw [show j + 1 + 3 = j + 4 by rfl, hb, hC, hB]; ring
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | hx) | hx
    · rcases hmem x hx with h | ⟨i, hi5, hij, hi⟩ | ⟨i, hi5, hij, hi⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨i, hi5, by omega, hi⟩)
      · exact Or.inr (Or.inr ⟨i, hi5, by omega, hi⟩)
    · exact Or.inr (Or.inr ⟨j, hj, by omega, hx⟩)
    · exact Or.inr (Or.inl ⟨j + 1, by omega, le_rfl, hx⟩)

/-- The invariant holds for `terms 10`. -/
theorem inv_terms_ten : Inv 5 (terms 10) := by
  rw [terms_ten]
  refine ⟨rfl, by decide, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hb5 : b 5 = 93 := by decide
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact Or.inl (by decide)
    | exact Or.inr (Or.inl ⟨5, le_rfl, le_rfl, hb5.symm⟩)

/-- `a(2j+1) = F(j+3)` once `terms (2j)` satisfies the invariant. -/
theorem a_odd_of_inv (j : ℕ) (hj : 5 ≤ j) (hL : Inv j (terms (2 * j))) :
    a (2 * j + 1) = fib (j + 3) :=
  step_odd j hj _ hL

/-- `a(2j+2) = b (j+1)` once `terms (2j)` satisfies the invariant. -/
theorem a_even_of_inv (j : ℕ) (hj : 5 ≤ j) (hL : Inv j (terms (2 * j))) :
    a (2 * j + 2) = b (j + 1) := by
  rw [a_succ, terms, ← a_succ, a_odd_of_inv j hj hL]
  exact step_even j hj _ hL

/-- For every `j ≥ 5`, `terms (2j)` satisfies the invariant. -/
theorem inv_terms (j : ℕ) (hj : 5 ≤ j) : Inv j (terms (2 * j)) := by
  induction j, hj using Nat.le_induction with
  | base => exact inv_terms_ten
  | succ j hj ih =>
    have h2 : terms (2 * (j + 1)) = terms (2 * j) ++ [a (2 * j + 1)] ++ [a (2 * j + 2)] := rfl
    rw [h2, a_odd_of_inv j hj ih, a_even_of_inv j hj ih]
    exact inv_succ j hj _ ih

/-! ## Ground truth: the first listed terms -/

/-- `terms k` lists `a 1, ..., a k`. -/
theorem getElem?_terms (k n : ℕ) (h : n < k) : (terms k)[n]? = some (a (n + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hk : terms (k + 1) = terms k ++ [a (k + 1)] := rfl
    rw [hk]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · rw [List.getElem?_append_left (by rw [length_terms]; exact h'), ih h']
    · rw [List.getElem?_append_right (by rw [length_terms]), length_terms]
      simp

/-- The first ten terms of A248982 as listed in the entry. -/
theorem first_ten :
    [a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10] =
      [1, 3, 2, 6, 13, 5, 26, 8, 53, 93] := by
  have h := fun n (hn : n < 10) => getElem?_terms 10 n hn
  simp only [terms_ten] at h
  have e : ∀ n (hn : n < 10), a (n + 1) = [1, 3, 2, 6, 13, 5, 26, 8, 53, 93][n]'(by simpa using hn) := by
    intro n hn
    have := h n hn
    rw [List.getElem?_eq_getElem (by simpa using hn)] at this
    exact (Option.some.inj this).symm
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num), e 6 (by norm_num), e 7 (by norm_num),
    e 8 (by norm_num), e 9 (by norm_num)]
  rfl

example : a 7 = 26 := by
  have := congrArg (fun l => l[6]?) first_ten
  simpa using this

/-! ## Closed forms -/

/-- `a(2j+2) = b (j+1)` for `j ≥ 4` (the case `j = 4` is the base term `93`). -/
theorem a_even_closed (j : ℕ) (hj : 4 ≤ j) : a (2 * j + 2) = b (j + 1) := by
  rcases (show j = 4 ∨ 5 ≤ j by omega) with rfl | hj5
  · have := congrArg (fun l => l[9]?) first_ten
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at this
    rw [this]; decide
  · exact a_even_of_inv j hj5 (inv_terms j hj5)

/-- **Conjecture (A248982 formula line), proved.** For `n > 4`,
`a(2n+1) = F(n+3)` (`F = A000045`). -/
theorem a_two_mul_add_one (n : ℕ) (hn : 4 < n) : a (2 * n + 1) = fib (n + 3) :=
  a_odd_of_inv n hn (inv_terms n hn)

/-- `b i = 2i F(i+3) - (2i-1) F(i+2)` over `ℤ`. -/
theorem b_eq_int (i : ℕ) :
    (b i : ℤ) = (2 * i : ℤ) * fib (i + 3) - ((2 * i : ℤ) - 1) * fib (i + 2) := by
  have h : fib (i + 3) = fib (i + 1) + fib (i + 2) := fib_add_two
  unfold b
  rw [h]; push_cast; ring

/-- **Fried's refined form, even case.** For even `n ≥ 10`,
`a(n) = n F(n/2+3) - (n-1) F(n/2+2)`. -/
theorem a_even_fried (n : ℕ) (hn : 10 ≤ n) (he : Even n) :
    (a n : ℤ) = (n : ℤ) * fib (n / 2 + 3) - ((n : ℤ) - 1) * fib (n / 2 + 2) := by
  obtain ⟨j, rfl⟩ := he
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : (k + 1 + (k + 1)) / 2 = k + 1 := by omega
  rw [show k + 1 + (k + 1) = 2 * k + 2 by ring, a_even_closed k (by omega), b_eq_int,
    show (2 * k + 2) / 2 = k + 1 by omega]
  push_cast; ring

/-- **Fried's refined form, odd case.** For odd `n ≥ 10`, `a(n) = F((n+1)/2+2)`. -/
theorem a_odd_fried (n : ℕ) (hn : 10 ≤ n) (ho : Odd n) : a n = fib ((n + 1) / 2 + 2) := by
  obtain ⟨j, rfl⟩ := ho
  rw [a_two_mul_add_one j (by omega), show (2 * j + 1 + 1) / 2 = j + 1 by omega]

/-- **Conjecture (Colin Barker, Oct 19 2014), proved.**
For `n > 17`, `a(n) = 2 a(n-2) + a(n-4) - 2 a(n-6) - a(n-8)`. -/
theorem a_recurrence (n : ℕ) (hn : 17 < n) :
    (a n : ℤ) = 2 * a (n - 2) + a (n - 4) - 2 * a (n - 6) - a (n - 8) := by
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 5 := ⟨j - 5, by omega⟩
    rw [show t + 5 + (t + 5) = 2 * (t + 4) + 2 by ring,
      show 2 * (t + 4) + 2 - 2 = 2 * (t + 3) + 2 by omega,
      show 2 * (t + 4) + 2 - 4 = 2 * (t + 2) + 2 by omega,
      show 2 * (t + 4) + 2 - 6 = 2 * (t + 1) + 2 by omega,
      show 2 * (t + 4) + 2 - 8 = 2 * t + 2 by omega,
      a_even_closed _ (by omega), a_even_closed _ (by omega), a_even_closed _ (by omega),
      a_even_closed _ (by omega), a_even_closed _ (by omega)]
    have h3 : fib (t + 3) = fib (t + 1) + fib (t + 2) := fib_add_two
    have h4 : fib (t + 4) = fib (t + 2) + fib (t + 3) := fib_add_two
    have h5 : fib (t + 5) = fib (t + 3) + fib (t + 4) := fib_add_two
    have h6 : fib (t + 6) = fib (t + 4) + fib (t + 5) := fib_add_two
    have h7 : fib (t + 7) = fib (t + 5) + fib (t + 6) := fib_add_two
    simp only [b]
    rw [show t + 4 + 1 + 2 = t + 7 by ring, show t + 4 + 1 + 1 = t + 6 by ring,
      show t + 3 + 1 + 2 = t + 6 by ring, show t + 3 + 1 + 1 = t + 5 by ring,
      show t + 2 + 1 + 2 = t + 5 by ring, show t + 2 + 1 + 1 = t + 4 by ring,
      show t + 1 + 1 + 2 = t + 4 by ring, show t + 1 + 1 + 1 = t + 3 by ring,
      show t + 1 + 2 = t + 3 by ring, h7, h6, h5, h4, h3]
    push_cast; ring
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 9 := ⟨j - 9, by omega⟩
    rw [show 2 * (t + 9) + 1 - 2 = 2 * (t + 8) + 1 by omega,
      show 2 * (t + 9) + 1 - 4 = 2 * (t + 7) + 1 by omega,
      show 2 * (t + 9) + 1 - 6 = 2 * (t + 6) + 1 by omega,
      show 2 * (t + 9) + 1 - 8 = 2 * (t + 5) + 1 by omega,
      a_two_mul_add_one _ (by omega), a_two_mul_add_one _ (by omega),
      a_two_mul_add_one _ (by omega), a_two_mul_add_one _ (by omega),
      a_two_mul_add_one _ (by omega)]
    have h3 : fib (t + 10) = fib (t + 8) + fib (t + 9) := fib_add_two
    have h4 : fib (t + 11) = fib (t + 9) + fib (t + 10) := fib_add_two
    have h5 : fib (t + 12) = fib (t + 10) + fib (t + 11) := fib_add_two
    rw [show t + 9 + 3 = t + 12 by ring, show t + 8 + 3 = t + 11 by ring,
      show t + 7 + 3 = t + 10 by ring, show t + 6 + 3 = t + 9 by ring,
      show t + 5 + 3 = t + 8 by ring, h5, h4, h3]
    push_cast; ring

/-! ## Further ground truth from the closed forms -/

example : a 11 = 21 := by rw [show 11 = 2 * 5 + 1 by rfl, a_two_mul_add_one 5 (by norm_num)]; decide
example : a 12 = 177 := by rw [show 12 = 2 * 5 + 2 by rfl, a_even_closed 5 (by norm_num)]; decide
example : a 18 = 1079 := by rw [show 18 = 2 * 8 + 2 by rfl, a_even_closed 8 (by norm_num)]; decide
example : a 51 = 317811 := by
  rw [show 51 = 2 * 25 + 1 by rfl, a_two_mul_add_one 25 (by norm_num)]; decide
example : a 50 = 6266068 := by
  rw [show 50 = 2 * 24 + 2 by rfl, a_even_closed 24 (by norm_num)]; decide

end Candidates.A248982GreedyDistinctLeast
