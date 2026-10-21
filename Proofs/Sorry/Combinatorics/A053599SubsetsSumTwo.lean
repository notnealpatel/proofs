/-
# A053599 — Kimberling: subsets whose two least elements outsum the maximum

## OEIS source (retrieved with `oeis show A053599`, 2026-10-21)

```
NAME:     Number of nonempty subsequences {s(k)} of 1..n such that the
          difference sequence is palindromic.
TERMS:    1,3,7,13,23,37,59,89,135,197,291,417,607,861,1243,1753,2519,3541,
          5075,7121,10191,14285,20427,28617,40903,57285,81859,114625,...
KEYWORDS: nonn,easy
OFFSET:   a(1) = 1
FORMULA:  a(1)=1, a(2)=3 and, for n > 2, a(n) = 2*a(n-2) + 2*n - 1.
FORMULA:  a(n) = 5*2^((n+1)/2) - 2*n - 7 for odd n, 7*2^(n/2) - 2*n - 7 for
          even n. - _Andrew Woods_, May 19 2012
COMMENT (the conjecture):
  Conjecture:  let b(n) be the number of subsets S of {1,2,...,n} having more
  than one element such that (sum of least two elements of S) > max(S).  Then
  b(0) = b(1) = 0 and b(n+2) = a(n+1) for n >= 0. - _Clark Kimberling_
  Sep 27 2022
```

## Status

Triage status: open (no proof in the entry or the literature as far as the
triage could tell).  This module proves it: `kimberling_b_add_two_eq` below is
sorry-free.

## Definitional-fidelity note

`b` is the literal subset count of the comment: subsets `S ⊆ {1, …, n}` with
`2 ≤ |S|` and `max S < least S + secondLeast S`.  The sequence `a` is the
entry's closed form (Woods' FORMULA line) over `ℤ`, which is how the triage
statement phrases the conjecture; the NAME-line definition (palindromic
difference sequences) is not formalized here.  The ground-truth examples check
the closed form against the first twelve DATA terms, and `a053599_add_two`
proves the entry's recurrence for it.

## Proof

Fixing the two least elements `x < y` of `S ⊆ {1, …, n + 2}`, the rest of `S`
is an arbitrary subset of `(y, min (n + 2) (x + y - 1)]`.  Writing
`x = i + 1`, `y = n + 2 - j` with `i + j ≤ n`, that window has `min i j`
elements, so `b (n + 2) = ∑_{i + j ≤ n} 2 ^ min i j`.  Splitting off the axes
`i = 0`, `j = 0` and shifting the rest gives the recurrence
`h (n + 2) = 2 h n + 2 n + 5`, which matches the entry's recurrence.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A053599SubsetsSumTwo

open Finset

/-! ## Definition layer -/

/-- A finite set of naturals with at least two elements is nonempty. -/
theorem nonempty_of_two_le_card {S : Finset ℕ} (h : 2 ≤ S.card) : S.Nonempty :=
  Finset.card_pos.mp (by omega)

/-- Removing the least element of a set with at least two elements leaves a
nonempty set. -/
theorem erase_min'_nonempty {S : Finset ℕ} (h : 2 ≤ S.card) :
    (S.erase (S.min' (nonempty_of_two_le_card h))).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]
  omega

/-- The least element of a finite set of naturals with at least two elements. -/
def least (S : Finset ℕ) (h : 2 ≤ S.card) : ℕ := S.min' (nonempty_of_two_le_card h)

/-- The second least element of a finite set of naturals with at least two
elements: the least element after the least one is removed. -/
def secondLeast (S : Finset ℕ) (h : 2 ≤ S.card) : ℕ :=
  (S.erase (least S h)).min' (erase_min'_nonempty h)

/-- The greatest element `max(S)` of a finite set of naturals with at least two
elements. -/
def greatest (S : Finset ℕ) (h : 2 ≤ S.card) : ℕ := S.max' (nonempty_of_two_le_card h)

/-- Kimberling's predicate: `S` has more than one element and the sum of its
two least elements exceeds `max(S)`. -/
def IsKimberling (S : Finset ℕ) : Prop :=
  ∃ h : 2 ≤ S.card, greatest S h < least S h + secondLeast S h

instance : DecidablePred IsKimberling := fun S => by
  unfold IsKimberling; infer_instance

/-- `b n`: the number of subsets `S` of `{1, …, n}` having more than one
element such that (sum of the least two elements of `S`) `> max(S)`. -/
def b (n : ℕ) : ℕ := ((Icc 1 n).powerset.filter IsKimberling).card

/-- A053599 via the entry's closed form (Andrew Woods, May 19 2012):
`a(n) = 5*2^((n+1)/2) - 2n - 7` for odd `n`, `7*2^(n/2) - 2n - 7` for even `n`,
computed in `ℤ` so that no subtraction is truncated. -/
def a053599 (n : ℕ) : ℤ :=
  if n % 2 = 1 then 5 * 2 ^ ((n + 1) / 2) - 2 * n - 7 else 7 * 2 ^ (n / 2) - 2 * n - 7

/-! ## Ground truth -/

-- Satisfiability: `{1, 2}` is a Kimberling set (`1 + 2 > 2`), `{1, 2, 3}` is
-- not (`1 + 2 = 3`), and a singleton is not (fewer than two elements).
example : IsKimberling {1, 2} := by decide
example : ¬ IsKimberling {1, 2, 3} := by decide
example : ¬ IsKimberling {5} := by decide

-- Kimberling's boundary values `b(0) = b(1) = 0`, and the first values of `b`
-- against `a(1), …, a(6) = 1, 3, 7, 13, 23, 37` (brute force over subsets).
example : b 0 = 0 := by decide
example : b 1 = 0 := by decide
example : b 2 = 1 := by decide
example : b 3 = 3 := by decide
example : b 4 = 7 := by decide
example : b 5 = 13 := by decide
example : b 6 = 23 := by decide
example : b 7 = 37 := by decide

-- The closed form reproduces the first twelve DATA terms of A053599.
example : (List.range 12).map (fun n => a053599 (n + 1)) =
    [1, 3, 7, 13, 23, 37, 59, 89, 135, 197, 291, 417] := by decide

/-! ## Structure of a Kimberling set -/

/-- A `min'` is determined by membership and minimality. -/
theorem min'_eq_of_mem {T : Finset ℕ} (hT : T.Nonempty) {y : ℕ} (hy : y ∈ T)
    (hle : ∀ z ∈ T, y ≤ z) : T.min' hT = y :=
  le_antisymm (Finset.min'_le _ _ hy) (Finset.le_min' _ _ _ hle)

section Structure

variable {x y : ℕ} {R : Finset ℕ}

/-- If `x < y < R`, then `x ∉ insert y R`. -/
theorem not_mem_insert_of_lt (hxy : x < y) (hR : ∀ r ∈ R, y < r) : x ∉ insert y R := by
  intro hx
  rcases Finset.mem_insert.mp hx with hxy' | hxR
  · omega
  · have hyx := hR x hxR
    omega

/-- If `x < y < R`, then `insert x (insert y R)` has at least two elements. -/
theorem two_le_card_insert_insert (hxy : x < y) (hR : ∀ r ∈ R, y < r) :
    2 ≤ (insert x (insert y R)).card := by
  have hy : y ∉ R := fun hyR => lt_irrefl _ (hR y hyR)
  rw [card_insert_of_notMem (not_mem_insert_of_lt hxy hR), card_insert_of_notMem hy]
  omega

/-- If `x < y < R`, the least element of `insert x (insert y R)` is `x`. -/
theorem least_insert_insert (hxy : x < y) (hR : ∀ r ∈ R, y < r)
    (h : 2 ≤ (insert x (insert y R)).card) : least (insert x (insert y R)) h = x := by
  apply min'_eq_of_mem _ (mem_insert_self _ _)
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact le_rfl
  rcases Finset.mem_insert.mp hz with rfl | hz
  · omega
  · have hyz := hR z hz
    omega

/-- If `x < y < R`, the second least element of `insert x (insert y R)` is
`y`. -/
theorem secondLeast_insert_insert (hxy : x < y) (hR : ∀ r ∈ R, y < r)
    (h : 2 ≤ (insert x (insert y R)).card) :
    secondLeast (insert x (insert y R)) h = y := by
  have herase :
      (insert x (insert y R)).erase (least (insert x (insert y R)) h) = insert y R := by
    rw [least_insert_insert hxy hR h, erase_insert (not_mem_insert_of_lt hxy hR)]
  apply min'_eq_of_mem
  · rw [herase]
    exact mem_insert_self _ _
  · intro z hz
    rw [herase] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · have hyz := hR z hz
      omega

/-- For `x < y < R`, the set `insert x (insert y R)` is a Kimberling set iff
`0 < x` and every element of `R` is below `x + y`. -/
theorem isKimberling_insert_insert (hxy : x < y) (hR : ∀ r ∈ R, y < r) :
    IsKimberling (insert x (insert y R)) ↔ 0 < x ∧ ∀ r ∈ R, r < x + y := by
  constructor
  · rintro ⟨h, hlt⟩
    rw [least_insert_insert hxy hR h, secondLeast_insert_insert hxy hR h, greatest,
      max'_lt_iff] at hlt
    refine ⟨?_, fun r hr => hlt r (mem_insert_of_mem (mem_insert_of_mem hr))⟩
    have hy := hlt y (mem_insert_of_mem (mem_insert_self _ _))
    omega
  · rintro ⟨hx, hRlt⟩
    refine ⟨two_le_card_insert_insert hxy hR, ?_⟩
    rw [least_insert_insert hxy hR, secondLeast_insert_insert hxy hR, greatest, max'_lt_iff]
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · omega
    rcases Finset.mem_insert.mp hz with rfl | hz
    · omega
    · exact hRlt z hz

end Structure

/-- Every finite set of naturals with at least two elements is
`insert x (insert y R)` with `x < y < R` (its two least elements and the
rest). -/
theorem exists_eq_insert_insert {S : Finset ℕ} (h : 2 ≤ S.card) :
    ∃ x y : ℕ, ∃ R : Finset ℕ, x < y ∧ (∀ r ∈ R, y < r) ∧ S = insert x (insert y R) := by
  set x := least S h with hxdef
  set y := secondLeast S h with hydef
  have hxS : x ∈ S := Finset.min'_mem _ _
  have hyS' : y ∈ S.erase x := Finset.min'_mem _ _
  have hyx : y ≠ x := Finset.ne_of_mem_erase hyS'
  have hyS : y ∈ S := Finset.mem_of_mem_erase hyS'
  have hxy : x < y := lt_of_le_of_ne (Finset.min'_le _ _ hyS) (Ne.symm hyx)
  refine ⟨x, y, (S.erase x).erase y, hxy, ?_, ?_⟩
  · intro r hr
    have hr' : r ∈ S.erase x := Finset.mem_of_mem_erase hr
    have hry : r ≠ y := Finset.ne_of_mem_erase hr
    exact lt_of_le_of_ne (Finset.min'_le _ _ hr') (Ne.symm hry)
  · rw [insert_erase hyS', insert_erase hxS]

/-! ## Counting -/

/-- The index pairs `(i, j)` with `i + j ≤ n`; they encode the two least
elements `x = i + 1 < y = n + 2 - j` of a subset of `{1, …, n + 2}`. -/
def pairs (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (range (n + 1)).sigma (fun i => range (n + 1 - i))

/-- The window of admissible further elements `r` for least elements
`x = i + 1`, `y = n + 2 - j`: `y < r ≤ n + 2` and `r < x + y`. -/
def window (n i j : ℕ) : Finset ℕ :=
  (Ioc (n + 2 - j) (n + 2)).filter (· < (i + 1) + (n + 2 - j))

/-- The window is an interval of length `min i j`. -/
theorem window_eq {n i j : ℕ} (hij : i + j ≤ n) :
    window n i j = Ioc (n + 2 - j) (n + 2 - j + min i j) := by
  ext r
  simp only [window, mem_filter, mem_Ioc]
  omega

/-- The window has `min i j` elements. -/
theorem card_window {n i j : ℕ} (hij : i + j ≤ n) : (window n i j).card = min i j := by
  rw [window_eq hij, Nat.card_Ioc]
  omega

/-- Membership in `pairs n`. -/
theorem mem_pairs {n : ℕ} {p : Σ _ : ℕ, ℕ} : p ∈ pairs n ↔ p.1 + p.2 ≤ n := by
  simp only [pairs, mem_sigma, mem_range]
  omega

/-- Bijection: Kimberling subsets of `{1, …, n + 2}` correspond to a pair
`(i, j)` with `i + j ≤ n` together with a subset of its window, via
`(i, j, R) ↦ {i + 1, n + 2 - j} ∪ R`. -/
theorem b_add_two_eq_card_sigma (n : ℕ) :
    b (n + 2) = ((pairs n).sigma (fun p => (window n p.1 p.2).powerset)).card := by
  symm
  unfold b
  refine Finset.card_bij (fun q _ => insert (q.1.1 + 1) (insert (n + 2 - q.1.2) q.2)) ?_ ?_ ?_
  · rintro ⟨⟨i, j⟩, R⟩ hq
    simp only [mem_sigma, mem_powerset] at hq
    obtain ⟨hp, hR⟩ := hq
    have hij : i + j ≤ n := mem_pairs.mp hp
    have hRw : ∀ r ∈ R, n + 2 - j < r ∧ r ≤ n + 2 ∧ r < (i + 1) + (n + 2 - j) := by
      intro r hr
      have hrw := hR hr
      simp only [window, mem_filter, mem_Ioc] at hrw
      omega
    have hxy : i + 1 < n + 2 - j := by omega
    have hRy : ∀ r ∈ R, n + 2 - j < r := fun r hr => (hRw r hr).1
    simp only [mem_filter, mem_powerset]
    refine ⟨?_, (isKimberling_insert_insert hxy hRy).mpr
      ⟨by omega, fun r hr => (hRw r hr).2.2⟩⟩
    intro z hz
    simp only [mem_insert, mem_Icc] at hz ⊢
    rcases hz with rfl | rfl | hz
    · omega
    · omega
    · have hzw := hRw z hz
      omega
  · rintro ⟨⟨i, j⟩, R⟩ hq ⟨⟨i', j'⟩, R'⟩ hq' heq
    simp only [mem_sigma, mem_powerset] at hq hq'
    have hij : i + j ≤ n := mem_pairs.mp hq.1
    have hij' : i' + j' ≤ n := mem_pairs.mp hq'.1
    have hRy : ∀ r ∈ R, n + 2 - j < r := by
      intro r hr
      have hrw := hq.2 hr
      simp only [window, mem_filter, mem_Ioc] at hrw
      omega
    have hRy' : ∀ r ∈ R', n + 2 - j' < r := by
      intro r hr
      have hrw := hq'.2 hr
      simp only [window, mem_filter, mem_Ioc] at hrw
      omega
    have hxy : i + 1 < n + 2 - j := by omega
    have hxy' : i' + 1 < n + 2 - j' := by omega
    simp only at heq
    have h2 := two_le_card_insert_insert hxy hRy
    have h2' := two_le_card_insert_insert hxy' hRy'
    have hl := least_insert_insert hxy hRy h2
    have hs := secondLeast_insert_insert hxy hRy h2
    have hl' := least_insert_insert hxy' hRy' h2'
    have hs' := secondLeast_insert_insert hxy' hRy' h2'
    have hi : i = i' := by
      have hleq : least (insert (i + 1) (insert (n + 2 - j) R)) h2 =
          least (insert (i' + 1) (insert (n + 2 - j') R')) h2' := by
        simp only [least, heq]
      omega
    have hj : j = j' := by
      have hseq : secondLeast (insert (i + 1) (insert (n + 2 - j) R)) h2 =
          secondLeast (insert (i' + 1) (insert (n + 2 - j') R')) h2' := by
        simp only [secondLeast, least, heq]
      omega
    subst hi hj
    have hR : R = R' := by
      have e1 := congrArg (fun S => (S.erase (i + 1)).erase (n + 2 - j)) heq
      have hyR : n + 2 - j ∉ R := fun hmem => lt_irrefl _ (hRy _ hmem)
      have hyR' : n + 2 - j ∉ R' := fun hmem => lt_irrefl _ (hRy' _ hmem)
      simp only [erase_insert (not_mem_insert_of_lt hxy hRy),
        erase_insert (not_mem_insert_of_lt hxy hRy'), erase_insert hyR, erase_insert hyR'] at e1
      exact e1
    subst hR
    rfl
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    obtain ⟨hsub, hK⟩ := hS
    obtain ⟨x, y, R, hxy, hRy, rfl⟩ := exists_eq_insert_insert hK.1
    obtain ⟨hx0, hRlt⟩ := (isKimberling_insert_insert hxy hRy).mp hK
    have hyle : y ≤ n + 2 := by
      have hyI := hsub (mem_insert_of_mem (mem_insert_self _ _))
      simp only [mem_Icc] at hyI
      omega
    have hRle : ∀ r ∈ R, r ≤ n + 2 := by
      intro r hr
      have hrI := hsub (mem_insert_of_mem (mem_insert_of_mem hr))
      simp only [mem_Icc] at hrI
      omega
    refine ⟨⟨⟨x - 1, n + 2 - y⟩, R⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_powerset]
      refine ⟨mem_pairs.mpr (by simp only; omega), ?_⟩
      intro r hr
      simp only [window, mem_filter, mem_Ioc]
      have h1 := hRy r hr
      have h2 := hRlt r hr
      have h3 := hRle r hr
      omega
    · simp only
      have e1 : x - 1 + 1 = x := by omega
      have e2 : n + 2 - (n + 2 - y) = y := by omega
      rw [e1, e2]

/-- The weighted lattice-point sum `∑_{i + j ≤ n} 2 ^ min i j`. -/
def diagSum (n : ℕ) : ℕ := ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i), 2 ^ min i j

/-- `b (n + 2) = ∑_{i + j ≤ n} 2 ^ min i j`. -/
theorem b_add_two_eq_diagSum (n : ℕ) : b (n + 2) = diagSum n := by
  rw [b_add_two_eq_card_sigma, card_sigma, pairs, sum_sigma, diagSum]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  dsimp only
  rw [card_powerset, card_window (by omega)]

/-- The recurrence `diagSum (n + 2) = 2 * diagSum n + 2 n + 5`: the axis terms
`i = 0` or `j = 0` contribute `2 n + 5`, and the shift `(i, j) ↦ (i + 1, j + 1)`
doubles the rest. -/
theorem diagSum_add_two (n : ℕ) : diagSum (n + 2) = 2 * diagSum n + 2 * n + 5 := by
  have hinner : ∀ i ∈ range (n + 2),
      (∑ j ∈ range (n + 2 + 1 - (i + 1)), 2 ^ min (i + 1) j) =
        2 * (∑ j ∈ range (n + 1 - i), 2 ^ min i j) + 1 := by
    intro i hi
    have hi' : i < n + 2 := mem_range.mp hi
    rw [show n + 2 + 1 - (i + 1) = (n + 1 - i) + 1 by omega, sum_range_succ', mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show min (i + 1) (j + 1) = min i j + 1 by omega, pow_succ]
    ring
  unfold diagSum
  rw [sum_range_succ', sum_congr rfl hinner, sum_range_succ]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, smul_eq_mul, mul_one, tsub_self,
    range_zero, sum_empty, mul_zero, zero_add, tsub_zero, zero_le, inf_of_le_left, pow_zero]
  ring

/-- The entry's recurrence `a(n) = 2 a(n-2) + 2 n - 1` holds for the closed
form, stated as `a(n + 2) = 2 a(n) + 2 (n + 2) - 1` (valid for every `n`). -/
theorem a053599_add_two (n : ℕ) :
    a053599 (n + 2) = 2 * a053599 n + 2 * ((n + 2 : ℕ) : ℤ) - 1 := by
  unfold a053599
  have hmod : (n + 2) % 2 = n % 2 := by omega
  rw [hmod]
  split_ifs with hn
  · rw [show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega, pow_succ]
    push_cast
    ring
  · rw [show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ]
    push_cast
    ring

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A053599, Clark Kimberling, Sep 27 2022).**

Verbatim: "let b(n) be the number of subsets S of {1,2,...,n} having more than
one element such that (sum of least two elements of S) > max(S).  Then
b(0) = b(1) = 0 and b(n+2) = a(n+1) for n >= 0."

Here `a = A053599` is given by the entry's closed form
`a(n) = 5*2^((n+1)/2) - 2n - 7` (odd `n`), `7*2^(n/2) - 2n - 7` (even `n`).
The boundary values `b 0 = b 1 = 0` are checked by `decide` above.  Proof:
`b (n + 2) = ∑_{i + j ≤ n} 2 ^ min i j` (`b_add_two_eq_diagSum`), and both
sides satisfy the same second-order recurrence with the same initial values. -/
theorem kimberling_b_add_two_eq (n : ℕ) : (b (n + 2) : ℤ) = a053599 (n + 1) := by
  rw [b_add_two_eq_diagSum]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | m + 2, ih =>
      rw [diagSum_add_two, a053599_add_two, ← ih m (by omega)]
      push_cast
      ring

end Candidates.A053599SubsetsSumTwo
