import Mathlib

set_option autoImplicit false

/-!
# Palindromic rows of A267632

`T n k` counts the `k`-element subsets of `{1,…,n}` whose sum is divisible by
`n`; read as a triangle for `1 ≤ k ≤ n` this is OEIS A267632. An unattributed
OEIS comment observes (an "observation-conjecture") that the row with its last
entry removed, `(T n 1, …, T n (n-1))`, is a palindrome whenever `n` is odd or
`n` is a power of `2`; equivalently `T n k = T n (n - k)` for `1 ≤ k ≤ n - 1`
under those hypotheses.

This file proves the odd case (`T_symm_of_odd`): complementation
`S ↦ {1,…,n} \ S` bijects `k`-subsets with `(n-k)`-subsets and changes the sum
from `s` to `(1 + ⋯ + n) - s`, so it preserves divisibility by `n` exactly when
`n ∣ 1 + ⋯ + n`. For odd `n = 2m + 1` the total is `n * (m + 1)`, and the
symmetry follows — for every `k ≤ n`, in particular on the conjectured range.

The power-of-2 case is only stated (`T_symm_of_two_pow`), with an intended
`sorry`: for even `n` the total `n * (n+1) / 2` is not divisible by `n`, the
complement argument fails, and no proof is known. The plausible route is the
Ramanathan/Barnes formula
`T n k = (1/n) * ∑_{s ∣ gcd n k} (-1)^(k - k/s) * φ(s) * C(n/s, k/s)`.

Ground truth for all numeric checks: `oeis show A267632`, rows 1–12.
Vocabulary matches the sibling `Proofs/Enumerative/Zumkeller.lean`: subsets of
`Finset.range n` stand for subsets of `{1,…,n}` via the shift `i ↦ i + 1`.
-/

open Finset

namespace A267632

/-- The `k`-element subsets of `{1,…,n}` — encoded as subsets `S` of
`Finset.range n` via the shift `i ↦ i + 1` — whose shifted sum `∑ i ∈ S, (i+1)`
is divisible by `n`. -/
def rowSubsets (n k : ℕ) : Finset (Finset ℕ) :=
  (Finset.powersetCard k (Finset.range n)).filter (fun S => n ∣ S.sum (· + 1))

/-- Membership in `rowSubsets`, unfolded. -/
lemma mem_rowSubsets {n k : ℕ} {S : Finset ℕ} :
    S ∈ rowSubsets n k ↔ S ⊆ Finset.range n ∧ S.card = k ∧ n ∣ S.sum (· + 1) := by
  simp only [rowSubsets, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

-- Ground check: the only 2-subset of {1,2,3} with sum divisible by 3 is {1,2},
-- encoded as {0,1}.
example : rowSubsets 3 2 = {{0, 1}} := by decide

/-- `T n k` = number of `k`-element subsets of `{1,…,n}` with sum divisible by
`n`. For `1 ≤ k ≤ n` this is the triangle entry `T(n, k)` of OEIS A267632. -/
def T (n k : ℕ) : ℕ := (rowSubsets n k).card

-- Ground checks against `oeis show A267632`, rows 1–8 in full.
example : [T 1 1] = [1] := rfl
example : [T 2 1, T 2 2] = [1, 0] := rfl
example : [T 3 1, T 3 2, T 3 3] = [1, 1, 1] := rfl
example : [T 4 1, T 4 2, T 4 3, T 4 4] = [1, 1, 1, 0] := rfl
example : [T 5 1, T 5 2, T 5 3, T 5 4, T 5 5] = [1, 2, 2, 1, 1] := rfl
example : [T 6 1, T 6 2, T 6 3, T 6 4, T 6 5, T 6 6] = [1, 2, 4, 3, 1, 0] := rfl
example : [T 7 1, T 7 2, T 7 3, T 7 4, T 7 5, T 7 6, T 7 7] =
    [1, 3, 5, 5, 3, 1, 1] := rfl
set_option maxRecDepth 4000 in
example : [T 8 1, T 8 2, T 8 3, T 8 4, T 8 5, T 8 6, T 8 7, T 8 8] =
    [1, 3, 7, 9, 7, 3, 1, 0] := rfl

-- Boundary behavior outside the triangle: the empty set gives `T n 0 = 1`,
-- and `T n k = 0` when `n < k` (no `k`-subsets exist).
example : T 5 0 = 1 := rfl
example : T 5 6 = 0 := rfl

-- Negative controls (rows 6, 10, 12 of `oeis show A267632`): for even `n` not
-- a power of 2 the truncated row is NOT a palindrome, so the definition is not
-- accidentally symmetric.
example : T 6 2 = 2 ∧ T 6 4 = 3 := ⟨rfl, rfl⟩
set_option maxRecDepth 8000 in
example : T 10 2 = 4 ∧ T 10 8 = 5 := ⟨rfl, rfl⟩
set_option maxRecDepth 16000 in
example : T 12 4 = 42 ∧ T 12 8 = 43 := ⟨rfl, rfl⟩

/-- Gauss sum, multiplicatively: `2 * (1 + 2 + ⋯ + n) = n * (n + 1)`.
Stated with the factor `2` on the left so that no `Nat` division carries
content. -/
lemma two_mul_sum_range_add_one (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

-- Ground check: 2 * (1 + 2 + 3 + 4 + 5) = 30 = 5 * 6.
example : 2 * ∑ i ∈ Finset.range 5, (i + 1) = 5 * 6 := two_mul_sum_range_add_one 5

/-- For odd `n = 2m + 1` the total `1 + 2 + ⋯ + n` equals `n * (m + 1)`, so it
is divisible by `n`. This is the arithmetic fact behind the palindrome rows and
exactly what fails for even `n`. -/
lemma dvd_sum_range_add_one_of_odd {n : ℕ} (hn : Odd n) :
    n ∣ ∑ i ∈ Finset.range n, (i + 1) := by
  obtain ⟨m, rfl⟩ := hn
  refine ⟨m + 1, ?_⟩
  have h2 : 2 * ∑ i ∈ Finset.range (2 * m + 1), (i + 1) =
      2 * ((2 * m + 1) * (m + 1)) := by
    rw [two_mul_sum_range_add_one]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

-- Sharpness: divisibility of the total genuinely fails at even `n`
-- (`1 + ⋯ + 8 = 36` and `¬ 8 ∣ 36`), which is why the complement route below
-- does not reach the power-of-2 case.
example : ¬ (8 : ℕ) ∣ ∑ i ∈ Finset.range 8, (i + 1) := by decide

/-- Complementation inside `{1,…,n}`: if `n` divides the total `1 + ⋯ + n`,
then the complement `{1,…,n} \ S` of a set counted by `T n k` is counted by
`T n (n - k)`. -/
lemma sdiff_mem_rowSubsets {n : ℕ} (htot : n ∣ ∑ i ∈ Finset.range n, (i + 1))
    {k : ℕ} {S : Finset ℕ} (hS : S ∈ rowSubsets n k) :
    Finset.range n \ S ∈ rowSubsets n (n - k) := by
  obtain ⟨hsub, hcard, hdvd⟩ := mem_rowSubsets.mp hS
  refine mem_rowSubsets.mpr ⟨Finset.sdiff_subset, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard]
  · have hsplit : (∑ x ∈ Finset.range n \ S, (x + 1)) + ∑ x ∈ S, (x + 1) =
        ∑ x ∈ Finset.range n, (x + 1) := Finset.sum_sdiff hsub
    have htot' : n ∣ (∑ x ∈ S, (x + 1)) + ∑ x ∈ Finset.range n \ S, (x + 1) := by
      rw [add_comm, hsplit]; exact htot
    exact (Nat.dvd_add_right hdvd).mp htot'

/-- **Complement symmetry.** If `n` divides the total `1 + ⋯ + n`, then
complementation `S ↦ {1,…,n} \ S` is a bijection between the `k`-subsets and
the `(n-k)`-subsets of `{1,…,n}` with sum divisible by `n`, hence
`T n k = T n (n - k)` for every `k ≤ n`. -/
theorem T_symm_of_dvd_total {n : ℕ} (htot : n ∣ ∑ i ∈ Finset.range n, (i + 1))
    {k : ℕ} (hk : k ≤ n) :
    T n k = T n (n - k) := by
  show (rowSubsets n k).card = (rowSubsets n (n - k)).card
  refine Finset.card_bij' (fun S _ => Finset.range n \ S)
    (fun S _ => Finset.range n \ S)
    (fun S hS => sdiff_mem_rowSubsets htot hS)
    (fun S hS => ?_) (fun S hS => ?_) (fun S hS => ?_)
  · -- the complement maps the `(n-k)`-side back into the `k`-side
    have hmem : Finset.range n \ S ∈ rowSubsets n (n - (n - k)) :=
      sdiff_mem_rowSubsets htot hS
    rwa [Nat.sub_sub_self hk] at hmem
  · -- left inverse on the `k`-side
    exact Finset.sdiff_sdiff_eq_self (mem_rowSubsets.mp hS).1
  · -- right inverse on the `(n-k)`-side
    exact Finset.sdiff_sdiff_eq_self (mem_rowSubsets.mp hS).1

-- Satisfiability of `T_symm_of_dvd_total`: both hypotheses hold jointly at
-- `n = 5`, `k = 2`, where the conclusion instance `T 5 2 = T 5 3` is `2 = 2`.
example : T 5 2 = T 5 3 := T_symm_of_dvd_total (by decide) (by norm_num)

/-- **Odd case of the A267632 palindrome observation** (sorry-free). For odd
`n` and any `k ≤ n`, the number of `k`-element subsets of `{1,…,n}` with sum
divisible by `n` equals the number of `(n-k)`-element ones:
`T n k = T n (n - k)`. In particular the truncated row
`(T n 1, …, T n (n-1))` is a palindrome, which is the OEIS claim; for odd `n`
the symmetry extends to the endpoints `k = 0` and `k = n` as well. -/
theorem T_symm_of_odd {n : ℕ} (hn : Odd n) {k : ℕ} (hk : k ≤ n) :
    T n k = T n (n - k) :=
  T_symm_of_dvd_total (dvd_sum_range_add_one_of_odd hn) hk

-- Satisfiability of `T_symm_of_odd`: both hypotheses hold jointly at
-- `n = 7`, `k = 3`; the conclusion instance `T 7 3 = T 7 4` is `5 = 5`.
example : T 7 3 = T 7 4 := T_symm_of_odd (by decide) (by norm_num)

-- Ground check of the conclusion on the full truncated rows 5 and 7.
example : [T 5 1, T 5 2, T 5 3, T 5 4] = [T 5 4, T 5 3, T 5 2, T 5 1] := rfl
example : [T 7 1, T 7 2, T 7 3, T 7 4, T 7 5, T 7 6] =
    [T 7 6, T 7 5, T 7 4, T 7 3, T 7 2, T 7 1] := rfl

/-- **Power-of-2 case of the A267632 palindrome observation** (OPEN). For
`n = 2 ^ j` and `1 ≤ k < n`, conjecturally `T n k = T n (n - k)`, i.e. the
truncated row is a palindrome. The complement bijection of
`T_symm_of_dvd_total` fails here: `n` does not divide `1 + ⋯ + n` for even `n`
(see the sharpness example above). The bound `k < n` is necessary:
`T n n = 0 < 1 = T n 0` for even `n`. For `1 ≤ j` the hypotheses are jointly
satisfiable (e.g. `j = 3`, `k = 2`); for `j = 0` they are contradictory and the
odd case `T_symm_of_odd` covers `n = 1` instead. Ground-truth instances for
`j ≤ 3` are verified below. A plausible route is the Ramanathan/Barnes formula
`T n k = (1/n) * ∑_{s ∣ gcd n k} (-1)^(k - k/s) * φ(s) * C(n/s, k/s)` with
`s` ranging over powers of `2`, but this is unworked. -/
theorem T_symm_of_two_pow (j : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < 2 ^ j) :
    T (2 ^ j) k = T (2 ^ j) (2 ^ j - k) := by
  -- INTENDED SORRY: open conjecture (campaign HOLD tier); the complement
  -- argument fails for even `n` and the Gauss-sum route is unworked.
  sorry

-- Satisfiability of `T_symm_of_two_pow`: both hypotheses hold jointly at
-- `j = 3`, `k = 2`, and the conclusion instance `T 8 2 = T 8 6` is `3 = 3`.
example : 1 ≤ 2 ∧ 2 < 2 ^ 3 := by norm_num
example : T 8 2 = T 8 6 := rfl

-- Ground truth for `T_symm_of_two_pow` at `j = 1, 2, 3`: every conclusion
-- instance on the truncated rows 2, 4, 8 holds by computation.
example : [T 2 1] = [T 2 1] := rfl
example : [T 4 1, T 4 2, T 4 3] = [T 4 3, T 4 2, T 4 1] := rfl
example : [T 8 1, T 8 2, T 8 3, T 8 4, T 8 5, T 8 6, T 8 7] =
    [T 8 7, T 8 6, T 8 5, T 8 4, T 8 3, T 8 2, T 8 1] := rfl

-- Sharpness of `k < n` in the power-of-2 case: at `k = n` the symmetry fails
-- for even `n` (the OEIS row keeps its non-palindromic last entry).
set_option maxRecDepth 4000 in
example : T 8 8 = 0 ∧ T 8 0 = 1 := ⟨rfl, rfl⟩

end A267632
