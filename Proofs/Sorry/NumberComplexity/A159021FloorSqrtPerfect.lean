/-
# A159021 — Librandi: the squares in `a(n+1) = a(n) + ⌊√a(n)⌋`, `a(0) = 19`, are `(7·2^k)^2`

## OEIS source (retrieved with `oeis show A159021`, 2026-10-21)

```
NAME:     a(0)=19; a(n) = a(n-1) + floor(sqrt(a(n-1))), n > 0.
TERMS:    19,23,27,32,37,43,49,56,63,70,78,86,95,104,114,124,135,146,158,
          170,183,196,210,224,238,253,268,284,300,317,334,352,370,389,408,
          428,448,469,490,512,534,557,580,604,628,653,678,704,730,757,784,
          812,840,868,897,926,956,986,1017
COMMENT:  Row 3 in square array A159016.
COMMENT:  This sequence contains infinitely many squares.
          - _Philippe Deléham_, Apr 04 2009
COMMENT (the conjecture):
  Conjecture: The squares are of the form (7*2^k)^2 (see A005009).
  - _Vincenzo Librandi_, Apr 10 2009
PROGRAM:  NestList[#+Floor[Sqrt[#]]&,19,60] (* _Harvey P. Dale_, Jan 04 2013 *)
```

Formulation used here (from the triage card): for all `n`, `a(n)` is a
perfect square iff `a(n) = (7*2^k)^2` for some `k ≥ 0`.  Equivalently, the
squares in the sequence are exactly `49*4^k`, and every such value occurs.

## Status

Triage: "open" (no proof in the entry, which only has the comments by
Deléham and Librandi; the same mechanism is stated without proof in the
sibling entries A002984, A159018, A159020, A159022–A159027).  The mechanism
is olympiad folklore, so the statement is unlikely to be new.  Proved below
in full (no `sorry`).

Computation (python, 2026-10-21): the first 2·10^6 terms contain exactly 18
squares, `(7·2^k)^2` for `k = 0..17`, at indices `6, 21, 50, 107, …`, with
index gaps `2·(7·2^k) + 1`.

## Proof

Write `x = K^2 + s` with `0 ≤ s ≤ 2K`, so `⌊√x⌋ = K`.  From `K^2 + (r+1)`
with `r + 1 ≤ K` two steps reach `(K+1)^2 + r`, and neither term is a
square.  From a square `m^2 = (c+1)^2` the terms are `m^2`, `m^2 + m`,
`(m+1)^2 - 1`, `(m+1)^2 + (m-1)`, after which the residue falls by one per
block and vanishes exactly at block `2m`.  So the next square after `m^2` is
`(2m)^2`, reached `2m + 1` steps later.  Starting from `a(6) = 49 = 7^2` and
checking `a(0..5)` directly gives the claim.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A159021FloorSqrtPerfect

/-! ## Definition layer -/

/-- OEIS A159021: `a(0) = 19`, `a(n+1) = a(n) + ⌊√a(n)⌋`.  `Nat.sqrt` is the
floor of the real square root on `ℕ`, so this mirrors the entry exactly. -/
def a : ℕ → ℕ
  | 0 => 19
  | n + 1 => a n + Nat.sqrt (a n)

/-- The index of the `k`-th square `(7*2^k)^2` in A159021: `6`, and then the
gap after the square `m^2` is `2m + 1`. -/
def squareIndex : ℕ → ℕ
  | 0 => 6
  | k + 1 => squareIndex k + (2 * (7 * 2 ^ k) + 1)

-- Ground truth: the first listed terms of the OEIS DATA line.
example : a 0 = 19 ∧ a 1 = 23 ∧ a 2 = 27 ∧ a 3 = 32 ∧ a 4 = 37 ∧ a 5 = 43 ∧
    a 6 = 49 ∧ a 7 = 56 ∧ a 8 = 63 ∧ a 9 = 70 ∧ a 21 = 196 := by
  decide +kernel

-- Ground truth: the last listed term, `a(58) = 1017`.
example : a 58 = 1017 := by decide +kernel

-- Ground truth: the square indices `6, 21, 50` match the computation.
example : squareIndex 0 = 6 ∧ squareIndex 1 = 21 ∧ squareIndex 2 = 50 := by decide

/-! ## Block arithmetic -/

/-- If `s ≤ 2K` then `⌊√(K^2 + s)⌋ = K`. -/
theorem sqrt_sq_add (K s : ℕ) (hs : s ≤ 2 * K) : Nat.sqrt (K ^ 2 + s) = K := by
  rw [sq]
  exact Nat.sqrt_add_eq K (by omega)

/-- A number strictly between `K^2` and `(K+1)^2` is not a square. -/
theorem not_isSquare_sq_add (K s : ℕ) (h1 : 0 < s) (h2 : s ≤ 2 * K) :
    ¬ IsSquare (K ^ 2 + s) := by
  rintro ⟨t, ht⟩
  have hlo : K * K < K ^ 2 + s := by nlinarith
  have hhi : K ^ 2 + s < (K + 1) * (K + 1) := by nlinarith
  exact Nat.not_exists_sq hlo hhi ⟨t, ht.symm⟩

/-- One step of the recursion inside block `K`. -/
theorem a_succ_of_eq (n K s : ℕ) (h : a n = K ^ 2 + s) (hs : s ≤ 2 * K) :
    a (n + 1) = K ^ 2 + (s + K) := by
  show a n + Nat.sqrt (a n) = _
  rw [h, sqrt_sq_add K s hs]
  ring

/-- **Residue descent.**  If `a n = K^2 + (r + j)` with `r + j ≤ K`, then after
`2j` steps the sequence is at `(K + j)^2 + r`, and none of the `2j` terms
`a n, …, a (n + 2j - 1)` is a square. -/
theorem descent (j : ℕ) : ∀ n K r : ℕ, a n = K ^ 2 + (r + j) → r + j ≤ K →
    a (n + 2 * j) = (K + j) ^ 2 + r ∧ ∀ i < 2 * j, ¬ IsSquare (a (n + i)) := by
  induction j with
  | zero =>
    intro n K r h _
    refine ⟨by simpa using h, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    intro n K r h hle
    have h1 : a (n + 1) = K ^ 2 + (r + (j + 1) + K) :=
      a_succ_of_eq n K _ h (by omega)
    have h2 : a (n + 1 + 1) = (K + 1) ^ 2 + (r + j) := by
      rw [a_succ_of_eq (n + 1) K _ h1 (by omega)]
      ring
    obtain ⟨hend, hmid⟩ := ih (n + 2) (K + 1) r h2 (by omega)
    refine ⟨?_, ?_⟩
    · have hidx : n + 2 * (j + 1) = n + 2 + 2 * j := by ring
      rw [hidx, hend]
      ring
    · intro i hi
      rcases i with _ | _ | i
      · rw [Nat.add_zero, h]
        exact not_isSquare_sq_add K _ (by omega) (by omega)
      · rw [h1]
        exact not_isSquare_sq_add K _ (by omega) (by omega)
      · have hidx : n + (i + 1 + 1) = n + 2 + i := by ring
        rw [hidx]
        exact hmid i (by omega)

/-- **Next square.**  If `a n = m^2` with `0 < m`, then `a (n + 2m + 1) = (2m)^2`
and no term strictly between is a square. -/
theorem next_square (n m : ℕ) (hm : 0 < m) (h : a n = m ^ 2) :
    a (n + (2 * m + 1)) = (2 * m) ^ 2 ∧
      ∀ i, 0 < i → i < 2 * m + 1 → ¬ IsSquare (a (n + i)) := by
  obtain ⟨c, rfl⟩ : ∃ c, m = c + 1 := ⟨m - 1, by omega⟩
  have h1 : a (n + 1) = (c + 1) ^ 2 + (0 + (c + 1)) :=
    a_succ_of_eq n (c + 1) 0 (by simpa using h) (by omega)
  have h2 : a (n + 1 + 1) = (c + 1) ^ 2 + (0 + (c + 1) + (c + 1)) :=
    a_succ_of_eq (n + 1) (c + 1) _ h1 (by omega)
  have h3 : a (n + 1 + 1 + 1) = (c + 2) ^ 2 + (0 + c) := by
    have h2' : a (n + 1 + 1) = (c + 1) ^ 2 + (2 * c + 2) := by
      rw [h2]
      ring
    rw [a_succ_of_eq (n + 1 + 1) (c + 1) _ h2' (by omega)]
    ring
  obtain ⟨hend, hmid⟩ := descent c (n + 3) (c + 2) 0 h3 (by omega)
  refine ⟨?_, ?_⟩
  · have hidx : n + (2 * (c + 1) + 1) = n + 3 + 2 * c := by ring
    rw [hidx, hend]
    ring
  · intro i hi0 hi
    rcases i with _ | _ | _ | i
    · exact absurd hi0 (lt_irrefl 0)
    · rw [h1]
      exact not_isSquare_sq_add (c + 1) _ (by omega) (by omega)
    · rw [h2]
      exact not_isSquare_sq_add (c + 1) _ (by omega) (by omega)
    · have hidx : n + (i + 1 + 1 + 1) = n + 3 + i := by ring
      rw [hidx]
      exact hmid i (by omega)

/-! ## The squares of A159021 -/

/-- The initial segment of A159021 in block form:
`19 = 4^2 + 3`, `23 = 4^2 + 7`, `27 = 5^2 + 2`, `32 = 5^2 + 7`, `37 = 6^2 + 1`,
`43 = 6^2 + 7`, and `a 6 = 49 = 7^2`. -/
theorem a_initial : a 0 = 4 ^ 2 + 3 ∧ a 1 = 4 ^ 2 + 7 ∧ a 2 = 5 ^ 2 + 2 ∧
    a 3 = 5 ^ 2 + 7 ∧ a 4 = 6 ^ 2 + 1 ∧ a 5 = 6 ^ 2 + 7 ∧ a 6 = 7 ^ 2 := by
  have h0 : a 0 = 4 ^ 2 + 3 := rfl
  have h1 : a 1 = 4 ^ 2 + 7 := a_succ_of_eq 0 4 3 h0 (by norm_num)
  have h2 : a 2 = 5 ^ 2 + 2 := by
    rw [a_succ_of_eq 1 4 7 h1 (by norm_num)]
    norm_num
  have h3 : a 3 = 5 ^ 2 + 7 := a_succ_of_eq 2 5 2 h2 (by norm_num)
  have h4 : a 4 = 6 ^ 2 + 1 := by
    rw [a_succ_of_eq 3 5 7 h3 (by norm_num)]
    norm_num
  have h5 : a 5 = 6 ^ 2 + 7 := a_succ_of_eq 4 6 1 h4 (by norm_num)
  have h6 : a 6 = 7 ^ 2 := by
    rw [a_succ_of_eq 5 6 7 h5 (by norm_num)]
    norm_num
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- The initial segment `a 0, …, a 5 = 19, 23, 27, 32, 37, 43` has no square. -/
theorem not_isSquare_a_of_lt_six : ∀ n < 6, ¬ IsSquare (a n) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := a_initial
  intro n hn
  interval_cases n
  · rw [h0]; exact not_isSquare_sq_add 4 3 (by norm_num) (by norm_num)
  · rw [h1]; exact not_isSquare_sq_add 4 7 (by norm_num) (by norm_num)
  · rw [h2]; exact not_isSquare_sq_add 5 2 (by norm_num) (by norm_num)
  · rw [h3]; exact not_isSquare_sq_add 5 7 (by norm_num) (by norm_num)
  · rw [h4]; exact not_isSquare_sq_add 6 1 (by norm_num) (by norm_num)
  · rw [h5]; exact not_isSquare_sq_add 6 7 (by norm_num) (by norm_num)

/-- `a (squareIndex k) = (7 * 2^k)^2`; in particular every value `49 * 4^k`
occurs in A159021. -/
theorem a_squareIndex (k : ℕ) : a (squareIndex k) = (7 * 2 ^ k) ^ 2 := by
  induction k with
  | zero =>
    show a 6 = (7 * 2 ^ 0) ^ 2
    rw [a_initial.2.2.2.2.2.2]
    norm_num
  | succ k ih =>
    have hpos : 0 < 7 * 2 ^ k := by positivity
    show a (squareIndex k + (2 * (7 * 2 ^ k) + 1)) = _
    rw [(next_square (squareIndex k) (7 * 2 ^ k) hpos ih).1]
    ring

/-- `squareIndex` grows at least linearly, so every index lies below some
`squareIndex k`. -/
theorem lt_squareIndex (n : ℕ) : n < squareIndex n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show n + 1 < squareIndex n + (2 * (7 * 2 ^ n) + 1)
    omega

/-- Every square term with index below `squareIndex k` is `(7 * 2^j)^2` for some
`j`. -/
theorem exists_of_isSquare_of_lt (k : ℕ) :
    ∀ n < squareIndex k, IsSquare (a n) → ∃ j, a n = (7 * 2 ^ j) ^ 2 := by
  induction k with
  | zero =>
    intro n hn hsq
    exact absurd hsq (not_isSquare_a_of_lt_six n hn)
  | succ k ih =>
    intro n hn hsq
    by_cases hlt : n < squareIndex k
    · exact ih n hlt hsq
    · obtain ⟨i, rfl⟩ : ∃ i, n = squareIndex k + i := ⟨n - squareIndex k, by omega⟩
      have hi : i < 2 * (7 * 2 ^ k) + 1 := by
        have hn' : squareIndex k + i < squareIndex k + (2 * (7 * 2 ^ k) + 1) := hn
        omega
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · exact ⟨k, by rw [hi0, Nat.add_zero, a_squareIndex]⟩
      · have hpos : 0 < 7 * 2 ^ k := by positivity
        exact absurd hsq
          ((next_square (squareIndex k) (7 * 2 ^ k) hpos (a_squareIndex k)).2 i hi0 hi)

/-- **Librandi's conjecture (A159021, Vincenzo Librandi, Apr 10 2009).**

Verbatim: "Conjecture: The squares are of the form (7*2^k)^2 (see A005009)."

For `a(0) = 19`, `a(n+1) = a(n) + ⌊√a(n)⌋`, the term `a(n)` is a perfect square
iff `a(n) = (7*2^k)^2` for some `k ≥ 0`. -/
theorem isSquare_a_iff (n : ℕ) : IsSquare (a n) ↔ ∃ k, a n = (7 * 2 ^ k) ^ 2 := by
  constructor
  · exact exists_of_isSquare_of_lt n n (lt_squareIndex n)
  · rintro ⟨k, hk⟩
    exact ⟨7 * 2 ^ k, by rw [hk, sq]⟩

/-- **Every value `(7*2^k)^2` occurs** (this also proves Deléham's comment that
A159021 contains infinitely many squares). -/
theorem exists_a_eq (k : ℕ) : ∃ n, a n = (7 * 2 ^ k) ^ 2 :=
  ⟨squareIndex k, a_squareIndex k⟩

/-- **Equivalent set form.**  The set of square values taken by A159021 is
exactly `{(7*2^k)^2 : k ∈ ℕ} = {49 * 4^k : k ∈ ℕ}`. -/
theorem squares_eq_range :
    {x | (∃ n, a n = x) ∧ IsSquare x} = Set.range (fun k : ℕ => 49 * 4 ^ k) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  have hval (k : ℕ) : (7 * 2 ^ k) ^ 2 = 49 * 4 ^ k := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  constructor
  · rintro ⟨⟨n, rfl⟩, hsq⟩
    obtain ⟨k, hk⟩ := (isSquare_a_iff n).1 hsq
    exact ⟨k, by rw [hk, hval]⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨n, hn⟩ := exists_a_eq k
    refine ⟨⟨n, by rw [hn, hval]⟩, ⟨7 * 2 ^ k, by rw [← hval, sq]⟩⟩

end Candidates.A159021FloorSqrtPerfect
