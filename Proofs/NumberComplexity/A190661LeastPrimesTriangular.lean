/-
# A190661 — the last block of `n` primes between triangular numbers lies beyond `n`

## OEIS source (retrieved with `oeis show A190661` and https://oeis.org/A190661, 2026-10-21)

```
NAME:     a(n) is the least number m such that there are at least n primes in
          the range (T(k-1), T(k)] for all k >= m, where T(k) is the k-th
          triangular number.
OFFSET:   0,2
TERMS:    1,7,16,33,52,66,79,72,109,93,121,119,130,153,169,194,180,222,235,275,
          294,267,256,296,329,339,333,420,383,373,372,454,396,443,449,504,463,...
COMMENT:  All values and even whether the sequence is well defined are conjectural.
COMMENT:  a(n) is the conjectured index of the last occurrence of n in A066888.
COMMENT (the conjecture):
          It is conjectured that for every n >= 0, a(n) > n.
EXAMPLE:  Because it appears that A066888(7) = 1 is the last 1 of that
          sequence, a(1) = 7.
AUTHOR:   John W. Nicholson, May 18 2011 (edited by T. D. Noe, May 19 2011).
          The comment block carries no per-comment attribution, so the
          conjecture is attributed to the entry author.
```

A066888(k) = pi(T(k)) - pi(T(k-1)) is the number of primes `p` with
`T(k-1) < p ≤ T(k)` (offset 1; terms `0,2,1,1,2,2,1,2,3,…`).

## Status

Triage: "open" as an OEIS comment, but only because `a(n)` itself may be
undefined (that `n` occurs in A066888 only finitely often, and at all, is a
Legendre-type problem).  Whenever `a(n)` exists, `a(n) > n` is elementary.
This file proves it for both readings of the entry, sorry-free.

## Definitional-fidelity note (load-bearing)

The NAME line and the DATA disagree.  Read literally, the NAME gives
`a(1) = 2` (every block `k ≥ 2` conjecturally contains a prime, and block
`k = 1`, i.e. `(0, 1]`, contains none), `a(2) = 8`, `a(3) = 17`, …; the DATA
`1, 7, 16, 33, …` instead matches the second comment and the EXAMPLE:
`a(n)` is the **last** `k` with A066888(k) = n.  (A python check, every
`k ≤ 3000`, reproduces all 51 listed terms as last occurrences, and the
literal-NAME values `1, 2, 8, 17, 34, 53, 67, 80, 80, …`.)  The DATA is not
monotone (`a(6) = 79 > a(7) = 72`), so it is not "least `m` with at least
`n + 1` primes in every block `k > m`" either.

We therefore state the conjecture for both readings:

* `lt_of_isGreatest_occurrence` — DATA reading: if `m` is the last index with
  exactly `n` primes in its block, then `n < m`.
* `lt_of_isLeast_nameProperty` — literal NAME reading: if `m ≥ 1` is the least
  index such that every block `k ≥ m` has at least `n` primes, then `n < m`.

Both are stated conditionally on `a(n)` being defined (`IsGreatest` /
`IsLeast`), which is exactly the entry's "whenever the sequence is well
defined"; the unconditional existence of `a(n)` is not claimed by the comment.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A190661LeastPrimesTriangular

/-! ## Definition layer -/

/-- The `k`-th triangular number `T(k) = k (k + 1) / 2` (the division is exact). -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- A066888(k): the number of primes `p` with `T(k-1) < p ≤ T(k)`.  Meaningful
for `k ≥ 1` (the OEIS offset); at `k = 0` the truncated `k - 1` gives the empty
interval `(0, 0]` and the junk value `0`, and every statement below guards
`1 ≤ k`. -/
def primesInBlock (k : ℕ) : ℕ :=
  ((Finset.Ioc (tri (k - 1)) (tri k)).filter Nat.Prime).card

/-! ## Ground truth -/

-- The triangular numbers `0, 1, 3, 6, 10, 15, 21, 28` (A000217).
example : (List.range 8).map tri = [0, 1, 3, 6, 10, 15, 21, 28] := by decide

-- The first terms of A066888: `0,2,1,1,2,2,1,2,3,2,2,3`.
example : (List.range 12).map (fun i => primesInBlock (i + 1)) =
    [0, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3] := by decide

-- DATA consistency: `a(0) = 1`, `a(1) = 7`, `a(2) = 16`, `a(3) = 33` are
-- occurrences of `0, 1, 2, 3` in A066888 (that they are the *last* ones is
-- the conjectural part of the entry and is not checkable).
example : primesInBlock 1 = 0 ∧ primesInBlock 7 = 1 ∧ primesInBlock 16 = 2 ∧
    primesInBlock 33 = 3 := by decide +kernel

/-! ## Helper lemmas -/

/-- `T(j + 1) = T(j) + (j + 1)`. -/
theorem tri_succ (j : ℕ) : tri (j + 1) = tri j + (j + 1) := by
  unfold tri
  have hmul : (j + 1) * (j + 1 + 1) = j * (j + 1) + (j + 1) * 2 := by ring
  rw [hmul, Nat.add_mul_div_right _ _ two_pos]

/-- `3 ≤ T(j)` for `j ≥ 2`. -/
theorem three_le_tri {j : ℕ} (hj : 2 ≤ j) : 3 ≤ tri j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rw [tri_succ, tri_succ]
  omega

/-- The block `(T(k-1), T(k)]` has `k` elements. -/
theorem card_block (k : ℕ) (hk : 1 ≤ k) : (Finset.Ioc (tri (k - 1)) (tri k)).card = k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.card_Ioc, Nat.add_sub_cancel, tri_succ]
  omega

/-- **Key step.** For `k ≥ 3` the block `(T(k-1), T(k)]` consists of `k ≥ 3`
consecutive integers all above `3`, so it contains an even number `≥ 4`, which is
composite; hence fewer than `k` of its elements are prime. -/
theorem primesInBlock_lt {k : ℕ} (hk : 3 ≤ k) : primesInBlock k < k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hlow : 3 ≤ tri j := three_le_tri (by omega)
  have htop : tri (j + 1) = tri j + (j + 1) := tri_succ j
  -- an even element `e` of the block with `4 ≤ e`
  obtain ⟨e, he1, he2, heven⟩ : ∃ e, tri j < e ∧ e ≤ tri j + 2 ∧ Even e := by
    rcases Nat.even_or_odd (tri j) with h | h
    · exact ⟨tri j + 2, by omega, le_rfl, h.add even_two⟩
    · exact ⟨tri j + 1, by omega, by omega, h.add_one⟩
  have hmem : e ∈ Finset.Ioc (tri (j + 1 - 1)) (tri (j + 1)) := by
    rw [Finset.mem_Ioc, Nat.add_sub_cancel]
    omega
  have hnp : ¬ e.Prime := fun hp => by
    have h2 : e = 2 := (hp.even_iff).mp heven
    omega
  have hss : (Finset.Ioc (tri (j + 1 - 1)) (tri (j + 1))).filter Nat.Prime ⊂
      Finset.Ioc (tri (j + 1 - 1)) (tri (j + 1)) :=
    Finset.filter_ssubset.mpr ⟨e, hmem, hnp⟩
  have hlt := Finset.card_lt_card hss
  rw [card_block (j + 1) (by omega)] at hlt
  exact hlt

/-! ## The conjecture -/

/-- **A190661 conjecture, DATA reading (John W. Nicholson, May 18 2011).**

Verbatim: "It is conjectured that for every n >= 0, a(n) > n."  Here `a(n)` is
read as in the entry's comment and EXAMPLE, which the listed terms match: the
index of the last occurrence of `n` in A066888, i.e. the greatest `k ≥ 1` with
exactly `n` primes in `(T(k-1), T(k)]`.  Whenever this last occurrence exists,
it exceeds `n`.

Proof: block `1` has `0` primes, block `2` (`= {2, 3}`) has `2` but block `5`
also has `2`, and every block `k ≥ 3` has fewer than `k` primes. -/
theorem lt_of_isGreatest_occurrence (n m : ℕ)
    (hm : IsGreatest {k : ℕ | 1 ≤ k ∧ primesInBlock k = n} m) : n < m := by
  obtain ⟨⟨hm1, hmn⟩, hmax⟩ := hm
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with h | h | h
  · subst h
    have h1 : primesInBlock 1 = 0 := by decide
    omega
  · subst h
    have h2 : primesInBlock 2 = 2 := by decide
    have h5 : primesInBlock 5 = 2 := by decide
    have h5mem : 5 ∈ {k : ℕ | 1 ≤ k ∧ primesInBlock k = n} := ⟨by omega, by omega⟩
    have h52 : 5 ≤ 2 := hmax h5mem
    omega
  · have hlt := primesInBlock_lt h
    omega

/-- **A190661 conjecture, literal NAME reading.**

Verbatim: "It is conjectured that for every n >= 0, a(n) > n," with `a(n)` "the
least number m such that there are at least n primes in the range
(T(k-1), T(k)] for all k >= m".  Whenever such a least `m ≥ 1` exists, it
exceeds `n`.  (Under this reading `a(1) = 2`, not the listed `7`; see the module
header.) -/
theorem lt_of_isLeast_nameProperty (n m : ℕ)
    (hm : IsLeast {m : ℕ | 1 ≤ m ∧ ∀ k, m ≤ k → n ≤ primesInBlock k} m) : n < m := by
  obtain ⟨⟨hm1, hall⟩, -⟩ := hm
  by_contra hle
  rw [not_lt] at hle
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
  · subst h
    have h1 : primesInBlock 1 = 0 := by decide
    have := hall 1 (by omega)
    omega
  · subst h
    have h3 : primesInBlock 3 = 1 := by decide
    have := hall 3 (by omega)
    omega
  · have hlt := primesInBlock_lt h
    have := hall n hle
    omega

/-! ## Non-vacuity -/

-- The DATA-reading hypothesis is satisfiable in a finite sense: index `7` has
-- exactly one prime, and no index `≤ 7` other than `3, 4, 7` has exactly one,
-- so the set in `lt_of_isGreatest_occurrence` is nonempty for `n = 1`.
example : 7 ∈ {k : ℕ | 1 ≤ k ∧ primesInBlock k = 1} := ⟨by omega, by decide⟩

-- The NAME-reading hypothesis is satisfiable: `a(0) = 1` under that reading.
example : IsLeast {m : ℕ | 1 ≤ m ∧ ∀ k, m ≤ k → 0 ≤ primesInBlock k} 1 :=
  ⟨⟨le_rfl, fun _ _ => Nat.zero_le _⟩, fun _ hm => hm.1⟩

end Candidates.A190661LeastPrimesTriangular
