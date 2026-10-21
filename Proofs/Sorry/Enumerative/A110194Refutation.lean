/-
# A110194 — the two-block conjecture for the differences of A110095 is false

## OEIS source (retrieved 2026-10-21; `oeis show A110194` and the live entry)

```
A110194   First differences of A110095 (least nonprime sequence whose first
          differences are nonprime).
OFFSET:   1
DATA:     1,8,1,4,1,1,4,1,1,4,1,1,4,1,1,1,1,4,4,1,1,4,1,1,4,1,1,4,1,1,1,1,4,4,
          1,1,1,1,4,4,1,1,4,1,1,1,1,4,4,1,1,4,1,1,4,1,1,1,1,1,1,1,1,1,1,4,4,...
COMMENT:  Conjecture: from a(5) on, are there only substrings <1 1 4> and
          <1 1 1 1 4 4 >?
AUTHOR:   Alexandre Wajnberg and Eric Angelini, Sep 06 2005
EXTENSIONS: More terms from Michel Marcus, Aug 09 2022
```

A110095: "Least increasing sequence of nonprimes whose first differences are
also nonprime", offset 1, data `0,1,9,10,14,15,16,20,21,22,26,...`; PARI
(Michel Marcus): `new = last+1; while(isprime(new) || isprime(new-last), new++)`.
No later comment on either entry retracts the conjecture.

## Status

This module **refutes** the conjecture.  Reading the conjecture as "the word
`a(5) a(6) a(7) ...` is a concatenation of the blocks `1 1 4` and
`1 1 1 1 4 4`", the parse is forced (a block starting at position `p` is
`1 1 4` exactly when `a(p+2) = 4`), and it reaches position `56` after the
blocks starting at `5, 8, 11, 14, 20, 23, 26, 29, 35, 41, 44, 50, 53`.  But
`a(56) = ... = a(65) = 1` (ten consecutive ones: A110095 runs
`112, 116, 117, ..., 126`, caused by the prime gap from `113` to `127`), so
neither block fits at `56`.  The OEIS DATA line itself already exhibits the
run.  In general every prime gap `g` produces a run of `g - 4` ones, so the
two-block pattern can only persist while all prime gaps are `≤ 8`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A110194Refutation

/-! ## Definition layer -/

/-- Bounded linear search: starting at candidate `k` and trying at most `fuel`
candidates `k, k+1, ...`, return the first `m` with `m` nonprime and `m - x`
nonprime (returns `k + fuel` if none is found; `next_isLeast` shows this junk
branch is never used by `next`). -/
def searchFrom (x : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k => if ¬ k.Prime ∧ ¬ (k - x).Prime then k else searchFrom x fuel (k + 1)

/-- The A110095 step: the least `k > x` such that `k` is nonprime and `k - x` is
nonprime.  (A suitable `k ≤ x + 9` always exists; see `next_isLeast`.) -/
def next (x : ℕ) : ℕ := searchFrom x 9 (x + 1)

/-- A110095 with its OEIS offset 1: `A110095 1 = 0` and
`A110095 (n + 1) = next (A110095 n)` for `n ≥ 1`.  The index `0` lies outside
the OEIS domain (its value is the junk `0`) and is never used below. -/
def A110095 (n : ℕ) : ℕ := next^[n - 1] 0

/-- A110194 with its OEIS offset 1: `a(n) = A110095(n+1) - A110095(n)`.  The
natural subtraction is exact since `A110095` is strictly increasing
(`A110095_lt_succ`). -/
def A110194 (n : ℕ) : ℕ := A110095 (n + 1) - A110095 n

/-! ## Fidelity of `next`: it is the least admissible successor -/

/-- Specification of the bounded search: if some admissible `m` lies in
`[k, k + fuel)`, the search returns an admissible value `≥ k` below which no
candidate `≥ k` is admissible. -/
theorem searchFrom_spec (x : ℕ) :
    ∀ (fuel k m : ℕ), k ≤ m → m < k + fuel → (¬ m.Prime ∧ ¬ (m - x).Prime) →
      (¬ (searchFrom x fuel k).Prime ∧ ¬ (searchFrom x fuel k - x).Prime) ∧
      k ≤ searchFrom x fuel k ∧
      ∀ j, k ≤ j → j < searchFrom x fuel k → ¬ (¬ j.Prime ∧ ¬ (j - x).Prime) := by
  intro fuel
  induction fuel with
  | zero => intro k m hkm hmk _; omega
  | succ fuel ih =>
    intro k m hkm hmk hm
    by_cases hk : ¬ k.Prime ∧ ¬ (k - x).Prime
    · simp only [searchFrom, if_pos hk]
      exact ⟨hk, le_rfl, fun j hj hjk => absurd hjk (not_lt.mpr hj)⟩
    · simp only [searchFrom, if_neg hk]
      have hkm' : k + 1 ≤ m := by
        rcases Nat.eq_or_lt_of_le hkm with h | h
        · exact absurd (h ▸ hm) hk
        · exact h
      obtain ⟨hP, hle, hmin⟩ := ih (k + 1) m hkm' (by omega) hm
      refine ⟨hP, by omega, fun j hj hjr => ?_⟩
      rcases Nat.eq_or_lt_of_le hj with h | h
      · exact h ▸ hk
      · exact hmin j h hjr

/-- An even number `≥ 4` is not prime. -/
theorem not_prime_of_even_of_four_le {m : ℕ} (he : Even m) (h4 : 4 ≤ m) : ¬ m.Prime := by
  intro hp
  have h2 : m = 2 := (Nat.Prime.even_iff hp).mp he
  omega

/-- **Fidelity of `next`.**  `next x` is the least `k` with `x < k`, `k`
nonprime and `k - x` nonprime — exactly the A110095 rule. -/
theorem next_isLeast (x : ℕ) :
    IsLeast {k | x < k ∧ ¬ k.Prime ∧ ¬ (k - x).Prime} (next x) := by
  have hex : ∃ m, x + 1 ≤ m ∧ m < x + 1 + 9 ∧ ¬ m.Prime ∧ ¬ (m - x).Prime := by
    rcases Nat.even_or_odd x with hx | hx
    · refine ⟨x + 4, by omega, by omega,
        not_prime_of_even_of_four_le (hx.add (by decide)) (by omega), ?_⟩
      rw [Nat.add_sub_cancel_left]
      decide
    · refine ⟨x + 9, by omega, by omega,
        not_prime_of_even_of_four_le (hx.add_odd (by decide)) (by omega), ?_⟩
      rw [Nat.add_sub_cancel_left]
      decide
  obtain ⟨m, hm1, hm2, hm⟩ := hex
  obtain ⟨hP, hle, hmin⟩ := searchFrom_spec x 9 (x + 1) m hm1 hm2 hm
  refine ⟨⟨by unfold next; omega, hP⟩, fun j hj => ?_⟩
  obtain ⟨hxj, hjP⟩ := hj
  by_contra hlt
  exact hmin j (by omega) (lt_of_not_ge hlt) hjP

/-- `A110095 1 = 0`, the OEIS initial term. -/
theorem A110095_one : A110095 1 = 0 := rfl

/-- The A110095 recursion: for `n ≥ 1`, `A110095 (n + 1) = next (A110095 n)`. -/
theorem A110095_succ {n : ℕ} (hn : 1 ≤ n) : A110095 (n + 1) = next (A110095 n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [A110095, Nat.add_sub_cancel, Function.iterate_succ_apply']

/-- A110095 is strictly increasing on its domain, so the natural subtraction in
`A110194` is an honest difference. -/
theorem A110095_lt_succ {n : ℕ} (hn : 1 ≤ n) : A110095 n < A110095 (n + 1) := by
  rw [A110095_succ hn]
  exact (next_isLeast (A110095 n)).1.1

/-! ## Ground truth against the OEIS data -/

/-- `A110095 (1), ..., A110095 (62)` agree with the OEIS data. -/
example : (List.range 62).map (fun i => A110095 (i + 1)) =
    [0, 1, 9, 10, 14, 15, 16, 20, 21, 22, 26, 27, 28, 32, 33, 34, 35, 36, 40, 44,
     45, 46, 50, 51, 52, 56, 57, 58, 62, 63, 64, 65, 66, 70, 74, 75, 76, 77, 78, 82,
     86, 87, 88, 92, 93, 94, 95, 96, 100, 104, 105, 106, 110, 111, 112, 116, 117,
     118, 119, 120, 121, 122] := by
  decide +kernel

/-- `A110194 (1), ..., A110194 (68)` agree with the OEIS data. -/
example : (List.range 68).map (fun i => A110194 (i + 1)) =
    [1, 8, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 4, 1,
     1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4,
     1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1] := by
  decide +kernel

/-! ## The conjecture -/

/-- The block `1 1 4` occurs in A110194 starting at position `p`. -/
def Block114 (p : ℕ) : Prop :=
  A110194 p = 1 ∧ A110194 (p + 1) = 1 ∧ A110194 (p + 2) = 4

/-- The block `1 1 1 1 4 4` occurs in A110194 starting at position `p`. -/
def Block111144 (p : ℕ) : Prop :=
  A110194 p = 1 ∧ A110194 (p + 1) = 1 ∧ A110194 (p + 2) = 1 ∧
    A110194 (p + 3) = 1 ∧ A110194 (p + 4) = 4 ∧ A110194 (p + 5) = 4

/-- `Block114 p` is decidable (a conjunction of natural-number equalities). -/
instance (p : ℕ) : Decidable (Block114 p) := by unfold Block114; infer_instance

/-- `Block111144 p` is decidable (a conjunction of natural-number equalities). -/
instance (p : ℕ) : Decidable (Block111144 p) := by unfold Block111144; infer_instance

/-- **Wajnberg–Angelini conjecture (A110194, Sep 06 2005).**  Verbatim:
"Conjecture: from a(5) on, are there only substrings <1 1 4> and
<1 1 1 1 4 4 >?"

Formalized: the infinite word `a(5) a(6) a(7) ...` is a concatenation of the
blocks `1 1 4` and `1 1 1 1 4 4`, i.e. there are block start positions
`b 0 = 5 < b 1 < b 2 < ...` such that each block `b i` is one of the two
words and the next block starts right after it. -/
def Conjecture : Prop :=
  ∃ b : ℕ → ℕ, b 0 = 5 ∧ ∀ i,
    (Block114 (b i) ∧ b (i + 1) = b i + 3) ∨ (Block111144 (b i) ∧ b (i + 1) = b i + 6)

/-! ## The refutation -/

/-- The forced parsing step: the start of the block after a block at `p`, or
`none` if neither block occurs at `p`. -/
def parseStep (p : ℕ) : Option ℕ :=
  if Block114 p then some (p + 3) else if Block111144 p then some (p + 6) else none

/-- The forced parse from position `5`, iterated `i` times. -/
def parse : ℕ → Option ℕ
  | 0 => some 5
  | i + 1 => (parse i).bind parseStep

/-- The two blocks never both start at the same position (they differ in the
third letter), so a valid block decomposition follows `parseStep`. -/
theorem parseStep_eq {p r : ℕ}
    (h : (Block114 p ∧ r = p + 3) ∨ (Block111144 p ∧ r = p + 6)) :
    parseStep p = some r := by
  rcases h with ⟨hb, hr⟩ | ⟨hb, hr⟩
  · simp only [parseStep, if_pos hb, hr]
  · have hn : ¬ Block114 p := fun h114 => by
      have h1 := h114.2.2
      have h2 := hb.2.2.1
      omega
    simp only [parseStep, if_neg hn, if_pos hb, hr]

/-- Any block decomposition agrees with the forced parse. -/
theorem parse_eq_some {b : ℕ → ℕ} (h0 : b 0 = 5) (h : ∀ i,
    (Block114 (b i) ∧ b (i + 1) = b i + 3) ∨ (Block111144 (b i) ∧ b (i + 1) = b i + 6)) :
    ∀ i, parse i = some (b i) := by
  intro i
  induction i with
  | zero => simp only [parse, h0]
  | succ i ih => simp only [parse, ih, Option.bind_some, parseStep_eq (h i)]

/-- Non-vacuity of the parse: the first thirteen blocks (from position `5`)
genuinely fit, and the parse reaches position `56`. -/
example : parse 13 = some 56 := by
  decide +kernel

/-- The forced parse gets stuck after 14 blocks: it reaches position `56`, where
`a(56) = ... = a(65) = 1`, so neither block fits. -/
theorem parse_fourteen : parse 14 = none := by
  decide +kernel

/-- **The A110194 conjecture is false.**  The block decomposition of
`a(5) a(6) ...` is forced and reaches position `56` (blocks start at
`5, 8, 11, 14, 20, 23, 26, 29, 35, 41, 44, 50, 53, 56`), but
`a(56), ..., a(65)` are ten consecutive `1`s, coming from the prime gap
`113, 127` (A110095 runs `112, 116, 117, ..., 126`).  Every prime gap `g`
gives a run of `g - 4` ones, so the conjectured pattern only holds while
prime gaps are at most `8`; the authors presumably extrapolated from the
initial range, where all relevant prime gaps are `≤ 8`. -/
theorem A110194_conjecture_false : ¬ Conjecture := by
  rintro ⟨b, h0, h⟩
  have hparse := parse_eq_some h0 h 14
  rw [parse_fourteen] at hparse
  exact Option.some_ne_none _ hparse.symm

end Candidates.A110194Refutation
