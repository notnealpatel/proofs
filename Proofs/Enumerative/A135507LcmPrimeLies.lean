/-
# A135507 — McEachen: prime ratios `a(n+1)/a(n) - 2` lie in A140460 or 2 above it

## OEIS source (retrieved with `oeis show A135507` and `oeis show A140460`, 2026-10-21)

```
A135507
NAME:     a(1) = 1; for n > 1, a(n) = 2*a(n-1) + lcm(a(n-1),n).
TERMS:    1,4,20,60,180,540,4860,19440,58320,174960,2274480,6823440,20470320,
          184232880,552698640,1658095920,31503822480,94511467440,...
KEYWORDS: nonn,nice
COMMENT:  Conjecture: Let p = a(n+1)/a(n)-2. If p is prime then p = A140460(m)
          or p = A140460(m) + 2 for some m. - _Bill McEachen_, Apr 04 2024

A140460
NAME:     a(0) = 2; thereafter a(n) = smallest integer not a multiple of an
          earlier terms nor a sum of two earlier terms.
TERMS:    2,3,7,11,17,23,29,37,41,47,53,59,65,71,79,83,89,95,101,107,113,125,...
PROGRAMS: Mathematica (McMahon) and C (sieve): `m` is kept iff `m ≥ 2`, no
          kept `d < m` divides `m`, and `m` is not `i + j` with kept `j < i`.
```

## Status

Triage: open (no proof in the entry or the literature found).  The A135507
hypothesis is in fact not needed: every prime `p` satisfies "`p` or `p - 2` is a
term of A140460".  This module proves that stronger statement and derives the
conjecture from it (no `sorry`).

Argument: `2, 3` are terms, so every later term is coprime to `6`, i.e.
`≡ ±1 (mod 6)`.  A prime `p ≥ 5` is `≡ ±1 (mod 6)` and has no term `< p`
dividing it, so if it is not a term it is `i + j` with terms `j < i`.  Two
terms `> 3` sum to `0, ±2 (mod 6)`, and `3 + i` with `i > 3` is even; hence
`j = 2` and `p - 2 = i` is a term.

## Definitional-fidelity note

A140460 is encoded through its sieve (the entry's C program): `termsBelow n` is
the increasing list of terms `< n`, `IsTerm m` is membership, and
`a140460 = Nat.nth IsTerm` enumerates the terms in increasing order.  The
recursive specification `isTerm_iff` is the greedy rule; whether "sum of two
earlier terms" requires distinct terms is immaterial, because `2 * t` is a
multiple of the earlier term `t`.  Ground-truth checks pin the first 13 terms.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A135507LcmPrimeLies

/-! ## A135507 -/

/-- OEIS A135507 (offset 1): `a(1) = 1` and `a(n) = 2 a(n-1) + lcm(a(n-1), n)` for
`n > 1`.  Index `0` lies outside the entry's domain and is set to `0`. -/
def A135507 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * A135507 (n + 1) + Nat.lcm (A135507 (n + 1)) (n + 2)

example : (List.range 12).map (fun k => A135507 (k + 1)) =
    [1, 4, 20, 60, 180, 540, 4860, 19440, 58320, 174960, 2274480, 6823440] := by
  decide +kernel

/-- Every term of A135507 with index `n ≥ 1` is positive, so the ratio
`a(n+1)/a(n)` in the conjecture is a genuine quotient. -/
theorem A135507_pos (n : ℕ) (hn : 1 ≤ n) : 0 < A135507 n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [A135507]
    omega

/-! ## A140460 via its sieve -/

/-- One sieve step: append `n` to the list `L` of earlier terms iff `2 ≤ n`, no
member of `L` divides `n`, and `n` is not a sum of two distinct members of `L`. -/
def step (L : List ℕ) (n : ℕ) : List ℕ :=
  if 2 ≤ n ∧ (∀ d ∈ L, ¬ d ∣ n) ∧ ¬ (∃ i ∈ L, ∃ j ∈ L, j < i ∧ i + j = n) then
    L ++ [n]
  else L

/-- `termsBelow n` is the increasing list of the terms of A140460 that are `< n`. -/
def termsBelow : ℕ → List ℕ
  | 0 => []
  | n + 1 => step (termsBelow n) n

/-- `IsTerm m` holds iff `m` is a term of OEIS A140460. -/
def IsTerm (m : ℕ) : Prop := m ∈ termsBelow (m + 1)

/-- Membership in A140460 is decidable (it is list membership). -/
instance : DecidablePred IsTerm := fun m =>
  inferInstanceAs (Decidable (m ∈ termsBelow (m + 1)))

/-- OEIS A140460 (offset 0): the `m`-th term in increasing order. -/
noncomputable def a140460 (m : ℕ) : ℕ := Nat.nth IsTerm m

example : termsBelow 66 = [2, 3, 7, 11, 17, 23, 29, 37, 41, 47, 53, 59, 65] := by
  decide +kernel

/-- Membership in one sieve step. -/
theorem mem_step {L : List ℕ} {n x : ℕ} :
    x ∈ step L n ↔ x ∈ L ∨ (x = n ∧ 2 ≤ n ∧ (∀ d ∈ L, ¬ d ∣ n) ∧
      ¬ (∃ i ∈ L, ∃ j ∈ L, j < i ∧ i + j = n)) := by
  unfold step
  split_ifs with h
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (hx | rfl)
      · exact Or.inl hx
      · exact Or.inr ⟨rfl, h⟩
    · rintro (hx | ⟨rfl, -⟩)
      · exact Or.inl hx
      · exact Or.inr rfl
  · constructor
    · exact Or.inl
    · rintro (hx | ⟨rfl, hc⟩)
      · exact hx
      · exact absurd hc h

/-- Every member of `termsBelow n` is `< n`. -/
theorem lt_of_mem_termsBelow {n x : ℕ} (hx : x ∈ termsBelow n) : x < n := by
  induction n with
  | zero => simp [termsBelow] at hx
  | succ n ih =>
    rw [termsBelow, mem_step] at hx
    rcases hx with hx | ⟨rfl, -⟩
    · exact Nat.lt_succ_of_lt (ih hx)
    · exact Nat.lt_succ_self x

/-- `termsBelow n` lists exactly the terms of A140460 below `n`. -/
theorem mem_termsBelow {n x : ℕ} : x ∈ termsBelow n ↔ x < n ∧ IsTerm x := by
  induction n generalizing x with
  | zero => simp [termsBelow]
  | succ n ih =>
    have hn : n ∉ termsBelow n := fun h => lt_irrefl n (lt_of_mem_termsBelow h)
    have hterm : IsTerm n ↔ 2 ≤ n ∧ (∀ d ∈ termsBelow n, ¬ d ∣ n) ∧
        ¬ (∃ i ∈ termsBelow n, ∃ j ∈ termsBelow n, j < i ∧ i + j = n) := by
      unfold IsTerm
      rw [termsBelow, mem_step]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h hn
        · exact h
      · exact fun h => Or.inr ⟨rfl, h⟩
    rw [termsBelow, mem_step, ih, ← hterm]
    constructor
    · rintro (⟨hlt, hx⟩ | ⟨rfl, hx⟩)
      · exact ⟨Nat.lt_succ_of_lt hlt, hx⟩
      · exact ⟨Nat.lt_succ_self x, hx⟩
    · rintro ⟨hlt, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | rfl
      · exact Or.inl ⟨hlt, hx⟩
      · exact Or.inr ⟨rfl, hx⟩

/-- The greedy rule of A140460: `m` is a term iff `2 ≤ m`, no smaller term divides
`m`, and `m` is not a sum `i + j` of terms `j < i < m`. -/
theorem isTerm_iff (m : ℕ) : IsTerm m ↔ 2 ≤ m ∧ (∀ d, IsTerm d → d < m → ¬ d ∣ m) ∧
    ¬ ∃ i j, IsTerm i ∧ IsTerm j ∧ i < m ∧ j < i ∧ i + j = m := by
  have hm : m ∉ termsBelow m := fun h => lt_irrefl m (lt_of_mem_termsBelow h)
  have hstep : IsTerm m ↔ 2 ≤ m ∧ (∀ d ∈ termsBelow m, ¬ d ∣ m) ∧
      ¬ (∃ i ∈ termsBelow m, ∃ j ∈ termsBelow m, j < i ∧ i + j = m) := by
    unfold IsTerm
    rw [termsBelow, mem_step]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h hm
      · exact h
    · exact fun h => Or.inr ⟨rfl, h⟩
  rw [hstep]
  simp only [mem_termsBelow]
  constructor
  · rintro ⟨h2, hd, hs⟩
    refine ⟨h2, fun d hd' hdm => hd d ⟨hdm, hd'⟩, ?_⟩
    rintro ⟨i, j, hi, hj, him, hji, hij⟩
    exact hs ⟨i, ⟨him, hi⟩, j, ⟨lt_trans hji him, hj⟩, hji, hij⟩
  · rintro ⟨h2, hd, hs⟩
    refine ⟨h2, fun d ⟨hdm, hd'⟩ => hd d hd' hdm, ?_⟩
    rintro ⟨i, ⟨him, hi⟩, j, ⟨-, hj⟩, hji, hij⟩
    exact hs ⟨i, j, hi, hj, him, hji, hij⟩

/-- The number of terms of A140460 below `n` is the length of `termsBelow n`. -/
theorem count_eq_length (n : ℕ) : Nat.count IsTerm n = (termsBelow n).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.count_succ, ih]
    have hn : n ∉ termsBelow n := fun h => lt_irrefl n (lt_of_mem_termsBelow h)
    have hsucc : termsBelow (n + 1) = step (termsBelow n) n := rfl
    by_cases hT : IsTerm n
    · rw [if_pos hT, hsucc]
      have hT' : n ∈ step (termsBelow n) n := hT
      unfold step at hT' ⊢
      split_ifs at hT' ⊢ with hc
      · simp
      · exact absurd hT' hn
    · rw [if_neg hT, hsucc]
      have hT' : n ∉ step (termsBelow n) n := hT
      unfold step at hT' ⊢
      split_ifs at hT' ⊢ with hc
      · simp at hT'
      · rfl

example : a140460 0 = 2 ∧ a140460 1 = 3 ∧ a140460 2 = 7 ∧ a140460 3 = 11 ∧
    a140460 12 = 65 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := Nat.nth_count (p := IsTerm) (n := 2) (by decide +kernel)
    rwa [count_eq_length, show (termsBelow 2).length = 0 by decide +kernel] at h
  · have h := Nat.nth_count (p := IsTerm) (n := 3) (by decide +kernel)
    rwa [count_eq_length, show (termsBelow 3).length = 1 by decide +kernel] at h
  · have h := Nat.nth_count (p := IsTerm) (n := 7) (by decide +kernel)
    rwa [count_eq_length, show (termsBelow 7).length = 2 by decide +kernel] at h
  · have h := Nat.nth_count (p := IsTerm) (n := 11) (by decide +kernel)
    rwa [count_eq_length, show (termsBelow 11).length = 3 by decide +kernel] at h
  · have h := Nat.nth_count (p := IsTerm) (n := 65) (by decide +kernel)
    rwa [count_eq_length, show (termsBelow 65).length = 12 by decide +kernel] at h

/-! ## Every prime is a term of A140460 or two more than a term -/

/-- Every term of A140460 is at least `2`. -/
theorem two_le_of_isTerm {m : ℕ} (hm : IsTerm m) : 2 ≤ m :=
  ((isTerm_iff m).mp hm).1

/-- `2` is a term of A140460. -/
theorem isTerm_two : IsTerm 2 := by decide

/-- `3` is a term of A140460. -/
theorem isTerm_three : IsTerm 3 := by decide

/-- Every term of A140460 larger than `3` is `≡ ±1 (mod 6)`, since neither of the
earlier terms `2, 3` divides it. -/
theorem mod_six_of_isTerm {m : ℕ} (hm : IsTerm m) (h3 : 3 < m) :
    m % 6 = 1 ∨ m % 6 = 5 := by
  have hd := ((isTerm_iff m).mp hm).2.1
  have h2 : ¬ 2 ∣ m := hd 2 isTerm_two (by omega)
  have h3' : ¬ 3 ∣ m := hd 3 isTerm_three h3
  omega

/-- A prime `p ≥ 5` is `≡ ±1 (mod 6)`. -/
theorem mod_six_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  omega

/-- If a prime `p` is not a term of A140460, then `p - 2` is a term (and `5 ≤ p`). -/
theorem isTerm_sub_two_of_prime {p : ℕ} (hp : p.Prime) (hnot : ¬ IsTerm p) :
    5 ≤ p ∧ IsTerm (p - 2) := by
  have h5 : 5 ≤ p := by
    have h2 := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with rfl | rfl | rfl | h
    · exact absurd isTerm_two hnot
    · exact absurd isTerm_three hnot
    · exact absurd hp (by decide)
    · exact h
  refine ⟨h5, ?_⟩
  -- No smaller term divides the prime `p`, so `p` must be a sum of two terms.
  have hdiv : ∀ d, IsTerm d → d < p → ¬ d ∣ p := by
    intro d hd hdp hdvd
    rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
    · have := two_le_of_isTerm hd
      omega
    · omega
  have hsum : ∃ i j, IsTerm i ∧ IsTerm j ∧ i < p ∧ j < i ∧ i + j = p := by
    by_contra hs
    exact hnot ((isTerm_iff p).mpr ⟨hp.two_le, hdiv, hs⟩)
  obtain ⟨i, j, hi, hj, -, hji, hij⟩ := hsum
  have hp6 := mod_six_of_prime hp h5
  have hj2 := two_le_of_isTerm hj
  rcases (show j = 2 ∨ j = 3 ∨ 3 < j by omega) with rfl | rfl | hj3
  · -- `p = i + 2`
    have hi' : i = p - 2 := by omega
    rwa [← hi']
  · -- `p = i + 3` with `i > 3` a term: parity contradiction
    have hi6 := mod_six_of_isTerm hi hji
    omega
  · -- both summands are terms `> 3`: residue contradiction mod 6
    have hi6 := mod_six_of_isTerm hi (lt_trans hj3 hji)
    have hj6 := mod_six_of_isTerm hj hj3
    omega

/-- Every term of A140460 occurs in the enumeration `a140460`. -/
theorem exists_a140460_eq {x : ℕ} (hx : IsTerm x) : ∃ m, a140460 m = x := by
  obtain ⟨m, -, hm⟩ := Nat.exists_lt_card_nth_eq hx
  exact ⟨m, hm⟩

/-- **Every prime is a term of A140460 or two more than a term.**  For every prime
`p` there is `m` with `p = A140460(m)` or `p = A140460(m) + 2`.  This is
stronger than McEachen's conjecture on A135507: no hypothesis on `p` beyond
primality is needed. -/
theorem prime_eq_a140460_or_add_two (p : ℕ) (hp : p.Prime) :
    ∃ m, p = a140460 m ∨ p = a140460 m + 2 := by
  by_cases hT : IsTerm p
  · obtain ⟨m, hm⟩ := exists_a140460_eq hT
    exact ⟨m, Or.inl hm.symm⟩
  · obtain ⟨h5, hT2⟩ := isTerm_sub_two_of_prime hp hT
    obtain ⟨m, hm⟩ := exists_a140460_eq hT2
    exact ⟨m, Or.inr (by omega)⟩

/-- **McEachen's conjecture (A135507, Bill McEachen, Apr 04 2024).**

Verbatim: "Conjecture: Let p = a(n+1)/a(n)-2. If p is prime then p = A140460(m)
or p = A140460(m) + 2 for some m."

Here `a = A135507` with `n ≥ 1` (the entry's offset), and the ratio is taken in
`ℚ` so no truncated division or subtraction enters (`A135507_pos` shows the
denominator is nonzero).  Proved via `prime_eq_a140460_or_add_two`. -/
theorem conjecture (n : ℕ) (_hn : 1 ≤ n) (p : ℕ)
    (_hratio : (p : ℚ) = (A135507 (n + 1) : ℚ) / (A135507 n : ℚ) - 2) (hp : p.Prime) :
    ∃ m, p = a140460 m ∨ p = a140460 m + 2 := by
  -- The ratio hypothesis is not needed: the conclusion holds for every prime.
  exact prime_eq_a140460_or_add_two p hp

/-- Non-vacuity: at `n = 2` the ratio is `A135507(3)/A135507(2) - 2 = 20/4 - 2 = 3`,
a prime, so the hypotheses of `conjecture` are jointly satisfiable. -/
example : (1 ≤ 2) ∧ ((3 : ℕ) : ℚ) = (A135507 (2 + 1) : ℚ) / (A135507 2 : ℚ) - 2 ∧
    (3 : ℕ).Prime := by
  refine ⟨by norm_num, ?_, Nat.prime_three⟩
  have h3 : A135507 3 = 20 := by decide +kernel
  have h2 : A135507 2 = 4 := by decide +kernel
  rw [h3, h2]
  norm_num

end Candidates.A135507LcmPrimeLies
