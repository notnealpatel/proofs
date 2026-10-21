/-
# A115801 — 9k = 25 ⊗ k iff 15k = 19 ⊗ k (carryless multiplication)

## OEIS source (retrieved with `oeis show A115801`, 2026-10-21)

```
NAME:     Numbers k such that 9*k = A048720(25,k), where A048720 is carryless
          base-2 multiplication.
TERMS:    0,15,30,31,60,62,63,120,124,126,127,240,248,252,254,255,480,496,504,
          508,510,511,960,992,1008,1016,1020,1022,1023,1920,1984,2016,2032,2040,
          2044,2046,2047,3840,3855,3968,4032,4064,4080,4088,4092,4094,4095,7680,
          7695,7710,7711,7936,7951,8064,8128,8160,8176,8184
COMMENT:  If n is a term, then 2*n is also a term, and vice versa.
COMMENT (the conjecture):
  Conjecture: also k such that 15*k = A048720(19,k). This has been checked for
  all k in range 0 .. 2^25. - _Antti Karttunen_, Dec 21 2025
```

`A048720` (carryless product): "Multiplication table {0..i} X {0..j} of binary
polynomials (polynomials over GF(2)) interpreted as binary vectors, then written
in base 10; or, binary multiplication without carries", with the recurrence
`T(c, 2b) = 2 T(c, b)` and `T(c, 2b+1) = 2 T(c, b) XOR c` (Henry Bottomley,
Mar 16 2001), which is the definition `clmul` below.

## Status

Triage literature status: open (no proof in the entry or the literature as far
as the triage could tell; the entry reports a check for `k < 2^25`).  This file
proves the conjecture for every natural number `k`.

## Proof method

Both conditions are recognised by finite automata reading the binary digits of
`k` from the least significant end: the condition `e * q + c = clmul a q ^^^ m`
on `q = 2 q' + b` splits into a parity check on the last bit and the same
condition on `q'` with updated carry `c` and pending mask `m`
(`clEq_two_mul_add_iff`).  For the two conditions of the conjecture a finite
relation between the states of the two automata (`bisimS`), together with two
finite sets of dead states (`dead₁`, `dead₂`), is closed under the transition;
this is checked by `decide`, and a strong induction on `q` (`clEq_iff_of_bisim`)
turns it into the equivalence.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A115801NaturalClmulCase

/-! ## Definitions -/

/-- Carryless base-2 multiplication `A048720(n, k)`, by recursion on the second
argument: `clmul n 0 = 0` and `clmul n k = 2 * clmul n (k / 2) XOR (n if k is odd,
else 0)`, i.e. Bottomley's `T(c, 2b) = 2 T(c, b)`, `T(c, 2b+1) = 2 T(c, b) XOR c`. -/
def clmul (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * clmul n ((k + 1) / 2) ^^^ (if (k + 1) % 2 = 1 then n else 0)

/-! ### Ground truth against A048720 and A115801 -/

-- A048720 table entries: T(3,3) = 5, T(3,4) = 12, T(5,5) = 17, T(3,5) = 15, T(6,6) = 20.
example : clmul 3 3 = 5 := by simp [clmul]
example : clmul 3 4 = 12 := by simp [clmul]
example : clmul 5 5 = 17 := by simp [clmul]
example : clmul 3 5 = 15 := by simp [clmul]
example : clmul 6 6 = 20 := by simp [clmul]
-- Terms of A115801 satisfy `9 * k = clmul 25 k`.
example : clmul 25 15 = 9 * 15 := by simp [clmul]
example : clmul 25 7695 = 9 * 7695 := by simp [clmul]
-- Non-terms: 1 and 16 + 15 * 2 = 46 are not in A115801.
example : clmul 25 1 ≠ 9 * 1 := by simp [clmul]
example : clmul 25 46 ≠ 9 * 46 := by simp [clmul]
-- The conjectured second description on the same values.
example : clmul 19 7695 = 15 * 7695 := by simp [clmul]
example : clmul 19 46 ≠ 15 * 46 := by simp [clmul]

/-! ## Automaton machinery -/

/-- The digit recurrence of `clmul`: `clmul n (2 q + b) = 2 * clmul n q XOR n * b`
for a binary digit `b`. -/
theorem clmul_two_mul_add (n q b : ℕ) (hb : b < 2) :
    clmul n (2 * q + b) = 2 * clmul n q ^^^ n * b := by
  rcases Nat.eq_zero_or_pos (2 * q + b) with h0 | hpos
  · have hq : q = 0 := by omega
    have hb0 : b = 0 := by omega
    subst hq hb0
    simp [clmul]
  · obtain ⟨k, hk⟩ : ∃ k, 2 * q + b = k + 1 := ⟨2 * q + b - 1, by omega⟩
    have hdiv : (k + 1) / 2 = q := by omega
    have hmod : (k + 1) % 2 = b := by omega
    rw [hk, clmul, hdiv, hmod]
    interval_cases b <;> simp

/-- Splitting an equation `2 u + v = 2 X XOR w` into its last binary digit and the
equation one digit up. -/
theorem two_mul_add_eq_xor_iff (u v X w : ℕ) :
    2 * u + v = 2 * X ^^^ w ↔ v % 2 = w % 2 ∧ u + v / 2 = X ^^^ (w / 2) := by
  have h1 : (2 * X ^^^ w) % 2 = w % 2 := by
    have hpow := Nat.xor_mod_two_pow (n := 1) (a := 2 * X) (b := w)
    simp only [pow_one] at hpow
    rw [hpow]
    simp
  have h2 : (2 * X ^^^ w) / 2 = X ^^^ (w / 2) := by
    rw [Nat.xor_div_two]
    simp
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h1, ← h]
      omega
    · rw [← h2, ← h]
      omega
  · rintro ⟨hlow, hhigh⟩
    rw [← Nat.div_add_mod (2 * X ^^^ w) 2, h1, h2, ← hhigh, ← hlow]
    omega

/-- The generalised condition `e * q + c = clmul a q XOR m`: the automaton for
`e * k = clmul a k` in state carry `c`, pending mask `m`. -/
def ClEq (a e q c m : ℕ) : Prop := e * q + c = clmul a q ^^^ m

/-- The parity check performed by the automaton for `(a, e)` on digit `b` in state
`s = (carry, mask)`. -/
def OkBit (a e b : ℕ) (s : ℕ × ℕ) : Prop := (e * b + s.1) % 2 = (a * b ^^^ s.2) % 2

/-- `OkBit` is a decidable equation of natural numbers. -/
instance (a e b : ℕ) (s : ℕ × ℕ) : Decidable (OkBit a e b s) := by
  unfold OkBit
  infer_instance

/-- The state reached by the automaton for `(a, e)` after digit `b` from state
`s = (carry, mask)`. -/
def nextState (a e b : ℕ) (s : ℕ × ℕ) : ℕ × ℕ := ((e * b + s.1) / 2, (a * b ^^^ s.2) / 2)

/-- One automaton step: the condition on `2 q + b` is the parity check on `b` plus
the condition on `q` in the next state. -/
theorem clEq_two_mul_add_iff (a e q b : ℕ) (s : ℕ × ℕ) (hb : b < 2) :
    ClEq a e (2 * q + b) s.1 s.2 ↔
      OkBit a e b s ∧ ClEq a e q (nextState a e b s).1 (nextState a e b s).2 := by
  unfold ClEq OkBit nextState
  rw [clmul_two_mul_add a q b hb, Nat.xor_assoc]
  have hlhs : e * (2 * q + b) + s.1 = 2 * (e * q) + (e * b + s.1) := by ring
  rw [hlhs, two_mul_add_eq_xor_iff]

/-- At `q = 0` the condition says carry equals mask. -/
theorem clEq_zero_iff (a e c m : ℕ) : ClEq a e 0 c m ↔ c = m := by
  simp [ClEq, clmul]

/-- Halving strictly decreases a positive natural number: `q / 2 < q` for `0 < q`. -/
theorem div_two_lt_of_pos (q : ℕ) (hq : 0 < q) : q / 2 < q := by omega

/-- A set `D` of states that contains no accepting state (carry ≠ mask) and is closed
under the passing transitions consists of dead states: no `q` is accepted from it. -/
theorem not_clEq_of_dead (a e : ℕ) (D : List (ℕ × ℕ))
    (hacc : ∀ s ∈ D, s.1 ≠ s.2)
    (hclosed : ∀ s ∈ D, ∀ b < 2, OkBit a e b s → nextState a e b s ∈ D) :
    ∀ q, ∀ s ∈ D, ¬ ClEq a e q s.1 s.2 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      rw [clEq_zero_iff]
      exact hacc s hs
    · have hb : q % 2 < 2 := Nat.mod_lt q (by norm_num)
      have hdecomp : q = 2 * (q / 2) + q % 2 := (Nat.div_add_mod q 2).symm
      rw [hdecomp, clEq_two_mul_add_iff a e (q / 2) (q % 2) s hb]
      rintro ⟨hok, hrest⟩
      exact ih (q / 2) (div_two_lt_of_pos q hqpos) _ (hclosed s hs (q % 2) hb hok) hrest

/-- **Bisimulation principle.** Let `S` relate states of the automata for `(a₁, e₁)`
and `(a₂, e₂)` with matching acceptance, and suppose every digit either keeps both
automata alive inside `S`, or sends each automaton that stays alive into its dead set.
Then from every related pair the two conditions agree for all `q`. -/
theorem clEq_iff_of_bisim (a₁ e₁ a₂ e₂ : ℕ) (S : List ((ℕ × ℕ) × (ℕ × ℕ)))
    (D₁ D₂ : List (ℕ × ℕ))
    (hD₁acc : ∀ s ∈ D₁, s.1 ≠ s.2)
    (hD₁closed : ∀ s ∈ D₁, ∀ b < 2, OkBit a₁ e₁ b s → nextState a₁ e₁ b s ∈ D₁)
    (hD₂acc : ∀ s ∈ D₂, s.1 ≠ s.2)
    (hD₂closed : ∀ s ∈ D₂, ∀ b < 2, OkBit a₂ e₂ b s → nextState a₂ e₂ b s ∈ D₂)
    (hacc : ∀ p ∈ S, (p.1.1 = p.1.2 ↔ p.2.1 = p.2.2))
    (hstep : ∀ p ∈ S, ∀ b < 2,
      (OkBit a₁ e₁ b p.1 ∧ OkBit a₂ e₂ b p.2 ∧
          (nextState a₁ e₁ b p.1, nextState a₂ e₂ b p.2) ∈ S) ∨
        ((OkBit a₁ e₁ b p.1 → nextState a₁ e₁ b p.1 ∈ D₁) ∧
          (OkBit a₂ e₂ b p.2 → nextState a₂ e₂ b p.2 ∈ D₂))) :
    ∀ q, ∀ p ∈ S, (ClEq a₁ e₁ q p.1.1 p.1.2 ↔ ClEq a₂ e₂ q p.2.1 p.2.2) := by
  have hdead₁ := not_clEq_of_dead a₁ e₁ D₁ hD₁acc hD₁closed
  have hdead₂ := not_clEq_of_dead a₂ e₂ D₂ hD₂acc hD₂closed
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p hp
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      rw [clEq_zero_iff, clEq_zero_iff]
      exact hacc p hp
    · have hb : q % 2 < 2 := Nat.mod_lt q (by norm_num)
      have hdecomp : q = 2 * (q / 2) + q % 2 := (Nat.div_add_mod q 2).symm
      have hlt : q / 2 < q := div_two_lt_of_pos q hqpos
      rw [hdecomp, clEq_two_mul_add_iff a₁ e₁ (q / 2) (q % 2) p.1 hb,
        clEq_two_mul_add_iff a₂ e₂ (q / 2) (q % 2) p.2 hb]
      rcases hstep p hp (q % 2) hb with ⟨hok₁, hok₂, hmem⟩ | ⟨hd₁, hd₂⟩
      · have hrec := ih (q / 2) hlt _ hmem
        exact and_congr (iff_of_true hok₁ hok₂) hrec
      · constructor
        · rintro ⟨hok₁, hrest⟩
          exact absurd hrest (hdead₁ (q / 2) _ (hd₁ hok₁))
        · rintro ⟨hok₂, hrest⟩
          exact absurd hrest (hdead₂ (q / 2) _ (hd₂ hok₂))

/-! ## The concrete automata for `(25, 9)` and `(19, 15)` -/

/-- Reachable related state pairs of the automata for `9 k = clmul 25 k` and
`15 k = clmul 19 k`, starting from `((0, 0), (0, 0))`. -/
def bisimS : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  [((0, 0), (0, 0)), ((1, 1), (1, 1)), ((2, 2), (3, 3)), ((2, 6), (3, 4)), ((3, 4), (6, 7)),
    ((3, 5), (5, 6)), ((4, 4), (7, 7)), ((4, 12), (7, 9)), ((5, 12), (8, 9)),
    ((5, 13), (9, 8)), ((6, 10), (11, 13)), ((6, 14), (11, 10)), ((7, 9), (13, 15)),
    ((8, 8), (14, 14))]

/-- Dead states of the automaton for `9 k = clmul 25 k`. -/
def dead₁ : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (1, 3), (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (5, 12), (5, 13), (5, 15),
    (6, 14), (6, 15), (7, 10), (7, 11), (8, 9)]

/-- Dead states of the automaton for `15 k = clmul 19 k`. -/
def dead₂ : List (ℕ × ℕ) := [(3, 4), (5, 6), (6, 7), (8, 9), (9, 8), (11, 10)]

/-- From every related pair in `bisimS`, the two conditions agree for all `q`. -/
theorem clEq_25_9_iff_clEq_19_15 :
    ∀ q, ∀ p ∈ bisimS, (ClEq 25 9 q p.1.1 p.1.2 ↔ ClEq 19 15 q p.2.1 p.2.2) :=
  clEq_iff_of_bisim 25 9 19 15 bisimS dead₁ dead₂ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ## The conjecture -/

/-- **A115801 conjecture (Antti Karttunen, Dec 21 2025), proved.**
For every natural number `k`, `9 * k = A048720(25, k)` if and only if
`15 * k = A048720(19, k)`. -/
theorem a115801_conjecture (k : ℕ) : 9 * k = clmul 25 k ↔ 15 * k = clmul 19 k := by
  have hstart : ((0, 0), (0, 0)) ∈ bisimS := by decide
  have h := clEq_25_9_iff_clEq_19_15 k _ hstart
  simpa [ClEq] using h

end Candidates.A115801NaturalClmulCase
