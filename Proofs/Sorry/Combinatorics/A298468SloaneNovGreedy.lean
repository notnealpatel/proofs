/-
# A298468 — Sloane (Nov 2019): closed form of the greedy system aa, bb, cc

## OEIS source (retrieved with `oeis show A298468`, 2026-10-21)

```
NAME:     Solution (aa(n)) of the system of 3 complementary equations in Comments.
TERMS:    1,4,6,9,12,14,16,19,21,24,26,29,32,34,36,39,42,44,46,49,52,54,56,59,61,
          64,66,69,72,74,76,79,81,84,86,89,92,94,96,99,101,104,106,109,112,114,
          116,119,122,124,126,129,132,134,136,139,141,144,146,149
COMMENT:  Define sequences aa(n), bb(n), cc(n) recursively, starting with
          aa(0) = 1, bb(0) = 2, cc(0) = 3:
          aa(n) = least new;
          bb(n) = aa(n) + cc(n-1);
          cc(n) = least new;
          where "least new k" means the least positive integer not yet placed.
COMMENT (the conjecture):
          From _N. J. A. Sloane_, Nov 05 2019: (Start)
          Conjecture: For t >= 1, aa(2t) = 5t+1(+1 if binary expansion of t ends
          in an odd number of 0's), and for t >= 0, aa(2t+1) = 5t+4.
          The first part may also be written as aa(2t) = 5t+1+A328789(t-1).
          (End)
PROGRAM:  (Mathematica, Peter J. C. Moses, Apr 23 2018) places aa(n), then
          bb(n) = aa(n) + cc(n-1), then cc(n) = least positive integer not among
          all values placed so far (including aa(n) and bb(n)).
```

## Status

Triage: open (no proof recorded in the entry or found in the literature;
absence of a match is not evidence of novelty).  The triage simulated the
system for `n < 400000`; this attempt re-ran it for `n < 10^6` with no
counterexample.  This module proves the conjecture (`sloane_conjecture`),
together with the companion closed forms for `bb` and `cc` and Kimberling's
partition claim, with no unproved step.

"Binary expansion of `t` ends in an odd number of 0's" is, for `t ≥ 1`,
`Odd (padicValNat 2 t)`.  The alternative form via A328789 is not used: the
triage observed that A328789 is an eta-quotient that does not match the
period-doubling indicator intended here.

## Formalization

`step n` carries the triple `(aa n, bb n, cc n)` together with the finite set of
all values placed at times `0, …, n`.  `leastNew s` is the least positive
integer not in `s`.  The proof exhibits closed forms `cfA`, `cfB`, `cfC`, proves
that they partition the positive integers with the monotonicity needed for the
greedy choices, and shows by induction that `step` computes them.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A298468SloaneNovGreedy

/-! ## Definition layer -/

/-- Every finite set of naturals misses some positive integer. -/
theorem exists_pos_not_mem (s : Finset ℕ) : ∃ x, 0 < x ∧ x ∉ s :=
  ⟨s.sup id + 1, Nat.succ_pos _, fun h => by
    have hle : (s.sup id + 1 : ℕ) ≤ s.sup id := Finset.le_sup (f := id) h
    omega⟩

/-- "Least new": the least positive integer not in the set `s` of placed values. -/
def leastNew (s : Finset ℕ) : ℕ := Nat.find (exists_pos_not_mem s)

/-- The greedy system of A298468.  `step n = ((aa n, bb n, cc n), P n)` where
`P n` is the set of all values `aa i, bb i, cc i` with `i ≤ n`.  Start:
`aa 0 = 1, bb 0 = 2, cc 0 = 3`.  For `n ≥ 1`: `aa n` is the least positive
integer not yet placed, `bb n = aa n + cc (n-1)`, and `cc n` is the least
positive integer not yet placed once `aa n` and `bb n` are placed. -/
def step : ℕ → (ℕ × ℕ × ℕ) × Finset ℕ
  | 0 => ((1, 2, 3), {1, 2, 3})
  | n + 1 =>
    match step n with
    | ((_, _, c), P) =>
      let a' := leastNew P
      let b' := a' + c
      let c' := leastNew (insert b' (insert a' P))
      ((a', b', c'), insert c' (insert b' (insert a' P)))

/-- `aa n` (A298468). -/
def aa (n : ℕ) : ℕ := (step n).1.1

/-- `bb n` (A297469). -/
def bb (n : ℕ) : ℕ := (step n).1.2.1

/-- `cc n` (A047218). -/
def cc (n : ℕ) : ℕ := (step n).1.2.2

/-! ### Ground truth against the listed terms -/

example : (List.range 30).map aa =
    [1, 4, 6, 9, 12, 14, 16, 19, 21, 24, 26, 29, 32, 34, 36, 39, 42, 44, 46, 49,
     52, 54, 56, 59, 61, 64, 66, 69, 72, 74] := by
  decide +kernel

example : (List.range 8).map bb = [2, 7, 11, 17, 22, 27, 31, 37] := by
  decide +kernel

example : (List.range 8).map cc = [3, 5, 8, 10, 13, 15, 18, 20] := by
  decide +kernel

/-! ## Closed forms -/

/-- Indicator that the 2-adic valuation of `t` is odd. -/
def oddVal (t : ℕ) : ℕ := if Odd (padicValNat 2 t) then 1 else 0

/-- Closed form for `aa`. -/
def cfA (n : ℕ) : ℕ :=
  if n % 2 = 1 then 5 * (n / 2) + 4 else if n = 0 then 1 else 5 * (n / 2) + 1 + oddVal (n / 2)

/-- Closed form for `cc`. -/
def cfC (n : ℕ) : ℕ := if n % 2 = 1 then 5 * (n / 2) + 5 else 5 * (n / 2) + 3

/-- Closed form for `bb`. -/
def cfB (n : ℕ) : ℕ := if n = 0 then 2 else cfA n + cfC (n - 1)

/-- The indicator `oddVal` is `0` or `1`. -/
theorem oddVal_le (t : ℕ) : oddVal t ≤ 1 := by
  unfold oddVal; split_ifs <;> omega

/-- An odd number has 2-adic valuation `0`, which is even. -/
theorem oddVal_of_odd (t : ℕ) (ht : t % 2 = 1) : oddVal t = 0 := by
  have h0 : padicValNat 2 t = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  simp [oddVal, h0]

/-- Doubling a positive `u` flips the parity of its 2-adic valuation. -/
theorem oddVal_two_mul (u : ℕ) (hu : 0 < u) : oddVal (2 * u) + oddVal u = 1 := by
  have hv : padicValNat 2 (2 * u) = padicValNat 2 u + 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self, add_comm]
  unfold oddVal
  rw [hv]
  by_cases h : Odd (padicValNat 2 u)
  · have h' : ¬ Odd (padicValNat 2 u + 1) := by
      rw [Nat.odd_add_one]; exact not_not.mpr h
    simp [h, h']
  · have h' : Odd (padicValNat 2 u + 1) := by rw [Nat.odd_add_one]; exact h
    simp [h, h']

/-- `cfA 0 = 1`. -/
theorem cfA_zero : cfA 0 = 1 := by simp [cfA]

/-- `cfA (2t+1) = 5t+4`. -/
theorem cfA_odd (t : ℕ) : cfA (2 * t + 1) = 5 * t + 4 := by
  unfold cfA; rw [if_pos (by omega)]; omega

/-- `cfA (2t) = 5t+1+oddVal t` for `t ≥ 1`. -/
theorem cfA_even (t : ℕ) (ht : 0 < t) : cfA (2 * t) = 5 * t + 1 + oddVal t := by
  unfold cfA; rw [if_neg (by omega), if_neg (by omega)]
  have h2 : 2 * t / 2 = t := by omega
  rw [h2]

/-- `cfC (2t+1) = 5t+5`. -/
theorem cfC_odd (t : ℕ) : cfC (2 * t + 1) = 5 * t + 5 := by
  unfold cfC; rw [if_pos (by omega)]; omega

/-- `cfC (2t) = 5t+3`. -/
theorem cfC_even (t : ℕ) : cfC (2 * t) = 5 * t + 3 := by
  unfold cfC; rw [if_neg (by omega)]; omega

/-- `cfB 0 = 2`. -/
theorem cfB_zero : cfB 0 = 2 := by simp [cfB]

/-- `cfB (2t+1) = 10t+7`. -/
theorem cfB_odd (t : ℕ) : cfB (2 * t + 1) = 10 * t + 7 := by
  unfold cfB; rw [if_neg (by omega), cfA_odd, show 2 * t + 1 - 1 = 2 * t by omega, cfC_even]
  omega

/-- `cfB (2t) = 10t+1+oddVal t` for `t ≥ 1`. -/
theorem cfB_even (t : ℕ) (ht : 0 < t) : cfB (2 * t) = 10 * t + 1 + oddVal t := by
  unfold cfB
  rw [if_neg (by omega), cfA_even t ht, show 2 * t - 1 = 2 * (t - 1) + 1 by omega, cfC_odd]
  omega

/-- Every natural is `0`, odd, or a positive even number. -/
theorem parity_cases (n : ℕ) : n = 0 ∨ (∃ t, n = 2 * t + 1) ∨ ∃ t, 0 < t ∧ n = 2 * t := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · left; rfl
    · right; right; exact ⟨t, ht, rfl⟩
  · right; left; exact ⟨t, rfl⟩

/-- `aa n < cc n` for the closed forms. -/
theorem cfA_lt_cfC (n : ℕ) : cfA n < cfC n := by
  rcases parity_cases n with rfl | ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
  · simp [cfA, cfC]
  · rw [cfA_odd, cfC_odd]; omega
  · rw [cfA_even t ht, cfC_even]; have := oddVal_le t; omega

/-- `cc n < aa (n + 1)` for the closed forms. -/
theorem cfC_lt_cfA_succ (n : ℕ) : cfC n < cfA (n + 1) := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · rw [cfC_even, cfA_odd]; omega
  · rw [cfC_odd, show 2 * t + 1 + 1 = 2 * (t + 1) by omega, cfA_even (t + 1) (by omega)]
    omega

/-- The closed form of `aa` is strictly increasing. -/
theorem cfA_strictMono : StrictMono cfA :=
  strictMono_nat_of_lt_succ fun n => (cfA_lt_cfC n).trans (cfC_lt_cfA_succ n)

/-- The closed form of `cc` is strictly increasing. -/
theorem cfC_strictMono : StrictMono cfC :=
  strictMono_nat_of_lt_succ fun n => (cfC_lt_cfA_succ n).trans (cfA_lt_cfC (n + 1))

/-- `aa n ≤ bb n` for the closed forms. -/
theorem cfA_le_cfB (n : ℕ) : cfA n ≤ cfB n := by
  unfold cfB
  split_ifs with h
  · subst h; simp [cfA]
  · omega

/-- The closed form of `bb` is strictly increasing. -/
theorem cfB_strictMono : StrictMono cfB := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rcases parity_cases n with rfl | ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [cfB_zero, show (0 + 1 : ℕ) = 2 * 0 + 1 by rfl, cfB_odd]; omega
  · rw [cfB_odd, show 2 * t + 1 + 1 = 2 * (t + 1) by omega, cfB_even (t + 1) (by omega)]
    omega
  · rw [cfB_even t ht, cfB_odd]; have := oddVal_le t; omega

/-- Residues of the closed form of `cc` modulo 5. -/
theorem cfC_mod (n : ℕ) : cfC n % 5 = 0 ∨ cfC n % 5 = 3 := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · rw [cfC_even]; omega
  · rw [cfC_odd]; omega

/-- Residues of the closed form of `bb` modulo 5. -/
theorem cfB_mod (n : ℕ) : cfB n % 5 = 1 ∨ cfB n % 5 = 2 := by
  rcases parity_cases n with rfl | ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [cfB_zero]; omega
  · rw [cfB_odd]; omega
  · rw [cfB_even t ht]; have := oddVal_le t; omega

/-- Residues of the closed form of `aa` modulo 5. -/
theorem cfA_mod (n : ℕ) : cfA n % 5 = 1 ∨ cfA n % 5 = 2 ∨ cfA n % 5 = 4 := by
  rcases parity_cases n with rfl | ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [cfA_zero]; omega
  · rw [cfA_odd]; omega
  · rw [cfA_even t ht]; have := oddVal_le t; omega

/-- The closed forms of `aa` and `bb` never take a common value. -/
theorem cfA_ne_cfB (m i : ℕ) : cfA m ≠ cfB i := by
  rcases parity_cases m with rfl | ⟨t, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [cfA_zero]
    rcases parity_cases i with rfl | ⟨u, rfl⟩ | ⟨u, hu, rfl⟩
    · rw [cfB_zero]; omega
    · rw [cfB_odd]; omega
    · rw [cfB_even u hu]; omega
  · rw [cfA_odd]
    rcases cfB_mod i with h | h <;> omega
  · rw [cfA_even t ht]
    have hot := oddVal_le t
    rcases parity_cases i with rfl | ⟨u, rfl⟩ | ⟨u, hu, rfl⟩
    · rw [cfB_zero]; omega
    · rw [cfB_odd]
      intro h
      have htodd : t % 2 = 1 := by omega
      have h0 := oddVal_of_odd t htodd
      omega
    · rw [cfB_even u hu]
      intro h
      have hou := oddVal_le u
      have htu : t = 2 * u := by omega
      have hsum := oddVal_two_mul u hu
      rw [← htu] at hsum
      omega

/-- The closed forms cover every positive integer. -/
theorem cover (y : ℕ) (hy : 0 < y) : ∃ m, y = cfA m ∨ y = cfB m ∨ y = cfC m := by
  have hr : y % 5 < 5 := Nat.mod_lt _ (by norm_num)
  set s := y / 5 with hs
  have hy5 : y = 5 * s + y % 5 := by omega
  interval_cases hr5 : y % 5
  · refine ⟨2 * (s - 1) + 1, Or.inr (Or.inr ?_)⟩; rw [cfC_odd]; omega
  · -- y = 5 s + 1
    rcases parity_cases s with hs0 | ⟨u, hu⟩ | ⟨u, hu0, hu⟩
    · exact ⟨0, Or.inl (by rw [cfA_zero]; omega)⟩
    · refine ⟨2 * s, Or.inl ?_⟩
      rw [cfA_even s (by omega), oddVal_of_odd s (by omega)]; omega
    · have hsum := oddVal_two_mul u hu0
      rw [← hu] at hsum
      have hos := oddVal_le s
      by_cases ho : oddVal s = 0
      · refine ⟨2 * s, Or.inl ?_⟩
        rw [cfA_even s (by omega), ho]; omega
      · refine ⟨s, Or.inr (Or.inl ?_)⟩
        rw [hu, cfB_even u hu0]; omega
  · -- y = 5 s + 2
    rcases parity_cases s with hs0 | ⟨u, hu⟩ | ⟨u, hu0, hu⟩
    · exact ⟨0, Or.inr (Or.inl (by rw [cfB_zero]; omega))⟩
    · refine ⟨s, Or.inr (Or.inl ?_)⟩
      rw [hu, cfB_odd]; omega
    · have hsum := oddVal_two_mul u hu0
      rw [← hu] at hsum
      have hos := oddVal_le s
      by_cases ho : oddVal s = 0
      · refine ⟨s, Or.inr (Or.inl ?_)⟩
        rw [hu, cfB_even u hu0]; omega
      · refine ⟨2 * s, Or.inl ?_⟩
        rw [cfA_even s (by omega)]; omega
  · exact ⟨2 * s, Or.inr (Or.inr (by rw [cfC_even]; omega))⟩
  · exact ⟨2 * s + 1, Or.inl (by rw [cfA_odd]; omega)⟩

/-! ## The greedy system computes the closed forms -/

/-- Characterization of `leastNew`: a positive non-member below which every
positive integer is a member. -/
theorem leastNew_eq (s : Finset ℕ) (x : ℕ) (hx0 : 0 < x) (hxs : x ∉ s)
    (hmin : ∀ y, 0 < y → y < x → y ∈ s) : leastNew s = x := by
  unfold leastNew
  rw [Nat.find_eq_iff]
  refine ⟨⟨hx0, hxs⟩, fun y hyx hy => hy.2 (hmin y hy.1 hyx)⟩

/-- A value placed at time `m` is at least `aa m`. -/
theorem cfA_le_of_placed (m y : ℕ) (h : y = cfA m ∨ y = cfB m ∨ y = cfC m) : cfA m ≤ y := by
  rcases h with rfl | rfl | rfl
  · exact le_rfl
  · exact cfA_le_cfB m
  · exact (cfA_lt_cfC m).le

/-- Invariant: `step n` holds the closed-form triple and the set of values
placed at times `≤ n`. -/
theorem step_spec (n : ℕ) : (step n).1 = (cfA n, cfB n, cfC n) ∧
    ∀ y, y ∈ (step n).2 ↔ ∃ i ≤ n, y = cfA i ∨ y = cfB i ∨ y = cfC i := by
  induction n with
  | zero =>
    refine ⟨by simp [step, cfA, cfB, cfC], fun y => ?_⟩
    simp [step, cfA, cfB, cfC]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    set P := (step n).2 with hP
    have hs : step n = ((cfA n, cfB n, cfC n), P) := by rw [← h1]
    have ha : leastNew P = cfA (n + 1) := by
      refine leastNew_eq P _ ((Nat.zero_le _).trans_lt (cfC_lt_cfA_succ n)) ?_ ?_
      · rw [h2]
        rintro ⟨i, hi, hA | hB | hC⟩
        · exact absurd hA (cfA_strictMono (by omega : i < n + 1)).ne'
        · exact cfA_ne_cfB _ _ hB
        · have hCi : cfC i ≤ cfC n := cfC_strictMono.monotone hi
          have := cfC_lt_cfA_succ n
          omega
      · intro y hy0 hylt
        rw [h2]
        obtain ⟨m, hm⟩ := cover y hy0
        refine ⟨m, ?_, hm⟩
        by_contra hmn
        have hle := cfA_le_of_placed m y hm
        have hmono : cfA (n + 1) ≤ cfA m := cfA_strictMono.monotone (by omega)
        omega
    have hb : cfA (n + 1) + cfC n = cfB (n + 1) := by simp [cfB]
    have hc : leastNew (insert (cfB (n + 1)) (insert (cfA (n + 1)) P)) = cfC (n + 1) := by
      refine leastNew_eq _ _ ((Nat.zero_le _).trans_lt (cfA_lt_cfC (n + 1))) ?_ ?_
      · intro hmem
        simp only [Finset.mem_insert, h2] at hmem
        rcases hmem with h | h | ⟨i, hi, hcase⟩
        · have h3 := cfC_mod (n + 1); have h4 := cfB_mod (n + 1); omega
        · exact (cfA_lt_cfC (n + 1)).ne' h
        · rcases hcase with hA | hB | hC
          · have hAi : cfA i ≤ cfA (n + 1) := cfA_strictMono.monotone (by omega)
            have := cfA_lt_cfC (n + 1)
            omega
          · have h3 := cfC_mod (n + 1); have h4 := cfB_mod i; omega
          · exact absurd hC (cfC_strictMono (by omega : i < n + 1)).ne'
      · intro y hy0 hylt
        simp only [Finset.mem_insert, h2]
        obtain ⟨m, hm⟩ := cover y hy0
        have hle := cfA_le_of_placed m y hm
        rcases lt_trichotomy m (n + 1) with hmn | hmn | hmn
        · exact Or.inr (Or.inr ⟨m, by omega, hm⟩)
        · subst hmn
          rcases hm with hA | hB | hC
          · exact Or.inr (Or.inl hA)
          · exact Or.inl hB
          · omega
        · have hmono : cfA (n + 1 + 1) ≤ cfA m := cfA_strictMono.monotone (by omega)
          have := cfC_lt_cfA_succ (n + 1)
          omega
    have hstep : step (n + 1) = ((cfA (n + 1), cfB (n + 1), cfC (n + 1)),
        insert (cfC (n + 1)) (insert (cfB (n + 1)) (insert (cfA (n + 1)) P))) := by
      rw [step, hs]
      simp only [ha, hb, hc]
    rw [hstep]
    refine ⟨rfl, fun y => ?_⟩
    simp only [Finset.mem_insert, h2]
    constructor
    · rintro (hC | hB | hA | ⟨i, hi, hcase⟩)
      · exact ⟨n + 1, le_rfl, Or.inr (Or.inr hC)⟩
      · exact ⟨n + 1, le_rfl, Or.inr (Or.inl hB)⟩
      · exact ⟨n + 1, le_rfl, Or.inl hA⟩
      · exact ⟨i, by omega, hcase⟩
    · rintro ⟨i, hi, hcase⟩
      rcases Nat.lt_or_ge i (n + 1) with hin | hin
      · exact Or.inr (Or.inr (Or.inr ⟨i, by omega, hcase⟩))
      · have hi' : i = n + 1 := by omega
        subst hi'
        rcases hcase with hA | hB | hC
        · exact Or.inr (Or.inr (Or.inl hA))
        · exact Or.inr (Or.inl hB)
        · exact Or.inl hC

/-- `aa` agrees with its closed form. -/
theorem aa_eq_cfA (n : ℕ) : aa n = cfA n := by
  simp [aa, (step_spec n).1]

/-- `bb` agrees with its closed form. -/
theorem bb_eq_cfB (n : ℕ) : bb n = cfB n := by
  simp [bb, (step_spec n).1]

/-- `cc` agrees with its closed form. -/
theorem cc_eq_cfC (n : ℕ) : cc n = cfC n := by
  simp [cc, (step_spec n).1]

/-! ## Sloane's conjecture -/

/-- Second half of Sloane's conjecture (A298468, Nov 05 2019): for `t ≥ 0`,
`aa(2t+1) = 5t+4`. -/
theorem aa_two_mul_add_one (t : ℕ) : aa (2 * t + 1) = 5 * t + 4 := by
  rw [aa_eq_cfA, cfA_odd]

/-- First half of Sloane's conjecture (A298468, Nov 05 2019): for `t ≥ 1`,
`aa(2t) = 5t+1`, plus `1` when the binary expansion of `t` ends in an odd number
of zeros, i.e. when the 2-adic valuation of `t` is odd. -/
theorem aa_two_mul (t : ℕ) (ht : 0 < t) :
    aa (2 * t) = 5 * t + 1 + if Odd (padicValNat 2 t) then 1 else 0 := by
  rw [aa_eq_cfA, cfA_even t ht]
  rfl

/-- **Sloane's conjecture (A298468, N. J. A. Sloane, Nov 05 2019).**

Verbatim: "Conjecture: For t >= 1, aa(2t) = 5t+1(+1 if binary expansion of t
ends in an odd number of 0's), and for t >= 0, aa(2t+1) = 5t+4."

Here `aa` is the greedy sequence of the entry: `aa 0 = 1, bb 0 = 2, cc 0 = 3`,
and for `n ≥ 1`, `aa n` is the least positive integer not yet placed,
`bb n = aa n + cc (n-1)`, and `cc n` is the least positive integer not yet
placed after `aa n` and `bb n`.  "Binary expansion of `t` ends in an odd number
of 0's" is `Odd (padicValNat 2 t)` (meaningful since `t ≥ 1`). -/
theorem sloane_conjecture :
    (∀ t : ℕ, 0 < t → aa (2 * t) = 5 * t + 1 + if Odd (padicValNat 2 t) then 1 else 0) ∧
      ∀ t : ℕ, aa (2 * t + 1) = 5 * t + 4 :=
  ⟨aa_two_mul, aa_two_mul_add_one⟩

/-- Companion closed form for `bb` (A297469): `bb(2t+1) = 10t+7`. -/
theorem bb_two_mul_add_one (t : ℕ) : bb (2 * t + 1) = 10 * t + 7 := by
  rw [bb_eq_cfB, cfB_odd]

/-- Companion closed form for `bb` (A297469): for `t ≥ 1`,
`bb(2t) = 10t+1`, plus `1` when the 2-adic valuation of `t` is odd. -/
theorem bb_two_mul (t : ℕ) (ht : 0 < t) :
    bb (2 * t) = 10 * t + 1 + if Odd (padicValNat 2 t) then 1 else 0 := by
  rw [bb_eq_cfB, cfB_even t ht]
  rfl

/-- Kimberling's claim in the entry that `cc = A047218` (numbers congruent to
`0` or `3` mod 5), in closed form: `cc(2t) = 5t+3` and `cc(2t+1) = 5t+5`. -/
theorem cc_closed_form (t : ℕ) : cc (2 * t) = 5 * t + 3 ∧ cc (2 * t + 1) = 5 * t + 5 :=
  ⟨by rw [cc_eq_cfC, cfC_even], by rw [cc_eq_cfC, cfC_odd]⟩

/-- Kimberling's claim in the entry: the sequences `aa`, `bb`, `cc` partition
the positive integers.  Every positive integer is some `aa m`, `bb m` or `cc m`,
and the three sequences are injective with pairwise disjoint ranges. -/
theorem partition :
    (∀ y : ℕ, 0 < y → ∃ m, y = aa m ∨ y = bb m ∨ y = cc m) ∧
      Function.Injective aa ∧ Function.Injective bb ∧ Function.Injective cc ∧
      (∀ m i, aa m ≠ bb i) ∧ (∀ m i, aa m ≠ cc i) ∧ (∀ m i, bb m ≠ cc i) := by
  have hA : aa = cfA := funext aa_eq_cfA
  have hB : bb = cfB := funext bb_eq_cfB
  have hC : cc = cfC := funext cc_eq_cfC
  rw [hA, hB, hC]
  refine ⟨cover, cfA_strictMono.injective, cfB_strictMono.injective,
    cfC_strictMono.injective, cfA_ne_cfB, fun m i h => ?_, fun m i h => ?_⟩
  · have h1 := cfA_mod m; have h2 := cfC_mod i; omega
  · have h1 := cfB_mod m; have h2 := cfC_mod i; omega

end Candidates.A298468SloaneNovGreedy
