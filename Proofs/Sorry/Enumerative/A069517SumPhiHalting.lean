/-
# A069517 — Bala: `∑_{d ∣ n} a(d)^2 φ(d)` is the halting time of Turing machine 3626

## OEIS source (retrieved with `oeis show A069517` / `oeis show A393210`, 2026-10-21)

```
A069517
NAME:     a(n) = (-1)*Sum_{d|n} (moebius(d)*(-1)^d).
TERMS:    1,2,0,2,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,...
FORMULA:  Multiplicative with a(2^e) = 2 and a(p^e) = 0 for an odd prime p.
          - _Amiram Eldar_, Aug 29 2023
FORMULA (the conjecture, last line of a block by Peter Bala):
  From _Peter Bala_, Sep 11 2026: (Start) ...
  Conjecture: Sum_{d | n} a(d)^2 * phi(d) = A393210(n). (End)

A393210
NAME:     Halting time for Wolfram's 2-state 2-symbol Turing machine 3626 when
          started with n on the tape.
TERMS:    1,5,1,13,1,5,1,29,1,5,1,13,1,5,1,61,1,5,1,13,1,5,1,29,...
COMMENT:  Machine 3626 computes the identity function. This machine exhibits
          exponential growth in halting time ...
PROGRAM:  PacletSymbol["WolframInstitute/TuringMachine",
          "OneSidedTuringMachineFunction"][{3626, 2, 2}, {1, lim}, lim, "Steps"]
```

The one-sided convention (A392245, quoting Wolfram 2026, "P vs. NP and the
Difficulty of Computation", section "The Basic Setup"): the binary digits of
`n` are written on the tape, the machine starts on the cell of the least
significant bit in state 1, and it stops when its head goes further to the
right than where it started.  A392245 also gives the explicit transition table
of machine 1285, which pins down the rule-number decoding used here (checked
below by `decide`).  The decoding was further cross-checked by an independent
Python simulation against the listed data of A393210 (machine 3626), A037227
(machine 3589) and A393209 (machine 1511).

## Status

Triage: open (no proof in the entry or the literature found).  This module
proves the conjecture: for `n = 2^m · o` with `o` odd, machine 3626 halts after
exactly `2^(m+2) - 3` steps, and `∑_{d ∣ n} a(d)^2 φ(d) = 4 · 2^m - 3`.

Proof idea.  The `m` trailing zeros of `n` form a binary counter whose least
significant bit sits next to the lowest `1` of `n` (a sentinel).  State 2
increments the counter moving right, state 1 sweeps back left over zeros to the
sentinel.  The counter runs from `0` to overflow; the overflow carry leaves the
starting cell, which halts the machine.  A self-similar recursion on the counter
width gives `f(k+1) = 2 f(k) + k + 3`, `f(0) = 0`, so `f(k) = 2^(k+2) - k - 4`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A069517SumPhiHalting

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## The sequence A069517 -/

/-- OEIS A069517: `a(n) = (-1) * ∑_{d ∣ n} μ(d) (-1)^d`. -/
def a069517 (n : ℕ) : ℤ := -∑ d ∈ n.divisors, ArithmeticFunction.moebius d * (-1) ^ d

/-- Ground truth: the first sixteen listed terms of A069517. -/
example : (List.range 16).map (fun i => a069517 (i + 1)) =
    [1, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2] := by decide +kernel

/-! ## Wolfram's 2-state 2-symbol one-sided Turing machines -/

/-- Position of the case `(state, colour)` in Wolfram's rule-number digits for 2-state
2-symbol machines: the cases are ordered `(1,1), (1,0), (2,1), (2,0)`, most significant
base-8 digit first. -/
def caseIndex (st : ℕ) (c : Bool) : ℕ := 2 * (st - 1) + (if c then 0 else 1)

/-- The base-8 digit of rule number `num` governing the case `(st, c)`. -/
def ruleDigit (num st : ℕ) (c : Bool) : ℕ := num / 8 ^ (3 - caseIndex st c) % 8

/-- Transition of the 2-state 2-symbol machine with Wolfram number `num` in state `st`
reading colour `c`: returns `(new state, colour written, moves right?)`.  A digit `d`
encodes new state `d / 4 + 1`, written colour `(d / 2) % 2`, and a move to the right
iff `d` is odd. -/
def transition (num st : ℕ) (c : Bool) : ℕ × Bool × Bool :=
  let d := ruleDigit num st c
  (d / 4 + 1, decide (d / 2 % 2 = 1), decide (d % 2 = 1))

/-- Ground truth for the decoding: machine 1285 has the table given in A392245,
`1U -> 1UL, 0U -> 0DL, 1D -> 0UL, 0D -> 0DR` (U = state 1, D = state 2). -/
example : transition 1285 1 true = (1, true, false) ∧ transition 1285 1 false = (2, false, false) ∧
    transition 1285 2 true = (1, false, false) ∧ transition 1285 2 false = (2, false, true) := by
  decide

/-- A machine configuration: current state, head position (increasing to the right; the
starting cell is position `0`), and tape contents. -/
structure Config where
  /-- Current state (`1` or `2`). -/
  state : ℕ
  /-- Head position; the starting cell is `0` and moving right increases it. -/
  head : ℤ
  /-- Tape contents (`true` = colour 1). -/
  tape : ℤ → Bool

/-- One step of machine `num`: write, change state, and move the head. -/
def step (num : ℕ) (cfg : Config) : Config :=
  let r := transition num cfg.state (cfg.tape cfg.head)
  { state := r.1
    head := if r.2.2 then cfg.head + 1 else cfg.head - 1
    tape := Function.update cfg.tape cfg.head r.2.1 }

/-- Initial tape for input `n`: bit `i` of `n` sits at position `-i` (least significant bit
under the head, more significant bits to the left), blank to the right. -/
def initTape (n : ℕ) (p : ℤ) : Bool := decide (p ≤ 0) && n.testBit (-p).toNat

/-- Initial configuration on input `n`: state 1, head on the least significant bit. -/
def init (n : ℕ) : Config := ⟨1, 0, initTape n⟩

/-- Configuration of machine `num` after `t` steps on input `n`. -/
def run (num n t : ℕ) : Config := (step num)^[t] (init n)

open scoped Classical in
/-- Halting time of the one-sided machine `num` on input `n`: the first step count after
which the head is strictly to the right of its starting cell (`0` if it never halts). -/
noncomputable def haltingTime (num n : ℕ) : ℕ :=
  if h : ∃ t, 0 < (run num n t).head then Nat.find h else 0

/-- OEIS A393210: halting time of Wolfram's 2-state 2-symbol machine 3626 on input `n`. -/
noncomputable def a393210 (n : ℕ) : ℕ := haltingTime 3626 n

/-- Ground truth (direct evaluation): on input `2` machine 3626 is still on the tape after
four steps and has left it to the right after five (A393210(2) = 5). -/
example : (run 3626 2 4).head = 0 ∧ (run 3626 2 5).head = 1 := by
  constructor <;> rfl

/-! ## The four rules of machine 3626 -/

/-- Machine 3626, state 1 reading 0: keep 0, stay in state 1, move left. -/
lemma step_one_false (p : ℤ) (tp : ℤ → Bool) (hp : tp p = false) :
    step 3626 ⟨1, p, tp⟩ = ⟨1, p - 1, tp⟩ := by
  have ht : transition 3626 1 false = (1, false, false) := by decide
  simp only [step, hp, ht, Bool.false_eq_true, if_false]
  rw [← hp, Function.update_eq_self]

/-- Machine 3626, state 1 reading 1: keep 1, go to state 2, move right. -/
lemma step_one_true (p : ℤ) (tp : ℤ → Bool) (hp : tp p = true) :
    step 3626 ⟨1, p, tp⟩ = ⟨2, p + 1, tp⟩ := by
  have ht : transition 3626 1 true = (2, true, true) := by decide
  simp only [step, hp, ht, if_true]
  rw [← hp, Function.update_eq_self]

/-- Machine 3626, state 2 reading 0: write 1, go to state 1, move left. -/
lemma step_two_false (p : ℤ) (tp : ℤ → Bool) (hp : tp p = false) :
    step 3626 ⟨2, p, tp⟩ = ⟨1, p - 1, Function.update tp p true⟩ := by
  have ht : transition 3626 2 false = (1, true, false) := by decide
  simp only [step, hp, ht, Bool.false_eq_true, if_false]

/-- Machine 3626, state 2 reading 1: write 0, stay in state 2, move right. -/
lemma step_two_true (p : ℤ) (tp : ℤ → Bool) (hp : tp p = true) :
    step 3626 ⟨2, p, tp⟩ = ⟨2, p + 1, Function.update tp p false⟩ := by
  have ht : transition 3626 2 true = (2, false, true) := by decide
  simp only [step, hp, ht, if_true]

/-! ## Runs that stay left of a bound -/

/-- A run of machine 3626 of `t` steps from `c` to `c'` before whose last step the head
never stands to the right of `hi`. -/
def GoodRun (hi : ℤ) (c : Config) (t : ℕ) (c' : Config) : Prop :=
  (step 3626)^[t] c = c' ∧ ∀ s < t, ((step 3626)^[s] c).head ≤ hi

/-- Runs compose. -/
lemma GoodRun.trans {hi : ℤ} {c c' c'' : Config} {t u : ℕ} (h1 : GoodRun hi c t c')
    (h2 : GoodRun hi c' u c'') : GoodRun hi c (t + u) c'' := by
  refine ⟨?_, fun s hs => ?_⟩
  · rw [add_comm, Function.iterate_add_apply, h1.1, h2.1]
  · by_cases hst : s < t
    · exact h1.2 s hst
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hst)
      rw [add_comm, Function.iterate_add_apply, h1.1]
      exact h2.2 r (by omega)

/-- The head bound of a run may be relaxed. -/
lemma GoodRun.mono {hi hi' : ℤ} {c c' : Config} {t : ℕ} (h : GoodRun hi c t c')
    (hle : hi ≤ hi') : GoodRun hi' c t c' :=
  ⟨h.1, fun s hs => (h.2 s hs).trans hle⟩

/-- A single step is a run of length one. -/
lemma GoodRun.single {hi : ℤ} {c c' : Config} (hc : c.head ≤ hi) (hs : step 3626 c = c') :
    GoodRun hi c 1 c' :=
  ⟨by simpa using hs, fun s hs' => by
    have hs0 : s = 0 := by omega
    subst hs0; simpa using hc⟩

/-- State 1 sweeps left over `j` blank cells `p, p-1, …, p-j+1` without changing the tape. -/
lemma sweep (j : ℕ) : ∀ (p : ℤ) (tp : ℤ → Bool), (∀ i : ℤ, p - j < i → i ≤ p → tp i = false) →
    GoodRun p ⟨1, p, tp⟩ j ⟨1, p - j, tp⟩ := by
  induction j with
  | zero => intro p tp _; exact ⟨by simp, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro p tp hz
    have h1 : GoodRun p ⟨1, p, tp⟩ 1 ⟨1, p - 1, tp⟩ :=
      GoodRun.single le_rfl (step_one_false p tp (hz p (by push_cast; omega) le_rfl))
    have h2 := (ih (p - 1) tp
      (fun i hi1 hi2 => hz i (by push_cast at hi1 ⊢; omega) (by omega))).mono
      (show p - 1 ≤ p by omega)
    have h3 := h1.trans h2
    rw [add_comm] at h3
    convert h3 using 2
    push_cast; ring

/-- Running time of the `k`-bit counter: `f 0 = 0`, `f (k+1) = 2 f k + k + 3`. -/
def counterTime : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * counterTime k + k + 3

/-- Closed form `f k = 2^(k+2) - k - 4`. -/
lemma counterTime_eq (k : ℕ) : (counterTime k : ℤ) = 2 ^ (k + 2) - k - 4 := by
  induction k with
  | zero => simp [counterTime]
  | succ k ih =>
    simp only [counterTime]
    push_cast
    rw [ih]; ring

/-- **Counter lemma.** If cells `p-k+1, …, p` are blank and cell `p-k` holds a `1`, then
machine 3626 started in state 2 on cell `p-k+1` counts the block from `0` to overflow and
leaves it on the right: after `counterTime k` steps it is in state 2 on cell `p+1`, with the
tape restored, and before that its head never passes `p`. -/
lemma counter (k : ℕ) : ∀ (p : ℤ) (tp : ℤ → Bool),
    (∀ i : ℤ, p - k < i → i ≤ p → tp i = false) → tp (p - k) = true →
    GoodRun p ⟨2, p - k + 1, tp⟩ (counterTime k) ⟨2, p + 1, tp⟩ := by
  induction k with
  | zero =>
    intro p tp _ _
    exact ⟨by simp [counterTime], fun s hs => absurd hs (by simp [counterTime])⟩
  | succ k ih =>
    intro p tp hz hs
    push_cast at hz hs ⊢
    have hp : tp p = false := hz p (by omega) le_rfl
    set tp' := Function.update tp p true with htp'
    -- the low `k` bits count to overflow, carrying into cell `p`
    have r1 : GoodRun p ⟨2, p - (k + 1) + 1, tp⟩ (counterTime k) ⟨2, p, tp⟩ := by
      have hsub := ih (p - 1) tp (fun i h1 h2 => hz i (by omega) (by omega))
        (by rw [← hs]; ring_nf)
      convert hsub.mono (show p - 1 ≤ p by omega) using 3 <;> ring
    -- the top bit is set
    have r2 : GoodRun p ⟨2, p, tp⟩ 1 ⟨1, p - 1, tp'⟩ :=
      GoodRun.single le_rfl (step_two_false p tp hp)
    -- state 1 sweeps back over the cleared low bits
    have r3 : GoodRun p ⟨1, p - 1, tp'⟩ k ⟨1, p - 1 - k, tp'⟩ :=
      (sweep k (p - 1) tp' (fun i h1 h2 => by
        rw [htp', Function.update_of_ne (by omega)]; exact hz i (by omega) (by omega))).mono
        (by omega)
    -- bounce off the sentinel
    have r4 : GoodRun p ⟨1, p - 1 - k, tp'⟩ 1 ⟨2, p - k, tp'⟩ := by
      refine GoodRun.single (by simp only; omega) ?_
      rw [step_one_true]
      · congr 1; ring
      · rw [htp', Function.update_of_ne (by omega), ← hs]; ring_nf
    -- the low bits count to overflow again
    have r5 : GoodRun p ⟨2, p - k, tp'⟩ (counterTime k) ⟨2, p, tp'⟩ := by
      have hsub := ih (p - 1) tp' (fun i h1 h2 => by
          rw [htp', Function.update_of_ne (by omega)]; exact hz i (by omega) (by omega))
        (by rw [htp', Function.update_of_ne (by omega), ← hs]; ring_nf)
      convert hsub.mono (show p - 1 ≤ p by omega) using 3 <;> ring
    -- the top bit overflows and the head leaves the block
    have r6 : GoodRun p ⟨2, p, tp'⟩ 1 ⟨2, p + 1, tp⟩ := by
      refine GoodRun.single le_rfl ?_
      rw [step_two_true p tp' (by simp [htp'])]
      congr 1
      rw [htp', Function.update_idem, ← hp, Function.update_eq_self]
    have hall := ((((r1.trans r2).trans r3).trans r4).trans r5).trans r6
    convert hall using 2
    simp only [counterTime]; ring

/-- The initial tape of `2^m · o` (`o` odd) is blank on cells `-m+1, …, 0`. -/
lemma initTape_zero {m o : ℕ} (i : ℤ) (h1 : -(m : ℤ) < i) (h2 : i ≤ 0) :
    initTape (2 ^ m * o) i = false := by
  simp only [initTape, h2, decide_true, Bool.true_and]
  rw [mul_comm, Nat.testBit_mul_two_pow]
  simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
  intro hle; omega

/-- The initial tape of `2^m · o` (`o` odd) holds a `1` on cell `-m`. -/
lemma initTape_sentinel {m o : ℕ} (ho : Odd o) : initTape (2 ^ m * o) (-(m : ℤ)) = true := by
  simp only [initTape, neg_nonpos, Nat.cast_nonneg, decide_true, Bool.true_and, neg_neg,
    Int.toNat_natCast]
  rw [mul_comm, Nat.testBit_mul_two_pow]
  simp [Nat.testBit_zero, Nat.odd_iff.mp ho]

/-- On input `2^m · o` (`o` odd) machine 3626 first leaves the tape to the right after
`m + 1 + counterTime m` steps. -/
lemma run_two_pow_mul (m o : ℕ) (ho : Odd o) :
    GoodRun 0 (init (2 ^ m * o)) (m + 1 + counterTime m) ⟨2, 1, initTape (2 ^ m * o)⟩ := by
  set tp := initTape (2 ^ m * o) with htp
  have hz : ∀ i : ℤ, 0 - (m : ℤ) < i → i ≤ 0 → tp i = false := fun i h1 h2 =>
    initTape_zero i (by omega) h2
  have hs : tp (0 - (m : ℤ)) = true := by rw [zero_sub]; exact initTape_sentinel ho
  have r1 : GoodRun 0 ⟨1, 0, tp⟩ m ⟨1, 0 - m, tp⟩ := sweep m 0 tp hz
  have r2 : GoodRun 0 ⟨1, 0 - m, tp⟩ 1 ⟨2, 0 - m + 1, tp⟩ :=
    GoodRun.single (by simp only; omega) (step_one_true _ tp hs)
  have r3 : GoodRun 0 ⟨2, 0 - m + 1, tp⟩ (counterTime m) ⟨2, 0 + 1, tp⟩ :=
    counter m 0 tp hz hs
  have hall := (r1.trans r2).trans r3
  exact (by simpa using hall : GoodRun 0 ⟨1, 0, tp⟩ (m + 1 + counterTime m) ⟨2, 1, tp⟩)

/-- The halting time of machine 3626 on `2^m · o` (`o` odd) is `2^(m+2) - 3`, and the machine
does halt then. -/
theorem a393210_two_pow_mul (m o : ℕ) (ho : Odd o) :
    0 < (run 3626 (2 ^ m * o) (a393210 (2 ^ m * o))).head ∧
      (a393210 (2 ^ m * o) : ℤ) = 2 ^ (m + 2) - 3 := by
  have hrun := run_two_pow_mul m o ho
  have hex : ∃ t, 0 < (run 3626 (2 ^ m * o) t).head :=
    ⟨m + 1 + counterTime m, by simp [run, hrun.1]⟩
  have hfind : Nat.find hex = m + 1 + counterTime m := by
    rw [Nat.find_eq_iff]
    refine ⟨by simp [run, hrun.1], fun s hs => ?_⟩
    have hle := hrun.2 s hs
    simp only [run, not_lt]
    exact hle
  have ha : a393210 (2 ^ m * o) = m + 1 + counterTime m := by
    rw [a393210, haltingTime, dif_pos hex, hfind]
  refine ⟨by rw [ha]; simp [run, hrun.1], ?_⟩
  rw [ha]; push_cast; rw [counterTime_eq]; ring

/-- **Halting time of machine 3626.** For `n ≥ 1`, A393210(n) = `2^(v₂(n)+2) - 3`, and
machine 3626 indeed halts on `n` (the halting time is not the junk value). -/
theorem a393210_eq (n : ℕ) (hn : 0 < n) :
    0 < (run 3626 n (a393210 n)).head ∧ (a393210 n : ℤ) = 2 ^ (padicValNat 2 n + 2) - 3 := by
  obtain ⟨m, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hv : padicValNat 2 (2 ^ m * o) = m := by
    rw [padicValNat.mul (by positivity) (by rintro rfl; simp at ho), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd ho.not_two_dvd_nat, add_zero]
  rw [hv]
  exact a393210_two_pow_mul m o ho

/-- Ground truth (consequence of `a393210_two_pow_mul`): the first sixteen listed terms of A393210. -/
example : (List.range 16).map (fun i => (a393210 (i + 1) : ℤ)) =
    [1, 5, 1, 13, 1, 5, 1, 29, 1, 5, 1, 13, 1, 5, 1, 61] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil]
  simp only [List.cons.injEq, and_true]
  have h := fun m o (ho : Odd o) => (a393210_two_pow_mul m o ho).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h 0 1 (by decide)
  · simpa using h 1 1 (by decide)
  · simpa using h 0 3 (by decide)
  · simpa using h 2 1 (by decide)
  · simpa using h 0 5 (by decide)
  · simpa using h 1 3 (by decide)
  · simpa using h 0 7 (by decide)
  · simpa using h 3 1 (by decide)
  · simpa using h 0 9 (by decide)
  · simpa using h 1 5 (by decide)
  · simpa using h 0 11 (by decide)
  · simpa using h 2 3 (by decide)
  · simpa using h 0 13 (by decide)
  · simpa using h 1 7 (by decide)
  · simpa using h 0 15 (by decide)
  · simpa using h 4 1 (by decide)

/-! ## The divisor sum `∑_{d ∣ n} a(d)^2 φ(d)` -/

/-- The multiplicative summand `e ↦ -(μ(e) (-1)^e)` of A069517, as an arithmetic function. -/
def aSummand : ArithmeticFunction ℤ := ⟨fun e => -(μ e * (-1) ^ e), by simp⟩

lemma aSummand_apply (e : ℕ) : aSummand e = -(μ e * (-1) ^ e) := rfl

/-- `e ↦ -(μ(e) (-1)^e)` is multiplicative (coprime arguments are not both even). -/
lemma isMultiplicative_aSummand : aSummand.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [aSummand_apply], fun {m n} _ _ hmn => ?_⟩
  simp only [aSummand_apply, isMultiplicative_moebius.map_mul_of_coprime hmn, pow_mul]
  rcases Nat.even_or_odd m with hme | hmo
  · have hno : Odd n := by
      rcases Nat.even_or_odd n with hne | hno
      · exfalso
        have h2m : 2 ∣ m := even_iff_two_dvd.mp hme
        have h2n : 2 ∣ n := even_iff_two_dvd.mp hne
        have h21 := Nat.dvd_one.mp (hmn ▸ Nat.dvd_gcd h2m h2n)
        omega
      · exact hno
    rw [hme.neg_one_pow, one_pow, hno.neg_one_pow]; ring
  · rw [hmo.neg_one_pow]
    rcases Nat.even_or_odd n with hne | hno
    · rw [hne.neg_one_pow]; ring
    · rw [hno.neg_one_pow]; ring

/-- A069517 as an arithmetic function: the summatory function of `aSummand`. -/
def aFun : ArithmeticFunction ℤ := aSummand * (ζ : ArithmeticFunction ℤ)

lemma aFun_apply (n : ℕ) : aFun n = a069517 n := by
  rw [aFun, coe_mul_zeta_apply, a069517, ← Finset.sum_neg_distrib]
  rfl

/-- A069517 is multiplicative. -/
lemma isMultiplicative_aFun : aFun.IsMultiplicative :=
  isMultiplicative_aSummand.mul isMultiplicative_zeta.natCast

/-- Euler's totient as an integer-valued arithmetic function. -/
def totientInt : ArithmeticFunction ℤ := ⟨fun d => (Nat.totient d : ℤ), by simp⟩

/-- The integer-valued totient is multiplicative. -/
lemma isMultiplicative_totientInt : totientInt.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [totientInt], fun {m n} _ _ hmn => ?_⟩
  show ((Nat.totient (m * n) : ℕ) : ℤ) = (Nat.totient m : ℤ) * (Nat.totient n : ℤ)
  rw [Nat.totient_mul hmn]; push_cast; ring

/-- The divisor sum `n ↦ ∑_{d ∣ n} a(d)^2 φ(d)` as an arithmetic function. -/
def sumFun : ArithmeticFunction ℤ := ((aFun.pmul aFun).pmul totientInt) * (ζ : ArithmeticFunction ℤ)

lemma sumFun_apply (n : ℕ) :
    sumFun n = ∑ d ∈ n.divisors, a069517 d ^ 2 * (Nat.totient d : ℤ) := by
  rw [sumFun, coe_mul_zeta_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pmul_apply, pmul_apply, aFun_apply, sq]; rfl

/-- The divisor sum is multiplicative. -/
lemma isMultiplicative_sumFun : sumFun.IsMultiplicative :=
  ((isMultiplicative_aFun.pmul isMultiplicative_aFun).pmul isMultiplicative_totientInt).mul
    isMultiplicative_zeta.natCast

/-- For odd `d`, `a(d) = [d = 1]` (all divisors are odd, so `a(d) = ∑_{e ∣ d} μ(e)`). -/
lemma a069517_of_odd {d : ℕ} (hd : Odd d) : a069517 d = if d = 1 then 1 else 0 := by
  have h1 : (μ * (ζ : ArithmeticFunction ℤ)) d = if d = 1 then 1 else 0 := by
    rw [moebius_mul_coe_zeta, one_apply]
  rw [coe_mul_zeta_apply] at h1
  rw [← h1, a069517, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  have heo : Odd e := hd.of_dvd_nat (Nat.dvd_of_mem_divisors he)
  rw [heo.neg_one_pow]; ring

/-- `a(2^(j+1)) = 2`. -/
lemma a069517_two_pow (j : ℕ) : a069517 (2 ^ (j + 1)) = 2 := by
  rw [← aFun_apply, aFun, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction j with
  | zero => simp [Finset.sum_range_succ, aSummand_apply, moebius_apply_prime Nat.prime_two]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, aSummand_apply,
      moebius_apply_prime_pow Nat.prime_two (by omega)]
    simp

/-- On odd `o` the divisor sum is `1`. -/
lemma sumFun_odd {o : ℕ} (ho : Odd o) : sumFun o = 1 := by
  rw [sumFun_apply, Finset.sum_eq_single 1]
  · simp [a069517_of_odd odd_one]
  · intro d hd hd1
    rw [a069517_of_odd (ho.of_dvd_nat (Nat.dvd_of_mem_divisors hd)), if_neg hd1]
    simp
  · intro h; exact absurd (Nat.one_mem_divisors.mpr (by rintro rfl; simp at ho)) h

/-- On `2^m` the divisor sum is `1 + ∑_{j=1}^m 4 · 2^(j-1) = 4 · 2^m - 3`. -/
lemma sumFun_two_pow (m : ℕ) : sumFun (2 ^ m) = 4 * 2 ^ m - 3 := by
  rw [sumFun_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction m with
  | zero => simp [a069517_of_odd odd_one]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, a069517_two_pow, Nat.totient_prime_pow_succ Nat.prime_two]
    push_cast; ring

/-- `∑_{d ∣ 2^m o} a(d)^2 φ(d) = 4 · 2^m - 3` for odd `o`. -/
theorem sum_sq_mul_totient_two_pow_mul (m o : ℕ) (ho : Odd o) :
    ∑ d ∈ (2 ^ m * o).divisors, a069517 d ^ 2 * (Nat.totient d : ℤ) = 4 * 2 ^ m - 3 := by
  rw [← sumFun_apply, isMultiplicative_sumFun.map_mul_of_coprime, sumFun_odd ho, sumFun_two_pow,
    mul_one]
  exact Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    ho.not_two_dvd_nat)

/-! ## The conjecture -/

/-- **Bala's conjecture (A069517, Peter Bala, Sep 11 2026), proved.**

Verbatim: "Conjecture: Sum_{d | n} a(d)^2 * phi(d) = A393210(n)."

For every `n ≥ 1`, `∑_{d ∣ n} a(d)^2 φ(d)` equals the halting time of Wolfram's 2-state
2-symbol one-sided Turing machine 3626 started on `n` (A393210, offset 1).  The companion
statement `a393210_eq` shows the machine really halts on every `n ≥ 1`, so `a393210 n` is
the genuine halting time and not the junk value of `haltingTime`. -/
theorem sum_sq_mul_totient_eq_a393210 (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, a069517 d ^ 2 * (Nat.totient d : ℤ) = a393210 n := by
  obtain ⟨m, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  rw [sum_sq_mul_totient_two_pow_mul m o ho, (a393210_two_pow_mul m o ho).2]
  ring

end Candidates.A069517SumPhiHalting
