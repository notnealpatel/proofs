/-
# A071033: decimal encoding of Rule 94 rows

OEIS A071033, Karl V. Keller, Jr. (Oct 25 2021); Robert Price's cellular
automaton program (Feb 21 2016).
Starting from one ON cell on `ℤ`, each light-cone row is read as a decimal
word of zeroes and ones. For every `n > 1`, the parity-dependent floor
formulas follow from the exact cell shape and an alternating repunit sum.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A071033RuleSingleCell

/-! ## Definitions -/

/-- Wolfram's elementary rule 94: the new state of a cell whose left, centre and
right neighbours are `l`, `c`, `r` is bit number `4l + 2c + r` of the integer
`94` (Wolfram's numbering convention, as used by `CellularAutomaton[94, ...]`). -/
def rule94 (l c r : Bool) : Bool :=
  Nat.testBit 94 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- The evolution of rule 94 on `ℤ` started from a single ON cell at `0`:
`ca n i` is the state of cell `i` after `n` steps. -/
def ca : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | n + 1 => fun i => rule94 (ca n (i - 1)) (ca n i) (ca n (i + 1))

/-- A071033: row `n` of the rule 94 evolution, restricted to the `2n+1` cells
`-n, ..., n` and read as a decimal string (cell `-n` is the most significant
digit, cell `n - k` carries weight `10^k`). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if ca n ((n : ℤ) - (k : ℤ)) then 10 ^ k else 0

-- Example: Wolfram's rule-94 truth table (neighbourhoods 111, ..., 000
-- map to 0,1,0,1,1,1,1,0).
example : rule94 true true true = false ∧ rule94 true true false = true ∧
    rule94 true false true = false ∧ rule94 true false false = true ∧
    rule94 false true true = true ∧ rule94 false true false = true ∧
    rule94 false false true = true ∧ rule94 false false false = false := by decide

-- Example: the first listed terms of A071033.
example : a 0 = 1 := by decide
example : a 1 = 111 := by decide
example : a 2 = 11011 := by decide
example : a 3 = 1110111 := by decide
example : a 4 = 110101011 := by decide
example : a 5 = 11101010111 := by decide

/-! ## Cell characterization -/

/-- The explicit shape of row `n`: cell `i` is ON iff `-n ≤ i ≤ n` and
(`i` is odd, or `i ≤ 1 - n`, or `n - 1 ≤ i`). -/
def cellOn (n : ℕ) (i : ℤ) : Prop :=
  -(n : ℤ) ≤ i ∧ i ≤ n ∧ (i % 2 = 1 ∨ i ≤ 1 - n ∨ (n : ℤ) - 1 ≤ i)

/-- `cellOn n` is decidable (it is a Boolean combination of integer
comparisons). -/
instance (n : ℕ) : DecidablePred (cellOn n) := fun i => by unfold cellOn; infer_instance

/-- Rule 94 as a Boolean formula: ON iff some neighbour is ON, except for the
neighbourhoods `101` and `111`. -/
theorem rule94_spec (l c r : Bool) :
    rule94 l c r = ((l || c || r) && !(l && !c && r) && !(l && c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

/-- Every row of the rule 94 evolution from one ON cell has the explicit shape
`cellOn`. -/
theorem ca_eq (n : ℕ) (i : ℤ) : ca n i = decide (cellOn n i) := by
  induction n generalizing i with
  | zero =>
    simp only [ca, cellOn]
    congr 1
    apply propext
    omega
  | succ n ih =>
    simp only [ca, ih, rule94_spec]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp,
      decide_eq_true_eq, decide_eq_false_iff_not]
    simp only [cellOn]
    push_cast
    omega

/-- Digit `k` (weight `10^k`) of row `m + 2` is `1` iff `k ≤ 1`, or
`2m + 3 ≤ k`, or `m + k` is odd. -/
theorem ca_digit (m k : ℕ) (hk : k ≤ 2 * m + 4) :
    ca (m + 2) (((m + 2 : ℕ) : ℤ) - (k : ℤ)) = true ↔
      (k ≤ 1 ∨ 2 * m + 3 ≤ k ∨ (m + k) % 2 = 1) := by
  rw [ca_eq, decide_eq_true_eq, cellOn]
  push_cast
  omega

/-! ## The alternating repunit -/

/-- The alternating repunit of length `2m + 1`: the sum of `10^k` over
`k < 2m + 1` with `m + k` odd. -/
def altRepunit (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * m + 1), if (m + k) % 2 = 1 then 10 ^ k else 0

-- Example: `altRepunit 1 = 101`, `altRepunit 2 = 1010`, `altRepunit 3 = 1010101`.
example : altRepunit 1 = 101 ∧ altRepunit 2 = 1010 ∧ altRepunit 3 = 1010101 := by decide

/-- The one-step recurrence of the alternating repunit. -/
theorem altRepunit_succ (m : ℕ) :
    altRepunit (m + 1) = (if m % 2 = 0 then 1 else 0) + 10 * altRepunit m +
      (if m % 2 = 0 then 10 ^ (2 * m + 2) else 0) := by
  unfold altRepunit
  rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring, Finset.sum_range_succ',
    Finset.sum_range_succ, Finset.mul_sum]
  have hsum : ∀ k ∈ Finset.range (2 * m + 1),
      (if (m + 1 + (k + 1)) % 2 = 1 then 10 ^ (k + 1) else 0) =
        10 * (if (m + k) % 2 = 1 then 10 ^ k else 0) := by
    intro k _
    have hpar : (m + 1 + (k + 1)) % 2 = 1 ↔ (m + k) % 2 = 1 := by omega
    by_cases h : (m + k) % 2 = 1
    · rw [if_pos (hpar.mpr h), if_pos h, pow_succ]; ring
    · rw [if_neg (fun h' => h (hpar.mp h')), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hsum]
  by_cases hm : m % 2 = 0
  · have h1 : (m + 1 + (2 * m + 1 + 1)) % 2 = 1 := by omega
    have h2 : (m + 1 + 0) % 2 = 1 := by omega
    rw [if_pos h1, if_pos h2, if_pos hm, if_pos hm]
    ring
  · have h1 : ¬ (m + 1 + (2 * m + 1 + 1)) % 2 = 1 := by omega
    have h2 : ¬ (m + 1 + 0) % 2 = 1 := by omega
    rw [if_neg h1, if_neg h2, if_neg hm, if_neg hm]
    ring

/-- Closed form of the alternating repunit:
`99 * altRepunit m + 10 = 10 * 100^m` for even `m`, and
`99 * altRepunit m + 1 = 100^(m+1)` for odd `m`. -/
theorem altRepunit_closed (m : ℕ) :
    (m % 2 = 0 → 99 * altRepunit m + 10 = 10 * 100 ^ m) ∧
      (m % 2 = 1 → 99 * altRepunit m + 1 = 100 ^ (m + 1)) := by
  induction m with
  | zero => refine ⟨fun _ => ?_, fun h => absurd h (by norm_num)⟩; decide
  | succ m ih =>
    rw [altRepunit_succ]
    have hx : (10 : ℕ) ^ (2 * m + 2) = 100 * 100 ^ m := by
      rw [pow_add, pow_mul]; norm_num; ring
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · have hev := ih.1 hm
      rw [if_pos hm, if_pos hm, hx]
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      rw [pow_succ, pow_succ]
      nlinarith
    · have hod := ih.2 hm
      have hne : ¬ m % 2 = 0 := by omega
      rw [if_neg hne, if_neg hne]
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      rw [pow_succ] at hod ⊢
      omega

/-! ## Digit decomposition and the closed forms -/

/-- Row `m + 2` read in decimal: `11 + 10^(2m+3) + 10^(2m+4) + 100 * altRepunit m`. -/
theorem a_decomp (m : ℕ) :
    a (m + 2) = 11 + 10 ^ (2 * m + 3) + 10 ^ (2 * m + 4) + 100 * altRepunit m := by
  unfold a altRepunit
  rw [show 2 * (m + 2) + 1 = (2 * m + 1) + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have hmid : ∀ k ∈ Finset.range (2 * m + 1),
      (if ca (m + 2) (((m + 2 : ℕ) : ℤ) - ((k + 1 + 1 : ℕ) : ℤ)) then 10 ^ (k + 1 + 1) else 0) =
        100 * (if (m + k) % 2 = 1 then 10 ^ k else 0) := by
    intro k hk
    have hk' : k < 2 * m + 1 := Finset.mem_range.mp hk
    have hiff := ca_digit m (k + 1 + 1) (by omega)
    have hpar : (k + 1 + 1 ≤ 1 ∨ 2 * m + 3 ≤ k + 1 + 1 ∨ (m + (k + 1 + 1)) % 2 = 1) ↔
        (m + k) % 2 = 1 := by omega
    by_cases h : (m + k) % 2 = 1
    · rw [if_pos (hiff.mpr (hpar.mpr h)), if_pos h]; ring
    · have hf : ca (m + 2) (((m + 2 : ℕ) : ℤ) - ((k + 1 + 1 : ℕ) : ℤ)) = false := by
        rw [← Bool.not_eq_true]; exact fun h' => h (hpar.mp (hiff.mp h'))
      rw [hf, if_neg h, mul_zero]
      rfl
  rw [Finset.sum_congr rfl hmid]
  have h0 : ca (m + 2) (((m + 2 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) = true :=
    (ca_digit m 0 (by omega)).mpr (by omega)
  have h1 : ca (m + 2) (((m + 2 : ℕ) : ℤ) - ((0 + 1 : ℕ) : ℤ)) = true :=
    (ca_digit m (0 + 1) (by omega)).mpr (by omega)
  have h3 : ca (m + 2) (((m + 2 : ℕ) : ℤ) - ((2 * m + 1 + 1 + 1 : ℕ) : ℤ)) = true :=
    (ca_digit m _ (by omega)).mpr (by omega)
  have h4 : ca (m + 2) (((m + 2 : ℕ) : ℤ) - ((2 * m + 1 + 1 + 1 + 1 : ℕ) : ℤ)) = true :=
    (ca_digit m _ (by omega)).mpr (by omega)
  rw [if_pos h0, if_pos h1, if_pos h3, if_pos h4]
  ring

/-- Power bookkeeping in terms of `100^m`. -/
theorem pow_facts (m : ℕ) :
    (10 : ℕ) ^ (2 * m + 3) = 1000 * 100 ^ m ∧ (10 : ℕ) ^ (2 * m + 4) = 10000 * 100 ^ m ∧
      (100 : ℕ) ^ (m + 2) = 10000 * 100 ^ m ∧ (100 : ℕ) ^ (m + 1) = 100 * 100 ^ m := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pow_add] <;> (try rw [pow_mul]) <;> norm_num <;> ring

/-- Keller's formula, even case: for even `n > 1`,
`a(n) = floor((1090 * 100^n + 10) / 990) + 1`. -/
theorem a_even (n : ℕ) (hn : 1 < n) (heven : Even n) :
    a n = (1090 * 100 ^ n + 10) / 990 + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m % 2 = 0 := by rcases heven with ⟨r, hr⟩; omega
  have hO := (altRepunit_closed m).1 hm
  obtain ⟨p3, p4, p2, -⟩ := pow_facts m
  rw [a_decomp, p3, p4, p2]
  omega

/-- Keller's formula, odd case: for odd `n > 1`,
`a(n) = floor((1099 * 100^n + 9090) / 990) + 1`. -/
theorem a_odd (n : ℕ) (hn : 1 < n) (hodd : Odd n) :
    a n = (1099 * 100 ^ n + 9090) / 990 + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m % 2 = 1 := by rcases hodd with ⟨r, hr⟩; omega
  have hO := (altRepunit_closed m).2 hm
  obtain ⟨p3, p4, p2, p1⟩ := pow_facts m
  rw [p1] at hO
  rw [a_decomp, p3, p4, p2]
  omega

/-! ## The conjecture -/

/-- Keller's A071033 floor formulas for the decimal encoding of Rule 94
rows, for `n > 1`. Natural division supplies the floor; the bound is
essential, since the formulas fail at the initial rows `n = 0,1`. -/
theorem keller_conjecture (n : ℕ) (hn : 1 < n) :
    a n = if Odd n then (1099 * 100 ^ n + 9090) / 990 + 1
      else (1090 * 100 ^ n + 10) / 990 + 1 := by
  by_cases hodd : Odd n
  · rw [if_pos hodd]
    exact a_odd n hn hodd
  · rw [if_neg hodd]
    exact a_even n hn (Nat.not_odd_iff_even.mp hodd)

/-! ## Examples -/

-- The guard `1 < n` is load-bearing: at `n = 1` the odd formula gives 121 ≠ 111,
-- and at `n = 0` the even formula gives 2 ≠ 1.
example : a 1 ≠ (1099 * 100 ^ 1 + 9090) / 990 + 1 := by decide
example : a 0 ≠ (1090 * 100 ^ 0 + 10) / 990 + 1 := by decide

-- Non-vacuity: the hypotheses of both cases are jointly satisfiable.
example : 1 < 2 ∧ Even 2 ∧ 1 < 3 ∧ Odd 3 := by decide

end Candidates.A071033RuleSingleCell
