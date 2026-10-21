/-
# Verrill: `‖((b+1)n) ⊖_b n‖ = n ⊕_{-b} (-n)`; for `b = 2`, OEIS A178729

## Source

H. A. Verrill, *Note on the negative base xor sequence `n ⊕_{-b} (-n)`*,
arXiv:2506.09509 (retrieved with `fetch 2506.09509`, 2026-10-21).

* Section 1, equation (1.1) (`equ:originalconjecture`), the A178729 conjecture:
  "It was conjectured [A178729] that for non-negative integers `n`,
  `n ⊕ (3n) = n ⊕_{-2} (-n)`", where `⊕` is bitwise XOR and
  `(∑ aᵢ (-2)ⁱ) ⊕_{-2} (∑ bᵢ (-2)ⁱ) = ∑ ((aᵢ + bᵢ) mod 2) 2ⁱ`.
* Definition `def:ominus`: for `α = ∑ aᵢ bⁱ`, `β = ∑ bᵢ bⁱ` (base `b`),
  `α ⊖_b β = ∑ ((aᵢ - bᵢ) mod b) bⁱ`; for integers `α = ∑ aᵢ (-b)ⁱ`,
  `β = ∑ bᵢ (-b)ⁱ` with `aᵢ, bᵢ ∈ {0, …, b-1}`,
  `α ⊕_{-b} β = ∑ ((aᵢ + bᵢ) mod b) bⁱ`; and `‖α‖ = ∑ min(aᵢ, 1) bⁱ`.
* Theorem `thm:main` (verbatim): "For all positive integers `b` and `n`, we have
  `‖((b+1)n) ⊖_b n‖ = n ⊕_{-b} (-n)`" (the double bar is the paper's
  `\overline{\overline{·}}`). "In the case that `b = 2`, (generalresult) is exactly the
  same as (originalconjecture)."

OEIS A178729 (`oeis show A178729`, 2026-10-21): "a(n) = n XOR 3n, where XOR is bitwise
XOR." FORMULA: "a(n) = A005351(n) XOR A005352(n) (conjectured). Proved by Verrill link."
A005351: "Base -2 representation for n regarded as base 2, then evaluated."
A005352: "Base -2 representation of -n reinterpreted as binary." (offset 1).

## Status

Proved in the paper (by finite transducers). Formalized here, date 2026-10-21, with no
`sorry`. Base `b = 1` has no base-`b` expansion, so the general theorem assumes `2 ≤ b`;
`n = 0` is included (both sides are `0`).

## Proof route

The paper's two three-state machines become a simultaneous strong induction on `m`
(input read in base `b`, `m = b q + a`) of
`L₀ = R₁`, `L_c = R₂` (`0 < c < b`), `L_b(m) = R₁(m + 1)`, where
`L_c(m) = ‖((b+1)m + c) ⊖_b m‖`, `R₁(m) = m ⊕_{-b} (-m)`, `R₂(m) = (m+1) ⊕_{-b} (-m)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.VerrillBaseBDigitIdentity

/-! ## Definitions and digit recursions -/

/-- Termination measure for the base `-b` division step `z ↦ -(z / b)`:
`2 |z| + [z < 0]`. It strictly decreases on every nonzero `z` when `2 ≤ b`. -/
def negaMeasure (z : ℤ) : ℕ := 2 * z.natAbs + if z < 0 then 1 else 0

/-- For `2 ≤ b`, the base `-b` step `z ↦ -(z / b)` never increases `negaMeasure`, and
strictly decreases it when `z ≠ 0`. -/
theorem negaMeasure_step (b : ℕ) (hb : 2 ≤ b) (z : ℤ) :
    negaMeasure (-(z / b)) ≤ negaMeasure z ∧ (z ≠ 0 → negaMeasure (-(z / b)) < negaMeasure z) := by
  have hb0 : (0 : ℤ) < b := by omega
  have h1 : (b : ℤ) * (z / b) ≤ z := Int.mul_ediv_self_le hb0.ne'
  have h2 : z < (b : ℤ) * (z / b) + b := Int.lt_mul_ediv_self_add hb0
  have hb2 : (2 : ℤ) ≤ b := by exact_mod_cast hb
  rcases le_or_gt 0 (z / b) with hk | hk
  · have h3 : 2 * (z / b) ≤ (b : ℤ) * (z / b) := by nlinarith
    unfold negaMeasure
    constructor <;> split_ifs <;> omega
  · have h3 : (b : ℤ) * (z / b) + b ≤ 2 * (z / b) + 2 := by nlinarith
    unfold negaMeasure
    constructor <;> split_ifs <;> omega

/-- Verrill's `x ⊖_b y` (Definition `def:ominus`, eq. (minusb)): write `x = ∑ aᵢ bⁱ` and
`y = ∑ bᵢ bⁱ` in base `b` and return `∑ ((aᵢ - bᵢ) mod b) bⁱ`. The lowest digits are
`x % b`, `y % b`; the digit `(aᵢ - bᵢ) mod b` is computed in `ℕ` as
`(aᵢ + (b - bᵢ)) % b` (no truncation since `bᵢ < b`, see `digitSub_digit_cast`). Junk value `0`
for `b < 2`. -/
def digitSub (b x y : ℕ) : ℕ :=
  if b < 2 ∨ (x = 0 ∧ y = 0) then 0
  else (x % b + (b - y % b)) % b + b * digitSub b (x / b) (y / b)
termination_by x + y
decreasing_by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · have hy : 0 < y := by omega
    have := Nat.div_lt_self hy (by omega : 1 < b)
    subst hx; simp only [Nat.zero_div, zero_add]; omega
  · have := Nat.div_lt_self hx (by omega : 1 < b)
    have := Nat.div_le_self y b
    omega

/-- Verrill's double bar `‖α‖ = ∑ min(aᵢ, 1) bⁱ` for `α = ∑ aᵢ bⁱ` in base `b`:
every nonzero base-`b` digit is replaced by `1`. Uses Mathlib's `Nat.digits`/`Nat.ofDigits`. -/
def digitIndicator (b x : ℕ) : ℕ := Nat.ofDigits b ((Nat.digits b x).map (fun d => min d 1))

/-- Verrill's `α ⊕_{-b} β` (Definition `def:ominus`, eq. (oplus-b)): write `α = ∑ aᵢ (-b)ⁱ`
and `β = ∑ bᵢ (-b)ⁱ` with digits in `{0, …, b-1}` and return `∑ ((aᵢ + bᵢ) mod b) bⁱ`.
The base `-b` digits are produced by the standard division algorithm: the lowest digit
of `z` is `z % b ∈ [0, b)` and the remaining digits are those of `-(z / b)`, since
`z = z % b + (-b) * (-(z / b))` (see `negaStep_spec`). Junk value `0` for `b < 2`. -/
def negaXor (b : ℕ) (α β : ℤ) : ℕ :=
  if b < 2 ∨ (α = 0 ∧ β = 0) then 0
  else ((α % b + β % b) % b).toNat + b * negaXor b (-(α / b)) (-(β / b))
termination_by negaMeasure α + negaMeasure β
decreasing_by
  have hb : 2 ≤ b := by omega
  have hα := negaMeasure_step b hb α
  have hβ := negaMeasure_step b hb β
  by_cases ha : α = 0
  · have := hβ.2 (by omega); omega
  · have := hα.2 ha; omega

example : (List.range 15).map (fun n : ℕ => negaXor 3 n (-n)) =
    [0, 3, 3, 9, 12, 12, 9, 30, 30, 27, 30, 30, 36, 39, 39] := by decide +kernel
example : (List.range 15).map (fun n : ℕ => digitIndicator 3 (digitSub 3 (4*n) n)) =
    [0, 3, 3, 9, 12, 12, 9, 30, 30, 27, 30, 30, 36, 39, 39] := by decide +kernel

/-- `0 ⊖_b 0 = 0`. -/
theorem digitSub_zero_zero (b : ℕ) : digitSub b 0 0 = 0 := by
  rw [digitSub]; simp

/-- Digit recursion for `⊖_b`: lowest digit `(x % b - y % b) mod b`, remaining digits
`(x / b) ⊖_b (y / b)`. Valid for all `x y` (including `0, 0`). -/
theorem digitSub_rec (b : ℕ) (hb : 2 ≤ b) (x y : ℕ) :
    digitSub b x y = (x % b + (b - y % b)) % b + b * digitSub b (x / b) (y / b) := by
  rw [digitSub]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ : x = 0 ∧ y = 0 := by omega
    simp [digitSub_zero_zero]
  · rfl

/-- Digit recursion for the double bar: `‖x‖ = min (x % b) 1 + b ‖x / b‖`. -/
theorem digitIndicator_rec (b : ℕ) (hb : 2 ≤ b) (x : ℕ) :
    digitIndicator b x = min (x % b) 1 + b * digitIndicator b (x / b) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [digitIndicator]
  · rw [digitIndicator, Nat.digits_def' (by omega) hx, List.map_cons, Nat.ofDigits_cons]
    rfl

/-- `0 ⊕_{-b} 0 = 0`. -/
theorem negaXor_zero_zero (b : ℕ) : negaXor b 0 0 = 0 := by
  rw [negaXor]; simp

/-- Digit recursion for `⊕_{-b}`: lowest digit `(α % b + β % b) mod b`, remaining digits
`(-(α / b)) ⊕_{-b} (-(β / b))`. Valid for all `α β` (including `0, 0`). -/
theorem negaXor_rec (b : ℕ) (hb : 2 ≤ b) (α β : ℤ) :
    negaXor b α β = ((α % b + β % b) % b).toNat + b * negaXor b (-(α / b)) (-(β / b)) := by
  rw [negaXor]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ : α = 0 ∧ β = 0 := by omega
    simp [negaXor_zero_zero]
  · rfl

/-- Induction principle along the simultaneous base `-b` division of a pair of integers. -/
theorem negaPair_induction (b : ℕ) (hb : 2 ≤ b) (P : ℤ → ℤ → Prop)
    (step : ∀ α β, (¬(α = 0 ∧ β = 0) → P (-(α / b)) (-(β / b))) → P α β) (α β : ℤ) :
    P α β := by
  suffices key : ∀ N : ℕ, ∀ α β : ℤ, negaMeasure α + negaMeasure β < N → P α β from
    key _ α β (Nat.lt_succ_self _)
  intro N
  induction N with
  | zero => intro α β h; omega
  | succ N ih =>
    intro α β hN
    apply step
    intro hne
    apply ih
    have hα := negaMeasure_step b hb α
    have hβ := negaMeasure_step b hb β
    by_cases ha : α = 0
    · have := hβ.2 (by omega); omega
    · have := hα.2 ha; omega

/-- `⊕_{-b}` is commutative. -/
theorem negaXor_comm (b : ℕ) (hb : 2 ≤ b) (α β : ℤ) : negaXor b α β = negaXor b β α := by
  induction α, β using negaPair_induction b hb with
  | step α β ih =>
    by_cases h : α = 0 ∧ β = 0
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · rw [negaXor_rec b hb α β, negaXor_rec b hb β α, add_comm (α % (b : ℤ)), ih h]


/-- Euclidean quotient and remainder by `b` of `z = r + b k` with `0 ≤ r < b`. -/
theorem ediv_emod_of_eq (b : ℕ) (hb : 2 ≤ b) (z k r : ℤ) (h0 : 0 ≤ r) (h1 : r < b)
    (hz : z = r + b * k) : z / b = k ∧ z % b = r :=
  (Int.ediv_emod_unique (by omega)).2 ⟨hz.symm, h0, h1⟩

/-- Transducer state `R₁(m) = m ⊕_{-b} (-m)` (state `00` of Lemma `lem:1`). -/
def stateR1 (b m : ℕ) : ℕ := negaXor b (m : ℤ) (-(m : ℤ))

/-- Transducer state `R₂(m) = (m + 1) ⊕_{-b} (-m)` (state `10` of Lemma `lem:1`). -/
def stateR2 (b m : ℕ) : ℕ := negaXor b ((m : ℤ) + 1) (-(m : ℤ))

/-- One step of the right-hand transducer from state `R₁`: on input digit `a`, output `0`
and move to `R₁` if `a = 0`, else to `R₂`. -/
theorem stateR1_rec (b : ℕ) (hb : 2 ≤ b) (q a : ℕ) (ha : a < b) :
    stateR1 b (b * q + a) = b * (if a = 0 then stateR1 b q else stateR2 b q) := by
  have hz : ((b * q + a : ℕ) : ℤ) = (a : ℤ) + b * q := by push_cast; ring
  obtain ⟨d1, m1⟩ := ediv_emod_of_eq b hb _ q a (by omega) (by omega) hz
  rw [stateR1, negaXor_rec b hb, d1, m1]
  split_ifs with h0
  · subst h0
    have hz' : -((b * q + 0 : ℕ) : ℤ) = 0 + b * (-(q : ℤ)) := by push_cast; ring
    obtain ⟨d2, m2⟩ := ediv_emod_of_eq b hb _ (-(q : ℤ)) 0 le_rfl (by omega) hz'
    rw [d2, m2, neg_neg, negaXor_comm b hb]
    simp [stateR1]
  · have hz' : -((b * q + a : ℕ) : ℤ) = ((b : ℤ) - a) + b * (-(q : ℤ) - 1) := by
      push_cast; ring
    obtain ⟨d2, m2⟩ := ediv_emod_of_eq b hb _ (-(q : ℤ) - 1) (b - a) (by omega) (by omega) hz'
    have hdig : (((a : ℤ) + ((b : ℤ) - a)) % b).toNat = 0 := by simp
    have hneg : -(-(q : ℤ) - 1) = (q : ℤ) + 1 := by ring
    rw [d2, m2, hdig, hneg, zero_add, negaXor_comm b hb, stateR2]

/-- One step of the right-hand transducer from state `R₂`: on input digit `a`, output `1`
and move to `R₁` if `a = 0`, to `R₂` if `0 < a < b - 1`, and to `R₁(· + 1)` (state `11`)
if `a = b - 1`. -/
theorem stateR2_rec (b : ℕ) (hb : 2 ≤ b) (q a : ℕ) (ha : a < b) :
    stateR2 b (b * q + a) = 1 + b * (if a = 0 then stateR1 b q
      else if a + 1 < b then stateR2 b q else stateR1 b (q + 1)) := by
  have hone : ((1 : ℤ) % b).toNat = 1 := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]; rfl
  rw [stateR2, negaXor_rec b hb]
  split_ifs with h0 h1
  · subst h0
    have hz : ((b * q + 0 : ℕ) : ℤ) + 1 = 1 + b * (q : ℤ) := by push_cast; ring
    have hz' : -((b * q + 0 : ℕ) : ℤ) = 0 + b * (-(q : ℤ)) := by push_cast; ring
    obtain ⟨d1, m1⟩ := ediv_emod_of_eq b hb _ q 1 (by omega) (by omega) hz
    obtain ⟨d2, m2⟩ := ediv_emod_of_eq b hb _ (-(q : ℤ)) 0 le_rfl (by omega) hz'
    rw [d1, m1, d2, m2, neg_neg, add_zero, hone, negaXor_comm b hb, stateR1]
  · have hz : ((b * q + a : ℕ) : ℤ) + 1 = ((a : ℤ) + 1) + b * (q : ℤ) := by push_cast; ring
    have hz' : -((b * q + a : ℕ) : ℤ) = ((b : ℤ) - a) + b * (-(q : ℤ) - 1) := by
      push_cast; ring
    obtain ⟨d1, m1⟩ := ediv_emod_of_eq b hb _ q ((a : ℤ) + 1) (by omega) (by omega) hz
    obtain ⟨d2, m2⟩ := ediv_emod_of_eq b hb _ (-(q : ℤ) - 1) (b - a) (by omega) (by omega) hz'
    have hsum : (a : ℤ) + 1 + ((b : ℤ) - a) = 1 + b * 1 := by ring
    have hneg : -(-(q : ℤ) - 1) = (q : ℤ) + 1 := by ring
    rw [d1, m1, d2, m2, hsum, Int.add_mul_emod_self_left, hone, hneg, negaXor_comm b hb,
      stateR2]
  · have hab : a + 1 = b := by omega
    have hz : ((b * q + a : ℕ) : ℤ) + 1 = 0 + b * ((q : ℤ) + 1) := by
      rw [← hab]; push_cast; ring
    have hz' : -((b * q + a : ℕ) : ℤ) = 1 + b * (-(q : ℤ) - 1) := by
      rw [← hab]; push_cast; ring
    obtain ⟨d1, m1⟩ := ediv_emod_of_eq b hb _ ((q : ℤ) + 1) 0 le_rfl (by omega) hz
    obtain ⟨d2, m2⟩ := ediv_emod_of_eq b hb _ (-(q : ℤ) - 1) 1 (by omega) (by omega) hz'
    have hneg : -(-(q : ℤ) - 1) = (q : ℤ) + 1 := by ring
    rw [d1, m1, d2, m2, zero_add, hone, hneg, negaXor_comm b hb, stateR1]
    push_cast; rfl

/-- Transducer state `L_c(m) = ‖((b + 1) m + c) ⊖_b m‖` with multiplication carry `c`. -/
def stateL (b c m : ℕ) : ℕ := digitIndicator b (digitSub b ((b + 1) * m + c) m)

/-- The digit of `((b+1)m + c) ⊖_b m` at the current position is `c mod b`:
`((a + c) % b - a) mod b = c % b` for `a < b`, `c ≤ b`. -/
theorem sub_digit_eq (b : ℕ) (a c : ℕ) (ha : a < b) (hc : c ≤ b) :
    ((a + c) % b + (b - a)) % b = c % b := by
  rcases lt_or_ge (a + c) b with h | h
  · rw [Nat.mod_eq_of_lt h, show a + c + (b - a) = c + b by omega, Nat.add_mod_right]
  · have e : (a + c) % b = a + c - b := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [e, show a + c - b + (b - a) = c by omega]

/-- One step of the left-hand transducer (eq. (t2)): from carry `c ≤ b` on input digit
`a < b`, output `min (c mod b) 1` and move to carry `a + ⌊(a + c) / b⌋`. -/
theorem stateL_rec (b : ℕ) (hb : 2 ≤ b) (c q a : ℕ) (hc : c ≤ b) (ha : a < b) :
    stateL b c (b * q + a) = min (c % b) 1 + b * stateL b (a + (a + c) / b) q := by
  have hb0 : 0 < b := by omega
  have hx : (b + 1) * (b * q + a) + c = (a + c) + b * ((b + 1) * q + a) := by ring
  have hxm : ((b + 1) * (b * q + a) + c) % b = (a + c) % b := by
    rw [hx, Nat.add_mul_mod_self_left]
  have hxd : ((b + 1) * (b * q + a) + c) / b = (b + 1) * q + (a + (a + c) / b) := by
    rw [hx, Nat.add_mul_div_left _ _ hb0]; ring
  have hym : (b * q + a) % b = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have hyd : (b * q + a) / b = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hb0, Nat.div_eq_of_lt ha, zero_add]
  set R := digitSub b ((b + 1) * q + (a + (a + c) / b)) q with hR
  have hsub : digitSub b ((b + 1) * (b * q + a) + c) (b * q + a) = c % b + b * R := by
    rw [digitSub_rec b hb, hxm, hym, hxd, hyd, sub_digit_eq b a c ha hc]
  have hdm : (c % b + b * R) % b = c % b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  have hdd : (c % b + b * R) / b = R := by
    rw [Nat.add_mul_div_left _ _ hb0, Nat.div_eq_of_lt (Nat.mod_lt _ hb0), zero_add]
  rw [stateL, hsub, digitIndicator_rec b hb, hdm, hdd, stateL]


/-- `stateL_rec` at `m = 0`. -/
theorem stateL_rec_zero (b : ℕ) (hb : 2 ≤ b) (c : ℕ) (hc : c ≤ b) :
    stateL b c 0 = min (c % b) 1 + b * stateL b (c / b) 0 := by
  simpa using stateL_rec b hb c 0 0 hc (by omega)

/-- The two transducers agree, state by state (proof of Theorem `thm:main`):
`L₀ = R₁`, `L_c = R₂` for `0 < c < b`, and `L_b(m) = R₁(m + 1)`. -/
theorem main_triple (b : ℕ) (hb : 2 ≤ b) (m : ℕ) :
    stateL b 0 m = stateR1 b m ∧
    (∀ c, 0 < c → c < b → stateL b c m = stateR2 b m) ∧
    stateL b b m = stateR1 b (m + 1) := by
  have hb0 : 0 < b := by omega
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- base case `m = 0`
    have hL0 : stateL b 0 0 = 0 := by
      simp [stateL, digitSub_zero_zero, digitIndicator]
    have hR10 : stateR1 b 0 = 0 := by
      simp [stateR1, negaXor_zero_zero]
    have hLc : ∀ c, 0 < c → c < b → stateL b c 0 = 1 := by
      intro c hc0 hcb
      rw [stateL_rec_zero b hb c hcb.le, Nat.mod_eq_of_lt hcb, Nat.div_eq_of_lt hcb, hL0]
      omega
    have hR20 : stateR2 b 0 = 1 := by
      simpa [hR10] using stateR2_rec b hb 0 0 hb0
    refine ⟨by rw [hL0, hR10], fun c hc0 hcb => by rw [hLc c hc0 hcb, hR20], ?_⟩
    have hR11 : stateR1 b 1 = b := by
      simpa [hR20] using stateR1_rec b hb 0 1 (by omega)
    rw [stateL_rec_zero b hb b le_rfl, Nat.mod_self, Nat.div_self hb0, hLc 1 one_pos (by omega),
      hR11]
    simp
  · -- inductive step `m = b q + a`
    obtain ⟨q, a, ha, rfl⟩ : ∃ q a, a < b ∧ m = b * q + a :=
      ⟨m / b, m % b, Nat.mod_lt _ hb0, (Nat.div_add_mod m b).symm⟩
    have hbq : 2 * q ≤ b * q := Nat.mul_le_mul_right q hb
    obtain ⟨ihA, ihB, ihC⟩ := ih q (by omega)
    refine ⟨?_, ?_, ?_⟩
    · -- `L₀ = R₁`
      rw [stateL_rec b hb 0 q a (by omega) ha, stateR1_rec b hb q a ha, Nat.zero_mod,
        add_zero, Nat.div_eq_of_lt ha, add_zero]
      split_ifs with h0
      · subst h0; rw [ihA]; simp
      · rw [ihB a (by omega) ha]; simp
    · -- `L_c = R₂` for `0 < c < b`
      intro c hc0 hcb
      rw [stateL_rec b hb c q a hcb.le ha, stateR2_rec b hb q a ha, Nat.mod_eq_of_lt hcb,
        show min c 1 = 1 by omega]
      split_ifs with h0 h1
      · subst h0; rw [zero_add, zero_add, Nat.div_eq_of_lt hcb, ihA]
      · have hle : (a + c) / b < 2 := Nat.div_lt_of_lt_mul (by omega)
        have hpos : 0 < a + (a + c) / b :=
          lt_of_lt_of_le (Nat.pos_of_ne_zero h0) (Nat.le_add_right _ _)
        rw [ihB _ hpos (by omega)]
      · have hab : a + 1 = b := by omega
        have hq : (a + c) / b = 1 :=
          Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
        rw [hq, hab, ihC]
    · -- `L_b(m) = R₁(m + 1)`
      have hq : (a + b) / b = 1 := by
        rw [Nat.add_div_right _ hb0, Nat.div_eq_of_lt ha]
      rw [stateL_rec b hb b q a le_rfl ha, Nat.mod_self, hq]
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt ha) with h1 | h1
      · rw [show b * q + a + 1 = b * q + (a + 1) by ring, stateR1_rec b hb q (a + 1) h1,
          if_neg (by omega), ihB _ (by omega) h1]
        simp
      · have hab : a + 1 = b := h1
        rw [show b * q + a + 1 = b * (q + 1) + 0 by rw [Nat.add_assoc, hab]; ring,
          stateR1_rec b hb (q + 1) 0 hb0, if_pos rfl, hab, ihC]
        simp


/-- The base `-2` (negabinary) digit string of the integer `x`, read as a binary numeral.
The least digit is `x % 2 ∈ {0, 1}` and the remaining digits are those of `-(x / 2)`,
since `x = x % 2 + (-2) * (-(x / 2))`. -/
def negabin (x : ℤ) : ℕ :=
  if x = 0 then 0 else (x % 2).toNat + 2 * negabin (-(x / 2))
termination_by 2 * x.natAbs + (if x < 0 then 1 else 0)
decreasing_by
  split_ifs <;> omega

/-- Digit recursion for `negabin`, valid for all `x` (including `0`). -/
theorem negabin_rec (x : ℤ) : negabin x = (x % 2).toNat + 2 * negabin (-(x / 2)) := by
  rw [negabin]
  split_ifs with h
  · subst h; rw [negabin]; simp
  · rfl

/-- Bit recursion for `XOR`: `x XOR y = ((x % 2 + y % 2) % 2) + 2 ((x/2) XOR (y/2))`. -/
theorem xor_rec (x y : ℕ) : x ^^^ y = (x % 2 + y % 2) % 2 + 2 * ((x / 2) ^^^ (y / 2)) := by
  conv_lhs => rw [← Nat.div_add_mod x 2, ← Nat.div_add_mod y 2]
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
    simp only [hx, hy]
  · simpa [Nat.bit_val, add_comm] using Nat.xor_bit false (x / 2) false (y / 2)
  · simpa [Nat.bit_val, add_comm] using Nat.xor_bit false (x / 2) true (y / 2)
  · simpa [Nat.bit_val, add_comm] using Nat.xor_bit true (x / 2) false (y / 2)
  · simpa [Nat.bit_val, add_comm] using Nat.xor_bit true (x / 2) true (y / 2)

/-- In base `2` every digit is `0` or `1`, so the double bar is the identity. -/
theorem digitIndicator_two (x : ℕ) : digitIndicator 2 x = x := by
  rw [digitIndicator]
  have hmap : (Nat.digits 2 x).map (fun d => min d 1) = Nat.digits 2 x := by
    conv_rhs => rw [← List.map_id (Nat.digits 2 x)]
    refine List.map_congr_left fun d hd => ?_
    have := Nat.digits_lt_base (by norm_num) hd
    simp only [id]; omega
  rw [hmap, Nat.ofDigits_digits]

/-- In base `2`, `x ⊖_2 y = x XOR y`. -/
theorem digitSub_two (x y : ℕ) : digitSub 2 x y = x ^^^ y := by
  induction h : x + y using Nat.strong_induction_on generalizing x y with
  | _ s ih =>
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0; simp [digitSub_zero_zero]
  · rw [digitSub_rec 2 le_rfl, xor_rec, ih (x / 2 + y / 2) (by omega) _ _ rfl]
    congr 1
    omega

/-- In base `-2`, `α ⊕_{-2} β = negabin α XOR negabin β`. -/
theorem negaXor_two (α β : ℤ) : negaXor 2 α β = negabin α ^^^ negabin β := by
  induction α, β using negaPair_induction 2 le_rfl with
  | step α β ih =>
    by_cases h : α = 0 ∧ β = 0
    · obtain ⟨rfl, rfl⟩ := h; simp [negaXor_zero_zero, negabin]
    · rw [negaXor_rec 2 le_rfl, ih h]
      simp only [Nat.cast_ofNat]
      conv_rhs => rw [negabin_rec α, negabin_rec β, xor_rec]
      have h1 : ((α % 2).toNat + 2 * negabin (-(α / 2))) % 2 = (α % 2).toNat := by omega
      have h2 : ((β % 2).toNat + 2 * negabin (-(β / 2))) % 2 = (β % 2).toNat := by omega
      have h3 : ((α % 2).toNat + 2 * negabin (-(α / 2))) / 2 = negabin (-(α / 2)) := by omega
      have h4 : ((β % 2).toNat + 2 * negabin (-(β / 2))) / 2 = negabin (-(β / 2)) := by omega
      rw [h1, h2, h3, h4]
      congr 1
      omega

/-! ## Faithfulness of the digit algorithms -/

/-- The base `-b` division step is a valid expansion step: `z = (z % b) + (-b) · (-(z / b))`
with lowest digit `z % b ∈ [0, b)`. -/
theorem negaStep_spec (b : ℕ) (hb : 2 ≤ b) (z : ℤ) :
    z = z % b + (-(b : ℤ)) * (-(z / b)) ∧ 0 ≤ z % b ∧ z % b < b := by
  have hb0 : (b : ℤ) ≠ 0 := by omega
  refine ⟨?_, Int.emod_nonneg _ hb0, Int.emod_lt_of_pos _ (by omega)⟩
  rw [neg_mul_neg]
  linarith [Int.mul_ediv_add_emod z (b : ℤ)]

/-- The natural-number digit `(a + (b - c)) % b` used in `digitSub` is the paper's
`(a - c) mod b` for base-`b` digits `c < b`. -/
theorem digitSub_digit_cast (b a c : ℕ) (hc : c < b) :
    (((a + (b - c)) % b : ℕ) : ℤ) = ((a : ℤ) - c) % b := by
  have hsub : (((a + (b - c) : ℕ)) : ℤ) = ((a : ℤ) - c) + b * 1 := by
    rw [Nat.cast_add, Nat.cast_sub hc.le]; ring
  rw [Int.natCast_mod, hsub, Int.add_mul_emod_self_left]

/-! ## Ground truth -/

/-- OEIS A178729: `a(n) = n XOR 3n`. -/
def a178729 (n : ℕ) : ℕ := n ^^^ (3 * n)

/-- OEIS A005351: the base `-2` representation of `n` regarded as base `2`. -/
def a005351 (n : ℕ) : ℕ := negabin n

/-- OEIS A005352: the base `-2` representation of `-n` reinterpreted as binary (OEIS offset
`1`; the value at `0` is `0`). -/
def a005352 (n : ℕ) : ℕ := negabin (-(n : ℤ))

-- A178729 DATA (offset 0).
example : (List.range 30).map a178729 =
    [0, 2, 4, 10, 8, 10, 20, 18, 16, 18, 20, 42, 40, 42, 36, 34, 32, 34, 36, 42, 40, 42, 84,
      82, 80, 82, 84, 74, 72, 74] := by
  decide +kernel

-- A005351 and A005352 DATA.
example : (List.range 20).map a005351 =
    [0, 1, 6, 7, 4, 5, 26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23] := by
  decide +kernel

example : (List.range 20).map (fun i => a005352 (i + 1)) =
    [3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 53, 52, 55, 54, 49, 48, 51, 50, 61, 60] := by
  decide +kernel

-- The paper's table: `10₋₂ = 11110`, `(-10)₋₂ = 001010`, `14₋₂ = 10010`, `(-14)₋₂ = 110110`.
example : negabin 10 = 0b11110 ∧ negabin (-10) = 0b1010 ∧ negabin 14 = 0b10010 ∧
    negabin (-14) = 0b110110 := by
  decide +kernel

-- The paper's table, last column: `(3n) ⊖_2 n` for `n = 10, …, 14`, both sides.
example : (List.range 5).map (fun i => digitIndicator 2 (digitSub 2 (3 * (i + 10)) (i + 10))) =
    [20, 42, 40, 42, 36] := by
  decide +kernel

example : (List.range 5).map (fun i : ℕ => negaXor 2 ((i : ℤ) + 10) (-((i : ℤ) + 10))) =
    [20, 42, 40, 42, 36] := by
  decide +kernel

-- `⊖_b`, the double bar and `⊕_{-b}` on small base-`3` inputs:
-- `22₃ ⊖₃ 12₃ = 10₃`, `‖202₃‖ = 101₃`, `2 ⊕_{-3} 1 = 0`, and `(-1) ⊕_{-3} 0 = 12₃ = 5`
-- since `-1 = 2 + 1·(-3)` has base `-3` digits `1, 2` (most significant first).
example : digitSub 3 8 5 = 3 ∧ digitIndicator 3 20 = 10 ∧ negaXor 3 2 1 = 0 ∧
    negaXor 3 (-1) 0 = 5 := by
  decide +kernel

-- Both sides of Theorem `thm:main` for `b = 3` and `b = 5`, `n < 15` (independently
-- computed in Python: `[0, 3, 3, 9, 12, 12, 9, 30, 30, 27, 30, 30, 36, 39, 39]` and
-- `[0, 5, 5, 5, 5, 25, 30, 30, 30, 30, 25, 30, 30, 30, 30]`).
example : (List.range 15).map (fun n => digitIndicator 3 (digitSub 3 (4 * n) n)) =
    [0, 3, 3, 9, 12, 12, 9, 30, 30, 27, 30, 30, 36, 39, 39] := by
  decide +kernel

example : (List.range 15).map (fun n : ℕ => negaXor 3 n (-n)) =
    [0, 3, 3, 9, 12, 12, 9, 30, 30, 27, 30, 30, 36, 39, 39] := by
  decide +kernel

example : (List.range 15).map (fun n : ℕ => negaXor 5 n (-n)) =
    [0, 5, 5, 5, 5, 25, 30, 30, 30, 30, 25, 30, 30, 30, 30] := by
  decide +kernel

/-! ## The theorems -/

/-- **Verrill, Theorem `thm:main` (arXiv:2506.09509).** For every base `b ≥ 2` and every
`n ≥ 0`, replacing each nonzero base-`b` digit of `((b+1)n) ⊖_b n` by `1` gives
`n ⊕_{-b} (-n)`: `‖((b+1)n) ⊖_b n‖ = n ⊕_{-b} (-n)`. -/
theorem verrill_thm_main (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    digitIndicator b (digitSub b ((b + 1) * n) n) = negaXor b n (-n) := by
  simpa [stateL, stateR1] using (main_triple b hb n).1

/-- **Equation (1.1) of arXiv:2506.09509 (the A178729 conjecture), proved.** For every
`n ≥ 0`, `n XOR 3n = n ⊕_{-2} (-n)`. -/
theorem verrill_eq_1_1 (n : ℕ) : n ^^^ (3 * n) = negaXor 2 n (-n) := by
  have h := verrill_thm_main 2 le_rfl n
  rw [digitIndicator_two, digitSub_two, Nat.xor_comm] at h
  exact h

/-- **OEIS A178729 formula (conjectured there, proved by Verrill).** For every `n ≥ 0`,
`A178729(n) = n XOR 3n = A005351(n) XOR A005352(n)`: the XOR of the negabinary digit
strings of `n` and `-n`, read in binary. -/
theorem a178729_eq_a005351_xor_a005352 (n : ℕ) : a178729 n = a005351 n ^^^ a005352 n := by
  rw [a178729, a005351, a005352, verrill_eq_1_1, negaXor_two]

end Candidates.VerrillBaseBDigitIdentity
