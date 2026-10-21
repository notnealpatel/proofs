/-
# A106297 — Wu: periods of the Lucas 5-step sequence modulo prime powers

## OEIS source (retrieved 2026-10-21 with `oeis show A106297`)

```
NAME:     Period of the Lucas 5-step sequence A074048 mod n.
TERMS:    1,1,104,6,781,104,2801,12,312,781,16105,312,30941,2801,81224,24,
          88741,312,13032,4686,291304,16105,12166,312,3905,30941,936,16806,...
FORMULA:  Let the prime factorization of n be p1^e1...pk^ek. Then
          a(n) = lcm(a(p1^e1), ..., a(pk^ek)).
FORMULA (the conjecture):
  Conjectures: a(5^k) = 781*5^(k-1) for k > 0. a(2^k) = 3*2^(k-1) for k > 1.
  If a(p) != a(p^2) for prime p > 2, then a(p^k) = p^(k-1)*a(p) for k > 0.
  - _Chai Wah Wu_, Feb 25 2022
COMMENT:
  This sequence can differ from the corresponding Fibonacci sequence (A106303)
  only when n is a multiple of 2 or 599 because 9584 is the discriminant of
  the characteristic polynomial x^5-x^4-x^3-x^2-x-1 and the prime factors of
  9584 are 2 and 599. [corrected by _Avery Diep_, Aug 25 2025]
```

A074048: "Pentanacci numbers with initial conditions a(0)=5, a(1)=1, a(2)=3,
a(3)=7, a(4)=15", terms 5,1,3,7,15,31,57,113,223,439,863,1695,3333,...

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This module proves all three parts.

## Proof outline

Write `Δ = fwdDiff t` for the difference operator with step `t` on integer
sequences, and `R` for the integer sequences satisfying the pentanacci
recurrence.  Newton's formula `s (n + k t) = ∑ C(k, m) Δ^m s n` reduces every
lifting step to `p`-adic estimates on iterated differences.

* For an odd prime `p ∤ 1198 = 2 · 599`, the identity
  `1198 · I n = 9 L n + 254 L (n+1) - 198 L (n+2) + 10 L (n+3) + 15 L (n+4)`
  (with `I` the impulse sequence `0,0,0,0,1,…`) shows that a period of `L`
  mod `p` is a period of every sequence in `R` mod `p`; hence
  `Δ` raises the `p`-adic valuation on `R` and the classical lifting argument
  applies.
* For `p = 599`, the period is `598` and `Δ²` (not `Δ`) raises valuations on
  `R` (a finite check on `I`); one weak lifting step reaches the strong case.
* For `p = 2`, `Δ` with step `12` raises valuations by `2` on `R` (a finite
  check on `I` mod `4`), and `Δ_{12} L` has valuation exactly `3`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A106297LucasStepInitial

open Finset fwdDiff

/-! ## Definitions -/

/-- The Lucas 5-step sequence A074048: `5, 1, 3, 7, 15`, then each term is the
sum of the previous five. -/
def luc5 : ℕ → ℤ
  | 0 => 5
  | 1 => 1
  | 2 => 3
  | 3 => 7
  | 4 => 15
  | n + 5 => luc5 n + luc5 (n + 1) + luc5 (n + 2) + luc5 (n + 3) + luc5 (n + 4)

/-- `t` is a period of `luc5` modulo `m`: `t > 0` and `L (n + t) ≡ L n (mod m)`
for every `n`. -/
def IsPeriodMod (m t : ℕ) : Prop :=
  0 < t ∧ ∀ n, (m : ℤ) ∣ luc5 (n + t) - luc5 n

/-- A106297: the least period of `luc5` modulo `m` (the infimum of the set of
periods; `exists_isPeriodMod` shows the set is nonempty for `0 < m`). -/
noncomputable def period (m : ℕ) : ℕ := sInf {t | IsPeriodMod m t}

/-! ## Ground truth for `luc5` -/

example : (List.range 14).map luc5 =
    [5, 1, 3, 7, 15, 31, 57, 113, 223, 439, 863, 1695, 3333, 6553] := by decide

/-! ## Sequences satisfying the pentanacci recurrence -/

/-- `s` satisfies the pentanacci recurrence `s (n+5) = s n + ⋯ + s (n+4)`. -/
def IsRec (s : ℕ → ℤ) : Prop :=
  ∀ n, s (n + 5) = s n + s (n + 1) + s (n + 2) + s (n + 3) + s (n + 4)

/-- The impulse pentanacci sequence `0, 0, 0, 0, 1, 1, 2, 4, 8, …` (A001591). -/
def imp : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | n + 5 => imp n + imp (n + 1) + imp (n + 2) + imp (n + 3) + imp (n + 4)

example : (List.range 12).map imp = [0, 0, 0, 0, 1, 1, 2, 4, 8, 16, 31, 61] := by decide

/-- `luc5` satisfies the recurrence. -/
theorem isRec_luc5 : IsRec luc5 := fun _ => rfl

/-- `imp` satisfies the recurrence. -/
theorem isRec_imp : IsRec imp := fun _ => rfl

/-- The recurrence is preserved by forward differences with any step. -/
theorem IsRec.fwdDiff {s : ℕ → ℤ} (hs : IsRec s) (t : ℕ) : IsRec (Δ_[t] s) := by
  intro n
  have h1 := hs (n + t)
  have h2 := hs n
  simp only [_root_.fwdDiff]
  rw [show n + 5 + t = n + t + 5 by omega, show n + 1 + t = n + t + 1 by omega,
    show n + 2 + t = n + t + 2 by omega, show n + 3 + t = n + t + 3 by omega,
    show n + 4 + t = n + t + 4 by omega, h1, h2]
  ring

/-- The recurrence is preserved by iterated forward differences. -/
theorem IsRec.iterate_fwdDiff {s : ℕ → ℤ} (hs : IsRec s) (t k : ℕ) :
    IsRec ((Δ_[t])^[k] s) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.fwdDiff t

/-- A recurrence sequence whose first five terms are divisible by `q` is
divisible by `q` everywhere. -/
theorem IsRec.dvd_of_lt_five {s : ℕ → ℤ} (hs : IsRec s) {q : ℤ}
    (h : ∀ n < 5, q ∣ s n) : ∀ n, q ∣ s n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 5 with hn | hn
    · exact h n hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [hs k]
      refine dvd_add (dvd_add (dvd_add (dvd_add (ih k ?_) (ih (k + 1) ?_)) (ih (k + 2) ?_))
        (ih (k + 3) ?_)) (ih (k + 4) ?_) <;> omega

/-- Two recurrence sequences agreeing on their first five terms are equal. -/
theorem IsRec.ext {s s' : ℕ → ℤ} (hs : IsRec s) (hs' : IsRec s')
    (h : ∀ n < 5, s n = s' n) : ∀ n, s n = s' n := by
  have hd : IsRec (fun n => s n - s' n) := by
    intro n
    simp only
    rw [hs n, hs' n]
    ring
  intro n
  have := hd.dvd_of_lt_five (q := 0) (fun k hk => by simp [h k hk]) n
  simpa [sub_eq_zero] using this

/-- Exact division of a recurrence sequence by a common divisor of its terms. -/
theorem IsRec.exists_eq_mul {s : ℕ → ℤ} (hs : IsRec s) {q : ℤ} (hq : q ≠ 0)
    (h : ∀ n, q ∣ s n) : ∃ s', IsRec s' ∧ ∀ n, s n = q * s' n := by
  refine ⟨fun n => s n / q, ?_, fun n => (Int.mul_ediv_cancel' (h n)).symm⟩
  intro n
  apply mul_left_cancel₀ hq
  simp only [mul_add, Int.mul_ediv_cancel' (h _)]
  exact hs n

/-- Every recurrence sequence is an integer combination of shifts of `imp`. -/
theorem IsRec.eq_imp_comb {s : ℕ → ℤ} (hs : IsRec s) (n : ℕ) :
    s n = (s 4 - s 3 - s 2 - s 1 - s 0) * imp n + (s 3 - s 2 - s 1 - s 0) * imp (n + 1)
      + (s 2 - s 1 - s 0) * imp (n + 2) + (s 1 - s 0) * imp (n + 3) + s 0 * imp (n + 4) := by
  refine hs.ext (s' := fun n => (s 4 - s 3 - s 2 - s 1 - s 0) * imp n
      + (s 3 - s 2 - s 1 - s 0) * imp (n + 1) + (s 2 - s 1 - s 0) * imp (n + 2)
      + (s 1 - s 0) * imp (n + 3) + s 0 * imp (n + 4)) ?_ ?_ n
  · intro k
    have h0 := isRec_imp k
    have h1 := isRec_imp (k + 1)
    have h2 := isRec_imp (k + 2)
    have h3 := isRec_imp (k + 3)
    have h4 := isRec_imp (k + 4)
    simp only
    ring_nf at h0 h1 h2 h3 h4 ⊢
    linear_combination (s 4 - s 3 - s 2 - s 1 - s 0) * h0 + (s 3 - s 2 - s 1 - s 0) * h1
      + (s 2 - s 1 - s 0) * h2 + (s 1 - s 0) * h3 + s 0 * h4
  · intro k hk
    interval_cases k <;> simp [imp] <;> ring

/-! ## Iterated forward differences -/

/-- Iterated differences commute with a combination of five consecutive shifts. -/
theorem iterate_fwdDiff_comb (t k : ℕ) (c0 c1 c2 c3 c4 : ℤ) (w : ℕ → ℤ) (n : ℕ) :
    (Δ_[t])^[k] (fun n => c0 * w n + c1 * w (n + 1) + c2 * w (n + 2) + c3 * w (n + 3)
      + c4 * w (n + 4)) n
    = c0 * (Δ_[t])^[k] w n + c1 * (Δ_[t])^[k] w (n + 1) + c2 * (Δ_[t])^[k] w (n + 2)
      + c3 * (Δ_[t])^[k] w (n + 3) + c4 * (Δ_[t])^[k] w (n + 4) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', _root_.fwdDiff, ih]
    rw [show n + t + 1 = n + 1 + t by omega, show n + t + 2 = n + 2 + t by omega,
      show n + t + 3 = n + 3 + t by omega, show n + t + 4 = n + 4 + t by omega]
    ring

/-- Iterated differences commute with multiplication by a constant. -/
theorem iterate_fwdDiff_const_mul (t k : ℕ) (c : ℤ) (w : ℕ → ℤ) (n : ℕ) :
    (Δ_[t])^[k] (fun n => c * w n) n = c * (Δ_[t])^[k] w n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', _root_.fwdDiff, ih]
    ring

/-- Iterated differences preserve divisibility of all terms. -/
theorem dvd_iterate_fwdDiff {q : ℤ} {w : ℕ → ℤ} (h : ∀ n, q ∣ w n) (t k : ℕ) :
    ∀ n, q ∣ (Δ_[t])^[k] w n := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    intro n
    rw [Function.iterate_succ_apply']
    exact dvd_sub (ih _) (ih _)

/-- Newton's formula for a difference with step `k * t`. -/
theorem fwdDiff_mul_eq_sum (s : ℕ → ℤ) (t k n : ℕ) :
    Δ_[k * t] s n = ∑ m ∈ range k, (k.choose (m + 1) : ℤ) * (Δ_[t])^[m + 1] s n := by
  have hN := shift_eq_sum_fwdDiff_iter t s k n
  simp only [smul_eq_mul, nsmul_eq_mul] at hN
  rw [sum_range_succ'] at hN
  simp only [Nat.choose_zero_right, Nat.cast_one, Function.iterate_zero, id_eq,
    one_mul] at hN
  simp only [_root_.fwdDiff, hN]
  ring

/-- `Raises q g k t`: the operator `(Δ_[t])^[k]` maps recurrence sequences divisible
by `q ^ e` to sequences divisible by `q ^ (e + g)`. -/
def Raises (q : ℤ) (g k t : ℕ) : Prop :=
  ∀ s, IsRec s → ∀ e : ℕ, (∀ n, q ^ e ∣ s n) → ∀ n, q ^ (e + g) ∣ (Δ_[t])^[k] s n

/-- A divisibility property of the iterated differences of `imp` propagates to all
recurrence sequences, with the gain in valuation. -/
theorem raises_of_imp {q : ℤ} (hq : q ≠ 0) {g k t : ℕ}
    (h : ∀ n, q ^ g ∣ (Δ_[t])^[k] imp n) : Raises q g k t := by
  intro s hs e he n
  obtain ⟨s', hs', hss'⟩ := hs.exists_eq_mul (pow_ne_zero e hq) he
  have hfun : s = fun n => q ^ e * s' n := funext hss'
  have hfun' : s' = fun n => (s' 4 - s' 3 - s' 2 - s' 1 - s' 0) * imp n
      + (s' 3 - s' 2 - s' 1 - s' 0) * imp (n + 1) + (s' 2 - s' 1 - s' 0) * imp (n + 2)
      + (s' 1 - s' 0) * imp (n + 3) + s' 0 * imp (n + 4) := funext hs'.eq_imp_comb
  rw [hfun, iterate_fwdDiff_const_mul, hfun', iterate_fwdDiff_comb, pow_add]
  apply mul_dvd_mul_left
  exact dvd_add (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (h _) _)
    (dvd_mul_of_dvd_right (h _) _)) (dvd_mul_of_dvd_right (h _) _))
    (dvd_mul_of_dvd_right (h _) _)) (dvd_mul_of_dvd_right (h _) _)

/-- A single difference that raises valuations keeps doing so at every multiple of
its step. -/
theorem Raises.mul {q : ℤ} {g t : ℕ} (h : Raises q g 1 t) (k : ℕ) : Raises q g 1 (k * t) := by
  intro s hs e he n
  simp only [Function.iterate_one]
  rw [fwdDiff_mul_eq_sum]
  refine dvd_sum fun m _ => dvd_mul_of_dvd_right ?_ _
  rw [Function.iterate_succ_apply]
  exact dvd_iterate_fwdDiff (fun n => by simpa using h s hs e he n) t m n

/-- Iterating a difference that raises valuations by `g`. -/
theorem Raises.iterate_one {q : ℤ} {g t : ℕ} (h : Raises q g 1 t) {y : ℕ → ℤ} (hy : IsRec y)
    {j : ℕ} (hj : ∀ n, q ^ j ∣ y n) (a : ℕ) : ∀ n, q ^ (j + g * a) ∣ (Δ_[t])^[a] y n := by
  induction a with
  | zero => simpa using hj
  | succ a ih =>
    intro n
    rw [Function.iterate_succ_apply', show j + g * (a + 1) = (j + g * a) + g by ring]
    simpa using h _ (hy.iterate_fwdDiff t a) _ ih n

/-- Iterating a second difference that raises valuations by `1`. -/
theorem Raises.iterate_two {q : ℤ} {t : ℕ} (h : Raises q 1 2 t) {y : ℕ → ℤ} (hy : IsRec y)
    {j : ℕ} (hj : ∀ n, q ^ j ∣ y n) (a : ℕ) : ∀ n, q ^ (j + a / 2) ∣ (Δ_[t])^[a] y n := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro n
    rcases Nat.lt_or_ge a 2 with ha | ha
    · rw [show a / 2 = 0 by omega, add_zero]
      exact dvd_iterate_fwdDiff hj t a n
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
      rw [show b + 2 = 2 + b by ring, Function.iterate_add_apply,
        show j + (2 + b) / 2 = (j + b / 2) + 1 by omega]
      exact h _ (hy.iterate_fwdDiff t b) _ (ih b (by omega)) n

/-- **Strong lifting step.**  If `Δ_[t]` raises `p`-adic valuations on recurrence
sequences (`p ≥ 3` prime) and `p ^ j ∣ Δ_[t] s`, then
`Δ_[p t] s ≡ p · Δ_[t] s (mod p ^ (j + 2))`. -/
theorem step_strong {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {t : ℕ} (h : Raises p 1 1 t)
    {s : ℕ → ℤ} (hs : IsRec s) {j : ℕ} (hj : ∀ n, (p : ℤ) ^ j ∣ Δ_[t] s n) (n : ℕ) :
    (p : ℤ) ^ (j + 2) ∣ Δ_[p * t] s n - p * Δ_[t] s n := by
  have hval := h.iterate_one (hs.fwdDiff t) hj
  rw [fwdDiff_mul_eq_sum]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  rw [sum_range_succ']
  simp only [zero_add, Nat.choose_one_right, Function.iterate_one, add_sub_cancel_right]
  refine dvd_sum fun m hm => ?_
  rw [mem_range] at hm
  rw [Function.iterate_succ_apply]
  rcases Nat.lt_or_ge (m + 1 + 1) (p' + 1) with hlt | hge
  · have hc : ((p' + 1 : ℕ) : ℤ) ∣ ((p' + 1).choose (m + 1 + 1) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) hlt)
    rw [pow_succ']
    exact mul_dvd_mul hc ((pow_dvd_pow _ (by omega)).trans (hval (m + 1) n))
  · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans (hval (m + 1) n)) _

/-- **Weak lifting step.**  If `Δ_[t]²` raises `p`-adic valuations on recurrence
sequences (`p ≥ 5` prime) and `p ^ j ∣ Δ_[t] s`, then
`Δ_[p t] s ≡ p · Δ_[t] s + C(p, 2) · Δ_[t]² s (mod p ^ (j + 2))`. -/
theorem step_weak {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {t : ℕ} (h : Raises p 1 2 t)
    {s : ℕ → ℤ} (hs : IsRec s) {j : ℕ} (hj : ∀ n, (p : ℤ) ^ j ∣ Δ_[t] s n) (n : ℕ) :
    (p : ℤ) ^ (j + 2) ∣
      Δ_[p * t] s n - p * Δ_[t] s n - (p.choose 2 : ℤ) * (Δ_[t])^[2] s n := by
  have hval := h.iterate_two (hs.fwdDiff t) hj
  rw [fwdDiff_mul_eq_sum]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  rw [sum_range_succ', sum_range_succ']
  simp only [zero_add, Nat.choose_one_right, Function.iterate_one]
  rw [show (Nat.choose (p' + 2) (1 + 1) : ℤ) * (Δ_[t])^[1 + 1] s n
      = ((p' + 2).choose 2 : ℤ) * (Δ_[t])^[2] s n from rfl]
  rw [show ∀ a b c : ℤ, a + b + c - c - b = a by intros; ring]
  refine dvd_sum fun m hm => ?_
  rw [mem_range] at hm
  rw [Function.iterate_succ_apply]
  rcases Nat.lt_or_ge (m + 1 + 1 + 1) (p' + 2) with hlt | hge
  · have hc : ((p' + 2 : ℕ) : ℤ) ∣ ((p' + 2).choose (m + 1 + 1 + 1) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) hlt)
    rw [pow_succ']
    exact mul_dvd_mul hc ((pow_dvd_pow _ (by omega)).trans (hval (m + 1 + 1) n))
  · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans (hval (m + 1 + 1) n)) _

/-- A second difference raising valuations makes the `p`-fold step a first
difference raising valuations. -/
theorem Raises.strong_of_weak {p : ℕ} {t : ℕ} (h : Raises p 1 2 t) :
    Raises p 1 1 (p * t) := by
  intro x hx e he n
  simp only [Function.iterate_one]
  rw [fwdDiff_mul_eq_sum]
  refine dvd_sum fun m _ => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_add, Nat.choose_one_right, Function.iterate_one]
    rw [pow_succ']
    exact mul_dvd_mul_left _ (by simpa using dvd_iterate_fwdDiff he t 1 n)
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [show m' + 1 + 1 = m' + 2 by ring, Function.iterate_add_apply]
    exact dvd_mul_of_dvd_right
      (dvd_iterate_fwdDiff (h x hx e he) t m' n) _

/-- **2-adic lifting step.**  If `Δ_[t]` raises `2`-adic valuations by `2` and
`2 ^ j ∣ Δ_[t] s`, then `Δ_[2 t] s ≡ 2 · Δ_[t] s (mod 2 ^ (j + 2))`. -/
theorem step_two {t : ℕ} (h : Raises 2 2 1 t) {s : ℕ → ℤ} (hs : IsRec s) {j : ℕ}
    (hj : ∀ n, (2 : ℤ) ^ j ∣ Δ_[t] s n) (n : ℕ) :
    (2 : ℤ) ^ (j + 2) ∣ Δ_[2 * t] s n - 2 * Δ_[t] s n := by
  rw [fwdDiff_mul_eq_sum]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.choose_one_right,
    Function.iterate_one]
  rw [show (1 + 1 : ℕ) = 2 from rfl, Nat.choose_self, Function.iterate_succ_apply]
  simpa using h _ (hs.fwdDiff t) j hj n

/-! ## Periods -/

/-- A period can be certified on the first five indices. -/
theorem isPeriodMod_of_lt_five {m t : ℕ} (ht : 0 < t)
    (h : ∀ n < 5, (m : ℤ) ∣ luc5 (n + t) - luc5 n) : IsPeriodMod m t :=
  ⟨ht, (isRec_luc5.fwdDiff t).dvd_of_lt_five h⟩

/-- A period modulo `m` is a period modulo every divisor of `m`. -/
theorem IsPeriodMod.of_dvd {m m' t : ℕ} (h : IsPeriodMod m t) (hd : m' ∣ m) :
    IsPeriodMod m' t :=
  ⟨h.1, fun n => (Int.natCast_dvd_natCast.mpr hd).trans (h.2 n)⟩

/-- Positive multiples of periods are periods. -/
theorem IsPeriodMod.mul {m t : ℕ} (h : IsPeriodMod m t) {k : ℕ} (hk : 0 < k) :
    IsPeriodMod m (k * t) := by
  refine ⟨Nat.mul_pos hk h.1, fun n => ?_⟩
  change (m : ℤ) ∣ Δ_[k * t] luc5 n
  rw [fwdDiff_mul_eq_sum]
  refine dvd_sum fun i _ => dvd_mul_of_dvd_right ?_ _
  rw [Function.iterate_succ_apply]
  exact dvd_iterate_fwdDiff h.2 t i n

/-- The difference of two distinct periods is a period. -/
theorem IsPeriodMod.sub {m t1 t2 : ℕ} (h1 : IsPeriodMod m t1) (h2 : IsPeriodMod m t2)
    (hlt : t1 < t2) : IsPeriodMod m (t2 - t1) := by
  refine ⟨by omega, fun n => ?_⟩
  have e1 := h1.2 (n + (t2 - t1))
  have e2 := h2.2 n
  rw [show n + (t2 - t1) + t1 = n + t2 by omega] at e1
  have hid : luc5 (n + (t2 - t1)) - luc5 n
      = (luc5 (n + t2) - luc5 n) - (luc5 (n + t2) - luc5 (n + (t2 - t1))) := by ring
  rw [hid]
  exact dvd_sub e2 e1

/-- The least period divides every period. -/
theorem period_dvd {m t : ℕ} (ht : IsPeriodMod m t) : period m ∣ t := by
  have hmem : IsPeriodMod m (period m) := by
    have hin : period m ∈ {t | IsPeriodMod m t} := Nat.sInf_mem ⟨t, ht⟩
    exact hin
  set a := period m with ha
  by_contra hnd
  have hr : 0 < t % a := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
  have hdm := Nat.div_add_mod t a
  have hper : IsPeriodMod m (t % a) := by
    rcases Nat.eq_zero_or_pos (t / a) with h0 | hpos
    · rw [h0, mul_zero, zero_add] at hdm
      rwa [hdm]
    · have hsub := (hmem.mul hpos).sub ht (by
        generalize t / a = c at hdm hpos ⊢
        rw [mul_comm] at hdm
        omega)
      convert hsub using 1
      generalize t / a = c at hdm hpos ⊢
      rw [mul_comm] at hdm
      omega
  have hle : a ≤ t % a := Nat.sInf_le hper
  exact absurd (Nat.mod_lt t hmem.1) (not_lt.mpr hle)

/-- A period `t` all of whose period divisors are at least `t` is the least period. -/
theorem period_eq_of {m t : ℕ} (ht : IsPeriodMod m t)
    (hmin : ∀ d, d ∣ t → IsPeriodMod m d → t ≤ d) : period m = t := by
  have hmem : IsPeriodMod m (period m) := by
    have hin : period m ∈ {t | IsPeriodMod m t} := Nat.sInf_mem ⟨t, ht⟩
    exact hin
  exact le_antisymm (Nat.sInf_le ht) (hmin _ (period_dvd ht) hmem)

/-- Every modulus `m > 0` admits a period (pigeonhole on windows of five residues and
invertibility of the recurrence). -/
theorem exists_isPeriodMod {m : ℕ} (hm : 0 < m) : ∃ t, IsPeriodMod m t := by
  haveI : NeZero m := ⟨hm.ne'⟩
  let f : ℕ → (Fin 5 → ZMod m) := fun n i => (luc5 (n + i) : ZMod m)
  let g : (Fin 5 → ZMod m) → (Fin 5 → ZMod m) :=
    fun v => ![v 4 - v 0 - v 1 - v 2 - v 3, v 0, v 1, v 2, v 3]
  let h : (Fin 5 → ZMod m) → (Fin 5 → ZMod m) :=
    fun v => ![v 1, v 2, v 3, v 4, v 0 + v 1 + v 2 + v 3 + v 4]
  have hrec : ∀ a, (luc5 (a + 5) : ZMod m) = luc5 a + luc5 (a + 1) + luc5 (a + 2)
      + luc5 (a + 3) + luc5 (a + 4) := fun a => by rw [isRec_luc5 a]; push_cast; ring
  have hg : ∀ a, f a = g (f (a + 1)) := by
    intro a
    funext i
    fin_cases i
    · simp [f, g, hrec]
      ring
    all_goals simp [f, g, add_assoc]
  have hh : ∀ a, f (a + 1) = h (f a) := by
    intro a
    funext i
    fin_cases i <;> simp [f, h, hrec]
  obtain ⟨x, y, hxy, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ x y, x < y → f x = f y → ∃ t, IsPeriodMod m t := by
    intro x y hlt hfxy
    have hback : ∀ c, c ≤ x → f (x - c) = f (y - c) := by
      intro c
      induction c with
      | zero => simpa using hfxy
      | succ c ih =>
        intro hc
        have e := ih (by omega)
        rw [show x - c = (x - (c + 1)) + 1 by omega, show y - c = (y - (c + 1)) + 1 by omega]
          at e
        rw [hg (x - (c + 1)), hg (y - (c + 1)), e]
    have h0 : f 0 = f (y - x) := by simpa using hback x le_rfl
    have hall : ∀ n, f n = f (n + (y - x)) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih => rw [hh n, show n + 1 + (y - x) = n + (y - x) + 1 by omega, hh, ih]
    refine ⟨y - x, by omega, fun n => ?_⟩
    have e := congr_fun (hall n) 0
    simp only [f, Fin.val_zero, add_zero] at e
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp e
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · exact key x y hlt hf
  · exact key y x hlt hf.symm

/-- The least period modulo `m > 0` is a period. -/
theorem isPeriodMod_period {m : ℕ} (hm : 0 < m) : IsPeriodMod m (period m) := by
  have hmem : period m ∈ {t | IsPeriodMod m t} := Nat.sInf_mem (exists_isPeriodMod hm)
  exact hmem

/-! ## Iterated lifting -/

/-- **Iterated lifting.**  If a property `P` of steps is stable under multiplying the
step by `p`, and for steps with `P` the `p`-fold difference of `luc5` agrees with
`p` times the difference modulo `p ^ (j + 2)`, then exact divisibility of the
differences by `p ^ j` propagates along the steps `p ^ k * t`. -/
theorem lift_iter {p : ℕ} (P : ℕ → Prop) (hP : ∀ t, P t → P (p * t))
    (hstep : ∀ t j, P t → (∀ n, (p : ℤ) ^ j ∣ Δ_[t] luc5 n) →
      ∀ n, (p : ℤ) ^ (j + 2) ∣ Δ_[p * t] luc5 n - p * Δ_[t] luc5 n)
    (hp : p ≠ 0) {t j n0 : ℕ} (ht : P t) (hj : ∀ n, (p : ℤ) ^ j ∣ Δ_[t] luc5 n)
    (hn0 : ¬ (p : ℤ) ^ (j + 1) ∣ Δ_[t] luc5 n0) (k : ℕ) :
    P (p ^ k * t) ∧ (∀ n, (p : ℤ) ^ (j + k) ∣ Δ_[p ^ k * t] luc5 n) ∧
      ¬ (p : ℤ) ^ (j + k + 1) ∣ Δ_[p ^ k * t] luc5 n0 := by
  induction k with
  | zero => simpa using ⟨ht, hj, hn0⟩
  | succ k ih =>
    obtain ⟨hPk, hdk, hndk⟩ := ih
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    rw [pow_succ', mul_assoc]
    have hst := hstep _ _ hPk hdk
    refine ⟨hP _ hPk, fun n => ?_, fun hcon => hndk ?_⟩
    · have e := (pow_dvd_pow (p : ℤ) (by omega : j + (k + 1) ≤ j + k + 2)).trans (hst n)
      have e2 : (p : ℤ) ^ (j + (k + 1)) ∣ p * Δ_[p ^ k * t] luc5 n := by
        rw [show j + (k + 1) = 1 + (j + k) by ring, pow_add, pow_one]
        exact mul_dvd_mul_left _ (hdk n)
      simpa using dvd_add e e2
    · have e := (pow_dvd_pow (p : ℤ) (by omega : j + (k + 1) + 1 ≤ j + k + 2)).trans (hst n0)
      have e2 := dvd_sub hcon e
      rw [sub_sub_cancel, show j + (k + 1) + 1 = 1 + (j + k + 1) by ring, pow_add,
        pow_one] at e2
      exact (mul_dvd_mul_iff_left hpz).mp e2

/-- **Chain criterion for the least period at prime powers.**  If `period (p ^ c) = t`
and, for every `i`, `p ^ i * t` is a period modulo `p ^ (c + i)` but not modulo
`p ^ (c + i + 1)`, then `period (p ^ (c + k)) = p ^ k * t`. -/
theorem period_eq_of_chain {p : ℕ} (hp : p.Prime) {c t : ℕ} (hc : period (p ^ c) = t)
    (hchain : ∀ i, IsPeriodMod (p ^ (c + i)) (p ^ i * t) ∧
      ¬ IsPeriodMod (p ^ (c + i + 1)) (p ^ i * t)) (k : ℕ) :
    period (p ^ (c + k)) = p ^ k * t := by
  refine period_eq_of (hchain k).1 fun d hd hdper => ?_
  have htd : t ∣ d := hc ▸ period_dvd (hdper.of_dvd (pow_dvd_pow p (by omega)))
  obtain ⟨e, rfl⟩ := htd
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exact absurd (hchain 0).1.1 (by simp [h0])
    · exact h0
  have he : e ∣ p ^ k := by
    rw [mul_comm] at hd
    exact Nat.dvd_of_mul_dvd_mul_right ht0 hd
  obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).mp he
  rcases Nat.lt_or_ge i k with hlt | hge
  · exfalso
    apply (hchain i).2
    rw [mul_comm]
    exact hdper.of_dvd (pow_dvd_pow p (by omega))
  · rw [mul_comm t, show i = k by omega]

/-- If `t` is not a period modulo `m` but `t > 0`, some difference is not divisible. -/
theorem exists_not_dvd_of_not_isPeriodMod {m t : ℕ} (ht : 0 < t) (h : ¬ IsPeriodMod m t) :
    ∃ n, ¬ (m : ℤ) ∣ Δ_[t] luc5 n := by
  by_contra hcon
  push Not at hcon
  exact h ⟨ht, hcon⟩

/-- Turn the conclusion of `lift_iter` into the chain hypothesis of
`period_eq_of_chain` (the modulus exponent is `c + i`, the valuation `j + i` with
`j = c`). -/
theorem chain_of_lift {p t c n0 : ℕ} (ht : 0 < t) (hp : p ≠ 0)
    (h : ∀ k, (∀ n, (p : ℤ) ^ (c + k) ∣ Δ_[p ^ k * t] luc5 n) ∧
      ¬ (p : ℤ) ^ (c + k + 1) ∣ Δ_[p ^ k * t] luc5 n0) (i : ℕ) :
    IsPeriodMod (p ^ (c + i)) (p ^ i * t) ∧ ¬ IsPeriodMod (p ^ (c + i + 1)) (p ^ i * t) := by
  refine ⟨⟨Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero hp) i) ht, fun n => ?_⟩, fun hper => ?_⟩
  · exact_mod_cast (h i).1 n
  · exact (h i).2 (by exact_mod_cast hper.2 n0)

/-- A divisor of a positive non-period is a non-period. -/
theorem not_isPeriodMod_of_dvd {m d t : ℕ} (hd : d ∣ t) (ht : 0 < t)
    (hnot : ¬ IsPeriodMod m t) : ¬ IsPeriodMod m d := by
  intro hper
  obtain ⟨e, rfl⟩ := hd
  apply hnot
  rw [mul_comm]
  exact hper.mul (Nat.pos_of_mul_pos_left ht)

/-- If `period (p ^ 2) ≠ period p` then `period p` is not a period modulo `p ^ 2`. -/
theorem not_isPeriodMod_sq {p : ℕ} (hp : 0 < p) (hne : period (p ^ 2) ≠ period p) :
    ¬ IsPeriodMod (p ^ 2) (period p) := by
  intro h
  apply hne
  refine Nat.dvd_antisymm (period_dvd h) (period_dvd ?_)
  exact (isPeriodMod_period (pow_pos hp 2)).of_dvd (dvd_pow_self p two_ne_zero)

/-! ## Odd primes other than 599 -/

/-- `1198 · imp n` is an integer combination of five consecutive terms of `luc5`
(`1198 = 2 · 599` divides the Krylov determinant `2^4 · 599` of `luc5`). -/
theorem imp_mul_eq (n : ℕ) : 1198 * imp n = 9 * luc5 n + 254 * luc5 (n + 1)
    - 198 * luc5 (n + 2) + 10 * luc5 (n + 3) + 15 * luc5 (n + 4) := by
  refine IsRec.ext (s := fun n => 1198 * imp n) (s' := fun n => 9 * luc5 n
    + 254 * luc5 (n + 1) - 198 * luc5 (n + 2) + 10 * luc5 (n + 3) + 15 * luc5 (n + 4))
    ?_ ?_ ?_ n
  · intro k
    simp only
    rw [isRec_imp k]
    ring
  · intro k
    have h0 := isRec_luc5 k
    have h1 := isRec_luc5 (k + 1)
    have h2 := isRec_luc5 (k + 2)
    have h3 := isRec_luc5 (k + 3)
    have h4 := isRec_luc5 (k + 4)
    simp only
    ring_nf at h0 h1 h2 h3 h4 ⊢
    linear_combination 9 * h0 + 254 * h1 - 198 * h2 + 10 * h3 + 15 * h4
  · decide

/-- For a prime `p ∉ {2, 599}`, a period of `luc5` modulo `p` makes `Δ_[t]` raise
`p`-adic valuations on every recurrence sequence. -/
theorem raises_of_isPeriodMod {p t : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h599 : p ≠ 599)
    (ht : IsPeriodMod p t) : Raises p 1 1 t := by
  apply raises_of_imp (by exact_mod_cast hp.ne_zero)
  intro n
  simp only [pow_one, Function.iterate_one]
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hid : 1198 * Δ_[t] imp n = 9 * Δ_[t] luc5 n + 254 * Δ_[t] luc5 (n + 1)
      - 198 * Δ_[t] luc5 (n + 2) + 10 * Δ_[t] luc5 (n + 3) + 15 * Δ_[t] luc5 (n + 4) := by
    simp only [_root_.fwdDiff]
    rw [mul_sub, imp_mul_eq, imp_mul_eq, show n + t + 1 = n + 1 + t by omega,
      show n + t + 2 = n + 2 + t by omega, show n + t + 3 = n + 3 + t by omega,
      show n + t + 4 = n + 4 + t by omega]
    ring
  have hdiv : (p : ℤ) ∣ 1198 * Δ_[t] imp n := by
    rw [hid]
    exact dvd_add (dvd_add (dvd_sub (dvd_add (dvd_mul_of_dvd_right (ht.2 _) _)
      (dvd_mul_of_dvd_right (ht.2 _) _)) (dvd_mul_of_dvd_right (ht.2 _) _))
      (dvd_mul_of_dvd_right (ht.2 _) _)) (dvd_mul_of_dvd_right (ht.2 _) _)
  rcases hpi.dvd_or_dvd hdiv with h | h
  · exfalso
    have hn : p ∣ 2 * 599 := by exact_mod_cast h
    have hp599 : Nat.Prime 599 := by norm_num
    rcases (Nat.Prime.dvd_mul hp).mp hn with h' | h'
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact h599 ((Nat.prime_dvd_prime_iff_eq hp hp599).mp h')
  · exact h

/-! ## The prime 599 -/

/-- `Δ_[598]²` raises `599`-adic valuations on recurrence sequences (finite check
on `imp`). -/
theorem raises_599 : Raises 599 1 2 598 := by
  apply raises_of_imp (by norm_num)
  simp only [pow_one]
  refine (isRec_imp.iterate_fwdDiff 598 2).dvd_of_lt_five ?_
  set_option maxRecDepth 100000 in decide

/-- `598` is a period of `luc5` modulo `599`. -/
theorem isPeriodMod_599 : IsPeriodMod 599 598 := by
  refine isPeriodMod_of_lt_five (by norm_num) ?_
  set_option maxRecDepth 100000 in decide

/-- The least period of `luc5` modulo `599` is `598`. -/
theorem period_599 : period 599 = 598 := by
  refine period_eq_of isPeriodMod_599 fun d hd hper => ?_
  by_contra hlt
  push Not at hlt
  have hcases : ∀ d ∈ Nat.divisors 598, d < 598 → d ∣ 299 ∨ d ∣ 46 ∨ d ∣ 26 := by decide
  have hn299 : ¬ IsPeriodMod 599 299 := fun h => by
    have := h.2 0
    revert this
    set_option maxRecDepth 100000 in decide
  have hn46 : ¬ IsPeriodMod 599 46 := fun h => by
    have := h.2 0
    revert this
    set_option maxRecDepth 100000 in decide
  have hn26 : ¬ IsPeriodMod 599 26 := fun h => by
    have := h.2 0
    revert this
    decide
  rcases hcases d (Nat.mem_divisors.mpr ⟨hd, by norm_num⟩) hlt with h | h | h
  · exact not_isPeriodMod_of_dvd h (by norm_num) hn299 hper
  · exact not_isPeriodMod_of_dvd h (by norm_num) hn46 hper
  · exact not_isPeriodMod_of_dvd h (by norm_num) hn26 hper

/-- **The weak lifting step at `599`.**  If `598` is not a period modulo `599²`,
then `599 · 598` is a period modulo `599²` but not modulo `599³`. -/
theorem lift_599 {n0 : ℕ} (hn0 : ¬ (599 : ℤ) ^ 2 ∣ Δ_[598] luc5 n0) :
    (∀ n, ((599 : ℕ) : ℤ) ^ 2 ∣ Δ_[599 * 598] luc5 n) ∧
      ∃ n1, ¬ ((599 : ℕ) : ℤ) ^ (2 + 1) ∣ Δ_[599 * 598] luc5 n1 := by
  have hj : ∀ n, ((599 : ℕ) : ℤ) ^ 1 ∣ Δ_[598] luc5 n := fun n => by
    rw [pow_one]
    exact isPeriodMod_599.2 n
  have hw := step_weak (by norm_num) (by norm_num) raises_599 isRec_luc5 hj
  have hc : ((Nat.choose 599 2 : ℕ) : ℤ) = 599 * 299 := by
    rw [Nat.choose_two_right]
    norm_num
  rw [hc] at hw
  set y : ℕ → ℤ := Δ_[598] luc5 with hy
  have h2 : ∀ n, (Δ_[598])^[2] luc5 n = Δ_[598] y n := fun n => rfl
  simp only [h2] at hw
  have hyd : ∀ n, (599 : ℤ) ∣ y n := by simpa using hj
  have hdy : ∀ n, (599 : ℤ) ∣ Δ_[598] y n := by
    simpa using dvd_iterate_fwdDiff hyd 598 1
  have hd2y : ∀ n, (599 : ℤ) ^ 2 ∣ (Δ_[598])^[2] y n := by
    simpa using raises_599 y (isRec_luc5.fwdDiff 598) 1 (by simpa using hyd)
  -- `z n = y n + 299 Δ y n`, and `Δ_[599·598] L ≡ 599 z (mod 599³)`.
  have hz : ∀ n, (599 : ℤ) ^ 3 ∣ Δ_[599 * 598] luc5 n - 599 * (y n + 299 * Δ_[598] y n) := by
    intro n
    have e := hw n
    rw [show ((599 : ℕ) : ℤ) ^ (1 + 2) = 599 ^ 3 by norm_num,
      show ((599 : ℕ) : ℤ) = 599 by norm_num] at e
    have hid : Δ_[599 * 598] luc5 n - 599 * (y n + 299 * Δ_[598] y n)
        = Δ_[599 * 598] luc5 n - 599 * y n - 599 * 299 * Δ_[598] y n := by ring
    rw [hid]
    exact e
  have hzd : ∀ n, (599 : ℤ) ∣ y n + 299 * Δ_[598] y n :=
    fun n => dvd_add (hyd n) (dvd_mul_of_dvd_right (hdy n) _)
  refine ⟨fun n => ?_, ?_⟩
  · have e1 := (pow_dvd_pow (599 : ℤ) (by norm_num : 2 ≤ 3)).trans (hz n)
    have e2 : (599 : ℤ) ^ 2 ∣ 599 * (y n + 299 * Δ_[598] y n) := by
      rw [sq]
      exact mul_dvd_mul_left _ (hzd n)
    simpa using dvd_add e1 e2
  · by_contra hall
    push Not at hall
    have hz2 : ∀ n, (599 : ℤ) ^ 2 ∣ y n + 299 * Δ_[598] y n := by
      intro n
      have e := dvd_sub (by simpa using hall n) (hz n)
      rw [sub_sub_cancel, pow_succ'] at e
      exact (mul_dvd_mul_iff_left (by norm_num : (599 : ℤ) ≠ 0)).mp e
    have hdy2 : ∀ n, (599 : ℤ) ^ 2 ∣ Δ_[598] y n := by
      intro n
      have e := dvd_sub (hz2 (n + 598)) (hz2 n)
      have hid : y (n + 598) + 299 * Δ_[598] y (n + 598) - (y n + 299 * Δ_[598] y n)
          = Δ_[598] y n + 299 * (Δ_[598])^[2] y n := by
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
          _root_.fwdDiff]
        ring
      rw [hid] at e
      have e2 := dvd_mul_of_dvd_right (hd2y n) 299
      simpa using dvd_sub e e2
    apply hn0
    have e := dvd_sub (hz2 n0) (dvd_mul_of_dvd_right (hdy2 n0) 299)
    simpa using e

/-- **Part (ii) at `p = 599`**: the chain of exact periods. -/
theorem chain_599 (hne : period (599 ^ 2) ≠ period 599) (i : ℕ) :
    IsPeriodMod (599 ^ (1 + i)) (599 ^ i * 598) ∧
      ¬ IsPeriodMod (599 ^ (1 + i + 1)) (599 ^ i * 598) := by
  have hnot : ¬ IsPeriodMod (599 ^ 2) 598 := period_599 ▸ not_isPeriodMod_sq (by norm_num) hne
  rcases i with _ | k
  · exact ⟨by simpa using isPeriodMod_599, by simpa using hnot⟩
  · obtain ⟨n0, hn0⟩ := exists_not_dvd_of_not_isPeriodMod (by norm_num) hnot
    obtain ⟨hall, n1, hn1⟩ := lift_599 (n0 := n0) (by exact_mod_cast hn0)
    have hrw : 599 ^ (k + 1) * 598 = 599 ^ k * (599 * 598) := by ring
    rw [hrw, show 1 + (k + 1) = 2 + k by ring]
    exact chain_of_lift (by norm_num) (by norm_num) (fun k => (lift_iter (p := 599)
      (Raises 599 1 1) (fun t h => h.mul 599)
      (fun t j h hj n => step_strong (by norm_num) (by norm_num) h isRec_luc5 hj n)
      (by norm_num) raises_599.strong_of_weak hall hn1 k).2) k

/-! ## Part (ii): odd primes -/

/-- **Part (ii)** (Chai Wah Wu's conjecture in A106297, Feb 25 2022): for every
prime `p > 2` with `a(p²) ≠ a(p)`, `a(p^k) = p^(k-1) · a(p)` for all `k ≥ 1`, where
`a = period` is the least period of the Lucas 5-step sequence A074048. -/
theorem period_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hne : period (p ^ 2) ≠ period p) (k : ℕ) (hk : 1 ≤ k) :
    period (p ^ k) = p ^ (k - 1) * period p := by
  obtain ⟨i, rfl⟩ : ∃ i, k = 1 + i := ⟨k - 1, by omega⟩
  rw [show 1 + i - 1 = i by omega]
  by_cases h599 : p = 599
  · subst h599
    rw [period_599]
    exact period_eq_of_chain hp (by simpa using period_599) (chain_599 hne) i
  · have ht := isPeriodMod_period hp.pos
    have hR := raises_of_isPeriodMod hp (by omega) h599 ht
    have hnot := not_isPeriodMod_sq hp.pos hne
    obtain ⟨n0, hn0⟩ := exists_not_dvd_of_not_isPeriodMod ht.1 hnot
    have hj : ∀ n, (p : ℤ) ^ 1 ∣ Δ_[period p] luc5 n := fun n => by
      rw [pow_one]
      exact ht.2 n
    have hlift := lift_iter (p := p) (Raises p 1 1) (fun t h => h.mul p)
      (fun t j h hj n => step_strong hp (by omega) h isRec_luc5 hj n) hp.ne_zero hR hj
      (n0 := n0) (by exact_mod_cast hn0)
    exact period_eq_of_chain hp (by simp)
      (chain_of_lift ht.1 hp.ne_zero (fun k => (hlift k).2)) i

/-! ## Part (i): powers of two -/

/-- `Δ_[12]` raises `2`-adic valuations by `2` on recurrence sequences (finite check
on `imp` modulo `4`). -/
theorem raises_two : Raises 2 2 1 12 := by
  apply raises_of_imp (by norm_num)
  simp only [Function.iterate_one]
  refine (isRec_imp.fwdDiff 12).dvd_of_lt_five ?_
  decide

/-- `period 4 = 6` (A106297(4) = 6). -/
theorem period_four : period 4 = 6 := by
  have h6 : IsPeriodMod 4 6 := isPeriodMod_of_lt_five (by norm_num) (by decide)
  refine period_eq_of h6 fun d hd hper => ?_
  by_contra hlt
  push Not at hlt
  have hcases : ∀ d ∈ Nat.divisors 6, d < 6 → d ∣ 2 ∨ d ∣ 3 := by decide
  have hn2 : ¬ IsPeriodMod 4 2 := fun h => by
    have := h.2 0
    revert this
    decide
  have hn3 : ¬ IsPeriodMod 4 3 := fun h => by
    have := h.2 0
    revert this
    decide
  rcases hcases d (Nat.mem_divisors.mpr ⟨hd, by norm_num⟩) hlt with h | h
  · exact not_isPeriodMod_of_dvd h (by norm_num) hn2 hper
  · exact not_isPeriodMod_of_dvd h (by norm_num) hn3 hper

/-- The chain of exact periods at powers of `2`, starting from modulus `4`. -/
theorem chain_two (i : ℕ) :
    IsPeriodMod (2 ^ (2 + i)) (2 ^ i * 6) ∧ ¬ IsPeriodMod (2 ^ (2 + i + 1)) (2 ^ i * 6) := by
  rcases i with _ | k
  · refine ⟨isPeriodMod_of_lt_five (by norm_num) (by decide), fun h => ?_⟩
    have := h.2 0
    revert this
    decide
  · have hj : ∀ n, ((2 : ℕ) : ℤ) ^ 3 ∣ Δ_[12] luc5 n :=
      (isRec_luc5.fwdDiff 12).dvd_of_lt_five (by decide)
    have hn1 : ¬ ((2 : ℕ) : ℤ) ^ (3 + 1) ∣ Δ_[12] luc5 1 := by decide
    have hlift := lift_iter (p := 2) (Raises 2 2 1) (fun t h => h.mul 2)
      (fun t j h hj n => by
        have e := step_two h isRec_luc5 (j := j) (by exact_mod_cast hj) n
        exact_mod_cast e)
      (by norm_num) raises_two hj hn1
    have hrw : 2 ^ (k + 1) * 6 = 2 ^ k * 12 := by ring
    rw [hrw, show 2 + (k + 1) = 3 + k by ring]
    exact chain_of_lift (by norm_num) (by norm_num) (fun k => (hlift k).2) k

/-- **Part (i)** (Chai Wah Wu's conjecture in A106297, Feb 25 2022):
`a(2^k) = 3 · 2^(k-1)` for every `k ≥ 2`. -/
theorem period_two_pow (k : ℕ) (hk : 2 ≤ k) : period (2 ^ k) = 3 * 2 ^ (k - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = 2 + i := ⟨k - 2, by omega⟩
  rw [period_eq_of_chain Nat.prime_two (by simpa using period_four) chain_two i,
    show 2 + i - 1 = i + 1 by omega, pow_succ]
  ring

/-! ## Part (iii): powers of five -/

/-- `period 5 = 781` (A106297(5) = 781). -/
theorem period_five : period 5 = 781 := by
  have h781 : IsPeriodMod 5 781 :=
    isPeriodMod_of_lt_five (by norm_num) (by set_option maxRecDepth 100000 in decide)
  refine period_eq_of h781 fun d hd hper => ?_
  by_contra hlt
  push Not at hlt
  have hcases : ∀ d ∈ Nat.divisors 781, d < 781 → d ∣ 11 ∨ d ∣ 71 := by
    set_option maxRecDepth 100000 in decide
  have hn11 : ¬ IsPeriodMod 5 11 := fun h => by
    have := h.2 1
    revert this
    decide
  have hn71 : ¬ IsPeriodMod 5 71 := fun h => by
    have := h.2 0
    revert this
    decide
  rcases hcases d (Nat.mem_divisors.mpr ⟨hd, by norm_num⟩) hlt with h | h
  · exact not_isPeriodMod_of_dvd h (by norm_num) hn11 hper
  · exact not_isPeriodMod_of_dvd h (by norm_num) hn71 hper

/-- `period 25 ≠ period 5`: `781` is not a period modulo `25`. -/
theorem period_twentyfive_ne : period (5 ^ 2) ≠ period 5 := by
  intro h
  have hper := isPeriodMod_period (m := 5 ^ 2) (by norm_num)
  rw [h, period_five] at hper
  have := hper.2 1
  revert this
  set_option maxRecDepth 100000 in decide

/-- **Part (iii)** (Chai Wah Wu's conjecture in A106297, Feb 25 2022):
`a(5^k) = 781 · 5^(k-1)` for every `k ≥ 1`. -/
theorem period_five_pow (k : ℕ) (hk : 1 ≤ k) : period (5 ^ k) = 781 * 5 ^ (k - 1) := by
  rw [period_prime_pow 5 (by norm_num) (by norm_num) period_twentyfive_ne k hk, period_five,
    mul_comm]

/-! ## The conjecture -/

/-- **Chai Wah Wu's conjectures on A106297** (formula section of A106297,
Feb 25 2022).  Let `a(m)` be the least period of the Lucas 5-step sequence
A074048 (`5, 1, 3, 7, 15`, then each term the sum of the previous five) modulo `m`.
Then (i) `a(2^k) = 3 · 2^(k-1)` for `k ≥ 2`; (ii) for every prime `p > 2` with
`a(p²) ≠ a(p)`, `a(p^k) = p^(k-1) · a(p)` for all `k ≥ 1`; (iii)
`a(5^k) = 781 · 5^(k-1)` for `k ≥ 1`. -/
theorem conjecture :
    (∀ k : ℕ, 2 ≤ k → period (2 ^ k) = 3 * 2 ^ (k - 1)) ∧
    (∀ p : ℕ, p.Prime → 2 < p → period (p ^ 2) ≠ period p →
      ∀ k : ℕ, 1 ≤ k → period (p ^ k) = p ^ (k - 1) * period p) ∧
    (∀ k : ℕ, 1 ≤ k → period (5 ^ k) = 781 * 5 ^ (k - 1)) :=
  ⟨period_two_pow, period_prime_pow, period_five_pow⟩

/-! ## Ground truth and non-vacuity -/

/-- The hypothesis of part (ii) is satisfiable: it holds at `p = 5`. -/
example : Nat.Prime 5 ∧ 2 < 5 ∧ period (5 ^ 2) ≠ period 5 :=
  ⟨by norm_num, by norm_num, period_twentyfive_ne⟩

/-- A106297(4) = 6, A106297(5) = 781, and A106297(599) = 598 (from the entry's data
and the 599 comment). -/
example : period 4 = 6 ∧ period 5 = 781 ∧ period 599 = 598 :=
  ⟨period_four, period_five, period_599⟩

end Candidates.A106297LucasStepInitial
