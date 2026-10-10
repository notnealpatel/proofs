import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Erdos1052

/-- The source residue and prime conditions put the odd component base at least 73. -/
theorem a12_e3_base_le (p : ℕ) (hp : p.Prime) (hp13 : 13 < p)
    (hp24 : p % 24 = 1) : 73 ≤ p := by
  by_contra hn
  have hcases : p = 25 ∨ p = 49 := by omega
  rcases hcases with h | h <;> subst p <;> norm_num at hp

/-- Outside the fixed core, an odd prime below 23 is 11, 17, or 19. -/
theorem a12_square_base_gap (q : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13) :
    q = 11 ∨ q = 17 ∨ q = 19 ∨ 23 ≤ q := by
  by_cases h : 23 ≤ q
  · exact Or.inr (Or.inr (Or.inr h))
  · have hb : q ≤ 22 := by omega
    interval_cases q <;> norm_num [Nat.odd_iff] at *

example : Nat.Prime 73 ∧ 13 < (73 : ℕ) ∧ (73 : ℕ) % 24 = 1 := by decide
example : Nat.Prime 17 ∧ Odd (17 : ℕ) ∧ (17 : ℕ) ≠ 3 ∧
    (17 : ℕ) ≠ 5 ∧ (17 : ℕ) ≠ 7 ∧ (17 : ℕ) ≠ 13 := by decide

/-- Without an 11-square seed, a square denominator is at least 289;
only bases 17 and 19 require this weaker bound instead of 529. -/
theorem a12_no_seed_denominator_le (q d : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13)
    (hd : 0 < d) (hn : ¬ (q = 11 ∧ d = 1)) :
    (if q = 17 ∨ q = 19 then 289 else 529) ≤ q ^ (2 * d) := by
  have hg := a12_square_base_gap q hq ho h3 h5 h7 h13
  rcases hg with h11 | h17 | h19 | h23
  · subst q
    have h4 : 4 ≤ 2 * d := by omega
    simpa using (show 529 ≤ 11 ^ (2 * d) from
      (by norm_num : 529 ≤ (11 : ℕ) ^ 4).trans
        (Nat.pow_le_pow_right (by decide) h4))
  · subst q
    simpa using (show 289 ≤ 17 ^ (2 * d) from
      (by norm_num : 289 ≤ (17 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_right (by decide) (by omega)))
  · subst q
    simpa using (show 289 ≤ 19 ^ (2 * d) from
      (by norm_num : 289 ≤ (19 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_right (by decide) (by omega)))
  · have hexc : ¬ (q = 17 ∨ q = 19) := by omega
    simp only [if_neg hexc]
    calc
      529 = 23 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left h23 2
      _ ≤ q ^ (2 * d) := Nat.pow_le_pow_right hq.pos (by omega)

/-- The reciprocal bound transfers the integer denominator estimate to rational abundance. -/
theorem a12_no_seed_ratio_le (q d : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13)
    (hd : 0 < d) (hn : ¬ (q = 11 ∧ d = 1)) :
    1 + 1 / (q ^ (2 * d) : ℚ) ≤
      if q = 17 ∨ q = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ) := by
  have hb := a12_no_seed_denominator_le q d hq ho h3 h5 h7 h13 hd hn
  split_ifs with h
  · rw [if_pos h] at hb
    have hbq : (289 : ℚ) ≤ q ^ (2 * d) := by exact_mod_cast hb
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 289) hbq
    have hh := add_le_add_left hi 1
    norm_num at hh ⊢
    simpa only [add_comm] using hh
  · rw [if_neg h] at hb
    have hbq : (529 : ℚ) ≤ q ^ (2 * d) := by exact_mod_cast hb
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 529) hbq
    have hh := add_le_add_left hi 1
    norm_num at hh ⊢
    simpa only [add_comm] using hh

example : ¬ ((11 : ℕ) = 11 ∧ (2 : ℕ) = 1) ∧ 0 < (2 : ℕ) ∧
    Nat.Prime 11 ∧ Odd (11 : ℕ) ∧ (11 : ℕ) ≠ 3 ∧ (11 : ℕ) ≠ 5 ∧
    (11 : ℕ) ≠ 7 ∧ (11 : ℕ) ≠ 13 := by decide

/-- Five distinct bases admit at most two of the exceptional rational factors. -/
theorem a12_five_caps_le (q1 q2 q3 q4 q5 : ℕ)
    (hd : List.Pairwise (· ≠ ·) [q1, q2, q3, q4, q5]) :
    (if q1 = 17 ∨ q1 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q2 = 17 ∨ q2 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q3 = 17 ∨ q3 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q4 = 17 ∨ q4 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q5 = 17 ∨ q5 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) ≤
      (290 / 289 : ℚ) ^ 2 * (530 / 529 : ℚ) ^ 3 := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_false] at hd
  split_ifs <;> norm_num <;> omega

example : List.Pairwise (· ≠ ·) ([17, 19, 23, 29, 31] : List ℕ) := by decide

/-- For e at least three, the full a=12 identity forces an actual 11-square
among the five unspecified square slots. No assertion is made for e=1. -/
theorem a12_e3_forces_eleven_square
    (p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1)
    (_he : 0 < e) (_heodd : Odd e) (he3 : 3 ≤ e)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hd4 : 0 < d4) (hd5 : 0 < d5)
    (hcomponents : ∀ q ∈ ({q1, q2, q3, q4, q5} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, q1, q2, q3, q4, q5])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) *
      (q3 ^ (2 * d3) + 1) * (q4 ^ (2 * d4) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * q1 ^ (2 * d1) * q2 ^ (2 * d2) *
        q3 ^ (2 * d3) * q4 ^ (2 * d4) * q5 ^ (2 * d5)) :
    (q1 = 11 ∧ d1 = 1) ∨ (q2 = 11 ∧ d2 = 1) ∨ (q3 = 11 ∧ d3 = 1) ∨
      (q4 = 11 ∧ d4 = 1) ∨ (q5 = 11 ∧ d5 = 1) := by
  by_contra hn
  have hc1 := hcomponents q1 (by simp)
  have hn1 : ¬ (q1 = 11 ∧ d1 = 1) := fun h => hn (Or.inl h)
  have hb1 := a12_no_seed_ratio_le q1 d1 hc1.1 hc1.2.1 hc1.2.2.1
    hc1.2.2.2.1 hc1.2.2.2.2.1 hc1.2.2.2.2.2 hd1 hn1
  have hc2 := hcomponents q2 (by simp)
  have hn2 : ¬ (q2 = 11 ∧ d2 = 1) := fun h => hn (Or.inr (Or.inl h))
  have hb2 := a12_no_seed_ratio_le q2 d2 hc2.1 hc2.2.1 hc2.2.2.1
    hc2.2.2.2.1 hc2.2.2.2.2.1 hc2.2.2.2.2.2 hd2 hn2
  have hc3 := hcomponents q3 (by simp)
  have hn3 : ¬ (q3 = 11 ∧ d3 = 1) := fun h => hn (Or.inr (Or.inr (Or.inl h)))
  have hb3 := a12_no_seed_ratio_le q3 d3 hc3.1 hc3.2.1 hc3.2.2.1
    hc3.2.2.2.1 hc3.2.2.2.2.1 hc3.2.2.2.2.2 hd3 hn3
  have hc4 := hcomponents q4 (by simp)
  have hn4 : ¬ (q4 = 11 ∧ d4 = 1) := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hb4 := a12_no_seed_ratio_le q4 d4 hc4.1 hc4.2.1 hc4.2.2.1
    hc4.2.2.2.1 hc4.2.2.2.2.1 hc4.2.2.2.2.2 hd4 hn4
  have hc5 := hcomponents q5 (by simp)
  have hn5 : ¬ (q5 = 11 ∧ d5 = 1) := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (h)))))
  have hb5 := a12_no_seed_ratio_le q5 d5 hc5.1 hc5.2.1 hc5.2.2.1
    hc5.2.2.2.1 hc5.2.2.2.2.1 hc5.2.2.2.2.2 hd5 hn5
  have hp73 := a12_e3_base_le p hp hp13 hp24
  have hpe : 73 ^ 3 ≤ p ^ e :=
    (Nat.pow_le_pow_left hp73 3).trans (Nat.pow_le_pow_right hp.pos he3)
  have hpeq : (73 ^ 3 : ℚ) ≤ (p : ℚ) ^ e := by exact_mod_cast hpe
  have hbp : 1 + 1 / (p : ℚ) ^ e ≤ 1 + 1 / (73 ^ 3 : ℚ) := by
    simpa only [add_comm] using
      add_le_add_left (one_div_le_one_div_of_le (by norm_num) hpeq) (1 : ℚ)
  have hz1 : (q1 : ℚ) ^ (2 * d1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc1.1.ne_zero)
  have hz2 : (q2 : ℚ) ^ (2 * d2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc2.1.ne_zero)
  have hz3 : (q3 : ℚ) ^ (2 * d3) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc3.1.ne_zero)
  have hz4 : (q4 : ℚ) ^ (2 * d4) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc4.1.ne_zero)
  have hz5 : (q5 : ℚ) ^ (2 * d5) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc5.1.ne_zero)
  have hzp : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hidq : (4097 : ℚ) * ((p : ℚ) ^ e + 1) *
      ((q1 : ℚ) ^ (2 * d1) + 1) * ((q2 : ℚ) ^ (2 * d2) + 1) *
      ((q3 : ℚ) ^ (2 * d3) + 1) * ((q4 : ℚ) ^ (2 * d4) + 1) *
      ((q5 : ℚ) ^ (2 * d5) + 1) =
      4160 * (p : ℚ) ^ e * (q1 : ℚ) ^ (2 * d1) * (q2 : ℚ) ^ (2 * d2) *
        (q3 : ℚ) ^ (2 * d3) * (q4 : ℚ) ^ (2 * d4) * (q5 : ℚ) ^ (2 * d5) := by
    norm_num at hid
    exact_mod_cast hid
  have hratio : (1 + 1 / 4096 : ℚ) * (1 + 1 / (p : ℚ) ^ e) *
      (1 + 1 / (q1 : ℚ) ^ (2 * d1)) * (1 + 1 / (q2 : ℚ) ^ (2 * d2)) *
      (1 + 1 / (q3 : ℚ) ^ (2 * d3)) * (1 + 1 / (q4 : ℚ) ^ (2 * d4)) *
      (1 + 1 / (q5 : ℚ) ^ (2 * d5)) = 65 / 64 := by
    field_simp
    nlinarith only [hidq]
  have hcap := a12_five_caps_le q1 q2 q3 q4 q5 (List.pairwise_cons.mp hdistinct).2
  have hprod :
    (1 + 1 / (q1 : ℚ) ^ (2 * d1)) * (1 + 1 / (q2 : ℚ) ^ (2 * d2)) * (1 + 1 / (q3 : ℚ) ^ (2 * d3)) * (1 + 1 / (q4 : ℚ) ^ (2 * d4)) * (1 + 1 / (q5 : ℚ) ^ (2 * d5)) ≤
      (if q1 = 17 ∨ q1 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q2 = 17 ∨ q2 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q3 = 17 ∨ q3 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q4 = 17 ∨ q4 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) * (if q5 = 17 ∨ q5 = 19 then (290 / 289 : ℚ) else (530 / 529 : ℚ)) := by
    gcongr
  have hprod' := hprod.trans hcap
  have hbound : (1 + 1 / 4096 : ℚ) * (1 + 1 / (p : ℚ) ^ e) *
      ((1 + 1 / (q1 : ℚ) ^ (2 * d1)) * (1 + 1 / (q2 : ℚ) ^ (2 * d2)) *
       (1 + 1 / (q3 : ℚ) ^ (2 * d3)) * (1 + 1 / (q4 : ℚ) ^ (2 * d4)) *
       (1 + 1 / (q5 : ℚ) ^ (2 * d5))) ≤
      (1 + 1 / 4096 : ℚ) * (1 + 1 / (73 ^ 3 : ℚ)) *
        ((290 / 289 : ℚ) ^ 2 * (530 / 529 : ℚ) ^ 3) := by
    gcongr
  have hratio' : (1 + 1 / 4096 : ℚ) * (1 + 1 / (p : ℚ) ^ e) *
      ((1 + 1 / (q1 : ℚ) ^ (2 * d1)) * (1 + 1 / (q2 : ℚ) ^ (2 * d2)) *
       (1 + 1 / (q3 : ℚ) ^ (2 * d3)) * (1 + 1 / (q4 : ℚ) ^ (2 * d4)) *
       (1 + 1 / (q5 : ℚ) ^ (2 * d5))) = 65 / 64 := by
    convert hratio using 1
    ring
  rw [hratio'] at hbound
  norm_num at hbound

example : Nat.Prime 73 ∧ 13 < (73 : ℕ) ∧ (73 : ℕ) % 24 = 1 ∧
    0 < (3 : ℕ) ∧ Odd (3 : ℕ) ∧ 3 ≤ (3 : ℕ) ∧
    0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧
    (∀ q ∈ ({11, 17, 19, 23, 29} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13) ∧
    List.Pairwise (· ≠ ·) ([73, 11, 17, 19, 23, 29] : List ℕ) := by decide

end Erdos1052
