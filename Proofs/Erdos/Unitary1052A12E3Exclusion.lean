import Erdos.Unitary1052A12E3Force61

set_option autoImplicit false

namespace Erdos1052

/-- An allowed residual prime below 29, after removing 11 and 61, is 17, 19, or 23. -/
theorem a12_residual_gap (q : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13)
    (h11 : q ≠ 11) : q = 17 ∨ q = 19 ∨ q = 23 ∨ 29 ≤ q := by
  by_cases h : 29 ≤ q
  · exact Or.inr (Or.inr (Or.inr h))
  · have hb : q ≤ 28 := by omega
    interval_cases q <;> norm_num [Nat.odd_iff] at *

example : Nat.Prime 23 ∧ Odd (23 : ℕ) ∧ (23 : ℕ) ≠ 3 ∧
    (23 : ℕ) ≠ 5 ∧ (23 : ℕ) ≠ 7 ∧ (23 : ℕ) ≠ 13 ∧ (23 : ℕ) ≠ 11 := by decide

/-- Absence of the actual 17-square gives a denominator cap, not absence of its base. -/
theorem a12_no_17_denominator (q d : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13)
    (h11 : q ≠ 11) (hd : 0 < d) (hn : ¬ (q = 17 ∧ d = 1)) :
    (if q = 19 then 361 else if q = 23 then 529 else 841) ≤ q ^ (2 * d) := by
  have hg := a12_residual_gap q hq ho h3 h5 h7 h13 h11
  rcases hg with h17 | h19 | h23 | h29
  · subst q
    have he : 4 ≤ 2 * d := by omega
    simpa using (show 841 ≤ 17 ^ (2 * d) from
      (by norm_num : 841 ≤ (17 : ℕ) ^ 4).trans
        (Nat.pow_le_pow_right (by decide) he))
  · subst q
    have he : 2 ≤ 2 * d := by omega
    simpa using (show 361 ≤ 19 ^ (2 * d) from
      (by norm_num : 361 ≤ (19 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_right (by decide) he))
  · subst q
    have he : 2 ≤ 2 * d := by omega
    simpa using (show 529 ≤ 23 ^ (2 * d) from
      (by norm_num : 529 ≤ (23 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_right (by decide) he))
  · have hx : q ≠ 19 := by omega
    have h23 : q ≠ 23 := by omega
    simp only [if_neg hx, if_neg h23]
    calc
      841 = 29 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left h29 2
      _ ≤ q ^ (2 * d) := Nat.pow_le_pow_right hq.pos (by omega)

/-- The integer cap bounds the rational abundance of every positive residual power. -/
theorem a12_no_17_ratio (q d : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13)
    (h11 : q ≠ 11) (hd : 0 < d) (hn : ¬ (q = 17 ∧ d = 1)) :
    1 + 1 / (q : ℚ) ^ (2 * d) ≤
      if q = 19 then (362 / 361 : ℚ) else if q = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ) := by
  have hb := a12_no_17_denominator q d hq ho h3 h5 h7 h13 h11 hd hn
  split_ifs at hb ⊢ <;>
    (have hbq := (show ((_: ℕ) : ℚ) ≤ (q : ℚ) ^ (2 * d) from by exact_mod_cast hb)
     have hi := add_le_add_left (one_div_le_one_div_of_le (by norm_num) hbq) (1 : ℚ)
     norm_num at hi ⊢
     linarith)

/-- Three distinct residual bases use each exceptional cap at most once. -/
theorem a12_no_17_three_caps (q1 q2 q3 : ℕ)
    (hd : List.Pairwise (· ≠ ·) [q1, q2, q3]) :
    (if q1 = 19 then (362 / 361 : ℚ) else if q1 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
    (if q2 = 19 then (362 / 361 : ℚ) else if q2 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
    (if q3 = 19 then (362 / 361 : ℚ) else if q3 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) ≤
    (362 / 361 : ℚ) * (530 / 529) * (842 / 841) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_false] at hd
  split_ifs <;> norm_num <;> omega

example : ¬ ((17 : ℕ) = 17 ∧ (2 : ℕ) = 1) ∧ 0 < (2 : ℕ) := by decide
example : List.Pairwise (· ≠ ·) ([19, 23, 29] : List ℕ) := by decide

/-- Absence of the actual 19-square gives a denominator cap, not absence of its base. -/
theorem a12_no_19_denominator (q d : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13)
    (h11 : q ≠ 11) (hd : 0 < d) (hn : ¬ (q = 19 ∧ d = 1)) :
    (if q = 17 then 289 else if q = 23 then 529 else 841) ≤ q ^ (2 * d) := by
  have hg := a12_residual_gap q hq ho h3 h5 h7 h13 h11
  rcases hg with h17 | h19 | h23 | h29
  · subst q
    have he : 2 ≤ 2 * d := by omega
    simpa using (show 289 ≤ 17 ^ (2 * d) from
      (by norm_num : 289 ≤ (17 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_right (by decide) he))
  · subst q
    have he : 4 ≤ 2 * d := by omega
    simpa using (show 841 ≤ 19 ^ (2 * d) from
      (by norm_num : 841 ≤ (19 : ℕ) ^ 4).trans
        (Nat.pow_le_pow_right (by decide) he))
  · subst q
    have he : 2 ≤ 2 * d := by omega
    simpa using (show 529 ≤ 23 ^ (2 * d) from
      (by norm_num : 529 ≤ (23 : ℕ) ^ 2).trans
        (Nat.pow_le_pow_right (by decide) he))
  · have hx : q ≠ 17 := by omega
    have h23 : q ≠ 23 := by omega
    simp only [if_neg hx, if_neg h23]
    calc
      841 = 29 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left h29 2
      _ ≤ q ^ (2 * d) := Nat.pow_le_pow_right hq.pos (by omega)

/-- The integer cap bounds the rational abundance of every positive residual power. -/
theorem a12_no_19_ratio (q d : ℕ) (hq : q.Prime) (ho : Odd q)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h7 : q ≠ 7) (h13 : q ≠ 13)
    (h11 : q ≠ 11) (hd : 0 < d) (hn : ¬ (q = 19 ∧ d = 1)) :
    1 + 1 / (q : ℚ) ^ (2 * d) ≤
      if q = 17 then (290 / 289 : ℚ) else if q = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ) := by
  have hb := a12_no_19_denominator q d hq ho h3 h5 h7 h13 h11 hd hn
  split_ifs at hb ⊢ <;>
    (have hbq := (show ((_: ℕ) : ℚ) ≤ (q : ℚ) ^ (2 * d) from by exact_mod_cast hb)
     have hi := add_le_add_left (one_div_le_one_div_of_le (by norm_num) hbq) (1 : ℚ)
     norm_num at hi ⊢
     linarith)

/-- Three distinct residual bases use each exceptional cap at most once. -/
theorem a12_no_19_three_caps (q1 q2 q3 : ℕ)
    (hd : List.Pairwise (· ≠ ·) [q1, q2, q3]) :
    (if q1 = 17 then (290 / 289 : ℚ) else if q1 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
    (if q2 = 17 then (290 / 289 : ℚ) else if q2 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
    (if q3 = 17 then (290 / 289 : ℚ) else if q3 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) ≤
    (290 / 289 : ℚ) * (530 / 529) * (842 / 841) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_false] at hd
  split_ifs <;> norm_num <;> omega

example : ¬ ((19 : ℕ) = 19 ∧ (2 : ℕ) = 1) ∧ 0 < (2 : ℕ) := by decide
example : List.Pairwise (· ≠ ·) ([17, 23, 29] : List ℕ) := by decide

/-- The ordered full identity with the paid 11 and 61 slots forces an actual 17-square. -/
theorem a12_e3_ordered_forces_17
    (p e c r1 r2 r3 b1 b2 b3 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1) (he3 : 3 ≤ e)
    (hc : 0 < c) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hcomponents : ∀ r ∈ ({r1, r2, r3} : Finset ℕ),
      r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, 11, 61, r1, r2, r3])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) * (61 ^ (2 * c) + 1) *
      (r1 ^ (2 * b1) + 1) * (r2 ^ (2 * b2) + 1) * (r3 ^ (2 * b3) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * 61 ^ (2 * c) *
        r1 ^ (2 * b1) * r2 ^ (2 * b2) * r3 ^ (2 * b3)) :
    (r1 = 17 ∧ b1 = 1) ∨ (r2 = 17 ∧ b2 = 1) ∨ (r3 = 17 ∧ b3 = 1) := by
  by_contra hn
  have hcomp1 := hcomponents r1 (by simp)
  have hn1 : ¬ (r1 = 17 ∧ b1 = 1) := by tauto
  have h111 : r1 ≠ 11 := Ne.symm ((List.pairwise_cons.mp
    (List.pairwise_cons.mp hdistinct).2).1 r1 (by simp))
  have hbnd1 := a12_no_17_ratio r1 b1 hcomp1.1 hcomp1.2.1 hcomp1.2.2.1
    hcomp1.2.2.2.1 hcomp1.2.2.2.2.1 hcomp1.2.2.2.2.2 h111 hb1 hn1
  have hcomp2 := hcomponents r2 (by simp)
  have hn2 : ¬ (r2 = 17 ∧ b2 = 1) := by tauto
  have h112 : r2 ≠ 11 := Ne.symm ((List.pairwise_cons.mp
    (List.pairwise_cons.mp hdistinct).2).1 r2 (by simp))
  have hbnd2 := a12_no_17_ratio r2 b2 hcomp2.1 hcomp2.2.1 hcomp2.2.2.1
    hcomp2.2.2.2.1 hcomp2.2.2.2.2.1 hcomp2.2.2.2.2.2 h112 hb2 hn2
  have hcomp3 := hcomponents r3 (by simp)
  have hn3 : ¬ (r3 = 17 ∧ b3 = 1) := by tauto
  have h113 : r3 ≠ 11 := Ne.symm ((List.pairwise_cons.mp
    (List.pairwise_cons.mp hdistinct).2).1 r3 (by simp))
  have hbnd3 := a12_no_17_ratio r3 b3 hcomp3.1 hcomp3.2.1 hcomp3.2.2.1
    hcomp3.2.2.2.1 hcomp3.2.2.2.2.1 hcomp3.2.2.2.2.2 h113 hb3 hn3
  have hp73 := a12_e3_base_le p hp hp13 hp24
  have hpe : 73 ^ 3 ≤ p ^ e :=
    (Nat.pow_le_pow_left hp73 3).trans (Nat.pow_le_pow_right hp.pos he3)
  have hpeq : (73 ^ 3 : ℚ) ≤ (p : ℚ) ^ e := by exact_mod_cast hpe
  have hbp : 1 + 1 / (p : ℚ) ^ e ≤ 1 + 1 / (73 ^ 3 : ℚ) := by
    simpa only [add_comm] using
      add_le_add_left (one_div_le_one_div_of_le (by norm_num) hpeq) (1 : ℚ)
  have hcpe : 61 ^ 2 ≤ 61 ^ (2 * c) := Nat.pow_le_pow_right (by decide) (by omega)
  have hcpeq : (61 ^ 2 : ℚ) ≤ (61 : ℚ) ^ (2 * c) := by exact_mod_cast hcpe
  have hbc : 1 + 1 / (61 : ℚ) ^ (2 * c) ≤ (3722 / 3721 : ℚ) := by
    have hi := add_le_add_left (one_div_le_one_div_of_le (by norm_num) hcpeq) (1 : ℚ)
    norm_num at hi ⊢
    linarith
  have hzp : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hz1 : (r1 : ℚ) ^ (2 * b1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hcomp1.1.ne_zero)
  have hz2 : (r2 : ℚ) ^ (2 * b2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hcomp2.1.ne_zero)
  have hz3 : (r3 : ℚ) ^ (2 * b3) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hcomp3.1.ne_zero)
  have hidq : (4097 : ℚ) * ((p : ℚ) ^ e + 1) * 122 * ((61 : ℚ) ^ (2 * c) + 1) *
      ((r1 : ℚ) ^ (2 * b1) + 1) * ((r2 : ℚ) ^ (2 * b2) + 1) * ((r3 : ℚ) ^ (2 * b3) + 1) =
      4160 * (p : ℚ) ^ e * 121 * (61 : ℚ) ^ (2 * c) *
        (r1 : ℚ) ^ (2 * b1) * (r2 : ℚ) ^ (2 * b2) * (r3 : ℚ) ^ (2 * b3) := by
    norm_num at hid
    exact_mod_cast hid
  have hratio : (4097 / 4096 : ℚ) * (1 + 1 / (p : ℚ) ^ e) * (122 / 121) *
      (1 + 1 / (61 : ℚ) ^ (2 * c)) *
      ((1 + 1 / (r1 : ℚ) ^ (2 * b1)) * (1 + 1 / (r2 : ℚ) ^ (2 * b2)) *
        (1 + 1 / (r3 : ℚ) ^ (2 * b3))) = 65 / 64 := by
    field_simp
    nlinarith only [hidq]
  have hrds : List.Pairwise (· ≠ ·) [r1, r2, r3] :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hdistinct).2).2).2
  have hcap := a12_no_17_three_caps r1 r2 r3 hrds
  have hprod :
      (1 + 1 / (r1 : ℚ) ^ (2 * b1)) * (1 + 1 / (r2 : ℚ) ^ (2 * b2)) *
      (1 + 1 / (r3 : ℚ) ^ (2 * b3)) ≤
      (if r1 = 19 then (362 / 361 : ℚ) else if r1 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
      (if r2 = 19 then (362 / 361 : ℚ) else if r2 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
      (if r3 = 19 then (362 / 361 : ℚ) else if r3 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) := by
    gcongr
  have hprod' := hprod.trans hcap
  have hbound : (4097 / 4096 : ℚ) * (1 + 1 / (p : ℚ) ^ e) * (122 / 121) *
      (1 + 1 / (61 : ℚ) ^ (2 * c)) *
      ((1 + 1 / (r1 : ℚ) ^ (2 * b1)) * (1 + 1 / (r2 : ℚ) ^ (2 * b2)) *
        (1 + 1 / (r3 : ℚ) ^ (2 * b3))) ≤
      (4097 / 4096 : ℚ) * (1 + 1 / (73 ^ 3 : ℚ)) * (122 / 121) *
        (3722 / 3721) * ((362 / 361) * (530 / 529) * (842 / 841)) := by
    gcongr
  rw [hratio] at hbound
  norm_num at hbound

/-- The ordered full identity with the paid 11 and 61 slots forces an actual 19-square. -/
theorem a12_e3_ordered_forces_19
    (p e c r1 r2 r3 b1 b2 b3 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1) (he3 : 3 ≤ e)
    (hc : 0 < c) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hcomponents : ∀ r ∈ ({r1, r2, r3} : Finset ℕ),
      r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, 11, 61, r1, r2, r3])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) * (61 ^ (2 * c) + 1) *
      (r1 ^ (2 * b1) + 1) * (r2 ^ (2 * b2) + 1) * (r3 ^ (2 * b3) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * 61 ^ (2 * c) *
        r1 ^ (2 * b1) * r2 ^ (2 * b2) * r3 ^ (2 * b3)) :
    (r1 = 19 ∧ b1 = 1) ∨ (r2 = 19 ∧ b2 = 1) ∨ (r3 = 19 ∧ b3 = 1) := by
  by_contra hn
  have hcomp1 := hcomponents r1 (by simp)
  have hn1 : ¬ (r1 = 19 ∧ b1 = 1) := by tauto
  have h111 : r1 ≠ 11 := Ne.symm ((List.pairwise_cons.mp
    (List.pairwise_cons.mp hdistinct).2).1 r1 (by simp))
  have hbnd1 := a12_no_19_ratio r1 b1 hcomp1.1 hcomp1.2.1 hcomp1.2.2.1
    hcomp1.2.2.2.1 hcomp1.2.2.2.2.1 hcomp1.2.2.2.2.2 h111 hb1 hn1
  have hcomp2 := hcomponents r2 (by simp)
  have hn2 : ¬ (r2 = 19 ∧ b2 = 1) := by tauto
  have h112 : r2 ≠ 11 := Ne.symm ((List.pairwise_cons.mp
    (List.pairwise_cons.mp hdistinct).2).1 r2 (by simp))
  have hbnd2 := a12_no_19_ratio r2 b2 hcomp2.1 hcomp2.2.1 hcomp2.2.2.1
    hcomp2.2.2.2.1 hcomp2.2.2.2.2.1 hcomp2.2.2.2.2.2 h112 hb2 hn2
  have hcomp3 := hcomponents r3 (by simp)
  have hn3 : ¬ (r3 = 19 ∧ b3 = 1) := by tauto
  have h113 : r3 ≠ 11 := Ne.symm ((List.pairwise_cons.mp
    (List.pairwise_cons.mp hdistinct).2).1 r3 (by simp))
  have hbnd3 := a12_no_19_ratio r3 b3 hcomp3.1 hcomp3.2.1 hcomp3.2.2.1
    hcomp3.2.2.2.1 hcomp3.2.2.2.2.1 hcomp3.2.2.2.2.2 h113 hb3 hn3
  have hp73 := a12_e3_base_le p hp hp13 hp24
  have hpe : 73 ^ 3 ≤ p ^ e :=
    (Nat.pow_le_pow_left hp73 3).trans (Nat.pow_le_pow_right hp.pos he3)
  have hpeq : (73 ^ 3 : ℚ) ≤ (p : ℚ) ^ e := by exact_mod_cast hpe
  have hbp : 1 + 1 / (p : ℚ) ^ e ≤ 1 + 1 / (73 ^ 3 : ℚ) := by
    simpa only [add_comm] using
      add_le_add_left (one_div_le_one_div_of_le (by norm_num) hpeq) (1 : ℚ)
  have hcpe : 61 ^ 2 ≤ 61 ^ (2 * c) := Nat.pow_le_pow_right (by decide) (by omega)
  have hcpeq : (61 ^ 2 : ℚ) ≤ (61 : ℚ) ^ (2 * c) := by exact_mod_cast hcpe
  have hbc : 1 + 1 / (61 : ℚ) ^ (2 * c) ≤ (3722 / 3721 : ℚ) := by
    have hi := add_le_add_left (one_div_le_one_div_of_le (by norm_num) hcpeq) (1 : ℚ)
    norm_num at hi ⊢
    linarith
  have hzp : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hz1 : (r1 : ℚ) ^ (2 * b1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hcomp1.1.ne_zero)
  have hz2 : (r2 : ℚ) ^ (2 * b2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hcomp2.1.ne_zero)
  have hz3 : (r3 : ℚ) ^ (2 * b3) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hcomp3.1.ne_zero)
  have hidq : (4097 : ℚ) * ((p : ℚ) ^ e + 1) * 122 * ((61 : ℚ) ^ (2 * c) + 1) *
      ((r1 : ℚ) ^ (2 * b1) + 1) * ((r2 : ℚ) ^ (2 * b2) + 1) * ((r3 : ℚ) ^ (2 * b3) + 1) =
      4160 * (p : ℚ) ^ e * 121 * (61 : ℚ) ^ (2 * c) *
        (r1 : ℚ) ^ (2 * b1) * (r2 : ℚ) ^ (2 * b2) * (r3 : ℚ) ^ (2 * b3) := by
    norm_num at hid
    exact_mod_cast hid
  have hratio : (4097 / 4096 : ℚ) * (1 + 1 / (p : ℚ) ^ e) * (122 / 121) *
      (1 + 1 / (61 : ℚ) ^ (2 * c)) *
      ((1 + 1 / (r1 : ℚ) ^ (2 * b1)) * (1 + 1 / (r2 : ℚ) ^ (2 * b2)) *
        (1 + 1 / (r3 : ℚ) ^ (2 * b3))) = 65 / 64 := by
    field_simp
    nlinarith only [hidq]
  have hrds : List.Pairwise (· ≠ ·) [r1, r2, r3] :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hdistinct).2).2).2
  have hcap := a12_no_19_three_caps r1 r2 r3 hrds
  have hprod :
      (1 + 1 / (r1 : ℚ) ^ (2 * b1)) * (1 + 1 / (r2 : ℚ) ^ (2 * b2)) *
      (1 + 1 / (r3 : ℚ) ^ (2 * b3)) ≤
      (if r1 = 17 then (290 / 289 : ℚ) else if r1 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
      (if r2 = 17 then (290 / 289 : ℚ) else if r2 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) *
      (if r3 = 17 then (290 / 289 : ℚ) else if r3 = 23 then (530 / 529 : ℚ) else (842 / 841 : ℚ)) := by
    gcongr
  have hprod' := hprod.trans hcap
  have hbound : (4097 / 4096 : ℚ) * (1 + 1 / (p : ℚ) ^ e) * (122 / 121) *
      (1 + 1 / (61 : ℚ) ^ (2 * c)) *
      ((1 + 1 / (r1 : ℚ) ^ (2 * b1)) * (1 + 1 / (r2 : ℚ) ^ (2 * b2)) *
        (1 + 1 / (r3 : ℚ) ^ (2 * b3))) ≤
      (4097 / 4096 : ℚ) * (1 + 1 / (73 ^ 3 : ℚ)) * (122 / 121) *
        (3722 / 3721) * ((290 / 289) * (530 / 529) * (842 / 841)) := by
    gcongr
  rw [hratio] at hbound
  norm_num at hbound

/-- Once four actual slots are 11-square, 61-power, 17-square and 19-square,
29 and 181 must both occupy the sole remaining prime slot, which is impossible. -/
theorem a12_four_forced_slots_false (p e c r d : ℕ)
    (hp : p.Prime) (hp24 : p % 24 = 1) (hr : r.Prime)
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) * (61 ^ (2 * c) + 1) *
      (17 ^ 2 + 1) * (19 ^ 2 + 1) * (r ^ (2 * d) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * 61 ^ (2 * c) * 17 ^ 2 * 19 ^ 2 * r ^ (2 * d)) :
    False := by
  have hp29 : Nat.Prime 29 := by decide
  have hnotp29 : ¬ 29 ∣ p ^ e := by
    intro hd
    have heq : 29 = p := (Nat.prime_dvd_prime_iff_eq hp29 hp).mp (hp29.dvd_of_dvd_pow hd)
    rw [← heq] at hp24
    norm_num at hp24
  have hnot61_29 : ¬ 29 ∣ 61 ^ (2 * c) := by
    intro hd
    have hb := hp29.dvd_of_dvd_pow hd
    norm_num at hb
  have hdiv29 : 29 ∣ (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) * (61 ^ (2 * c) + 1) *
      (17 ^ 2 + 1) * (19 ^ 2 + 1) * (r ^ (2 * d) + 1) := by
    simp only [hp29.dvd_mul]
    norm_num
  rw [hid] at hdiv29
  simp only [hp29.dvd_mul] at hdiv29
  norm_num at hdiv29
  have hrdiv29 : 29 ∣ r ^ (2 * d) := by
    rcases hdiv29 with (h | h) | h
    · exact False.elim (hnotp29 h)
    · exact False.elim (hnot61_29 h)
    · exact h
  have heq29 : 29 = r := (Nat.prime_dvd_prime_iff_eq hp29 hr).mp
    (hp29.dvd_of_dvd_pow hrdiv29)
  have hp181 : Nat.Prime 181 := by norm_num
  have hnotp181 : ¬ 181 ∣ p ^ e := by
    intro hd
    have heq : 181 = p := (Nat.prime_dvd_prime_iff_eq hp181 hp).mp (hp181.dvd_of_dvd_pow hd)
    rw [← heq] at hp24
    norm_num at hp24
  have hnot61_181 : ¬ 181 ∣ 61 ^ (2 * c) := by
    intro hd
    have hb := hp181.dvd_of_dvd_pow hd
    norm_num at hb
  have hdiv181 : 181 ∣ (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) * (61 ^ (2 * c) + 1) *
      (17 ^ 2 + 1) * (19 ^ 2 + 1) * (r ^ (2 * d) + 1) := by
    simp only [hp181.dvd_mul]
    norm_num
  rw [hid] at hdiv181
  simp only [hp181.dvd_mul] at hdiv181
  norm_num at hdiv181
  have hrdiv181 : 181 ∣ r ^ (2 * d) := by
    rcases hdiv181 with (h | h) | h
    · exact False.elim (hnotp181 h)
    · exact False.elim (hnot61_181 h)
    · exact h
  have heq181 : 181 = r := (Nat.prime_dvd_prime_iff_eq hp181 hr).mp
    (hp181.dvd_of_dvd_pow hrdiv181)
  omega

example : Nat.Prime 73 ∧ (73 : ℕ) % 24 = 1 ∧ Nat.Prime 29 := by decide

/-- With the actual 11 and 61 slots ordered first, the full e-at-least-three identity is impossible. -/
theorem a12_e3_ordered_false
    (p e c r1 r2 r3 b1 b2 b3 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1) (he3 : 3 ≤ e)
    (hc : 0 < c) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hcomponents : ∀ r ∈ ({r1, r2, r3} : Finset ℕ),
      r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, 11, 61, r1, r2, r3])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) * (61 ^ (2 * c) + 1) *
      (r1 ^ (2 * b1) + 1) * (r2 ^ (2 * b2) + 1) * (r3 ^ (2 * b3) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * 61 ^ (2 * c) *
        r1 ^ (2 * b1) * r2 ^ (2 * b2) * r3 ^ (2 * b3)) : False := by
  have h17 := a12_e3_ordered_forces_17 p e c r1 r2 r3 b1 b2 b3
    hp hp13 hp24 he3 hc hb1 hb2 hb3 hcomponents hdistinct hid
  have h19 := a12_e3_ordered_forces_19 p e c r1 r2 r3 b1 b2 b3
    hp hp13 hp24 he3 hc hb1 hb2 hb3 hcomponents hdistinct hid
  have hrds : List.Pairwise (· ≠ ·) [r1, r2, r3] :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hdistinct).2).2).2
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_false] at hrds
  rcases h17 with h17 | h17 | h17 <;> rcases h19 with h19 | h19 | h19
  · omega
  · rcases h17 with ⟨hq17, hb17⟩
    rcases h19 with ⟨hq19, hb19⟩
    subst r1
    subst b1
    subst r2
    subst b2
    apply a12_four_forced_slots_false p e c r3 b3 hp hp24
      (hcomponents r3 (by simp)).1
    exact hid
  · rcases h17 with ⟨hq17, hb17⟩
    rcases h19 with ⟨hq19, hb19⟩
    subst r1
    subst b1
    subst r3
    subst b3
    apply a12_four_forced_slots_false p e c r2 b2 hp hp24
      (hcomponents r2 (by simp)).1
    convert hid using 1 <;> ring
  · rcases h17 with ⟨hq17, hb17⟩
    rcases h19 with ⟨hq19, hb19⟩
    subst r2
    subst b2
    subst r1
    subst b1
    apply a12_four_forced_slots_false p e c r3 b3 hp hp24
      (hcomponents r3 (by simp)).1
    convert hid using 1 <;> ring
  · omega
  · rcases h17 with ⟨hq17, hb17⟩
    rcases h19 with ⟨hq19, hb19⟩
    subst r2
    subst b2
    subst r3
    subst b3
    apply a12_four_forced_slots_false p e c r1 b1 hp hp24
      (hcomponents r1 (by simp)).1
    convert hid using 1 <;> ring
  · rcases h17 with ⟨hq17, hb17⟩
    rcases h19 with ⟨hq19, hb19⟩
    subst r3
    subst b3
    subst r1
    subst b1
    apply a12_four_forced_slots_false p e c r2 b2 hp hp24
      (hcomponents r2 (by simp)).1
    convert hid using 1 <;> ring
  · rcases h17 with ⟨hq17, hb17⟩
    rcases h19 with ⟨hq19, hb19⟩
    subst r3
    subst b3
    subst r2
    subst b2
    apply a12_four_forced_slots_false p e c r1 b1 hp hp24
      (hcomponents r1 (by simp)).1
    convert hid using 1 <;> ring
  · omega

example : Nat.Prime 73 ∧ 13 < (73 : ℕ) ∧ (73 : ℕ) % 24 = 1 ∧
    3 ≤ (3 : ℕ) ∧ 0 < (1 : ℕ) ∧
    (∀ r ∈ ({17, 19, 23} : Finset ℕ),
      r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13) ∧
    List.Pairwise (· ≠ ·) ([73, 11, 61, 17, 19, 23] : List ℕ) := by decide

set_option maxHeartbeats 2000000 in
/-- The full five-slot a=12 identity is impossible for positive odd e at least three.
All prime bases are actual distinct components; square exponent parameters stay paired with their bases. -/
theorem a12_e3_false
    (p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1)
    (he : 0 < e) (heodd : Odd e) (he3 : 3 ≤ e)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hd4 : 0 < d4) (hd5 : 0 < d5)
    (hcomponents : ∀ q ∈ ({q1, q2, q3, q4, q5} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, q1, q2, q3, q4, q5])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) *
      (q3 ^ (2 * d3) + 1) * (q4 ^ (2 * d4) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * q1 ^ (2 * d1) * q2 ^ (2 * d2) *
        q3 ^ (2 * d3) * q4 ^ (2 * d4) * q5 ^ (2 * d5)) : False := by
  have h11 := a12_e3_forces_eleven_square p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5
    hp hp13 hp24 he heodd he3 hd1 hd2 hd3 hd4 hd5 hcomponents hdistinct hid
  have h61 := a12_e3_forces_sixty_one_not_dvd_eighty_one p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5
    hp hp13 hp24 he heodd he3 hd1 hd2 hd3 hd4 hd5 hcomponents hdistinct hid
  rcases h11 with h11 | h11 | h11 | h11 | h11 <;>
    rcases h61 with h61 | h61 | h61 | h61 | h61
  · omega
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q1
    subst d1
    subst q2
    have hcomp : ∀ r ∈ ({q3, q4, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 11, 61, q3, q4, q5] [p, 11, 61, q3, q4, q5] :=
      List.Perm.refl _
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q3, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d2 q3 q4 q5 d3 d4 d5
      hp hp13 hp24 he3 hd2 hd3 hd4 hd5 hcomp hdist
    exact hid
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q1
    subst d1
    subst q3
    have hcomp : ∀ r ∈ ({q2, q4, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 11, q2, 61, q4, q5] [p, 11, 61, q2, q4, q5] :=
      (((List.Perm.swap 61 q2 [q4, q5]).cons 11).cons p)
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q2, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d3 q2 q4 q5 d2 d4 d5
      hp hp13 hp24 he3 hd3 hd2 hd4 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q1
    subst d1
    subst q4
    have hcomp : ∀ r ∈ ({q2, q3, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 11, q2, q3, 61, q5] [p, 11, 61, q2, q3, q5] :=
      (((((List.Perm.swap 61 q3 [q5]).cons q2).cons 11).cons p).trans (((List.Perm.swap 61 q2 [q3, q5]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q2, q3, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d4 q2 q3 q5 d2 d3 d5
      hp hp13 hp24 he3 hd4 hd2 hd3 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q1
    subst d1
    subst q5
    have hcomp : ∀ r ∈ ({q2, q3, q4} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 11, q2, q3, q4, 61] [p, 11, 61, q2, q3, q4] :=
      (((((((List.Perm.swap 61 q4 []).cons q3).cons q2).cons 11).cons p).trans ((((List.Perm.swap 61 q3 [q4]).cons q2).cons 11).cons p)).trans (((List.Perm.swap 61 q2 [q3, q4]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q2, q3, q4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d5 q2 q3 q4 d2 d3 d4
      hp hp13 hp24 he3 hd5 hd2 hd3 hd4 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q2
    subst d2
    subst q1
    have hcomp : ∀ r ∈ ({q3, q4, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 61, 11, q3, q4, q5] [p, 11, 61, q3, q4, q5] :=
      ((List.Perm.swap 11 61 [q3, q4, q5]).cons p)
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q3, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d1 q3 q4 q5 d3 d4 d5
      hp hp13 hp24 he3 hd1 hd3 hd4 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · omega
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q2
    subst d2
    subst q3
    have hcomp : ∀ r ∈ ({q1, q4, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, 11, 61, q4, q5] [p, 11, 61, q1, q4, q5] :=
      (((List.Perm.swap 11 q1 [61, q4, q5]).cons p).trans (((List.Perm.swap 61 q1 [q4, q5]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d3 q1 q4 q5 d1 d4 d5
      hp hp13 hp24 he3 hd3 hd1 hd4 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q2
    subst d2
    subst q4
    have hcomp : ∀ r ∈ ({q1, q3, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, 11, q3, 61, q5] [p, 11, 61, q1, q3, q5] :=
      ((((List.Perm.swap 11 q1 [q3, 61, q5]).cons p).trans ((((List.Perm.swap 61 q3 [q5]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q3, q5]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q3, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d4 q1 q3 q5 d1 d3 d5
      hp hp13 hp24 he3 hd4 hd1 hd3 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q2
    subst d2
    subst q5
    have hcomp : ∀ r ∈ ({q1, q3, q4} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, 11, q3, q4, 61] [p, 11, 61, q1, q3, q4] :=
      (((((List.Perm.swap 11 q1 [q3, q4, 61]).cons p).trans (((((List.Perm.swap 61 q4 []).cons q3).cons q1).cons 11).cons p)).trans ((((List.Perm.swap 61 q3 [q4]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q3, q4]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q3, q4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d5 q1 q3 q4 d1 d3 d4
      hp hp13 hp24 he3 hd5 hd1 hd3 hd4 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q3
    subst d3
    subst q1
    have hcomp : ∀ r ∈ ({q2, q4, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 61, q2, 11, q4, q5] [p, 11, 61, q2, q4, q5] :=
      ((((List.Perm.swap 11 q2 [q4, q5]).cons 61).cons p).trans ((List.Perm.swap 11 61 [q2, q4, q5]).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q2, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d1 q2 q4 q5 d2 d4 d5
      hp hp13 hp24 he3 hd1 hd2 hd4 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q3
    subst d3
    subst q2
    have hcomp : ∀ r ∈ ({q1, q4, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, 61, 11, q4, q5] [p, 11, 61, q1, q4, q5] :=
      (((((List.Perm.swap 11 61 [q4, q5]).cons q1).cons p).trans ((List.Perm.swap 11 q1 [61, q4, q5]).cons p)).trans (((List.Perm.swap 61 q1 [q4, q5]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d2 q1 q4 q5 d1 d4 d5
      hp hp13 hp24 he3 hd2 hd1 hd4 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · omega
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q3
    subst d3
    subst q4
    have hcomp : ∀ r ∈ ({q1, q2, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, 11, 61, q5] [p, 11, 61, q1, q2, q5] :=
      ((((((List.Perm.swap 11 q2 [61, q5]).cons q1).cons p).trans ((List.Perm.swap 11 q1 [q2, 61, q5]).cons p)).trans ((((List.Perm.swap 61 q2 [q5]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q2, q5]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d4 q1 q2 q5 d1 d2 d5
      hp hp13 hp24 he3 hd4 hd1 hd2 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q3
    subst d3
    subst q5
    have hcomp : ∀ r ∈ ({q1, q2, q4} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, 11, q4, 61] [p, 11, 61, q1, q2, q4] :=
      (((((((List.Perm.swap 11 q2 [q4, 61]).cons q1).cons p).trans ((List.Perm.swap 11 q1 [q2, q4, 61]).cons p)).trans (((((List.Perm.swap 61 q4 []).cons q2).cons q1).cons 11).cons p)).trans ((((List.Perm.swap 61 q2 [q4]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q2, q4]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d5 q1 q2 q4 d1 d2 d4
      hp hp13 hp24 he3 hd5 hd1 hd2 hd4 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q4
    subst d4
    subst q1
    have hcomp : ∀ r ∈ ({q2, q3, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 61, q2, q3, 11, q5] [p, 11, 61, q2, q3, q5] :=
      ((((((List.Perm.swap 11 q3 [q5]).cons q2).cons 61).cons p).trans (((List.Perm.swap 11 q2 [q3, q5]).cons 61).cons p)).trans ((List.Perm.swap 11 61 [q2, q3, q5]).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q2, q3, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d1 q2 q3 q5 d2 d3 d5
      hp hp13 hp24 he3 hd1 hd2 hd3 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q4
    subst d4
    subst q2
    have hcomp : ∀ r ∈ ({q1, q3, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, 61, q3, 11, q5] [p, 11, 61, q1, q3, q5] :=
      (((((((List.Perm.swap 11 q3 [q5]).cons 61).cons q1).cons p).trans (((List.Perm.swap 11 61 [q3, q5]).cons q1).cons p)).trans ((List.Perm.swap 11 q1 [61, q3, q5]).cons p)).trans (((List.Perm.swap 61 q1 [q3, q5]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q3, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d2 q1 q3 q5 d1 d3 d5
      hp hp13 hp24 he3 hd2 hd1 hd3 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q4
    subst d4
    subst q3
    have hcomp : ∀ r ∈ ({q1, q2, q5} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, 61, 11, q5] [p, 11, 61, q1, q2, q5] :=
      ((((((((List.Perm.swap 11 61 [q5]).cons q2).cons q1).cons p).trans (((List.Perm.swap 11 q2 [61, q5]).cons q1).cons p)).trans ((List.Perm.swap 11 q1 [q2, 61, q5]).cons p)).trans ((((List.Perm.swap 61 q2 [q5]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q2, q5]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d3 q1 q2 q5 d1 d2 d5
      hp hp13 hp24 he3 hd3 hd1 hd2 hd5 hcomp hdist
    convert hid using 1 <;> ring
  · omega
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q4
    subst d4
    subst q5
    have hcomp : ∀ r ∈ ({q1, q2, q3} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, q3, 11, 61] [p, 11, 61, q1, q2, q3] :=
      (((((((((List.Perm.swap 11 q3 [61]).cons q2).cons q1).cons p).trans (((List.Perm.swap 11 q2 [q3, 61]).cons q1).cons p)).trans ((List.Perm.swap 11 q1 [q2, q3, 61]).cons p)).trans (((((List.Perm.swap 61 q3 []).cons q2).cons q1).cons 11).cons p)).trans ((((List.Perm.swap 61 q2 [q3]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q2, q3]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q3] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d5 q1 q2 q3 d1 d2 d3
      hp hp13 hp24 he3 hd5 hd1 hd2 hd3 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q5
    subst d5
    subst q1
    have hcomp : ∀ r ∈ ({q2, q3, q4} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, 61, q2, q3, q4, 11] [p, 11, 61, q2, q3, q4] :=
      ((((((((List.Perm.swap 11 q4 []).cons q3).cons q2).cons 61).cons p).trans ((((List.Perm.swap 11 q3 [q4]).cons q2).cons 61).cons p)).trans (((List.Perm.swap 11 q2 [q3, q4]).cons 61).cons p)).trans ((List.Perm.swap 11 61 [q2, q3, q4]).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q2, q3, q4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d1 q2 q3 q4 d2 d3 d4
      hp hp13 hp24 he3 hd1 hd2 hd3 hd4 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q5
    subst d5
    subst q2
    have hcomp : ∀ r ∈ ({q1, q3, q4} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, 61, q3, q4, 11] [p, 11, 61, q1, q3, q4] :=
      (((((((((List.Perm.swap 11 q4 []).cons q3).cons 61).cons q1).cons p).trans ((((List.Perm.swap 11 q3 [q4]).cons 61).cons q1).cons p)).trans (((List.Perm.swap 11 61 [q3, q4]).cons q1).cons p)).trans ((List.Perm.swap 11 q1 [61, q3, q4]).cons p)).trans (((List.Perm.swap 61 q1 [q3, q4]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q3, q4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d2 q1 q3 q4 d1 d3 d4
      hp hp13 hp24 he3 hd2 hd1 hd3 hd4 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q5
    subst d5
    subst q3
    have hcomp : ∀ r ∈ ({q1, q2, q4} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, 61, q4, 11] [p, 11, 61, q1, q2, q4] :=
      ((((((((((List.Perm.swap 11 q4 []).cons 61).cons q2).cons q1).cons p).trans ((((List.Perm.swap 11 61 [q4]).cons q2).cons q1).cons p)).trans (((List.Perm.swap 11 q2 [61, q4]).cons q1).cons p)).trans ((List.Perm.swap 11 q1 [q2, 61, q4]).cons p)).trans ((((List.Perm.swap 61 q2 [q4]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q2, q4]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d3 q1 q2 q4 d1 d2 d4
      hp hp13 hp24 he3 hd3 hd1 hd2 hd4 hcomp hdist
    convert hid using 1 <;> ring
  · rcases h11 with ⟨hq11, hd11⟩
    rcases h61 with ⟨hq61, _h81⟩
    subst q5
    subst d5
    subst q4
    have hcomp : ∀ r ∈ ({q1, q2, q3} : Finset ℕ),
        r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13 := by
      intro r hr
      apply hcomponents r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, q3, 61, 11] [p, 11, 61, q1, q2, q3] :=
      (((((((((((List.Perm.swap 11 61 []).cons q3).cons q2).cons q1).cons p).trans ((((List.Perm.swap 11 q3 [61]).cons q2).cons q1).cons p)).trans (((List.Perm.swap 11 q2 [q3, 61]).cons q1).cons p)).trans ((List.Perm.swap 11 q1 [q2, q3, 61]).cons p)).trans (((((List.Perm.swap 61 q3 []).cons q2).cons q1).cons 11).cons p)).trans ((((List.Perm.swap 61 q2 [q3]).cons q1).cons 11).cons p)).trans (((List.Perm.swap 61 q1 [q2, q3]).cons 11).cons p))
    have hdist : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q3] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_e3_ordered_false p e d4 q1 q2 q3 d1 d2 d3
      hp hp13 hp24 he3 hd4 hd1 hd2 hd3 hcomp hdist
    convert hid using 1 <;> ring
  · omega
/-- In the same full a=12 branch, positivity and oddness force the odd exponent to be one. -/
theorem a12_odd_exponent_eq_one
    (p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1)
    (he : 0 < e) (heodd : Odd e)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hd4 : 0 < d4) (hd5 : 0 < d5)
    (hcomponents : ∀ q ∈ ({q1, q2, q3, q4, q5} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, q1, q2, q3, q4, q5])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) *
      (q3 ^ (2 * d3) + 1) * (q4 ^ (2 * d4) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * q1 ^ (2 * d1) * q2 ^ (2 * d2) *
        q3 ^ (2 * d3) * q4 ^ (2 * d4) * q5 ^ (2 * d5)) : e = 1 := by
  have he_lt : e < 3 := by
    by_contra hn
    exact a12_e3_false p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5
      hp hp13 hp24 he heodd (by omega) hd1 hd2 hd3 hd4 hd5 hcomponents hdistinct hid
  obtain ⟨k, hk⟩ := heodd
  omega

example : Nat.Prime 73 ∧ 13 < (73 : ℕ) ∧ (73 : ℕ) % 24 = 1 ∧
    0 < (3 : ℕ) ∧ Odd (3 : ℕ) ∧ 3 ≤ (3 : ℕ) ∧
    0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧
    (∀ q ∈ ({11, 61, 17, 19, 23} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13) ∧
    List.Pairwise (· ≠ ·) ([73, 11, 61, 17, 19, 23] : List ℕ) := by decide

end Erdos1052
