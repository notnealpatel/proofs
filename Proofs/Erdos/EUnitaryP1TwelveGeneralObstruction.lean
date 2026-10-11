import Erdos.EUnitaryP1TwelveObstruction
import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit false
namespace EUnitaryP1

private theorem localA_even_of_prime_ne_two (p b : ℕ) (hp : p.Prime) (h2 : p ≠ 2)
    (hb : 1 < b) : 2 ∣ localA p b := by
  have hz : b ≠ 0 := by omega
  have hm (d : ℕ) (hd : d ∈ exponentDivisors b) : b / d ∈ exponentDivisors b := by
    obtain ⟨hpos, hdiv, hcop⟩ := exponentDivisors_mem hd
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdiv, hz⟩, ?_⟩
    rw [Nat.div_div_self hdiv hz]
    exact hcop.symm
  have hnf (d : ℕ) (hd : d ∈ exponentDivisors b) : b / d ≠ d := by
    obtain ⟨hpos, hdiv, hcop⟩ := exponentDivisors_mem hd
    intro heq
    have hone : d = 1 := (Nat.coprime_self d).mp (by simpa only [heq] using hcop)
    have hmul := Nat.mul_div_cancel' hdiv
    rw [heq, hone] at hmul
    omega
  have hs : (∑ d ∈ exponentDivisors b, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun d _ => b / d)
    · intro d hd; decide
    · intro d hd _; exact hnf d hd
    · exact hm
    · intro d hd; exact Nat.div_div_self (exponentDivisors_mem hd).2.1 hz
  have hcast : (p : ZMod 2) = 1 := by
    have ho := hp.eq_two_or_odd.resolve_left h2
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast, ZMod.val_one] using ho
  apply (ZMod.natCast_eq_zero_iff (localA p b) 2).mp
  simpa only [localA,Nat.cast_sum,Nat.cast_pow,hcast,one_pow] using hs

example : Nat.Prime 229 ∧ 229 ≠ 2 ∧ 1 < (3:ℕ) := by norm_num
example : 2 ∣ localA 229 3 := localA_even_of_prime_ne_two 229 3 (by norm_num) (by decide) (by decide)

private theorem successor_ratio_le_of_card_le_three (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3) (hc : S.card ≤ 3) :
    (∏ q ∈ S, ((q:ℚ)+1)/q) ≤ (576/385:ℚ) := by
  let E : Finset ℕ := {5,7}
  let r : ℚ := 12/11
  let g : ℕ → ℚ := fun q => (((q:ℚ)+1)/q)/r
  have hpos (q : ℕ) (hq : q ∈ S) : 0 < g q := by
    have hh := (hS q hq).1.pos
    dsimp [g,r]; positivity
  have hsmall (q : ℕ) (hq : q ∈ S) (hn : q ∉ E) : g q ≤ 1 := by
    have hp := (hS q hq).1
    have h2 := (hS q hq).2.1
    have h3 := (hS q hq).2.2
    have hk : q ≠ 5 ∧ q ≠ 7 := by simpa [E] using hn
    have hn9 : q ≠ 9 := by rintro rfl; norm_num at hp
    have ho := hp.eq_two_or_odd.resolve_left h2
    have hge : 11 ≤ q := by have hh := hp.two_le; omega
    have hqpos : (0:ℚ) < q := by exact_mod_cast hp.pos
    have hgeq : (11:ℚ) ≤ q := by exact_mod_cast hge
    dsimp [g,r]
    apply (div_le_one (by norm_num : (0:ℚ)<12/11)).mpr
    apply (div_le_iff₀ hqpos).mpr
    linarith
  have hE (q : ℕ) (hq : q ∈ E) : 1 ≤ g q := by
    simp only [E,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> norm_num [g,r]
  have hp1 : (∏ q ∈ S, g q) ≤ ∏ q ∈ S.filter (fun q => q ∈ E), g q := by
    rw [Finset.prod_filter]
    apply Finset.prod_le_prod
    · intro q hq; exact (hpos q hq).le
    · intro q hq
      split_ifs with he
      · exact le_rfl
      · exact hsmall q hq he
  have hp2 : (∏ q ∈ S.filter (fun q => q ∈ E), g q) ≤ ∏ q ∈ E, g q := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro q hq; exact (Finset.mem_filter.mp hq).2
    · intro q hq; exact (hpos q (Finset.mem_filter.mp hq).1).le
    · intro q hq _; exact hE q hq
  have heq : (∏ q ∈ S, ((q:ℚ)+1)/q) = r^S.card*(∏ q ∈ S, g q) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    dsimp [g,r]; ring
  rw [heq]
  calc
    r^S.card*(∏ q ∈ S, g q) ≤ r^S.card*(∏ q ∈ E, g q) :=
      mul_le_mul_of_nonneg_left (hp1.trans hp2) (by dsimp [r]; positivity)
    _ ≤ r^3*(∏ q ∈ E, g q) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num [r]) hc)
      (Finset.prod_nonneg (fun q hq => (hE q hq).trans' (by norm_num)))
    _ = 576/385 := by norm_num [E,g,r]


example : (∀ q ∈ ({5,7,11}:Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3) ∧
    ({5,7,11}:Finset ℕ).card ≤ 3 := by norm_num

/-- At every base, an even exponent at least two makes its successor divide the normalized local factor. -/
theorem dvd_localA_of_even (p c : ℕ) (hc : 2 ≤ c) (he : Even c) : (p+1) ∣ localA p c := by
  have hz : c ≠ 0 := by omega
  have hm (d : ℕ) (hd : d ∈ exponentDivisors c) : c / d ∈ exponentDivisors c := by
    obtain ⟨hpos, hdiv, hcop⟩ := exponentDivisors_mem hd
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdiv, hz⟩, ?_⟩
    rw [Nat.div_div_self hdiv hz]
    exact hcop.symm
  have hnf (d : ℕ) (hd : d ∈ exponentDivisors c) : c / d ≠ d := by
    obtain ⟨hpos, hdiv, hcop⟩ := exponentDivisors_mem hd
    intro heq
    have hone : d = 1 := (Nat.coprime_self d).mp (by simpa only [heq] using hcop)
    have hmul := Nat.mul_div_cancel' hdiv
    rw [heq, hone] at hmul
    omega
  have hpair (d : ℕ) (hd : d ∈ exponentDivisors c) :
      (p : ZMod (p+1))^(d-1) + (p : ZMod (p+1))^(c/d-1) = 0 := by
    obtain ⟨hpos, hdiv, hcop⟩ := exponentDivisors_mem hd
    have hqpos := (exponentDivisors_mem (hm d hd)).1
    have hmul := Nat.mul_div_cancel' hdiv
    have hcm : c % 2 = 0 := Nat.even_iff.mp he
    have hmod : d % 2 * (c/d % 2) % 2 = 0 := by
      rw [← hmul, Nat.mul_mod] at hcm
      exact hcm
    have hnot : ¬ (d % 2 = 0 ∧ c/d % 2 = 0) := by
      intro hh
      have hg := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hh.1) (Nat.dvd_of_mod_eq_zero hh.2)
      rw [hcop.gcd_eq_one] at hg
      norm_num at hg
    have hpar : (Even (d-1) ∧ Odd (c/d-1)) ∨ (Odd (d-1) ∧ Even (c/d-1)) := by
      rw [Nat.even_iff, Nat.odd_iff, Nat.odd_iff, Nat.even_iff]
      rcases Nat.mod_two_eq_zero_or_one d with hd2 | hd2 <;>
        rcases Nat.mod_two_eq_zero_or_one (c/d) with hq2 | hq2 <;>
        simp only [hd2, hq2] at hmod <;> omega
    have hpcast : (p : ZMod (p+1)) = -1 := by
      have hh := ZMod.natCast_self (p+1)
      rw [Nat.cast_add, Nat.cast_one] at hh
      exact eq_neg_of_add_eq_zero_left hh
    rw [hpcast]
    rcases hpar with hh | hh
    · rw [hh.1.neg_one_pow, hh.2.neg_one_pow]; ring
    · rw [hh.1.neg_one_pow, hh.2.neg_one_pow]; ring
  have hs : (∑ d ∈ exponentDivisors c, (p : ZMod (p+1))^(d-1)) = 0 := by
    apply Finset.sum_involution (fun d _ => c / d)
    · exact hpair
    · intro d hd _; exact hnf d hd
    · exact hm
    · intro d hd; exact Nat.div_div_self (exponentDivisors_mem hd).2.1 hz
  apply (ZMod.natCast_eq_zero_iff (localA p c) (p+1)).mp
  simpa only [localA, Nat.cast_sum, Nat.cast_pow, Nat.cast_one] using hs


example : 2 ≤ (6:ℕ) ∧ Even (6:ℕ) := by decide
example : 6 ∣ localA 5 6 := dvd_localA_of_even 5 6 (by decide) (by decide)

private theorem geom_le (p m : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ Finset.range m, p^i) ≤ p^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hpos : 0 ≤ p^m := Nat.zero_le _
    nlinarith

private theorem proper_sum_le (p a k : ℕ) (hp : 2 ≤ p) (ha : 0 < a)
    (hdle : ∀ d ∈ (exponentDivisors a).erase a, d ≤ k) :
    localA p a ≤ p^(a-1) + p^k := by
  let T := (exponentDivisors a).erase a
  have hmem : a ∈ exponentDivisors a := by
    simp [exponentDivisors, Nat.mem_divisors, Nat.ne_of_gt ha, Nat.div_self ha]
  have hdpos (d : ℕ) (hd : d ∈ T) : 0 < d :=
    (exponentDivisors_mem (Finset.mem_erase.mp hd).2).1
  have hinj : Set.InjOn (fun d : ℕ => d-1) T := by
    intro d hd e he hde
    have hp := hdpos d hd
    have hq := hdpos e he
    dsimp only at hde
    omega
  have himage : T.image (fun d => d-1) ⊆ Finset.range k := by
    intro i hi
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (by have hh := hdle d hd; have hpos := hdpos d hd; omega)
  have hsum : (∑ d ∈ T, p^(d-1)) ≤ ∑ i ∈ Finset.range k, p^i := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset himage
  have hsplit : localA p a = (∑ d ∈ T, p^(d-1)) + p^(a-1) :=
    (Finset.sum_erase_add (exponentDivisors a) (fun d => p^(d-1)) hmem).symm
  rw [hsplit]
  have hg := geom_le p k hp
  omega

private theorem proper_quotient_ge_two (a d : ℕ) (ha : 0 < a)
    (hd : d ∈ (exponentDivisors a).erase a) : 2 ≤ a/d := by
  obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hd
  obtain ⟨hpos,hdiv,_⟩ := exponentDivisors_mem hmem
  have hmul := Nat.mul_div_cancel' hdiv
  have hqpos := Nat.div_pos (Nat.le_of_dvd ha hdiv) hpos
  by_contra hn
  have hq : a/d = 1 := by omega
  rw [hq,Nat.mul_one] at hmul
  exact hne hmul

/-- At any base at least two and exponent at least two, the local factor is bounded by the successor times the power two below the exponent. -/
theorem localA_le (p a : ℕ) (hp : 2 ≤ p) (ha : 2 ≤ a) :
    localA p a ≤ (p+1)*p^(a-2) := by
  by_cases he : a = 2
  · subst a; simp [localA_two]
  have ha3 : 3 ≤ a := by omega
  have hbound := proper_sum_le p a (a-2) hp (by omega) (by
    intro d hd
    have hdiv := (exponentDivisors_mem (Finset.mem_erase.mp hd).2).2.1
    have hmul := Nat.mul_div_cancel' hdiv
    have hq := proper_quotient_ge_two a d (by omega) hd
    have hh := (Nat.mul_le_mul_left d hq).trans_eq hmul
    omega)
  have he : a-1 = (a-2)+1 := by omega
  rw [he,pow_succ] at hbound
  nlinarith

example : 2 ≤ (5:ℕ) ∧ 2 ≤ (6:ℕ) := by decide
example : localA 5 6 ≤ 6*5^4 := localA_le 5 6 (by decide) (by decide)

/-- At an odd exponent at least three, the local factor exceeds its leading term by at most the power three below the exponent. -/
theorem localA_le_of_odd (p a : ℕ) (hp : 2 ≤ p) (ha : 3 ≤ a) (ho : Odd a) :
    localA p a ≤ p^(a-1) + p^(a-3) := by
  by_cases he : a = 3
  · subst a
    have hd : exponentDivisors 3 = {1,3} := by decide
    simp [localA,hd,Nat.add_comm]
  have ha5 : 5 ≤ a := by have hh := Nat.odd_iff.mp ho; omega
  apply proper_sum_le p a (a-3) hp (by omega)
  intro d hd
  have hdiv := (exponentDivisors_mem (Finset.mem_erase.mp hd).2).2.1
  have hmul := Nat.mul_div_cancel' hdiv
  have hq2 := proper_quotient_ge_two a d (by omega) hd
  have hq3 : 3 ≤ a/d := by
    have hod := Nat.odd_iff.mp ho
    by_contra hn
    have heq : a/d = 2 := by omega
    have hev : a%2 = 0 := by rw [← hmul,heq,Nat.mul_mod]; simp
    omega
  have hh := (Nat.mul_le_mul_left d hq3).trans_eq hmul
  omega

example : 2 ≤ (5:ℕ) ∧ 3 ≤ (15:ℕ) ∧ Odd (15:ℕ) := by decide
example : localA 5 15 ≤ 5^14+5^12 := localA_le_of_odd 5 15 (by decide) (by decide) (by decide)

private theorem val_eq (n k : ℕ) (hn : n ≠ 0) (hd : 2^k ∣ n)
    (hnd : ¬ 2^(k+1) ∣ n) : padicValNat 2 n = k := by
  have hlo := (padicValNat_dvd_iff_le hn).mp hd
  have hhi : ¬ k+1 ≤ padicValNat 2 n := by
    intro hh; exact hnd ((padicValNat_dvd_iff_le hn).mpr hh)
  omega
private theorem val6 : padicValNat 2 6 = 1 := val_eq 6 1 (by decide) (by decide) (by decide)
private theorem val8 : padicValNat 2 8 = 3 := val_eq 8 3 (by decide) (by decide) (by decide)
private theorem val14 : padicValNat 2 14 = 1 := val_eq 14 1 (by decide) (by decide) (by decide)
private theorem val18 : padicValNat 2 18 = 1 := val_eq 18 1 (by decide) (by decide) (by decide)

private theorem weight_pos (q : ℕ) (hp : q.Prime) (h2 : q ≠ 2) :
    1 ≤ padicValNat 2 (q+1) := by
  have ho := hp.eq_two_or_odd.resolve_left h2
  apply (padicValNat_dvd_iff_le (by omega : q+1 ≠ 0)).mp
  change 2 ∣ q+1
  exact Nat.dvd_of_mod_eq_zero (by omega)


private theorem successor_ratio_power_le (q : ℕ) (hp : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (hn : q ∉ ({5,7,13,17}:Finset ℕ)) :
    ((q:ℚ)+1)/q ≤ (23/22:ℚ)^(padicValNat 2 (q+1)) := by
  let E : Finset ℕ := {5,7,13,17}
  let r : ℚ := 23/22
  let w : ℕ → ℕ := fun q => padicValNat 2 (q+1)
  have hk : q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 ∧ q ≠ 17 := by simpa [E] using hn
  have hw : 1 ≤ w q := weight_pos q hp h2
  have hd : 2^(w q) ∣ q+1 := pow_padicValNat_dvd
  have hnd : ¬ 2^(w q+1) ∣ q+1 := pow_succ_padicValNat_not_dvd (by omega)
  have hqpos : (0:ℚ) < q := by exact_mod_cast hp.pos
  have hratio (L : ℕ) (hL : 0 < L) (hge : L ≤ q) :
      ((q:ℚ)+1)/q ≤ ((L:ℚ)+1)/L := by
    have hLq : (0:ℚ) < L := by exact_mod_cast hL
    have hgeq : (L:ℚ) ≤ q := by exact_mod_cast hge
    apply (div_le_div_iff₀ hqpos hLq).mpr
    nlinarith
  have hbound : ((q:ℚ)+1)/q ≤ r^(w q) := by
    by_cases h1 : w q = 1
    · rw [h1] at hd hnd ⊢
      norm_num only [pow_one, show (2:ℕ)^2 = 4 by decide] at hd hnd
      have hmod := Nat.mod_eq_zero_of_dvd hd
      have hnmod : (q+1)%4 ≠ 0 := by intro hh; exact hnd (Nat.dvd_of_mod_eq_zero hh)
      have hn9 : q ≠ 9 := by rintro rfl; norm_num at hp
      have hn21 : q ≠ 21 := by rintro rfl; norm_num at hp
      have hn25 : q ≠ 25 := by rintro rfl; norm_num at hp
      have hge : 29 ≤ q := by have hh := hp.two_le; omega
      exact (hratio 29 (by decide) hge).trans (by norm_num [r])
    · by_cases h2w : w q = 2
      · rw [h2w] at hd hnd ⊢
        norm_num at hd hnd
        have hmod := Nat.mod_eq_zero_of_dvd hd
        have hnmod : (q+1)%8 ≠ 0 := by intro hh; exact hnd (Nat.dvd_of_mod_eq_zero hh)
        have hge : 11 ≤ q := by omega
        exact (hratio 11 (by decide) hge).trans (by norm_num [r])
      · by_cases h3w : w q = 3
        · rw [h3w] at hd hnd ⊢
          norm_num at hd hnd
          have hmod := Nat.mod_eq_zero_of_dvd hd
          have hnmod : (q+1)%16 ≠ 0 := by intro hh; exact hnd (Nat.dvd_of_mod_eq_zero hh)
          have hge : 23 ≤ q := by omega
          exact (hratio 23 (by decide) hge).trans (by norm_num [r])
        · have hw4 : 4 ≤ w q := by omega
          have hd16 : 16 ∣ q+1 := (Nat.pow_dvd_pow 2 hw4).trans hd
          have hge : 15 ≤ q := by have hh := Nat.le_of_dvd (by omega : 0 < q+1) hd16; omega
          calc
            ((q:ℚ)+1)/q ≤ 16/15 := by have hh := hratio 15 (by decide) hge; norm_num at hh; exact hh
            _ ≤ r^4 := by norm_num [r]
            _ ≤ r^(w q) := pow_le_pow_right₀ (by norm_num [r]) hw4
  exact hbound

private theorem localA_pos (p a : ℕ) (hp : 0 < p) (ha : 0 < a) : 0 < localA p a := by
  have hmem : a ∈ exponentDivisors a := by
    simp [exponentDivisors, Nat.mem_divisors, Nat.ne_of_gt ha, Nat.div_self ha]
  have hh := Finset.single_le_sum (fun d _ => Nat.zero_le (p^(d-1))) hmem
  exact lt_of_lt_of_le (pow_pos hp _) hh

private theorem local_ratio_le (p a : ℕ) (hp : 2 ≤ p) (ha : 2 ≤ a) :
    (localA p a:ℚ)/p^(a-1) ≤ ((p:ℚ)+1)/p := by
  have hpq : (0:ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hh : (localA p a:ℚ) ≤ ((p:ℚ)+1)*p^(a-2) := by exact_mod_cast localA_le p a hp ha
  apply (div_le_div_iff₀ (by positivity) hpq).mpr
  have he : a-1 = (a-2)+1 := by omega
  rw [he,pow_succ]
  nlinarith

private theorem local_ratio_le_of_odd (p a : ℕ) (hp : 2 ≤ p) (ha : 3 ≤ a) (ho : Odd a) :
    (localA p a:ℚ)/p^(a-1) ≤ 1+1/(p:ℚ)^2 := by
  have hpq : (0:ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hh : (localA p a:ℚ) ≤ (p:ℚ)^(a-1)+p^(a-3) := by
    exact_mod_cast localA_le_of_odd p a hp ha ho
  apply (div_le_iff₀ (by positivity)).mpr
  have he : a-1 = (a-3)+2 := by omega
  have hid : (1+1/(p:ℚ)^2)*(p:ℚ)^(a-1) = p^(a-1)+p^(a-3) := by
    rw [he,pow_add,add_mul,one_mul,
      mul_left_comm (1/(p:ℚ)^2) ((p:ℚ)^(a-3)) ((p:ℚ)^2),
      one_div_mul_cancel (by positivity : (p:ℚ)^2 ≠ 0),mul_one]
  rw [hid]
  exact hh

private theorem actual_weight_pos (p a : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (ha : 2 ≤ a) :
    1 ≤ padicValNat 2 (localA p a) := by
  apply (padicValNat_dvd_iff_le (Nat.ne_of_gt (localA_pos p a hp.pos (by omega)))).mp
  exact localA_even_of_prime_ne_two p a hp h2 (by omega)

private theorem successor_weight_le_actual (p a : ℕ) (ha : 2 ≤ a) (he : Even a)
    (hp : 0 < p) : padicValNat 2 (p+1) ≤ padicValNat 2 (localA p a) := by
  apply (padicValNat_dvd_iff_le (Nat.ne_of_gt (localA_pos p a hp (by omega)))).mp
  exact (pow_padicValNat_dvd).trans (dvd_localA_of_even p a ha he)

private theorem local_weighted_bound (q a : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (ha : 2 ≤ a) :
    (localA q a:ℚ)/q^(a-1) ≤ (23/22:ℚ)^(padicValNat 2 (localA q a)) *
      (if Even a ∧ q ∈ ({5,7,13,17}:Finset ℕ) then
        (((q:ℚ)+1)/q)/(23/22:ℚ)^(padicValNat 2 (q+1)) else 1) := by
  have hr : (1:ℚ) ≤ 23/22 := by norm_num
  have hw := actual_weight_pos q a hq h2 ha
  rcases Nat.even_or_odd a with he | ho
  · have hk := successor_weight_le_actual q a ha he hq.pos
    by_cases hE : q ∈ ({5,7,13,17}:Finset ℕ)
    · rw [if_pos ⟨he,hE⟩]
      calc
        (localA q a:ℚ)/q^(a-1) ≤ ((q:ℚ)+1)/q := local_ratio_le q a hq.two_le ha
        _ = (23/22:ℚ)^(padicValNat 2 (q+1))*((((q:ℚ)+1)/q)/(23/22:ℚ)^(padicValNat 2 (q+1))) := by
          rw [mul_comm,div_mul_cancel₀ _ (by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr hk) (by positivity)
    · rw [if_neg (by simp [hE]),mul_one]
      exact (local_ratio_le q a hq.two_le ha).trans
        ((successor_ratio_power_le q hq h2 h3 hE).trans (pow_le_pow_right₀ hr hk))
  · rw [if_neg (by intro hh; exact (Nat.not_even_iff_odd.mpr ho) hh.1),mul_one]
    have hq5 : 5 ≤ q := by have hh := hq.two_le; have hh2 := hq.eq_two_or_odd.resolve_left h2; omega
    have hqq : (5:ℚ) ≤ q := by exact_mod_cast hq5
    have hpq : (0:ℚ) < q := by exact_mod_cast hq.pos
    have hodd : (localA q a:ℚ)/q^(a-1) ≤ 26/25 := by
      have ha3 : 3 ≤ a := by have hh := Nat.odd_iff.mp ho; omega
      apply (local_ratio_le_of_odd q a hq.two_le ha3 ho).trans
      have hh : (1:ℚ)/(q:ℚ)^2 ≤ 1/25 := by
        apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
        nlinarith
      linarith
    exact hodd.trans ((by norm_num : (26/25:ℚ) ≤ 23/22).trans
      (by simpa using pow_le_pow_right₀ hr hw))

private theorem weighted_local_ratio_bound (dropFive : Bool) (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3)
    (he : ∀ q ∈ S, 2 ≤ e q)
    (h5 : dropFive = true → 5 ∈ S → Odd (e 5))
    (hW : (∑ q ∈ S, padicValNat 2 (localA q (e q))) ≤ 10) :
    (∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)) ≤
      (if dropFive then (57927087/35592271:ℚ) else 30222828/16178305) := by
  let E0 : Finset ℕ := {5,7,13,17}
  let E := if dropFive then E0.erase 5 else E0
  let r : ℚ := 23/22
  let C : ℕ → ℚ := fun q => (((q:ℚ)+1)/q)/r^(padicValNat 2 (q+1))
  have hC (q : ℕ) (hq : q ∈ E0) : 1 ≤ C q := by
    simp only [E0,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      norm_num [C,r,val6,val8,val14,val18]
  have hsub : E ⊆ E0 := by
    cases dropFive <;> simp [E,Finset.erase_subset]
  have hlocal (q : ℕ) (hq : q ∈ S) :
      (localA q (e q):ℚ)/q^(e q-1) ≤ r^(padicValNat 2 (localA q (e q))) *
        (if q ∈ E then C q else 1) := by
    apply (local_weighted_bound q (e q) (hS q hq).1 (hS q hq).2.1
      (hS q hq).2.2 (he q hq)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change (if Even (e q) ∧ q ∈ E0 then C q else 1) ≤ (if q ∈ E then C q else 1)
    by_cases hpair : Even (e q) ∧ q ∈ E0
    · have hmem : q ∈ E := by
        cases hom : dropFive
        · simpa only [E,hom,Bool.false_eq_true,if_false] using hpair.2
        · have hne : q ≠ 5 := by
            intro hq5
            subst q
            exact (Nat.not_even_iff_odd.mpr (h5 hom hq)) hpair.1
          simpa only [E,hom,if_true,Finset.mem_erase] using And.intro hne hpair.2
      rw [if_pos hpair,if_pos hmem]
    · rw [if_neg hpair]
      split_ifs with hh
      · exact hC q (hsub hh)
      · exact le_rfl
  have hprod : (∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)) ≤
      r^(∑ q ∈ S, padicValNat 2 (localA q (e q))) *
        (∏ q ∈ S.filter (fun q => q ∈ E), C q) := by
    rw [Finset.prod_filter,← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro q hq; positivity
    · exact hlocal
  have hinsert : (∏ q ∈ S.filter (fun q => q ∈ E), C q) ≤ ∏ q ∈ E, C q := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro q hq; exact (Finset.mem_filter.mp hq).2
    · intro q hq; exact (hC q (hsub (Finset.mem_filter.mp hq).2)).trans' (by norm_num)
    · intro q hq _; exact hC q (hsub hq)
  calc
    (∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)) ≤
        r^(∑ q ∈ S, padicValNat 2 (localA q (e q))) * (∏ q ∈ E, C q) :=
      hprod.trans (mul_le_mul_of_nonneg_left hinsert (by positivity))
    _ ≤ r^10*(∏ q ∈ E, C q) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num [r]) hW)
      (Finset.prod_nonneg (fun q hq => (hC q (hsub hq)).trans' (by norm_num)))
    _ = _ := by cases dropFive <;> norm_num [E,E0,C,r,val6,val8,val14,val18]

/-- Arbitrary active exponents obey the weighted rational envelope using the actual local-factor two-adic costs. -/
theorem weighted_localA_ratio_le (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3)
    (he : ∀ q ∈ S, 2 ≤ e q)
    (hW : (∑ q ∈ S, padicValNat 2 (localA q (e q))) ≤ 10) :
    (∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)) ≤ (30222828/16178305:ℚ) :=
  weighted_local_ratio_bound false S e hS he (by simp) hW

/-- If five is absent or has an odd exponent, its exceptional correction can be omitted from the actual-cost envelope. -/
theorem weighted_localA_ratio_le_of_odd_five (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3)
    (he : ∀ q ∈ S, 2 ≤ e q) (h5 : 5 ∈ S → Odd (e 5))
    (hW : (∑ q ∈ S, padicValNat 2 (localA q (e q))) ≤ 10) :
    (∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)) ≤ (57927087/35592271:ℚ) :=
  weighted_local_ratio_bound true S e hS he (fun _ => h5) hW

example : (∀ q ∈ ({5}:Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3) ∧
    (∀ q ∈ ({5}:Finset ℕ), 2 ≤ (fun _ : ℕ => 2) q) ∧
    (∑ q ∈ ({5}:Finset ℕ), padicValNat 2 (localA q 2)) ≤ 10 := by
  norm_num [localA_two,val6]

private theorem val26 : padicValNat 2 26 = 1 := val_eq 26 1 (by decide) (by decide) (by decide)
example : (∀ q ∈ ({5}:Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3) ∧
    (∀ q ∈ ({5}:Finset ℕ), 2 ≤ (fun _ : ℕ => 3) q) ∧
    (5 ∈ ({5}:Finset ℕ) → Odd ((fun _ : ℕ => 3) 5)) ∧
    (∑ q ∈ ({5}:Finset ℕ), padicValNat 2 (localA q 3)) ≤ 10 := by
  have hA : localA 5 3 = 26 := by decide
  norm_num [hA,val26]; decide

private theorem prime_mem_power_prod (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ q ∈ S, q.Prime) (hd : p ∣ ∏ q ∈ S, q^(e q-1)) : p ∈ S := by
  have hex : p ∣ ∏ q ∈ S, q^(e q-1) ↔ ∃ q ∈ S, p ∣ q^(e q-1) := by
    clear hS hd
    induction S using Finset.induction_on with
    | empty => simp [hp.not_dvd_one]
    | @insert q S hq ih => simp [Finset.prod_insert hq,hp.dvd_mul,ih]
  obtain ⟨q,hq,hdq⟩ := hex.mp hd
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp (hp.dvd_of_dvd_pow hdq)
  simpa only [heq] using hq

private theorem coprime_power_prod (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ p) : Nat.Coprime p (∏ q ∈ S, q^(e q-1)) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (hS p (prime_mem_power_prod p hp S e (fun q hq => (hS q hq).1) hd)).2 rfl

private theorem general_capacity (b c : ℕ) (S : Finset ℕ) (e : ℕ → ℕ)
    (hb : 3 ≤ b) (hc : 2 ≤ c)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229)
    (hid : 2061*localA 3 b*localA 229 c*(∏ q ∈ S, localA q (e q)) =
      2^12*3^(b-1)*229^(c-1)*(∏ q ∈ S, q^(e q-1))) :
    (∑ q ∈ S, padicValNat 2 (localA q (e q))) ≤ 10 ∧
      (b = 6 → (∑ q ∈ S, padicValNat 2 (localA q (e q))) ≤ 3) := by
  let W := ∑ q ∈ S, padicValNat 2 (localA q (e q))
  have hp : 2^W ∣ ∏ q ∈ S, localA q (e q) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun q _ => pow_padicValNat_dvd)
  have hC := localA_even_of_prime_ne_two 229 c (by norm_num) (by decide) (by omega)
  have hco : Nat.Coprime 2 (3^(b-1)*229^(c-1)*(∏ q ∈ S, q^(e q-1))) :=
    (((show Nat.Coprime 2 3 from by decide).pow_right _).mul_right
      ((show Nat.Coprime 2 229 from by decide).pow_right _)).mul_right
      (coprime_power_prod 2 (by decide) S e (fun q hq => ⟨(hS q hq).1,(hS q hq).2.1⟩))
  have hextract (k : ℕ) (hA : 2^k ∣ localA 3 b) : k+1+W ≤ 12 := by
    have hd : 2^(k+1+W) ∣ 2061*localA 3 b*localA 229 c*(∏ q ∈ S, localA q (e q)) := by
      have hh := Nat.mul_dvd_mul (Nat.mul_dvd_mul hA hC) hp
      have hh' := dvd_mul_of_dvd_right hh 2061
      simpa only [pow_add,pow_one,Nat.mul_assoc] using hh'
    rw [hid] at hd
    have hpow : 2^(k+1+W) ∣ 2^12 := (hco.pow_left _).dvd_of_dvd_mul_right
      (by simpa only [Nat.mul_assoc] using hd)
    exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hpow
  constructor
  · have hh := hextract 1 (localA_three_even b (by omega)); dsimp [W] at hh; omega
  · intro he
    have hA : 2^8 ∣ localA 3 b := by rw [he,localA_three_six]; decide
    have hh := hextract 8 hA; dsimp [W] at hh; omega

private theorem odd_five_of_normalized_three (c : ℕ) (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229)
    (he : ∀ q ∈ S, 2 ≤ e q)
    (hid : 2061*localA 3 3*localA 229 c*(∏ q ∈ S, localA q (e q)) =
      2^12*3^(3-1)*229^(c-1)*(∏ q ∈ S, q^(e q-1))) : Odd (e 5) := by
  have hA : localA 3 3 = 10 := by decide
  have h5L : 5 ∣ 2061*localA 3 3*localA 229 c*(∏ q ∈ S, localA q (e q)) := by
    rw [hA]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by decide) _) _) _
  have hco5 : Nat.Coprime 5 (2^12*3^(3-1)*229^(c-1)) :=
    (((show Nat.Coprime 5 2 from by decide).pow_right _).mul_right
      ((show Nat.Coprime 5 3 from by decide).pow_right _)).mul_right
      ((show Nat.Coprime 5 229 from by decide).pow_right _)
  have hm : 5 ∈ S := prime_mem_power_prod 5 (by decide) S e (fun q hq => (hS q hq).1)
    (hco5.dvd_of_dvd_mul_left (by rw [← hid]; exact h5L))
  rcases Nat.even_or_odd (e 5) with hev | hod
  · have hP : 3 ∣ ∏ q ∈ S, localA q (e q) :=
      (by decide : 3 ∣ 6).trans ((dvd_localA_of_even 5 (e 5) (he 5 hm) hev).trans
        (Finset.dvd_prod_of_mem (fun q => localA q (e q)) hm))
    have hd : 3^3 ∣ 2061*localA 3 3*localA 229 c*(∏ q ∈ S, localA q (e q)) :=
      Nat.mul_dvd_mul (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (by decide : 9 ∣ 2061) (localA 3 3)) (localA 229 c)) hP
    rw [hid] at hd
    have hco3 : Nat.Coprime 3 (2^12*229^(c-1)*(∏ q ∈ S, q^(e q-1))) :=
      (((show Nat.Coprime 3 2 from by decide).pow_right _).mul_right
        ((show Nat.Coprime 3 229 from by decide).pow_right _)).mul_right
        (coprime_power_prod 3 (by decide) S e (fun q hq => ⟨(hS q hq).1,(hS q hq).2.2.1⟩))
    have hpow : 3^3 ∣ 3^(3-1) := (hco3.pow_left 3).dvd_of_dvd_mul_right
      (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hd)
    norm_num at hpow
  · exact hod

private theorem three_bound (b : ℕ) (hb : 4 ≤ b) (h6 : b ≠ 6) :
    (localA 3 b : ℚ) ≤ (28/27:ℚ)*3^(b-1) := by
  by_cases h4 : b = 4
  · subst b
    have hA : localA 3 4 = 28 := by decide
    norm_num [hA]
  · by_cases h5 : b = 5
    · subst b; norm_num [localA_three_five]
    · have h7 : 7 ≤ b := by omega
      have ht : (54:ℚ)*localA 3 b < 55*3^(b-1) := by
        exact_mod_cast localA_three_tail_lt b h7
      have hpos : (0:ℚ) < 3^(b-1) := by positivity
      nlinarith

private theorem general_ratio_contradiction (b c : ℕ) (S : Finset ℕ) (e : ℕ → ℕ)
    (_hb : 0 < b) (hc : 2 ≤ c) (hS : ∀ q ∈ S, q.Prime)
    (hid : 2061*localA 3 b*localA 229 c*(∏ q ∈ S, localA q (e q)) =
      2^12*3^(b-1)*229^(c-1)*(∏ q ∈ S, q^(e q-1)))
    (K M : ℚ) (hK : 0 ≤ K) (_hM : 0 ≤ M)
    (hA : (localA 3 b:ℚ) ≤ K*3^(b-1))
    (hR : (∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)) ≤ M)
    (hgap : 2061*K*(230/229)*M < (4096:ℚ)) : False := by
  let X : ℚ := 3^(b-1)*229^(c-1)
  let R : ℚ := ∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)
  have hX : 0 < X := by dsimp [X]; positivity
  have hR0 : 0 ≤ R := by
    apply Finset.prod_nonneg
    intro q hq
    have hp := (hS q hq).pos
    positivity
  have hB : (0:ℚ) < ∏ q ∈ S, (q:ℚ)^(e q-1) := by
    apply Finset.prod_pos
    intro q hq; have hp : (0:ℚ) < q := by exact_mod_cast (hS q hq).pos
    positivity
  have hReq : R = (∏ q ∈ S, (localA q (e q):ℚ))/(∏ q ∈ S, (q:ℚ)^(e q-1)) :=
    Finset.prod_div_distrib _ _
  have hscale : (2061:ℚ)*localA 3 b*localA 229 c*R = 4096*X := by
    rw [hReq, ← mul_div_assoc, div_eq_iff hB.ne']
    dsimp [X]
    have hh := congrArg (fun n : ℕ => (n:ℚ)) hid
    push_cast at hh
    simpa only [mul_assoc] using hh
  have hC : (localA 229 c:ℚ) ≤ (230/229:ℚ)*229^(c-1) := by
    have hh : (localA 229 c:ℚ) ≤ 230*229^(c-2) := by exact_mod_cast localA_le 229 c (by decide) hc
    have he : c-1 = (c-2)+1 := by omega
    rw [he,pow_succ]
    nlinarith
  have hAC : (localA 3 b:ℚ)*localA 229 c ≤ K*(230/229)*X := by
    calc
      (localA 3 b:ℚ)*localA 229 c ≤ (K*3^(b-1))*((230/229)*229^(c-1)) :=
        mul_le_mul hA hC (by positivity) (mul_nonneg hK (by positivity))
      _ = K*(230/229)*X := by dsimp [X]; ring
  have hu : ((localA 3 b:ℚ)*localA 229 c)*R ≤ (K*(230/229)*X)*M :=
    mul_le_mul hAC hR hR0 (by positivity)
  have hstrict := mul_lt_mul_of_pos_right hgap hX
  nlinarith


/-- The exponent-twelve normalized perfectness identity is impossible for arbitrary other active prime exponents, with no capacity or parity premise. -/
theorem normalized_general_229_ne (b c : ℕ) (S : Finset ℕ) (e : ℕ → ℕ)
    (hb : 3 ≤ b) (hc : 2 ≤ c)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229)
    (he : ∀ q ∈ S, 2 ≤ e q) :
    2061*localA 3 b*localA 229 c*(∏ q ∈ S, localA q (e q)) ≠
      2^12*3^(b-1)*229^(c-1)*(∏ q ∈ S, q^(e q-1)) := by
  intro hid
  have hcap := general_capacity b c S e hb hc hS hid
  have hS23 : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 :=
    fun q hq => ⟨(hS q hq).1,(hS q hq).2.1,(hS q hq).2.2.1⟩
  by_cases h3 : b = 3
  · subst b
    have h5 := odd_five_of_normalized_three c S e hS he hid
    have hA : (localA 3 3:ℚ) ≤ (10/9:ℚ)*3^(3-1) := by
      have hh : localA 3 3 = 10 := by decide
      norm_num [hh]
    exact general_ratio_contradiction 3 c S e (by decide) hc (fun q hq => (hS q hq).1) hid
      (10/9) (57927087/35592271) (by norm_num) (by norm_num) hA
      (weighted_localA_ratio_le_of_odd_five S e hS23 he (fun _ => h5) hcap.1) (by norm_num)
  · by_cases h6 : b = 6
    · have hcard : S.card ≤ 3 := by
        have hh : S.card ≤ ∑ q ∈ S, padicValNat 2 (localA q (e q)) := by
          simpa using Finset.sum_le_sum
            (fun q hq => actual_weight_pos q (e q) (hS q hq).1 (hS q hq).2.1 (he q hq))
        exact hh.trans (hcap.2 h6)
      have hA : (localA 3 b:ℚ) ≤ (256/243:ℚ)*3^(b-1) := by
        rw [h6]; norm_num [localA_three_six]
      have hR : (∏ q ∈ S, (localA q (e q):ℚ)/q^(e q-1)) ≤ (576/385:ℚ) := by
        apply le_trans _ (successor_ratio_le_of_card_le_three S hS23 hcard)
        apply Finset.prod_le_prod
        · intro q hq; positivity
        · intro q hq; exact local_ratio_le q (e q) (hS q hq).1.two_le (he q hq)
      exact general_ratio_contradiction b c S e (by omega) hc (fun q hq => (hS q hq).1) hid
        (256/243) (576/385) (by norm_num) (by norm_num) hA hR (by norm_num)
    · exact general_ratio_contradiction b c S e (by omega) hc (fun q hq => (hS q hq).1) hid
        (28/27) (30222828/16178305) (by norm_num) (by norm_num)
        (three_bound b (by omega) h6) (weighted_localA_ratio_le S e hS23 he hcap.1) (by norm_num)

example : 3 ≤ (3:ℕ) ∧ 2 ≤ (3:ℕ) ∧
    (∀ q ∈ ({5}:Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229) ∧
    (∀ q ∈ ({5}:Finset ℕ), 2 ≤ (fun _ : ℕ => 15) q) := by norm_num
example : 2061*localA 3 3*localA 229 3*(∏ q ∈ ({5}:Finset ℕ), localA q 15) ≠
    2^12*3^(3-1)*229^(3-1)*(∏ q ∈ ({5}:Finset ℕ), q^(15-1)) :=
  normalized_general_229_ne 3 3 {5} (fun _ => 15) (by decide) (by decide)
    (by norm_num) (by norm_num)

private theorem actual_normalized_identity (n : ℕ) (hn : 0 < n)
    (hid : sigmaEU n = 2*n) :
    (∏ p ∈ n.primeFactors.filter (fun p => 2 ≤ n.factorization p), localA p (n.factorization p)) =
      2*(∏ p ∈ n.primeFactors.filter (fun p => 2 ≤ n.factorization p), p^(n.factorization p-1)) := by
  let F := n.primeFactors
  let T := F.filter (fun p => 2 ≤ n.factorization p)
  let P := ∏ p ∈ F, p
  let A := ∏ p ∈ F, localA p (n.factorization p)
  let D := ∏ p ∈ F, p^(n.factorization p-1)
  have hpos (p : ℕ) (hp : p ∈ F) : 0 < n.factorization p := by
    have hm := Nat.mem_primeFactors.mp hp
    have hne : n.factorization p ≠ 0 := by
      intro hz
      rcases (Nat.factorization_eq_zero_iff n p).mp hz with hh | hh | hh
      · exact hh hm.1
      · exact hh hm.2.1
      · exact (Nat.ne_of_gt hn) hh
    omega
  have hP : 0 < P := Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
  have hnprod : n = P*D := by
    rw [Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hn)]
    dsimp [P,D,F]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [← pow_succ',Nat.sub_add_cancel (hpos p hp)]
  have hsigma : sigmaEU n = P*A := by
    rw [sigmaEU,if_neg (Nat.ne_of_gt hn)]
    simp_rw [local_sum_eq]
    exact Finset.prod_mul_distrib
  have hfull : A = 2*D := Nat.mul_left_cancel hP (by
    rw [← hsigma,hid,hnprod]; ring)
  have hAF : (∏ p ∈ T, localA p (n.factorization p)) = A := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have heq : n.factorization p = 1 := by
      have hh : ¬ 2 ≤ n.factorization p := by
        intro hh; exact hnot (Finset.mem_filter.mpr ⟨hp,hh⟩)
      have hhpos := hpos p hp
      omega
    rw [heq,localA_one]
  have hDF : (∏ p ∈ T, p^(n.factorization p-1)) = D := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have heq : n.factorization p = 1 := by
      have hh : ¬ 2 ≤ n.factorization p := by
        intro hh; exact hnot (Finset.mem_filter.mpr ⟨hp,hh⟩)
      have hhpos := hpos p hp
      omega
    simp [heq]
  change (∏ p ∈ T, localA p (n.factorization p)) = 2*(∏ p ∈ T, p^(n.factorization p-1))
  rw [hAF,hDF]
  exact hfull

private theorem normalized_active_ne (U : Finset ℕ) (e : ℕ → ℕ)
    (hU : ∀ q ∈ U, q.Prime ∧ q ≠ 2) (he : ∀ q ∈ U, 2 ≤ e q) :
    2061*(∏ q ∈ U, localA q (e q)) ≠ 4096*(∏ q ∈ U, q^(e q-1)) := by
  intro hid
  have hforce (p : ℕ) (hp : p.Prime) (hd : p ∣ 2061) (hco : Nat.Coprime p 4096) : p ∈ U :=
    prime_mem_power_prod p hp U e (fun q hq => (hU q hq).1)
      (hco.dvd_of_dvd_mul_left (by rw [← hid]; exact dvd_mul_of_dvd_left hd _))
  have h3 : 3 ∈ U := hforce 3 (by decide) (by decide) (by decide)
  have h229 : 229 ∈ U := hforce 229 (by norm_num) (by norm_num) (by
    change Nat.Coprime 229 (2^12)
    exact (show Nat.Coprime 229 2 from by decide).pow_right 12)
  have h229' : 229 ∈ U.erase 3 := Finset.mem_erase.mpr ⟨by decide,h229⟩
  let S := (U.erase 3).erase 229
  have hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229 := by
    intro q hq
    have hh := Finset.mem_erase.mp hq
    have hh' := Finset.mem_erase.mp hh.2
    exact ⟨(hU q hh'.2).1,(hU q hh'.2).2,hh'.1,hh.1⟩
  have heS : ∀ q ∈ S, 2 ≤ e q := by
    intro q hq
    exact he q (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq))
  have hb : 2 ≤ e 3 := he 3 h3
  have hc : 2 ≤ e 229 := he 229 h229
  rw [← Finset.mul_prod_erase U (fun q => localA q (e q)) h3,
    ← Finset.mul_prod_erase U (fun q => q^(e q-1)) h3,
    ← Finset.mul_prod_erase (U.erase 3) (fun q => localA q (e q)) h229',
    ← Finset.mul_prod_erase (U.erase 3) (fun q => q^(e q-1)) h229'] at hid
  have hid' : 2061*localA 3 (e 3)*localA 229 (e 229)*(∏ q ∈ S, localA q (e q)) =
      2^12*3^(e 3-1)*229^(e 229-1)*(∏ q ∈ S, q^(e q-1)) := by
    simpa only [Nat.mul_assoc,Nat.reducePow,S] using hid
  have hb3 : 3 ≤ e 3 := by
    have hd : 3^2 ∣ 2061*localA 3 (e 3)*localA 229 (e 229)*(∏ q ∈ S, localA q (e q)) :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide) _) _) _
    rw [hid'] at hd
    have hco : Nat.Coprime 3 (2^12*229^(e 229-1)*(∏ q ∈ S, q^(e q-1))) :=
      (((show Nat.Coprime 3 2 from by decide).pow_right _).mul_right
        ((show Nat.Coprime 3 229 from by decide).pow_right _)).mul_right
        (coprime_power_prod 3 (by decide) S e (fun q hq => ⟨(hS q hq).1,(hS q hq).2.2.1⟩))
    have hpow : 3^2 ∣ 3^(e 3-1) := (hco.pow_left 2).dvd_of_dvd_mul_right
      (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hd)
    have hh := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 3)).mp hpow
    omega
  exact normalized_general_229_ne (e 3) (e 229) S e hb3 hc hS heS hid'

/-- No positive integer whose actual two-adic factorization exponent is twelve is exponential-unitary perfect; all other prime exponents, including one, are unrestricted. -/
theorem sigmaEU_twelve_ne (n : ℕ) (hn : 0 < n) (ha : n.factorization 2 = 12) :
    sigmaEU n ≠ 2*n := by
  intro hperfect
  let T := n.primeFactors.filter (fun p => 2 ≤ n.factorization p)
  have h2dvd : 2 ∣ n := by
    by_contra hd
    have hz : n.factorization 2 = 0 := (Nat.factorization_eq_zero_iff n 2).mpr (Or.inr (Or.inl hd))
    omega
  have h2 : 2 ∈ T := Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨by decide,h2dvd,Nat.ne_of_gt hn⟩,by omega⟩
  have hid : (∏ p ∈ T, localA p (n.factorization p)) =
      2*(∏ p ∈ T, p^(n.factorization p-1)) := actual_normalized_identity n hn hperfect
  rw [← Finset.mul_prod_erase T (fun p => localA p (n.factorization p)) h2,
    ← Finset.mul_prod_erase T (fun p => p^(n.factorization p-1)) h2,ha,localA_two_twelve] at hid
  have hraw : 2061*(∏ p ∈ T.erase 2, localA p (n.factorization p)) =
      4096*(∏ p ∈ T.erase 2, p^(n.factorization p-1)) := by
    simpa only [Nat.reduceSub,Nat.reducePow,← Nat.mul_assoc,Nat.reduceMul] using hid
  apply normalized_active_ne (T.erase 2) n.factorization _ _ hraw
  · intro p hp
    have hh := Finset.mem_erase.mp hp
    have hmem := Finset.mem_filter.mp hh.2
    exact ⟨(Nat.mem_primeFactors.mp hmem.1).1,hh.1⟩
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
example : 0 < (2:ℕ)^12 ∧ ((2:ℕ)^12).factorization 2 = 12 := by
  constructor
  · positivity
  · simp only [Nat.factorization_pow, Nat.Prime.factorization (by decide : Nat.Prime 2),
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

example : sigmaEU ((2:ℕ)^12) ≠ 2*((2:ℕ)^12) :=
  sigmaEU_twelve_ne _ (by positivity)
    (by simp only [Nat.factorization_pow, Nat.Prime.factorization (by decide : Nat.Prime 2),
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one])

end EUnitaryP1
