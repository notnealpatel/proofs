import Sorry.Erdos.Unitary1052NineOddReduction

set_option autoImplicit false

namespace Erdos1052.NineOdd.WitnessInterval

/-- The identity over actual values transports back to distinct prime bases. -/
theorem base_identity (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ y ∈ P.image (fun p => p ^ e p), (y + 1)) =
      2 ^ (a + 1) * ∏ y ∈ P.image (fun p => p ^ e p), y) :
    (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p) := by
  simpa only [Finset.prod_image (component_injOn P e hp he), Nat.pow_succ,
    mul_assoc, mul_left_comm, mul_comm] using hid

/-- An actual prime value fixes its base and exponent one. -/
theorem actual_prime (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (q : ℕ) (hq : q.Prime) (hm : q ∈ P.image (fun p => p ^ e p)) :
    q ∈ P ∧ e q = 1 := by
  apply (mem_component_prime_power_iff P e hp he q 1 hq (by decide)).mp
  simpa only [pow_one] using hm

/-- Actual membership at an odd prime gives a one-unit successor budget. -/
theorem prime_budget (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hm : q ∈ P.image (fun p => p ^ e p)) :
    padicValNat q (2 ^ a + 1) +
      (∑ y ∈ P.image (fun p => p ^ e p), padicValNat q (y + 1)) = 1 := by
  obtain ⟨hqm, heq⟩ := actual_prime P e hp he q hq hm
  rw [Finset.sum_image (component_injOn P e hp he)]
  simpa only [if_pos hqm, heq] using ordinary_valuation_budget a P e hp hid q hq hq2

/-- A successor divisible by a prime exhausts a one-unit budget and forbids
that prime on every other successor. -/
theorem exhausted (X : Finset ℕ) (q t s : ℕ) (hq : q ≠ 1)
    (hs : s ∈ X) (hd : q ∣ s + 1)
    (hb : t + (∑ y ∈ X, padicValNat q (y + 1)) = 1) :
    ∀ y ∈ X, y ≠ s → ¬ q ∣ y + 1 := by
  have hvs : 1 ≤ padicValNat q (s + 1) := by
    apply (Nat.pow_dvd_iff_le_padicValNat hq (by omega)).mp
    simpa only [pow_one] using hd
  intro y hym hys
  have hsub : ({s, y} : Finset ℕ) ⊆ X := by
    intro z hzm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzm
    rcases hzm with rfl | rfl
    · exact hs
    · exact hym
  have hsum := Finset.sum_le_sum_of_subset hsub (f := fun z => padicValNat q (z + 1))
  have hsy : s ∉ ({y} : Finset ℕ) := by simp [Ne.symm hys]
  rw [Finset.sum_insert hsy, Finset.sum_singleton] at hsum
  have hyv : padicValNat q (y + 1) = 0 := by omega
  rcases padicValNat.eq_zero_iff.mp hyv with hq1 | hy0 | hnd
  · exact (hq hq1).elim
  · omega
  · exact hnd

example :
    let X : Finset ℕ := {11, 7}
    11 ∈ X ∧ 3 ∣ 11 + 1 ∧
      0 + (∑ y ∈ X, padicValNat 3 (y + 1)) = 1 := by
  have hv : padicValNat 3 12 = 1 :=
    valuation_eq_of_pow_dvd 3 12 1 (by decide) (by decide) (by decide) (by decide)
  have hn : padicValNat 3 8 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  norm_num [hv, hn]

/-- All actual values other than three and eleven are one modulo three when
successor twelve spends the entire three-budget. -/
theorem mod_three (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (y : ℕ) (hym : y ∈ P.image (fun p => p ^ e p)) (hy3 : y ≠ 3) (hy11 : y ≠ 11) :
    y % 3 = 1 := by
  have hb := prime_budget a P e hp he hid 3 (by decide) (by decide) h3
  have hns := exhausted _ 3 _ 11 (by decide) h11 (by decide) hb y hym hy11
  obtain ⟨h3b, he3⟩ := actual_prime P e hp he 3 (by decide) h3
  have hnc : ¬ 3 ∣ y := by
    obtain ⟨p, hpm, hpy⟩ := Finset.mem_image.mp hym
    intro hd
    have hdp : 3 ∣ p := (by decide : Nat.Prime 3).dvd_of_dvd_pow (hpy ▸ hd)
    have h3p : 3 = p := (Nat.prime_dvd_prime_iff_eq (by decide) (hp p hpm)).mp hdp
    subst p
    exact hy3 (by simpa only [he3, pow_one] using hpy.symm)
  rw [Nat.dvd_iff_mod_eq_zero] at hns hnc
  omega

/-- The odd prime-power values congruent to one modulo three below 61 form
this short list. The exponent bound is derived only from the value bound. -/
theorem small_prime_power (p k : ℕ) (hp : p.Prime) (ho : Odd p)
    (hk : 0 < k) (hlt : p ^ k < 61) (hm : p ^ k % 3 = 1) :
    p ^ k ∈ ({7, 13, 19, 25, 31, 37, 43, 49} : Finset ℕ) := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    omega
  have hp61 : p < 61 := (Nat.le_pow hk).trans_lt hlt
  have hk4 : k < 4 := by
    by_contra hn
    have h4 : 4 ≤ k := by omega
    have hbound : 3 ^ 4 ≤ p ^ k :=
      (Nat.pow_le_pow_left hp3 4).trans (Nat.pow_le_pow_right (by omega) h4)
    norm_num at hbound
    omega
  have hfinite : ∀ p : Fin 61, ∀ k : Fin 4,
      p.val.Prime → Odd p.val → 0 < k.val → p.val ^ k.val < 61 →
      p.val ^ k.val % 3 = 1 →
      p.val ^ k.val ∈ ({7, 13, 19, 25, 31, 37, 43, 49} : Finset ℕ) := by
    decide
  exact hfinite ⟨p, hp61⟩ ⟨k, hk4⟩ hp ho hk hlt hm

example : Nat.Prime 7 ∧ Odd (7 : ℕ) ∧ 0 < (2 : ℕ) ∧
    7 ^ 2 < (61 : ℕ) ∧ 7 ^ 2 % 3 = (1 : ℕ) := by decide

/-- Each positive finite argument contributes at least one to the ratio. -/
theorem one_le_ratio (y : ℕ) (hy : 0 < y) : 1 ≤ componentRatio y := by
  have hyq : (0 : ℚ) < y := by exact_mod_cast hy
  unfold componentRatio
  apply (le_div_iff₀ hyq).mpr
  linarith

example : 0 < (31 : ℕ) := by decide

/-- Two distinct components at least a threshold leave at most seven values
below it in a nine-component set. -/
theorem count_below_of_two_large (X : Finset ℕ) (hc : X.card = 9)
    (b x y : ℕ) (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hbx : b ≤ x) (hby : b ≤ y) :
    (X.filter (fun z => z < b)).card ≤ 7 := by
  have hym : y ∈ X.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hcx : (X.erase x).card = 8 := by
    rw [Finset.card_erase_of_mem hx, hc]
  have hcxy : ((X.erase x).erase y).card = 7 := by
    rw [Finset.card_erase_of_mem hym, hcx]
  have hsub : X.filter (fun z => z < b) ⊆ (X.erase x).erase y := by
    intro z hzm
    obtain ⟨hz, hzb⟩ := Finset.mem_filter.mp hzm
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hz⟩⟩ <;> omega
  exact (Finset.card_le_card hsub).trans_eq hcxy

example :
    let X : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 373, 32769}
    X.card = 9 ∧ 373 ∈ X ∧ 32769 ∈ X ∧ (373 : ℕ) ≠ 32769 ∧
      373 ≤ (373 : ℕ) ∧ 373 ≤ (32769 : ℕ) := by decide

/-- The saturated budgets and the occupied seven-base component reduce all
actual values below 61 to the fixed six and the two possible residual primes. -/
theorem small_actual_values (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (x : ℕ) (hxm : x ∈ P.image (fun p => p ^ e p))
    (hx : 373 ≤ x) (hd : 11 ∣ x + 1) :
    ∀ y ∈ P.image (fun p => p ^ e p), y < 61 →
      y ∈ ({3, 7, 11, 13, 19, 25, 31, 37} : Finset ℕ) := by
  have hb := prime_budget a P e hp he hid 11 (by decide) (by decide) h11
  have hn43 : 43 ∉ P.image (fun p => p ^ e p) := by
    intro h43
    exact exhausted _ 11 _ x (by decide) hxm hd hb 43 h43 (by omega) (by decide)
  have hn49 : 49 ∉ P.image (fun p => p ^ e p) := by
    intro h49
    obtain ⟨h7b, he7⟩ := actual_prime P e hp he 7 (by decide) h7
    have hm49 : 7 ^ 2 ∈ P.image (fun p => p ^ e p) := h49
    have he72 := ((mem_component_prime_power_iff P e hp he 7 2
      (by decide) (by decide)).mp hm49).2
    omega
  intro y hym hy61
  by_cases hy3 : y = 3
  · simp [hy3]
  by_cases hy11 : y = 11
  · simp [hy11]
  have hm := mod_three a P e hp he hid h3 h11 y hym hy3 hy11
  obtain ⟨p, hpm, hpy⟩ := Finset.mem_image.mp hym
  have hl := small_prime_power p (e p) (hp p hpm) (ho p hpm) (he p hpm)
    (by simpa only [hpy] using hy61) (by simpa only [hpy] using hm)
  rw [hpy] at hl
  have hy43 : y ≠ 43 := by intro hy; exact hn43 (hy ▸ hym)
  have hy49 : y ≠ 49 := by intro hy; exact hn49 (hy ▸ hym)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
  omega

/-- The fixed six components together with either 31 or 37 already have
ratio exceeding two, regardless of any other positive finite components. -/
theorem not_ratio_of_small_residual (a : ℕ) (X : Finset ℕ)
    (hpos : ∀ y ∈ X, 0 < y)
    (hfixed : ({3, 7, 11, 13, 19, 25} : Finset ℕ) ⊆ X)
    (hr : 31 ∈ X ∨ 37 ∈ X) :
    componentRatio (2 ^ a) * (∏ y ∈ X, componentRatio y) ≠ 2 := by
  obtain ⟨r, hrm, hrv⟩ : ∃ r ∈ X, r = 31 ∨ r = 37 := by
    rcases hr with h31 | h37
    · exact ⟨31, h31, Or.inl rfl⟩
    · exact ⟨37, h37, Or.inr rfl⟩
  let S : Finset ℕ := {3, 7, 11, 13, 19, 25, r}
  have hsub : S ⊆ X := by
    intro y hym
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hym
    rcases hym with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfixed (by simp)
    · exact hfixed (by simp)
    · exact hfixed (by simp)
    · exact hfixed (by simp)
    · exact hfixed (by simp)
    · exact hfixed (by simp)
    · exact hrm
  have hprod : (∏ y ∈ S, componentRatio y) ≤ ∏ y ∈ X, componentRatio y := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsub
    · intro y hym
      exact (componentRatio_pos (hpos y (hsub hym))).le
    · intro y hym _
      exact one_le_ratio y (hpos y hym)
  have hgap : 2 < ∏ y ∈ S, componentRatio y := by
    rcases hrv with rfl | rfl <;> norm_num [S, componentRatio]
  have hbinary : 1 ≤ componentRatio (2 ^ a) := one_le_ratio _ (by positivity)
  have hnonneg : 0 ≤ ∏ y ∈ X, componentRatio y :=
    Finset.prod_nonneg (fun y hym => (componentRatio_pos (hpos y hym)).le)
  have hfull := le_mul_of_one_le_left hnonneg hbinary
  exact ne_of_gt (hgap.trans_le (hprod.trans hfull))

example :
    let X : Finset ℕ := {3, 7, 11, 13, 19, 25, 31}
    (∀ y ∈ X, 0 < y) ∧ ({3, 7, 11, 13, 19, 25} : Finset ℕ) ⊆ X ∧
      (31 ∈ X ∨ 37 ∈ X) := by decide

example :
    let P : Finset ℕ := {3, 5}
    let e : ℕ → ℕ := fun _ => 1
    (∀ p ∈ P, p.Prime) ∧ (∀ p ∈ P, Odd p) ∧ (∀ p ∈ P, 0 < e p) ∧
      (2 ^ 2 + 1) * (∏ y ∈ P.image (fun p => p ^ e p), (y + 1)) =
        2 ^ (2 + 1) * ∏ y ∈ P.image (fun p => p ^ e p), y := by decide

/-- Dependency-free interval kernel: with the six actual components
3, 7, 11, 13, 19, 25 explicit, nine distinct odd prime bases, positive exponents,
an even binary exponent at least eleven, the ordinary identity, and a component
exceeding 32768, no actual value in [373,32769) can supply eleven on its successor.
Actual 19 and 25 are assumptions, not conclusions imported from a forcing theorem. -/
theorem interval_kernel (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (hev : Even a)
    (hid : (2 ^ a + 1) * (∏ y ∈ P.image (fun p => p ^ e p), (y + 1)) =
      2 ^ (a + 1) * ∏ y ∈ P.image (fun p => p ^ e p), y)
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (h13 : 13 ∈ P.image (fun p => p ^ e p))
    (h19 : 19 ∈ P.image (fun p => p ^ e p))
    (h25 : 25 ∈ P.image (fun p => p ^ e p))
    (_hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (hlarge : ∃ y ∈ P.image (fun p => p ^ e p), 32768 < y)
    (x : ℕ) (hxm : x ∈ P.image (fun p => p ^ e p))
    (hxlo : 373 ≤ x) (hxhi : x < 32769) (hd : 11 ∣ x + 1) : False := by
  let X := P.image (fun p => p ^ e p)
  have hcX : X.card = 9 := (component_card P e hp he).trans hc
  have hbase := base_identity a P e hp he hid
  have hratio : componentRatio (2 ^ a) * (∏ y ∈ X, componentRatio y) = 2 :=
    actual_component_ratio a P e hp he hbase
  have hpos : ∀ y ∈ X, 0 < y := by
    intro y hym
    obtain ⟨p, hpm, hpy⟩ := Finset.mem_image.mp hym
    rw [← hpy]
    exact pow_pos (hp p hpm).pos _
  have hfixed : ({3, 7, 11, 13, 19, 25} : Finset ℕ) ⊆ X := by
    intro y hym
    simp only [Finset.mem_insert, Finset.mem_singleton] at hym
    rcases hym with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h7
    · exact h11
    · exact h13
    · exact h19
    · exact h25
  by_cases hr : 31 ∈ X ∨ 37 ∈ X
  · exact not_ratio_of_small_residual a X hpos hfixed hr hratio
  have hn31 : 31 ∉ X := fun hm => hr (Or.inl hm)
  have hn37 : 37 ∉ X := fun hm => hr (Or.inr hm)
  have hsmall : ∀ y ∈ X, y < 61 →
      y ∈ ({3, 7, 11, 13, 19, 25} : Finset ℕ) := by
    intro y hym hy61
    have hl := small_actual_values a P e hp ho he hbase h3 h7 h11 x hxm hxlo hd y hym hy61
    have hy31 : y ≠ 31 := by intro hy; exact hn31 (hy ▸ hym)
    have hy37 : y ≠ 37 := by intro hy; exact hn37 (hy ▸ hym)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    omega
  obtain ⟨y, hym, hylarge⟩ := hlarge
  have hxy : x ≠ y := by omega
  have hcount373 : (X.filter (fun z => z < 373)).card ≤ 7 :=
    count_below_of_two_large X hcX 373 x y hxm hym hxy hxlo (by omega)
  have ha12 : 12 ≤ a := by obtain ⟨k, hk⟩ := hev; omega
  let b : Fin 9 → ℕ := ![3, 7, 11, 13, 19, 25, 61, 373, 32769]
  have hb : ∀ i, 0 < b i := by decide
  have hcut : ∀ i : Fin 9, i.val < 7 → b i ≤ 61 := by decide
  have hcounts : ∀ i : Fin 9, i.val < 7 →
      (({3, 7, 11, 13, 19, 25} : Finset ℕ).filter (fun z => z < b i)).card ≤ i.val := by
    decide
  have hdom : ∀ i, b i ≤ X.orderEmbOfFin hcX i := by
    intro i
    by_cases hi : i.val < 7
    · apply sorted_component_lower
      exact (count_lt_le_of_small_list X {3, 7, 11, 13, 19, 25} 61 (b i)
        (hcut i hi) hsmall).trans (hcounts i hi)
    by_cases hi7 : i = 7
    · subst i
      apply sorted_component_lower
      exact hcount373
    · have hi8 : i = 8 := by apply Fin.ext; have hine := Fin.isLt i; omega
      subst i
      exact sorted_last_lower X hcX (by decide) 32769 ⟨y, hym, by omega⟩
  have hgap : componentRatio (2 ^ 12) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_sorted_envelope a X hcX b 12 ha12 hb hdom hgap hratio

end Erdos1052.NineOdd.WitnessInterval
