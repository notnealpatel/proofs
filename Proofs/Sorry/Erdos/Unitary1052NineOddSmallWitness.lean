import Sorry.Erdos.Unitary1052NineOddReduction

set_option autoImplicit false

namespace Erdos1052.NineOdd.SmallWitness

/-- Actual prime membership fixes its own base and exponent one. -/
theorem prime_base (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (q : ℕ) (hq : q.Prime) (hm : q ∈ P.image (fun p => p ^ e p)) :
    q ∈ P ∧ e q = 1 := by
  apply (mem_component_prime_power_iff P e hp he q 1 hq (by omega)).mp
  simpa using hm

/-- Actual3 and11 make all other components one modulo three. -/
theorem mod_three (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hx3 : x ≠ 3) (hx11 : x ≠ 11) :
    x % 3 = 1 := by
  obtain ⟨h3P, he3⟩ := prime_base P e hp he 3 (by decide) h3
  have hbudget := actual_valuation_budget a P e hp he hid h3P
  rw [he3] at hbudget
  have hv11 : padicValNat 3 12 = 1 :=
    valuation_eq_of_pow_dvd 3 12 1 (by decide) (by decide) (by decide) (by decide)
  have hsub : ({11, x} : Finset ℕ) ⊆ P.image (fun p => p ^ e p) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact h11
    · exact hx
  have hsum := Finset.sum_le_sum_of_subset hsub (f := fun y => padicValNat 3 (y + 1))
  have h11x : (11 : ℕ) ≠ x := hx11.symm
  simp only [Finset.sum_insert (by simpa using h11x : (11 : ℕ) ∉ {x}),
    Finset.sum_singleton] at hsum
  rw [show 11 + 1 = (12 : ℕ) from rfl, hv11] at hsum
  have hxval : padicValNat 3 (x + 1) = 0 := by omega
  have hnSucc : ¬ 3 ∣ x + 1 := by simpa using padicValNat.eq_zero_iff.mp hxval
  have hn : ¬ 3 ∣ x := by
    intro hd
    obtain ⟨p, hpm, hpx⟩ := Finset.mem_image.mp hx
    have h3p : 3 ∣ p := (by decide : Nat.Prime 3).dvd_of_dvd_pow (hpx.symm ▸ hd)
    have hp3 : 3 = p := (Nat.prime_dvd_prime_iff_eq (by decide) (hp p hpm)).mp h3p
    subst p
    rw [he3, pow_one] at hpx
    exact hx3 hpx.symm
  rw [Nat.dvd_iff_mod_eq_zero] at hn hnSucc
  omega

/-- The odd prime-power components below55 have this exhaustive list;
the exponent bound is derived only within this interval. -/
theorem odd_prime_power_lt_fifty_five (p k : ℕ) (hp : p.Prime)
    (hp2 : 2 < p) (hk : 0 < k) (hlt : p ^ k < 55) :
    p ^ k ∈ ({3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31, 37, 41, 43, 47, 49, 53} : Finset ℕ) := by
  have hp55 : p < 55 := (Nat.le_pow hk).trans_lt hlt
  have hk4 : k < 4 := by
    by_contra h
    have hbound : 3 ^ 4 ≤ p ^ k :=
      (Nat.pow_le_pow_left (by omega : 3 ≤ p) 4).trans
        (Nat.pow_le_pow_right (by omega) (by omega : 4 ≤ k))
    norm_num at hbound
    omega
  have hfinite : ∀ p : Fin 55, ∀ k : Fin 4,
      p.val.Prime → 2 < p.val → 0 < k.val → p.val ^ k.val < 55 →
      p.val ^ k.val ∈ ({3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31, 37, 41, 43, 47, 49, 53} : Finset ℕ) := by decide
  exact hfinite ⟨p, hp55⟩ ⟨k, hk4⟩ hp hp2 hk hlt

example : (3 : ℕ).Prime ∧ 2 < (3 : ℕ) ∧ 0 < (3 : ℕ) ∧ (3 : ℕ) ^ 3 < 55 := by decide

/-- The actual3/11 branch has only these possible component values below55.
The list safely retains49 before using the actual7 base constraint. -/
theorem small_component_list (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hlt : x < 55) :
    x ∈ ({3, 7, 11, 13, 19, 25, 31, 37, 43, 49} : Finset ℕ) := by
  by_cases hx3 : x = 3
  · subst x; decide
  by_cases hx11 : x = 11
  · subst x; decide
  have hmod := mod_three a P e hp he hid h3 h11 x hx hx3 hx11
  obtain ⟨p, hpm, hpx⟩ := Finset.mem_image.mp hx
  have hlist := odd_prime_power_lt_fifty_five p (e p) (hp p hpm) (hp2 p hpm)
    (he p hpm) (hpx.symm ▸ hlt)
  rw [hpx] at hlist
  have hx5 : x ≠ 5 := fun h => hn5 (h ▸ hx)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlist ⊢
  omega

/-- Two distinct members at or above a threshold leave at most n-2 members
below it, giving the penultimate sorted lower bound. -/
theorem sorted_penultimate_lower (X : Finset ℕ) (hc : X.card = 9)
    (b x y : ℕ) (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hbx : b ≤ x) (hby : b ≤ y) : b ≤ X.orderEmbOfFin hc 7 := by
  apply sorted_component_lower
  have hsub : ({x, y} : Finset ℕ) ⊆ X := by simp [Finset.insert_subset_iff, hx, hy]
  have hcard : (X \ {x, y}).card = 7 := by
    rw [Finset.card_sdiff_of_subset hsub, hc]
    simp [hxy]
  have hfilter : X.filter (fun z => z < b) ⊆ X \ {x, y} := by
    intro z hz
    obtain ⟨hzX, hzb⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_sdiff.mpr
    refine ⟨hzX, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h <;> subst z <;> omega
  have hle := Finset.card_le_card hfilter
  rw [hcard] at hle
  exact hle

example : ({3, 7, 11, 13, 19, 25, 31, 109, 32769} : Finset ℕ).card = 9 ∧
    109 ∈ ({3, 7, 11, 13, 19, 25, 31, 109, 32769} : Finset ℕ) ∧
    32769 ∈ ({3, 7, 11, 13, 19, 25, 31, 109, 32769} : Finset ℕ) ∧
    (109 : ℕ) ≠ 32769 ∧ 109 ≤ (109 : ℕ) ∧ 109 ≤ (32769 : ℕ) := by decide

/-- Under exactly the small-witness branch premises, actual19 is forced.
The upper bound on x ensures the large component occupies a separate slot. -/
theorem actual19_of_small_witness (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (haEven : Even a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (hlarge : ∃ y ∈ P.image (fun p => p ^ e p), 32768 < y)
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (_h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (_h13 : 13 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hxhi : x < 32769) (hx11 : 11 ∣ x + 1) :
    19 ∈ P.image (fun p => p ^ e p) := by
  by_contra hn19
  let X := P.image (fun p => p ^ e p)
  have hcX : X.card = 9 := (component_card P e hp he).trans hc
  have ha12 : 12 ≤ a := by
    have hamod := Nat.even_iff.mp haEven
    omega
  have hsmall : ∀ y ∈ X, y < 38 → y ∈ ({3, 7, 11, 13, 25, 31, 37} : Finset ℕ) := by
    intro y hy hlt
    have hl := small_component_list a P e hp hp2 he hid h3 h11 hn5 y hy (by omega)
    have hy19 : y ≠ 19 := fun h => hn19 (h ▸ hy)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    omega
  let b : Fin 9 → ℕ := ![3, 7, 11, 13, 25, 31, 37, 109, 32769]
  have hb : ∀ i, 0 < b i := by decide
  obtain ⟨L, hLX, hLlarge⟩ := hlarge
  have hdom : ∀ i, b i ≤ X.orderEmbOfFin hcX i := by
    intro i
    by_cases hi : i.val < 7
    · apply sorted_component_lower
      have hb38 : b i ≤ 38 := by fin_cases i <;> simp_all [b]
      have hcount := count_lt_le_of_small_list X {3, 7, 11, 13, 25, 31, 37}
        38 (b i) hb38 hsmall
      have hnum : (({3, 7, 11, 13, 25, 31, 37} : Finset ℕ).filter
          (fun y => y < b i)).card ≤ i.val := by fin_cases i <;> decide
      exact hcount.trans hnum
    · have hiCases : i = 7 ∨ i = 8 := by
        have hival : i.val = 7 ∨ i.val = 8 := by omega
        rcases hival with h | h
        · left; exact Fin.ext h
        · right; exact Fin.ext h
      rcases hiCases with rfl | rfl
      · change 109 ≤ X.orderEmbOfFin hcX 7
        exact sorted_penultimate_lower X hcX 109 x L hx hLX (by omega) hxlo (by omega)
      · change 32769 ≤ X.orderEmbOfFin hcX 8
        exact sorted_last_lower X hcX (by decide) 32769 ⟨L, hLX, by omega⟩
  have hgap : componentRatio (2 ^ 12) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_sorted_envelope a X hcX b 12 ha12 hb hdom hgap
    (actual_component_ratio a P e hp he hid)

/-- Transport the exact ordinary budget to actual components for a present
odd prime. -/
theorem odd_budget (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqm : q ∈ P) :
    padicValNat q (2 ^ a + 1) +
      (∑ y ∈ P.image (fun p => p ^ e p), padicValNat q (y + 1)) = e q := by
  rw [Finset.sum_image (component_injOn P e hp he)]
  simpa only [if_pos hqm] using ordinary_valuation_budget a P e hp hid q hq hq2

/-- An odd modular period prevents every power from having a successor
 divisible by the modulus, provided the modulus is larger than two. -/
theorem odd_period_nonsupplier (q b d k : ℕ) (hq : 2 < q) (hd : Odd d)
    (hperiod : (b : ZMod q) ^ d = 1) : ¬ q ∣ b ^ k + 1 := by
  intro hdiv
  have hz : (b : ZMod q) ^ k + 1 = 0 := by
    have hcast := (ZMod.natCast_eq_zero_iff (b ^ k + 1) q).mpr hdiv
    simpa using hcast
  have hneg : (b : ZMod q) ^ k = -1 := by linear_combination hz
  have hpow : (1 : ZMod q) = -1 := by
    calc
      (1 : ZMod q) = ((b : ZMod q) ^ d) ^ k := by rw [hperiod, one_pow]
      _ = ((b : ZMod q) ^ k) ^ d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = -1 := by rw [hneg, hd.neg_one_pow]
  have htwo : (2 : ZMod q) = 0 := by linear_combination hpow
  have hdiv2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp htwo
  have hle := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) hdiv2
  omega

example : 2 < (11 : ℕ) ∧ Odd (5 : ℕ) ∧ (5 : ZMod 11) ^ 5 = 1 := by decide

/-- A11-supplier at least109 excludes actual43 by the one-unit11 budget. -/
theorem forty_three_absent (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hx11 : 11 ∣ x + 1) : 43 ∉ P.image (fun p => p ^ e p) := by
  obtain ⟨h11P, he11⟩ := prime_base P e hp he 11 (by decide) h11
  have hb := odd_budget a P e hp he hid 11 (by decide) (by decide) h11P
  rw [he11] at hb
  have hxv : 1 ≤ padicValNat 11 (x + 1) :=
    (Nat.pow_dvd_iff_le_padicValNat (by decide) (by omega)).mp (by simpa using hx11)
  intro h43
  have hsub : ({43, x} : Finset ℕ) ⊆ P.image (fun p => p ^ e p) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact h43
    · exact hx
  have hs := Finset.sum_le_sum_of_subset hsub (f := fun y => padicValNat 11 (y + 1))
  have hv44 : padicValNat 11 44 = 1 :=
    valuation_eq_of_pow_dvd 11 44 1 (by decide) (by decide) (by decide) (by decide)
  rw [Finset.sum_insert (by simp; omega : (43 : ℕ) ∉ {x}), Finset.sum_singleton] at hs
  norm_num only [show (43 : ℕ) + 1 = 44 from rfl, hv44] at hs
  omega

/-- Any set of k high components leaves at most9-k low components.
This converts slot allocations into sorted-envelope bounds. -/
theorem sorted_lower_of_high_subset (X F : Finset ℕ) (hc : X.card = 9)
    (hFX : F ⊆ X) (b : ℕ) (hhigh : ∀ y ∈ F, b ≤ y)
    (i : Fin 9) (hcard : 9 - i.val ≤ F.card) : b ≤ X.orderEmbOfFin hc i := by
  apply sorted_component_lower
  have hf : X.filter (fun y => y < b) ⊆ X \ F := by
    intro y hy
    obtain ⟨hyX, hyb⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_sdiff.mpr ⟨hyX, fun hyF => (not_lt_of_ge (hhigh y hyF)) hyb⟩
  have hcount := Finset.card_le_card hf
  rw [Finset.card_sdiff_of_subset hFX, hc] at hcount
  omega

example : ({109, 625, 32769} : Finset ℕ) ⊆ {3, 7, 11, 13, 19, 31, 109, 625, 32769} ∧
    (∀ y ∈ ({109, 625, 32769} : Finset ℕ), 109 ≤ y) ∧
    9 - (6 : Fin 9).val ≤ ({109, 625, 32769} : Finset ℕ).card := by decide

/-- Actual19 forces a base5 component distinct from the11 witness, with an
 even positive exponent at least two. No finite exponent cap is imposed. -/
theorem five_component (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (h19 : 19 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx11 : 11 ∣ x + 1) :
    5 ∈ P ∧ 2 ≤ e 5 ∧ Even (e 5) ∧ 5 ^ e 5 ≠ x := by
  obtain ⟨h19P, he19⟩ := prime_base P e hp he 19 (by decide) h19
  have h5P := successor_prime_mem a P e hp hid 5 (by decide) (by decide) 19 h19P
    (by rw [he19]; norm_num)
  have he5 := he 5 h5P
  have hz : 5 ^ e 5 ∈ P.image (fun p => p ^ e p) := Finset.mem_image.mpr ⟨5, h5P, rfl⟩
  have he5ne : e 5 ≠ 1 := by
    intro h
    apply hn5
    simpa [h] using hz
  have hz3 : 5 ^ e 5 ≠ 3 := by
    intro h
    have hd : 5 ∣ 3 := h ▸ dvd_pow_self 5 (ne_of_gt he5)
    norm_num at hd
  have hz11 : 5 ^ e 5 ≠ 11 := by
    intro h
    have hd : 5 ∣ 11 := h ▸ dvd_pow_self 5 (ne_of_gt he5)
    norm_num at hd
  have hm := mod_three a P e hp he hid h3 h11 _ hz hz3 hz11
  have heven : Even (e 5) := by
    rcases Nat.even_or_odd (e 5) with h | h
    · exact h
    · have hcast : (5 : ZMod 3) = -1 := by decide
      have hzero : (5 : ZMod 3) ^ e 5 + 1 = 0 := by rw [hcast, h.neg_one_pow]; ring
      have hd : 3 ∣ 5 ^ e 5 + 1 := by
        apply (ZMod.natCast_eq_zero_iff (5 ^ e 5 + 1) 3).mp
        simpa using hzero
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      omega
  have hne : 5 ^ e 5 ≠ x := by
    intro h
    apply odd_period_nonsupplier 11 5 5 (e 5) (by decide) (by decide) (by decide)
    simpa [h] using hx11
  exact ⟨h5P, by omega, heven, hne⟩

/-- With the base5 exponent at least four, the actual7 and actual11
constraints reduce every component below55 to these seven values. -/
theorem small_list_of_large_five (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hx11 : 11 ∣ x + 1) (he5 : 4 ≤ e 5) :
    ∀ y ∈ P.image (fun p => p ^ e p), y < 55 →
      y ∈ ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ) := by
  have hn43 := forty_three_absent a P e hp he hid h11 x hx hxlo hx11
  obtain ⟨h7P, he7⟩ := prime_base P e hp he 7 (by decide) h7
  have hn49 : 49 ∉ P.image (fun p => p ^ e p) := by
    intro h
    have hm : 7 ^ 2 ∈ P.image (fun p => p ^ e p) := h
    have hb := (mem_component_prime_power_iff P e hp he 7 2 (by decide) (by decide)).mp hm
    omega
  have hn25 : 25 ∉ P.image (fun p => p ^ e p) := by
    intro h
    have hm : 5 ^ 2 ∈ P.image (fun p => p ^ e p) := h
    have hb := (mem_component_prime_power_iff P e hp he 5 2 (by decide) (by decide)).mp hm
    omega
  intro y hy hy55
  have hl := small_component_list a P e hp hp2 he hid h3 h11 hn5 y hy hy55
  have hy25 : y ≠ 25 := fun h => hn25 (h ▸ hy)
  have hy43 : y ≠ 43 := fun h => hn43 (h ▸ hy)
  have hy49 : y ≠ 49 := fun h => hn49 (h ▸ hy)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
  omega

/-- If the base5 component is at least625, every large component must be
that very component. Three distinct high components give the G2 envelope. -/
theorem sole_large_five (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (haEven : Even a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hxhi : x < 32769) (hx11 : 11 ∣ x + 1)
    (h5P : 5 ∈ P) (he5 : 4 ≤ e 5) :
    ∀ L ∈ P.image (fun p => p ^ e p), 32768 < L → L = 5 ^ e 5 := by
  let X := P.image (fun p => p ^ e p)
  let z := 5 ^ e 5
  have hz : z ∈ X := Finset.mem_image.mpr ⟨5, h5P, rfl⟩
  have hz625 : 625 ≤ z := by
    change 5 ^ 4 ≤ 5 ^ e 5
    exact Nat.pow_le_pow_right (by decide) he5
  have hzx : z ≠ x := by
    intro h
    apply odd_period_nonsupplier 11 5 5 (e 5) (by decide) (by decide) (by decide)
    simpa [← h] using hx11
  have hcX : X.card = 9 := (component_card P e hp he).trans hc
  have ha12 : 12 ≤ a := by have hamod := Nat.even_iff.mp haEven; omega
  have hsmall := small_list_of_large_five a P e hp hp2 he hid h3 h7 h11 hn5 x hx hxlo hx11 he5
  intro L hLX hLlarge
  by_contra hLz
  have hzL : z ≠ L := Ne.symm hLz
  let b : Fin 9 → ℕ := ![3, 7, 11, 13, 19, 31, 109, 625, 32769]
  have hb : ∀ i, 0 < b i := by decide
  have hdom : ∀ i, b i ≤ X.orderEmbOfFin hcX i := by
    intro i
    by_cases hi : i.val < 6
    · apply sorted_component_lower
      have hcut : b i ≤ 55 := by fin_cases i <;> simp_all [b]
      have hcount := count_lt_le_of_small_list X {3, 7, 11, 13, 19, 31, 37}
        55 (b i) hcut hsmall
      have hnum : (({3, 7, 11, 13, 19, 31, 37} : Finset ℕ).filter
          (fun y => y < b i)).card ≤ i.val := by fin_cases i <;> norm_num at hi <;> decide
      exact hcount.trans hnum
    · have hiCases : i = 6 ∨ i = 7 ∨ i = 8 := by
        have hival : i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
        rcases hival with h | h | h
        · left; exact Fin.ext h
        · right; left; exact Fin.ext h
        · right; right; exact Fin.ext h
      rcases hiCases with rfl | rfl | rfl
      · change 109 ≤ X.orderEmbOfFin hcX 6
        apply sorted_lower_of_high_subset X {x, z, L} hcX
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact hx
          · exact hz
          · exact hLX
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl <;> omega
        · simp [hzx.symm, hzL, show x ≠ L by omega]
      · change 625 ≤ X.orderEmbOfFin hcX 7
        exact sorted_penultimate_lower X hcX 625 z L hz hLX hzL hz625 (by omega)
      · change 32769 ≤ X.orderEmbOfFin hcX 8
        exact sorted_last_lower X hcX (by decide) 32769 ⟨L, hLX, by omega⟩
  have hgap : componentRatio (2 ^ 12) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_sorted_envelope a X hcX b 12 ha12 hb hdom hgap
    (actual_component_ratio a P e hp he hid)

/-- Two distinct high actual values and a finite short-value list certify
an envelope without double-allocating the large component. -/
theorem two_high_envelope (a : ℕ) (X L : Finset ℕ) (hc : X.card = 9)
    (ha : 12 ≤ a) (hsmall : ∀ y ∈ X, y < 55 → y ∈ L)
    (x z : ℕ) (hx : x ∈ X) (hz : z ∈ X) (hxlo : 109 ≤ x)
    (hzlo : 32769 ≤ z) (hxz : x ≠ z)
    (b : Fin 9 → ℕ) (hb : ∀ i, 0 < b i)
    (hb7 : b 7 = 109) (hb8 : b 8 = 32769)
    (hcut : ∀ i : Fin 9, i.val < 7 → b i ≤ 55)
    (hcounts : ∀ i : Fin 9, i.val < 7 → (L.filter (fun y => y < b i)).card ≤ i.val)
    (hgap : componentRatio (2 ^ 12) * (∏ i : Fin 9, componentRatio (b i)) < 2) :
    componentRatio (2 ^ a) * (∏ y ∈ X, componentRatio y) ≠ 2 := by
  apply not_perfect_of_sorted_envelope a X hc b 12 ha hb _ hgap
  intro i
  by_cases hi : i.val < 7
  · apply sorted_component_lower
    exact (count_lt_le_of_small_list X L 55 (b i) (hcut i hi) hsmall).trans (hcounts i hi)
  · have hiCases : i = 7 ∨ i = 8 := by
      have hival : i.val = 7 ∨ i.val = 8 := by omega
      rcases hival with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    rcases hiCases with rfl | rfl
    · rw [hb7]
      exact sorted_penultimate_lower X hc 109 x z hx hz hxz hxlo (by omega)
    · rw [hb8]
      exact sorted_last_lower X hc (by decide) 32769 ⟨z, hz, hzlo⟩

/-- If the forced base5 exponent is at least four, the only large component
is its power, its exponent is at least eight, and actual31 and37 are forced.
All three additional conclusions are derived, not public branch premises. -/
theorem terminal_components_of_large_five (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (haEven : Even a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (hlarge : ∃ y ∈ P.image (fun p => p ^ e p), 32768 < y)
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hxhi : x < 32769) (hx11 : 11 ∣ x + 1)
    (h5P : 5 ∈ P) (he5 : 4 ≤ e 5) (he5Even : Even (e 5)) :
    8 ≤ e 5 ∧ 32769 ≤ 5 ^ e 5 ∧
      31 ∈ P.image (fun p => p ^ e p) ∧ 37 ∈ P.image (fun p => p ^ e p) := by
  let X := P.image (fun p => p ^ e p)
  let z := 5 ^ e 5
  have hz : z ∈ X := Finset.mem_image.mpr ⟨5, h5P, rfl⟩
  have hzlo : 32769 ≤ z := by
    obtain ⟨L, hLX, hLlarge⟩ := hlarge
    have hLz := sole_large_five a P e hc hp hp2 he ha haEven hid h3 h7 h11 hn5
      x hx hxlo hxhi hx11 h5P he5 L hLX hLlarge
    omega
  have he8 : 8 ≤ e 5 := by
    by_contra hn
    have hmod := Nat.even_iff.mp he5Even
    have he6 : e 5 ≤ 6 := by omega
    have hpow : z ≤ 5 ^ 6 := Nat.pow_le_pow_right (by decide) he6
    norm_num at hpow
    omega
  have hxz : x ≠ z := by omega
  have hcX : X.card = 9 := (component_card P e hp he).trans hc
  have ha12 : 12 ≤ a := by have hmod := Nat.even_iff.mp haEven; omega
  have hsmall := small_list_of_large_five a P e hp hp2 he hid h3 h7 h11 hn5 x hx hxlo hx11 he5
  have hratio := actual_component_ratio a P e hp he hid
  have h31 : 31 ∈ X := by
    by_contra hn31
    have hs : ∀ y ∈ X, y < 55 → y ∈ ({3, 7, 11, 13, 19, 37} : Finset ℕ) := by
      intro y hy hlt
      have hl := hsmall y hy hlt
      have hy31 : y ≠ 31 := fun h => hn31 (h ▸ hy)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      omega
    let b : Fin 9 → ℕ := ![3, 7, 11, 13, 19, 37, 43, 109, 32769]
    have hcut : ∀ i : Fin 9, i.val < 7 → b i ≤ 55 := by
      intro i hi; fin_cases i <;> simp_all [b]
    have hcounts : ∀ i : Fin 9, i.val < 7 →
        (({3, 7, 11, 13, 19, 37} : Finset ℕ).filter (fun y => y < b i)).card ≤ i.val := by
      intro i hi; fin_cases i <;> first | omega | decide
    have hgap : componentRatio (2 ^ 12) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
      norm_num [b, componentRatio, Fin.prod_univ_succ]
    exact two_high_envelope a X {3, 7, 11, 13, 19, 37} hcX ha12 hs x z hx hz
      hxlo hzlo hxz b (by decide) rfl rfl hcut hcounts hgap hratio
  have h37 : 37 ∈ X := by
    by_contra hn37
    have hs : ∀ y ∈ X, y < 55 → y ∈ ({3, 7, 11, 13, 19, 31} : Finset ℕ) := by
      intro y hy hlt
      have hl := hsmall y hy hlt
      have hy37 : y ≠ 37 := fun h => hn37 (h ▸ hy)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      omega
    let b : Fin 9 → ℕ := ![3, 7, 11, 13, 19, 31, 55, 109, 32769]
    have hcut : ∀ i : Fin 9, i.val < 7 → b i ≤ 55 := by
      intro i hi; fin_cases i <;> simp_all [b]
    have hcounts : ∀ i : Fin 9, i.val < 7 →
        (({3, 7, 11, 13, 19, 31} : Finset ℕ).filter (fun y => y < b i)).card ≤ i.val := by
      intro i hi; fin_cases i <;> first | omega | decide
    have hgap : componentRatio (2 ^ 12) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
      norm_num [b, componentRatio, Fin.prod_univ_succ]
    exact two_high_envelope a X {3, 7, 11, 13, 19, 31} hcX ha12 hs x z hx hz
      hxlo hzlo hxz b (by decide) rfl rfl hcut hcounts hgap hratio
  exact ⟨he8, hzlo, h31, h37⟩

/-- Seven fixed small members and two distinct high members exhaust a
nine-element finset; no further slot or base can be counted. -/
theorem exact_terminal_finset (X : Finset ℕ) (hc : X.card = 9)
    (hcore : ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ) ⊆ X)
    (x z : ℕ) (hx : x ∈ X) (hz : z ∈ X) (hxlo : 109 ≤ x)
    (hzlo : 32769 ≤ z) (hxz : x ≠ z) :
    X = {x, z, 3, 7, 11, 13, 19, 31, 37} := by
  let C : Finset ℕ := {3, 7, 11, 13, 19, 31, 37}
  have hxC : x ∉ C := by simp only [C, Finset.mem_insert, Finset.mem_singleton]; omega
  have hzC : z ∉ C := by simp only [C, Finset.mem_insert, Finset.mem_singleton]; omega
  have hxinsert : x ∉ insert z C := by simp [hxz, hxC]
  have hcard : (insert x (insert z C)).card = 9 := by
    rw [Finset.card_insert_of_notMem hxinsert, Finset.card_insert_of_notMem hzC]
    decide
  have hsub : insert x (insert z C) ⊆ X := by
    exact Finset.insert_subset_iff.mpr ⟨hx, Finset.insert_subset_iff.mpr ⟨hz, hcore⟩⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

example : ({109, 390625, 3, 7, 11, 13, 19, 31, 37} : Finset ℕ).card = 9 ∧
    ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ) ⊆ {109, 390625, 3, 7, 11, 13, 19, 31, 37} ∧
    109 ∈ ({109, 390625, 3, 7, 11, 13, 19, 31, 37} : Finset ℕ) ∧
    390625 ∈ ({109, 390625, 3, 7, 11, 13, 19, 31, 37} : Finset ℕ) ∧
    109 ≤ (109 : ℕ) ∧ 32769 ≤ (390625 : ℕ) ∧ (109 : ℕ) ≠ 390625 := by decide

/-- Under the original small-witness premises, failure of actual25 forces
the exact rejected configuration and an even base5 exponent at least eight.
All slot allocations and auxiliary component memberships are consequences. -/
theorem configuration_of_not_actual25 (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (haEven : Even a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (hlarge : ∃ y ∈ P.image (fun p => p ^ e p), 32768 < y)
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (h13 : 13 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hxhi : x < 32769) (hx11 : 11 ∣ x + 1)
    (hn25 : 25 ∉ P.image (fun p => p ^ e p)) :
    5 ∈ P ∧ Even (e 5) ∧ 8 ≤ e 5 ∧
      P.image (fun p => p ^ e p) = {x, 5 ^ e 5, 3, 7, 11, 13, 19, 31, 37} := by
  have h19 := actual19_of_small_witness a P e hc hp hp2 he ha haEven hid hlarge
    h3 h7 h11 h13 hn5 x hx hxlo hxhi hx11
  obtain ⟨h5P, he5lo, he5Even, hzx⟩ := five_component a P e hp he hid h3 h11 h19 hn5 x hx11
  have he5ne : e 5 ≠ 2 := by
    intro h
    apply hn25
    exact (mem_component_prime_power_iff P e hp he 5 2 (by decide) (by decide)).mpr ⟨h5P, h⟩
  have he5four : 4 ≤ e 5 := by have hmod := Nat.even_iff.mp he5Even; omega
  obtain ⟨he8, hzlo, h31, h37⟩ := terminal_components_of_large_five a P e hc hp hp2 he
    ha haEven hid hlarge h3 h7 h11 hn5 x hx hxlo hxhi hx11 h5P he5four he5Even
  have hcore : ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ) ⊆ P.image (fun p => p ^ e p) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h7
    · exact h11
    · exact h13
    · exact h19
    · exact h31
    · exact h37
  have hz : 5 ^ e 5 ∈ P.image (fun p => p ^ e p) := Finset.mem_image.mpr ⟨5, h5P, rfl⟩
  have hX := exact_terminal_finset (P.image (fun p => p ^ e p))
    ((component_card P e hp he).trans hc) hcore x (5 ^ e 5) hx hz hxlo hzlo hzx.symm
  exact ⟨h5P, he5Even, he8, hX⟩

/-- Odd prime bases give odd actual components, without any exponent cap. -/
theorem component_odd (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) : Odd x := by
  obtain ⟨p, hpm, rfl⟩ := Finset.mem_image.mp hx
  exact ((hp p hpm).odd_of_ne_two (by have h := hp2 p hpm; omega)).pow

example : (∀ p ∈ ({3} : Finset ℕ), p.Prime ∧ 2 < p) ∧
    9 ∈ ({3} : Finset ℕ).image (fun p => p ^ 2) := by norm_num

/-- Applying the two-adic valuation to the full ordinary identity gives
exactly a+1 successor units on the odd actual components. -/
theorem two_budget (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 0 < a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) :
    (∑ y ∈ P.image (fun p => p ^ e p), padicValNat 2 (y + 1)) = a + 1 := by
  have hpow : ∀ p ∈ P, p ^ e p ≠ 0 :=
    fun p hpm => pow_ne_zero _ (hp p hpm).ne_zero
  have hsucc : ∀ p ∈ P, p ^ e p + 1 ≠ 0 := fun p _ => by omega
  have hbinary : padicValNat 2 (2 ^ a + 1) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    have hd : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
    intro hs
    have h1 : 2 ∣ 1 := (Nat.dvd_add_iff_right hd).mpr hs
    norm_num at h1
  have hterms : ∀ p ∈ P, padicValNat 2 (p ^ e p) = 0 := by
    intro p hpm
    have hn : ¬ 2 ∣ p := by
      intro hd
      have hpEq := (Nat.prime_dvd_prime_iff_eq (by decide) (hp p hpm)).mp hd
      have hlt := hp2 p hpm
      omega
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hn, mul_zero]
  have hval := congrArg (padicValNat 2) hid
  rw [padicValNat.mul (p := 2) (a := 2 ^ a + 1) (by positivity)
      (Finset.prod_ne_zero_iff.mpr hsucc),
    padicValNat.mul (p := 2) (a := 2) (by decide)
      (mul_ne_zero (pow_ne_zero a (by decide)) (Finset.prod_ne_zero_iff.mpr hpow)),
    padicValNat.mul (p := 2) (a := 2 ^ a) (pow_ne_zero a (by decide))
      (Finset.prod_ne_zero_iff.mpr hpow),
    valuation_prod 2 P _ hsucc, valuation_prod 2 P _ hpow,
    Finset.sum_congr rfl hterms] at hval
  have hvTwo : padicValNat 2 2 = 1 :=
    valuation_eq_of_pow_dvd 2 2 1 (by decide) (by decide) (by decide) (by decide)
  simp only [hbinary, padicValNat.pow, hvTwo, mul_one,
    Finset.sum_const_zero, add_zero, zero_add] at hval
  rw [Finset.sum_image (component_injOn P e hp he)]
  omega

/-- Distinct terminal components allow expansion of any natural-valued sum
without accidentally deleting a duplicate summand. -/
theorem terminal_sum (f : ℕ → ℕ) (x z : ℕ) (hxlo : 109 ≤ x)
    (hxhi : x < 32769) (hzlo : 32769 ≤ z) :
    (∑ y ∈ ({x, z, 3, 7, 11, 13, 19, 31, 37} : Finset ℕ), f y) =
      f x + f z + (∑ y ∈ ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ), f y) := by
  have hxnot : x ∉ ({z, 3, 7, 11, 13, 19, 31, 37} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hznot : z ∉ ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  rw [Finset.sum_insert hxnot, Finset.sum_insert hznot, ← add_assoc]

example : 109 ≤ (109 : ℕ) ∧ (109 : ℕ) < 32769 ∧ 32769 ≤ (390625 : ℕ) := by decide

/-- The ordinary two-budget hypotheses are jointly realized by the model 6. -/
example : ({3} : Finset ℕ).card = 1 ∧
    (∀ p ∈ ({3} : Finset ℕ), p.Prime ∧ 2 < p ∧ 0 < (fun _ : ℕ => 1) p) ∧
    0 < (1 : ℕ) ∧
    (2 ^ 1 + 1) * (∏ p ∈ ({3} : Finset ℕ), (p ^ 1 + 1)) =
      2 * (2 ^ 1 * ∏ p ∈ ({3} : Finset ℕ), p ^ 1) := by
  norm_num

/-- On the derived even interval 18 through 30, the binary successor
cannot contain a third factor of five. This is not a global exponent cap. -/
theorem binary_five_bound (a : ℕ) (hlo : 18 ≤ a) (hhi : a ≤ 30)
    (heven : Even a) : padicValNat 5 (2 ^ a + 1) ≤ 2 := by
  have hn : ¬ 5 ^ 3 ∣ 2 ^ a + 1 := by
    have hmod := Nat.even_iff.mp heven
    interval_cases a <;> omega
  have hnot : ¬ 3 ≤ padicValNat 5 (2 ^ a + 1) := by
    intro h
    exact hn ((Nat.pow_dvd_iff_le_padicValNat (by decide) (by positivity)).mpr h)
  omega

example : 18 ≤ (18 : ℕ) ∧ (18 : ℕ) ≤ 30 ∧ Even (18 : ℕ) := by decide

/-- The terminal configuration derived when actual25 is absent contradicts
its coupled 31-, two-, and five-adic ordinary budgets. -/
theorem not_terminal_configuration (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (haEven : Even a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hxhi : x < 32769) (hx11 : 11 ∣ x + 1)
    (h5P : 5 ∈ P) (_hE : Even (e 5)) (hE8 : 8 ≤ e 5)
    (hX : P.image (fun p => p ^ e p) = {x, 5 ^ e 5, 3, 7, 11, 13, 19, 31, 37}) :
    False := by
  have hxodd := component_odd P e hp hp2 x hx
  have hxmod := Nat.odd_iff.mp hxodd
  have hnpos : 0 < x + 1 := by omega
  have hnhi : x + 1 ≤ 32768 := by omega
  have hzlo : 32769 ≤ 5 ^ e 5 := by
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (5 : ℕ)) hE8
    norm_num at hpow
    omega
  have h31 : 31 ∈ P.image (fun p => p ^ e p) := by rw [hX]; simp
  obtain ⟨h31P, he31⟩ := prime_base P e hp he 31 (by decide) h31
  have hb31 := odd_budget a P e hp he hid 31 (by decide) (by decide) h31P
  have hv31b : padicValNat 31 (2 ^ a + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd
      (odd_period_nonsupplier 31 2 5 a (by decide) (by decide) (by decide))
  have hv31z : padicValNat 31 (5 ^ e 5 + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd
      (odd_period_nonsupplier 31 5 3 (e 5) (by decide) (by decide) (by decide))
  have hfixed31 : (∑ y ∈ ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ),
      padicValNat 31 (y + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    apply padicValNat.eq_zero_of_not_dvd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  rw [hX, terminal_sum _ x (5 ^ e 5) hxlo hxhi hzlo,
    hv31b, hv31z, hfixed31, he31] at hb31
  have hd31 : 31 ∣ x + 1 := by
    have hd := (Nat.pow_dvd_iff_le_padicValNat (p := 31) (k := 1)
      (by decide) (by omega)).mpr (by omega : 1 ≤ padicValNat 31 (x + 1))
    simpa using hd
  have hn125 : ¬ 5 ^ 3 ∣ x + 1 := by
    intro hd125
    have hd341 : 11 * 31 ∣ x + 1 :=
      (by decide : Nat.Coprime 11 31).mul_dvd_of_dvd_of_dvd hx11 hd31
    have hd : (11 * 31) * 5 ^ 3 ∣ x + 1 :=
      (by decide : Nat.Coprime (11 * 31) (5 ^ 3)).mul_dvd_of_dvd_of_dvd hd341 hd125
    have hle := Nat.le_of_dvd hnpos hd
    norm_num at hle
    exact (not_le_of_gt (by decide : 32768 < (42625 : ℕ))) (hle.trans hnhi)
  have hv5x : padicValNat 5 (x + 1) ≤ 2 := by
    have hnot : ¬ 3 ≤ padicValNat 5 (x + 1) := by
      intro h
      exact hn125 ((Nat.pow_dvd_iff_le_padicValNat (by decide) (by omega)).mpr h)
    omega
  have hv2z : padicValNat 2 (5 ^ e 5 + 1) = 1 := by
    have hzmod : (5 : ZMod 4) ^ e 5 = 1 := by
      rw [show (5 : ZMod 4) = 1 from by decide, one_pow]
    have hn4 : ¬ 4 ∣ 5 ^ e 5 + 1 := by
      intro hd
      have hz := (ZMod.natCast_eq_zero_iff (5 ^ e 5 + 1) 4).mpr hd
      have hz' : (1 : ZMod 4) + 1 = 0 := by simpa [hzmod] using hz
      exact (by decide : (1 : ZMod 4) + 1 ≠ 0) hz'
    have hd2 : 2 ∣ 5 ^ e 5 + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have hm := Nat.odd_iff.mp ((by decide : Odd (5 : ℕ)).pow (n := e 5))
      omega
    exact valuation_eq_of_pow_dvd 2 _ 1 (by decide) (by omega)
      (by simpa using hd2) (by simpa using hn4)
  have hfixed2 : (∑ y ∈ ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ),
      padicValNat 2 (y + 1)) = 16 := by
    have h4 := valuation_eq_of_pow_dvd 2 4 2 (by decide) (by decide) (by decide) (by decide)
    have h8 := valuation_eq_of_pow_dvd 2 8 3 (by decide) (by decide) (by decide) (by decide)
    have h12 := valuation_eq_of_pow_dvd 2 12 2 (by decide) (by decide) (by decide) (by decide)
    have h14 := valuation_eq_of_pow_dvd 2 14 1 (by decide) (by decide) (by decide) (by decide)
    have h20 := valuation_eq_of_pow_dvd 2 20 2 (by decide) (by decide) (by decide) (by decide)
    have h32 := valuation_eq_of_pow_dvd 2 32 5 (by decide) (by decide) (by decide) (by decide)
    have h38 := valuation_eq_of_pow_dvd 2 38 1 (by decide) (by decide) (by decide) (by decide)
    norm_num [Finset.sum_insert, h4, h8, h12, h14, h20, h32, h38]
  have hb2 := two_budget a P e hp hp2 he (by omega) hid
  rw [hX, terminal_sum _ x (5 ^ e 5) hxlo hxhi hzlo, hv2z, hfixed2] at hb2
  let s := padicValNat 2 (x + 1)
  have hslo : 1 ≤ s := by
    apply (Nat.pow_dvd_iff_le_padicValNat (by decide) (by omega)).mp
    change 2 ∣ x + 1
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hshi : s ≤ 15 := by
    have hd : 2 ^ s ∣ x + 1 :=
      (Nat.pow_dvd_iff_le_padicValNat (by decide) (by omega)).mpr (le_refl s)
    have hle : 2 ^ s ≤ 2 ^ 15 := (Nat.le_of_dvd hnpos hd).trans hnhi
    exact (Nat.pow_le_pow_iff_right (by decide)).mp hle
  have haeq : a = 16 + s := by change s + 1 + 16 = a + 1 at hb2; omega
  have hamod := Nat.even_iff.mp haEven
  have halo : 18 ≤ a := by omega
  have hahi : a ≤ 30 := by omega
  have hv5b := binary_five_bound a halo hahi haEven
  have hv5z : padicValNat 5 (5 ^ e 5 + 1) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    have hd : 5 ∣ 5 ^ e 5 := dvd_pow_self 5 (by omega)
    intro hs
    have h1 : 5 ∣ 1 := (Nat.dvd_add_iff_right hd).mpr hs
    norm_num at h1
  have hfixed5 : (∑ y ∈ ({3, 7, 11, 13, 19, 31, 37} : Finset ℕ),
      padicValNat 5 (y + 1)) = 1 := by
    have h4 := valuation_eq_of_pow_dvd 5 4 0 (by decide) (by decide) (by decide) (by decide)
    have h8 := valuation_eq_of_pow_dvd 5 8 0 (by decide) (by decide) (by decide) (by decide)
    have h12 := valuation_eq_of_pow_dvd 5 12 0 (by decide) (by decide) (by decide) (by decide)
    have h14 := valuation_eq_of_pow_dvd 5 14 0 (by decide) (by decide) (by decide) (by decide)
    have h20 := valuation_eq_of_pow_dvd 5 20 1 (by decide) (by decide) (by decide) (by decide)
    have h32 := valuation_eq_of_pow_dvd 5 32 0 (by decide) (by decide) (by decide) (by decide)
    have h38 := valuation_eq_of_pow_dvd 5 38 0 (by decide) (by decide) (by decide) (by decide)
    norm_num [Finset.sum_insert, h4, h8, h12, h14, h20, h32, h38]
  have hb5 := odd_budget a P e hp he hid 5 (by decide) (by decide) h5P
  rw [hX, terminal_sum _ x (5 ^ e 5) hxlo hxhi hzlo, hv5z, hfixed5] at hb5
  omega

/-- For any actual eleven-supplier component in the stated small interval,
the original ordinary nine-odd branch forces actual19 and actual25. -/
theorem actual19_and_actual25_of_small_witness (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (haEven : Even a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (hlarge : ∃ y ∈ P.image (fun p => p ^ e p), 32768 < y)
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (h13 : 13 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 109 ≤ x)
    (hxhi : x < 32769) (hx11 : 11 ∣ x + 1) :
    19 ∈ P.image (fun p => p ^ e p) ∧ 25 ∈ P.image (fun p => p ^ e p) := by
  have h19 := actual19_of_small_witness a P e hc hp hp2 he ha haEven hid hlarge
    h3 h7 h11 h13 hn5 x hx hxlo hxhi hx11
  have h25 : 25 ∈ P.image (fun p => p ^ e p) := by
    by_contra hn25
    obtain ⟨h5P, hE, hE8, hX⟩ := configuration_of_not_actual25 a P e hc hp hp2 he
      ha haEven hid hlarge h3 h7 h11 h13 hn5 x hx hxlo hxhi hx11 hn25
    exact not_terminal_configuration a P e hp hp2 he ha haEven hid
      x hx hxlo hxhi hx11 h5P hE hE8 hX
  exact ⟨h19, h25⟩

end Erdos1052.NineOdd.SmallWitness
