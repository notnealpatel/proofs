import Enumerative.FubiniTwoAdicPeriod

/-!
# Sharp two-adic onset of Fubini periodicity

For positive exponent `m` and positive shift `T`, the actual sequence
`A051293.fubini` repeats modulo `2 ^ m` from `N` exactly when its exact
eventual period divides `T` and `twoAdicOnset m ≤ N`.

Poonen's finite congruence, with `q = 2 ^ m`, has multiplier `-1`.
For an admissible shift, odd-index terms vanish by the imported dyadic LTE
bound, except the top index whose increment is already zero. At indices
`n ≥ m - 2`, all even-index terms except `q - 2` vanish. The remaining
term is `-2 * (-2)^n * (2^T - 1)`: it vanishes for `n ≥ m - 1` and is
nonzero at `n = m - 2` for every positive shift. This argument includes
`m = 2`, `n = 0`, with the usual `0^0 = 1` convention. No infinite series
or cancellation by nonunits in `ZMod` is used.

The period necessity is imported from `Enumerative.FubiniTwoAdicPeriod`.
For the finite identity, see B. Poonen, *Periodicity of a combinatorial
sequence*, Fibonacci Quarterly 26 (1988), 70–76. No novelty claim is made.
-/

set_option autoImplicit false

namespace A000670

/-- The sharp dyadic onset is zero at exponent one and `m - 1` otherwise. -/
def twoAdicOnset (m : ℕ) : ℕ := if m = 1 then 0 else m - 1

example : twoAdicOnset 1 = 0 := rfl
example : twoAdicOnset 2 = 1 := rfl
example : twoAdicOnset 5 = 4 := rfl

/-- At and above the last boundary index, the finite Poonen difference has
only its `q - 2` term left, for every admissible shift. -/
theorem two_onset_survivor (m T n : ℕ) (hm : 2 ≤ m)
    (hT : 2 ^ (max 1 (m - 4)) ∣ T) (hn : m - 2 ≤ n) :
    (A051293.fubini (n + T) : ZMod (2 ^ m)) - A051293.fubini n =
      -2 * (-2 : ZMod (2 ^ m)) ^ n * ((2 : ZMod (2 ^ m)) ^ T - 1) := by
  let q := 2 ^ m
  have hq : 4 ≤ q := by
    exact (show 4 = 2 ^ 2 by decide).le.trans (Nat.pow_le_pow_right (by decide) hm)
  have hzero : (2 : ZMod q) ^ m = 0 := by
    exact (Nat.cast_pow 2 m).symm.trans (ZMod.natCast_self q)
  have hqexp : m ≤ q := Nat.le_of_lt Nat.lt_two_pow_self
  have hfactor : (2 : ZMod q) ^ q - 1 = -1 := by
    rw [pow_eq_zero_of_le hqexp hzero, zero_sub]
  have hA := poonen_congr q (n + T)
  have hB := poonen_congr q n
  rw [hfactor] at hA hB
  have hsum : (A051293.fubini (n + T) : ZMod q) - A051293.fubini n =
      - ∑ j ∈ Finset.range q, (2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ n *
        ((j : ZMod q) ^ T - 1) := by
    have hdiff := congrArg₂ (fun a b : ZMod q => a - b) hA hB
    rw [← Finset.sum_sub_distrib] at hdiff
    have hterms : (∑ j ∈ Finset.range q,
        ((2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ (n + T) -
          (2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ n)) =
        ∑ j ∈ Finset.range q, (2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ n *
          ((j : ZMod q) ^ T - 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    rw [hterms] at hdiff
    linear_combination -hdiff
  rw [hsum]
  have heven : Even T := even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega : max 1 (m - 4) ≠ 0)).trans hT)
  have htop : ((q - 1 : ℕ) : ZMod q) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have htwo : ((q - 2 : ℕ) : ZMod q) = -2 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_ofNat, zero_sub]
  rw [Finset.sum_eq_single (q - 2)]
  · rw [htwo, show q - 1 - (q - 2) = 1 by omega, show (2 : ZMod q) ^ 1 = 2 by ring]
    have hp : (-2 : ZMod q) ^ T = 2 ^ T := heven.neg_pow 2
    rw [hp]
    ring
  · intro j hj hne
    have hjq : j < q := Finset.mem_range.mp hj
    by_cases hd : 2 ∣ j
    · obtain ⟨k, hk⟩ := hd
      have hjnot : j ≠ q - 1 := by
        intro hh
        have hz : (j : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ⟨k, hk⟩
        have hq2 : (q : ZMod 2) = 0 := by
          exact (ZMod.natCast_eq_zero_iff q 2).mpr (dvd_pow_self 2 (by omega))
        rw [hh, Nat.cast_sub (by omega), hq2] at hz
        norm_num at hz
      have hcoeff : 3 ≤ q - 1 - j := by
        have hje : Even j := even_iff_two_dvd.mpr ⟨k, hk⟩
        have hqe : Even q := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
        obtain ⟨a, ha⟩ := hje
        obtain ⟨b, hb⟩ := hqe
        omega
      have hdiv : 2 ^ n ∣ j ^ n := by
        rw [hk, mul_pow]
        exact dvd_mul_right _ _
      obtain ⟨a, ha⟩ := hdiv
      have hjpow : (j : ZMod q) ^ n = 2 ^ n * (a : ZMod q) := by
        have hc := congrArg (fun x : ℕ => (x : ZMod q)) ha
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
      rw [hjpow]
      have hpow : (2 : ZMod q) ^ (q - 1 - j) * 2 ^ n = 0 := by
        rw [← pow_add]
        exact pow_eq_zero_of_le (by omega) hzero
      calc
        _ = ((2 : ZMod q) ^ (q - 1 - j) * 2 ^ n) * (a : ZMod q) *
          ((j : ZMod q) ^ T - 1) := by ring
        _ = 0 := by rw [hpow]; ring
    · by_cases ht : j = q - 1
      · rw [ht, htop, heven.neg_one_pow, sub_self, mul_zero]
      have hcoeff : 2 ≤ q - 1 - j := by
        have hjodd : Odd j := Nat.not_even_iff_odd.mp (fun h => hd h.two_dvd)
        have hqeven : Even q := by
          dsimp [q]
          exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
        obtain ⟨a, ha⟩ := hjodd
        obtain ⟨b, hb⟩ := hqeven
        omega
      obtain ⟨a, ha⟩ := ((two_pow_dvd_odd_increment j (max 1 (m - 4)) hd (by omega)).trans
        (Nat.pow_sub_one_dvd_pow_sub_one j hT))
      have hjpos : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        exact hd (hj0 ▸ dvd_zero 2)
      have hp : 1 ≤ j ^ T := one_le_pow₀ hjpos
      have hjpow : (j : ZMod q) ^ T - 1 = 2 ^ (max 1 (m - 4) + 2) * (a : ZMod q) := by
        have hc := congrArg (fun x : ℕ => (x : ZMod q)) ha
        simpa only [Nat.cast_sub hp, Nat.cast_one, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat] using hc
      rw [hjpow]
      have hpow : (2 : ZMod q) ^ (q - 1 - j) * 2 ^ (max 1 (m - 4) + 2) = 0 := by
        rw [← pow_add]
        exact pow_eq_zero_of_le (by omega) hzero
      calc
        _ = ((2 : ZMod q) ^ (q - 1 - j) * 2 ^ (max 1 (m - 4) + 2)) * (j : ZMod q) ^ n * a := by ring
        _ = 0 := by rw [hpow]; ring
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

/-- The isolated boundary term has valuation exactly `m - 1` for positive shifts. -/
theorem two_boundary_term_ne_zero (m T : ℕ) (hm : 2 ≤ m) (hpos : 0 < T) :
    (-2 : ZMod (2 ^ m)) * (-2 : ZMod (2 ^ m)) ^ (m - 2) *
      ((2 : ZMod (2 ^ m)) ^ T - 1) ≠ 0 := by
  have hp : 1 < 2 ^ T := one_lt_pow₀ (by decide) (by omega)
  have hodd : ¬ 2 ∣ 2 ^ T - 1 := by
    intro hd
    have htwo : 2 ∣ 2 ^ T := dvd_pow_self 2 (by omega)
    have hone : 2 ∣ 1 := (Nat.dvd_sub_iff_right (by omega) htwo).mp hd
    exact (by decide : ¬ 2 ∣ 1) hone
  have hval : padicValNat 2 (2 ^ (m - 1) * (2 ^ T - 1)) = m - 1 := by
    rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hodd, add_zero]
  intro hz
  have hrewrite : (-2 : ZMod (2 ^ m)) * (-2 : ZMod (2 ^ m)) ^ (m - 2) *
      ((2 : ZMod (2 ^ m)) ^ T - 1) =
      (-1 : ZMod (2 ^ m)) ^ (m - 1) *
        ((2 ^ (m - 1) * (2 ^ T - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ 2 ^ T)]
    push_cast
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ, pow_succ, neg_pow]
    ring
  rw [hrewrite] at hz
  have hcast : ((2 ^ (m - 1) * (2 ^ T - 1) : ℕ) : ZMod (2 ^ m)) = 0 :=
    (isUnit_one.neg.pow (m - 1)).mul_right_eq_zero.mp hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hv := (padicValNat_dvd_iff_le (mul_ne_zero (pow_ne_zero _ (by decide)) (by omega) : 2 ^ (m - 1) * (2 ^ T - 1) ≠ 0)).mp hd
  rw [hval] at hv
  omega

/-- Every admissible shift is a period from index `m - 1` onward. -/
theorem two_onset_tail {m T n : ℕ} (hm : 2 ≤ m)
    (hT : 2 ^ (max 1 (m - 4)) ∣ T) (hn : m - 1 ≤ n) :
    A051293.fubini (n + T) ≡ A051293.fubini n [MOD 2 ^ m] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  apply sub_eq_zero.mp
  rw [two_onset_survivor m T n hm hT (by omega)]
  have hzero : (2 : ZMod (2 ^ m)) ^ m = 0 := by
    exact (Nat.cast_pow 2 m).symm.trans (ZMod.natCast_self _)
  have hpow : (-2 : ZMod (2 ^ m)) * (-2 : ZMod (2 ^ m)) ^ n = 0 := by
    rw [← pow_succ', neg_pow, pow_eq_zero_of_le (by omega : m ≤ n + 1) hzero, mul_zero]
  rw [hpow, zero_mul]

/-- At the last index before onset, no positive admissible shift works. -/
theorem two_onset_boundary_not_modEq {m T : ℕ} (hm : 2 ≤ m) (hpos : 0 < T)
    (hT : 2 ^ (max 1 (m - 4)) ∣ T) :
    ¬ A051293.fubini (m - 2 + T) ≡ A051293.fubini (m - 2) [MOD 2 ^ m] := by
  intro heq
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq
  have hdiff := two_onset_survivor m T (m - 2) hm hT (le_refl _)
  rw [hcast, sub_self] at hdiff
  exact two_boundary_term_ne_zero m T hm hpos hdiff.symm

/-- Modulo two, every shift works at every index, including index zero. -/
theorem fubini_add_modEq_two (n T : ℕ) :
    A051293.fubini (n + T) ≡ A051293.fubini n [MOD 2] := by
  induction T with
  | zero => exact Nat.ModEq.refl _
  | succ T ih =>
    exact (fubini_succ_modEq_two (n + T)).trans ih

/-- Whole sharp dyadic onset criterion for the actual Fubini sequence:
for positive exponent and shift, all residues repeat from `N` exactly when
the exact eventual period divides the shift and the sharp onset is at most `N`. -/
theorem fubini_two_power_onset_iff {m T N : ℕ} (hm : 1 ≤ m) (hpos : 0 < T) :
    (∀ n, N ≤ n → A051293.fubini (n + T) ≡ A051293.fubini n [MOD 2 ^ m]) ↔
      (if m ≤ 1 then 1 else 2 ^ (max 1 (m - 4))) ∣ T ∧ twoAdicOnset m ≤ N := by
  constructor
  · intro h
    have hT := (fubini_two_adic_eventual_period_iff m T).mp ⟨N, h⟩
    refine ⟨hT, ?_⟩
    by_cases hm1 : m = 1
    · simp [twoAdicOnset, hm1]
    · have hm2 : 2 ≤ m := by omega
      have hT' : 2 ^ (max 1 (m - 4)) ∣ T := by
        simpa only [if_neg (by omega : ¬ m ≤ 1)] using hT
      by_contra hN
      have hidx : N ≤ m - 2 := by
        simp only [twoAdicOnset, if_neg hm1] at hN
        omega
      exact two_onset_boundary_not_modEq hm2 hpos hT' (h (m - 2) hidx)
  · rintro ⟨hT, hN⟩ n hn
    by_cases hm1 : m = 1
    · subst m
      exact fubini_add_modEq_two n T
    · have hm2 : 2 ≤ m := by omega
      have hT' : 2 ^ (max 1 (m - 4)) ∣ T := by
        simpa only [if_neg (by omega : ¬ m ≤ 1)] using hT
      have honset : m - 1 ≤ N := by
        simpa only [twoAdicOnset, if_neg hm1] using hN
      exact two_onset_tail hm2 hT' (honset.trans hn)

example : 2 ≤ (2 : ℕ) ∧ 0 < (2 : ℕ) ∧
    2 ^ (max 1 (2 - 4)) ∣ (2 : ℕ) ∧ (2 : ℕ) - 2 ≤ 0 := by decide

example : 2 ≤ (5 : ℕ) ∧ 0 < (2 : ℕ) ∧
    2 ^ (max 1 (5 - 4)) ∣ (2 : ℕ) ∧ (5 : ℕ) - 1 ≤ 4 := by decide

example : 1 ≤ (1 : ℕ) ∧ 0 < (1 : ℕ) ∧
    (if (1 : ℕ) ≤ 1 then 1 else 2 ^ (max 1 (1 - 4))) ∣ (1 : ℕ) ∧
    twoAdicOnset 1 ≤ 0 := by decide

example : ∀ n, 0 ≤ n → A051293.fubini (n + 1) ≡ A051293.fubini n [MOD 2 ^ 1] := by
  exact (fubini_two_power_onset_iff (by decide) (by decide)).mpr ⟨by decide, by decide⟩

example : ∀ n, 1 ≤ n → A051293.fubini (n + 2) ≡ A051293.fubini n [MOD 2 ^ 2] := by
  exact (fubini_two_power_onset_iff (by decide) (by decide)).mpr ⟨by decide, by decide⟩

example : ¬ (∀ n, 0 ≤ n → A051293.fubini (n + 2) ≡ A051293.fubini n [MOD 2 ^ 2]) := by
  rw [fubini_two_power_onset_iff (by decide) (by decide)]
  decide

example : ∀ n, 4 ≤ n → A051293.fubini (n + 6) ≡ A051293.fubini n [MOD 2 ^ 5] := by
  exact (fubini_two_power_onset_iff (by decide) (by decide)).mpr ⟨by decide, by decide⟩

example : ¬ (∀ n, 3 ≤ n → A051293.fubini (n + 6) ≡ A051293.fubini n [MOD 2 ^ 5]) := by
  rw [fubini_two_power_onset_iff (by decide) (by decide)]
  decide

example : ∀ n, 5 ≤ n → A051293.fubini (n + 12) ≡ A051293.fubini n [MOD 2 ^ 6] := by
  exact (fubini_two_power_onset_iff (by decide) (by decide)).mpr ⟨by decide, by decide⟩

example : ¬ (∀ n, 4 ≤ n → A051293.fubini (n + 12) ≡ A051293.fubini n [MOD 2 ^ 6]) := by
  rw [fubini_two_power_onset_iff (by decide) (by decide)]
  decide

example : ∀ n, 0 ≤ n → A051293.fubini (n + 0) ≡ A051293.fubini n [MOD 2 ^ 2] := by
  intro n _
  exact Nat.ModEq.refl _

end A000670
