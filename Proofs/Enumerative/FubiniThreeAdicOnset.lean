import Enumerative.FubiniPrimePowerPeriod

/-!
# Sharp three-adic onset of Fubini periodicity

For `1 ≤ m` and positive shifts `T`, the actual sequence `A051293.fubini`
repeats modulo `3 ^ m` at every index at least `N` exactly when
`2 * 3 ^ (m - 1)` divides `T` and `threeAdicOnset m ≤ N`.
The onset is one for `m = 1`, and `2 * (m / 2)` otherwise.

The proof uses Poonen's finite congruence and the exact eventual-period
criterion imported above. The unit-index terms are periodic even at index
zero. After factoring `3 ^ n` from the nonunit-index terms, their coefficient
modulo three is evaluated in six-term blocks. Only one extra boundary index,
`n = m - 1` for odd `m`, is needed beyond direct prime-power vanishing.
All cancellation involving powers of three is done in natural divisibility,
not in a ring with zero divisors. No infinite-series identity is used.

For the imported finite formula and eventual period theorem, see B. Poonen,
*Periodicity of a combinatorial sequence*, Fibonacci Quarterly 26 (1988),
70–76. No novelty or attribution claim is made for the sharp onset formula.
-/

set_option autoImplicit false
open Finset

namespace A000670
open A051293

/-- The sharp onset for the actual Fubini sequence modulo `3 ^ m`, for
positive `m`; the value at zero is defined by the same piecewise formula. -/
def threeAdicOnset (m : ℕ) : ℕ := if m = 1 then 1 else 2 * (m / 2)

example : threeAdicOnset 1 = 1 := rfl
example : threeAdicOnset 2 = 2 := rfl
example : threeAdicOnset 3 = 2 := rfl
example : threeAdicOnset 4 = 4 := rfl

/-- The terms of Poonen's finite sum whose indices are divisible by three. -/
def threeAdicNonunitSum (m n : ℕ) : ZMod (3 ^ m) :=
  ∑ j ∈ (range (3 ^ m)).filter (fun j => 3 ∣ j),
    (2 : ZMod (3 ^ m)) ^ (3 ^ m - 1 - j) * (j : ZMod (3 ^ m)) ^ n

example : threeAdicNonunitSum 1 0 = 1 := by decide
example : threeAdicNonunitSum 1 1 = 0 := by decide

/-- A unit index in the Poonen sum is periodic from index zero for every
multiple of the Euler period. -/
theorem three_unit_pow_period {m T : ℕ} (hm : 1 ≤ m)
    (hT : 2 * 3 ^ (m - 1) ∣ T) (j : ℕ) (hj : ¬ 3 ∣ j) (n : ℕ) :
    (j : ZMod (3 ^ m)) ^ (n + T) = (j : ZMod (3 ^ m)) ^ n := by
  have hcop : Nat.Coprime j (3 ^ m) :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hj).symm.pow_right m
  have hphi : Nat.totient (3 ^ m) = 2 * 3 ^ (m - 1) := by
    rw [← Nat.sub_add_cancel hm, Nat.totient_prime_pow_succ Nat.prime_three]
    simp [Nat.mul_comm]
  have heuler : (j : ZMod (3 ^ m)) ^ (2 * 3 ^ (m - 1)) = 1 := by
    rw [← hphi]
    have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hcop)
    simpa using he
  obtain ⟨t, rfl⟩ := hT
  rw [pow_add, pow_mul, heuler, one_pow, mul_one]

/-- At indices at least `m`, every nonunit term is zero. -/
theorem three_nonunitSum_eq_zero_of_le {m n : ℕ} (hn : m ≤ n) :
    threeAdicNonunitSum m n = 0 := by
  apply sum_eq_zero
  intro j hj
  obtain ⟨k, rfl⟩ := (mem_filter.mp hj).2
  have hz : (((3 * k : ℕ) : ZMod (3 ^ m))) ^ n = 0 := by
    push_cast
    have h3 : (3 : ZMod (3 ^ m)) ^ n = 0 := by
      simpa using ZMod.natCast_pow_eq_zero_of_le 3 hn
    rw [mul_pow, h3, zero_mul]
  exact mul_eq_zero_of_right _ hz

/-- The finite Poonen formula isolates the entire periodicity defect in
its nonunit-index part, including index zero. -/
theorem three_poonen_difference {m T : ℕ} (hm : 1 ≤ m)
    (hT : 2 * 3 ^ (m - 1) ∣ T) (n : ℕ) :
    ((2 : ZMod (3 ^ m)) ^ (3 ^ m) - 1) *
        ((fubini (n + T) : ZMod (3 ^ m)) - (fubini n : ZMod (3 ^ m))) =
      threeAdicNonunitSum m (n + T) - threeAdicNonunitSum m n := by
  rw [mul_sub, poonen_congr, poonen_congr, ← sum_sub_distrib]
  unfold threeAdicNonunitSum
  rw [← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro j hj
  by_cases hdiv : 3 ∣ j
  · simp [hdiv]
  · simp [hdiv, three_unit_pow_period hm hT j hdiv n]

/-- The Poonen multiplier is a unit modulo every power of three. -/
theorem three_poonen_multiplier_isUnit (m : ℕ) :
    IsUnit ((2 : ZMod (3 ^ m)) ^ (3 ^ m) - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfermat (i : ℕ) : (2 : ZMod 3) ^ 3 ^ i = 2 := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  have hone : 1 ≤ 2 ^ 3 ^ m := Nat.one_le_two_pow
  have hndvd : ¬ 3 ∣ (2 ^ 3 ^ m - 1) := by
    intro hdvd
    have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      ((Nat.modEq_iff_dvd' hone).mpr hdvd)
    push_cast at he
    rw [hfermat m] at he
    exact one_ne_zero (α := ZMod 3) (by linear_combination (-1 : ZMod 3) * he)
  have hcop : Nat.Coprime (2 ^ 3 ^ m - 1) (3 ^ m) :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hndvd).symm.pow_right m
  have hcast : ((2 ^ 3 ^ m - 1 : ℕ) : ZMod (3 ^ m)) =
      (2 : ZMod (3 ^ m)) ^ (3 ^ m) - 1 := by
    rw [Nat.cast_sub hone]
    push_cast
    rfl
  rw [← hcast]
  exact (ZMod.isUnit_iff_coprime _ _).mpr hcop

/-- A positive multiple of the three-adic Euler period is at least `m`. -/
theorem three_period_ge_exponent {m T : ℕ} (hm : 1 ≤ m) (hpos : 0 < T)
    (hT : 2 * 3 ^ (m - 1) ∣ T) : m ≤ T := by
  have hbound (s : ℕ) : s + 1 ≤ 2 * 3 ^ s := by
    induction s with
    | zero => norm_num
    | succ s ih =>
      rw [pow_succ]
      nlinarith [Nat.one_le_pow s 3 (by decide)]
  have hbound' : m ≤ 2 * 3 ^ (m - 1) := by
    simpa only [Nat.sub_add_cancel hm] using hbound (m - 1)
  exact hbound'.trans (Nat.le_of_dvd hpos hT)

/-- For positive admissible shifts, equality of actual Fubini residues at any
index is equivalent to vanishing of the nonunit-index finite sum. -/
theorem three_fubini_eq_iff_nonunitSum_eq_zero {m T : ℕ}
    (hm : 1 ≤ m) (hpos : 0 < T) (hT : 2 * 3 ^ (m - 1) ∣ T) (n : ℕ) :
    fubini (n + T) ≡ fubini n [MOD 3 ^ m] ↔ threeAdicNonunitSum m n = 0 := by
  have hshift : threeAdicNonunitSum m (n + T) = 0 :=
    three_nonunitSum_eq_zero_of_le (by have hb := three_period_ge_exponent hm hpos hT; omega)
  have hdiff := three_poonen_difference hm hT n
  rw [hshift, zero_sub] at hdiff
  constructor
  · intro he
    have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr he
    rw [hcast, sub_self, mul_zero] at hdiff
    exact neg_eq_zero.mp hdiff.symm
  · intro hz
    rw [hz, neg_zero] at hdiff
    have hmul : ((2 : ZMod (3 ^ m)) ^ (3 ^ m) - 1) *
        ((fubini (n + T) : ZMod (3 ^ m)) - (fubini n : ZMod (3 ^ m))) =
        ((2 : ZMod (3 ^ m)) ^ (3 ^ m) - 1) * 0 := by simpa using hdiff
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp
      (sub_eq_zero.mp ((three_poonen_multiplier_isUnit m).mul_left_cancel hmul))

/-- Reindex the nonunit terms exactly by `j = 3*k` and factor out `3^n`. -/
theorem three_nonunitSum_factor {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    threeAdicNonunitSum m n = (3 : ZMod (3 ^ m)) ^ n *
      ∑ k ∈ range (3 ^ (m - 1)),
        (2 : ZMod (3 ^ m)) ^ (3 ^ m - 1 - 3 * k) * (k : ZMod (3 ^ m)) ^ n := by
  unfold threeAdicNonunitSum
  rw [mul_sum]
  symm
  refine sum_bij (fun k _ => 3 * k) ?_ ?_ ?_ ?_
  · intro k hk
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, dvd_mul_right 3 k⟩
    have hp : 3 ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm]
    rw [hp]
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hk) (by decide)
  · intro a ha b hb he
    omega
  · intro j hj
    obtain ⟨k, hk⟩ := (mem_filter.mp hj).2
    refine ⟨k, mem_range.mpr ?_, hk.symm⟩
    have hlt := mem_range.mp (mem_filter.mp hj).1
    have hp : 3 ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm]
    rw [hk, hp] at hlt
    omega
  · intro k hk
    push_cast
    rw [mul_pow]
    ring

/-- No zero-divisor cancellation is used: a zero product by `3^n`, with
`n < m`, forces the other factor to reduce to zero modulo three. -/
theorem three_high_cancel {m n : ℕ} (hn : n < m) (a : ZMod (3 ^ m))
    (ha : (3 : ZMod (3 ^ m)) ^ n * a = 0) :
    ZMod.castHom (dvd_pow_self 3 (by omega : m ≠ 0)) (ZMod 3) a = 0 := by
  haveI : NeZero (3 ^ m) := ⟨by positivity⟩
  have hz : ((3 ^ n * a.val : ℕ) : ZMod (3 ^ m)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val] using ha
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hd' : 3 ^ n * 3 ∣ 3 ^ n * a.val := by
    rw [← pow_succ]
    exact (pow_dvd_pow 3 hn).trans hd
  have hd3 : 3 ∣ a.val := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 3 ^ n)).mp hd'
  rw [← ZMod.natCast_zmod_val a, map_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hd3

/-- At the top nontrivial layer, a coefficient zero modulo three kills the
product, established using natural divisibility rather than cancellation. -/
theorem three_high_vanish {m : ℕ} (hm : 1 ≤ m) (a : ZMod (3 ^ m))
    (ha : ZMod.castHom (dvd_pow_self 3 (by omega : m ≠ 0)) (ZMod 3) a = 0) :
    (3 : ZMod (3 ^ m)) ^ (m - 1) * a = 0 := by
  haveI : NeZero (3 ^ m) := ⟨by positivity⟩
  have ha' : (a.val : ZMod 3) = 0 := by
    rw [← ZMod.natCast_zmod_val a, map_natCast] at ha
    exact ha
  have hd3 := (ZMod.natCast_eq_zero_iff _ _).mp ha'
  have hd : 3 ^ m ∣ 3 ^ (m - 1) * a.val := by
    conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd3
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val] using hz

/-- A finite six-block calculation for the weighted moments modulo three,
valid also at exponent zero with the usual `0^0 = 1` convention. -/
theorem three_six_block_moment (a n : ℕ) :
    (∑ k ∈ range (6 * a + 3), (2 : ZMod 3) ^ k * (k : ZMod 3) ^ n) =
      (0 : ZMod 3) ^ n + 2 + 2 ^ n := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h6 : (6 : ZMod 3) = 0 := by decide
  have htwo3 : (2 : ZMod 3) ^ 3 = -1 := by decide
  have htwo6 : (2 : ZMod 3) ^ 6 = 1 := by decide
  have htwo2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have hshift (k : ℕ) :
      (2 : ZMod 3) ^ (3 + k) * ((3 + k : ℕ) : ZMod 3) ^ n =
        -(2 ^ k * (k : ZMod 3) ^ n) := by
    rw [Nat.add_comm 3 k, pow_add, Nat.cast_add, Nat.cast_ofNat, h3, add_zero, htwo3]
    ring
  have hblock : (∑ k ∈ range 6, (2 : ZMod 3) ^ k * (k : ZMod 3) ^ n) = 0 := by
    rw [show 6 = 3 + 3 by rfl, sum_range_add]
    simp_rw [hshift]
    rw [sum_neg_distrib, add_neg_cancel]
  have hperiod (k r : ℕ) :
      (2 : ZMod 3) ^ (6 * k + r) * ((6 * k + r : ℕ) : ZMod 3) ^ n =
        2 ^ r * (r : ZMod 3) ^ n := by
    rw [pow_add, pow_mul, htwo6, one_pow, one_mul]
    simp [Nat.cast_add, Nat.cast_mul, h6]
  have hzero (b : ℕ) : (∑ k ∈ range (6 * b), (2 : ZMod 3) ^ k * (k : ZMod 3) ^ n) = 0 := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.mul_succ, sum_range_add, ih, zero_add]
      simp_rw [hperiod]
      exact hblock
  rw [sum_range_add, hzero, zero_add]
  simp_rw [hperiod]
  simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
    pow_zero, pow_one, one_pow, mul_one, one_mul, zero_add, htwo2,
    Nat.cast_ofNat]

/-- Reduction of each natural-power Poonen weight modulo three. The bound
on the index keeps natural subtraction away from truncation. -/
theorem three_weight_reduction {m k : ℕ} (hm : 1 ≤ m)
    (hk : k < 3 ^ (m - 1)) :
    (2 : ZMod 3) ^ (3 ^ m - 1 - 3 * k) = 2 ^ k := by
  have htwo2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have hodd : 3 ^ m % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd (3 : ℕ)).pow)
  have hp : 3 ^ m = 3 * 3 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  have hbound : 3 * k ≤ 3 ^ m - 1 := by omega
  rw [pow_eq_pow_mod (3 ^ m - 1 - 3 * k) htwo2, pow_eq_pow_mod k htwo2]
  congr 1
  omega

/-- The factored nonunit coefficient reduces to a finite six-block moment
modulo three. This includes exponent zero rather than discarding `0^0`. -/
theorem three_coefficient_reduction {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    ZMod.castHom (dvd_pow_self 3 (by omega : m ≠ 0)) (ZMod 3)
      (∑ k ∈ range (3 ^ (m - 1)),
        (2 : ZMod (3 ^ m)) ^ (3 ^ m - 1 - 3 * k) * (k : ZMod (3 ^ m)) ^ n) =
      (0 : ZMod 3) ^ n + 2 + 2 ^ n := by
  simp only [map_sum, map_mul, map_pow, map_ofNat, map_natCast]
  have hsum : (∑ k ∈ range (3 ^ (m - 1)),
      (2 : ZMod 3) ^ (3 ^ m - 1 - 3 * k) * (k : ZMod 3) ^ n) =
      ∑ k ∈ range (3 ^ (m - 1)), (2 : ZMod 3) ^ k * (k : ZMod 3) ^ n := by
    apply sum_congr rfl
    intro k hk
    rw [three_weight_reduction (by omega) (mem_range.mp hk)]
  rw [hsum]
  obtain ⟨a, ha⟩ := (by decide : Odd (3 : ℕ)).pow (n := m - 2)
  have hL : 3 ^ (m - 1) = 6 * a + 3 := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ, ha]
    omega
  rw [hL]
  exact three_six_block_moment a n

/-- Nonunit terms vanish from the claimed sharp onset. -/
theorem three_nonunitSum_sharp_tail {m n : ℕ} (hm : 1 ≤ m)
    (hn : threeAdicOnset m ≤ n) : threeAdicNonunitSum m n = 0 := by
  by_cases hmn : m ≤ n
  · exact three_nonunitSum_eq_zero_of_le hmn
  by_cases hm1 : m = 1
  · subst m
    have hn1 : 1 ≤ n := hn
    exact (hmn hn1).elim
  have hm2 : 2 ≤ m := by omega
  have hthreshold : 2 * (m / 2) ≤ n := by
    simpa only [threeAdicOnset, if_neg hm1] using hn
  have hnv : n = m - 1 := by omega
  have hpositive : m - 1 ≠ 0 := by omega
  have heven : (m - 1) % 2 = 0 := by omega
  rw [three_nonunitSum_factor hm n, hnv]
  apply three_high_vanish hm
  rw [three_coefficient_reduction hm2 (m - 1), zero_pow hpositive,
    pow_eq_pow_mod (m - 1) (show (2 : ZMod 3) ^ 2 = 1 by decide), heven]
  decide

/-- The nonunit sum is nonzero at the last index before onset. -/
theorem three_nonunitSum_before_onset_ne_zero {m : ℕ} (hm : 1 ≤ m) :
    threeAdicNonunitSum m (threeAdicOnset m - 1) ≠ 0 := by
  by_cases hm1 : m = 1
  · subst m
    decide
  have hm2 : 2 ≤ m := by omega
  have hidx : threeAdicOnset m - 1 < m := by
    simp only [threeAdicOnset, if_neg hm1]
    omega
  have hpositive : threeAdicOnset m - 1 ≠ 0 := by
    simp only [threeAdicOnset, if_neg hm1]
    omega
  have hodd : (threeAdicOnset m - 1) % 2 = 1 := by
    simp only [threeAdicOnset, if_neg hm1]
    omega
  intro hz
  rw [three_nonunitSum_factor hm] at hz
  have he := three_high_cancel hidx _ hz
  rw [three_coefficient_reduction hm2, zero_pow hpositive,
    pow_eq_pow_mod (threeAdicOnset m - 1) (show (2 : ZMod 3) ^ 2 = 1 by decide), hodd] at he
  exact (by decide : (0 : ZMod 3) + 2 + 2 ^ 1 ≠ 0) he

/-- Whole sharp three-adic onset criterion for the actual Fubini sequence:
all residues repeat after a positive shift from `N` exactly when the Euler
period divides the shift and the sharp onset is at most `N`. -/
theorem fubini_three_power_onset_iff {m T N : ℕ} (hm : 1 ≤ m) (hpos : 0 < T) :
    (∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD 3 ^ m]) ↔
      2 * 3 ^ (m - 1) ∣ T ∧ threeAdicOnset m ≤ N := by
  constructor
  · intro h
    have hT : 2 * 3 ^ (m - 1) ∣ T := by
      have he := (fubini_prime_power_eventual_period_iff Nat.prime_three (by decide) hm).mp
        ⟨N, h⟩
      simpa only [Nat.reduceSub, Nat.mul_comm] using he
    refine ⟨hT, ?_⟩
    by_contra hN
    have hidx : N ≤ threeAdicOnset m - 1 := by omega
    have hz := (three_fubini_eq_iff_nonunitSum_eq_zero hm hpos hT _).mp (h _ hidx)
    exact three_nonunitSum_before_onset_ne_zero hm hz
  · rintro ⟨hT, hN⟩ n hn
    exact (three_fubini_eq_iff_nonunitSum_eq_zero hm hpos hT n).mpr
      (three_nonunitSum_sharp_tail hm (hN.trans hn))

example : 1 ≤ (3 : ℕ) ∧ 0 < (18 : ℕ) ∧ 2 * 3 ^ (3 - 1) ∣ (18 : ℕ) ∧
    threeAdicOnset 3 ≤ 2 := by decide

example : ∀ n, 2 ≤ n → fubini (n + 18) ≡ fubini n [MOD 3 ^ 3] := by
  exact (fubini_three_power_onset_iff (by decide) (by decide)).mpr ⟨by decide, by decide⟩

example : ¬ (∀ n, 1 ≤ n → fubini (n + 18) ≡ fubini n [MOD 3 ^ 3]) := by
  rw [fubini_three_power_onset_iff (by decide) (by decide)]
  decide

example : ∀ n, 1 ≤ n → fubini (n + 2) ≡ fubini n [MOD 3 ^ 1] := by
  exact (fubini_three_power_onset_iff (by decide) (by decide)).mpr ⟨by decide, by decide⟩

example : ¬ (∀ n, 0 ≤ n → fubini (n + 2) ≡ fubini n [MOD 3 ^ 1]) := by
  rw [fubini_three_power_onset_iff (by decide) (by decide)]
  decide

example : ∀ n, 0 ≤ n → fubini (n + 0) ≡ fubini n [MOD 3 ^ 1] := by
  intro n hn
  exact Nat.ModEq.refl _

example : 1 ≤ (1 : ℕ) ∧ 0 < (2 : ℕ) ∧ 2 * 3 ^ (1 - 1) ∣ (2 : ℕ) ∧
    ¬ 3 ∣ (1 : ℕ) ∧ 0 < 3 ^ (1 - 1) ∧ (0 : ℕ) < 1 := by decide

example : (3 : ZMod (3 ^ 1)) ^ (0 : ℕ) * 0 = 0 := by decide

example : ZMod.castHom (dvd_refl 3) (ZMod 3) (0 : ZMod (3 ^ 1)) = 0 := by decide

example : threeAdicOnset 2 ≤ 2 ∧ 2 ≤ (2 : ℕ) := by decide

end A000670
