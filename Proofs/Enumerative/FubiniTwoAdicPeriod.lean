import Enumerative.FubiniMod

/-!
# Exact eventual periods of Fubini numbers modulo powers of two

This formalizes the known dyadic period pattern for the actual sequence
`A051293.fubini`. It characterizes every natural shift, including zero, and
allows modulus one. No optimal starting index or novelty is claimed.
The proof uses Poonen's finite-sum identity from `Enumerative.FubiniMod`,
the two-adic lifting-the-exponent theorem, and closure of tail periods under gcd.
-/

set_option autoImplicit false

namespace A000670

/-- The power of two dividing the dyadic increment of the base three is exact. -/
theorem padicValNat_three_pow_two_pow_sub_one (r : ℕ) (hr : 1 ≤ r) :
    padicValNat 2 (3 ^ (2 ^ r) - 1) = r + 2 := by
  have heven : Even (2 ^ r) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have h := padicValNat.pow_two_sub_one (x := 3) (by omega) (by decide)
    (pow_ne_zero r (by decide : (2 : ℕ) ≠ 0)) heven
  have hfour : padicValNat 2 4 = 2 := by
    exact padicValNat.prime_pow 2
  norm_num [padicValNat.prime_pow, hfour] at h ⊢
  omega

example : 1 ≤ (1 : ℕ) ∧ padicValNat 2 (3 ^ (2 ^ 1) - 1) = 3 := by
  constructor
  · decide
  · exact padicValNat_three_pow_two_pow_sub_one 1 (by decide)

/-- An odd base has a dyadic increment divisible by two extra powers of two. -/
lemma two_pow_dvd_odd_increment (j r : ℕ) (hj : ¬2 ∣ j) (hr : 1 ≤ r) :
    2 ^ (r + 2) ∣ j ^ (2 ^ r) - 1 := by
  by_cases hsmall : j ≤ 1
  · have hj1 : j = 1 := by
      by_contra h
      have : j = 0 := by omega
      subst j
      exact hj (dvd_zero 2)
    subst j
    simp
  have hjbig : 1 < j := by omega
  have hn : 2 ^ r ≠ 0 := pow_ne_zero _ (by decide)
  have heven : Even (2 ^ r) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have hpos : 1 < j ^ (2 ^ r) := one_lt_pow₀ hjbig hn
  apply (padicValNat_dvd_iff_le (by omega : j ^ (2 ^ r) - 1 ≠ 0)).mpr
  have h := padicValNat.pow_two_sub_one_ge hjbig hj hn heven
  rw [padicValNat.prime_pow] at h
  exact h

/-- Poonen's finite sum for a dyadic shift has just one surviving term. -/
theorem fubini_two_pow_shift_survivor (r n : ℕ) (hr : 1 ≤ r) (hn : r + 4 ≤ n) :
    (A051293.fubini (n + 2 ^ r) : ZMod (2 ^ (r + 5))) - A051293.fubini n =
      -4 * (-3 : ZMod (2 ^ (r + 5))) ^ n * ((3 : ZMod (2 ^ (r + 5))) ^ (2 ^ r) - 1) := by
  let q := 2 ^ (r + 5)
  have hq : 8 ≤ q := by
    exact (show 8 = 2 ^ 3 by decide).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hzero : (2 : ZMod q) ^ (r + 5) = 0 := by
    exact (Nat.cast_pow 2 (r + 5)).symm.trans (ZMod.natCast_self q)
  have hqexp : r + 5 ≤ q := Nat.le_of_lt Nat.lt_two_pow_self
  have hfactor : (2 : ZMod q) ^ q - 1 = -1 := by
    rw [pow_eq_zero_of_le hqexp hzero, zero_sub]
  have hA := poonen_congr q (n + 2 ^ r)
  have hB := poonen_congr q n
  rw [hfactor] at hA hB
  have hsum : (A051293.fubini (n + 2 ^ r) : ZMod q) - A051293.fubini n =
      - ∑ j ∈ Finset.range q, (2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ n *
        ((j : ZMod q) ^ (2 ^ r) - 1) := by
    have hdiff := congrArg₂ (fun a b : ZMod q => a - b) hA hB
    rw [← Finset.sum_sub_distrib] at hdiff
    have hterms : (∑ j ∈ Finset.range q,
        ((2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ (n + 2 ^ r) -
          (2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ n)) =
        ∑ j ∈ Finset.range q, (2 : ZMod q) ^ (q - 1 - j) * (j : ZMod q) ^ n *
          ((j : ZMod q) ^ (2 ^ r) - 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    rw [hterms] at hdiff
    linear_combination -hdiff
  rw [hsum]
  have heven : Even (2 ^ r) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have htop : ((q - 1 : ℕ) : ZMod q) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hthree : ((q - 3 : ℕ) : ZMod q) = -3 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_ofNat, zero_sub]
  rw [Finset.sum_eq_single (q - 3)]
  · rw [hthree, show q - 1 - (q - 3) = 2 by omega, show (2 : ZMod q) ^ 2 = 4 by ring]
    have hp : (-3 : ZMod q) ^ (2 ^ r) = 3 ^ (2 ^ r) := heven.neg_pow 3
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
      have hcoeff : 1 ≤ q - 1 - j := by omega
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
          ((j : ZMod q) ^ (2 ^ r) - 1) := by ring
        _ = 0 := by rw [hpow]; ring
    · by_cases ht : j = q - 1
      · rw [ht, htop, heven.neg_one_pow, sub_self, mul_zero]
      have hcoeff : 4 ≤ q - 1 - j := by
        have hjodd : Odd j := Nat.not_even_iff_odd.mp (fun h => hd h.two_dvd)
        have hqeven : Even q := by
          dsimp [q]
          exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
        obtain ⟨a, ha⟩ := hjodd
        obtain ⟨b, hb⟩ := hqeven
        omega
      obtain ⟨a, ha⟩ := two_pow_dvd_odd_increment j r hd hr
      have hjpos : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        exact hd (hj0 ▸ dvd_zero 2)
      have hp : 1 ≤ j ^ (2 ^ r) := one_le_pow₀ hjpos
      have hjpow : (j : ZMod q) ^ (2 ^ r) - 1 = 2 ^ (r + 2) * (a : ZMod q) := by
        have hc := congrArg (fun x : ℕ => (x : ZMod q)) ha
        simpa only [Nat.cast_sub hp, Nat.cast_one, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat] using hc
      rw [hjpow]
      have hpow : (2 : ZMod q) ^ (q - 1 - j) * 2 ^ (r + 2) = 0 := by
        rw [← pow_add]
        exact pow_eq_zero_of_le (by omega) hzero
      calc
        _ = ((2 : ZMod q) ^ (q - 1 - j) * 2 ^ (r + 2)) * (j : ZMod q) ^ n * a := by ring
        _ = 0 := by rw [hpow]; ring
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

/-- The natural magnitude of the surviving term has exactly the required valuation. -/
lemma survivor_valuation (r n : ℕ) (hr : 1 ≤ r) :
    padicValNat 2 (4 * 3 ^ n * (3 ^ (2 ^ r) - 1)) = r + 4 := by
  have hp : 1 < 3 ^ (2 ^ r) := one_lt_pow₀ (by decide) (pow_ne_zero _ (by decide))
  have hd : 3 ^ (2 ^ r) - 1 ≠ 0 := by omega
  have hthree : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have hfour : padicValNat 2 4 = 2 := padicValNat.prime_pow 2
  rw [padicValNat.mul (by positivity) hd, padicValNat.mul (by decide)
    (pow_ne_zero _ (by decide)), padicValNat.pow, hthree, hfour,
    padicValNat_three_pow_two_pow_sub_one r hr]
  omega

/-- The dyadic shift is not a congruence at the next power of two. -/
theorem fubini_two_pow_shift_not_modEq (r n : ℕ) (hr : 1 ≤ r) (hn : r + 4 ≤ n) :
    ¬ A051293.fubini (n + 2 ^ r) ≡ A051293.fubini n [MOD 2 ^ (r + 5)] := by
  intro h
  have heq := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hz := (sub_eq_zero.mpr heq).symm.trans (fubini_two_pow_shift_survivor r n hr hn)
  have hu : IsUnit ((-3 : ZMod (2 ^ (r + 5))) ^ n) := by
    apply IsUnit.pow
    apply IsUnit.neg
    exact (ZMod.isUnit_iff_coprime 3 _).mpr ((by decide : Nat.Coprime 3 2).pow_right _)
  have hz' : (4 : ZMod (2 ^ (r + 5))) * (3 ^ (2 ^ r) - 1) = 0 := by
    apply neg_eq_zero.mp
    apply hu.mul_left_eq_zero.mp
    calc
      _ = -4 * (-3 : ZMod (2 ^ (r + 5))) ^ n * (3 ^ (2 ^ r) - 1) := by ring
      _ = 0 := hz.symm
  have hp : 1 ≤ 3 ^ (2 ^ r) := one_le_pow₀ (by decide)
  have hcast : ((4 * 3 ^ n * (3 ^ (2 ^ r) - 1) : ℕ) : ZMod (2 ^ (r + 5))) = 0 := by
    push_cast [Nat.cast_sub hp]
    calc
      _ = (4 * (3 ^ (2 ^ r) - 1) : ZMod (2 ^ (r + 5))) * 3 ^ n := by ring
      _ = 0 := by rw [hz', zero_mul]
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hnonzero : 4 * 3 ^ n * (3 ^ (2 ^ r) - 1) ≠ 0 := by
    have hpow : 1 < 3 ^ (2 ^ r) := one_lt_pow₀ (by decide) (pow_ne_zero _ (by decide))
    exact mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero _ (by decide))) (by omega)
  have hv := (padicValNat_dvd_iff_le hnonzero).mp hd
  rw [survivor_valuation r n hr] at hv
  omega

/-- The dyadic shift is a congruence one power of two lower. -/
theorem fubini_two_pow_shift_modEq (r n : ℕ) (hr : 1 ≤ r) (hn : r + 4 ≤ n) :
    A051293.fubini (n + 2 ^ r) ≡ A051293.fubini n [MOD 2 ^ (r + 4)] := by
  have h := fubini_two_pow_shift_survivor r n hr hn
  let f := ZMod.castHom (show 2 ^ (r + 4) ∣ 2 ^ (r + 5) from pow_dvd_pow 2 (by omega))
    (ZMod (2 ^ (r + 4)))
  have hmap := congrArg f h
  simp only [map_sub, map_natCast, map_mul, map_neg, map_ofNat, map_pow, map_one] at hmap
  obtain ⟨a, ha⟩ := two_pow_dvd_odd_increment 3 r (by decide) hr
  have hp : 1 ≤ 3 ^ (2 ^ r) := one_le_pow₀ (by decide)
  have hc := congrArg (fun x : ℕ => (x : ZMod (2 ^ (r + 4)))) ha
  simp only [Nat.cast_sub hp, Nat.cast_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hz : (4 : ZMod (2 ^ (r + 4))) * 2 ^ (r + 2) = 0 := by
    have hpow : (2 : ZMod (2 ^ (r + 4))) ^ (r + 4) = 0 := by
      exact (Nat.cast_pow 2 (r + 4)).symm.trans (ZMod.natCast_self _)
    calc
      _ = (2 : ZMod (2 ^ (r + 4))) ^ (r + 4) := by
        rw [show r + 4 = 2 + (r + 2) by omega, pow_add]
        ring
      _ = 0 := hpow
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  apply sub_eq_zero.mp
  rw [hmap, hc]
  calc
    _ = -(4 * 2 ^ (r + 2) : ZMod (2 ^ (r + 4))) * (-3) ^ n * a := by ring
    _ = 0 := by rw [hz]; ring

/-- A tail period remains a tail period after multiplication. -/
lemma eventual_period_mul {α : Type*} (f : ℕ → α) {a b : ℕ}
    (ha : ∃ N, ∀ n, N ≤ n → f (n + a) = f n) (hab : a ∣ b) :
    ∃ N, ∀ n, N ≤ n → f (n + b) = f n := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨k, rfl⟩ := hab
  refine ⟨N, fun n hn => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hN _ (by omega), ih]

/-- Two tail periods have their greatest common divisor as a tail period. -/
lemma eventual_period_gcd {α : Type*} (f : ℕ → α) {a b : ℕ}
    (ha : ∃ N, ∀ n, N ≤ n → f (n + a) = f n)
    (hb : ∃ N, ∀ n, N ≤ n → f (n + b) = f n) :
    ∃ N, ∀ n, N ≤ n → f (n + Nat.gcd a b) = f n := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  let N := max A B
  let shift : (ℕ → α) → (ℕ → α) := fun g n => g (n + 1)
  have hiter (k : ℕ) (g : ℕ → α) : shift^[k] g = fun n => g (n + k) := by
    induction k generalizing g with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      funext n
      dsimp [shift]
      congr 1
  have hpa : Function.IsPeriodicPt shift a (fun n => f (N + n)) := by
    change shift^[a] (fun n => f (N + n)) = _
    rw [hiter]
    funext n
    exact (by simpa only [Nat.add_assoc] using hA (N + n) (by dsimp [N]; omega))
  have hpb : Function.IsPeriodicPt shift b (fun n => f (N + n)) := by
    change shift^[b] (fun n => f (N + n)) = _
    rw [hiter]
    funext n
    exact (by simpa only [Nat.add_assoc] using hB (N + n) (by dsimp [N]; omega))
  have hg := hpa.gcd hpb
  change shift^[Nat.gcd a b] (fun n => f (N + n)) = _ at hg
  rw [hiter] at hg
  refine ⟨N, fun n hn => ?_⟩
  have hvalue := congrFun hg (n - N)
  simpa only [← Nat.add_assoc, Nat.add_sub_of_le hn] using hvalue

/-- A power-of-two period is minimal once its half is excluded. -/
lemma eventual_period_two_pow_iff {α : Type*} (f : ℕ → α) (k T : ℕ) (hk : 1 ≤ k)
    (hupper : ∃ N, ∀ n, N ≤ n → f (n + 2 ^ k) = f n)
    (hlower : ¬ ∃ N, ∀ n, N ≤ n → f (n + 2 ^ (k - 1)) = f n) :
    (∃ N, ∀ n, N ≤ n → f (n + T) = f n) ↔ 2 ^ k ∣ T := by
  constructor
  · intro hT
    by_contra hnot
    have hg := eventual_period_gcd f hupper hT
    obtain ⟨j, hj, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ k) T)
    have hjlt : j < k := by
      by_contra h
      have hjk : j = k := by omega
      exact hnot (by simpa only [heq, hjk] using Nat.gcd_dvd_right (2 ^ k) T)
    apply hlower
    apply eventual_period_mul f hg
    rw [heq]
    exact pow_dvd_pow 2 (by omega)
  · exact eventual_period_mul f hupper

/-- Consecutive Fubini residues modulo four cannot eventually coincide. -/
lemma fubini_not_eventual_period_one_four :
    ¬ ∃ N, ∀ n, N ≤ n → A051293.fubini (n + 1) ≡ A051293.fubini n [MOD 4] := by
  intro ⟨N, hN⟩
  have hpair (k : ℕ) :
      A051293.fubini (1 + 2 * k) ≡ A051293.fubini 1 [MOD 4] ∧
      A051293.fubini (2 + 2 * k) ≡ A051293.fubini 2 [MOD 4] := by
    induction k with
    | zero => exact ⟨Nat.ModEq.refl _, Nat.ModEq.refl _⟩
    | succ k ih =>
      constructor
      · simpa only [Nat.mul_succ, Nat.add_assoc] using
          (fubini_add_two_modEq_four (1 + 2 * k) (by omega)).trans ih.1
      · simpa only [Nat.mul_succ, Nat.add_assoc] using
          (fubini_add_two_modEq_four (2 + 2 * k) (by omega)).trans ih.2
  have hmid : A051293.fubini (2 + 2 * N) ≡ A051293.fubini (1 + 2 * N) [MOD 4] := by
    have hi : 1 + 2 * N + 1 = 2 + 2 * N := by omega
    simpa only [hi] using hN (1 + 2 * N) (by omega)
  have h := (hpair N).2.symm.trans (hmid.trans (hpair N).1)
  rw [A051293.fubini_one, A051293.fubini_two] at h
  exact (by decide : ¬ (3 ≡ 1 [MOD 4])) h

/-- The proposed dyadic period is an eventual period at every exponent at least two. -/
lemma fubini_two_adic_upper (m : ℕ) (hm : 2 ≤ m) :
    ∃ N, ∀ n, N ≤ n → A051293.fubini (n + 2 ^ (max 1 (m - 4))) ≡
      A051293.fubini n [MOD 2 ^ m] := by
  by_cases hsmall : m ≤ 5
  · refine ⟨5, fun n hn => ?_⟩
    have hk : max 1 (m - 4) = 1 := by omega
    rw [hk]
    exact Nat.ModEq.of_dvd (pow_dvd_pow 2 hsmall) (fubini_two_pow_shift_modEq 1 n (by decide) hn)
  · refine ⟨m, fun n hn => ?_⟩
    have hk : max 1 (m - 4) = m - 4 := by omega
    rw [hk]
    have h := fubini_two_pow_shift_modEq (m - 4) n (by omega) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 4 ≤ m)] using h

/-- Half of the proposed dyadic period is never an eventual period. -/
lemma fubini_two_adic_lower (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ N, ∀ n, N ≤ n → A051293.fubini (n + 2 ^ (max 1 (m - 4) - 1)) ≡
      A051293.fubini n [MOD 2 ^ m] := by
  intro ⟨N, hN⟩
  by_cases hsmall : m ≤ 5
  · apply fubini_not_eventual_period_one_four
    refine ⟨N, fun n hn => ?_⟩
    have hk : max 1 (m - 4) - 1 = 0 := by omega
    have h := Nat.ModEq.of_dvd (pow_dvd_pow 2 hm) (hN n hn)
    simpa only [hk, pow_zero, show (2 : ℕ) ^ 2 = 4 by decide] using h
  · let n := max N m
    have hk : max 1 (m - 4) - 1 = m - 5 := by omega
    have hbad := fubini_two_pow_shift_not_modEq (m - 5) n (by omega) (by dsimp [n]; omega)
    have hgood := hN n (by dsimp [n]; omega)
    rw [hk] at hgood
    apply hbad
    simpa only [Nat.sub_add_cancel (by omega : 5 ≤ m)] using hgood

/-- The eventual periods of the actual Fubini sequence modulo `2^m` are exactly
multiples of `1` for `m ≤ 1`, and of `2^(max 1 (m-4))` otherwise, including shift zero. -/
theorem fubini_two_adic_eventual_period_iff (m T : ℕ) :
    (∃ N, ∀ n, N ≤ n → A051293.fubini (n + T) ≡ A051293.fubini n [MOD 2 ^ m]) ↔
      (if m ≤ 1 then 1 else 2 ^ (max 1 (m - 4))) ∣ T := by
  by_cases hm : m ≤ 1
  · rw [if_pos hm]
    constructor
    · intro _
      exact one_dvd T
    · intro _
      interval_cases m
      · refine ⟨0, fun n _ => ?_⟩
        exact Nat.modEq_one
      · have hbase : ∃ N, ∀ n, N ≤ n →
            (A051293.fubini (n + 1) : ZMod 2) = A051293.fubini n :=
          ⟨0, fun n _ => (ZMod.natCast_eq_natCast_iff _ _ _).mpr (fubini_succ_modEq_two n)⟩
        obtain ⟨N, hN⟩ := eventual_period_mul (fun n => (A051293.fubini n : ZMod 2)) hbase (one_dvd T)
        exact ⟨N, fun n hn => (ZMod.natCast_eq_natCast_iff _ _ _).mp (hN n hn)⟩
  · rw [if_neg hm]
    have hm2 : 2 ≤ m := by omega
    have hu := fubini_two_adic_upper m hm2
    have hl := fubini_two_adic_lower m hm2
    have hcast : (∃ N, ∀ n, N ≤ n →
        (A051293.fubini (n + 2 ^ (max 1 (m - 4))) : ZMod (2 ^ m)) = A051293.fubini n) := by
      simpa only [ZMod.natCast_eq_natCast_iff] using hu
    have hlcast : ¬ ∃ N, ∀ n, N ≤ n →
        (A051293.fubini (n + 2 ^ (max 1 (m - 4) - 1)) : ZMod (2 ^ m)) = A051293.fubini n := by
      simpa only [ZMod.natCast_eq_natCast_iff] using hl
    have h := eventual_period_two_pow_iff (fun n => (A051293.fubini n : ZMod (2 ^ m)))
      (max 1 (m - 4)) T (by omega) hcast hlcast
    simpa only [ZMod.natCast_eq_natCast_iff] using h

example : ∃ N, ∀ n, N ≤ n → A051293.fubini (n + 2) ≡ A051293.fubini n [MOD 32] := by
  exact (fubini_two_adic_eventual_period_iff 5 2).mpr (by decide)

example : ∃ N, ∀ n, N ≤ n → A051293.fubini (n + 0) ≡ A051293.fubini n [MOD 1] := by
  exact (fubini_two_adic_eventual_period_iff 0 0).mpr (by decide)

example :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n + 2) % 2 = n % 2) ∧
    ¬ (∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n + 1) % 2 = n % 2) := by
  constructor
  · exact ⟨0, fun n _ => by omega⟩
  · rintro ⟨N, hN⟩
    have h := hN N (le_refl N)
    omega

end A000670
