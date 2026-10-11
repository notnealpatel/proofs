import Erdos.InfinitarySuperperfectSquareInput
import Erdos.InfinitarySuccessorOrigins

set_option autoImplicit false

namespace InfinitarySuperperfect

private theorem prime313 : Nat.Prime 313 := by norm_num

/-- A 313-divisible binary successor forces the base's eighth power to be one
modulo 313, at every height, without a finite height cutoff. -/
theorem pow_eight_eq_one_of_313_dvd (b h : ℕ)
    (hd : 313 ∣ b ^ (2 ^ h) + 1) : (b : ZMod 313) ^ 8 = 1 := by
  letI : Fact (Nat.Prime 313) := ⟨prime313⟩
  have hord := Erdos.InfinitarySuccessorOrigins.orderOf_eq_two_pow_succ
    313 b h prime313 (by norm_num) hd
  have hb : (b : ZMod 313) ≠ 0 := by
    intro hz
    have hc := (ZMod.natCast_eq_zero_iff (b ^ (2 ^ h) + 1) 313).mpr hd
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hz,
      zero_pow (by positivity : 2 ^ h ≠ 0), zero_add] at hc
    exact one_ne_zero hc
  have hdiv : 2 ^ (h + 1) ∣ 312 := by
    rw [← hord]
    exact ZMod.orderOf_dvd_card_sub_one hb
  have hbound : h + 1 ≤ 3 := by
    by_contra hh
    have h16 : 16 ∣ 312 := (by norm_num : 16 = 2 ^ 4) ▸
      (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : 4 ≤ h + 1)) hdiv)
    norm_num at h16
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hord]
  exact Nat.pow_dvd_pow 2 hbound

/-- Neither base two nor base three has any binary successor divisible by 313. -/
theorem not_dvd_313_two_three (h : ℕ) :
    ¬313 ∣ 2 ^ (2 ^ h) + 1 ∧ ¬313 ∣ 3 ^ (2 ^ h) + 1 := by
  constructor
  · intro hd
    have hc := pow_eight_eq_one_of_313_dvd 2 h hd
    exact (by decide : (2 : ZMod 313) ^ 8 ≠ 1) hc
  · intro hd
    have hc := pow_eight_eq_one_of_313_dvd 3 h hd
    exact (by decide : (3 : ZMod 313) ^ 8 ≠ 1) hc

private theorem reverse_high_impossible (p h : ℕ) (hh : 1 ≤ h)
    (hp8 : (p : ZMod 313) ^ 8 = 1)
    (hs : ∀ q : ℕ, q.Prime → q ∣ 313 ^ (2 ^ h) + 1 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = p) : False := by
  by_cases hh1 : h = 1
  · subst h
    have h97 := hs 97 (by norm_num) (by norm_num)
    have h101 := hs 101 (by norm_num) (by norm_num)
    norm_num at h97 h101
    omega
  have hh2 : 2 ≤ h := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh2
  let s := 313 ^ (2 ^ (2 + k)) + 1
  let r := s / 2
  have hs4 : s % 4 = 2 := by
    dsimp [s]
    simp [Nat.add_mod, Nat.pow_mod]
  have hs3 : s % 3 = 2 := by
    dsimp [s]
    simp [Nat.add_mod, Nat.pow_mod]
  have hs5 : s % 5 = 2 := by
    dsimp [s]
    rw [show 2 ^ (2 + k) = 4 * 2 ^ k by rw [pow_add]; norm_num,
      pow_mul]
    simp [Nat.add_mod, Nat.pow_mod]
  have heq : 2 * r = s := by dsimp [r]; omega
  have hrpos : 0 < r := by
    have hspos : 0 < s := by dsimp [s]; positivity
    omega
  have hrpow : r = p ^ r.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd (ne_of_gt hrpos)
    intro q hq hqr
    have hqs : q ∣ s := hqr.trans (by rw [← heq]; exact dvd_mul_left r 2)
    rcases hs q hq hqs with h2 | h3 | h5 | hp
    · subst q
      obtain ⟨t, ht⟩ := hqr
      have h4 : 4 ∣ s := by rw [← heq, ht]; omega
      have hz := Nat.mod_eq_zero_of_dvd h4
      omega
    · subst q
      have hz := Nat.mod_eq_zero_of_dvd hqs
      omega
    · subst q
      have hz := Nat.mod_eq_zero_of_dvd hqs
      omega
    · exact hp
  have hr8 : (r : ZMod 313) ^ 8 = 1 := by
    rw [hrpow, Nat.cast_pow, ← pow_mul, Nat.mul_comm, pow_mul, hp8, one_pow]
  have hcast : (2 : ZMod 313) * r = 1 := by
    have hc := congrArg (fun x : ℕ => (x : ZMod 313)) heq
    simpa [s, show (313 : ZMod 313) = 0 by decide,
      zero_pow (by positivity : 2 ^ (2 + k) ≠ 0)] using hc
  have hr157 : (r : ZMod 313) = 157 := by
    calc
      (r : ZMod 313) = 157 * (2 * r) := by
        rw [← mul_assoc, show (157 : ZMod 313) * 2 = 1 by decide, one_mul]
      _ = 157 := by rw [hcast]; ring
  rw [hr157] at hr8
  exact (by decide : (157 : ZMod 313) ^ 8 ≠ 1) hr8

private theorem localSigma_two_pow (b j : ℕ) :
    localSigma b (2 ^ j) = 1 + b ^ (2 ^ j) := by
  have hb : binarySupport (2 ^ j) = {j} := by
    ext h
    simp only [mem_binarySupport_iff, Nat.testBit_two_pow,
      decide_eq_true_eq, Finset.mem_singleton]
    omega
  simp [localSigma, hb]

private theorem sigma_shape (a j ell p : ℕ) (ha : 0 < a)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    sigma (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell)) =
      localSigma 2 a * (1 + 3 ^ (2 ^ j)) * 626 * (1 + p ^ (2 ^ ell)) := by
  have hp0 := hp.pos
  have hf : (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell)).primeFactors =
      {2, 3, 5, p} := by
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_prime_pow (by omega : a ≠ 0) Nat.prime_two,
      Nat.primeFactors_prime_pow (by positivity : 2 ^ j ≠ 0) (by norm_num : Nat.Prime 3),
      Nat.primeFactors_prime_pow (by norm_num : (4 : ℕ) ≠ 0) (by norm_num : Nat.Prime 5),
      Nat.primeFactors_prime_pow (by positivity : 2 ^ ell ≠ 0) hp]
    ext q
    simp
  have hv : (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell)).factorization =
      a • Nat.factorization 2 + (2 ^ j) • Nat.factorization 3 +
      4 • Nat.factorization 5 + (2 ^ ell) • Nat.factorization p := by
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity)]
    simp only [Nat.factorization_pow]
  have hv2 : (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell)).factorization 2 = a := by
    rw [hv]
    simp [Nat.Prime.factorization, hp, Nat.prime_two,
      show Nat.Prime 3 by norm_num, show Nat.Prime 5 by norm_num, hp2]
  have hv3 : (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell)).factorization 3 = 2 ^ j := by
    rw [hv]
    simp [Nat.Prime.factorization, hp, Nat.prime_two,
      show Nat.Prime 3 by norm_num, show Nat.Prime 5 by norm_num, hp3]
  have hv5 : (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell)).factorization 5 = 4 := by
    rw [hv]
    simp [Nat.Prime.factorization, hp, Nat.prime_two,
      show Nat.Prime 3 by norm_num, show Nat.Prime 5 by norm_num, hp5]
  have hvp : (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell)).factorization p = 2 ^ ell := by
    rw [hv]
    simp [Nat.Prime.factorization, hp, Nat.prime_two,
      show Nat.Prime 3 by norm_num, show Nat.Prime 5 by norm_num,
      Ne.symm hp2, Ne.symm hp3, Ne.symm hp5]
  rw [sigma, hf]
  rw [Finset.prod_insert (by simp [Ne.symm hp2]),
    Finset.prod_insert (by simp [Ne.symm hp3]),
    Finset.prod_insert (by simp [Ne.symm hp5]), Finset.prod_singleton,
    hv2, hv3, hv5, hvp, localSigma_two_pow, localSigma_two_pow,
    show (4 : ℕ) = 2 ^ 2 by norm_num, localSigma_two_pow]
  norm_num
  ring

private theorem prime_dvd_twice_shape (a j ell p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hd : q ∣ 2 * (2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell))) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = p := by
  have h2 : q ∣ 2 → q = 2 := fun h =>
    ((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hq.ne_one
  have h3 : q ∣ 3 → q = 3 := fun h =>
    ((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h).resolve_left hq.ne_one
  have h5 : q ∣ 5 → q = 5 := fun h =>
    ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h).resolve_left hq.ne_one
  have hpp : q ∣ p → q = p := fun h =>
    ((Nat.dvd_prime hp).mp h).resolve_left hq.ne_one
  rcases hq.dvd_mul.mp hd with ht | hn
  · exact Or.inl (h2 ht)
  rcases hq.dvd_mul.mp hn with hn | ht
  · rcases hq.dvd_mul.mp hn with hn | ht
    · rcases hq.dvd_mul.mp hn with ht | ht
      · exact Or.inl (h2 (hq.dvd_of_dvd_pow ht))
      · exact Or.inr (Or.inl (h3 (hq.dvd_of_dvd_pow ht)))
    · exact Or.inr (Or.inr (Or.inl (h5 (hq.dvd_of_dvd_pow ht))))
  · exact Or.inr (Or.inr (Or.inr (hpp (hq.dvd_of_dvd_pow ht))))

private theorem higher_bit_of_one_lt (b : ℕ) (hb : 1 < b) :
    ∃ h ∈ binarySupport b, 1 ≤ h := by
  by_contra hex
  have hsub : binarySupport b ⊆ {0} := by
    intro h hh
    have hnot : ¬1 ≤ h := fun hhpos => hex ⟨h, hh, hhpos⟩
    simp only [Finset.mem_singleton]
    omega
  have hsum : (∑ h ∈ binarySupport b, 2 ^ h) ≤ ∑ h ∈ ({0} : Finset ℕ), 2 ^ h :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [sum_binarySupport] at hsum
  simp only [Finset.sum_singleton, pow_zero] at hsum
  omega

/-- For the explicit actual-cycle input with the five exponent four, 313 occurs
exactly once in the forward sum, and the remaining odd input prime is 157.
No support-normalization hypothesis is assumed, and no contradiction for the
entire factorization-three branch is asserted. -/
theorem anchor313_of_actual_cycle_shape (n m a j ell p : ℕ)
    (ha : 2 ≤ a) (_haeven : Even a) (_hj : 1 ≤ j) (_hell : 1 ≤ ell)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hn : n = 2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell))
    (hforward : m = sigma n) (hreverse : sigma m = 2 * n) :
    m.factorization 313 = 1 ∧ p = 157 := by
  have hmpos : 0 < m := by rw [hforward]; exact sigma_pos n
  have hshape : m = localSigma 2 a * (1 + 3 ^ (2 ^ j)) * 626 *
      (1 + p ^ (2 ^ ell)) := by
    rw [hforward, hn]
    exact sigma_shape a j ell p (by omega) hp hp2 hp3 hp5
  have htwo : ¬313 ∣ localSigma 2 a := by
    intro hd
    obtain ⟨h, _, hdslot⟩ := (prime313.prime.dvd_finsetProd_iff
      (fun h => 1 + 2 ^ (2 ^ h))).mp hd
    exact (not_dvd_313_two_three h).1 (by simpa only [Nat.add_comm] using hdslot)
  have hthree : ¬313 ∣ 1 + 3 ^ (2 ^ j) := by
    simpa only [Nat.add_comm] using (not_dvd_313_two_three j).2
  have h626 : (626 : ℕ).factorization 313 = 1 := by
    rw [show (626 : ℕ) = 2 * 313 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.prime_two.factorization, prime313.factorization]
  have hlocalpos := localSigma_pos 2 a
  have h3ne : 1 + 3 ^ (2 ^ j) ≠ 0 := by omega
  have hpne : 1 + p ^ (2 ^ ell) ≠ 0 := by omega
  have hleftne : localSigma 2 a * (1 + 3 ^ (2 ^ j)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hlocalpos) h3ne
  have h626ne : (626 : ℕ) ≠ 0 := by decide
  have hB : m.factorization 313 = 1 + (1 + p ^ (2 ^ ell)).factorization 313 := by
    rw [hshape,
      Nat.factorization_mul
        (a := localSigma 2 a * (1 + 3 ^ (2 ^ j)) * 626)
        (b := 1 + p ^ (2 ^ ell)) (mul_ne_zero hleftne h626ne) hpne,
      Nat.factorization_mul (a := localSigma 2 a * (1 + 3 ^ (2 ^ j)))
        (b := 626) hleftne h626ne,
      Nat.factorization_mul (a := localSigma 2 a) (b := 1 + 3 ^ (2 ^ j))
        (ne_of_gt hlocalpos) h3ne]
    simp [Nat.factorization_eq_zero_of_not_dvd htwo,
      Nat.factorization_eq_zero_of_not_dvd hthree, h626]
  have h313 : 313 ∈ m.primeFactors := by
    apply (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hmpos)).mpr
    refine ⟨prime313, ?_⟩
    rw [hshape]
    exact (by norm_num : 313 ∣ 626).trans (dvd_mul_of_dvd_left (dvd_mul_left 626 _) _)
  have hsupport : ∀ q : ℕ, q.Prime → q ∣ sigma m →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = p := by
    intro q hq hd
    rw [hreverse, hn] at hd
    exact prime_dvd_twice_shape a j ell p q hp hq hd
  have hB1 : m.factorization 313 = 1 := by
    by_contra hne
    have hBgt : 1 < m.factorization 313 := by omega
    have hvalpos : 0 < (1 + p ^ (2 ^ ell)).factorization 313 := by omega
    have hpdvd : 313 ∣ p ^ (2 ^ ell) + 1 := by
      have hdiv := Nat.dvd_of_factorization_pos (ne_of_gt hvalpos)
      simpa only [Nat.add_comm] using hdiv
    have hp8 := pow_eight_eq_one_of_313_dvd p ell hpdvd
    obtain ⟨h, hh, hhpos⟩ := higher_bit_of_one_lt (m.factorization 313) hBgt
    have hslot := slot_dvd_sigma m 313 h h313 hh
    apply reverse_high_impossible p h hhpos hp8
    intro q hq hd
    exact hsupport q hq (hd.trans (by simpa only [Nat.add_comm] using hslot))
  refine ⟨hB1, ?_⟩
  have hbit : 0 ∈ binarySupport (m.factorization 313) := by
    rw [hB1]
    decide
  have hslot := slot_dvd_sigma m 313 0 h313 hbit
  have h157 : 157 ∣ sigma m := (by norm_num : 157 ∣ 1 + 313 ^ (2 ^ 0)).trans hslot
  have hs := hsupport 157 (by norm_num) h157
  rcases hs with h | h | h | h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · exact h.symm

example : 313 ∣ (5 : ℕ) ^ (2 ^ 2) + 1 := by norm_num

example : (5 : ZMod 313) ^ 8 = 1 := by decide

example : 2 ≤ (2 : ℕ) ∧ Even (2 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
    Nat.Prime 7 ∧ (7 : ℕ) ≠ 2 ∧ (7 : ℕ) ≠ 3 ∧ (7 : ℕ) ≠ 5 ∧
    (1102500 : ℕ) = 2 ^ 2 * 3 ^ (2 ^ 1) * 5 ^ 4 * 7 ^ (2 ^ 1) ∧
    (1565000 : ℕ) = sigma 1102500 := by
  have hf := sigma_shape 2 1 1 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hlocal : localSigma 2 2 = 5 := by decide
  norm_num [hlocal] at hf
  exact ⟨by norm_num, by decide, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, hf.symm⟩

end InfinitarySuperperfect
