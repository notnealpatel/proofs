import Erdos.EUnitaryP1TwelveObstruction
set_option autoImplicit false
namespace EUnitaryP1

/-- For every even exponent at least two, 230 divides the local base-229 factor. Complementary unitary exponent divisors have opposite parity and cancel modulo 230. -/
theorem dvd_localA_229_of_even (c : ℕ) (hc : 2 ≤ c) (he : Even c) : 230 ∣ localA 229 c := by
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
      (229 : ZMod 230)^(d-1) + (229 : ZMod 230)^(c/d-1) = 0 := by
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
    rw [show (229 : ZMod 230) = -1 by decide]
    rcases hpar with hh | hh
    · rw [hh.1.neg_one_pow, hh.2.neg_one_pow]; ring
    · rw [hh.1.neg_one_pow, hh.2.neg_one_pow]; ring
  have hs : (∑ d ∈ exponentDivisors c, (229 : ZMod 230)^(d-1)) = 0 := by
    apply Finset.sum_involution (fun d _ => c / d)
    · exact hpair
    · intro d hd _; exact hnf d hd
    · exact hm
    · intro d hd; exact Nat.div_div_self (exponentDivisors_mem hd).2.1 hz
  apply (ZMod.natCast_eq_zero_iff (localA 229 c) 230).mp
  simpa only [localA, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using hs

example : 230 ∣ localA 229 2 := dvd_localA_229_of_even 2 (by decide) (by decide)

private theorem geom229 (m : ℕ) : 228 * (∑ i ∈ Finset.range m, 229^i) + 1 = 229^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- For every exponent at least two, the local base-229 factor is at most 230 times 229 raised to the exponent minus two. -/
theorem localA_229_le (c : ℕ) (hc : 2 ≤ c) : localA 229 c ≤ 230 * 229^(c-2) := by
  by_cases he : c = 2
  · subst c; rw [localA_two]; norm_num
  have hc3 : 3 ≤ c := by omega
  let T := (exponentDivisors c).erase c
  have hcp : 0 < c := by omega
  have hcmem : c ∈ exponentDivisors c := by
    simp [exponentDivisors, Nat.mem_divisors, Nat.ne_of_gt hcp, Nat.div_self hcp]
  have hdpos (d : ℕ) (hd : d ∈ T) : 0 < d :=
    (exponentDivisors_mem (Finset.mem_erase.mp hd).2).1
  have hdle (d : ℕ) (hd : d ∈ T) : d ≤ c-2 := by
    have hne := (Finset.mem_erase.mp hd).1
    have hdiv := (exponentDivisors_mem (Finset.mem_erase.mp hd).2).2.1
    have hmul := Nat.mul_div_cancel' hdiv
    have hquotpos : 0 < c/d := Nat.div_pos (Nat.le_of_dvd hcp hdiv) (hdpos d hd)
    have hquot : 2 ≤ c/d := by
      by_contra hn
      have hq : c/d = 1 := by omega
      rw [hq, Nat.mul_one] at hmul
      exact hne hmul
    have htwod := (Nat.mul_le_mul_left d hquot).trans_eq hmul
    omega
  have himage : T.image (fun d => d-1) ⊆ Finset.range (c-2) := by
    intro i hi
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (by have hp := hdpos d hd; have hl := hdle d hd; omega)
  have hinj : Set.InjOn (fun d : ℕ => d-1) T := by
    intro d hd e he hde
    have hp := hdpos d hd
    have hq := hdpos e he
    dsimp only at hde
    omega
  have hsum : (∑ d ∈ T, 229^(d-1)) ≤ ∑ i ∈ Finset.range (c-2), 229^i := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset himage
  have hsplit : localA 229 c = (∑ d ∈ T, 229^(d-1)) + 229^(c-1) := by
    exact (Finset.sum_erase_add (exponentDivisors c) (fun d => 229^(d-1)) hcmem).symm
  have hgeom := geom229 (c-2)
  have hpow : 229^(c-1) = 229 * 229^(c-2) := by
    have he : c-1 = (c-2)+1 := by omega
    rw [he, pow_succ, Nat.mul_comm]
  omega

example : localA 229 2 ≤ 230 * 229^(2-2) := localA_229_le 2 (by decide)

private theorem force_prime (b c : ℕ) (S : Finset ℕ) (_hb : 0 < b) (_hc : 0 < c)
    (hS : ∀ q ∈ S, q.Prime) (p : ℕ) (hp : p.Prime)
    (h2 : p ≠ 2) (h3 : p ≠ 3) (h229 : p ≠ 229)
    (hid : 2061 * localA 3 b * localA 229 c * (∏ q ∈ S, (q+1)) =
      2^12 * 3^(b-1) * 229^(c-1) * (∏ q ∈ S, q))
    (hd : p ∣ 2061 * localA 3 b * localA 229 c * (∏ q ∈ S, (q+1))) : p ∈ S := by
  rw [hid] at hd
  have hn (r a : ℕ) (hr : r.Prime) (hne : p ≠ r) : ¬ p ∣ r^a := by
    intro hh
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hh))
  have hprod : p ∣ ∏ q ∈ S, q := by
    rcases hp.dvd_mul.mp hd with hh | hh
    · rcases hp.dvd_mul.mp hh with hh | hh
      · rcases hp.dvd_mul.mp hh with hh | hh
        · exact False.elim (hn 2 12 (by decide) h2 hh)
        · exact False.elim (hn 3 (b-1) (by decide) h3 hh)
      · exact False.elim (hn 229 (c-1) (by norm_num) h229 hh)
    · exact hh
  exact prime_mem_of_dvd_prod hp S hS hprod

private theorem split_two (S : Finset ℕ) (h5 : 5 ∈ S) (h23 : 23 ∈ S) :
    (∏ q ∈ S, (q+1)) = 144 * (∏ q ∈ S \ {5,23}, (q+1)) ∧
    (∏ q ∈ S, q) = 115 * (∏ q ∈ S \ {5,23}, q) := by
  have hsub : ({5,23} : Finset ℕ) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact h5
    · exact h23
  constructor
  · have hh := Finset.prod_sdiff (f := fun q : ℕ => q+1) hsub
    norm_num [Finset.prod_insert, Finset.prod_singleton] at hh
    simpa only [Nat.mul_comm] using hh.symm
  · have hh := Finset.prod_sdiff (f := fun q : ℕ => q) hsub
    norm_num [Finset.prod_insert, Finset.prod_singleton] at hh
    simpa only [Nat.mul_comm] using hh.symm

private theorem five_le (b c : ℕ) (S : Finset ℕ) (hb : 0 < b) (_hc : 0 < c)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 3) (h5 : 5 ∈ S) (h23 : 23 ∈ S)
    (hid : 2061 * localA 3 b * localA 229 c * (∏ q ∈ S, (q+1)) =
      2^12 * 3^(b-1) * 229^(c-1) * (∏ q ∈ S, q)) : 5 ≤ b := by
  have hs := split_two S h5 h23
  have h81 : 81 ∣ 2061 * localA 3 b * localA 229 c * (∏ q ∈ S, (q+1)) := by
    rw [hs.1]
    refine ⟨3664 * localA 3 b * localA 229 c * (∏ q ∈ S \ {5,23}, (q+1)), ?_⟩
    ring
  rw [hid] at h81
  have h3prod : Nat.Coprime 3 (∏ q ∈ S, q) := by
    apply (show Nat.Prime 3 from by decide).coprime_iff_not_dvd.mpr
    intro hd
    exact (hS 3 (prime_mem_of_dvd_prod (by decide) S (fun q hq => (hS q hq).1) hd)).2 rfl
  have hco : Nat.Coprime 81 (2^12 * 229^(c-1) * (∏ q ∈ S, q)) := by
    exact (((show Nat.Coprime 3 2 from by decide).pow_right 12).mul_right
      ((show Nat.Coprime 3 229 from by decide).pow_right (c-1))).mul_right h3prod |>.pow_left 4
  have hpower : 81 ∣ 3^(b-1) := by
    apply hco.dvd_of_dvd_mul_right
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h81
  have hle : 4 ≤ b-1 := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 3)).mp hpower
  omega

private theorem residual (b c k : ℕ) (S : Finset ℕ) (hb : 5 ≤ b) (hc : 2 ≤ c)
    (hk : localA 229 c = 230*k) (h5 : 5 ∈ S) (h23 : 23 ∈ S)
    (hid : 2061 * localA 3 b * localA 229 c * (∏ q ∈ S, (q+1)) =
      2^12 * 3^(b-1) * 229^(c-1) * (∏ q ∈ S, q)) :
    localA 3 b * k * (∏ q ∈ S \ {5,23}, (q+1)) =
      128 * 3^(b-5) * 229^(c-2) * (∏ q ∈ S \ {5,23}, q) := by
  have hs := split_two S h5 h23
  have hpow3 : 3^(b-1) = 81 * 3^(b-5) := by
    have he : b-1 = 4+(b-5) := by omega
    rw [he, pow_add]; norm_num
  have hpow229 : 229^(c-1) = 229 * 229^(c-2) := by
    have he : c-1 = 1+(c-2) := by omega
    rw [he, pow_add]; norm_num
  rw [hk, hs.1, hs.2, hpow3, hpow229] at hid
  ring_nf at hid ⊢
  omega

/-- For all positive base-three exponents and all even base-229 exponents at least two, the normalized exponent-twelve perfectness identity is impossible on any finite support of primes excluding two, three, and 229. No support-size or valuation certificate is assumed. -/
theorem normalized_229_ne_of_even (b c : ℕ) (S : Finset ℕ) (hb : 0 < b) (hc : 2 ≤ c) (he : Even c)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229) :
    2061 * localA 3 b * localA 229 c * (∏ q ∈ S, (q+1)) ≠
      2^12 * 3^(b-1) * 229^(c-1) * (∏ q ∈ S, q) := by
  intro hid
  have hcore := dvd_localA_229_of_even c hc he
  have h230 : 230 ∣ 2061 * localA 3 b * localA 229 c * (∏ q ∈ S, (q+1)) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hcore _) _
  have h5 : 5 ∈ S := force_prime b c S hb (by omega) (fun q hq => (hS q hq).1) 5 (by decide)
    (by decide) (by decide) (by decide) hid ((by decide : 5 ∣ 230).trans h230)
  have h23 : 23 ∈ S := force_prime b c S hb (by omega) (fun q hq => (hS q hq).1) 23 (by decide)
    (by decide) (by decide) (by decide) hid ((by decide : 23 ∣ 230).trans h230)
  have hb5 := five_le b c S hb (by omega) (fun q hq => ⟨(hS q hq).1,(hS q hq).2.2.1⟩) h5 h23 hid
  obtain ⟨k,hk⟩ := hcore
  have hkbound : k ≤ 229^(c-2) := by
    have hh := localA_229_le c hc
    rw [hk] at hh
    omega
  let U := S \ {5,23}
  let A := localA 3 b
  let P := ∏ q ∈ U, (q+1)
  let B := ∏ q ∈ U, q
  let Z := 3^(b-5)
  let W := 229^(c-2)
  have hr : A*k*P = 128*Z*W*B := residual b c k S hb5 hc hk h5 h23 hid
  have hU : ∀ q ∈ U, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 23 := by
    intro q hq
    have hs := hS q (Finset.mem_sdiff.mp hq).1
    have hn := (Finset.mem_sdiff.mp hq).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    exact ⟨hs.1,hs.2.1,hs.2.2.1,hn.1,hn.2⟩
  have hB : 0 < B := Finset.prod_pos (fun q hq => (hU q hq).1.pos)
  have hW : 0 < W := pow_pos (by decide) _
  have hco : Nat.Coprime 2 (Z*W*B) := by
    have h2B : Nat.Coprime 2 B := by
      apply (show Nat.Prime 2 from by decide).coprime_iff_not_dvd.mpr
      intro hd
      exact (hU 2 (prime_mem_of_dvd_prod (by decide) U (fun q hq => (hU q hq).1) hd)).2.1 rfl
    exact (((show Nat.Coprime 2 3 from by decide).pow_right (b-5)).mul_right
      ((show Nat.Coprime 2 229 from by decide).pow_right (c-2))).mul_right h2B
  have hcard : U.card ≤ 6 := by
    have hp : 2^U.card ∣ P := by
      have hh := Finset.prod_dvd_prod_of_dvd (fun _ : ℕ => 2) (fun q => q+1) (s := U) ?_
      · simpa [P] using hh
      · intro q hq
        have ho := (hU q hq).1.eq_two_or_odd.resolve_left (hU q hq).2.1
        exact Nat.dvd_of_mod_eq_zero (by omega)
    have hd : 2^(U.card+1) ∣ A*k*P := by
      have hh := Nat.mul_dvd_mul (localA_three_even b (by omega)) hp
      simpa only [A, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        dvd_mul_of_dvd_left hh k
    rw [hr] at hd
    have hd128 : 2^(U.card+1) ∣ 2^7 := by
      apply (hco.pow_left (U.card+1)).dvd_of_dvd_mul_right
      simpa only [Nat.mul_assoc, show (2:ℕ)^7 = 128 by decide] using hd
    have hh := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hd128
    omega
  have henv := residual_ratio_le U hU hcard
  have hrat : (∏ q ∈ U, ((q:ℚ)+1)/q) = (P:ℚ)/(B:ℚ) := by
    simp only [P,B,Finset.prod_div_distrib,Nat.cast_prod,Nat.cast_add,Nat.cast_one]
  rw [hrat] at henv
  have hBq : (0:ℚ) < B := by exact_mod_cast hB
  have heq : (1339481:ℚ)*P ≤ 2073600*B := by
    have hh := (div_le_iff₀ hBq).mp henv
    linarith
  have hen : 1339481*P ≤ 2073600*B := by exact_mod_cast heq
  have hlower : 128*Z*B ≤ A*P := by
    have hh := Nat.mul_le_mul_right P (Nat.mul_le_mul_left A hkbound)
    have hmul : W*(128*Z*B) ≤ W*(A*P) := by
      calc
        W*(128*Z*B) = A*k*P := by rw [hr]; ring
        _ ≤ A*W*P := hh
        _ = W*(A*P) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hW
  by_cases hseven : 7 ≤ b
  · have ht := localA_three_tail_lt b hseven
    have he : b-1 = (b-5)+4 := by omega
    have hpow : 3^(b-1) = Z*81 := by rw [he,pow_add]; rfl
    rw [hpow] at ht
    change 54*A < 55*(Z*81) at ht
    have hmul := Nat.mul_le_mul_left A hen
    have hstrict := Nat.mul_lt_mul_of_pos_right ht hB
    nlinarith [hmul,hstrict,hlower]
  · have hboundary : b = 5 ∨ b = 6 := by omega
    rcases hboundary with rfl | rfl
    · norm_num [A,Z,localA_three_five] at hlower
      nlinarith [hen,hB]
    · have hd : 2^8 ∣ 128*(Z*W*B) := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← hr]
        change 256 ∣ localA 3 6 * k * P
        rw [localA_three_six]
        exact dvd_mul_of_dvd_left (dvd_mul_right 256 k) P
      have hh := (hco.pow_left 8).dvd_of_dvd_mul_right hd
      norm_num at hh

example : (0 < (1:ℕ)) ∧ (2 ≤ (2:ℕ)) ∧ Even (2:ℕ) ∧
    (∀ q ∈ (∅ : Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229) := by
  simp
example : 2061 * localA 3 1 * localA 229 2 * (∏ q ∈ (∅ : Finset ℕ), (q+1)) ≠
    2^12 * 3^(1-1) * 229^(2-1) * (∏ q ∈ (∅ : Finset ℕ), q) :=
  normalized_229_ne_of_even 1 2 ∅ (by decide) (by decide) (by decide) (by simp)

/-- The actual exponential-unitary sum factors on the exponent-twelve family with a separate positive base-229 exponent, distinct remaining prime squares, and a positive coprime squarefree decoration. -/
theorem sigmaEU_twelve_229_class_eq (b c t : ℕ) (S : Finset ℕ) (hb : 0 < b) (hc : 0 < c) (ht : 0 < t)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229)
    (hsq : Squarefree t) (htc : Nat.Coprime t (6*229*(∏ q ∈ S, q))) :
    sigmaEU (t*2^12*3^b*229^c*(∏ q ∈ S, q^2)) =
      t*(2*2061)*(3*localA 3 b)*(229*localA 229 c)*(∏ q ∈ S, q*(q+1)) := by
  let N := t*2^12*3^b*(∏ q ∈ S, q^2)
  have htc' : Nat.Coprime t ((6*(∏ q ∈ S, q))*229) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htc
  have ht229 := (Nat.coprime_mul_iff_right.mp htc').2
  have hbase := (Nat.coprime_mul_iff_right.mp htc').1
  have hq229 (q : ℕ) (hq : q ∈ S) : Nat.Coprime q 229 := by
    apply (hS q hq).1.coprime_iff_not_dvd.mpr
    intro hd
    exact (hS q hq).2.2.2 ((Nat.prime_dvd_prime_iff_eq (hS q hq).1 (by norm_num)).mp hd)
  have hN : Nat.Coprime N 229 :=
    ((ht229.mul_left ((show Nat.Coprime 2 229 from by decide).pow_left 12)).mul_left
      ((show Nat.Coprime 3 229 from by decide).pow_left b)).mul_left
      (Nat.coprime_prod_left_iff.mpr (fun q hq => (hq229 q hq).pow_left 2))
  have hNpos : 0 < N := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ht (by positivity))
    (by positivity)) (Finset.prod_pos (fun q hq => pow_pos (hS q hq).1.pos _))
  have heq : t*2^12*3^b*229^c*(∏ q ∈ S, q^2) = N*229^c := by dsimp [N]; ring
  rw [heq, sigmaEU_mul_of_coprime N (229^c) hNpos (by positivity) (hN.pow_right c)]
  dsimp only [N]
  rw [sigmaEU_twelve_class_eq b t S hb ht
    (fun q hq => ⟨(hS q hq).1,(hS q hq).2.1,(hS q hq).2.2.1⟩) hsq hbase,
    sigmaEU_prime_pow 229 c (by norm_num) hc]
  ring

/-- No member of the exponent-twelve family with a positive base-three exponent, an even base-229 exponent at least two, distinct remaining prime squares, and a positive coprime squarefree decoration is exponential-unitary perfect. -/
theorem sigmaEU_twelve_229_class_ne_of_even (b c t : ℕ) (S : Finset ℕ) (hb : 0 < b) (hc : 2 ≤ c) (he : Even c)
    (ht : 0 < t) (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229)
    (hsq : Squarefree t) (htc : Nat.Coprime t (6*229*(∏ q ∈ S, q))) :
    sigmaEU (t*2^12*3^b*229^c*(∏ q ∈ S, q^2)) ≠
      2*(t*2^12*3^b*229^c*(∏ q ∈ S, q^2)) := by
  intro hid
  let D := t*2*3*229*(∏ q ∈ S, q)
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ht (by decide))
    (by decide)) (by decide)) (Finset.prod_pos (fun q hq => (hS q hq).1.pos))
  have hp3 : 3^b = 3*3^(b-1) := by
    rw [← pow_succ']; congr 1; omega
  have hp229 : 229^c = 229*229^(c-1) := by
    rw [← pow_succ']; congr 1; omega
  have hi : D*(2061*localA 3 b*localA 229 c*(∏ q ∈ S, (q+1))) =
      D*(2^12*3^(b-1)*229^(c-1)*(∏ q ∈ S, q)) := by
    calc
      D*(2061*localA 3 b*localA 229 c*(∏ q ∈ S, (q+1))) =
          sigmaEU (t*2^12*3^b*229^c*(∏ q ∈ S, q^2)) := by
        rw [sigmaEU_twelve_229_class_eq b c t S hb (by omega) ht hS hsq htc, Finset.prod_mul_distrib]
        dsimp [D]; ring
      _ = 2*(t*2^12*3^b*229^c*(∏ q ∈ S, q^2)) := hid
      _ = D*(2^12*3^(b-1)*229^(c-1)*(∏ q ∈ S, q)) := by
        rw [hp3,hp229,Finset.prod_pow]
        dsimp [D]; ring
  exact normalized_229_ne_of_even b c S hb hc he hS (Nat.eq_of_mul_eq_mul_left hD hi)

example : (0 < (1:ℕ)) ∧ (2 ≤ (2:ℕ)) ∧ Even (2:ℕ) ∧ (0 < (1:ℕ)) ∧
    (∀ q ∈ (∅ : Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229) ∧
    Squarefree (1:ℕ) ∧ Nat.Coprime 1 (6*229*(∏ q ∈ (∅ : Finset ℕ), q)) := by
  norm_num
example : sigmaEU (1*2^12*3^1*229^2*(∏ q ∈ (∅ : Finset ℕ), q^2)) ≠
    2*(1*2^12*3^1*229^2*(∏ q ∈ (∅ : Finset ℕ), q^2)) :=
  sigmaEU_twelve_229_class_ne_of_even 1 2 1 ∅ (by decide) (by decide) (by decide) (by decide) (by simp) (by norm_num) (by norm_num)

example : (0 < (1:ℕ)) ∧ (2 ≤ (4:ℕ)) ∧ Even (4:ℕ) ∧ (0 < (7:ℕ)) ∧
    (∀ q ∈ ({5} : Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229) ∧
    Squarefree (7:ℕ) ∧ Nat.Coprime 7 (6*229*(∏ q ∈ ({5} : Finset ℕ), q)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · norm_num
  · exact (by decide : Nat.Prime 7).squarefree
  · norm_num ; decide

example : sigmaEU (7*2^12*3^1*229^4*(∏ q ∈ ({5} : Finset ℕ), q^2)) ≠
    2*(7*2^12*3^1*229^4*(∏ q ∈ ({5} : Finset ℕ), q^2)) := by
  apply sigmaEU_twelve_229_class_ne_of_even 1 4 7 {5}
    (by decide) (by decide) (by decide) (by decide) (by norm_num)
  · exact (by decide : Nat.Prime 7).squarefree
  · norm_num ; decide

end EUnitaryP1
