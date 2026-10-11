import Erdos.InfinitarySuperperfect

set_option autoImplicit false

namespace InfinitarySuperperfect

/-- An odd square successor has exactly one factor of two. -/
theorem factorization_two_sq_add_one (x : ℕ) (hx : x % 2 = 1) :
    (1 + x ^ 2).factorization 2 = 1 := by
  have hx4 : x % 4 = 1 ∨ x % 4 = 3 := Nat.odd_mod_four_iff.mp hx
  have hmod : (1 + x ^ 2) % 4 = 2 := by
    rcases hx4 with h | h <;> norm_num [Nat.add_mod, Nat.pow_mod, h]
  have hpos : 1 + x ^ 2 ≠ 0 := by positivity
  have htwo : 2 ∣ 1 + x ^ 2 := by omega
  have hlo : 1 ≤ (1 + x ^ 2).factorization 2 := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hpos).mp
    simpa using htwo
  have hhi : ¬ 2 ≤ (1 + x ^ 2).factorization 2 := by
    intro h
    have hfour := (Nat.Prime.pow_dvd_iff_le_factorization
      (by decide : Nat.Prime 2) hpos).mpr h
    have hz : (1 + x ^ 2) % 4 = 0 := Nat.mod_eq_zero_of_dvd hfour
    omega
  omega

example : (1 + (3 : ℕ) ^ 2).factorization 2 = 1 :=
  factorization_two_sq_add_one 3 (by decide)

/-- A higher occupied bit at an odd base contributes exactly one factor of two. -/
theorem factorization_two_higher_slot (p j : ℕ) (hp : p % 2 = 1) :
    (1 + p ^ (2 ^ (j + 1))).factorization 2 = 1 := by
  rw [Nat.pow_succ, pow_mul]
  apply factorization_two_sq_add_one
  simp [Nat.pow_mod, hp]

example : (1 + (3 : ℕ) ^ (2 ^ (0 + 1))).factorization 2 = 1 :=
  factorization_two_higher_slot 3 0 (by decide)

/-- At an odd base with even exponent, the two-adic valuation is the number
of occupied binary positions. -/
theorem factorization_localSigma_two_of_odd_of_even (p e : ℕ)
    (hp : p % 2 = 1) (he : Even e) :
    (localSigma p e).factorization 2 = (binarySupport e).card := by
  unfold localSigma
  have hslots : ∀ j ∈ binarySupport e, (1 : ℕ) + p ^ (2 ^ j) ≠ 0 := by
    intro j hj
    positivity
  rw [Nat.factorization_prod hslots, Finsupp.finsetSum_apply]
  have hval : ∀ j ∈ binarySupport e, (1 + p ^ (2 ^ j)).factorization 2 = 1 := by
    intro j hj
    have hjpos := one_le_of_mem_binarySupport_of_even e j he hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact factorization_two_higher_slot p k hp
  simp [Finset.sum_congr rfl hval]

example : (localSigma 3 6).factorization 2 = (binarySupport 6).card :=
  factorization_localSigma_two_of_odd_of_even 3 6 (by decide) (by decide)

/-- All successor factors at base two are odd, so their product has no factor two. -/
theorem factorization_localSigma_two_two (e : ℕ) :
    (localSigma 2 e).factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdiv
  obtain ⟨j, hj, hslot⟩ := ((by decide : Nat.Prime 2).prime.dvd_finsetProd_iff
    (fun j => 1 + 2 ^ (2 ^ j))).mp hdiv
  have hpow : 2 ∣ 2 ^ (2 ^ j) := dvd_pow_self 2 (by positivity : 2 ^ j ≠ 0)
  have hbad : 2 ∣ 1 := (Nat.dvd_add_iff_left hpow).mpr hslot
  norm_num at hbad

example : (localSigma 2 6).factorization 2 = 0 :=
  factorization_localSigma_two_two 6

/-- For a positive square input, the exact two-adic budget of the canonical
infinitary sum is the total number of occupied bits at its actual odd primes. -/
theorem factorization_sigma_two_of_isSquare (n : ℕ) (hn : 0 < n)
    (hsquare : IsSquare n) :
    (sigma n).factorization 2 =
      ∑ p ∈ n.primeFactors, if p = 2 then 0 else (binarySupport (n.factorization p)).card := by
  have he := (isSquare_iff_even_factorization n hn).mp hsquare
  unfold sigma
  have hlocal : ∀ p ∈ n.primeFactors, localSigma p (n.factorization p) ≠ 0 := by
    intro p hp
    exact ne_of_gt (localSigma_pos p (n.factorization p))
  rw [Nat.factorization_prod hlocal, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    simp [factorization_localSigma_two_two]
  · have hprime := ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mp hp).1
    simp only [hp2, if_false]
    exact factorization_localSigma_two_of_odd_of_even p (n.factorization p)
      (hprime.eq_two_or_odd.resolve_left hp2) (he p)

example : 0 < (9 : ℕ) ∧ IsSquare (9 : ℕ) :=
  ⟨by decide, ⟨3, rfl⟩⟩
example : (sigma 9).factorization 2 =
    ∑ p ∈ (9 : ℕ).primeFactors,
      if p = 2 then 0 else (binarySupport ((9 : ℕ).factorization p)).card :=
  factorization_sigma_two_of_isSquare 9 (by decide) ⟨3, rfl⟩

/-- Valuation one on the forward sum of a positive square forces a unique
actual odd prime in the input, with a single higher binary exponent bit. -/
theorem exists_unique_odd_prime_bit_of_factorization_sigma_two_eq_one
    (n : ℕ) (hn : 0 < n) (hsquare : IsSquare n)
    (hf : (sigma n).factorization 2 = 1) :
    ∃ p j : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ n.primeFactors ∧ 1 ≤ j ∧
      n.factorization p = 2 ^ j ∧
      ∀ q ∈ n.primeFactors, q ≠ 2 → q ≠ p → n.factorization q = 0 := by
  let f : ℕ → ℕ := fun p => if p = 2 then 0 else (binarySupport (n.factorization p)).card
  have hsum : ∑ p ∈ n.primeFactors, f p = 1 := by
    rw [← hf]
    exact (factorization_sigma_two_of_isSquare n hn hsquare).symm
  obtain ⟨p, hp, hfp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega :
    (∑ p ∈ n.primeFactors, f p) ≠ 0)
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    simp [f] at hfp
  have hfle : f p ≤ 1 := by
    calc
      f p ≤ ∑ q ∈ n.primeFactors, f q :=
        Finset.single_le_sum (fun q hq => Nat.zero_le (f q)) hp
      _ = 1 := hsum
  have hfone : f p = 1 := by omega
  have hcard : (binarySupport (n.factorization p)).card = 1 := by
    simpa only [f, hp2, if_false] using hfone
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjmem : j ∈ binarySupport (n.factorization p) := by simp [hj]
  have hjpos : 1 ≤ j := one_le_of_mem_binarySupport_of_even _ _
    ((isSquare_iff_even_factorization n hn).mp hsquare p) hjmem
  have he : n.factorization p = 2 ^ j := by
    have hbits := sum_binarySupport (n.factorization p)
    simpa [hj] using hbits.symm
  have herase : ∑ q ∈ n.primeFactors.erase p, f q = 0 := by
    have hsplit := Finset.sum_erase_add n.primeFactors f hp
    omega
  refine ⟨p, j, ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mp hp).1,
    hp2, hp, hjpos, he, ?_⟩
  intro q hq hq2 hqp
  have hqerase : q ∈ n.primeFactors.erase p := Finset.mem_erase.mpr ⟨hqp, hq⟩
  have hfqle : f q ≤ 0 := by
    calc
      f q ≤ ∑ r ∈ n.primeFactors.erase p, f r :=
        Finset.single_le_sum (fun r hr => Nat.zero_le (f r)) hqerase
      _ = 0 := herase
  have hqcard : (binarySupport (n.factorization q)).card = 0 := by
    simpa only [f, hq2, if_false] using Nat.eq_zero_of_le_zero hfqle
  have hempty := Finset.card_eq_zero.mp hqcard
  have hbits := sum_binarySupport (n.factorization q)
  simpa [hempty] using hbits.symm

example : 0 < (9 : ℕ) ∧ IsSquare (9 : ℕ) ∧ (sigma 9).factorization 2 = 1 := by
  refine ⟨by decide, ⟨3, rfl⟩, ?_⟩
  rw [factorization_sigma_two_of_isSquare 9 (by decide) ⟨3, rfl⟩]
  have hnine : (9 : ℕ) = 3 ^ 2 := by decide
  rw [hnine, Nat.primeFactors_prime_pow (by decide : (2 : ℕ) ≠ 0)
    (by decide : Nat.Prime 3), Nat.Prime.factorization_pow (by decide : Nat.Prime 3)]
  norm_num [binarySupport]
  decide

/-- An actual local successor factor divides the canonical global sum. -/
theorem slot_dvd_sigma (n p j : ℕ) (hp : p ∈ n.primeFactors)
    (hj : j ∈ binarySupport (n.factorization p)) :
    1 + p ^ (2 ^ j) ∣ sigma n := by
  exact (Finset.dvd_prod_of_mem (fun j => 1 + p ^ (2 ^ j)) hj).trans
    (Finset.dvd_prod_of_mem (fun p => localSigma p (n.factorization p)) hp)

example : 1 + (3 : ℕ) ^ (2 ^ 1) ∣ sigma 9 := by
  apply slot_dvd_sigma
  · rw [show (9 : ℕ) = 3 ^ 2 by decide,
      Nat.primeFactors_prime_pow (by decide : (2 : ℕ) ≠ 0) (by decide : Nat.Prime 3)]
    simp
  · rw [show (9 : ℕ) = 3 ^ 2 by decide,
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3)]
    norm_num [binarySupport]
    decide

/-- Valuation one at two puts the local factor three into the global sum. -/
theorem three_dvd_sigma_of_factorization_two_eq_one (m : ℕ) (hm : 0 < m)
    (hf : m.factorization 2 = 1) : 3 ∣ sigma m := by
  have hdvd : 2 ∣ m := by
    change 2 ^ 1 ∣ m
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2)
      (ne_of_gt hm)).mpr (by omega)
  have hp : 2 ∈ m.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hm)).mpr ⟨by decide, hdvd⟩
  have hj : 0 ∈ binarySupport (m.factorization 2) := by rw [hf]; decide
  simpa using slot_dvd_sigma m 2 0 hp hj

example : 0 < (2 : ℕ) ∧ (2 : ℕ).factorization 2 = 1 := by norm_num

/-- If every actual odd prime except `p` has zero valuation, prime factorization
reconstructs the integer from its two-primary and `p`-primary factors. -/
theorem eq_two_pow_mul_prime_pow_of_odd_support (n p : ℕ) (hn : 0 < n)
    (_hp : p.Prime) (hp2 : p ≠ 2)
    (hother : ∀ q ∈ n.primeFactors, q ≠ 2 → q ≠ p → n.factorization q = 0) :
    n = 2 ^ (n.factorization 2) * p ^ (n.factorization p) := by
  have hsubset : n.primeFactors ⊆ {2, p} := by
    intro q hq
    by_cases hq2 : q = 2
    · simp [hq2]
    by_cases hqp : q = p
    · simp [hqp]
    have hqdata := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mp hq
    have hqpos := hqdata.1.factorization_pos_of_dvd (ne_of_gt hn) hqdata.2
    have hqzero := hother q hq hq2 hqp
    omega
  have hprod : (∏ q ∈ n.primeFactors, q ^ n.factorization q) =
      ∏ q ∈ ({2, p} : Finset ℕ), q ^ n.factorization q := by
    apply Finset.prod_subset hsubset
    intro q hq hnot
    have hzero : n.factorization q = 0 := by
      apply (Nat.factorization_eq_zero_iff n q).mpr
      by_cases hprime : q.Prime
      · right; left
        intro hdvd
        exact hnot ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr ⟨hprime, hdvd⟩)
      · exact Or.inl hprime
    simp [hzero]
  calc
    n = ∏ q ∈ n.primeFactors, q ^ n.factorization q :=
      Nat.prod_primeFactors_pow_factorization (ne_of_gt hn)
    _ = ∏ q ∈ ({2, p} : Finset ℕ), q ^ n.factorization q := hprod
    _ = 2 ^ (n.factorization 2) * p ^ (n.factorization p) := by simp [Ne.symm hp2]

example : 0 < (18 : ℕ) ∧ Nat.Prime 3 ∧ (3 : ℕ) ≠ 2 ∧
    (∀ q ∈ (18 : ℕ).primeFactors, q ≠ 2 → q ≠ 3 → (18 : ℕ).factorization q = 0) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro q hq hq2 hq3
  have hqdata := (Nat.mem_primeFactors_of_ne_zero (by decide : (18 : ℕ) ≠ 0)).mp hq
  have hdvd : q ∣ 2 * 3 ^ 2 := by simpa using hqdata.2
  rcases hqdata.1.dvd_mul.mp hdvd with htwo | hthree
  · have heq := (by decide : Nat.Prime 2).eq_one_or_self_of_dvd q htwo
    rcases heq with heq | heq
    · subst q; norm_num
    · exact (hq2 heq).elim
  · have hbase := hqdata.1.dvd_of_dvd_pow hthree
    have heq := (by decide : Nat.Prime 3).eq_one_or_self_of_dvd q hbase
    rcases heq with heq | heq
    · subst q; norm_num
    · exact (hq3 heq).elim

/-- Under the valuation-one branch and the actual cycle equations, the unique
odd input prime is three, with exponent a single higher binary bit. -/
theorem exists_three_bit_of_square_cycle_factorization_two_eq_one
    (n m : ℕ) (hn : 0 < n) (hsquare : IsSquare n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n) (hf : m.factorization 2 = 1) :
    ∃ j : ℕ, 1 ≤ j ∧ n.factorization 3 = 2 ^ j ∧
      n = 2 ^ (n.factorization 2) * 3 ^ (2 ^ j) := by
  have hforward : (sigma n).factorization 2 = 1 := by rw [← hm]; exact hf
  obtain ⟨p, j, hp, hp2, hpn, hj, he, hother⟩ :=
    exists_unique_odd_prime_bit_of_factorization_sigma_two_eq_one n hn hsquare hforward
  have hrepr := eq_two_pow_mul_prime_pow_of_odd_support n p hn hp hp2 hother
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hthree : 3 ∣ 2 * n := by
    rw [← hcycle]
    exact three_dvd_sigma_of_factorization_two_eq_one m hmpos hf
  have hthreeN : 3 ∣ n := ((by decide : Nat.Prime 3).dvd_mul.mp hthree).resolve_left (by decide)
  have hthreeP : 3 ∣ p := by
    rw [hrepr] at hthreeN
    have hnot : ¬ 3 ∣ 2 ^ n.factorization 2 := by
      intro h
      have hbad := (by decide : Nat.Prime 3).dvd_of_dvd_pow h
      norm_num at hbad
    exact (by decide : Nat.Prime 3).dvd_of_dvd_pow
      (((by decide : Nat.Prime 3).dvd_mul.mp hthreeN).resolve_left hnot)
  have hp3 : p = 3 := by
    rcases hp.eq_one_or_self_of_dvd 3 hthreeP with h | h
    · norm_num at h
    · exact h.symm
  subst p
  exact ⟨j, hj, he, by simpa only [he] using hrepr⟩

/-- A higher successor at an odd base at least three has an actual odd prime
factor; the factorization is not treated as squarefree. -/
theorem exists_odd_prime_dvd_higher_slot (p k : ℕ) (hp : p % 2 = 1)
    (hp3 : 3 ≤ p) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 1 + p ^ (2 ^ (k + 1)) := by
  let s := 1 + p ^ (2 ^ (k + 1))
  have hspos : s ≠ 0 := by dsimp [s]; positivity
  have hval : s.factorization 2 = 1 := factorization_two_higher_slot p k hp
  have hsize : 2 < s := by
    have hpow := Nat.le_self_pow (by positivity : 2 ^ (k + 1) ≠ 0) p
    dsimp only [s]
    omega
  have hcompl : s / 2 ^ s.factorization 2 ≠ 1 := by
    intro h
    have hsplit := Nat.ordProj_mul_ordCompl_eq_self s 2
    rw [h, hval] at hsplit
    norm_num at hsplit
    omega
  obtain ⟨r, hr, hdvd⟩ := Nat.exists_prime_and_dvd hcompl
  refine ⟨r, hr, ?_, hdvd.trans (Nat.ordCompl_dvd s 2)⟩
  intro hr2
  subst r
  exact Nat.not_dvd_ordCompl (by decide : Nat.Prime 2) hspos hdvd

example : (3 : ℕ) % 2 = 1 ∧ 3 ≤ (3 : ℕ) := by decide

/-- When the only odd prime in the reverse sum is three, every actual odd
prime congruent to one modulo four in the input has valuation exactly one. -/
theorem factorization_eq_one_of_prime_mod_four_of_sigma_odd_support
    (m q : ℕ) (hm : 0 < m) (hq : q.Prime) (hqm : q ∈ m.primeFactors)
    (hqmod : q % 4 = 1)
    (hsupport : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ sigma m → r = 3) :
    m.factorization q = 1 := by
  have hqodd : q % 2 = 1 := Nat.odd_of_mod_four_eq_one hqmod
  have hq3 : 3 ≤ q := by have hqpos := hq.two_le; omega
  have hslots : ∀ j ∈ binarySupport (m.factorization q), j = 0 := by
    intro j hj
    by_contra hj0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    obtain ⟨r, hr, hr2, hrslot⟩ := exists_odd_prime_dvd_higher_slot q k hqodd hq3
    have hrdiv : r ∣ sigma m := hrslot.trans (slot_dvd_sigma m q (k + 1) hqm hj)
    have hr3 := hsupport r hr hr2 hrdiv
    have hrmod := prime_mod_four_of_dvd_higher_successor q k r hr hr2 hrslot
    rw [hr3] at hrmod
    norm_num at hrmod
  have hsubset : binarySupport (m.factorization q) ⊆ {0} := by
    intro j hj
    simp [hslots j hj]
  have hle : m.factorization q ≤ 1 := by
    rw [← sum_binarySupport (m.factorization q)]
    calc
      (∑ j ∈ binarySupport (m.factorization q), 2 ^ j) ≤
          ∑ j ∈ ({0} : Finset ℕ), 2 ^ j := Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun j hj hnot => Nat.zero_le _)
      _ = 1 := by simp
  have hqdata := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hm)).mp hqm
  have hpos := hq.factorization_pos_of_dvd (ne_of_gt hm) hqdata.2
  omega

/-- A natural number congruent to two modulo four has exactly one factor two. -/
theorem factorization_two_eq_one_of_mod_four (s : ℕ) (hs : s % 4 = 2) :
    s.factorization 2 = 1 := by
  have hs0 : s ≠ 0 := by omega
  have hlo : 1 ≤ s.factorization 2 := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hs0).mp
    change 2 ∣ s
    omega
  have hhi : ¬ 2 ≤ s.factorization 2 := by
    intro h
    have hdvd := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hs0).mpr h
    have hz : s % 4 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  omega

example : (6 : ℕ) % 4 = 2 := by decide

/-- Each odd prime with valuation one and congruent to one modulo four has
successor twice a positive power of three, if the reverse sum has no other odd primes. -/
theorem exists_successor_eq_two_mul_three_pow (m q : ℕ) (hq : q.Prime)
    (hqm : q ∈ m.primeFactors) (hqmod : q % 4 = 1) (he : m.factorization q = 1)
    (hsupport : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ sigma m → r = 3) :
    ∃ t : ℕ, 1 ≤ t ∧ q + 1 = 2 * 3 ^ t := by
  have hj : 0 ∈ binarySupport (m.factorization q) := by rw [he]; decide
  have hdiv : q + 1 ∣ sigma m := by simpa [Nat.add_comm] using slot_dvd_sigma m q 0 hqm hj
  have hother : ∀ r ∈ (q + 1).primeFactors, r ≠ 2 → r ≠ 3 → (q + 1).factorization r = 0 := by
    intro r hr hr2 hr3
    have hrdata := (Nat.mem_primeFactors_of_ne_zero (by omega : q + 1 ≠ 0)).mp hr
    exact (hr3 (hsupport r hrdata.1 hr2 (hrdata.2.trans hdiv))).elim
  have hrepr := eq_two_pow_mul_prime_pow_of_odd_support (q + 1) 3 (by omega)
    (by decide) (by decide) hother
  have hmod : (q + 1) % 4 = 2 := by omega
  rw [factorization_two_eq_one_of_mod_four (q + 1) hmod] at hrepr
  have ht : 1 ≤ (q + 1).factorization 3 := by
    have hqpos := hq.two_le
    by_contra h
    have hz : (q + 1).factorization 3 = 0 := by omega
    rw [hz] at hrepr
    norm_num at hrepr
    omega
  exact ⟨(q + 1).factorization 3, ht, by simpa using hrepr⟩

/-- The canonical sum at nine is ten; this is the odd boundary cycle. -/
theorem sigma_nine : sigma 9 = 10 := by
  unfold sigma
  rw [show (9 : ℕ) = 3 ^ 2 by decide,
    Nat.primeFactors_prime_pow (by decide : (2 : ℕ) ≠ 0) (by decide : Nat.Prime 3),
    Nat.Prime.factorization_pow (by decide : Nat.Prime 3)]
  norm_num [localSigma, binarySupport]
  decide

/-- The canonical sum at ten is eighteen. -/
theorem sigma_ten : sigma 10 = 18 := by
  unfold sigma
  rw [show (10 : ℕ) = 2 * 5 by decide,
    Nat.primeFactors_mul (by decide : (2 : ℕ) ≠ 0) (by decide : (5 : ℕ) ≠ 0),
    Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (by decide : (5 : ℕ) ≠ 0),
    Nat.Prime.primeFactors (by decide : Nat.Prime 2),
    Nat.Prime.primeFactors (by decide : Nat.Prime 5),
    Nat.Prime.factorization (by decide : Nat.Prime 2),
    Nat.Prime.factorization (by decide : Nat.Prime 5)]
  norm_num [localSigma, binarySupport]
  decide

example : 0 < (9 : ℕ) ∧ IsSquare (9 : ℕ) ∧ 10 = sigma 9 ∧ sigma 10 = 2 * 9 ∧
    (10 : ℕ).factorization 2 = 1 := by
  refine ⟨by decide, ⟨3, rfl⟩, sigma_nine.symm, ?_, ?_⟩
  · simpa using sigma_ten
  · rw [show (10 : ℕ) = 2 * 5 by decide,
      Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (by decide : (5 : ℕ) ≠ 0),
      Nat.Prime.factorization (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 5)]
    norm_num

/-- The actual square-input valuation-one cycle forces a power-of-three odd
input component and valuation-one odd output components with successors twice
positive powers of three. No output squarefreeness is assumed. -/
theorem three_bit_and_odd_successors_of_square_cycle_factorization_two_eq_one
    (n m : ℕ) (hn : 0 < n) (hsquare : IsSquare n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n) (hf : m.factorization 2 = 1) :
    ∃ j : ℕ, 1 ≤ j ∧ n.factorization 3 = 2 ^ j ∧
      n = 2 ^ (n.factorization 2) * 3 ^ (2 ^ j) ∧
      ∀ q ∈ m.primeFactors, q ≠ 2 →
        q % 4 = 1 ∧ m.factorization q = 1 ∧
          ∃ t : ℕ, 1 ≤ t ∧ q + 1 = 2 * 3 ^ t := by
  obtain ⟨j, hj, hn3, hnrepr⟩ :=
    exists_three_bit_of_square_cycle_factorization_two_eq_one n m hn hsquare hm hcycle hf
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hsupport : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ sigma m → r = 3 := by
    intro r hr hr2 hrdiv
    rw [hcycle, hnrepr] at hrdiv
    have hnot2 : ¬ r ∣ 2 := by
      intro h
      rcases (by decide : Nat.Prime 2).eq_one_or_self_of_dvd r h with h | h
      · exact hr.ne_one h
      · exact hr2 h
    have hnDiv := (hr.dvd_mul.mp hrdiv).resolve_left hnot2
    have hnotpow : ¬ r ∣ 2 ^ n.factorization 2 := fun h => hnot2 (hr.dvd_of_dvd_pow h)
    have hthree := hr.dvd_of_dvd_pow ((hr.dvd_mul.mp hnDiv).resolve_left hnotpow)
    rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd r hthree with h | h
    · exact (hr.ne_one h).elim
    · exact h
  refine ⟨j, hj, hn3, hnrepr, ?_⟩
  intro q hqm hq2
  have hqdata := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hmpos)).mp hqm
  have hqdiv : q ∣ sigma n := by rw [← hm]; exact hqdata.2
  have hqmod := prime_mod_four_of_dvd_sigma_of_even n q
    (fun p hp => (isSquare_iff_even_factorization n hn).mp hsquare p)
    hqdata.1 hq2 hqdiv
  have he := factorization_eq_one_of_prime_mod_four_of_sigma_odd_support m q hmpos
    hqdata.1 hqm hqmod hsupport
  exact ⟨hqmod, he,
    exists_successor_eq_two_mul_three_pow m q hqdata.1 hqm hqmod he hsupport⟩

private theorem mod_nine_mul_sign (x y : ℕ)
    (hx : x % 9 = 1 ∨ x % 9 = 8) (hy : y % 9 = 1 ∨ y % 9 = 8) :
    (x * y) % 9 = 1 ∨ (x * y) % 9 = 8 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    norm_num [Nat.mul_mod, hx, hy]

private theorem mod_nine_pow_sign (q e : ℕ) (hq : q % 9 = 8) :
    q ^ e % 9 = 1 ∨ q ^ e % 9 = 8 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ]
    exact mod_nine_mul_sign (q ^ e) q ih (Or.inr hq)

/-- Arbitrary prime multiplicities preserve the sign modulo nine when every
actual prime factor is minus one modulo nine. -/
theorem mod_nine_sign_of_primeFactors (c : ℕ) (hc : 0 < c)
    (hprimes : ∀ q ∈ c.primeFactors, q % 9 = 8) :
    c % 9 = 1 ∨ c % 9 = 8 := by
  have hprod : ∀ s : Finset ℕ,
      (∀ q ∈ s, q % 9 = 8) →
      (∏ q ∈ s, q ^ c.factorization q) % 9 = 1 ∨
        (∏ q ∈ s, q ^ c.factorization q) % 9 = 8 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert q s hnot ih =>
      intro hq
      rw [Finset.prod_insert hnot]
      exact mod_nine_mul_sign _ _
        (mod_nine_pow_sign q _ (hq q (Finset.mem_insert_self q s)))
        (ih (fun r hr => hq r (Finset.mem_insert_of_mem hr)))
  have hsign := hprod c.primeFactors hprimes
  rwa [← Nat.prod_primeFactors_pow_factorization (ne_of_gt hc)] at hsign

example : 0 < (17 : ℕ) ∧ (∀ q ∈ (17 : ℕ).primeFactors, q % 9 = 8) := by
  refine ⟨by decide, ?_⟩
  rw [Nat.Prime.primeFactors (by decide : Nat.Prime 17)]
  simp

/-- The half-successor of a higher power of three cannot have all actual prime
factors with successor twice a positive power of three. The argument preserves
arbitrary multiplicities and forces the occupied bit to be exactly one. -/
theorem bit_eq_one_of_three_half_successor_prime_shapes (j c : ℕ) (hj : 1 ≤ j)
    (hhalf : 2 * c = 1 + 3 ^ (2 ^ j))
    (hshape : ∀ q ∈ c.primeFactors, ∃ t : ℕ, 1 ≤ t ∧ q + 1 = 2 * 3 ^ t) :
    j = 1 := by
  by_contra hj1
  have hj2 : 2 ≤ j := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj2
  have hD : 2 ^ j = 4 * 2 ^ k := by
    rw [hk, pow_add]
    ring
  have hpow5 : 3 ^ (2 ^ j) % 5 = 1 := by
    rw [hD, pow_mul]
    norm_num [Nat.pow_mod]
  have hc5 : c % 5 = 1 := by
    have hmod := congrArg (fun x : ℕ => x % 5) hhalf
    rw [Nat.mul_mod, Nat.add_mod, hpow5] at hmod
    have hbound := Nat.mod_lt c (by decide : 0 < 5)
    omega
  have hD2 : 2 ≤ 2 ^ j := by
    have hexp := Nat.lt_two_pow_self (n := j)
    omega
  have hpow9 : 3 ^ (2 ^ j) % 9 = 0 := by
    have hdvd : 3 ^ 2 ∣ 3 ^ (2 ^ j) := pow_dvd_pow 3 hD2
    exact Nat.mod_eq_zero_of_dvd hdvd
  have hc9 : c % 9 = 5 := by
    have hmod := congrArg (fun x : ℕ => x % 9) hhalf
    rw [Nat.mul_mod, Nat.add_mod, hpow9] at hmod
    have hbound := Nat.mod_lt c (by decide : 0 < 9)
    omega
  have hcpos : 0 < c := by
    have hpowpos : 0 < 3 ^ (2 ^ j) := by positivity
    omega
  have hprimes : ∀ q ∈ c.primeFactors, q % 9 = 8 := by
    intro q hq
    obtain ⟨t, ht, hqt⟩ := hshape q hq
    have ht2 : 2 ≤ t := by
      by_contra h
      have ht1 : t = 1 := by omega
      rw [ht1] at hqt
      norm_num at hqt
      have hq5 : q = 5 := by omega
      have hdiv := Nat.dvd_of_mem_primeFactors hq
      rw [hq5] at hdiv
      have hz : c % 5 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      omega
    have ht9 : 3 ^ t % 9 = 0 :=
      Nat.mod_eq_zero_of_dvd (pow_dvd_pow 3 ht2 : 3 ^ 2 ∣ 3 ^ t)
    have hmod := congrArg (fun x : ℕ => x % 9) hqt
    rw [Nat.add_mod, Nat.mul_mod, ht9] at hmod
    have hbound := Nat.mod_lt q (by decide : 0 < 9)
    omega
  have hsign := mod_nine_sign_of_primeFactors c hcpos hprimes
  omega

example : 1 ≤ (1 : ℕ) ∧ 2 * 5 = 1 + 3 ^ (2 ^ (1 : ℕ)) ∧
    (∀ q ∈ (5 : ℕ).primeFactors, ∃ t : ℕ, 1 ≤ t ∧ q + 1 = 2 * 3 ^ t) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [Nat.Prime.primeFactors (by decide : Nat.Prime 5)]
  intro q hq
  have hq5 : q = 5 := Finset.mem_singleton.mp hq
  subst q
  exact ⟨1, by decide, by decide⟩

/-- The forward square-input cycle connects the modular half-successor
obstruction to its actual occupied bit: the valuation of three is exactly two. -/
theorem factorization_three_eq_two_of_square_cycle_factorization_two_eq_one
    (n m : ℕ) (hn : 0 < n) (hsquare : IsSquare n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n) (hf : m.factorization 2 = 1) :
    n.factorization 3 = 2 := by
  obtain ⟨j, hj, hn3, hnrepr, hodd⟩ :=
    three_bit_and_odd_successors_of_square_cycle_factorization_two_eq_one
      n m hn hsquare hm hcycle hf
  have h3dvd : 3 ∣ n := by
    change 3 ^ 1 ∣ n
    apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3)
      (ne_of_gt hn)).mpr
    rw [hn3]
    have hpowpos : 0 < 2 ^ j := by positivity
    omega
  have h3mem := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr
    ⟨(by decide : Nat.Prime 3), h3dvd⟩
  have hjmem : j ∈ binarySupport (n.factorization 3) := by
    rw [hn3]
    simp [binarySupport, Nat.testBit_two_pow, Nat.lt_two_pow_self]
  have hslot : 1 + 3 ^ (2 ^ j) ∣ m := by
    rw [hm]
    exact slot_dvd_sigma n 3 j h3mem hjmem
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hval : (1 + 3 ^ (2 ^ j)).factorization 2 = 1 := by
    rw [hk]
    exact factorization_two_higher_slot 3 k (by decide)
  have htwo : 2 ∣ 1 + 3 ^ (2 ^ j) := by
    change 2 ^ 1 ∣ _
    apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2)
      (by positivity : 1 + 3 ^ (2 ^ j) ≠ 0)).mpr
    omega
  let c := (1 + 3 ^ (2 ^ j)) / 2
  have hhalf : 2 * c = 1 + 3 ^ (2 ^ j) := Nat.mul_div_cancel' htwo
  have hcm : c ∣ m := (Nat.div_dvd_of_dvd htwo).trans hslot
  have hcpos : 0 < c := by
    have hpos : 0 < 3 ^ (2 ^ j) := by positivity
    omega
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hshape : ∀ q ∈ c.primeFactors, ∃ t : ℕ, 1 ≤ t ∧ q + 1 = 2 * 3 ^ t := by
    intro q hq
    have hqdata := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hcpos)).mp hq
    have hqm := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hmpos)).mpr
      ⟨hqdata.1, hqdata.2.trans hcm⟩
    have hq2 : q ≠ 2 := by
      intro h
      subst q
      have h4 : 4 ∣ 1 + 3 ^ (2 ^ j) := by
        rw [← hhalf]
        obtain ⟨d, hd⟩ := hqdata.2
        rw [hd]
        exact ⟨d, by ring⟩
      change 2 ^ 2 ∣ 1 + 3 ^ (2 ^ j) at h4
      have hbad := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2)
        (by positivity : 1 + 3 ^ (2 ^ j) ≠ 0)).mp h4
      omega
    exact (hodd q hqm hq2).2.2
  have hj1 := bit_eq_one_of_three_half_successor_prime_shapes j c hj hhalf hshape
  rw [hn3, hj1]
  decide

/-- In the valuation-one branch of a positive square-input cycle, the reverse
three-adic budget permits only the two known output primes, two and five.
Consequently the output is ten. -/
theorem eq_ten_of_square_cycle_factorization_two_eq_one
    (n m : ℕ) (hn : 0 < n) (hsquare : IsSquare n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n) (hf : m.factorization 2 = 1) :
    m = 10 := by
  have hn3 := factorization_three_eq_two_of_square_cycle_factorization_two_eq_one
    n m hn hsquare hm hcycle hf
  obtain ⟨j, hj, hnbit, hnrepr, hodd⟩ :=
    three_bit_and_odd_successors_of_square_cycle_factorization_two_eq_one
      n m hn hsquare hm hcycle hf
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have h3dvd : 3 ∣ n := by
    change 3 ^ 1 ∣ n
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 3)
      (ne_of_gt hn)).mpr (by omega)
  have h3mem := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr
    ⟨(by decide : Nat.Prime 3), h3dvd⟩
  have hbit : 1 ∈ binarySupport (n.factorization 3) := by rw [hn3]; decide
  have hten : 10 ∣ m := by
    rw [hm]
    simpa using slot_dvd_sigma n 3 1 h3mem hbit
  have h5mem := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hmpos)).mpr
    ⟨(by decide : Nat.Prime 5), (by decide : 5 ∣ 10).trans hten⟩
  have h2dvd : 2 ∣ m := (by decide : 2 ∣ 10).trans hten
  have h2mem := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hmpos)).mpr
    ⟨(by decide : Nat.Prime 2), h2dvd⟩
  have h5e := (hodd 5 h5mem (by decide)).2.1
  have hreverse : (sigma m).factorization 3 = 2 := by
    rw [hcycle, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (ne_of_gt hn),
      Finsupp.add_apply, hn3]
    norm_num
  have hsum : (∑ q ∈ m.primeFactors, (localSigma q (m.factorization q)).factorization 3) = 2 := by
    have hlocal : ∀ q ∈ m.primeFactors, localSigma q (m.factorization q) ≠ 0 :=
      fun q hq => ne_of_gt (localSigma_pos q (m.factorization q))
    rw [sigma, Nat.factorization_prod hlocal, Finsupp.finsetSum_apply] at hreverse
    exact hreverse
  have hlocalone : ∀ q : ℕ, localSigma q 1 = 1 + q := by
    intro q
    have hbits : binarySupport 1 = {0} := by decide
    simp [localSigma, hbits]
  have hval2 : (localSigma 2 (m.factorization 2)).factorization 3 = 1 := by
    rw [hf, hlocalone]
    norm_num
  have hval6 : (6 : ℕ).factorization 3 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by decide,
      Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (by decide : (3 : ℕ) ≠ 0),
      Finsupp.add_apply]
    norm_num
  have hval5 : (localSigma 5 (m.factorization 5)).factorization 3 = 1 := by
    rw [h5e, hlocalone]
    exact hval6
  have hother : ∀ q ∈ m.primeFactors, q ≠ 2 → q ≠ 5 → m.factorization q = 0 := by
    intro q hq hq2 hq5
    obtain ⟨hqmod, hqe, t, ht, hqt⟩ := hodd q hq hq2
    have hdiv : 3 ∣ localSigma q (m.factorization q) := by
      rw [hqe, hlocalone, Nat.add_comm, hqt]
      exact dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega : t ≠ 0)) 2
    have hvalq : 1 ≤ (localSigma q (m.factorization q)).factorization 3 :=
      (by decide : Nat.Prime 3).factorization_pos_of_dvd
        (ne_of_gt (localSigma_pos q (m.factorization q))) hdiv
    have hsubset : ({2, 5, q} : Finset ℕ) ⊆ m.primeFactors := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with h | h | h
      · simpa only [h] using h2mem
      · simpa only [h] using h5mem
      · simpa only [h] using hq
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r hr hnot => Nat.zero_le ((localSigma r (m.factorization r)).factorization 3))
    have hthree : 3 ≤ ∑ r ∈ ({2, 5, q} : Finset ℕ),
        (localSigma r (m.factorization r)).factorization 3 := by
      simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton,
        Ne.symm hq2, or_self, not_false_eq_true, Finset.sum_insert, hval2,
        Ne.symm hq5, hval5, Finset.sum_singleton]
      omega
    omega
  have hrepr := eq_two_pow_mul_prime_pow_of_odd_support m 5 hmpos
    (by decide) (by decide) hother
  rw [hf, h5e] at hrepr
  simpa using hrepr

/-- An even positive square in a canonical infinitary superperfect cycle cannot
have forward sum of two-adic valuation exactly one. -/
theorem factorization_sigma_two_ne_one_of_even_square (n m : ℕ) (hn : 0 < n)
    (heven : 2 ∣ n) (hsquare : IsSquare n) (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) : m.factorization 2 ≠ 1 := by
  intro hf
  have hmten := eq_ten_of_square_cycle_factorization_two_eq_one n m hn hsquare hm hcycle hf
  have hnine : n = 9 := by
    rw [hmten, sigma_ten] at hcycle
    omega
  rw [hnine] at heven
  norm_num at heven

end InfinitarySuperperfect
