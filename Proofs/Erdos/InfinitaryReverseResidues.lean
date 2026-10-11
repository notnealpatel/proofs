import Erdos.InfinitaryReverseProduct

set_option autoImplicit false

namespace InfinitarySuperperfect

private theorem five_odd_mod (u : ℕ) (hu : Odd u) :
    5 ^ u % 3 = 2 ∧ 5 ^ u % 8 = 5 := by
  obtain ⟨t, rfl⟩ := hu
  simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]

private theorem three_mod_eight (v : ℕ) : 3 ^ v % 8 = 1 ∨ 3 ^ v % 8 = 3 := by
  rcases Nat.even_or_odd v with he | ho
  · obtain ⟨t, rfl⟩ := he
    left
    have ht : t + t = 2 * t := by omega
    simp [ht, pow_mul, Nat.pow_mod]
  · obtain ⟨t, rfl⟩ := ho
    right
    simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]

/-- An actual reverse tag with mixed three/five support and positive odd five-valuation
has height zero, positive three-valuation, and the required base-prime residues. -/
theorem reverseTag_residues (m q h : ℕ)
    (htag : (⟨q, h⟩ : Sigma fun _ : ℕ => ℕ) ∈ reverseTags m)
    (hq4 : q % 4 = 1)
    (hu : 0 < (normalizedSlot q h).factorization 5)
    (hodd : Odd ((normalizedSlot q h).factorization 5))
    (hshape : normalizedSlot q h =
      3 ^ ((normalizedSlot q h).factorization 3) *
      5 ^ ((normalizedSlot q h).factorization 5)) :
    h = 0 ∧ 0 < (normalizedSlot q h).factorization 3 ∧
      q % 3 = 2 ∧ q % 5 = 4 ∧ (q % 16 = 9 ∨ q % 16 = 13) := by
  obtain ⟨hp, _, _⟩ := (mem_reverseTags m ⟨q, h⟩).mp htag
  have hprime : q.Prime := (Nat.mem_primeFactors.mp hp).1
  have hq3 : q ≠ 3 := by intro he; subst q; norm_num at hq4
  have hqmod3 : q % 3 ≠ 0 := by
    intro hz
    have hd : 3 ∣ q := Nat.dvd_of_mod_eq_zero hz
    have he : q = 3 := (hprime.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd
    exact hq3 he
  let u := (normalizedSlot q h).factorization 5
  let v := (normalizedSlot q h).factorization 3
  have hid : 1 + q ^ (2 ^ h) = 2 * (3 ^ v * 5 ^ u) := by
    rw [← hshape]
    exact (normalizedSlot_spec q h hq4).1
  have h5zero : 5 ^ u % 5 = 0 := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hu
    change u = 1 + t at ht
    rw [ht, pow_add]
    simp
  have hraw5 := congrArg (fun x : ℕ => x % 5) hid
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, h5zero, Nat.mul_zero,
    Nat.zero_mod] at hraw5
  have hsmall : h < 2 := by
    by_contra hn
    have hh : 2 ≤ h := by omega
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hh
    have hfour : q ^ 4 % 5 = 0 ∨ q ^ 4 % 5 = 1 := by
      have hb : q % 5 < 5 := Nat.mod_lt _ (by decide)
      rw [Nat.pow_mod]
      interval_cases q % 5 <;> norm_num
    have hpow : q ^ (2 ^ (2 + t)) % 5 = 0 ∨ q ^ (2 ^ (2 + t)) % 5 = 1 := by
      rw [pow_add, pow_mul]
      change (q ^ 4) ^ (2 ^ t) % 5 = 0 ∨ (q ^ 4) ^ (2 ^ t) % 5 = 1
      rcases hfour with hz | ho
      · left
        rw [Nat.pow_mod, hz]
        simp
      · right
        rw [Nat.pow_mod, ho]
        simp
    rcases hpow with hz | ho
    · rw [hz] at hraw5
      norm_num at hraw5
    · rw [ho] at hraw5
      norm_num at hraw5
  have hu3 := (five_odd_mod u hodd).1
  have hzero : h = 0 := by
    by_contra hz
    have hh : h = 1 := by omega
    rw [hh] at hid
    have hsq : q ^ 2 % 3 = 1 := by
      have hb : q % 3 < 3 := Nat.mod_lt _ (by decide)
      rw [Nat.pow_mod]
      interval_cases q % 3 <;> norm_num at *
    have hraw3 := congrArg (fun x : ℕ => x % 3) hid
    have hvzero : v = 0 := by
      by_contra hv
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ v)
      have hv3 : 3 ^ v % 3 = 0 := by rw [ht, pow_add]; simp
      simp [Nat.add_mod, Nat.mul_mod, hsq, hv3] at hraw3
    simp [Nat.add_mod, Nat.mul_mod, hsq, hvzero, hu3] at hraw3
  rw [hzero] at hid
  simp only [pow_zero, pow_one] at hid
  have hvpos : 0 < v := by
    by_contra hv
    have hvzero : v = 0 := by omega
    have hraw3 := congrArg (fun x : ℕ => x % 3) hid
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at hraw3
    rw [hvzero, pow_zero, hu3] at hraw3
    norm_num at hraw3
    have hb : q % 3 < 3 := Nat.mod_lt _ (by decide)
    have hz : q % 3 = 0 := by omega
    exact hqmod3 hz
  have hv3 : 3 ^ v % 3 = 0 := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hvpos
    rw [ht, pow_add]
    simp
  have hres3 : q % 3 = 2 := by
    have hr := congrArg (fun x : ℕ => x % 3) hid
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, hv3] at hr
    norm_num at hr
    have hb : q % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have hres5 : q % 5 = 4 := by
    have hr := congrArg (fun x : ℕ => x % 5) hid
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, h5zero] at hr
    norm_num at hr
    have hb : q % 5 < 5 := Nat.mod_lt _ (by decide)
    omega
  have hr8 : (3 ^ v * 5 ^ u) % 8 = 5 ∨ (3 ^ v * 5 ^ u) % 8 = 7 := by
    rw [Nat.mul_mod, (five_odd_mod u hodd).2]
    rcases three_mod_eight v with hv | hv <;> rw [hv] <;> norm_num
  have hres16 : q % 16 = 9 ∨ q % 16 = 13 := by
    have hr := congrArg (fun x : ℕ => x % 16) hid
    rw [Nat.add_mod] at hr
    norm_num at hr
    have hb : q % 16 < 16 := Nat.mod_lt _ (by decide)
    have hmul : (2 * (3 ^ v * 5 ^ u)) % 16 =
        2 * ((3 ^ v * 5 ^ u) % 8) := by omega
    rw [hmul] at hr
    rcases hr8 with he | he <;> rw [he] at hr <;> omega
  exact ⟨hzero, hvpos, hres3, hres5, hres16⟩

/-- The mixed reverse-budget hypotheses yield an actual odd prime divisor with the
selected three/five and modulo-sixteen residues, without a forward or square premise. -/
theorem exists_reverse_prime_residues (n m j k : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2) (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1)
    (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hshape : n = 2 ^ (n.factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k)) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ m ∧ q % 4 = 1 ∧ q % 3 = 2 ∧
      q % 5 = 4 ∧ (q % 16 = 9 ∨ q % 16 = 13) := by
  obtain ⟨⟨q, h⟩, hi, hu, ho, hs⟩ :=
    exists_reverseTag_mixed n m j k hn hm hm2 hreverse hmod hj hk hshape
  obtain ⟨hp, htwo, _⟩ := (mem_reverseTags m ⟨q, h⟩).mp hi
  have hq4 := hmod q hp htwo
  obtain ⟨_, _, h3, h5, h16⟩ := reverseTag_residues m q h hi hq4 hu ho hs
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  exact ⟨q, hprime, htwo, hdiv, hq4, h3, h5, h16⟩

/-- Independent support and valuations for the joint D witness. -/
private theorem witness_data : (356 : ℕ).primeFactors = {2, 89} ∧
    (356 : ℕ).factorization 2 = 2 ∧ (356 : ℕ).factorization 89 = 1 := by
  have hrepr : (356 : ℕ) = 2 ^ 2 * 89 := by decide
  have htwo : Nat.Prime 2 := by decide
  have hp : Nat.Prime 89 := by decide
  rw [hrepr, Nat.primeFactors_mul (by decide) (by decide),
    Nat.primeFactors_prime_pow (by decide) htwo, hp.primeFactors,
    Nat.factorization_mul (by decide) (by decide), htwo.factorization_pow, hp.factorization]
  norm_num

/-- The concrete reverse support is nonempty and retains the actual base and height. -/
private theorem witness_tags : reverseTags 356 = {⟨89, 0⟩} := by
  obtain ⟨hp, htwo, h89⟩ := witness_data
  ext ⟨q, h⟩
  have hb : binarySupport 1 = {0} := by decide
  by_cases hq : q = 89
  · subst q
    simp [mem_reverseTags, hp, h89, hb]
  · simp only [mem_reverseTags, hp, Finset.mem_insert, Finset.mem_singleton]
    aesop

/-- All D hypotheses hold jointly at n=225, m=356, j=k=1, independently of the exports. -/
private theorem witness_premises : 0 < (225 : ℕ) ∧ 0 < (356 : ℕ) ∧
    (356 : ℕ).factorization 2 = 2 ∧ sigma 356 = 2 * 225 ∧
    (∀ q ∈ (356 : ℕ).primeFactors, q ≠ 2 → q % 4 = 1) ∧
    1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
    (225 : ℕ) = 2 ^ ((225 : ℕ).factorization 2) * 3 ^ (2 ^ (1 : ℕ)) * 5 ^ (2 ^ (1 : ℕ)) := by
  have hsigma : sigma 356 = 2 * 225 := by
    rw [sigma_eq_five_mul_raw_product 356 (by decide) witness_data.2.1, witness_tags]
    norm_num
  have hmod : ∀ q ∈ (356 : ℕ).primeFactors, q ≠ 2 → q % 4 = 1 := by
    intro q hq hq2
    rw [witness_data.1] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with h | h
    · exact (hq2 h).elim
    · subst q; decide
  have hv : (225 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  exact ⟨by decide, by decide, witness_data.2.1, hsigma, hmod,
    by decide, by decide, by norm_num [hv]⟩

/-- The selected slot has independently computed ordinary valuations two and one. -/
private theorem witness_slot : normalizedSlot 89 0 = 45 ∧
    (normalizedSlot 89 0).factorization 3 = 2 ∧
    (normalizedSlot 89 0).factorization 5 = 1 := by
  have hr : normalizedSlot 89 0 = 3 ^ 2 * 5 := by decide
  constructor
  · decide
  · rw [hr, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Finsupp.add_apply, (by decide : Nat.Prime 3).factorization_pow,
      (by decide : Nat.Prime 5).factorization]
    norm_num

example : (⟨89, 0⟩ : Sigma fun _ : ℕ => ℕ) ∈ reverseTags 356 := by
  rw [witness_tags]
  exact Finset.mem_singleton_self _

example : 0 = (0 : ℕ) ∧ 0 < (normalizedSlot 89 0).factorization 3 ∧
    89 % 3 = 2 ∧ 89 % 5 = 4 ∧ (89 % 16 = 9 ∨ 89 % 16 = 13) := by
  apply reverseTag_residues 356 89 0
  · rw [witness_tags]
    exact Finset.mem_singleton_self _
  · decide
  · rw [witness_slot.2.2]
    decide
  · rw [witness_slot.2.2]
    decide
  · rw [witness_slot.2.1, witness_slot.2.2, witness_slot.1]
    decide

example : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ 356 ∧ q % 4 = 1 ∧ q % 3 = 2 ∧
    q % 5 = 4 ∧ (q % 16 = 9 ∨ q % 16 = 13) := by
  obtain ⟨hn, hm, hm2, hr, hmod, hj, hk, hs⟩ := witness_premises
  exact exists_reverse_prime_residues 225 356 1 1 hn hm hm2 hr hmod hj hk hs

example : Nat.Prime 89 ∧ 89 ≠ 2 ∧ 89 ∣ 356 ∧ 89 % 4 = 1 ∧ 89 % 3 = 2 ∧
    89 % 5 = 4 ∧ 89 % 16 = 9 := by decide

example : Odd (225 : ℕ) ∧ ¬ Even (225 : ℕ) := by decide

/-- The joint witness is not a forward cycle: its forward sum is 260, not 356. -/
private theorem witness_forward : sigma 225 = 260 := by
  have hrepr : (225 : ℕ) = 3 ^ 2 * 5 ^ 2 := by decide
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have hp : (225 : ℕ).primeFactors = {3, 5} := by
    rw [hrepr, Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_prime_pow (by decide) h3,
      Nat.primeFactors_prime_pow (by decide) h5]
    decide
  have hv : (225 : ℕ).factorization 3 = 2 ∧ (225 : ℕ).factorization 5 = 2 := by
    rw [hrepr, Nat.factorization_mul (by decide) (by decide),
      h3.factorization_pow, h5.factorization_pow]
    norm_num
  rw [sigma, hp]
  norm_num [hv.1, hv.2]
  decide

example : sigma 225 ≠ 356 := by
  rw [witness_forward]
  decide

end InfinitarySuperperfect

