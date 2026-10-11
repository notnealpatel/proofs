import Erdos.InfinitaryReverseBudget

set_option autoImplicit false

namespace InfinitarySuperperfect

/-- The mixed input shape and reverse budget determine the tagged normalized product. -/
theorem reverseProduct_eq_mixed (n m j k : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2) (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1)
    (_hj : 1 ≤ j) (hk : 1 ≤ k)
    (hshape : n = 2 ^ (n.factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k)) :
    reverseProduct m = 3 ^ (2 ^ j) * 5 ^ (2 ^ k - 1) := by
  have hb := reverseCount_eq_factorization_two_add_one n m hn hm hm2 hreverse hmod
  have heq := sigma_eq_five_mul_two_pow_reverseCount m hm hm2 hmod
  rw [hb, hreverse, pow_succ] at heq
  have heq' : 2 * (2 ^ (n.factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k)) =
      5 * (2 ^ (n.factorization 2) * 2) * reverseProduct m := by
    calc
      _ = 2 * n := congrArg (fun x => 2 * x) hshape.symm
      _ = _ := heq
  have hc : 5 * reverseProduct m = 3 ^ (2 ^ j) * 5 ^ (2 ^ k) := by
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (n.factorization 2) * 2)
    calc
      (2 ^ (n.factorization 2) * 2) * (5 * reverseProduct m) =
          5 * (2 ^ (n.factorization 2) * 2) * reverseProduct m := by ring
      _ = 2 * (2 ^ (n.factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k)) := heq'.symm
      _ = (2 ^ (n.factorization 2) * 2) * (3 ^ (2 ^ j) * 5 ^ (2 ^ k)) := by ring
  have hp2 : 2 ≤ 2 ^ k := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hk)
  have hexp : 2 ^ k = (2 ^ k - 1) + 1 := by omega
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5)
  calc
    5 * reverseProduct m = 3 ^ (2 ^ j) * 5 ^ (2 ^ k) := hc
    _ = 5 * (3 ^ (2 ^ j) * 5 ^ (2 ^ k - 1)) := by
      conv_lhs => rw [hexp, pow_succ]
      ring

private theorem reconstruct_mixed (r A B : ℕ) (hr : 0 < r)
    (hd : r ∣ 3 ^ A * 5 ^ B) :
    r = 3 ^ (r.factorization 3) * 5 ^ (r.factorization 5) := by
  have hs : r.primeFactors ⊆ ({3, 5} : Finset ℕ) := by
    intro p hp
    obtain ⟨hprime, hdiv⟩ := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hr)).mp hp
    have hpdiv := hdiv.trans hd
    rcases hprime.dvd_mul.mp hpdiv with h3 | h5
    · have heq : p = 3 :=
        ((by decide : Nat.Prime 3).dvd_iff_eq hprime.ne_one).mp
          (hprime.dvd_of_dvd_pow h3) |>.symm
      simp [heq]
    · have heq : p = 5 :=
        ((by decide : Nat.Prime 5).dvd_iff_eq hprime.ne_one).mp
          (hprime.dvd_of_dvd_pow h5) |>.symm
      simp [heq]
  calc
    r = ∏ p ∈ r.primeFactors, p ^ r.factorization p :=
      Nat.prod_primeFactors_pow_factorization (ne_of_gt hr)
    _ = ∏ p ∈ ({3, 5} : Finset ℕ), p ^ r.factorization p := by
      apply Finset.prod_subset hs
      intro p hp hnot
      have hz : r.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        by_cases hprime : p.Prime
        · right; left
          intro hd'
          exact hnot ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt hr)).mpr ⟨hprime, hd'⟩)
        · exact Or.inl hprime
      simp [hz]
    _ = _ := by simp

/-- Some actual tagged occurrence has positive odd five-valuation and ordinary prime support
contained in three and five. Tags are retained even when their normalized values coincide. -/
theorem exists_reverseTag_mixed (n m j k : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2) (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1)
    (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hshape : n = 2 ^ (n.factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k)) :
    ∃ i ∈ reverseTags m,
      0 < (normalizedSlot i.1 i.2).factorization 5 ∧
      Odd ((normalizedSlot i.1 i.2).factorization 5) ∧
      normalizedSlot i.1 i.2 =
        3 ^ ((normalizedSlot i.1 i.2).factorization 3) *
        5 ^ ((normalizedSlot i.1 i.2).factorization 5) := by
  classical
  have hprod := reverseProduct_eq_mixed n m j k hn hm hm2 hreverse hmod hj hk hshape
  have hpos : ∀ i ∈ reverseTags m, 0 < normalizedSlot i.1 i.2 := by
    intro i hi
    obtain ⟨hp, htwo, _⟩ := (mem_reverseTags m i).mp hi
    exact (normalizedSlot_spec i.1 i.2 (hmod i.1 hp htwo)).2.1
  have hsum : (∑ i ∈ reverseTags m, (normalizedSlot i.1 i.2).factorization 5) =
      2 ^ k - 1 := by
    have hv := congrArg (fun f : ℕ →₀ ℕ => f 5)
      (Nat.factorization_prod (fun i hi => ne_of_gt (hpos i hi)))
    change (reverseProduct m).factorization 5 = _ at hv
    rw [hprod, Nat.factorization_mul (by positivity) (by positivity),
      Finsupp.add_apply, (by decide : Nat.Prime 3).factorization_pow,
      (by decide : Nat.Prime 5).factorization_pow] at hv
    simpa using hv.symm
  have heven : Even (2 ^ k) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add]
    exact even_two.mul_right _
  have hpowpos : 0 < 2 ^ k := by positivity
  have hodd : Odd (2 ^ k - 1) := by
    obtain ⟨t, ht⟩ := heven
    apply Nat.odd_iff.mpr
    omega
  have hselect : ∃ i ∈ reverseTags m, Odd ((normalizedSlot i.1 i.2).factorization 5) := by
    by_contra hnone
    have hall : ∀ i ∈ reverseTags m, Even ((normalizedSlot i.1 i.2).factorization 5) := by
      intro i hi
      exact Nat.not_odd_iff_even.mp (fun ho => hnone ⟨i, hi, ho⟩)
    have he := Finset.even_sum _ hall
    rw [hsum] at he
    exact (Nat.not_even_iff_odd.mpr hodd) he
  obtain ⟨i, hi, ho⟩ := hselect
  have hvpos : 0 < (normalizedSlot i.1 i.2).factorization 5 := by
    obtain ⟨t, ht⟩ := ho
    omega
  refine ⟨i, hi, hvpos, ho, ?_⟩
  apply reconstruct_mixed _ (2 ^ j) (2 ^ k - 1) (hpos i hi)
  rw [← hprod]
  exact Finset.dvd_prod_of_mem (fun i => normalizedSlot i.1 i.2) hi

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

example : reverseProduct 356 = 45 := by
  simp [reverseProduct, witness_tags, normalizedSlot]

example : 0 < (normalizedSlot 89 0).factorization 5 ∧
    Odd ((normalizedSlot 89 0).factorization 5) ∧
    normalizedSlot 89 0 = 3 ^ ((normalizedSlot 89 0).factorization 3) *
      5 ^ ((normalizedSlot 89 0).factorization 5) := by
  have hr : normalizedSlot 89 0 = 3 ^ 2 * 5 := by decide
  rw [hr, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Finsupp.add_apply, (by decide : Nat.Prime 3).factorization_pow,
    (by decide : Nat.Prime 5).factorization]
  norm_num

example : reverseProduct 356 = 3 ^ (2 ^ (1 : ℕ)) * 5 ^ (2 ^ (1 : ℕ) - 1) := by
  obtain ⟨hn, hm, hm2, hr, hmod, hj, hk, hs⟩ := witness_premises
  exact reverseProduct_eq_mixed 225 356 1 1 hn hm hm2 hr hmod hj hk hs

example : ∃ i ∈ reverseTags 356,
    0 < (normalizedSlot i.1 i.2).factorization 5 ∧
    Odd ((normalizedSlot i.1 i.2).factorization 5) ∧
    normalizedSlot i.1 i.2 = 3 ^ ((normalizedSlot i.1 i.2).factorization 3) *
      5 ^ ((normalizedSlot i.1 i.2).factorization 5) := by
  obtain ⟨hn, hm, hm2, hr, hmod, hj, hk, hs⟩ := witness_premises
  exact exists_reverseTag_mixed 225 356 1 1 hn hm hm2 hr hmod hj hk hs

example : Odd (225 : ℕ) := by decide

end InfinitarySuperperfect
