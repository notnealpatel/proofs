import NumberComplexity.GiugaDerivative

set_option autoImplicit false

namespace GiugaDerivative

/-- Every Giuga number is squarefree, a standard structural fact: a repeated
prime factor would force its defining quotient to be both zero and one modulo that prime. -/
theorem isGiuga_squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  have hn : n ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one h.2.1)
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hsq
  have hpn : p ∣ n := (dvd_mul_right p p).trans hsq
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
  have hquot : p ∣ n / p := (Nat.dvd_div_iff_mul_dvd hpn).mpr hsq
  have hp1 : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp
    ((h.2.2 p hmem).symm.trans (Nat.modEq_zero_iff_dvd.mpr hquot))
  exact hp.ne_one (Nat.dvd_one.mp hp1)

/-- A Giuga number has arithmetic derivative congruent to one modulo itself.
This standard structural fact combines its primewise residues using squarefreeness;
it does not assert the stronger equation `ad n = n + 1`. -/
theorem giuga_ad_modEq_one {n : ℕ} (h : IsGiuga n) : ad n ≡ 1 [MOD n] := by
  have hsf : Squarefree n := isGiuga_squarefree h
  have hprime : ∀ p ∈ n.primeFactors, ad n ≡ 1 [MOD p] := by
    intro p hp
    have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hsum : n / p + ∑ q ∈ n.primeFactors.erase p, n / q = ad n := by
      rw [Finset.add_sum_erase _ _ hp, ad_eq_sum_div_of_squarefree hsf]
    have hrest : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q :=
      Finset.dvd_sum fun q hq =>
        prime_dvd_div hpP
          (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
          (Finset.ne_of_mem_erase hq).symm hpn
          (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
    calc
      ad n = n / p + ∑ q ∈ n.primeFactors.erase p, n / q := hsum.symm
      _ ≡ n / p + 0 [MOD p] :=
        Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr hrest)
      _ = n / p := add_zero _
      _ ≡ 1 [MOD p] := h.2.2 p hp
  have hprod : ∀ s : Finset ℕ, s ⊆ n.primeFactors →
      ad n ≡ 1 [MOD ∏ p ∈ s, p] := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro hs
        simp [Nat.ModEq, Nat.mod_one]
    | @insert p s hps ih =>
        intro hs
        have hp : p ∈ n.primeFactors := hs (Finset.mem_insert_self p s)
        have hsub : s ⊆ n.primeFactors := fun q hq =>
          hs (Finset.mem_insert_of_mem hq)
        have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
          refine Nat.coprime_prod_right_iff.mpr ?_
          intro q hq
          exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
            (Nat.prime_of_mem_primeFactors (hsub hq))).mpr
            (ne_of_mem_of_not_mem hq hps).symm
        rw [Finset.prod_insert hps]
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hprime p hp, ih hsub⟩
  simpa only [Nat.prod_primeFactors_of_squarefree hsf] using
    hprod n.primeFactors (Finset.Subset.refl _)

example : IsGiuga 30 := isGiuga_30
example : Squarefree 30 := isGiuga_squarefree isGiuga_30
example : ad 30 ≡ 1 [MOD 30] := giuga_ad_modEq_one isGiuga_30

end GiugaDerivative
