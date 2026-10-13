import Mathlib

set_option autoImplicit false

namespace Candidates.A046094

/-- The rational `n · B_{n−1}` whose reduction mod `n` Agoh's congruence is
about.  `n − 1` uses `ℕ` subtraction; the relevant theorems carry `2 ≤ n`.
The definitions are total, and `n = 1`, where `bernoulli 0 = 1`, is an
intentional witness to the need for that guard. -/
def agohRat (n : ℕ) : ℚ := (n : ℚ) * bernoulli (n - 1)

/-- **Agoh's congruence** `n · B_{n−1} ≡ −1 (mod n)`, written division-free.

`q ≡ −1 (mod n)` for `q = a/b` in lowest terms with `gcd(b, n) = 1` means
`a ≡ −b (mod n)`, i.e. `n ∣ a + b`.  The coprimality conjunct is not decoration:
without it the congruence is not well-posed, and it is exactly what von
Staudt–Clausen supplies. -/
def AgohCongruence (n : ℕ) : Prop :=
  Nat.Coprime (agohRat n).den n ∧ (n : ℤ) ∣ (agohRat n).num + ((agohRat n).den : ℤ)

open Finset

private theorem quotient_den_dvd (n q : ℕ) : ((n : ℚ) / q).den ∣ q := by
  have h := Rat.den_dvd (n : ℤ) (q : ℤ)
  rw [Rat.divInt_eq_div] at h
  simp only [Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

private theorem quotient_den_of_dvd (n q : ℕ) (h : q ∣ n) :
    ((n : ℚ) / q).den = 1 := by
  obtain ⟨a, rfl⟩ := h
  by_cases hq : q = 0
  · simp [hq]
  · have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
    rw [Nat.cast_mul, mul_div_cancel_left₀ _ hq']
    simp

private theorem quotient_den_coprime (n q : ℕ) (hq : q.Prime) :
    Nat.Coprime ((n : ℚ) / q).den n := by
  by_cases h : q ∣ n
  · rw [quotient_den_of_dvd n q h]
    exact Nat.coprime_one_left n
  · exact (hq.coprime_iff_not_dvd.mpr h).of_dvd_left (quotient_den_dvd n q)

private theorem sum_den_coprime {ι : Type*} (s : Finset ι) (f : ι → ℚ) (n : ℕ)
    (h : ∀ i ∈ s, Nat.Coprime (f i).den n) :
    Nat.Coprime (∑ i ∈ s, f i).den n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((h a (mem_insert_self a s)).mul_left
      (ih (fun i hi => h i (mem_insert_of_mem hi)))).of_dvd_left
        (Rat.add_den_dvd _ _)

private theorem sub_den_coprime (a b : ℚ) (n : ℕ)
    (ha : Nat.Coprime a.den n) (hb : Nat.Coprime b.den n) :
    Nat.Coprime (a - b).den n :=
  (ha.mul_left hb).of_dvd_left (Rat.sub_den_dvd a b)

/-- **Well-posedness (von Staudt–Clausen consequence).**

`den(n · B_{n−1})` is coprime to `n`.  This is *not* a side condition to be
assumed — it is a theorem, and it is what makes `AgohCongruence` a statement
about a number rather than about a junk value.  It follows from Mathlib's
`Bernoulli.vonStaudt_clausen`: that theorem says `B_{2k} + Σ_{p−1 ∣ 2k} 1/p`
is an integer.  For positive even index `n − 1` (odd `n ≥ 3`),
`den(B_{n−1})` is the squarefree product `∏_{p−1 ∣ n−1} p`, and multiplying
by `n` cancels exactly the primes of that product dividing `n`.  For even
`n ≥ 4`, the odd-index Bernoulli number is zero; `n = 2` is handled separately.
Verified computationally for `2 ≤ n ≤ 60`: `gcd(den(n·B_{n−1}), n) = 1`
throughout. -/
theorem agohRat_den_coprime (n : ℕ) (hn : 2 ≤ n) :
    Nat.Coprime (agohRat n).den n := by
  by_cases htwo : n = 2
  · subst n
    norm_num [agohRat, bernoulli_one]
  by_cases heven : n % 2 = 0
  · have hodd : Odd (n - 1) := Nat.odd_iff.mpr (by omega)
    have hlarge : 1 < n - 1 := by omega
    simp [agohRat, bernoulli_eq_zero_of_odd hodd hlarge]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n - 1 = 2 * k := ⟨(n - 1) / 2, by omega⟩
    let s := (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have hB : bernoulli (2 * k) = (z : ℚ) - ∑ q ∈ s, (1 : ℚ) / q := by
      dsimp [s]
      linarith
    have hR : agohRat n = ((n : ℤ) * z : ℤ) - ∑ q ∈ s, (n : ℚ) / q := by
      rw [agohRat, hk, hB, mul_sub, Finset.mul_sum]
      simp [div_eq_mul_inv]
    rw [hR]
    apply sub_den_coprime
    · simpa only [Rat.den_intCast] using Nat.coprime_one_left n
    · apply sum_den_coprime
      intro q hq
      exact quotient_den_coprime n q (Finset.mem_filter.mp hq).2.1

/-- The **provable** direction: primes satisfy Agoh's congruence.  This should be
discharged, not archived. -/
theorem agohCongruence_of_prime {p : ℕ} (hp : p.Prime) : AgohCongruence p := by
  refine ⟨agohRat_den_coprime p hp.two_le, ?_⟩
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    norm_num [agohRat, bernoulli_one]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p - 1 = 2 * k := ⟨(p - 1) / 2, by omega⟩
  let s := (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)
  have hmem : p ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), hp, hk ▸ dvd_refl _⟩
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  let T : ℚ := (z : ℚ) - ∑ q ∈ s.erase p, (1 : ℚ) / q
  have hT : Nat.Coprime T.den p := by
    apply sub_den_coprime
    · simp
    · apply sum_den_coprime
      intro q hq
      obtain ⟨hne, hqs⟩ := Finset.mem_erase.mp hq
      have hprime : q.Prime := (Finset.mem_filter.mp hqs).2.1
      have hcop : Nat.Coprime q p := hprime.coprime_iff_not_dvd.mpr (by
        intro hdvd
        exact hne ((Nat.prime_dvd_prime_iff_eq hprime hp).mp hdvd))
      exact hcop.of_dvd_left (quotient_den_dvd 1 q)
  have hB : bernoulli (2 * k) = T - (1 : ℚ) / p := by
    have hsum := Finset.sum_erase_add s (fun q => (1 : ℚ) / q) hmem
    change (z : ℚ) = bernoulli (2 * k) + ∑ q ∈ s, (1 : ℚ) / q at hz
    dsimp [T]
    linarith
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hR : agohRat p = (p : ℚ) * T - 1 := by
    rw [agohRat, hk, hB, mul_sub, mul_one_div_cancel hpq]
  have hb : ((agohRat p).den : ℚ) ≠ 0 := by
    exact_mod_cast (Rat.den_pos (agohRat p)).ne'
  have hv : (T.den : ℚ) ≠ 0 := by exact_mod_cast (Rat.den_pos T).ne'
  have hEq : ((agohRat p).num : ℚ) / (agohRat p).den =
      (p : ℚ) * ((T.num : ℚ) / T.den) - 1 := by
    simpa only [Rat.num_div_den] using hR
  have hcross : (T.den : ℤ) * ((agohRat p).num + (agohRat p).den) =
      (p : ℤ) * (agohRat p).den * T.num := by
    have hcrossQ : (T.den : ℚ) * ((agohRat p).num + (agohRat p).den) =
        (p : ℚ) * (agohRat p).den * T.num := by
      field_simp at hEq
      nlinarith [hEq]
    exact_mod_cast hcrossQ
  have hcop : IsCoprime (p : ℤ) (T.den : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hT.symm
  apply hcop.dvd_of_dvd_mul_left
  rw [hcross]
  exact dvd_mul_of_dvd_left (dvd_mul_right (p : ℤ) _) _

example : agohRat 2 = -1 := by
  norm_num [agohRat, bernoulli_one]

example : AgohCongruence 2 := by
  norm_num [AgohCongruence, agohRat, bernoulli_one]

example : 2 ≤ (2 : ℕ) ∧ Nat.Prime 2 := by decide

end Candidates.A046094
