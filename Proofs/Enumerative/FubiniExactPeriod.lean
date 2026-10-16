import Enumerative.FubiniPrimePowerPeriod
import Enumerative.FubiniTwoAdicPeriod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact eventual Fubini periods for all positive moduli

The prime-power classifications combine over the finite prime factorization.
This is the known Fubini period classification, not an assertion about the
first index at which periodicity starts. Natural shifts include zero.
-/

set_option autoImplicit false

namespace A000670

/-- The exact local eventual period at a prime power of positive exponent. -/
def localPeriod (p e : ℕ) : ℕ :=
  if p = 2 then (if e ≤ 1 then 1 else 2 ^ (max 1 (e - 4)))
  else p ^ (e - 1) * (p - 1)

example : localPeriod 2 1 = 1 := rfl
example : localPeriod 2 5 = 2 := rfl
example : localPeriod 3 2 = 6 := rfl

/-- The least common multiple of the exact periods of the prime-power factors;
the empty least common multiple at modulus one is one. -/
def D (M : ℕ) : ℕ :=
  M.factorization.support.lcm (fun p => localPeriod p (M.factorization p))

example : D 1 = 1 := by simp [D]
private lemma D_twelve : D 12 = 2 := by
  unfold D
  rw [show 12 = 2 ^ 2 * 3 by decide,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
    Nat.prime_two.factorization, (by decide : Nat.Prime 3).factorization]
  norm_num [Finsupp.smul_single, Finsupp.support_add_eq_union, localPeriod]

private lemma D_forty_five : D 45 = 12 := by
  unfold D
  rw [show 45 = 3 ^ 2 * 5 by decide,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
    (by decide : Nat.Prime 3).factorization, (by decide : Nat.Prime 5).factorization]
  norm_num [Finsupp.smul_single, Finsupp.support_add_eq_union, localPeriod]
  change Nat.lcm 6 4 = 12
  decide

example : D 32 = 2 := by
  unfold D
  rw [show 32 = 2 ^ 5 by decide, Nat.factorization_pow, Nat.prime_two.factorization]
  norm_num [Finsupp.smul_single, localPeriod]

private lemma local_eventual_period_iff {p e T : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (∃ N, ∀ n, N ≤ n → A051293.fubini (n + T) ≡ A051293.fubini n [MOD p ^ e]) ↔
      localPeriod p e ∣ T := by
  by_cases htwo : p = 2
  · subst p
    simpa [localPeriod] using fubini_two_adic_eventual_period_iff e T
  · simpa only [localPeriod, if_neg htwo] using
      fubini_prime_power_eventual_period_iff hp htwo he

private lemma finite_common_onset (s : Finset ℕ) (R : ℕ → ℕ → Prop)
    (h : ∀ p ∈ s, ∃ N, ∀ n, N ≤ n → R p n) :
    ∃ N, ∀ p ∈ s, ∀ n, N ≤ n → R p n := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨Np, hNp⟩ := h p (Finset.mem_insert_self p s)
    obtain ⟨Ns, hNs⟩ := ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
    refine ⟨max Np Ns, ?_⟩
    intro q hq n hn
    rcases Finset.mem_insert.mp hq with rfl | hqs
    · exact hNp n (le_trans (le_max_left _ _) hn)
    · exact hNs q hqs n (le_trans (le_max_right _ _) hn)

private lemma modEq_of_factorization {M a b : ℕ} (hM : M ≠ 0)
    (h : ∀ p ∈ M.factorization.support, a ≡ b [MOD p ^ M.factorization p]) :
    a ≡ b [MOD M] := by
  apply Nat.modEq_iff_dvd.mpr
  apply Int.natCast_dvd.mpr
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ M).mpr
  intro p k hp hpk
  have hk : k ≤ M.factorization p := (hp.pow_dvd_iff_le_factorization hM).mp hpk
  by_cases he : M.factorization p = 0
  · have hk0 : k = 0 := by omega
    simp [hk0]
  · have hmem : p ∈ M.factorization.support := Finsupp.mem_support_iff.mpr he
    have hfull : p ^ M.factorization p ∣ ((b : ℤ) - (a : ℤ)).natAbs :=
      Int.natCast_dvd.mp (Nat.modEq_iff_dvd.mp (h p hmem))
    exact dvd_trans (pow_dvd_pow p hk) hfull

/-- For every positive modulus, the eventual periods of the actual Fubini
sequence are exactly the multiples of `D M`, including the zero shift.
No assertion about the onset of periodicity is made. -/
theorem fubini_eventual_period_iff {M T : ℕ} (hM : 1 ≤ M) :
    (∃ N, ∀ n, N ≤ n → A051293.fubini (n + T) ≡ A051293.fubini n [MOD M]) ↔
      D M ∣ T := by
  have hM0 : M ≠ 0 := by omega
  rw [D, Finset.lcm_dvd_iff]
  constructor
  · rintro ⟨N, hN⟩ p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have he : 1 ≤ M.factorization p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hp)
    apply (local_eventual_period_iff hprime he).mp
    have hdiv : p ^ M.factorization p ∣ M :=
      (hprime.pow_dvd_iff_le_factorization hM0).mpr (le_refl _)
    exact ⟨N, fun n hn => (hN n hn).of_dvd hdiv⟩
  · intro h
    have hlocal : ∀ p ∈ M.factorization.support, ∃ N, ∀ n, N ≤ n →
        A051293.fubini (n + T) ≡ A051293.fubini n [MOD p ^ M.factorization p] := by
      intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have he : 1 ≤ M.factorization p := Nat.one_le_iff_ne_zero.mpr
        (Finsupp.mem_support_iff.mp hp)
      exact (local_eventual_period_iff hprime he).mpr (h p hp)
    obtain ⟨N, hN⟩ := finite_common_onset M.factorization.support
      (fun p n => A051293.fubini (n + T) ≡ A051293.fubini n [MOD p ^ M.factorization p]) hlocal
    exact ⟨N, fun n hn => modEq_of_factorization hM0 (fun p hp => hN p hp n hn)⟩

example : ∃ N, ∀ n, N ≤ n →
    A051293.fubini (n + 0) ≡ A051293.fubini n [MOD 1] := by
  exact (fubini_eventual_period_iff (by decide)).mpr (dvd_zero _)

example : ∃ N, ∀ n, N ≤ n →
    A051293.fubini (n + 2) ≡ A051293.fubini n [MOD 12] := by
  exact (fubini_eventual_period_iff (by decide)).mpr (by rw [D_twelve])

example : ∃ N, ∀ n, N ≤ n →
    A051293.fubini (n + 12) ≡ A051293.fubini n [MOD 45] := by
  exact (fubini_eventual_period_iff (by decide)).mpr (by rw [D_forty_five])

example : ¬ ∃ N, ∀ n, N ≤ n →
    A051293.fubini (n + 6) ≡ A051293.fubini n [MOD 45] := by
  rw [fubini_eventual_period_iff (by decide), D_forty_five]
  decide

example : ∃ N, ∀ n, N ≤ n →
    A051293.fubini (n + 0) ≡ A051293.fubini n [MOD 45] := by
  exact (fubini_eventual_period_iff (by decide)).mpr (dvd_zero _)

end A000670
