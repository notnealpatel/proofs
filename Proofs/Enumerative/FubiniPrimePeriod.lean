import Enumerative.FubiniMod

/-!
# Exact eventual periods of Fubini numbers modulo odd primes

This formalizes the known lower bound in Poonen (1988), Theorem 1, and combines
it with the upper bound from `Enumerative.FubiniMod` to characterize all eventual
periods, including the zero shift. No novelty is claimed.

Reference: B. Poonen, *Periodicity of a combinatorial sequence*, Fibonacci
Quarterly 26 (1988), 70–76, https://www.fq.math.ca/Scanned/26-1/poonen.pdf.
-/

set_option autoImplicit false

open Finset

namespace A000670

open A051293

/-- At a prime, Poonen's truncated sum equals the Fubini number itself. -/
lemma fubini_prime_sum {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (fubini n : ZMod p) =
      ∑ j : Fin p, (2 : ZMod p) ^ (p - 1 - j.val) * (j.val : ZMod p) ^ n := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := poonen_congr p n
  rw [ZMod.pow_card, show (2 : ZMod p) - 1 = 1 by ring, one_mul] at h
  exact h.trans (Fin.sum_univ_eq_sum_range _ _).symm

/-- Every eventual period modulo an odd prime is divisible by one less than the prime. -/
theorem prime_sub_one_dvd_fubini_eventual_period {p T : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hperiod : ∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p]) :
    p - 1 ∣ T := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hN⟩ := hperiod
  let L := max N 1
  let c : Fin p → ZMod p := fun j =>
    (2 : ZMod p) ^ (p - 1 - j.val) * (j.val : ZMod p) ^ L *
      ((j.val : ZMod p) ^ T - 1)
  have hinj : Function.Injective (fun j : Fin p => (j.val : ZMod p)) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg ZMod.val hij
    simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using hv
  have hmom (r : Fin p) : ∑ j : Fin p, c j * (j.val : ZMod p) ^ r.val = 0 := by
    have heq : (fubini (L + r.val + T) : ZMod p) = (fubini (L + r.val) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hN _ (by dsimp [L]; omega))
    rw [fubini_prime_sum hp, fubini_prime_sum hp] at heq
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at heq
    calc
      _ = ∑ j : Fin p,
          ((2 : ZMod p) ^ (p - 1 - j.val) * (j.val : ZMod p) ^ (L + r.val + T) -
            (2 : ZMod p) ^ (p - 1 - j.val) * (j.val : ZMod p) ^ (L + r.val)) := by
              apply Finset.sum_congr rfl
              intro j _
              dsimp [c]
              simp only [pow_add]
              ring
      _ = 0 := heq
  have hc : c = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj hmom
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hodd (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  have hpow (x : ZMod p) (hx : x ≠ 0) : x ^ T = 1 := by
    let j : Fin p := ⟨x.val, x.val_lt⟩
    have hj : (j.val : ZMod p) = x := ZMod.natCast_zmod_val x
    have hzero := congrFun hc j
    change (2 : ZMod p) ^ (p - 1 - j.val) * (j.val : ZMod p) ^ L *
      ((j.val : ZMod p) ^ T - 1) = 0 at hzero
    rw [hj] at hzero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (pow_ne_zero _ htwo) (pow_ne_zero _ hx)))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hgT : g ^ T = 1 := by
    apply Units.ext
    exact hpow (g : ZMod p) g.ne_zero
  have hd := orderOf_dvd_of_pow_eq_one hgT
  rw [hg] at hd
  simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp] using hd

/-- Modulo an odd prime, the eventual periods are exactly the multiples of `p - 1`,
including the zero shift. -/
theorem fubini_prime_eventual_period_iff {p T : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p]) ↔ p - 1 ∣ T := by
  constructor
  · exact prime_sub_one_dvd_fubini_eventual_period hp hodd
  · intro hT
    obtain ⟨N, P, hP, _, hN⟩ :=
      fubini_mod_eventuallyPeriodic_conjecture p hp.one_lt.le
    rw [Nat.totient_prime hp] at hP
    obtain ⟨k, hk⟩ := hP.trans hT
    refine ⟨N, fun n hn => ?_⟩
    rw [hk]
    clear hk
    induction k with
    | zero => exact Nat.ModEq.refl _
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact (hN (n + P * k) (by omega)).trans ih

/-- For example, modulo three the shift two is an eventual period. -/
example : ∃ N, ∀ n, N ≤ n → fubini (n + 2) ≡ fubini n [MOD 3] := by
  exact (fubini_prime_eventual_period_iff (by decide) (by decide)).mpr (by decide)

/-- Modulo three, the shift one cannot be an eventual period. -/
example : ¬ (∃ N, ∀ n, N ≤ n → fubini (n + 1) ≡ fubini n [MOD 3]) := by
  rw [fubini_prime_eventual_period_iff (by decide) (by decide)]
  decide

/-- The zero shift is deliberately included among the eventual periods. -/
example : ∃ N, ∀ n, N ≤ n → fubini (n + 0) ≡ fubini n [MOD 3] := by
  exact ⟨0, fun n _ => by rfl⟩

end A000670
