/-
# A000670 — Bala: Fubini numbers mod k are eventually periodic, period ∣ φ(k)

## OEIS source (`oeis show A000670`, retrieved 2026-10-21)

```
NAME:     Fubini numbers: number of preferential arrangements of n labeled
          elements; or number of weak orders on n labeled elements; or number
          of ordered partitions of [n].
TERMS:    1,1,3,13,75,541,4683,47293,545835,7087261,102247563,...
COMMENT (the conjecture, verbatim):
  From _Peter Bala_, Jul 08 2022: (Start)
  Conjecture: Let k be a positive integer. The sequence obtained by reducing
  a(n) modulo k is eventually periodic with the period dividing
  phi(k) = A000010(k). For example, modulo 16 we obtain the sequence
  [1, 1, 3, 13, 11, 13, 11, 13, 11, 13, ...], with an apparent period of 2
  beginning at a(4). Cf. A354242.
  More generally, we conjecture that the same property holds for integer
  sequences having an e.g.f. of the form G(exp(x) - 1), where G(x) is an
  integral power series. (End)
```

## Status

Proved in the literature: B. Poonen, *Periodicity of a combinatorial
sequence*, Fibonacci Quarterly 26 (1988), 70–76 (Fubini case, with the
totient bound; prime-power case also Barsky).  Triage status:
"proved-elsewhere".  Both parts are already kernel-checked in this
repository:

* `A000670.fubini_mod_eventuallyPeriodic_conjecture`
  (`Proofs/Enumerative/FubiniMod.lean`), and
* `OrdinaryIntegralEGF.factorial_mul_coeff_subst_eventuallyPeriodic`
  (`Proofs/Enumerative/OrdinaryIntegralEGFComposition.lean`).

This card restates both parts of the conjecture in the house format and
discharges them from those theorems; it contains no `sorry`.

Computational re-validation (2026-10-21, Python, exact integers): for
`G ∈ {1/(1-x), x, ∑ (-1)^m (m+1) x^m, ∑ (m²-3) x^m, ∑ F_m x^m}`, every
`1 ≤ k ≤ 40`, and `60 ≤ n ≤ 200 - φ(k)`, `b(n + φ(k)) ≡ b(n) (mod k)`.
-/
import Mathlib
import Enumerative.Fubini
import Enumerative.FubiniMod
import Enumerative.OrdinaryIntegralEGF
import Enumerative.OrdinaryIntegralEGFComposition

set_option autoImplicit false

namespace Candidates.A000670FubiniModEventually

open A051293

/-! ## Definition layer

* `A051293.fubini : ℕ → ℕ` (`Proofs/Enumerative/Fubini.lean`), the OEIS
  recurrence `a(0) = 1`, `a(n) = ∑_{j<n} C(n,j) a(j)`, reused verbatim.
* `egfCompExpSubOne G`, the formal composition `G(exp(x) - 1)` over `ℚ` of an
  integral power series `G : PowerSeries ℤ`; the "integer sequence having
  e.g.f. `G(exp(x)-1)`" is a `b : ℕ → ℤ` with `b n = n! · [xⁿ] G(exp(x)-1)`. -/

/-- The formal power series `G(exp(x) - 1)` over `ℚ`, for an integral power
series `G`, defined by genuine formal substitution (the inner series has zero
constant term, so the substitution is well defined). -/
noncomputable def egfCompExpSubOne (G : PowerSeries ℤ) : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.exp ℚ - 1) (PowerSeries.map (Int.castRingHom ℚ) G)

/-! ## Ground truth -/

-- the first listed terms of A000670
example : fubini 0 = 1 ∧ fubini 1 = 1 ∧ fubini 2 = 3 ∧ fubini 3 = 13 ∧
    fubini 4 = 75 ∧ fubini 5 = 541 :=
  ⟨fubini_zero, fubini_one, fubini_two, fubini_three, fubini_four, fubini_five⟩

-- Bala's mod-16 example: residues `1, 1, 3, 13, 11, 13` of `a(0..5)`
example : fubini 0 % 16 = 1 ∧ fubini 1 % 16 = 1 ∧ fubini 2 % 16 = 3 ∧
    fubini 3 % 16 = 13 ∧ fubini 4 % 16 = 11 ∧ fubini 5 % 16 = 13 := by
  rw [fubini_zero, fubini_one, fubini_two, fubini_three, fubini_four, fubini_five]
  decide

/-- The geometric input `G = 1/(1-x) = ∑ xᵐ` recovers the first Fubini
numbers `1, 1, 3, 13` as factorial-scaled coefficients of `G(exp(x)-1)`
(the Fubini e.g.f. `1/(2 - exp x)`). -/
theorem factorial_mul_coeff_egf_geometric_eq (n : ℕ) (hn : n ≤ 3) :
    (n.factorial : ℚ) * PowerSeries.coeff n
        (egfCompExpSubOne (PowerSeries.mk fun _ => 1)) = (fubini n : ℚ) := by
  rw [egfCompExpSubOne, OrdinaryIntegralEGF.factorial_mul_coeff_subst_exp_sub_one]
  interval_cases n
  · rw [fubini_zero]; decide
  · rw [fubini_one]; decide
  · rw [fubini_two]; decide
  · rw [fubini_three]; decide

/-! ## The conjecture, part 1: Fubini numbers -/

/-- **Bala's conjecture, Fubini part (A000670, Peter Bala, Jul 08 2022).**
For every positive integer `k`, the sequence `a(n) mod k` of Fubini numbers is
eventually periodic with a period `P` dividing `φ(k)`: there are a threshold
`N` and a period `0 < P ∣ φ(k)` with `a(n + P) ≡ a(n) (mod k)` for all
`n ≥ N`.  Proved (Poonen 1988); discharged from
`A000670.fubini_mod_eventuallyPeriodic_conjecture`. -/
theorem fubini_mod_eventually_periodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD k] :=
  A000670.fubini_mod_eventuallyPeriodic_conjecture k hk

/-! ## The conjecture, part 2: e.g.f.s of the form `G(exp(x) - 1)` -/

/-- **Bala's conjecture, general part (A000670, Peter Bala, Jul 08 2022).**
Let `G` be an integral power series and let `b : ℕ → ℤ` be an integer sequence
with e.g.f. `G(exp(x) - 1)`, i.e. `b n = n! · [xⁿ] G(exp(x) - 1)` for all `n`.
Then for every positive integer `k`, `b(n) mod k` is eventually periodic with
a period `P` dividing `φ(k)`.  Discharged from
`OrdinaryIntegralEGF.factorial_mul_coeff_subst_eventuallyPeriodic`, using that
such `b` is unique. -/
theorem egf_comp_exp_sub_one_mod_eventually_periodic (G : PowerSeries ℤ)
    (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℚ) = (n.factorial : ℚ) * PowerSeries.coeff n (egfCompExpSubOne G))
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → b (n + P) ≡ b n [ZMOD k] := by
  obtain ⟨c, hc, N, hN⟩ :=
    OrdinaryIntegralEGF.factorial_mul_coeff_subst_eventuallyPeriodic G k hk
  have hbc : ∀ n : ℕ, b n = c n := by
    intro n
    have hq : (b n : ℚ) = (c n : ℚ) := (hb n).trans (hc n).symm
    exact_mod_cast hq
  refine ⟨N, Nat.totient k, dvd_rfl, Nat.totient_pos.mpr hk, fun n hn => ?_⟩
  rw [hbc, hbc, ← ZMod.intCast_eq_intCast_iff]
  exact hN n hn

/-- Non-vacuity of the general part: for every integral `G` an integer
sequence `b` with e.g.f. `G(exp(x) - 1)` exists (the coefficients are
integers), so the hypothesis `hb` is always satisfiable. -/
theorem exists_int_seq_egf_comp_exp_sub_one (G : PowerSeries ℤ) :
    ∃ b : ℕ → ℤ, ∀ n : ℕ,
      (b n : ℚ) = (n.factorial : ℚ) * PowerSeries.coeff n (egfCompExpSubOne G) :=
  ⟨OrdinaryIntegralEGF.weightedStirlingTransform (fun m => PowerSeries.coeff m G),
    fun n => (OrdinaryIntegralEGF.factorial_mul_coeff_subst_exp_sub_one G n).symm⟩

-- joint instantiation of the general part at `G = 1/(1-x)`, `k = 16`
example : ∃ N P : ℕ, P ∣ Nat.totient 16 ∧ 0 < P ∧ ∀ n : ℕ, N ≤ n →
    OrdinaryIntegralEGF.weightedStirlingTransform (fun _ => 1) (n + P) ≡
      OrdinaryIntegralEGF.weightedStirlingTransform (fun _ => 1) n [ZMOD 16] := by
  have h := egf_comp_exp_sub_one_mod_eventually_periodic (PowerSeries.mk fun _ => 1)
    (OrdinaryIntegralEGF.weightedStirlingTransform (fun _ => 1))
    (fun n => by
      rw [egfCompExpSubOne, OrdinaryIntegralEGF.factorial_mul_coeff_subst_exp_sub_one]
      simp only [PowerSeries.coeff_mk])
    16 (by decide)
  exact_mod_cast h

end Candidates.A000670FubiniModEventually
