import Enumerative.ZumkellerTauSigma

/-!
# Archived open admission

The attributed declaration below is relocated verbatim from `Enumerative.ZumkellerTauSigma`.
Its intended `sorry` is not a proof; production retains the independent results,
concrete witnesses, and explicitly hypothesis-parameterized conditional statements.
References to results above or below in the original attribution refer to production.

## Retired implementation card: Ianakiev tau-sigma (A083207)

Ivan N. Ianakiev's OEIS comment of 2020-04-24 asks exactly for a Zumkeller
partition when `d > 1`, `d ∣ k`, and `tau(d) * sigma(d) = k`. The exact production
predicates and conditional odd-perfect-number consequence are preserved.
The card was hard-blocked after two proposed routes were refuted: the
hypotheses do not force `6 ∣ k` (counterexample parameter `d = 496`), and a
suitable unitary Zumkeller divisor need not exist (`d = 234`). Neither route
can be revived without a substantive repair. The independently proved
`TauSigmaDominantPrime` necessary bound only excludes a dominant-prime
obstruction; it is not the general divisor-partition theorem. New structural
mathematics is still required. Retirement records a faithful admission, not
closure of the conjecture or its conditional consequences.
-/

set_option autoImplicit false

namespace ZumkellerTauSigma

/-- **Ianakiev's conjecture** (OEIS A083207, comment of 2020-04-24; cf. A331668).
If `d > 1` divides `k` and `τ(d) · σ(d) = k`, then `k` is a Zumkeller number.

The proof is an **intended `sorry`**: this is an open problem, and provably not just a
formalization gap — the odd-perfect reduction at the end of this file
(`not_isSquare_half_sigma_zero_mul_of_perfect`) shows any proof of this statement
settles an open question about odd perfect numbers.  See the module docstring for the
computational evidence (`d ≤ 10⁷`) and for exactly which qualifying `k` the proved
engines above do and do not reach. -/
theorem isZumkeller_of_sigma_zero_mul_sigma_one (d k : ℕ) (hd : 1 < d) (hdk : d ∣ k)
    (hk : ArithmeticFunction.sigma 0 d * ArithmeticFunction.sigma 1 d = k) :
    IsZumkeller k := by
  sorry

end ZumkellerTauSigma
