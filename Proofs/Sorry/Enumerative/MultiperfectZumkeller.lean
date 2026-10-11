import Enumerative.MultiperfectZumkeller

/-!
# Archived multiperfect-to-Zumkeller conjecture (A007691 → A083207)

OEIS A083207 records A007691 as a conjectured subsequence after its initial `1`.
Card `Formalize/A007691-multiperfect-zumkeller.md` classifies this as an open
conjectural subsequence assertion and the work as hard-blocked. The exact domain is
multiply-perfect natural numbers `n > 1`: the existing `Nat.IsMultiperfect` means
`0 < n` and `n ∣ σ(n)`, and `IsZumkeller` means positivity and a subset/complement
partition of the positive divisors into equal sums. The exclusion of `1` is essential:
`1` is multiply-perfect but not Zumkeller.

`Enumerative.MultiperfectZumkeller` proves the perfect-number slice unconditionally,
including hypothetical odd perfect numbers, the practical-to-Zumkeller realization
bridge, and nine listed examples. `Enumerative.ZumkellerSigmaHalf` supplies the
published Bhaskara Rao–Peng practical-number characterization. The explicit
conditional consequence of Coleman's open conjecture is not a proof of this claim.
The adopted `Enumerative.MultiperfectZumkellerCertificates` also proves only the
positive even `σ(n) = 3*n` and positive `6 ∣ n`, `σ(n) = 4*n` slices.

The missing mechanism is a divisor-partition argument for non-perfect multiperfect
numbers, in particular the unresolved abundancy-at-least-three cases beyond these
slices. This USER-authorized `sorry` is an archive-only statement interface, not a
proof or closure of the card; no practicality or Coleman hypothesis is inserted.
-/

set_option autoImplicit false

namespace Nat

/-- Conjecturally every multiply-perfect number other than the initial `1` is
Zumkeller (OEIS A083207, conjectured A007691 subsequence).
This is an explicit archive admission, not a proof of the non-perfect cases. -/
theorem IsMultiperfect.isZumkeller {n : ℕ} (hm : n.IsMultiperfect) (hn : 1 < n) :
    IsZumkeller n := by
  sorry

end Nat
