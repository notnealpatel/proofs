import Sorry.Quarantine.Enumerative.ZumkellerSigmaHalf

/-!
# Archived Ianakiev sigma-half conjecture (OEIS A083207)

Ivan N. Ianakiev, OEIS A083207, Apr 03 2017, conjectured that among every four
consecutive terms of the increasing Zumkeller sequence some term has Zumkeller
half-sigma. Retired implementation card
`Formalize/A083207-ianakiev-sigma-half.md` classified this as open,
with hard-blocked work and no known proof route. Reported verification of the first
`10^5` terms is finite evidence, not a kernel proof of the universal claim.

The exact existing proposition `IanakievSigmaHalf` is reused: for every natural
index `i` there are `j < 4` and a natural `m` such that
`2*m = ∑ d ∈ (Nat.nth IsZumkeller (i+j)).divisors, d` and `IsZumkeller m`.
These are four consecutive sequence terms, not four consecutive integers; exact
halving is expressed by multiplication, not truncated natural division.
`Enumerative.ZumkellerSigmaHalf` proves `infinite_setOf_isZumkeller`, removing the
`Nat.nth` junk-value concern, pins the first terms, and proves the published
Bhaskara Rao–Peng characterization for practical numbers. Defining the proposition
and establishing these prerequisites do not prove the conjecture.

The missing mechanism is a distribution theorem for Zumkeller numbers and their
half-sigma values beyond the finite verification. This USER-authorized `sorry` is
an archive-only statement interface, not a proof. Card retirement records statement
implementation, not mathematical closure.
-/

set_option autoImplicit false

/-- Ianakiev's conjecture: every four-term window in the increasing Zumkeller
sequence contains a term with Zumkeller half-sigma. This explicitly admitted archive
interface reuses `IanakievSigmaHalf` without changing its quantifiers. -/
theorem ianakiev_sigma_half : IanakievSigmaHalf := by
  sorry
