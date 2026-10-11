import GroupCount.Submult

/-!
# Archived Lopes group-count conjecture (OEIS A000001)

Jorge R. F. F. Lopes, OEIS A000001, Apr 21 2024, conjectured
`a(i) * a(j) ≤ a(i*j)` for nonnegative indices. This interface records precisely the
positive-order domain `0 < i`, `0 < j`, with the existing `GroupCount.gnu`, which
counts isomorphism classes of groups of order `n`, not labelled group structures.

Card `Formalize/A000001-lopes-submult.md` classifies the mathematical status as
conjectural and the work as hard-blocked: only the coprime case is proved.
`GroupCount.Submult` proves `mul_gnu_le_gnu_of_coprime` by direct products and records
`2 ≤ gnu 9` and `4 ≤ gnu 36`. The remaining mechanism is a construction injective on
isomorphism classes even when factor orders share primes. Coprime cancellation does
not establish that mechanism, and direct products alone do not supply the injection.

This is a USER-authorized archive-only `sorry` interface, not a proof or closure of
that card. No coprimality hypothesis is added; production is unchanged.
-/

set_option autoImplicit false

namespace GroupCount

/-- Lopes's conjecture: the product of the numbers of group isomorphism classes at
any two positive orders is at most the number at their product order.
This archive admission does not prove the shared-prime case. -/
theorem lopes_submultiplicative {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    gnu i * gnu j ≤ gnu (i * j) := by
  sorry

end GroupCount
