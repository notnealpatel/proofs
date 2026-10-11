/- Existing archived conjecture/dependent declarations, relocated unchanged.
Production definitions and finite certificates remain in `Erdos.Covering.ErdosMinus2k`. -/
import Erdos.Covering.ErdosMinus2k

/-!
# Retired implementation card: Erdős problem 1142 (A039669)

The exact predicate includes `m > 2` and primality of `m - 2^k` only for
`k ≥ 1` with `2^k < m`; without the first guard, `0, 1, 2` are vacuous solutions.
Production proves all seven memberships and completeness through `10^9`.
The admission is the forward classification; the archived set equality also
uses those proved memberships. `NotTwoPowerPlusPrime` supplies an infinite
complementary family, not global completeness. The primitive-root congruence
reduction used in the finite window is due to Chris Nash (2000). The strongest
citable search bound recorded in this card's OEIS evidence is `2^120`, not the
unreviewed `2^128` forum computation. An unbounded exclusion remains missing.

The consolidated A089654 contract is the odd-row form
`T(n,k) = 2*n + 1 - 2^k`. Production `ErdosRows` proves its exact bridge under
`0 < n`; row zero is empty and vacuously all-prime. The six indices
`{3, 7, 10, 22, 37, 52}` correspond to `{7, 15, 21, 45, 75, 105}`. OEIS A089654
attributes the conjecture to Erdős and records the weaker search bound `2^77`.
The two admission-consuming row classifications reside in
`Sorry.Erdos.Covering.ErdosRows`, not production. This was a hard-blocked card;
retiring both consolidated interfaces is statement implementation, not proof.
-/

set_option autoImplicit false

namespace Erdos.Covering

/-- **Erdős' completeness conjecture for A039669** (OEIS A039669 comment,
pinned 2026-07-30: "Erdős conjectures that these are the only values of
n with this property"; erdosproblems.com #1142: "Are there infinitely
many n (or any n > 105) such that n - 2^k is prime for all 1 < 2^k < n?").

OPEN. INTENDED SORRY — archived conjecture, disclosed in the module
header; it is this file's only `sorry`. The same statement is `sorry`'d
in google-deepmind/formal-conjectures (in the infinitude form, plus the
`2 ^ 44` window); see the module header.

Evidence: `4, 7, 15, 21, 45, 75, 105` are members
(`isAllPrimeMinusPow_4` … `_105`); no other member `m ≤ 10 ^ 9`
(`mem_of_isAllPrimeMinusPow_of_le`, kernel-checked here); no other
member below `2 ^ 44` (Mientka–Weitzenkamp 1969) or below `2 ^ 120`
(Alekseyev, OEIS 2011-12-08); and the number of members up to `N` is
`o(N)` by Vaughan 1973.

ROUTE: see the module header. §5's covering-congruence reduction is the
standard tool applied as far as it goes; it shrinks each finite window
but cannot close the infinite one. -/
theorem erdos_1142 (m : ℕ) (h : IsAllPrimeMinusPow m) :
    m ∈ ({4, 7, 15, 21, 45, 75, 105} : Finset ℕ) := by
  -- intended sorry: open conjecture (Formalize/A039669-erdos-minus-2k.md,
  -- erdosproblems.com #1142).
  sorry

/-- A039669 as a set, granting `erdos_1142`. No new `sorry`;
`sorryAx`-dependent through `erdos_1142`. -/
theorem setOf_isAllPrimeMinusPow_of_erdos_1142 :
    {m : ℕ | IsAllPrimeMinusPow m} = ({4, 7, 15, 21, 45, 75, 105} : Set ℕ) := by
  ext m
  constructor
  · intro h
    have hmem := erdos_1142 m h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [isAllPrimeMinusPow_4, isAllPrimeMinusPow_7, isAllPrimeMinusPow_15,
      isAllPrimeMinusPow_21, isAllPrimeMinusPow_45, isAllPrimeMinusPow_75,
      isAllPrimeMinusPow_105]

/-- The negative answer to the first half of erdosproblems #1142 ("Are
there infinitely many n …?"), granting `erdos_1142`. No new `sorry`;
`sorryAx`-dependent through `erdos_1142`. -/
theorem not_infinite_setOf_isAllPrimeMinusPow_of_erdos_1142 :
    ¬ {m : ℕ | IsAllPrimeMinusPow m}.Infinite := by
  rw [Set.not_infinite, setOf_isAllPrimeMinusPow_of_erdos_1142]
  exact (((((Set.finite_singleton 105).insert 75).insert 45).insert 21).insert 15
    |>.insert 7).insert 4

end Erdos.Covering
