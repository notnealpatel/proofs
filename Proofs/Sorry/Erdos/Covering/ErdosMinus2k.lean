/- Existing archived conjecture/dependent declarations, relocated unchanged.
Production definitions and finite certificates remain in `Erdos.Covering.ErdosMinus2k`. -/
import Erdos.Covering.ErdosMinus2k

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
