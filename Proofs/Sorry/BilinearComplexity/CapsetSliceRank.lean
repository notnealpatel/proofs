import BilinearComplexity.CapsetSliceRank

/-!
# Archived open admission

The attributed declaration below is relocated verbatim from `BilinearComplexity.CapsetSliceRank`.
Its intended `sorry` is not a proof; production retains the independent results,
concrete witnesses, and explicitly hypothesis-parameterized conditional statements.
References to results above or below in the original attribution refer to production.
-/

set_option autoImplicit false

namespace BilinearComplexity

/-- **Peebles' conjecture** (OEIS A236397 comment, pinned 2026-07-30:
"Peebles conjectures that if n is even, a(n+1) = 2*A090245(n)"; poster
Conjecture 5: "For all even n, 2a_n = c_{n+1}").

OPEN. INTENDED SORRY — archived conjecture, disclosed in the module header.
Evidence: matches all pinned terms — n = 0: 2 = 2·1, n = 2: 8 = 2·4,
n = 4: 40 = 2·20, n = 6: 224 = 2·112. The n = 0 and n = 2 instances are
kernel-verified below. Evenness is load-bearing (n = 3: 20 ≠ 18, n = 5:
96 ≠ 90 on pinned terms), though the identity coincidentally holds at
n = 1 (kernel-verified below). Only 8 terms of A236397 and 7 of A090245
are known; one new term of either sequence tests the conjecture. -/
theorem peebles_conjecture (n : ℕ) (hn : Even n) :
    sunflowerFreeWeight (n + 1) = 2 * capsetNumber n := by
  sorry

end BilinearComplexity
