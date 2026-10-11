import NumberComplexity.SlizkovDoubling

/-!
# Archived open admission: slizkov_doubling_gap

The original admission is relocated unchanged from `NumberComplexity.SlizkovDoubling`.
The proved definitions, engines, special cases, and ground checks remain there.
This module is not imported by production.
## Retired implementation card: A230528-slizkov-doubling

The former card tracked Slizkov's open question as hard-blocked and
counterexample-searchable, with no search dispatched. Its truncated-natural
subtraction notation is represented here by the equivalent positive-domain
additive inequality, not by an assertion about an unguarded junk value.
Retirement records the implemented admission boundary, not a proof.

`TwoBitAdditionChain` proves exact shortest lengths for every positive input
of binary weight at most two. Production `SlizkovDoubling` consequently proves
`l_two_mul_eq_add_one_of_binaryWeight_le_two` on that infinite family, as well
as the elementary append-a-doubling upper bound. These do not resolve arbitrary
binary weight. The scan through `k = 50000` is computational evidence only,
not a kernel-checked exclusion range. Any counterexample must have certified
optimal lengths: exhibiting two chains alone does not certify their minima.
The remaining alternatives are a structural general bound or such an optimality
certificate; neither is supplied by this archive.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- **Slizkov's question** (OEIS A230528 comment, Alexey Slizkov, 2024-01-20:
"Can the shortest addition chain for 2*k be shorter than one for k by more
than 1?") — archived as the conjecture that the answer is *no*, in additive
form (never `Nat` subtraction): for `0 < k`, `l k ≤ l (2 * k) + 1`.  OPEN,
intended `sorry`.

Status of the statement, per the pulled entries and the tier-2 search:

* it is *nontrivial*: it does not follow from tier 1, which bounds the
  opposite difference, and `l (2 * k) < l k` genuinely happens — smallest at
  `k = 375494703` (A230528; external, far beyond kernel range);
* the entry reports deficit-one terms. These are external evidence of
  sharpness if their optimal lengths are certified; openness of the question
  is not itself a proof that every reported deficit is exactly one;
* it is kernel-verified for `0 < k ≤ 7` with room to spare
  (`slizkov_of_le_seven`) and computationally verified for `k ≤ 50000`
  (tier-2 section, not a kernel-checked exhaustive theorem);
* a refutation is exactly a Slizkov witness (`slizkov_witness_iff`). The
  tier-2 scan reports none through `50000`; any proposed refutation needs
  certified optimal lengths, not merely two explicit chains.

The guard `0 < k` keeps the statement off the junk value `l 0 = 0` (the
`k = 0` instance is junk-true, not evidence). -/
theorem slizkov_doubling_gap (k : ℕ) (hk : 0 < k) : l k ≤ l (2 * k) + 1 := by
  -- intended sorry: open question; the entry reports deficit-one terms.
  -- The external scan reports no witness through 50000, not a kernel-checked
  -- exclusion. A refutation requires certified optimal lengths, or sufficient
  -- certified lower and upper bounds, not merely an explicit chain pair.
  sorry

end NumberComplexity
