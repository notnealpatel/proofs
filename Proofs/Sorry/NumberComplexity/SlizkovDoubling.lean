import NumberComplexity.SlizkovDoubling

/-!
# Archived open admission: slizkov_doubling_gap

The original admission is relocated unchanged from `NumberComplexity.SlizkovDoubling`.
The proved definitions, engines, special cases, and ground checks remain there.
This module is not imported by production.
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
* it is *sharp*: at each listed A230528 term the deficit is at least `1` by
  that entry's definition, and exactly `1` since a larger deficit would answer
  the entry's question (posed as open) — so the conjectured bound is attained
  with equality there and cannot be strengthened to `l k ≤ l (2 * k)`;
* it is kernel-verified for `0 < k ≤ 7` with room to spare
  (`slizkov_of_le_seven`) and computationally verified for `k ≤ 50000`
  (tier-2 section);
* a refutation is exactly a Slizkov witness (`slizkov_witness_iff`), which by
  the tier-2 search must have `k > 50000` — the project's witness-first
  epistemics would want the two explicit chains.

The guard `0 < k` keeps the statement off the junk value `l 0 = 0` (the
`k = 0` instance is junk-true, not evidence). -/
theorem slizkov_doubling_gap (k : ℕ) (hk : 0 < k) : l k ≤ l (2 * k) + 1 := by
  -- intended sorry: open question (card A230528-slizkov-doubling; ROUTE: none
  -- known — the entry offers only the seven deficit-1 terms as evidence, and
  -- a refutation would be an explicit chain pair at some k > 50000).
  sorry

end NumberComplexity
