import Sorry.Quarantine.NumberComplexity.KnuthStolarsky

/-!
# Archived open admission: knuth_stolarsky

The original admission is relocated unchanged from `NumberComplexity.KnuthStolarsky`.
The proved definitions, engines, special cases, and ground checks remain there.
This module is not imported by production.
## Retired implementation card: A003313-knuth-stolarsky

Card metadata: OEIS A003313; claim `knuth-stolarsky-lower-bound`; mathematical
status open; statement size M; proof difficulty hard. Source: Achim
Flammenkamp's 2016-10-26 comment, attributing the conjecture to D. E. Knuth,
K. Stolarsky et al. Retiring the card records statement implementation only.
The arbitrary-binary-weight inequality remains unproved.

The actual shortest-length API is `NumberComplexity.l`, the minimum of
`chainSteps` over `AdditionChain n`, built from `IsAddChain`; summands may
coincide. `l_eq_lAsc` reconciles this permissive predicate with ascending
chains. There is no `Nat.addChainLength` API. Binary weight is OEIS A000120.
The positive-input guard matches the original offset.

Both `knuth_stolarsky_of_binaryWeight_le_two` and
`knuth_stolarsky_of_le_sixteen` are proved in the production module itself;
the former uses the small-step lower bound, not exact two-bit lengths.
`TwoBitAdditionChain` imports `KnuthStolarsky` in the opposite direction and
separately proves `l_two_pow_add_two_pow`. That exact result feeds Slizkov,
not these partial bounds. Flammenkamp/Clift exhaustive chain tables are
external finite evidence, not the unrestricted theorem.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- **The Knuth–Stolarsky conjecture** (OEIS A003313, comment of Achim
Flammenkamp, Oct 26 2016, attributing it to D. E. Knuth, K. Stolarsky et al.;
first stated in a different form by Stolarsky 1969, Lemma 10) — OPEN:

`floor(log_2 n) + ceiling(log_2 (v n)) ≤ l n` for every `n ≥ 1`,

where `l` is A003313, the shortest-addition-chain length, and `v` is A000120, the
binary weight.  The guard `0 < n` keeps `Nat.log`, `Nat.clog` and `l` off their
junk values at `0` and matches the A003313 offset `1`.

Known: Schönhage 1975 proved the approximation
`l n ≥ log₂ n + log₂ (v n) − 2.123164629…`; Thurber 1973 proved the conjecture
for `v n ≤ 16` (Clift extended this to `v n ≤ 128` by November 2023); Clift
verified it for all `n ≤ 2 ^ 64` (October 2008) and for all `n` with
`l n − ⌊log₂ n⌋ ≤ 5` (September 2019).  Proved here without hypothesis for
`v n ≤ 2` (`knuth_stolarsky_of_binaryWeight_le_two`) and for `n ≤ 16`
(`knuth_stolarsky_of_le_sixteen`), and shown sharp on `3 * 2 ^ m`
(`knuth_stolarsky_eq_three_mul_two_pow`). -/
theorem knuth_stolarsky (n : ℕ) (hn : 0 < n) :
    Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ l n := by
  -- intended sorry: open conjecture (card `Formalize/A003313-knuth-stolarsky.md`).
  -- Confirmed open as of the 2026-08-05 pull of Flammenkamp's page quoted in the
  -- module docstring; the July 2024 Clift disproof recorded there refutes the
  -- adjacent Scholz-Brauer equality, not this bound.
  sorry

end NumberComplexity
