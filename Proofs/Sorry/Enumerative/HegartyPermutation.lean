import Enumerative.HegartyPermutation

/-!
# Open obligation for A094870

This quarantine module retains the existing unproved source statement under its original
namespace and header. The production module supplies the definitions and unconditional
proofs; importing production alone does not admit this conjecture. Source quotations,
limitations, and evidence for the statement are retained below and in the production
module's pinned source documentation. No mathematical proof closure is claimed.
## Archived implementation-card crosswalk

Former card `A094870-hegarty.md`: A094870, claim `hegarty-density`, statement size M,
proof difficulty hard; the conjecture is open and proving it remains hard-blocked.
The greedy sequence starts with 1, chooses the least unused positive value, and
forbids arithmetic progressions at equally spaced indices in choice order; it does
not forbid every three-element arithmetic progression in its range. Production
`Proofs/Enumerative/HegartyPermutation.lean` supplies the permutation, AP-avoidance,
and upper-bound infrastructure. Accepted revision
`ce7ab453d8530cbfdd65c41eeb8ea71072f3fc94`, publishing
`Proofs/Enumerative/HegartyThreeEighths.lean` and
`A094870.hegarty_three_eighths : ∀ n, 3 * (n + 1) ≤ 8 * A094870.a n`.
Thus the source's `3/8 ≤ a(N)/N < 3/2` is available, not merely the older `1/4`
bound used in the nonvacuity paragraph below. The remaining numerical-evidence-only
limit conjecture is exactly `conj_3_2` with denominator `n+1`, never `n`.
-/

set_option autoImplicit false

namespace A094870

/-- **Hegarty, Conjecture 3.2** = the OEIS comment "Conjecture: lim_{n->infinity} a(n)/n = 1
(P. Hegarty)", 0-indexed: `a n / (n + 1) → 1`, where `a n = A094870(n+1)` so that `(n : ℝ) +
1` is the OEIS index.  Hegarty writes of it: "We have no idea how one might prove this - our
only real evidence is numerical."

**Status: open.**  This is the single intended `sorry` of the file.  It is not vacuous: by
`ratio_mem_Ico` the sequence `a n / (n + 1)` is confined to `[1/4, 3/2)` for every `n`, so
the assertion is that a bounded sequence bounded away from `0` converges to the specific
interior point `1`. -/
theorem conj_3_2 :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 1) := by
  -- intended sorry: open conjecture (Hegarty, Conjecture 3.2; OEIS A094870 comment 2).
  sorry

end A094870
