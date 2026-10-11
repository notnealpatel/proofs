import Enumerative.HegartyPermutation

/-!
# Open obligation for A094870

This quarantine module retains the existing unproved source statement under its original
namespace and header. The production module supplies the definitions and unconditional
proofs; importing production alone does not admit this conjecture. Source quotations,
limitations, and evidence for the statement are retained below and in the production
module's pinned source documentation. No mathematical proof closure is claimed.
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
