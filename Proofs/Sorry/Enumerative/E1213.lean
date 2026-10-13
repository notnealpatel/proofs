/-
Erdős Problem #1213 — equal-sum intervals in bounded-gap sequences.

Archive statement: for a,K ≥ 1, a strictly increasing finite integer sequence
starting at a with adjacent gaps at most K and sufficiently large last term
contains two distinct nonempty index intervals with equal sums.

The Erdős problem archive attributes the affirmative result and an exponential
threshold to Hegyvári (1986). The primary Hegyvári text was unavailable. The
production proof uses an independently checked elementary sliding-window and
dyadic-counting route recovered from the secondary public argument in
sweetsky123/erdos-problem-1213; it makes no historical-proof or novelty claim.

The former speculative prefix-pigeonhole sketch is replaced by the checked
route: M = 2^(2K), W = K*M², and X is the sum of the first M entries. Windows
of each length r ≤ M cross levels X+qKr, q < M²/r, with overshoot less than Kr.
Their sums lie in [X,X+W). Dyadic blocks give strictly more than W slots.
Equal sums in different slots have different lengths, so their nonempty
endpoint intervals are distinct. The last-term threshold a₀*64^K ensures the
needed crossings. Prefix-only monotonicity guards every adjacent Nat gap;
0 < s guards the predecessor s-1. Both original theorem contracts are preserved.

All definitions and theorems now live in Enumerative.E1213 under the unchanged
ErdosCandidates.E1213 namespace. This compatibility archive imports them rather
than redeclaring or admitting them.
-/
import Enumerative.E1213

set_option autoImplicit false

namespace ErdosCandidates.E1213

/-- The original archive's length-five concrete interval witness. -/
example : HasEqualIntervalSums (fun t => t + 1) 5 := by
  refine ⟨0, 1, 2, 2, by omega, by omega, by omega, by omega, by decide, ?_⟩
  decide

end ErdosCandidates.E1213
