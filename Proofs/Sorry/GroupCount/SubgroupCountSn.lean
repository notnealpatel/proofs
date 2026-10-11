import GroupCount.SubgroupCountSn

/-!
# Unproved obligations associated with `GroupCount.SubgroupCountSn`

This archive imports the proved production layer; production does not import this archive.
The declarations below preserve the original names, types, and source provenance.
## Archived implementation-card crosswalk

Former card `A005432-pyber.md`: A005432, claim `pyber-subgroup-growth`, statement
size M, proof difficulty hard. Mathematical status: published theorem, not an
open conjecture; its proof remains unformalized. The count is of distinct
subgroups of `S_n`, with conjugate subgroups counted separately. Production
`Proofs/GroupCount/SubgroupCountSn.lean` defines `numSubgroupsSymm` and the exact
asymptotic predicates; the historic name `pyber_conjecture` is retained here.
The target is `log₂ a(n) = n²/16 + o(n²)`. Roney-Dougal–Tracey (2025),
arXiv:2503.05416, Theorem 1, gives stronger bounds
`2^(n²/16 + α n log n) ≤ a(n) ≤ 2^(n²/16 + β n^(3/2))`
for absolute constants `α > 0` and `β` and every `n > 1`.
`GroupCount.PyberConjecture.of_roneyDougalTracey` proves only the reduction from
that stronger statement. Its finite-group enumeration and asymptotic estimates
are still needed for a Lean proof; publication alone does not discharge this admission.
-/

set_option autoImplicit false

namespace GroupCount

/-- **The A005432 growth rate — archived, not proved here.**  The OEIS comment reads

> `L. Pyber shows c^(n^2(1+o(1))) <= a(n) <= d^(n^2(1+o(1))), c=2^(1/16), d=24^(1/6);`
> `conjectures lower bound is accurate.`

and this declaration archives the last clause: the number of subgroups of `Sₙ` is
`2^((1/16 + o(1)) n²)`.  **This is not an open problem.**  Pyber conjectured it in 1993;
Roney-Dougal and Tracey proved it in 2025 (arXiv:2503.05416, Theorem 1), in the stronger
form recorded as `GroupCount.RoneyDougalTraceyBound`.  The `sorry` records that their proof
is not formalized here — and `GroupCount.PyberConjecture.of_roneyDougalTracey` shows that
formalizing Theorem 1 would discharge it.  This is the only `sorry` in the file. -/
theorem pyber_conjecture : PyberConjecture := by
  sorry

end GroupCount
