import GroupCount.SubgroupCountSn

/-!
# Unproved obligations associated with `GroupCount.SubgroupCountSn`

This archive imports the proved production layer; production does not import this archive.
The declarations below preserve the original names, types, and source provenance.
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
