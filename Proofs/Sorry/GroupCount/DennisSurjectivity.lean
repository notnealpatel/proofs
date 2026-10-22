import Sorry.Quarantine.GroupCount.DennisSurjectivity

/-!
# Unproved obligations associated with `GroupCount.DennisSurjectivity`

This archive imports the proved production layer; production does not import this archive.
The declarations below preserve the original names, types, and source provenance.
## Archived implementation-card crosswalk

Former card `A046057-dennis-surjectivity.md`: A046057, R. Keith Dennis's open
surjectivity conjecture; proof work remains hard-blocked. The exact target is
`∀ n ≥ 1, ∃ m, gnu m = n`. Production
`Proofs/GroupCount/DennisSurjectivity.lean` pins the least witnesses for 1 and 2.
A053403 records 508 not-yet-realized candidate values in its search, with largest
listed term 55487; neither value is a certified obstruction to surjectivity.
Accepted main `4b6938dc2aa2fb5655f22433f2aeee02bf2377b3` publishes the full Hölder
`pq` formula `GroupCount.gnu_mul_primes` in `Proofs/GroupCount/HolderPQ.lean`.
It realizes a structured family only: characterize that family's values and
construct every remaining positive value to solve the conjecture. The existing
classification prerequisite is not a proof of Dennis surjectivity.
-/

set_option autoImplicit false

namespace GroupCount

/-- **Dennis's gnu-surjectivity conjecture** — OEIS A046057, first comment
(pulled live): "R. Keith Dennis conjectures that there are no 0's in this
sequence", the sequence being "Smallest order m > 0 for which there are n
nonisomorphic finite groups of order m, or 0 if no such order exists."
Equivalently: every positive integer is the number of groups of some order —
`gnu` is surjective onto the positive integers.  **OPEN**; this is the file's
single intended `sorry`.

Status, per the live entries:

* realized in the imported production module: `n = 1` (`GroupCount.exists_gnu_eq_one`)
  and `n = 2` (`GroupCount.exists_gnu_eq_two`);
* the companion A053403 records the search evidence (see the module docstring):
  conjecturally only finitely many candidate values are unaccounted for — 508
  known, the largest being `55487` — and if `55487` really is the largest, `gnu`
  takes all positive integer values;
* A046057 carries keyword `hard`, and even single values are open:
  `a(33) > 30500` (Muniru A Asiru's comment on the entry).

The hypothesis `1 ≤ n` restricts to the intended domain: `n = 0` is realized
only by the junk order `0` (`gnu 0 = 0`; see the ground-truth section), which
the OEIS name excludes by "order m > 0".  No `1 ≤ m` guard is needed on the
witness: by `GroupCount.one_le_of_one_le_gnu` any witness for `1 ≤ n` is
automatically positive. -/
theorem dennis_gnu_surjective (n : ℕ) (hn : 1 ≤ n) : ∃ m : ℕ, gnu m = n := by
  -- intended sorry: open conjecture (card A046057-dennis-surjectivity).
  -- ROUTE: the literature realizes values through Hölder-type classification
  -- formulas for gnu at orders p·q^k. The pq case is formalized in HolderPQ;
  -- it does not supply all positive values or prove the full conjecture.
  sorry

end GroupCount
