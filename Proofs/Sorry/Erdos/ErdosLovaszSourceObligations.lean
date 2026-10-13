/-!
# A391599: Erdos-Lovasz residual

DOCUMENTATION ONLY: no imports, executable declarations or admissions.
The preserved passage is the complete A391599 residual from Formalize/INDEX.
Current evidence was read from Proofs/Erdos/ErdosLovasz.lean. Sources there
include OEIS A391599 / Erdos Problem 21, Erdos-Lovasz (1975), Tripathi (2014),
Sivashankar (2026), and Barat/Wanless. For positive uniformity n, g(n) is the
minimum edge count of an n-uniform intersecting hypergraph with transversal
number n. Equivalently every set of size at most n-1 misses a family member.
It is not the minimum size of a maximal intersecting family.

Production proves the first four values, in particular g(4) = 9 from the
universal nine-edge lower bound and explicit upper witness. It also proves
the classical (8/3)n - 3 lower bound via ErdosLovaszLower.lean. These results
do not discharge the archived literature admissions now quarantined in
Sorry/Erdos/ErdosLovasz.lean: Sivashankar's positive-n 3n - 4 lower bound and eventual
((41-sqrt(19))/12 - epsilon)n lower bound for every epsilon > 0, Barat's
g(5) = 13 and g(6) <= 18. The same header also records the separate Kahn
linear upper-bound admission; derived consequences inherit those dependencies.
These statements and their dependent consequences live in the commensurate
quarantine module, not in production or in this documentation-only module.
This documentation neither adds admissions nor claims that the
remaining peeling, edge-colouring, extremal witnesses or search certificates
are formalized. The completed g(4) lower bound is not a remaining task.

## Formalize/INDEX — complete A391599 residual (verbatim)

```text
- **A391599:** `Proofs/Erdos/ErdosLovasz.lean:tripathi_erdosLovaszNum_four` now proves `g(4) = 9`, using `tripathi_nine_le_erdosLovaszNum_four` and the explicit upper witness. `erdos_lovasz_lower_bound` now also proves the classical `(8/3)n−3` lower bound using `ErdosLovaszLower.lean`. Remaining formalization targets include the Sivashankar lower bounds, `barat_erdosLovaszNum_five`, and `barat_erdosLovaszNum_six_le`. These still have archived `sorry` proofs; do not reassign `9 ≤ g(4)`.
```
-/
