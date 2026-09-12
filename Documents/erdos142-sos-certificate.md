# Erdős #142: exact `N = 9` SOS certificate

## Status

Here `r_3(N)` is the maximum size of a subset of `{0, ..., N-1}` containing no nonconstant three-term arithmetic progression.  The known finite value is

```text
r_3(9) = 5.
```

`Programs/Erdos142/3ap-sos-N9-degree4-exact.json` records an exact degree-four quotient-Gram certificate for the upper bound.  Its matrix entries are integers divided by the common denominator `20000000`; this is a compact encoding of the exact rational matrix, not floating-point data.  For the vector `v` of the 46 progression-free squarefree monomials of degree at most two, the verifier establishes in the Boolean/AP quotient

```text
5 - (x_0 + ... + x_8) = v^T Q v,
```

and proves `Q` positive semidefinite by an exact rational congruence followed by an exact `LDL^T` decomposition with four kernel columns and 42 strictly positive pivots.  It checks all 165 surviving quotient coefficients and all 169 valid Boolean assignments.  The four size-five assignments in the certificate establish the matching lower bound.

Run the verifier from any working directory; it locates the JSON relative to its own path.  A bounded, single-BLAS-thread invocation is:

```sh
env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  BLIS_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1 \
  timeout 60 sage Programs/Erdos142/verify_3ap_sos_n9.sage
```

The verifier uses exact Sage rationals throughout and has no reconstruction, SDP solver, or numerical-tolerance dependency.

## Proper-affine-window comparison

`Programs/Erdos142/verify_affine_lp_n9.sage` gives a separate exact operational comparison.  It enumerates the 85 proper affine windows in `{0, ..., 8}` of lengths one through eight, verifies the local capacities

```text
[1, 2, 2, 3, 4, 4, 4, 4],
```

and checks matching rational primal and dual certificates of value five.  The primal covers `{0, ..., 7}` once and `{8}` once, at costs four and one.  The dual is the indicator of the progression-free mask `355`.  Thus the exact local LP optimum is also five: the SOS certificate does **not** beat this comparator.  Its role here is only to preserve the capability to certify the same bound by a global exact degree-four SOS identity.  The LP certificate and SOS identity remain different kinds of information.

Run it with:

```sh
timeout 60 sage Programs/Erdos142/verify_affine_lp_n9.sage
```

## Scope

This is an exact computational certificate, not a Lean theorem and not a novelty claim.  It makes no asymptotic claim about Erdős #142.  A dense `N = 18` experiment reached approximately 11 GiB of memory; that attempt is not preserved here and should not be read as a scaling recommendation.

## Completed bounded proper-affine baseline (N = 20, 24, 32, 40)

I inspected the exact report `/tmp/r3-proper-affine-baseline-N20-24-32-40.json` and its verification output `/tmp/verify_r3_proper_affine_baseline.out`.  The all-proper-affine LP runs use Dybizbanski's exact capacities and finish with matching integer primal/dual objectives:

| N | windows | exact opt. | dual cost `r_3(N-1)+1` | exact `verifiedAPfree` witness |
|---:|---:|---:|---:|---|
| 20 | 553 | 9 | 8 + 1 = 9 | `{0,2,5,6,11,13,14,18,19}` |
| 24 | 843 | 10 | 9 + 1 = 10 | `{0,1,5,6,8,13,17,19,22,23}` |
| 32 | 1636 | 13 | 12 + 1 = 13 | `{0,1,4,6,9,10,13,21,23,24,28,30,31}` |
| 40 | 2722 | 15 | 14 + 1 = 15 | `{0,2,3,5,9,11,12,14,27,29,30,32,36,38,39}` |

For each row, the dual is the prefix `[0,N-1)` constraint with capacity `r_3(N-1)`, plus the final singleton constraint of cost 1.  The report and verifier explicitly check each displayed witness as `verifiedAPfree`, all proper-affine constraints over exact `QQ`, and equality of primal and dual objectives.  Hence adding valid constraints to this sparse model cannot beat the displayed witness at these four N.  No claim is made about possible sparse-model improvement at other N.  SDP was skipped, and this screen was stopped per plan.

This is a completed bounded computational experiment, using exact external arithmetic; it is not a Lean certificate or a novelty claim.
