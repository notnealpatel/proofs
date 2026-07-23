# T1 — Degree doubling: `s` shears ⇒ total degree `≤ 2^s`

**Goal.** The enabling engine for all lower bounds. A reversible circuit built from
`s` multiply-add shears interleaved with affine maps produces coordinate
polynomials of total degree `≤ 2^s`.

**Novelty.** Novel *as formalization* (Mathlib has no arithmetic-circuit/degree-of-
composition machinery); the math is the standard straight-line-program degree bound.

**Depends on.** A degree-under-`aeval` lemma that is **missing from Mathlib**.

## Statements

Model a circuit over `k^n` (use `MvPolynomial (Fin n) k` for coordinate polys).

**(A) The missing Mathlib lemma (reusable, upstreamable):**
```
theorem totalDegree_aeval_le {σ τ : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    (aeval f p).totalDegree ≤ p.totalDegree * ⨆ i ∈ p.vars, (f i).totalDegree
```
(or the cleaner uniform-bound form: if `∀ i, (f i).totalDegree ≤ D` then
`(aeval f p).totalDegree ≤ D * p.totalDegree`).

**(B) Circuit degree bound (the target):**
For a shear circuit `F : (Fin n → k) → (Fin n → k)` with `s` shear gates, each
coordinate polynomial `F_j ∈ MvPolynomial (Fin n) k` has `totalDegree ≤ 2^s`.

## Proof skeleton

- **(A)** `aeval f p = Σ_{m ∈ p.support} C (coeff m p) * Π_i (f i)^(m i)`. Bound each
  summand with `totalDegree_mul`/`totalDegree_prod`/`totalDegree_pow`:
  `deg ≤ Σ_i m i · D = D · |m| ≤ D · totalDegree p`; then `totalDegree_finset_sum`.
  Building blocks present: `totalDegree_add`, `totalDegree_mul`, `totalDegree_pow`,
  `totalDegree_smul_le`. Likely-missing helpers to assemble: `totalDegree_prod`,
  `totalDegree_finset_sum` (confirm; else induct).
- **(B)** Represent a circuit as a `List Gate`, `Gate := affine (LinearMap+const) |
  shear (i j l : Fin n)` (coord `l ← coord l + coord i * coord j`). Track
  `D := max_j (F_j).totalDegree`. Affine gate: composition with a degree-≤1 map, so
  by (A) `D ↦ ≤ D`. Shear gate: new `F_l = F_l + F_i·F_j`, `totalDegree ≤ max(D, 2D)
  = 2D`. Induction on the gate list with `s` = number of shear gates ⇒ `D ≤ 2^s`
  (start `D=1`, identity coords).

## Risks / gotchas

- Circuit datatype choice governs induction cleanliness (`List Gate` vs inductive
  `ShearCircuit`). Keep gates acting on named coordinates `Fin n`.
- (A) is the real work; do it generally so it upstreams and feeds T3.
- `totalDegree_X = 1` needs `[Nontrivial R]`.

## Decisions for USER before committing

1. Prove the **general** `totalDegree_aeval_le` (reusable, PR-worthy) or a bespoke
   circuit-specific bound? (Recommend general.)
2. Circuit representation: `List Gate` over `Fin n`, or specialize to `n = 3`
   matching `ShearAddition.lean`? General `n` is needed for T2 (inversion wants
   scratch registers).
3. Is the `2^s` bound alone the deliverable, or also prove **tightness** (a circuit
   achieving degree `2^s`, e.g. repeated squaring) to certify it's not improvable?
