# T3 — Quadratic-rank lower bound: `s` shears ⇒ deg-2 part is a sum of `≤ s` products

**Goal.** The low-degree lower-bound tool (Strassen base case), where T1's
degree-doubling is useless (it can't tell 1 shear from 2 for a quadratic target).
Generalize `ShearAddition.shear_comp_normal_form` (the `s=1` case) to `s` shears.

**Novelty.** Novel *as formalization* (multiplicative complexity absent from
Mathlib); the statement is folklore "quadratic part has rank ≤ #multiplications".

**Depends on.** `ShearAddition.lean` (base case + infrastructure); ideally shares
the T1 circuit datatype.

## Statement

For a shear circuit `F : k^n → k^n` with `s` shear gates, the degree-2 homogeneous
component of each coordinate lies in the span of `s` fixed **rank-1 quadratics**:
there are linear forms `u_1,v_1,…,u_s,v_s : k^n → k` (one pair per shear) with
```
∀ j, homogeneousComponent 2 (F_j)  ∈  span_k { u_1·v_1, …, u_s·v_s }.
```
Equivalently each coordinate's deg-2 part is a sum of `≤ s` products of linear
forms. **Corollary:** a target map whose deg-2 part is not such a sum needs `> s`
shears (in particular distinguishes `1` vs `≥2` shears — our EC-step regime).

## Proof skeleton

Induction on the gate list.
- **Affine gate** `x ↦ Lx+t`: `homogeneousComponent 2 (F_j ∘ affine)` is a linear
  combination of the previous coordinates' deg-2 parts (affine substitution: deg-2
  part of `g(Lx+t)` = (deg-2 part of `g`) evaluated at the linear part `L`, which
  keeps it in the same span). Span unchanged.
- **Shear gate** `w_l ← w_l + w_i·w_j`: new deg-2 part of coord `l` =
  `(old deg-2 of w_l) + (linear part of w_i)·(linear part of w_j)`. Adds **one** new
  product `u_{new}·v_{new}` to the spanning set; all other coords unchanged. So the
  span grows by ≤ 1 rank-1 quadratic per shear.

Base case `s=1` is exactly `shear_comp_normal_form` (deg-2 part = single product).

## Mathlib pointers

- `MvPolynomial.homogeneousComponent` (extraction of the degree-2 part).
- Linear/`span` machinery for "sum of ≤ s products of linear forms".
- Reuse T1's `Gate`/circuit type so T1 and T3 share the induction scaffold.

## Risks / gotchas

- Choice of invariant: "deg-2 part ∈ span of `s` products of linear forms" vs
  "symmetric-bilinear-form rank ≤ 2s". Prefer the *span-of-products* formulation
  (avoids char-2 pitfalls of symmetric matrices, and matches Strassen directly).
- Affine-substitution behaviour on `homogeneousComponent` needs a small lemma
  (deg-2 part transforms by the linear part only) — likely to be proven fresh.
- This is the most abstract of the tools; T1+T2 already deliver the flagship number,
  so T3 is "companion", not critical path.

## Decisions for USER before committing

1. Worth it now, or defer? T1+T2 give strong numbers; T3's payoff is *low-degree*
   separations (e.g. certifying a specific quadratic map needs ≥2 shears).
2. Full induction over `s`, or just prove `s=2` (enough to exhibit a concrete
   "needs ≥2 shears" quadratic target and validate the framework)?
3. Formalize the general **corollary** ("rank ≥ s+1 ⇒ not realizable with s") as a
   reusable lower-bound lemma, or only the forward normal form?
