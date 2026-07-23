# Reversible EC arithmetic via the multiply-add shear — formalization seeds

Index for a cluster of candidate Lean targets growing out of one already-built,
compiling file. Read this first; each `T*` note is self-contained but shares the
context below.

## Shared context

- **Prime / curve:** secp256k1, `p = 2^256 − 2^32 − 977`, `E : y² = x³ + 7` over `F_p`.
- **Primitive:** the reversible **multiply-add shear** `M(u,v,w) = (u,v,w+uv)` on
  `k³` (the `F_p`-algebraic analogue of a Toffoli gate; the single nonscalar
  multiplication in the arithmetic-circuit cost model). Affine bijections are free.
- **Already committed & green:** `Proofs/Xlib/ShearAddition.lean`
  (`namespace Xlib.ShearAddition`), providing:
  - `shear : k³ ≃ k³`; `shear_apply`, `shear_eq_add_smul` (rank-1 quadratic bump).
  - `shear_comp_normal_form` — `A₂∘M∘A₁` (affine `Aᵢ`) = affine + a *single* product
    of two affine forms · fixed vector `ℓ` (**the s=1 case of T3**).
  - `shearComp` / `shearComp_bijective_and_normal_form` — composite as an `Equiv`
    (bijection) with that normal form.
  - `no_reversible_clean_shear_addition`, `single_shear_cannot_clean` — one shear
    cannot return the ancilla to `0` (the `(c,λ,0)↦(a−c,cλ−b,0)` target collapses the
    `c=0` fibre, so is non-injective; no bijection realizes it).
  - `ancilla_carries_lambda` — the ancilla is forced injective in `λ` on `c=0`.
  - `singleShear` — the concrete `(c,λ,0)↦(X,Y,λ)` realization.

## The map being studied

Fixed `P=(a,b)`, varying `Q=(x,y)`; slope `λ=(y−b)/(x−a)`, `X=λ²−x−a`,
`Y=λ(a−X)−b`, `c:=a−X`. Step reduces to `(c,λ)↦(a−c, cλ−b)`. Exceptional fibre
`c=0 ⟺ X=a ⟺ Q=−2P` (tangent/doubling degeneracy).

## Mathlib coverage (checked)

- EC affine group law **DONE** over any field incl. **associativity** — ground
  against it (see T4). Never reprove.
- Polynomial automorphisms / tame automorphisms / multiplicative complexity /
  tensor rank / arithmetic circuits — **ABSENT**. Everything here is
  *novel-as-formalization*.
- `MvPolynomial.totalDegree` arithmetic (add/mul/pow/smul) DONE; **degree under
  `aeval`/composition MISSING** (the enabling gap for T1).

## Targets & dependency graph

| Note | What | Novelty | Depends on |
|---|---|---|---|
| T1 | degree-doubling: `s` shears ⇒ coord total degree `≤ 2^s` | novel formalization / known math | the missing `aeval` degree lemma |
| T2 | **flagship:** clean reversible inversion needs `≥ ⌈log₂(p−2)⌉ = 256` shears | novel formalization / known bound | T1 + a finite-field degree bridge |
| T3 | `s` shears ⇒ deg-2 part is sum of `≤ s` products (Strassen base) | novel formalization / folklore | `ShearAddition` (s=1 case) |
| T4 | tie our formulas + `c=0⟺Q=−2P` to Mathlib's proven group law | grounding (0 new math) | Mathlib EC API only |
| T5 | addition chains: bridge `min shears for xⁿ = l(n)`; open conjectures | mixed (bridge novel; conjectures open/research) | T1/T2 |

## Honest meta

None of T1–T5 is **new mathematics**. Value = (a) novel formal infrastructure
Mathlib lacks, (b) grounding our impossibility results in the *real* elliptic
curve. The genuinely open questions these tools *point at* — a nontrivial Toffoli
lower bound for one EC point addition; A230528's gap>1 — are research, not session
deliverables. Recommended order: **T4** (cheap, cements foundations) → **T1→T2**
(the flagship) → **T3** (companion low-degree bound) → **T5** (bridge + context).
