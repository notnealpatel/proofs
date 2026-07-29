# T4 — Ground our formulas in Mathlib's proven EC group law

**Goal.** Prove our ad-hoc `(c,λ)↦(a−c,cλ−b)` step *is* the secp256k1 group operation
on the chord locus, and `c=0 ⟺ Q=−2P` in Mathlib's proven-associative group.
Converts `ShearAddition.lean` from "plausible formulas" to "verified against the
group law." **Zero new math; pure grounding.** Do this first — it's cheap and
cements the foundation for T1–T3.

**Depends on.** Only Mathlib's affine Weierstrass API (all present).

## Setup

`W : WeierstrassCurve F`, `[Field F] [DecidableEq F]`, short form `a₁=a₂=a₃=0`
(secp256k1 = further `a₄=0, a₆=7` over `F=ZMod p`, `Fact p.Prime`). Take
`P=(a,b)` as the **first** summand, `Q=(x,y)` second, chord case `a ≠ x`.

## Correspondence (⚠ `slope` arg order is `(x₁ x₂ y₁ y₂)`)

| Ours | Mathlib term | reduces to (a₁=a₂=a₃=0) |
|---|---|---|
| `λ=(y−b)/(x−a)` | `W.slope a x b y` | `(b−y)/(a−x)=λ` |
| `X=λ²−x−a` | `W.addX a x λ` | `λ²+a₁λ−a₂−a−x → λ²−a−x` |
| `−P=(a,−b)` | `(a, W.negY a b)` | `−b−a₁a−a₃ → −b` |
| `Y=λ(a−X)−b` | `W.addY a x b λ` | `negY(addX)(negAddY) → λ(a−X)−b` |
| `c=a−X` | `a − W.addX a x λ` | — |

## Lemma chain (companion file `Proofs/ShearEC/ShearAdditionEC.lean`)

- `slope_eq`: `x≠a → W.slope a x b y = (y−b)/(x−a)` — `W.slope_of_X_ne (Ne.symm h)`
  (the `@[simp]` chord lemma gives `(b−y)/(a−x)`), sign-flip by `div; ring`.
- `addX_eq`: `W.addX a x ℓ = ℓ^2−x−a` — `simp [addX, h₁, h₂]; ring`.
- `negY_eq`: `W.negY a b = −b` — `simp [negY, h₁, h₃]`.
- `addY_eq`: `W.addY a x b ℓ = ℓ*(a − W.addX a x ℓ) − b` — unfold + `ring`.
- **payoff** `step_is_group_add` (`a≠x`, `hP hQ` nonsingular):
  `some a b hP + some x y hQ = some (addX…) (addY…) _` — this is `Point.add_of_X_ne`
  (`@[simp]`); rewrite to land on our `X,Y`. `nonsingular_add` supplies the witness.
- **fibre** `c_eq_zero_iff_neg` (`a≠x`):
  `a − W.addX a x (W.slope a x b y) = 0 ↔ some a b hP + some x y hQ = -(some a b hP)`.
  (→) `c=0 ⇒ X=a ⇒ Y=−b` (`addY_eq`) ⇒ sum `= some a (negY a b) _ = -(some a b hP)`
  (`neg_some`; witnesses equal by **proof irrelevance**, `Nonsingular` is a `Prop`).
  (←) equal points ⇒ equal x-coords (`Point.some.injEq`) ⇒ `X=a`.
- **corollary** `c=0 ↔ Q=−2P`: `P+Q=−P ↔ Q+P=−P` (`add_comm`) `↔ Q=−P−P`
  (`add_eq_iff_eq_sub`) `↔ Q=−(P+P)`. Use general `AddGroup` lemmas
  (`add_eq_zero_iff_eq_neg`, …).

## Gotchas

1. `slope` args `(x₁ x₂ y₁ y₂)`; needs `[DecidableEq F]`.
2. `Point.add_eq_zero` is **private** → use general `add_eq_zero_iff_eq_neg`.
3. `Nonsingular` is a `Prop` → proof irrelevance equates `some x y h₁ = some x y h₂`.
4. Domain is the **chord** case `a≠x` only (exactly where our shear map lives). The
   `x=a` doubling branch (`slope_of_Y_ne`, `add_self_of_Y_ne`) is out of domain —
   note, don't prove.
5. Formula identities need only `a₁=a₂=a₃=0`; prove general, instantiate secp256k1.

## Decisions for USER before committing

1. Generality: prove over general short-Weierstrass `W` (recommended) then a
   secp256k1 `example`, or straight at `ZMod p`?
2. Do we need actual point witnesses (`Fact p.Prime`, concrete `a,b` on curve) or
   is the abstract `hP hQ`-parametrized form the deliverable?
3. Cite the resulting lemmas from `ShearAddition.lean`'s docstring, or merge the
   companion file into it (it already `import Mathlib`)?
