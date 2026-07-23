# T2 — Flagship: clean reversible modular inversion needs `≥ ⌈log₂(p−2)⌉` shears

**Goal.** The headline number. Realizing `x ↦ x⁻¹` over `F_p` with shear gates
(hence the EC-addition slope `λ`) forces `s ≥ ⌈log₂(p−2)⌉`. For secp256k1,
`p−2 ∈ (2^255, 2^256)` ⇒ **`s ≥ 256`**. Explains why reversible EC arithmetic is
inversion-dominated.

**Novelty.** Novel *as formalization*; the bound is the folklore addition-chain /
degree floor `l(n) ≥ log₂ n` (see T5 for the sharper exact `l(p−2)`).

**Depends on.** T1 (degree `≤ 2^s`) + the finite-field degree bridge below.

## Statements

Inversion-with-`1/0:=0` is the total function `invF : F_p → F_p`, `invF = (·)^{p−2}`
(Fermat: `x^{p-1}=1` for `x≠0`, and `0^{p-2}=0`).

**(A) Degree bridge (the content lemma):**
```
theorem natDegree_ge_of_induces_inv {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X])
    (hf : ∀ x : ZMod p, f.eval x = x ^ (p - 2)) : p - 2 ≤ f.natDegree
```
Proof: `f − X^{p-2}` vanishes on all of `ZMod p`, so `(X^p − X) ∣ (f − X^{p-2})`
(vanishing ideal of `F_q` is `⟨X^q − X⟩`). If the difference is `0`,
`natDegree f = p−2`; else it is a nonzero multiple of a degree-`p` poly so
`natDegree ≥ p > p−2`. Either way `≥ p−2`.

**(B) The lower bound (T1 + A):**
If a shear circuit computes `invF` on some coordinate (as a function of the input
variable, scratch fixed), that coordinate's univariate restriction induces
`x^{p−2}`, so by (A) has degree `≥ p−2`; by T1 its total degree `≤ 2^s`. Hence
`2^s ≥ p−2`, i.e. `s ≥ ⌈log₂(p−2)⌉`. Instantiate secp256k1 ⇒ `s ≥ 256`.

## Proof skeleton / Mathlib pointers

- Vanishing lemma: `X^q − X = ∏_{a} (X − a)` over `F_q`; find exact name
  (`FiniteField.X_pow_card_sub_X` / `prod_X_sub_C`-style; **confirm as step 1**).
  Divisibility of a poly vanishing on all points: via that product + `roots`.
- `natDegree (X^{p-2}) = p−2`: `Polynomial.natDegree_X_pow`.
- Univariate restriction of a multivariate coordinate: substitute constants for
  scratch vars (`MvPolynomial.aeval`/`eval`), `totalDegree` bounds univariate
  `natDegree` of the restriction.
- `2^s ≥ N ⇒ s ≥ ⌈log₂ N⌉`: `Nat.le_log2` / `Nat.lt_pow_iff_log_lt` family.

## Risks / gotchas

- **Function-vs-polynomial** is the whole subtlety; (A) is exactly the fix — a
  circuit could use a higher-degree representative, but that only *raises* degree.
- Must define "circuit computes inversion" precisely (agreement as a *function* on
  `F_p`, on one designated coordinate, others = fixed scratch). Pin this before
  proving.
- Number: recompute `⌈log₂(p−2)⌉` in Lean; it is `256` (since `p−2 > 2^255`),
  **not** `254/255`.

## Decisions for USER before committing

1. Scope: prove the general "any shear circuit inducing `x^{p-2}` needs `s≥⌈log₂⌉`",
   or the concrete secp256k1 instance `s ≥ 256`, or both (general + `example`)?
2. Do we commit T1 first (dependency), or state T2 against a `sorry`-stubbed T1
   interface and parallelize?
3. Is the degree floor enough, or do we also want the sharper T5 bridge
   (`= l(p−2)`) — which needs addition-chain machinery and is a bigger lift?
