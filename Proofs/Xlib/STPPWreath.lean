import Mathlib
import Xlib.TPP
import Xlib.CUCapacity

/-!
# The Simultaneous Triple Product Property and wreath amplification

This file formalizes the **Simultaneous Triple Product Property** (STPP) of
Cohn–Kleinberg–Szegedy–Umans [math/0511460, the definition of
`section:stpp`] — the multi-triple generalization of the Cohn–Umans Triple
Product Property — together with the two pillars that turn it into asymptotic
`ω` bounds:

1. the **STPP capacity inequality** (CKSU `theorem:asi`)
   `∑ᵢ (|Aᵢ|·|Bᵢ|·|Cᵢ|)^{ω/3} ≤ D_ω(H)`, the multi-triple version of CU
   Theorem 4.1 (`Xlib.CUCapacity.capacity_rpow_le_charDegreeSumReal`); and
2. the **wreath-product amplification** of Cohn–Umans
   [math/0307321, the wreath theorem, CU.tex:1248–1255]: for `A = C₂ₙ` cyclic
   of order `2n`, the **imprimitive** wreath product `Gₙ = A ≀ Sₙ = Sₙ ⋉ Aⁿ`
   (`Sₙ` permuting the `n` coordinates of `Aⁿ`, CU.tex:1242–1246), of order
   `|Gₙ| = (2n)ⁿ·n!`, has pseudo-exponent
   `α(Gₙ) ≤ γ(Gₙ) = 2 + (1+log 2)/log n + O(1/(log n)²) → 2`.

This is the **furthest-out, "sorry-skeleton" layer** of the Cohn–Umans program:
the deliverable is *correct type signatures* for the STPP, the wreath
construction, and the pseudo-exponent convergence. The mathematical content of
the inequalities is `sorry`d (each rests on tensor-rank / Schönwage's asymptotic
sum inequality, the wreath character-degree computation via Clifford theory /
Huppert, or the indexed Wedderburn layer — none of which are in Mathlib, and
all of which sit one level below `Xlib.CUCapacity` and `Xlib.CharDegrees`).

## The STPP, precisely (CKSU `section:stpp`)

`n` triples of subsets `(Aᵢ, Bᵢ, Cᵢ)` of a group `H` satisfy the STPP when

* **(per-triple)** for each `i`, `(Aᵢ, Bᵢ, Cᵢ)` satisfies the ordinary TPP; and
* **(simultaneous)** for *all* `i, j, k` and all `aᵢ ∈ Aᵢ`, `aⱼ' ∈ Aⱼ`,
  `bⱼ ∈ Bⱼ`, `bₖ' ∈ Bₖ`, `cₖ ∈ Cₖ`, `cᵢ' ∈ Cᵢ`,
  `aᵢ (aⱼ')⁻¹ · bⱼ (bₖ')⁻¹ · cₖ (cᵢ')⁻¹ = 1` forces `i = j = k`.

The three indices `i, j, k` are **independent** and **cyclically chained**:
the `A`-quotient carries indices `(i, j)`, the `B`-quotient `(j, k)`, the
`C`-quotient `(k, i)`. This "strange condition" (CKSU's phrase) is exactly what
lets `n` independent matrix multiplications be packed into one group-algebra
multiplication; the conclusion only collapses the *indices* (`i = j = k`),
element equality then following from the per-triple ordinary TPP.

## Main definitions

* `Xlib.STPPWreath.SimultaneousTPP` — the STPP predicate on indexed families
  `A B C : Fin n → Finset G`.
* `Xlib.STPPWreath.cyclicGroup` — `C₂ₙ = Multiplicative (ZMod (2n))`, the
  cyclic base group of the Cohn–Umans wreath family.
* `Xlib.STPPWreath.ImprimitiveWreathProduct` — the **imprimitive** wreath product
  `Dⁿ ⋊ Sₙ` (`Sₙ` permuting the `n` coordinates of `Dⁿ` via `σ • f = f ∘ σ⁻¹`),
  built from `Mathlib.GroupTheory.SemidirectProduct`. Its order is `|D|ⁿ · n!`
  (`ImprimitiveWreathProduct.card`). This is the Cohn–Umans wreath group — **not**
  Mathlib's *regular* wreath product `RegularWreathProduct D Sₙ = D^{n!} ⋊ Sₙ`,
  whose order `|D|^{n!} · n!` differs for `n ≥ 3`.
* `Xlib.STPPWreath.wreathGroup` — `Gₙ = C₂ₙ ≀ Sₙ = C₂ₙⁿ ⋊ Sₙ`, the imprimitive
  Cohn–Umans family (`ImprimitiveWreathProduct (cyclicGroup n) n`), with the
  `Fintype` instance that `Xlib.CUCapacity.pseudoExponent` needs.
* `Xlib.STPPWreath.wreathGamma` — `γ(Gₙ) = 2 + (1+log 2)/log n`, the leading
  asymptotic bound on the pseudo-exponent.

## Main results (all `sorry`-skeleton)

* `Xlib.STPPWreath.SimultaneousTPP.tpp_of` — the STPP entails the per-index TPP.
* `Xlib.STPPWreath.stpp_capacity_le` — **(`sorry`)** the STPP capacity
  inequality `∑ᵢ (|Aᵢ|·|Bᵢ|·|Cᵢ|)^{ω/3} ≤ D_ω(H)` (CKSU `theorem:asi`).
* `Xlib.STPPWreath.wreath_charDegree_bound` — **(`sorry`)** the wreath
  character-degree bound `∑ⱼ cⱼ^ω ≤ (n!)^{ω-1} · (∑ₖ dₖ^ω)^n` (CKSU
  `lemma:wreath-char-degrees`, via Huppert / Clifford theory).
* `Xlib.STPPWreath.stpp_to_tpp_wreath` — **(`sorry`)** STPP triples in `H` lift
  to ordinary TPP subsets in `Sₙ ⋉ Hⁿ` (CKSU `theorem:STPP2TPP`).
* `Xlib.STPPWreath.pseudoExponent_wreath_le_gamma` — **(`sorry`)** the per-`n`
  pseudo-exponent bound `α(Gₙ) ≤ γ(Gₙ)` (CU wreath theorem).
* `Xlib.STPPWreath.pseudoExponent_wreath_tendsto_two` — **(`sorry`)** the
  amplification limit `α(Gₙ) → 2` as `n → ∞`.
* `Xlib.STPPWreath.abelian_wreath_family_tendsto_two` — **(`sorry`)** CU
  "Prop 11": for *abelian* `H`, the wreath family `Sₙ ⋉ Hⁿ` drives the
  pseudo-exponent to `2` (the abelian-base case; the non-abelian case is the
  BCGPU open frontier).

## References

* H. Cohn, R. Kleinberg, B. Szegedy, C. Umans, *Group-theoretic Algorithms for
  Matrix Multiplication*, FOCS 2005 [arXiv:math/0511460] (STPP definition
  `section:stpp`; capacity inequality `theorem:asi`; wreath character degrees
  `lemma:wreath-char-degrees`; STPP→TPP `theorem:STPP2TPP`).
* H. Cohn, C. Umans, *A Group-theoretic Approach to Fast Matrix
  Multiplication*, [arXiv:math/0307321] (the wreath theorem `α(Gₙ) ≤ γ(Gₙ)`,
  CU.tex:1248–1255; the abelian/`α>2` lemma, CU.tex:478–499).
-/

open scoped BigOperators

namespace Xlib.STPPWreath

open Xlib.TPP Xlib.CUCapacity Xlib.CharDegrees

/-! ### The Simultaneous Triple Product Property (CKSU `section:stpp`) -/

variable {G : Type*} [Group G]

/-- The **Simultaneous Triple Product Property** (Cohn–Kleinberg–Szegedy–Umans,
[math/0511460, the definition in `section:stpp`]).

The `n` triples of subsets `(A i, B i, C i)` of a finite group `G`
(`A B C : Fin n → Finset G`) satisfy the STPP when:

* **per-triple TPP:** for each index `i`, the triple `(A i, B i, C i)` satisfies
  the ordinary `Xlib.TPP.TripleProductProperty`; and

* **the simultaneous (cyclically-chained) condition:** for all indices
  `i j k : Fin n` and all `aᵢ ∈ A i`, `aⱼ' ∈ A j`, `bⱼ ∈ B j`, `bₖ' ∈ B k`,
  `cₖ ∈ C k`, `cᵢ' ∈ C i`,
  `aᵢ * (aⱼ')⁻¹ * bⱼ * (bₖ')⁻¹ * cₖ * (cᵢ')⁻¹ = 1`  forces  `i = j ∧ j = k`.

The index threading is `(i, j)` on `A`, `(j, k)` on `B`, `(k, i)` on `C`; the
conclusion collapses the indices, and element equality follows afterward from
the per-triple TPP. (In CKSU's additive notation for abelian `G` this reads
`aᵢ - aⱼ' + bⱼ - bₖ' + cₖ - cᵢ' = 0 ⟹ i = j = k`.)

**Orientation note (quotient direction).** The simultaneous condition above uses
the **right** quotients `aᵢ(aⱼ')⁻¹`, `bⱼ(bₖ')⁻¹`, `cₖ(cᵢ')⁻¹`, transcribed
*verbatim* from CKSU's primary definition
[math/0511460, FOCS05-10page.tex:1121–1127] (which fixes `Q(S) = {s₁s₂⁻¹}`, the
right quotient set, at line 363). The ordinary `Xlib.TPP.TripleProductProperty`
invoked in the *per-triple* conjunct instead uses the **left** quotient
`s'⁻¹ * s` — the Murthy/Wikipedia rendering, which `Xlib.TPP` documents as
equivalent to CU's right-quotient `Q(S)` form. The two conjuncts therefore use
different quotient sides, but each is faithful to the orientation of *its own*
source: bullet 1 to CU via the (documented-equivalent) `Xlib.TPP` form, bullet 2
to CKSU verbatim. We keep the right-quotient form here rather than rewriting it
left-handed precisely so that this definition reads identically to the cited
CKSU definition; the right- and left-quotient simultaneous conditions are
equivalent (both are universally quantified over *all* elements of the sets, and
the right quotient set `{xy⁻¹}` is the inverse-image of the left quotient set
`{y⁻¹x}`), so no generality is lost. -/
def SimultaneousTPP {n : ℕ} [Fintype G] [DecidableEq G]
    (A B C : Fin n → Finset G) : Prop :=
  (∀ i, TripleProductProperty (A i) (B i) (C i)) ∧
    (∀ i j k : Fin n,
      ∀ aᵢ ∈ A i, ∀ aⱼ' ∈ A j, ∀ bⱼ ∈ B j, ∀ bₖ' ∈ B k, ∀ cₖ ∈ C k, ∀ cᵢ' ∈ C i,
        aᵢ * (aⱼ')⁻¹ * bⱼ * (bₖ')⁻¹ * cₖ * (cᵢ')⁻¹ = 1 → i = j ∧ j = k)

omit [Group G] in
/-- The STPP entails the ordinary TPP of each individual triple `(A i, B i, C i)`
(the first conjunct). -/
theorem SimultaneousTPP.tpp_of {n : ℕ} [Group G] [Fintype G] [DecidableEq G]
    {A B C : Fin n → Finset G} (h : SimultaneousTPP A B C) (i : Fin n) :
    TripleProductProperty (A i) (B i) (C i) :=
  h.1 i

omit [Group G] in
/-- The simultaneous (cyclically-chained) condition extracted from the STPP
(the second conjunct). -/
theorem SimultaneousTPP.simultaneous {n : ℕ} [Group G] [Fintype G] [DecidableEq G]
    {A B C : Fin n → Finset G} (h : SimultaneousTPP A B C)
    (i j k : Fin n) (aᵢ : G) (haᵢ : aᵢ ∈ A i) (aⱼ' : G) (haⱼ' : aⱼ' ∈ A j)
    (bⱼ : G) (hbⱼ : bⱼ ∈ B j) (bₖ' : G) (hbₖ' : bₖ' ∈ B k)
    (cₖ : G) (hcₖ : cₖ ∈ C k) (cᵢ' : G) (hcᵢ' : cᵢ' ∈ C i)
    (heq : aᵢ * (aⱼ')⁻¹ * bⱼ * (bₖ')⁻¹ * cₖ * (cᵢ')⁻¹ = 1) : i = j ∧ j = k :=
  h.2 i j k aᵢ haᵢ aⱼ' haⱼ' bⱼ hbⱼ bₖ' hbₖ' cₖ hcₖ cᵢ' hcᵢ' heq

/-! ### The STPP capacity inequality (CKSU `theorem:asi`, `sorry`)

The multi-triple analogue of `Xlib.CUCapacity.capacity_rpow_le_charDegreeSumReal`
(CU Theorem 4.1). Whereas the single-triple bound reads
`(|S|·|T|·|U|)^{ω/3} ≤ D_ω(G)`, the STPP packs `n` independent triples into one
group-algebra multiplication, giving a *sum* on the left. -/

/-- **CKSU Theorem `theorem:asi`** [math/0511460]: the **STPP capacity
inequality**. If the `n` triples `(A i, B i, C i)` of a finite group `G` satisfy
the STPP, then

  `∑ᵢ (|A i| · |B i| · |C i|)^{ω/3} ≤ D_ω(G) = ∑ₖ dₖ^ω`.

This is the multi-triple version of CU Theorem 4.1
(`Xlib.CUCapacity.capacity_rpow_le_charDegreeSumReal`). For abelian `G` the
right-hand side collapses to `|G|` (`Xlib.CharDegrees.charDegreeSum_two`), the
form used in the `ω < 2.93` example.

**Proof debt** (CKSU `section:wreath`): pass to the wreath product
`Sₙ ⋉ Gⁿ` via `stpp_to_tpp_wreath` (CKSU `theorem:STPP2TPP`), apply the
single-triple bound CU Theorem 4.1, bound the wreath character degrees with
`wreath_charDegree_bound` (`lemma:wreath-char-degrees`), and take direct powers
and roots through Schönhage's asymptotic sum inequality
((15.11) in Bürgisser–Clausen–Shokrollahi) together with the
geometric-to-arithmetic mean step. None of tensor rank, the asymptotic sum
inequality, or the wreath character-degree computation is in Mathlib. `sorry`. -/
theorem stpp_capacity_le {n : ℕ} [Fintype G] [DecidableEq G]
    (A B C : Fin n → Finset G) (h : SimultaneousTPP A B C) :
    ∑ i, ((A i).card * (B i).card * (C i).card : ℝ) ^ (ω / 3)
      ≤ charDegreeSumReal G ω :=
  sorry

/-! ### The cyclic base group `C₂ₙ` and the imprimitive wreath product `Gₙ = A ≀ Sₙ`

The Cohn–Umans wreath family is the **imprimitive** wreath product `Dⁿ ⋊ Sₙ`,
where `Sₙ = Equiv.Perm (Fin n)` acts on the index set `{0,…,n-1}` — i.e. on the
`n` coordinates of `Dⁿ = (Fin n → D)` — by `σ • f = f ∘ σ⁻¹`. Its order is
`|D|ⁿ · n!`.

This is **not** Mathlib's `RegularWreathProduct D Q = (Q → D) ⋊ Q`, which is the
*regular* wreath product: there `Q` acts on *itself* (`Q = Sₙ` acts on the `n!`
points of `Sₙ`), giving base `D^{|Q|} = D^{n!}` and order `|D|^{n!} · n!`. For
`n ≥ 3` these differ (`n! > n`); the Cohn–Umans construction needs the
imprimitive group, so we build it here from Mathlib's `SemidirectProduct`.

The coordinate-permutation action is packaged as a genuine monoid homomorphism
`σ ↦ (f ↦ f ∘ σ⁻¹)` into `MulAut (Fin n → D)` via `MulEquiv.arrowCongr`. -/

/-- The coordinate-permutation action of `Sₙ = Equiv.Perm (Fin n)` on the
function group `Dⁿ = (Fin n → D)`, as a monoid homomorphism
`Equiv.Perm (Fin n) →* MulAut (Fin n → D)`.

A permutation `σ` is sent to the multiplicative automorphism `f ↦ f ∘ σ⁻¹` of
`Dⁿ` (`MulEquiv.arrowCongr σ (MulEquiv.refl D)`, whose underlying function is
`f ↦ f ∘ σ.symm`). This is a *homomorphism* (not an anti-homomorphism) because of
the inverse: with `Equiv.Perm.mul_apply` (`(σ*τ) x = σ (τ x)`) and
`MulAut.mul_apply` (`(a*b) m = a (b m)`),
`φ(στ) f = f ∘ (στ)⁻¹ = (f ∘ τ⁻¹) ∘ σ⁻¹ = (φ σ * φ τ) f`. -/
def permArrowHom (D : Type*) [Group D] (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (Fin n → D) where
  toFun σ := MulEquiv.arrowCongr (σ : Fin n ≃ Fin n) (MulEquiv.refl D)
  map_one' := by
    ext f i
    simp only [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, MulAut.one_apply,
      Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply]
  map_mul' σ τ := by
    ext f i
    simp only [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, MulAut.mul_apply,
      Equiv.symm_trans_apply, Equiv.Perm.mul_def]

/-- The **imprimitive wreath product** `Dⁿ ⋊ Sₙ` of a group `D` by the symmetric
group `Sₙ = Equiv.Perm (Fin n)`, with `Sₙ` permuting the `n` coordinates of
`Dⁿ = (Fin n → D)` via `permArrowHom` (`σ • f = f ∘ σ⁻¹`).

Realized as a `Mathlib.GroupTheory.SemidirectProduct`, so it inherits `Group`
and `DecidableEq` automatically; its order is `|D|ⁿ · n!`
(`ImprimitiveWreathProduct.card`). This is the Cohn–Umans wreath group, **not**
the regular wreath product `RegularWreathProduct D Sₙ = D^{n!} ⋊ Sₙ`. -/
abbrev ImprimitiveWreathProduct (D : Type*) [Group D] (n : ℕ) : Type _ :=
  SemidirectProduct (Fin n → D) (Equiv.Perm (Fin n)) (permArrowHom D n)

/-- `Fintype` for the imprimitive wreath product `Dⁿ ⋊ Sₙ`, built from the
product representation `(Fin n → D) × Equiv.Perm (Fin n)` via
`SemidirectProduct.equivProd`. (`DecidableEq` is supplied by `SemidirectProduct`'s
`deriving DecidableEq`.) Needed because `Xlib.CUCapacity.pseudoExponent` and
`Xlib.CharDegrees.charDegreeSumReal` are stated with `Fintype`. -/
instance instFintypeImprimitiveWreathProduct {D : Type*} [Group D] [Fintype D]
    [DecidableEq D] (n : ℕ) : Fintype (ImprimitiveWreathProduct D n) :=
  Fintype.ofEquiv _ (SemidirectProduct.equivProd).symm

/-- **The order of the imprimitive wreath product:**
`|Dⁿ ⋊ Sₙ| = |D|ⁿ · n!`.

This is the genuine Cohn–Umans wreath order. The proof chains
`SemidirectProduct.card` (`|N ⋊[φ] G| = |N| · |G|`) with `Nat.card_fun`
(`|Fin n → D| = |D|ⁿ`) and `Nat.card_perm` (`|Equiv.Perm (Fin n)| = (Fin n)! = n!`).
Contrast `RegularWreathProduct.card`, which gives `|D|^{n!} · n!`. -/
theorem ImprimitiveWreathProduct.card (D : Type*) [Group D] [Finite D] (n : ℕ) :
    Nat.card (ImprimitiveWreathProduct D n)
      = Nat.card D ^ n * Nat.factorial n := by
  rw [ImprimitiveWreathProduct, SemidirectProduct.card, Nat.card_fun, Nat.card_perm,
    Nat.card_fin]

/-- The **cyclic group `C₂ₙ`** of order `2n`, the Cohn–Umans wreath base
[math/0307321, CU.tex:1248]. Realized as `Multiplicative (ZMod (2n))` so that it
is a *multiplicative* finite group. The `NeZero (2*n)` instance — equivalently
`0 < n` — makes `ZMod (2n)` a genuine finite cyclic group of order `2n` rather
than `ℤ`. -/
abbrev cyclicGroup (n : ℕ) : Type := Multiplicative (ZMod (2 * n))

/-- The **Cohn–Umans wreath family** `Gₙ = C₂ₙ ≀ Sₙ` [math/0307321,
CU.tex:1248–1255], the **imprimitive** wreath product `C₂ₙⁿ ⋊ Sₙ` (via
`ImprimitiveWreathProduct`). Its order is `(2n)ⁿ · n!`
(`ImprimitiveWreathProduct.card`, with `|C₂ₙ| = 2n`). The pseudo-exponent of this
family converges to `2` (`pseudoExponent_wreath_tendsto_two`). -/
abbrev wreathGroup (n : ℕ) : Type _ :=
  ImprimitiveWreathProduct (cyclicGroup n) n

/-! ### The wreath character-degree bound (CKSU `lemma:wreath-char-degrees`)

The character degrees of `Sₙ ⋉ Hⁿ` are governed by Clifford theory / Huppert's
description (CKSU cite Huppert Theorem 25.6): the irreducibles are indexed by
partitions of `n` decorated by characters of `H`, with dimensions built from
multinomial coefficients and the symmetric-group irrep dimensions. The single
*inequality* the capacity proof needs is the power-sum bound below. -/

/-- **CKSU Lemma `lemma:wreath-char-degrees`** [math/0511460]: the wreath
character-degree power-sum bound. If `H` has character-degree power sum
`D_ω(H) = ∑ₖ dₖ^ω`, then the wreath product `G = Sₙ ⋉ Hⁿ` has

  `D_ω(G) = ∑ⱼ cⱼ^ω ≤ (n!)^{ω-1} · (∑ₖ dₖ^ω)^n`.

Here `Fintype.card (Equiv.Perm (Fin n)) = n!` is the index `[G : Hⁿ]` and the
permutation factor `(n!)^{ω-1}`.

**Proof debt** (CKSU `lemma:wreath-char-degrees`, proof sketch via Huppert
Theorem 25.6 / Clifford theory): for abelian `H` the degrees of `Sₙ ⋉ Hⁿ` are
at most `n!` with `∑ⱼ cⱼ² = |Sₙ ⋉ Hⁿ|`; the general case follows from Huppert's
character-degree description of the wreath product. The indexed character theory
of wreath products is absent from Mathlib (`Xlib.CharDegrees.charDegrees` is
itself a `sorry`). `sorry`. -/
theorem wreath_charDegree_bound {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (n : ℕ) :
    charDegreeSumReal (ImprimitiveWreathProduct H n) ω
      ≤ (Nat.factorial n : ℝ) ^ (ω - 1) * (charDegreeSumReal H ω) ^ n :=
  sorry

/-! ### STPP triples lift to TPP in the wreath product (CKSU `theorem:STPP2TPP`)

The structural heart of the wreath construction: STPP triples in the base `H`
produce ordinary TPP subsets in `Sₙ ⋉ Hⁿ`. This is the mechanism CKSU use to
show the STPP gives no extra power beyond the ordinary TPP — and it is the bridge
that lets `stpp_capacity_le` be proved from CU Theorem 4.1. We state the
existence of the three TPP carriers; the explicit carriers are
`Hₗ = {h π : πᵢ permutation, hᵢ ∈ (A/B/C) i}` with `|Hₗ| = n! · ∏ᵢ |·|`. -/

/-- **CKSU Theorem `theorem:STPP2TPP`** [math/0511460]: STPP triples in the base
group `H` lift to an ordinary TPP triple in the wreath product
`G = Sₙ ⋉ Hⁿ` (here `ImprimitiveWreathProduct H n`).

Concretely the carriers are `H₁, H₂, H₃ ⊆ G`, where `Hₗ` consists of all `h·π`
with `π` an arbitrary permutation and the `i`-th coordinate of `h` lying in
`A i` (resp. `B i`, `C i`); each has size `n! · ∏ᵢ |A i|` (resp. `B`, `C`). We
state the bare existence of a TPP triple in `G`.

**Proof debt** (CKSU `theorem:STPP2TPP`, CU.tex analogue of the wreath TPP):
a wreath triple product reduces to the permutation identity
`π₁π₁'⁻¹π₂π₂'⁻¹π₃π₃'⁻¹ = 1` together with a coordinatewise condition; the STPP
forces the permutations trivial and the per-triple TPP forces element equality.
The construction of the carrier finsets inside `ImprimitiveWreathProduct` and the
coordinatewise bookkeeping are mechanical but unported. `sorry`. -/
theorem stpp_to_tpp_wreath {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    {n : ℕ} (A B C : Fin n → Finset H) (h : SimultaneousTPP A B C) :
    ∃ S T U : Finset (ImprimitiveWreathProduct H n),
      TripleProductProperty S T U :=
  sorry

/-! ### Wreath pseudo-exponent amplification: `α(Gₙ) ≤ γ(Gₙ) → 2` (CU)

The Cohn–Umans wreath theorem [math/0307321, CU.tex:1248–1255]. With
`A = C₂ₙ` and `Gₙ = A ≀ Sₙ`, the three order-`n!` subgroups `H₁, H₂, H₃`
(built from the vectors `u = (1,…,n)` and `v = (n,…,1)`) realize `⟨n!, n!, n!⟩`,
giving `α(Gₙ) ≤ log(n!·(2n)ⁿ)/log n! = γ(Gₙ)`. Crucially CU show `α ≤ γ` here
(unlike the symmetric-group/triangular construction, where `α ≥ γ`), so this is
the family whose pseudo-exponent genuinely tends to `2`. -/

/-- The Cohn–Umans **wreath bound** `γ(Gₙ) = 2 + (1+log 2)/log n`
[math/0307321, CU.tex:1252], the leading two terms of the asymptotic upper bound
`γ(Gₙ) = 2 + (1+log 2)/log n + O(1/(log n)²)` on the pseudo-exponent of the
**imprimitive** wreath group `Gₙ = C₂ₙ ≀ Sₙ = C₂ₙⁿ ⋊ Sₙ`.

The genuine `γ` is `γ(Gₙ) = log|Gₙ| / log(n!) = log(n!·(2n)ⁿ)/log(n!)`
(CU.tex:1275), where `|Gₙ| = n!·(2n)ⁿ` is the **imprimitive** order
(CU.tex:1267, matching `ImprimitiveWreathProduct.card`; the regular wreath order
`(2n)^{n!}·n!` would be wrong) and `n!` is the largest character degree of `Gₙ`
(Huppert Thm 25.6), giving `|Gₙ|^{1/γ} = n!`. The constant `(1+log 2)` uses the
**natural** logarithm (Stirling `log(n!) = n log n − n + …` makes the `1/log n`
coefficient `1+log 2`, with `log = ln`; this is verified — the `pseudoExponent`
of `Xlib.CUCapacity` is the base-independent ratio `3·log|G|/log β(G)`, and the
two-term expansion of `log(n!·(2n)ⁿ)/log(n!)` in `1/log n` is `2 + (1+log 2)/log n`,
matching CU.tex:1279). -/
noncomputable def wreathGamma (n : ℕ) : ℝ :=
  2 + (1 + Real.log 2) / Real.log n

/-- **The Cohn–Umans wreath pseudo-exponent bound** [math/0307321,
CU.tex:1248–1255]: for `Gₙ = C₂ₙ ≀ Sₙ`,

  `α(Gₙ) ≤ γ(Gₙ) = 2 + (1+log 2)/log n + O(1/(log n)²)`.

We state the inequality against the two-term `wreathGamma n`; the `O`-term is the
gap between `wreathGamma n` and the exact `γ(Gₙ) = log|Gₙ|/log(n!)`, absorbed
into the bound. (`2 ≤ n` keeps `log n > 0` and `Gₙ` nontrivial.)

**Proof debt** (CU wreath theorem, CU.tex:1257–1300): exhibit the three
order-`n!` subgroups `H₁ = {(π,0)}`, `H₂ = {(π, πu−u)}`, `H₃ = {(π, πv−v)}` of
`Gₙ` (with `u = (1,…,n)`, `v = (n,…,1)`), prove they satisfy the TPP (the
`π(i)+σ(i)=2i ⟹ π=σ=1` argument in `ℤ/2nℤ`), so `Gₙ` realizes `⟨n!,n!,n!⟩` and
`tppCapacity Gₙ ≥ (n!)³`; then with `|Gₙ| = (2n)ⁿ·n!`
(`ImprimitiveWreathProduct.card`), `α(Gₙ) = 3·log|Gₙ|/log(tppCapacity Gₙ) ≤
log|Gₙ|/log(n!) = log((2n)ⁿ·n!)/log(n!)`, and expand by Stirling. The TPP-witness
construction inside `ImprimitiveWreathProduct` and the `log`-asymptotics are
unported. `sorry`. -/
theorem pseudoExponent_wreath_le_gamma (n : ℕ) (hn : 2 ≤ n) [NeZero (2 * n)] :
    pseudoExponent (wreathGroup n) ≤ wreathGamma n :=
  sorry

/-- **The wreath amplification limit** [math/0307321, CU.tex:1248–1255]: the
pseudo-exponent of the Cohn–Umans wreath family converges to `2`,

  `α(Gₙ) → 2` as `n → ∞`,    where `Gₙ = C₂ₙ ≀ Sₙ`.

This is *the* amplification statement of the program: a family of groups whose
pseudo-exponent meets the `α = 2` packing bound in the limit (necessary, but not
sufficient, for `ω = 2`). Note CU only prove `α ≤ γ` here, so the family
realizes `α → 2` but does **not** by itself yield a nontrivial bound on `ω` (the
`α < γ` hypothesis of the `ω`-corollary may fail — IDEA.md's caveat).

The statement is over `n` ranging through naturals with `0 < n` (so that
`NeZero (2n)` holds and `Gₙ` is a genuine finite group); we phrase it as a
filter limit along `Filter.atTop`.

**Proof debt:** `Real.Tendsto`-package the bound `2 ≤ α(Gₙ) ≤ wreathGamma n`
(lower bound `two_lt_pseudoExponent`, upper bound `pseudoExponent_wreath_le_gamma`)
with `wreathGamma n → 2` (since `(1+log 2)/log n → 0`), then squeeze. The
squeeze is elementary once the two per-`n` bounds are discharged, but both rest
on `sorry`s (`pseudoExponent_wreath_le_gamma`, and `two_lt_pseudoExponent`
upstream). `sorry`. -/
theorem pseudoExponent_wreath_tendsto_two :
    Filter.Tendsto
      (fun n : ℕ => pseudoExponent (wreathGroup (n + 1)))
      Filter.atTop (nhds 2) :=
  sorry

/-! ### CU "Proposition 11": abelian base ⟹ `α → 2` (`sorry`)

IDEA.md's "CU Prop 11" (the abelian-base wreath case). The wreath construction
`Sₙ ⋉ Hⁿ` and its character-degree bound `wreath_charDegree_bound` hold for
*any* `H`; the *abelian* restriction enters only in collapsing `D_ω(H) = |H|`
(via `Σ dᵢ² = |H|` and all `dᵢ = 1`), which is what drives the pseudo-exponent
of the family to `2`. The **non-abelian** base is the BCGPU open frontier:
whether a non-abelian `H` can push the per-copy pseudo-exponent below the
abelian value while still meeting the packing bound. -/

/-- **CU "Proposition 11"** (the abelian-base wreath case; IDEA.md): for an
*abelian* finite group `H`, the wreath family `Gₙ = H ≀ Sₙ = Sₙ ⋉ Hⁿ` drives the
pseudo-exponent to `2`,

  `α(Gₙ) → 2` as `n → ∞`.

The abelian hypothesis is used *only* in the `D_ω`-collapse step
(`∑ₖ dₖ^ω = |H|`, since every irreducible character degree of an abelian group
is `1`); the wreath TPP construction (`stpp_to_tpp_wreath`) and the
character-degree bound (`wreath_charDegree_bound`) are valid for general `H`.
The cyclic instance `H = C₂ₙ` is the concrete `pseudoExponent_wreath_tendsto_two`.

We require `0 < n` per member (via `NeZero` on `Equiv.Perm`-sized data); the
limit is along `Filter.atTop`.

**Proof debt:** for abelian `H`, `wreath_charDegree_bound` becomes
`D_ω(Gₙ) ≤ (n!)^{ω-1}·|H|^n`, so via CU Theorem 4.1
(`Xlib.CUCapacity.card_rpow_le_charDegreeSumReal`) and `|Gₙ| = |H|^n·n!`, the
pseudo-exponent `α(Gₙ) = 3·log|Gₙ|/log β(Gₙ)` is squeezed to `2` as `n → ∞`.
Rests on the abelian char-degree collapse (`Xlib.CharDegrees`, a `sorry`) and
the wreath `sorry`s above. `sorry`. -/
theorem abelian_wreath_family_tendsto_two {H : Type*} [CommGroup H] [Fintype H]
    [DecidableEq H] [Nontrivial H] :
    Filter.Tendsto
      (fun n : ℕ => pseudoExponent (ImprimitiveWreathProduct H (n + 1)))
      Filter.atTop (nhds 2) :=
  sorry

end Xlib.STPPWreath
