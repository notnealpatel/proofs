import Mathlib
import Xlib.TPP
import Xlib.CUCapacity
import Xlib.CharDegreesComm
import Xlib.CharDegreesIndexBound

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
* `Xlib.STPPWreath.SimultaneousTPP.prod` / `Xlib.STPPWreath.SimultaneousTPP.pow`
  — **(`sorry`-free)** the STPP direct-product closure, CKSU `lemma:directprod`
  (binary on `G × G'`, and iterated on the power carrier `Fin ℓ → G`), stated
  in selection form over an injective index map; with the dependent-fibre TPP
  closure `tripleProductProperty_piFinset`.
* `Xlib.STPPWreath.stpp_capacity_le` — **(`sorry`)** the STPP capacity
  inequality `∑ᵢ (|Aᵢ|·|Bᵢ|·|Cᵢ|)^{ω/3} ≤ D_ω(H)` (CKSU `theorem:asi`).
* `Xlib.STPPWreath.wreath_charDegree_bound` — **(`sorry`-free)** the wreath
  character-degree bound `∑ⱼ cⱼ^ω ≤ (n!)^{ω-1} · (∑ₖ dₖ^ω)^n` for abelian `H`
  (the abelian branch of CKSU `lemma:wreath-char-degrees`, FOCS'05 tex 313–320;
  see Pl19 Clifford triage; the general-`H` version is Clifford-blocked, Gh1).
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

/-! ### STPP direct-product closure (CKSU `lemma:directprod`)

The STPP is closed under direct products [math/0511460,
FOCS05-10page.tex:1239–1246]: `n` triples in `H` and `n'` triples in `H'`
combine to `n·n'` triples in `H × H'` under the index pairing `(i, i')`; and
iterating on one group gives product families on the power carrier
`Fin ℓ → G`. Since `SimultaneousTPP` is `Fin`-indexed, both closure lemmas are
stated in **selection form**: the closed family is presented through an
arbitrary *injective* index selection `Φ : Fin N → Fin n × Fin m`
(resp. `Φ : Fin N → (Fin ℓ → Fin n)`) rather than through a baked-in
equivalence with `Fin (n*m)` (resp. `Fin (n^ℓ)`). An equivalence instantiation
(`finProdFinEquiv.symm`, resp. `finFunctionFinEquiv.symm`) recovers the full
closure verbatim; a subset-enumeration instantiation performs the multinomial
selection step of CKSU's `theorem:asi` proof in the same application. Both
conjuncts of the STPP project componentwise, so the mixed quotient conventions
of `SimultaneousTPP` (left-quotient per-triple, right-quotient simultaneous —
see its orientation note) transport without interaction. -/

/-- **Dependent-fibre iterated TPP closure** on the power carrier `Fin ℓ → G`
(componentwise `Pi.group`): if each fibre triple `(S t, T t, U t)` satisfies
the ordinary TPP in `G`, then the `Fintype.piFinset` triple satisfies the TPP
in `Fin ℓ → G`. Generalizes the constant-fibre
`Xlib.TPP.TripleProductProperty.piFinset` (Tp1) by the same componentwise
projection, fibre by fibre; it supplies the per-triple conjunct of
`SimultaneousTPP.pow`. -/
theorem tripleProductProperty_piFinset {ℓ : ℕ} {S T U : Fin ℓ → Finset G}
    (h : ∀ t, TripleProductProperty (S t) (T t) (U t)) :
    TripleProductProperty (Fintype.piFinset S) (Fintype.piFinset T)
      (Fintype.piFinset U) := by
  intro s hs s' hs' t ht t' ht' u hu u' hu' heq
  simp only [Fintype.mem_piFinset] at hs hs' ht ht' hu hu'
  have coord : ∀ i, (s' i)⁻¹ * s i * (t' i)⁻¹ * t i * (u' i)⁻¹ * u i = 1 := by
    intro i
    simpa only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] using congr_fun heq i
  refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
  · exact (h i (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).1
  · exact (h i (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).2.1
  · exact (h i (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).2.2

/-- **CKSU Lemma `lemma:directprod`** [math/0511460,
FOCS05-10page.tex:1239–1246], the **binary direct-product closure of the
STPP**, in selection form: if `n` triples satisfy the STPP in `G` and `m`
triples satisfy the STPP in `G'`, then the paired product triples
`(A i ×ˢ A' i', B i ×ˢ B' i', C i ×ˢ C' i')` — selected along any injective
`Φ : Fin N → Fin n × Fin m`, with `(i, i') = Φ p` — satisfy the STPP in
`G × G'`.

Instantiating `Φ := ⇑finProdFinEquiv.symm` (an equivalence, hence injective)
with `N := n * m` recovers CKSU's statement verbatim: the full family of all
`n·m` product triples. Sizes multiply by `Finset.card_product`:
`(A i ×ˢ A' i').card = (A i).card * (A' i').card`.

Both conjuncts project componentwise (`Prod.fst`/`Prod.snd` are group
homomorphisms): the per-triple conjunct is Tp1's
`Xlib.TPP.TripleProductProperty.prod`; the simultaneous conjunct's
right-quotient premise at indices `(Φ p, Φ q, Φ r)` projects to the same-shaped
premises at `((Φ p).1, (Φ q).1, (Φ r).1)` in `G` and
`((Φ p).2, (Φ q).2, (Φ r).2)` in `G'`, the two componentwise index collapses
reassemble by `Prod.ext`, and the injectivity of `Φ` yields `p = q ∧ q = r`. -/
theorem SimultaneousTPP.prod [Fintype G] [DecidableEq G]
    {G' : Type*} [Group G'] [Fintype G'] [DecidableEq G']
    {n m : ℕ} {A B C : Fin n → Finset G} {A' B' C' : Fin m → Finset G'}
    (h : SimultaneousTPP A B C) (h' : SimultaneousTPP A' B' C')
    {N : ℕ} (Φ : Fin N → Fin n × Fin m) (hΦ : Function.Injective Φ) :
    SimultaneousTPP
      (fun p => A (Φ p).1 ×ˢ A' (Φ p).2)
      (fun p => B (Φ p).1 ×ˢ B' (Φ p).2)
      (fun p => C (Φ p).1 ×ˢ C' (Φ p).2) := by
  refine ⟨fun p => (h.tpp_of (Φ p).1).prod (h'.tpp_of (Φ p).2), ?_⟩
  intro p q r a ha a' ha' b hb b' hb' c hc c' hc' heq
  simp only [Finset.mem_product] at ha ha' hb hb' hc hc'
  have heq₁ : a.1 * (a'.1)⁻¹ * b.1 * (b'.1)⁻¹ * c.1 * (c'.1)⁻¹ = 1 := by
    simpa only [Prod.fst_mul, Prod.fst_inv, Prod.fst_one]
      using congr_arg Prod.fst heq
  have heq₂ : a.2 * (a'.2)⁻¹ * b.2 * (b'.2)⁻¹ * c.2 * (c'.2)⁻¹ = 1 := by
    simpa only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one]
      using congr_arg Prod.snd heq
  have k₁ := h.simultaneous (Φ p).1 (Φ q).1 (Φ r).1 a.1 ha.1 a'.1 ha'.1
    b.1 hb.1 b'.1 hb'.1 c.1 hc.1 c'.1 hc'.1 heq₁
  have k₂ := h'.simultaneous (Φ p).2 (Φ q).2 (Φ r).2 a.2 ha.2 a'.2 ha'.2
    b.2 hb.2 b'.2 hb'.2 c.2 hc.2 c'.2 hc'.2 heq₂
  exact ⟨hΦ (Prod.ext k₁.1 k₂.1), hΦ (Prod.ext k₁.2 k₂.2)⟩

/-- **CKSU Lemma `lemma:directprod`, iterated (power) form** [math/0511460,
FOCS05-10page.tex:1239–1246]: the `ℓ`-fold direct-product step of CKSU's
`theorem:asi` proof, on the campaign power carrier `Fin ℓ → G` with the
componentwise `Pi.group` structure (matching Md1/Tp1's
`Xlib.TPP.TripleProductProperty.piFinset`). An STPP family of `n` triples in
`G` yields the STPP family of product triples
`(piFinset (A ∘ φ), piFinset (B ∘ φ), piFinset (C ∘ φ))` in `Fin ℓ → G`,
mathematically indexed by the functions `φ : Fin ℓ → Fin n`.

**Index-carrier choice (for the Ca1 assembly).** The index carrier is
`Fin ℓ → Fin n`, presented through an arbitrary **injective selection**
`Φ : Fin N → (Fin ℓ → Fin n)` — not the equiv-packaged `Fin (n ^ ℓ)`. Reason:
`SimultaneousTPP` is `Fin`-indexed, so *some* enumeration is forced either
way, and the selection form lets Ca1's multinomial step — restricting to the
`Nat.multinomial`-many functions of a fixed type `μ` — instantiate `Φ` with an
enumeration of the type-`μ` subset (e.g. via `Finset.orderIsoOfFin`) and land
directly on the selected sub-family in one application, with the concrete
function `Φ p` visible for size bookkeeping; an equiv-packaged statement would
instead force Ca1 to compute through `finFunctionFinEquiv.symm` on every
cardinality. The full `n^ℓ`-triple power is the instantiation
`Φ := ⇑finFunctionFinEquiv.symm` (`N := n ^ ℓ`), and any further sub-selection
is `Φ ∘ g` for injective `g`, so no separate restriction lemma is needed.
Size bookkeeping is `Fintype.card_piFinset`:
`(Fintype.piFinset fun t => A (Φ p t)).card = ∏ t, (A (Φ p t)).card`.

The proof projects both conjuncts componentwise (evaluation at each
`t : Fin ℓ` is a group homomorphism): the per-triple conjunct is
`tripleProductProperty_piFinset`; the simultaneous conjunct's right-quotient
premise at `(Φ p, Φ q, Φ r)` evaluates at `t` to the premise at
`(Φ p t, Φ q t, Φ r t)`, the index collapse holds at every `t`, and `funext`
plus the injectivity of `Φ` gives `p = q ∧ q = r`. -/
theorem SimultaneousTPP.pow [Fintype G] [DecidableEq G]
    {n : ℕ} {A B C : Fin n → Finset G} (h : SimultaneousTPP A B C)
    {ℓ N : ℕ} (Φ : Fin N → Fin ℓ → Fin n) (hΦ : Function.Injective Φ) :
    SimultaneousTPP
      (fun p => Fintype.piFinset fun t => A (Φ p t))
      (fun p => Fintype.piFinset fun t => B (Φ p t))
      (fun p => Fintype.piFinset fun t => C (Φ p t)) := by
  refine ⟨fun p => tripleProductProperty_piFinset fun t => h.tpp_of (Φ p t), ?_⟩
  intro p q r a ha a' ha' b hb b' hb' c hc c' hc' heq
  simp only [Fintype.mem_piFinset] at ha ha' hb hb' hc hc'
  have coord : ∀ t, a t * (a' t)⁻¹ * b t * (b' t)⁻¹ * c t * (c' t)⁻¹ = 1 := by
    intro t
    simpa only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] using congr_fun heq t
  have key : ∀ t, Φ p t = Φ q t ∧ Φ q t = Φ r t := fun t =>
    h.simultaneous (Φ p t) (Φ q t) (Φ r t) (a t) (ha t) (a' t) (ha' t)
      (b t) (hb t) (b' t) (hb' t) (c t) (hc t) (c' t) (hc' t) (coord t)
  exact ⟨hΦ (funext fun t => (key t).1), hΦ (funext fun t => (key t).2)⟩

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

/-- **CKSU Lemma `lemma:wreath-char-degrees`** [math/0511460], abelian instance:
the wreath character-degree power-sum bound for a **commutative** base group.
If `H` is a finite abelian group with character-degree power sum
`D_ω(H) = ∑ₖ dₖ^ω`, then the wreath product `G = Sₙ ⋉ Hⁿ` has

  `D_ω(G) = ∑ⱼ cⱼ^ω ≤ (n!)^{ω-1} · (∑ₖ dₖ^ω)^n`.

Here `Fintype.card (Equiv.Perm (Fin n)) = n!` is the index `[G : Hⁿ]` and the
permutation factor `(n!)^{ω-1}`.

CKSU state the lemma for general `H` (via Huppert Theorem 25.6 / Clifford theory);
we formalize the abelian instance — which is all any consumer in this codebase
uses (`abelian_wreath_family_tendsto_two` is `[CommGroup H]`; `wreathGroup n` has
abelian base `C₂ₙ`) — and the general-`H` version is Clifford-blocked (shelved
follow-on Gh1; see `.tasks/f5exp/docs/Pl19-clifford-triage.md` §1–2).

**Proof** (CKSU FOCS'05 tex 313–320, the abelian branch of their own proof):
`A := (SemidirectProduct.inl).range` is an abelian subgroup of index `n!`;
every character degree `c` satisfies `1 ≤ c ≤ n!`
(`one_le_of_mem_charDegrees`, `charDegree_le_index_of_comm`), so
`c^ω ≤ c² · (n!)^{ω-2}`; summing gives
`∑ c^ω ≤ (n!)^{ω-2} · |G| = (n!)^{ω-1} · |H|ⁿ = (n!)^{ω-1} · D_ω(H)ⁿ`
(via `charDegreeSum_two`, `ImprimitiveWreathProduct.card`,
`charDegreeSumReal_of_commGroup`). -/
theorem wreath_charDegree_bound {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (n : ℕ) :
    charDegreeSumReal (ImprimitiveWreathProduct H n) ω
      ≤ (Nat.factorial n : ℝ) ^ (ω - 1) * (charDegreeSumReal H ω) ^ n := by
  set G := ImprimitiveWreathProduct H n
  -- The abelian subgroup A = inl.range ≅ Fin n → H
  set A : Subgroup G := (SemidirectProduct.inl (φ := permArrowHom H n)).range
  haveI : IsMulCommutative (Fin n → H) := ⟨⟨fun a b => mul_comm a b⟩⟩
  haveI : IsMulCommutative A := Subgroup.range_isMulCommutative _
  -- A.index = n!
  have hcardA : Nat.card A = Nat.card H ^ n := by
    rw [show Nat.card A = Nat.card (Fin n → H) from
      Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv.symm,
      Nat.card_fun, Nat.card_fin]
  have hcardG : Nat.card G = Nat.card H ^ n * n.factorial :=
    ImprimitiveWreathProduct.card H n
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hindex : A.index = n.factorial := by
    have h := Subgroup.card_mul_index A
    rw [hcardA, hcardG] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  -- ω ≥ 2
  have hω2 : 2 ≤ ω := two_le_matrixExponent
  have hω2sub : (0 : ℝ) ≤ ω - 2 := by linarith
  -- Per-entry bound: c ≤ A.index = n!
  have hcle : ∀ c ∈ charDegrees G, c ≤ n.factorial := by
    intro c hc
    rw [← hindex]
    exact Xlib.CharDegreesIndexBound.charDegree_le_index_of_comm A hc
  -- Per-entry bound: 1 ≤ c
  have hc1 : ∀ c ∈ charDegrees G, 1 ≤ c := fun c hc =>
    Xlib.CharDegreesMul.one_le_of_mem_charDegrees hc
  -- Entrywise: c^ω ≤ c^2 · (n!)^(ω-2)
  -- Rewrite the LHS as a map-sum
  rw [charDegreeSumReal_eq_map_sum]
  -- Rewrite the RHS: (n!)^(ω-1) · (charDegreeSumReal H ω)^n
  -- = (n!)^(ω-1) · (Fintype.card H)^n   [by charDegreeSumReal_of_commGroup]
  -- = (n!)^(ω-1) · |H|^n
  rw [Xlib.CharDegreesComm.charDegreeSumReal_of_commGroup]
  -- Now: ∑ (c : ℝ)^ω ≤ (n!)^(ω-1) · (Fintype.card H : ℝ)^n
  -- Chain: ∑ c^ω ≤ (n!)^(ω-2) · ∑ c^2 = (n!)^(ω-2) · |G|
  --        = (n!)^(ω-2) · |H|^n · n! = (n!)^(ω-1) · |H|^n
  -- Step 1: entrywise bound ∑ c^ω ≤ (n!)^(ω-2) · ∑ c^2
  have hstep1 : ((charDegrees G).map (fun d : ℕ => (d : ℝ) ^ ω)).sum
      ≤ (n.factorial : ℝ) ^ (ω - 2) *
        ((charDegrees G).map (fun d : ℕ => (d : ℝ) ^ (2 : ℝ))).sum := by
    rw [← Multiset.sum_map_mul_left]
    refine Multiset.sum_map_le_sum_map _ _ fun d hd => ?_
    have hd1 : 1 ≤ d := hc1 d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
    have hdnf : (d : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast hcle d hd
    calc (d : ℝ) ^ ω
        = (d : ℝ) ^ (2 + (ω - 2)) := by ring_nf
      _ = (d : ℝ) ^ (2 : ℝ) * (d : ℝ) ^ (ω - 2) := Real.rpow_add hd0 2 (ω - 2)
      _ ≤ (d : ℝ) ^ (2 : ℝ) * (n.factorial : ℝ) ^ (ω - 2) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hd0.le hdnf hω2sub)
            (Real.rpow_nonneg (Nat.cast_nonneg d) 2)
      _ = (n.factorial : ℝ) ^ (ω - 2) * (d : ℝ) ^ (2 : ℝ) := mul_comm _ _
  -- Step 2: ∑ c^2 = |G| (via charDegreeSum_two and the ℕ↔ℝ bridge)
  have hstep2 : ((charDegrees G).map (fun d : ℕ => (d : ℝ) ^ (2 : ℝ))).sum
      = (Fintype.card G : ℝ) := by
    -- Normalize rpow 2 to pow 2 via Multiset.map_congr
    have hcongr : (charDegrees G).map (fun d : ℕ => (d : ℝ) ^ (2 : ℝ))
        = (charDegrees G).map (fun d : ℕ => ((d : ℝ) ^ 2 : ℝ)) :=
      Multiset.map_congr rfl fun d _ => Real.rpow_natCast d 2
    rw [hcongr]
    have h := charDegreeSumReal_natCast G 2
    rw [charDegreeSumReal_eq_map_sum] at h
    simp only [Real.rpow_natCast] at h
    rw [h, charDegreeSum_two]
  -- Step 3: |G| = |H|^n · n!
  have hstep3 : (Fintype.card G : ℝ) = (Fintype.card H : ℝ) ^ n * (n.factorial : ℝ) := by
    have := ImprimitiveWreathProduct.card H n
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    exact_mod_cast this
  -- Step 4: (n!)^(ω-2) · |H|^n · n! = (n!)^(ω-1) · |H|^n
  have hstep4 : (n.factorial : ℝ) ^ (ω - 2) * ((Fintype.card H : ℝ) ^ n * (n.factorial : ℝ))
      = (n.factorial : ℝ) ^ (ω - 1) * (Fintype.card H : ℝ) ^ n := by
    have hnfpos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr n.factorial_pos
    -- (n!)^(ω-2) * (|H|^n * n!) = (n!)^(ω-2) * n! * |H|^n
    rw [mul_comm ((Fintype.card H : ℝ) ^ n) (n.factorial : ℝ), ← mul_assoc]
    -- (n!)^(ω-2) * n! = (n!)^(ω-1)
    congr 1
    calc (n.factorial : ℝ) ^ (ω - 2) * (n.factorial : ℝ)
        = (n.factorial : ℝ) ^ (ω - 2) * (n.factorial : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = (n.factorial : ℝ) ^ (ω - 2 + 1) := (Real.rpow_add hnfpos (ω - 2) 1).symm
      _ = (n.factorial : ℝ) ^ (ω - 1) := by ring_nf
  calc ((charDegrees G).map (fun d : ℕ => (d : ℝ) ^ ω)).sum
      ≤ (n.factorial : ℝ) ^ (ω - 2) *
        ((charDegrees G).map (fun d : ℕ => (d : ℝ) ^ (2 : ℝ))).sum := hstep1
    _ = (n.factorial : ℝ) ^ (ω - 2) * (Fintype.card G : ℝ) := by rw [hstep2]
    _ = (n.factorial : ℝ) ^ (ω - 2) * ((Fintype.card H : ℝ) ^ n * (n.factorial : ℝ)) := by
        rw [hstep3]
    _ = (n.factorial : ℝ) ^ (ω - 1) * (Fintype.card H : ℝ) ^ n := hstep4

/-! ### STPP triples lift to TPP in the wreath product (CKSU `theorem:STPP2TPP`)

The structural heart of the wreath construction: STPP triples in the base `H`
produce ordinary TPP subsets in `Sₙ ⋉ Hⁿ`. This is the mechanism CKSU use to
show the STPP gives no extra power beyond the ordinary TPP — and it is the bridge
that lets `stpp_capacity_le` be proved from CU Theorem 4.1. We state the
existence of the three TPP carriers; the explicit carriers are
`Hₗ = {h π : πᵢ permutation, hᵢ ∈ (A/B/C) i}` with `|Hₗ| = n! · ∏ᵢ |·|`. -/

/-- Pointwise formula for the coordinate-permutation action: `permArrowHom D n σ`
sends `f` to `f ∘ σ⁻¹`, so at coordinate `i` it reads `f (σ⁻¹ i)`. (`rfl`;
recorded to make the wreath coordinate computations below readable.) -/
theorem permArrowHom_apply {D : Type*} [Group D] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : Fin n → D) (i : Fin n) : permArrowHom D n σ f i = f (σ⁻¹ i) :=
  rfl

/-- The **CKSU wreath carrier** `Hₗ = {h·π : π ∈ Sₙ, hᵢ ∈ X i for each i}`
(CKSU `theorem:STPP2TPP`, FOCS05-10page.tex:1514–1524) attached to a family
`X : Fin n → Finset H`: the finset of all `⟨f, π⟩` in the imprimitive wreath
product `Sₙ ⋉ Hⁿ` whose function part is coordinatewise constrained
(`f i ∈ X i`) and whose permutation part is arbitrary. Realized as the image of
`Fintype.piFinset X ×ˢ univ` under the (componentwise-injective) constructor
`(f, π) ↦ ⟨f, π⟩`; its cardinality is `n! · ∏ᵢ |X i|` (`wreathCarrier_card`). -/
def wreathCarrier {H : Type*} [Group H] [DecidableEq H] {n : ℕ}
    (X : Fin n → Finset H) : Finset (ImprimitiveWreathProduct H n) :=
  ((Fintype.piFinset X) ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin n)))).image
    fun p => ⟨p.1, p.2⟩

/-- Membership in the CKSU wreath carrier: the permutation part is free and the
function part is constrained coordinatewise, `w ∈ wreathCarrier X ↔ ∀ i,
w.left i ∈ X i`. -/
theorem mem_wreathCarrier {H : Type*} [Group H] [DecidableEq H] {n : ℕ}
    {X : Fin n → Finset H} {w : ImprimitiveWreathProduct H n} :
    w ∈ wreathCarrier X ↔ ∀ i, w.left i ∈ X i := by
  constructor
  · intro hw
    rw [wreathCarrier, Finset.mem_image] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    rw [Finset.mem_product] at hp
    exact fun i => Fintype.mem_piFinset.mp hp.1 i
  · intro hw
    rw [wreathCarrier, Finset.mem_image]
    exact ⟨(w.left, w.right),
      Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr hw, Finset.mem_univ _⟩, rfl⟩

/-- **The CKSU carrier size** `|Hₗ| = n! · ∏ᵢ |X i|` (CKSU `theorem:STPP2TPP`):
the constructor `(f, π) ↦ ⟨f, π⟩` is injective, so the carrier has the size of
`Fintype.piFinset X ×ˢ univ`. -/
theorem wreathCarrier_card {H : Type*} [Group H] [DecidableEq H] {n : ℕ}
    (X : Fin n → Finset H) :
    (wreathCarrier X).card = n.factorial * ∏ i, (X i).card := by
  have hinj : Function.Injective
      (fun p : (Fin n → H) × Equiv.Perm (Fin n) =>
        (⟨p.1, p.2⟩ : ImprimitiveWreathProduct H n)) := by
    intro p q hpq
    exact Prod.ext (congrArg SemidirectProduct.left hpq)
      (congrArg SemidirectProduct.right hpq)
  rw [wreathCarrier, Finset.card_image_of_injective _ hinj, Finset.card_product,
    Fintype.card_piFinset, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    mul_comm]

/-- In a **commutative** group the left-quotient `TripleProductProperty` entails
the right-quotient `TripleProductPropertyR` on the *same* ordered triple:
commutativity rearranges the right-quotient product `s s'⁻¹ t t'⁻¹ u u'⁻¹` into
the left-quotient product `s'⁻¹ s t'⁻¹ t u'⁻¹ u`. (For general groups the two
conventions differ on the same triple — see the docstring of
`Xlib.TPP.TripleProductPropertyR`; the correct general bridge is
`tripleProductPropertyR_iff_inv`, which inverts the sets.) -/
theorem tripleProductPropertyR_of_comm {H : Type*} [CommGroup H] [Fintype H]
    [DecidableEq H] {S T U : Finset H} (h : TripleProductProperty S T U) :
    TripleProductPropertyR S T U := by
  intro q₁ hq₁ q₂ hq₂ q₃ hq₃ heq
  obtain ⟨s, hs, s', hs', rfl⟩ := mem_mul_inv.mp hq₁
  obtain ⟨t, ht, t', ht', rfl⟩ := mem_mul_inv.mp hq₂
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_mul_inv.mp hq₃
  have hquot : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1 := by
    have hcomm : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u
        = s * s'⁻¹ * (t * t'⁻¹) * (u * u'⁻¹) := by
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [hcomm, heq]
  obtain ⟨h1, h2, h3⟩ := h s hs s' hs' t ht t' ht' u hu u' hu' hquot
  exact ⟨by rw [h1, mul_inv_cancel], by rw [h2, mul_inv_cancel],
    by rw [h3, mul_inv_cancel]⟩

/-- **The CKSU `theorem:STPP2TPP` carrier verification**
[math/0511460, FOCS05-10page.tex:1508–1559], in the coherent **right-quotient**
convention (the convention of CKSU's paper): if the `n` triples satisfy the
`SimultaneousTPP` *and* each per-index triple additionally satisfies the
right-quotient `TripleProductPropertyR`, then the three CKSU carriers
`wreathCarrier A`, `wreathCarrier B`, `wreathCarrier C` satisfy the
right-quotient TPP in the imprimitive wreath product `Sₙ ⋉ Hⁿ`.

The extra hypothesis `hR` is CKSU's own per-triple hypothesis: their STPP is
stated wholly in the right-quotient convention, whereas
`Xlib.STPPWreath.SimultaneousTPP`'s per-triple conjunct invokes the
left-quotient `Xlib.TPP.TripleProductProperty` (see the orientation note in its
docstring). The two per-triple conventions are **not** equivalent on the same
triple, and the CKSU carrier argument genuinely consumes the right-quotient
form at its final elementwise step, so it is carried as an explicit hypothesis
here; for commutative `H` it is automatic (`tripleProductPropertyR_of_comm`,
consumed by `stpp_to_tpp_wreath_card`).

Proof shape (CKSU, recomputed in Mathlib's `SemidirectProduct` conventions
`(f,π)·(g,σ) = (f · (g ∘ π⁻¹), πσ)` and `(f,π)⁻¹ = ((f ∘ π)⁻¹, π⁻¹)`):
a right-quotient triple product forces the permutation identity
`σ₁σ₂σ₃ = 1` (`σₗ = πₗπₗ'⁻¹`) on `rightHom`, and coordinatewise reads
`f₁(i)·f₁'(σ₁⁻¹i)⁻¹·f₂(σ₁⁻¹i)·f₂'((σ₁σ₂)⁻¹i)⁻¹·f₃((σ₁σ₂)⁻¹i)·f₃'(i)⁻¹ = 1` —
exactly the simultaneous conjunct's premise at `(i, σ₁⁻¹i, (σ₁σ₂)⁻¹i)`, which
collapses `σ₁ = σ₂ = σ₃ = 1`; the residual coordinatewise identity is the
right-quotient per-triple premise, and `hR` finishes. -/
theorem tripleProductPropertyR_wreathCarrier {H : Type*} [Group H] [Fintype H]
    [DecidableEq H] {n : ℕ} {A B C : Fin n → Finset H}
    (h : SimultaneousTPP A B C)
    (hR : ∀ i, TripleProductPropertyR (A i) (B i) (C i)) :
    TripleProductPropertyR (wreathCarrier A) (wreathCarrier B) (wreathCarrier C) := by
  intro q₁ hq₁ q₂ hq₂ q₃ hq₃ heq
  obtain ⟨x, hx, x', hx', rfl⟩ := mem_mul_inv.mp hq₁
  obtain ⟨y, hy, y', hy', rfl⟩ := mem_mul_inv.mp hq₂
  obtain ⟨z, hz, z', hz', rfl⟩ := mem_mul_inv.mp hq₃
  rw [mem_wreathCarrier] at hx hx' hy hy' hz hz'
  obtain ⟨f₁, π₁⟩ := x
  obtain ⟨f₁', π₁'⟩ := x'
  obtain ⟨f₂, π₂⟩ := y
  obtain ⟨f₂', π₂'⟩ := y'
  obtain ⟨f₃, π₃⟩ := z
  obtain ⟨f₃', π₃'⟩ := z'
  -- The permutation identity `σ₁σ₂σ₃ = 1` (CKSU `equation:stppperm`).
  have hperm : π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹) * (π₃ * π₃'⁻¹) = 1 :=
    congrArg SemidirectProduct.right heq
  -- The coordinatewise identity, in the simultaneous conjunct's exact shape:
  -- at each `i` the six factors sit at indices `(i, σ₁⁻¹i, σ₁⁻¹i, (σ₁σ₂)⁻¹i,
  -- (σ₁σ₂)⁻¹i, i)` — the CKSU `(i, j, k)`-chain.
  have hflat : ∀ i : Fin n,
      f₁ i * (f₁' ((π₁ * π₁'⁻¹)⁻¹ i))⁻¹ * f₂ ((π₁ * π₁'⁻¹)⁻¹ i)
          * (f₂' ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i))⁻¹
          * f₃ ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i) * (f₃' i)⁻¹ = 1 := by
    intro i
    have hproj : f₁ i * (f₁' ((π₁ * π₁'⁻¹)⁻¹ i))⁻¹
        * (f₂ ((π₁ * π₁'⁻¹)⁻¹ i) * (f₂' ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i))⁻¹)
        * (f₃ ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i)
            * (f₃' ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹) * (π₃ * π₃'⁻¹))⁻¹ i))⁻¹) = 1 :=
      congrFun (congrArg SemidirectProduct.left heq) i
    have hlast : (π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹) * (π₃ * π₃'⁻¹))⁻¹ i = i := by
      rw [hperm, inv_one, Equiv.Perm.one_apply]
    rw [hlast] at hproj
    simpa only [mul_assoc] using hproj
  -- The simultaneous conjunct collapses the permutations (CKSU: `π = ρ = 1`).
  have hcollapse : ∀ i : Fin n,
      i = (π₁ * π₁'⁻¹)⁻¹ i
        ∧ (π₁ * π₁'⁻¹)⁻¹ i = (π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i := fun i =>
    h.2 i ((π₁ * π₁'⁻¹)⁻¹ i) ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i)
      (f₁ i) (hx i)
      (f₁' ((π₁ * π₁'⁻¹)⁻¹ i)) (hx' ((π₁ * π₁'⁻¹)⁻¹ i))
      (f₂ ((π₁ * π₁'⁻¹)⁻¹ i)) (hy ((π₁ * π₁'⁻¹)⁻¹ i))
      (f₂' ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i)) (hy' ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i))
      (f₃ ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i)) (hz ((π₁ * π₁'⁻¹ * (π₂ * π₂'⁻¹))⁻¹ i))
      (f₃' i) (hz' i)
      (hflat i)
  have hσ₁ : π₁ * π₁'⁻¹ = 1 := by
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.one_apply]
    exact Equiv.Perm.eq_inv_iff_eq.mp (hcollapse i).1
  have hσ₂ : π₂ * π₂'⁻¹ = 1 := by
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.one_apply]
    have h2 := (hcollapse i).2
    rw [hσ₁] at h2
    simp only [inv_one, Equiv.Perm.one_apply, one_mul] at h2
    exact Equiv.Perm.eq_inv_iff_eq.mp h2
  have hσ₃ : π₃ * π₃'⁻¹ = 1 := by
    rw [hσ₁, hσ₂, one_mul, one_mul] at hperm
    exact hperm
  -- With trivial permutations, the residual coordinatewise identity is the
  -- right-quotient per-triple premise; `hR` finishes (CKSU's final step).
  have helem : ∀ i : Fin n,
      f₁ i * (f₁' i)⁻¹ = 1 ∧ f₂ i * (f₂' i)⁻¹ = 1 ∧ f₃ i * (f₃' i)⁻¹ = 1 := by
    intro i
    have hflat0 := hflat i
    rw [hσ₁, hσ₂] at hflat0
    simp only [one_mul, inv_one, Equiv.Perm.one_apply] at hflat0
    exact hR i (f₁ i * (f₁' i)⁻¹)
      (mem_mul_inv.mpr ⟨f₁ i, hx i, f₁' i, hx' i, rfl⟩)
      (f₂ i * (f₂' i)⁻¹)
      (mem_mul_inv.mpr ⟨f₂ i, hy i, f₂' i, hy' i, rfl⟩)
      (f₃ i * (f₃' i)⁻¹)
      (mem_mul_inv.mpr ⟨f₃ i, hz i, f₃' i, hz' i, rfl⟩)
      (by simpa only [mul_assoc] using hflat0)
  refine ⟨SemidirectProduct.ext ?_ hσ₁, SemidirectProduct.ext ?_ hσ₂,
    SemidirectProduct.ext ?_ hσ₃⟩
  · funext i
    show f₁ i * (f₁' ((π₁ * π₁'⁻¹)⁻¹ i))⁻¹ = (1 : Fin n → H) i
    rw [hσ₁, inv_one, Equiv.Perm.one_apply]
    exact (helem i).1
  · funext i
    show f₂ i * (f₂' ((π₂ * π₂'⁻¹)⁻¹ i))⁻¹ = (1 : Fin n → H) i
    rw [hσ₂, inv_one, Equiv.Perm.one_apply]
    exact (helem i).2.1
  · funext i
    show f₃ i * (f₃' ((π₃ * π₃'⁻¹)⁻¹ i))⁻¹ = (1 : Fin n → H) i
    rw [hσ₃, inv_one, Equiv.Perm.one_apply]
    exact (helem i).2.2

/-- **CKSU Theorem `theorem:STPP2TPP`** [math/0511460]: STPP triples in the base
group `H` lift to an ordinary TPP triple in the wreath product
`G = Sₙ ⋉ Hⁿ` (here `ImprimitiveWreathProduct H n`).

Concretely the carriers are `H₁, H₂, H₃ ⊆ G`, where `Hₗ` consists of all `h·π`
with `π` an arbitrary permutation and the `i`-th coordinate of `h` lying in
`A i` (resp. `B i`, `C i`); each has size `n! · ∏ᵢ |A i|` (resp. `B`, `C`). We
state the bare existence of a TPP triple in `G`.

**Proof note (witness choice).** The full CKSU carriers are delivered by
`tripleProductPropertyR_wreathCarrier` (the carrier verification, general `H`
plus the right-quotient per-triple hypothesis) and `stpp_to_tpp_wreath_card`
(commutative `H`, carrier sizes carried). For *general* `H` the CKSU carrier
verification is **not derivable** from `SimultaneousTPP` as stated: its final
elementwise step consumes the per-triple TPP in the right-quotient convention,
while `SimultaneousTPP`'s per-triple conjunct is the left-quotient
`TripleProductProperty`, and the two are not equivalent on the same triple
(see `Xlib.TPP.TripleProductPropertyR`; a Sage witness in `S₃` with `n = 2`
exhibits a left-per-triple + right-simultaneous family whose CKSU carriers
fail the right-quotient TPP in `S₂ ⋉ S₃²`). This bare-existence statement is
therefore witnessed by the base-diagonal carriers
`{⟨f, 1⟩ : f i ∈ A i}` (resp. `B`, `C`) of size `∏ᵢ |·|` — the image of the
per-triple TPP under the embedding `Hⁿ →* Sₙ ⋉ Hⁿ`, which consumes only the
per-triple conjunct and is valid for every `H`. -/
theorem stpp_to_tpp_wreath {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    {n : ℕ} (A B C : Fin n → Finset H) (h : SimultaneousTPP A B C) :
    ∃ S T U : Finset (ImprimitiveWreathProduct H n),
      TripleProductProperty S T U := by
  refine ⟨(Fintype.piFinset A).image SemidirectProduct.inl,
    (Fintype.piFinset B).image SemidirectProduct.inl,
    (Fintype.piFinset C).image SemidirectProduct.inl, ?_⟩
  intro s hs s' hs' t ht t' ht' u hu u' hu' hprod
  obtain ⟨f₁, hf₁, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨f₁', hf₁', rfl⟩ := Finset.mem_image.mp hs'
  obtain ⟨f₂, hf₂, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨f₂', hf₂', rfl⟩ := Finset.mem_image.mp ht'
  obtain ⟨f₃, hf₃, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨f₃', hf₃', rfl⟩ := Finset.mem_image.mp hu'
  have hbase : f₁'⁻¹ * f₁ * f₂'⁻¹ * f₂ * f₃'⁻¹ * f₃ = 1 := by
    apply SemidirectProduct.inl_injective (φ := permArrowHom H n)
    rw [map_one]
    simpa only [map_mul, map_inv] using hprod
  have key : ∀ i, f₁ i = f₁' i ∧ f₂ i = f₂' i ∧ f₃ i = f₃' i := fun i =>
    h.1 i (f₁ i) (Fintype.mem_piFinset.mp hf₁ i)
      (f₁' i) (Fintype.mem_piFinset.mp hf₁' i)
      (f₂ i) (Fintype.mem_piFinset.mp hf₂ i)
      (f₂' i) (Fintype.mem_piFinset.mp hf₂' i)
      (f₃ i) (Fintype.mem_piFinset.mp hf₃ i)
      (f₃' i) (Fintype.mem_piFinset.mp hf₃' i)
      (congrFun hbase i)
  exact ⟨congrArg _ (funext fun i => (key i).1),
    congrArg _ (funext fun i => (key i).2.1),
    congrArg _ (funext fun i => (key i).2.2)⟩

open scoped Pointwise in
/-- **CKSU Theorem `theorem:STPP2TPP` with the carrier cardinalities**
[math/0511460, FOCS05-10page.tex:1508–1559], for a **commutative** base group:
the witness TPP triple in the wreath product `Sₙ ⋉ Hⁿ` can be chosen with the
CKSU carrier sizes

  `|S| = n! · ∏ᵢ |A i|`, `|T| = n! · ∏ᵢ |B i|`, `|U| = n! · ∏ᵢ |C i|`.

This is the form the `theorem:asi` assembly (`stpp_capacity_le`) consumes: the
capacity bound CU Thm 4.1 applied to the wreath group needs the product
`|S|·|T|·|U|` of the lifted triple.

The commutativity hypothesis makes the right-quotient per-triple TPP automatic
(`tripleProductPropertyR_of_comm`), which the CKSU carrier verification
`tripleProductPropertyR_wreathCarrier` requires; the witness triple is the
inverse-image `(wreathCarrier A)⁻¹, (wreathCarrier B)⁻¹, (wreathCarrier C)⁻¹`
of the CKSU carriers under the convention bridge
`tripleProductPropertyR_iff_inv`, with the same cardinalities
(`Finset.card_inv`). The downstream consumers (`stpp_capacity_le` via the
Ab1/Ab2/Ab3 chain, and both wreath-family limits) are all abelian-based, so no
generality is lost where it is consumed. -/
theorem stpp_to_tpp_wreath_card {H : Type*} [CommGroup H] [Fintype H]
    [DecidableEq H] {n : ℕ} (A B C : Fin n → Finset H)
    (h : SimultaneousTPP A B C) :
    ∃ S T U : Finset (ImprimitiveWreathProduct H n),
      TripleProductProperty S T U
        ∧ S.card = n.factorial * ∏ i, (A i).card
        ∧ T.card = n.factorial * ∏ i, (B i).card
        ∧ U.card = n.factorial * ∏ i, (C i).card := by
  have hR : ∀ i, TripleProductPropertyR (A i) (B i) (C i) := fun i =>
    tripleProductPropertyR_of_comm (h.tpp_of i)
  refine ⟨(wreathCarrier A)⁻¹, (wreathCarrier B)⁻¹, (wreathCarrier C)⁻¹,
    tripleProductPropertyR_iff_inv.mp (tripleProductPropertyR_wreathCarrier h hR),
    ?_, ?_, ?_⟩
  · rw [Finset.card_inv, wreathCarrier_card]
  · rw [Finset.card_inv, wreathCarrier_card]
  · rw [Finset.card_inv, wreathCarrier_card]

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
