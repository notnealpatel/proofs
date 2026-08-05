import Mathlib

/-!
# Commuting triples of permutations: the layer of Britnell's identity that is finite

## What this file is about

Let `T(G)` be the number of ordered triples `(f, g, h)` of pairwise-commuting elements of a
finite group `G`, and write `T(n) = T(S_n)`.  Franklin T. Adams-Watters conjectured (2006) and
J. R. Britnell proved (2012) that the numbers `T(n)/n!` are the coefficients of the Euler
transform of the sum-of-divisors function.  This file formalizes the *finite* half of Britnell's
argument — everything up to, but not including, the formal power series manipulation.

## Pinned sources

`goof oeis show A061256` (retrieved 2026-08-05), verbatim:

> `"id":"A061256"`
>
> `"name":"Euler transform of sigma(n), cf. A000203."`
>
> `"terms":"1,1,4,8,21,39,92,170,360,667,1316,2393,4541,8100,14824,26071,46422,80314,139978,`
> `238641,408201,686799,1156062,1920992,3189144,5238848,8589850,13963467,22641585,36447544,`
> `58507590,93334008,148449417,234829969,370345918"` (offset `0,3`, i.e. `a(0) = 1`)
>
> comment 1: `"This is also the number of ordered triples of permutations f, g, h in Symm(n)`
> `which all commute, divided by n!. This was conjectured by _Franklin T. Adams-Watters_,`
> `Jan 16 2006, and proved by J. R. Britnell in 2012."`
>
> comment 2: `"According to a message on a blog page by \"Allan\" (see Secret Blogging Seminar`
> `link) it appears that a(n) = number of conjugacy classes of commutative ordered pairs in`
> `Symm(n)."`
>
> formula 1: `"a(n) = A072169(n) / n!."`
>
> formula 2: `"G.f.: Product_{k=1..infinity} (1 - x^k)^(-sigma(k)). ..."`

`goof oeis show A072169` (retrieved 2026-08-05), verbatim:

> `"id":"A072169"`
>
> `"name":"Commuting permutations: number of ordered triples of permutations f, g, h in Symm(n)`
> `which all commute."`
>
> `"terms":"1,1,8,48,504,4680,66240,856800,14515200,242040960,4775500800,95520902400,`
> `2175146265600,50438868480000,1292330988748800,34092378448128000,971277752180736000,`
> `28566680100102144000,896191466580393984000,29029508406664077312000"`
>
> formula: `"Equals A061256(n)*n!."`

J. R. Britnell, *A formal identity involving commuting triples of permutations*,
arXiv:1203.5079 [math.CO], 2012; J. Combin. Theory Ser. A **120** (2013) 941–943.
Source fetched to `References/arXiv-1203-5079/CommTriplesFV.tex`.  Verbatim excerpts:

> "We prove a formal power series identity, relating the arithmetic sum-of-divisors function to
> commuting triples of permutations.  This establishes a conjecture of Franklin T.
> Adams-Watters."

> "The object of this note is to establish the following formal identity:
> `\prod_{j=1}^{\infty} (1-u^j)^{-\sigma(j)} = \sum_{n=0}^{\infty} \frac{T(n)}{n!} u^n,`
> where `\sigma` is the arithmetic sum-of-divisors function, and `T(n)` is the number of triples
> of pairwise-commuting elements of the symmetric group `S_n`. (Here `S_0` is the trivial group.)"

> "For a finite group `G`, we shall write `k(G)` for the number of conjugacy classes of `G`.
> The following simple fact seems first to have been stated by Erdős and Turán.
> **Lemma 1.** The number of pairs of commuting elements of `G` is `|G| k(G)`."

> "Let `g\in G`. It follows from Lemma 1 that the number of commuting triples of `G` whose first
> element is `g`, is given by `|Cent_G(g)| k(Cent_G(g))`.  So if `T(G)` is the total number of
> commuting triples, then
> `\frac{T(G)}{|G|} = \sum_{g \in G} \frac{|Cent_G(g)|}{|G|} k(Cent_G(g)) = \sum_{i=1}^r
> k(Cent_G(g_i))`,
> where `\{g_1,\dots, g_r\}` is a set of conjugacy class representatives for `G`."

## Main results

* `GroupCount.card_commutingPair` — Britnell's Lemma 1 (Erdős–Turán), in the orientation
  `#{commuting pairs} = |G| · k(G)`.  This is a one-line consequence of Mathlib's
  `card_comm_eq_card_conjClasses_mul_card`; it is restated here only to fix the alias.
* `GroupCount.commTripleCount_eq_sum_centralizer` — Britnell's displayed equation, in the
  denominator-free form `T(G) = ∑_{g ∈ G} |Cent_G(g)| · k(Cent_G(g))`.
* `GroupCount.commTripleCount_eq_card_orbits_mul_card` — Burnside's lemma applied to the
  simultaneous-conjugation action of `G` on its commuting pairs:
  `T(G) = #{orbits} · |G|`.  Hence `T(G)/|G|` is *the number of conjugacy classes of ordered
  commuting pairs*, which is OEIS comment 2 above.  Note that OEIS states comment 2 only as
  "it appears that"; the content of this theorem is that comment 2 is *equivalent* to comment 1
  (Britnell's theorem) with no extra input, since both describe `T(n)/n!`.
* `GroupCount.card_fixedBy_commutingPair` — Britnell's sentence "the number of commuting triples
  of `G` whose first element is `g` is `|Cent_G(g)| k(Cent_G(g))`", stated as the size of the
  fixed set of `g` in the Burnside action.  This is the bridge identifying the two
  decompositions of a triple by its first entry.
* `GroupCount.card_dvd_commTripleCount`, `GroupCount.factorial_dvd_A072169` — the divisibility
  `|G| ∣ T(G)`, so `A061256 n := T(n) / n !` is honest natural-number division, not truncation.
* `GroupCount.A072169_zero` … `GroupCount.A072169_four` and `GroupCount.A061256_zero` …
  `GroupCount.A061256_four` — kernel certificates `T(n) = 1, 1, 8, 48, 504` and
  `T(n)/n! = 1, 1, 4, 8, 21` for `n ≤ 4`, matching the pinned OEIS terms.

## What is *not* proved here: the gap

Britnell's identity itself is **not** formalized.  Downstream of the equation
`T(G) = ∑_{g} |Cent_G(g)| k(Cent_G(g))` proved here, his argument needs four further
ingredients, none of which exist in Mathlib:

0. The *second* equality of his displayed equation, `∑_{g∈G} (|Cent_G(g)|/|G|) k(Cent_G(g)) =
   ∑_{i=1}^r k(Cent_G(g_i))` over a set of conjugacy class representatives.  This is a routine
   class-counting repackaging and adds no content beyond the two theorems above (both already
   evaluate `T(G)/|G|`), but it is the shape his `S_n` analysis consumes.  Formalizing it needs
   a conjugation isomorphism `Cent_G(g) ≃* Cent_G(u g u⁻¹)` (absent from Mathlib: there is no
   `Subgroup.map_centralizer`) plus fiberwise-sum and orbit-stabilizer plumbing.  It is the one
   gap item that is pure plumbing rather than a missing mathematical layer.
1. `Cent_{S_n}(g) ≅ ∏_t (ℤ/tℤ ≀ S_{m_t})` for `g` of cycle type `(m_t)`.  Mathlib has the
   conjugacy classification of `S_n` by `Equiv.Perm.cycleType` but no wreath-product
   description of centralizers.
2. `k(ℤ/tℤ ≀ S_m)` = the number of `t`-tuples of partitions of total size `m`, via the
   cycle-sum invariant (James–Kerber, Theorem 4.2.8).  Mathlib has neither wreath products of
   this shape nor their conjugacy classification.
3. The formal power series step
   `∏_t P(u^t)^t = ∏_t ∏_s (1-u^{st})^{-t} = ∏_j (1-u^j)^{-σ(j)}`, which needs infinite
   products of formal power series and the Euler product for the partition generating function.
   Neither an Euler-transform layer nor infinite power series products exists in Mathlib or in
   this repository, and this file deliberately does not build one.

The fragment landed here is therefore layer-free: it is exactly the group-theoretic prelude
(Britnell's Lemma 1 and his equation for `T(G)/|G|`), plus the Burnside reformulation, plus
kernel-checked values at `n ≤ 4`.

## Note on a discrepancy in the task brief

The brief that commissioned this file listed the small values as
"`n ≤ 4: 1, 2, 8, 40, 300 / n! ⇒ a(n) = 1, 2, 4, ...`".  Those numbers are wrong.  The pinned
OEIS terms are `A072169 = 1, 1, 8, 48, 504, …` and `A061256 = 1, 1, 4, 8, 21, …`, and the
theorems `A072169_zero`–`A072169_four`, `A061256_zero`–`A061256_four` below check the OEIS
values in the kernel.

## Build note

This module is not yet imported by the library root `Proofs/GroupCount.lean`, so
`lake build GroupCount` does not reach it; build it with `lake build GroupCount.CommutingTriples`
until the root import is added.
-/

set_option autoImplicit false

namespace GroupCount

open MulAction
open scoped Nat

/-! ## Decidability of `Commute`

Mathlib does not register a `Decidable` instance for `Commute`, even though `Commute a b` is by
definition the equation `a * b = b * a` (`commute_iff_eq` is `Iff.rfl`).  The instance below is
needed so that the `Fintype` instances on `CommutingPair`/`CommutingTriple` are computable and
the small-`n` certificates can be closed by `decide` rather than `native_decide`. -/

/-- `Commute a b` is by definition the equation `a * b = b * a`, hence decidable whenever
equality on `M` is. -/
instance instDecidableCommute {M : Type*} [Mul M] [DecidableEq M] (a b : M) :
    Decidable (Commute a b) :=
  inferInstanceAs (Decidable (a * b = b * a))

/-! ## The two counted types -/

/-- Ordered pairs of commuting elements of `M`.  Reducible, and syntactically the subtype used
by Mathlib's `card_comm_eq_card_conjClasses_mul_card`. -/
abbrev CommutingPair (M : Type*) [Mul M] : Type _ := { p : M × M // Commute p.1 p.2 }

/-- Ordered triples of *pairwise*-commuting elements of `M`. -/
abbrev CommutingTriple (M : Type*) [Mul M] : Type _ :=
  { t : M × M × M // Commute t.1 t.2.1 ∧ Commute t.1 t.2.2 ∧ Commute t.2.1 t.2.2 }

/-- `commTripleCount M` is `T(G)` in Britnell's notation: the number of ordered triples of
pairwise-commuting elements of `M`. -/
noncomputable def commTripleCount (M : Type*) [Mul M] : ℕ := Nat.card (CommutingTriple M)

/-- Bridge from the `Nat.card` definition to the computable `Fintype.card`, used by the
small-`n` certificates. -/
theorem commTripleCount_eq_fintypeCard (M : Type*) [Mul M] [Fintype M] [DecidableEq M] :
    commTripleCount M = Fintype.card (CommutingTriple M) :=
  Nat.card_eq_fintype_card

/-! ## Britnell's Lemma 1 (Erdős–Turán) -/

/-- **Britnell, Lemma 1** (attributed there to Erdős–Turán): the number of ordered pairs of
commuting elements of a finite group `G` is `|G| · k(G)`, where `k(G)` is the number of
conjugacy classes.  This is Mathlib's `card_comm_eq_card_conjClasses_mul_card` with the factors
in Britnell's order. -/
theorem card_commutingPair (G : Type*) [Group G] :
    Nat.card (CommutingPair G) = Nat.card G * Nat.card (ConjClasses G) := by
  rw [card_comm_eq_card_conjClasses_mul_card, mul_comm]

/-! ## Britnell's equation for `T(G)`, via centralizers -/

/-- Splitting a commuting triple by its first entry `f`: the other two entries are a commuting
pair *inside* the centralizer of `f`. -/
def commutingTripleEquivSigmaCentralizer (G : Type*) [Group G] :
    CommutingTriple G ≃ Σ g : G, CommutingPair (Subgroup.centralizer ({g} : Set G)) where
  toFun t :=
    ⟨t.1.1, ⟨(⟨t.1.2.1, Subgroup.mem_centralizer_singleton_iff.mpr t.2.1.symm⟩,
              ⟨t.1.2.2, Subgroup.mem_centralizer_singleton_iff.mpr t.2.2.1.symm⟩),
             Subtype.ext t.2.2.2⟩⟩
  invFun x :=
    ⟨(x.1, (x.2.1.1 : G), (x.2.1.2 : G)),
      ⟨(Subgroup.mem_centralizer_singleton_iff.mp x.2.1.1.2).symm,
       (Subgroup.mem_centralizer_singleton_iff.mp x.2.1.2.2).symm,
       Subtype.ext_iff.mp x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Britnell's displayed equation**, cleared of denominators:
`T(G) = ∑_{g ∈ G} |Cent_G(g)| · k(Cent_G(g))`.

Britnell writes it as `T(G)/|G| = ∑_{g∈G} (|Cent_G(g)|/|G|) k(Cent_G(g))`; multiplying by `|G|`
gives the form below, which avoids division entirely. -/
theorem commTripleCount_eq_sum_centralizer (G : Type*) [Group G] [Fintype G] :
    commTripleCount G = ∑ g : G, Nat.card (Subgroup.centralizer ({g} : Set G))
        * Nat.card (ConjClasses (Subgroup.centralizer ({g} : Set G))) := by
  rw [commTripleCount, Nat.card_congr (commutingTripleEquivSigmaCentralizer G), Nat.card_sigma]
  exact Finset.sum_congr rfl fun g _ => card_commutingPair _

/-! ## Simultaneous conjugation on commuting pairs, and Burnside -/

section ConjActionOnPairs

variable {G : Type*} [Group G]

/-- Conjugation preserves commutation. -/
theorem commute_conjAct_smul (a : ConjAct G) {x y : G} (h : Commute x y) :
    Commute (a • x) (a • y) := by
  have hx : a • x = ConjAct.ofConjAct a * x * (ConjAct.ofConjAct a)⁻¹ := ConjAct.smul_def a x
  have hy : a • y = ConjAct.ofConjAct a * y * (ConjAct.ofConjAct a)⁻¹ := ConjAct.smul_def a y
  rw [hx, hy, commute_iff_eq]
  calc ConjAct.ofConjAct a * x * (ConjAct.ofConjAct a)⁻¹
        * (ConjAct.ofConjAct a * y * (ConjAct.ofConjAct a)⁻¹)
      = ConjAct.ofConjAct a * (x * y) * (ConjAct.ofConjAct a)⁻¹ := by group
    _ = ConjAct.ofConjAct a * (y * x) * (ConjAct.ofConjAct a)⁻¹ := by rw [h.eq]
    _ = ConjAct.ofConjAct a * y * (ConjAct.ofConjAct a)⁻¹
          * (ConjAct.ofConjAct a * x * (ConjAct.ofConjAct a)⁻¹) := by group

/-- `G` acts on its set of ordered commuting pairs by simultaneous conjugation. -/
instance instMulActionConjActCommutingPair : MulAction (ConjAct G) (CommutingPair G) where
  smul a p := ⟨a • (p : G × G), commute_conjAct_smul a p.2⟩
  one_smul p := Subtype.ext (one_smul (ConjAct G) (p : G × G))
  mul_smul a b p := Subtype.ext (mul_smul a b (p : G × G))

/-- The action on commuting pairs is the restriction of the componentwise conjugation action on
`G × G`: the underlying pair of `a • p` is `a • ↑p`. -/
@[simp]
theorem coe_conjAct_smul_commutingPair (a : ConjAct G) (p : CommutingPair G) :
    ((a • p : CommutingPair G) : G × G) = a • (p : G × G) := rfl

/-- Conjugation fixes an element exactly when the conjugator commutes with it. -/
theorem conjAct_smul_eq_self_iff (a : ConjAct G) (x : G) :
    a • x = x ↔ Commute (ConjAct.ofConjAct a) x := by
  rw [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, commute_iff_eq]

/-- A commuting pair is fixed by conjugation exactly when the conjugator commutes with both of
its entries — that is, exactly when adjoining the conjugator gives a commuting triple. -/
theorem mem_fixedBy_commutingPair (a : ConjAct G) (p : CommutingPair G) :
    p ∈ fixedBy (CommutingPair G) a ↔
      Commute (ConjAct.ofConjAct a) p.1.1 ∧ Commute (ConjAct.ofConjAct a) p.1.2 := by
  rw [mem_fixedBy, Subtype.ext_iff, coe_conjAct_smul_commutingPair, Prod.ext_iff]
  exact and_congr (conjAct_smul_eq_self_iff a p.1.1) (conjAct_smul_eq_self_iff a p.1.2)

/-- Splitting a commuting triple by its first entry, Burnside-style: the first entry is a
conjugator, and the other two entries form a commuting pair that it fixes. -/
def commutingTripleEquivSigmaFixedBy (G : Type*) [Group G] :
    CommutingTriple G ≃ Σ a : ConjAct G, fixedBy (CommutingPair G) a where
  toFun t :=
    ⟨ConjAct.toConjAct t.1.1,
      ⟨⟨(t.1.2.1, t.1.2.2), t.2.2.2⟩,
        (mem_fixedBy_commutingPair _ _).mpr ⟨t.2.1, t.2.2.1⟩⟩⟩
  invFun x :=
    ⟨(ConjAct.ofConjAct x.1, x.2.1.1.1, x.2.1.1.2),
      ⟨((mem_fixedBy_commutingPair x.1 x.2.1).mp x.2.2).1,
       ((mem_fixedBy_commutingPair x.1 x.2.1).mp x.2.2).2,
       x.2.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The commuting pairs fixed by `g` are exactly the commuting pairs of the centralizer of `g`.
This is the bridge between the two decompositions of a commuting triple by its first entry:
Burnside's (`commutingTripleEquivSigmaFixedBy`) and Britnell's
(`commutingTripleEquivSigmaCentralizer`). -/
def fixedByEquivCommutingPairCentralizer (g : G) :
    fixedBy (CommutingPair G) (ConjAct.toConjAct g)
      ≃ CommutingPair (Subgroup.centralizer ({g} : Set G)) where
  toFun p :=
    ⟨(⟨p.1.1.1, Subgroup.mem_centralizer_singleton_iff.mpr
        ((mem_fixedBy_commutingPair _ _).mp p.2).1.symm⟩,
      ⟨p.1.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
        ((mem_fixedBy_commutingPair _ _).mp p.2).2.symm⟩),
     Subtype.ext p.1.2⟩
  invFun q :=
    ⟨⟨((q.1.1 : G), (q.1.2 : G)), Subtype.ext_iff.mp q.2⟩,
     (mem_fixedBy_commutingPair _ _).mpr
       ⟨(Subgroup.mem_centralizer_singleton_iff.mp q.1.1.2).symm,
        (Subgroup.mem_centralizer_singleton_iff.mp q.1.2.2).symm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Britnell's fiber count**: "the number of commuting triples of `G` whose first element is
`g` is `|Cent_G(g)| · k(Cent_G(g))`."  Here the left-hand side is written as the number of
commuting pairs fixed by `g` under simultaneous conjugation, which is the same thing. -/
theorem card_fixedBy_commutingPair (g : G) :
    Nat.card (fixedBy (CommutingPair G) (ConjAct.toConjAct g))
      = Nat.card (Subgroup.centralizer ({g} : Set G))
        * Nat.card (ConjClasses (Subgroup.centralizer ({g} : Set G))) := by
  rw [Nat.card_congr (fixedByEquivCommutingPairCentralizer g), card_commutingPair]

end ConjActionOnPairs

/-- **Burnside's lemma for commuting triples.**  For a finite group `G`, the number of ordered
pairwise-commuting triples equals `|G|` times the number of orbits of `G` acting on its ordered
commuting pairs by simultaneous conjugation.

Combined with `A061256_eq_card_orbits` below, this says that `T(n)/n!` *is* the number of
conjugacy classes of ordered commuting pairs in `S_n` — OEIS comment 2, which OEIS records only
as "it appears that". -/
theorem commTripleCount_eq_card_orbits_mul_card (G : Type*) [Group G] [Finite G] :
    commTripleCount G
      = Nat.card (orbitRel.Quotient (ConjAct G) (CommutingPair G)) * Nat.card G := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have _ : Fintype (ConjAct G) := Fintype.ofFinite (ConjAct G)
  have _ : Fintype (CommutingPair G) := Fintype.ofFinite (CommutingPair G)
  have _ : ∀ a : ConjAct G, Fintype (fixedBy (CommutingPair G) a) := fun a =>
    Fintype.ofFinite (fixedBy (CommutingPair G) a)
  have _ : Fintype (orbitRel.Quotient (ConjAct G) (CommutingPair G)) :=
    Fintype.ofFinite (orbitRel.Quotient (ConjAct G) (CommutingPair G))
  calc commTripleCount G
      = Nat.card (Σ a : ConjAct G, fixedBy (CommutingPair G) a) :=
        Nat.card_congr (commutingTripleEquivSigmaFixedBy G)
    _ = ∑ a : ConjAct G, Nat.card (fixedBy (CommutingPair G) a) := Nat.card_sigma
    _ = ∑ a : ConjAct G, Fintype.card (fixedBy (CommutingPair G) a) :=
        Finset.sum_congr rfl fun a _ => Nat.card_eq_fintype_card
    _ = Fintype.card (orbitRel.Quotient (ConjAct G) (CommutingPair G))
          * Fintype.card (ConjAct G) :=
        MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (ConjAct G) (CommutingPair G)
    _ = Nat.card (orbitRel.Quotient (ConjAct G) (CommutingPair G)) * Nat.card G := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          Nat.card_congr ConjAct.ofConjAct.toEquiv]

/-- The order of a finite group divides its number of commuting triples.  This is what makes
`T(n)/n!` a genuine natural number rather than a truncated quotient. -/
theorem card_dvd_commTripleCount (G : Type*) [Group G] [Finite G] :
    Nat.card G ∣ commTripleCount G :=
  ⟨Nat.card (orbitRel.Quotient (ConjAct G) (CommutingPair G)), by
    rw [commTripleCount_eq_card_orbits_mul_card, mul_comm]⟩

/-! ## The symmetric group: A072169 and A061256 -/

/-- `A072169 n` is `T(n)`: the number of ordered triples of pairwise-commuting permutations of
`Fin n`.  OEIS A072169, "Commuting permutations: number of ordered triples of permutations
f, g, h in Symm(n) which all commute". -/
noncomputable def A072169 (n : ℕ) : ℕ := commTripleCount (Equiv.Perm (Fin n))

/-- `A061256 n` is `T(n)/n!`.  OEIS A061256 formula 1, `a(n) = A072169(n) / n!`; the division is
exact by `factorial_dvd_A072169`. -/
noncomputable def A061256 (n : ℕ) : ℕ := A072169 n / n !

/-- The symmetric group on `Fin n` has order `n !`. -/
theorem card_perm_fin (n : ℕ) : Nat.card (Equiv.Perm (Fin n)) = n ! := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- `n !` divides `T(n)`, so `A061256` is exact division. -/
theorem factorial_dvd_A072169 (n : ℕ) : n ! ∣ A072169 n := by
  have h := card_dvd_commTripleCount (Equiv.Perm (Fin n))
  rwa [card_perm_fin] at h

/-- OEIS A072169 formula: `A072169(n) = A061256(n) * n!`. -/
theorem A072169_eq_factorial_mul (n : ℕ) : A072169 n = n ! * A061256 n :=
  (Nat.mul_div_cancel' (factorial_dvd_A072169 n)).symm

/-- **OEIS A061256, comment 2**: `T(n)/n!` is the number of conjugacy classes of ordered
commuting pairs of permutations, i.e. the number of orbits of `S_n` acting on its commuting
pairs by simultaneous conjugation. -/
theorem A061256_eq_card_orbits (n : ℕ) :
    A061256 n = Nat.card (orbitRel.Quotient (ConjAct (Equiv.Perm (Fin n)))
      (CommutingPair (Equiv.Perm (Fin n)))) := by
  have h : A072169 n
      = Nat.card (orbitRel.Quotient (ConjAct (Equiv.Perm (Fin n)))
          (CommutingPair (Equiv.Perm (Fin n)))) * n ! := by
    rw [A072169, commTripleCount_eq_card_orbits_mul_card, card_perm_fin]
  rw [A061256, h, Nat.mul_div_cancel _ n.factorial_pos]

/-! ## Kernel certificates at `n ≤ 4`

The pinned OEIS terms are `A072169 = 1, 1, 8, 48, 504, …` and `A061256 = 1, 1, 4, 8, 21, …`.
All five triple counts below are closed by kernel `decide` (no `native_decide`); `n = 4`
enumerates `24³ = 13824` triples of permutations and is the expensive one. -/

/-- `T(0) = 1`: `S_0` is the trivial group, so the only commuting triple is `(1, 1, 1)`. -/
theorem A072169_zero : A072169 0 = 1 := by
  show commTripleCount (Equiv.Perm (Fin 0)) = 1
  rw [commTripleCount_eq_fintypeCard]
  decide

/-- `T(1) = 1`. -/
theorem A072169_one : A072169 1 = 1 := by
  show commTripleCount (Equiv.Perm (Fin 1)) = 1
  rw [commTripleCount_eq_fintypeCard]
  decide

/-- `T(2) = 8`: `S_2` is abelian of order `2`, so all `2³` triples commute. -/
theorem A072169_two : A072169 2 = 8 := by
  show commTripleCount (Equiv.Perm (Fin 2)) = 8
  rw [commTripleCount_eq_fintypeCard]
  decide

set_option maxRecDepth 100000 in
/-- `T(3) = 48`, out of `6³ = 216` triples in `S_3`. -/
theorem A072169_three : A072169 3 = 48 := by
  show commTripleCount (Equiv.Perm (Fin 3)) = 48
  rw [commTripleCount_eq_fintypeCard]
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1000000 in
/-- `T(4) = 504`, out of `24³ = 13824` triples in `S_4`. -/
theorem A072169_four : A072169 4 = 504 := by
  show commTripleCount (Equiv.Perm (Fin 4)) = 504
  rw [commTripleCount_eq_fintypeCard]
  decide

/-- `A061256(0) = 1 = 1/0!`. -/
theorem A061256_zero : A061256 0 = 1 := by
  rw [A061256, A072169_zero]; rfl

/-- `A061256(1) = 1 = 1/1!`. -/
theorem A061256_one : A061256 1 = 1 := by
  rw [A061256, A072169_one]; rfl

/-- `A061256(2) = 4 = 8/2!`. -/
theorem A061256_two : A061256 2 = 4 := by
  rw [A061256, A072169_two]; rfl

/-- `A061256(3) = 8 = 48/3!`. -/
theorem A061256_three : A061256 3 = 8 := by
  rw [A061256, A072169_three]; rfl

/-- `A061256(4) = 21 = 504/4!`. -/
theorem A061256_four : A061256 4 = 21 := by
  rw [A061256, A072169_four]; rfl

/-! ## Nonvacuity witnesses

Each general theorem is instantiated at a concrete group, jointly with the certificates, so the
statements are known to have content. -/

section GroundTruth

/-- Britnell's equation instantiated at `S_3`: `∑_{g ∈ S_3} |Cent(g)| · k(Cent(g)) = 48`.
The summands are `6·3` (identity), `2·2` (three transpositions) and `3·3` (two 3-cycles). -/
example : ∑ g : Equiv.Perm (Fin 3),
      Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 3))))
        * Nat.card (ConjClasses (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 3))))) = 48 := by
  rw [← commTripleCount_eq_sum_centralizer]
  exact A072169_three

/-- The Burnside theorem instantiated at `S_4`: `S_4` has exactly `21` orbits on its ordered
commuting pairs.  This orbit count is not itself amenable to `decide` — it is obtained from the
kernel-checked triple count `T(4) = 504` through `commTripleCount_eq_card_orbits_mul_card`. -/
example : Nat.card (orbitRel.Quotient (ConjAct (Equiv.Perm (Fin 4)))
    (CommutingPair (Equiv.Perm (Fin 4)))) = 21 :=
  (A061256_eq_card_orbits 4).symm.trans A061256_four

/-- The commuting-triple type is inhabited at every `n` (take the identity three times), so the
counted sets are nonempty. -/
example (n : ℕ) : Nonempty (CommutingTriple (Equiv.Perm (Fin n))) :=
  ⟨⟨(1, 1, 1), Commute.one_left 1, Commute.one_left 1, Commute.one_left 1⟩⟩

/-- Britnell's Lemma 1 run backwards at `S_3`: the kernel counts `18` commuting pairs, and the
lemma converts that into the conjugacy class count `k(S_3) = 3`, which is not itself amenable to
`decide`. -/
example : Nat.card (ConjClasses (Equiv.Perm (Fin 3))) = 3 := by
  have hpair : Nat.card (CommutingPair (Equiv.Perm (Fin 3))) = 18 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [card_commutingPair, card_perm_fin] at hpair
  simp only [Nat.factorial] at hpair
  omega

end GroundTruth

end GroupCount

/-! ## Signature audit (section variable check) -/

#check @GroupCount.commute_conjAct_smul
#check @GroupCount.instMulActionConjActCommutingPair
#check @GroupCount.coe_conjAct_smul_commutingPair
#check @GroupCount.conjAct_smul_eq_self_iff
#check @GroupCount.mem_fixedBy_commutingPair

/-! ## Axiom audit -/

#print axioms GroupCount.instDecidableCommute
#print axioms GroupCount.commTripleCount_eq_fintypeCard
#print axioms GroupCount.card_commutingPair
#print axioms GroupCount.commutingTripleEquivSigmaCentralizer
#print axioms GroupCount.commTripleCount_eq_sum_centralizer
#print axioms GroupCount.coe_conjAct_smul_commutingPair
#print axioms GroupCount.commute_conjAct_smul
#print axioms GroupCount.instMulActionConjActCommutingPair
#print axioms GroupCount.conjAct_smul_eq_self_iff
#print axioms GroupCount.mem_fixedBy_commutingPair
#print axioms GroupCount.commutingTripleEquivSigmaFixedBy
#print axioms GroupCount.fixedByEquivCommutingPairCentralizer
#print axioms GroupCount.card_fixedBy_commutingPair
#print axioms GroupCount.commTripleCount_eq_card_orbits_mul_card
#print axioms GroupCount.card_dvd_commTripleCount
#print axioms GroupCount.card_perm_fin
#print axioms GroupCount.factorial_dvd_A072169
#print axioms GroupCount.A072169_eq_factorial_mul
#print axioms GroupCount.A061256_eq_card_orbits
#print axioms GroupCount.A072169_zero
#print axioms GroupCount.A072169_one
#print axioms GroupCount.A072169_two
#print axioms GroupCount.A072169_three
#print axioms GroupCount.A072169_four
#print axioms GroupCount.A061256_zero
#print axioms GroupCount.A061256_one
#print axioms GroupCount.A061256_two
#print axioms GroupCount.A061256_three
#print axioms GroupCount.A061256_four
