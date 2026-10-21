/-
# Tarnauceanu — a characterization of ZM-groups

## Source

M. Tărnăuceanu, *A characterization of ZM-groups*, arXiv:1704.03083
(April 11, 2017).  Theorem 1.1 and Corollary 1.2; Corollary 1.2 settles
Conjecture 6 of Tărnăuceanu, *On a generalization of the Gauss formula*,
Asian-Eur. J. Math. 10 (2017), no. 1, 1750008.

Verbatim (LaTeX of the source):

```
Given a finite group $G$, we consider the functions
$$\varphi(G)=|\{a\in G \mid o(a)=\exp(G)\}| \mbox{ and }
  S(G)=\dd\sum_{H\leq\, G}\varphi(H).$$

Theorem 1.1. Let $G$ be a finite group. Then $S(G)\geq |G|, and we have
equality if and only if $G$ is a ZM-group, i.e. a group with all Sylow
subgroups cyclic.

Corollary 1.2. Let $G$ be a finite nilpotent group. Then $S(G)\geq |G|$,
and we have equality if and only if $G$ is cyclic.
```

## Status

Proved in the paper (date of this card: 2026-10-21).  The paper's
"if" direction goes through Hölder's presentation `ZM(m,n,r)` and
Calhoun's classification of its subgroups.  The proof here avoids both:

* the map `a ↦ (zpowers a, a)` injects `G` into the disjoint union of
  the sets `{a ∈ H | o(a) = exp H}`, because `o(a) = |⟨a⟩| = exp ⟨a⟩`;
  this is `S(G) ≥ |G|`;
* equality holds iff that injection is surjective, i.e. iff every
  `a ∈ H` with `o(a) = exp H` generates `H`;
* in a Z-group every subgroup `H` is a Z-group, so `exp H = |H|`
  (`IsZGroup.exponent_eq_card`) and such an `a` generates `H`;
* if a Sylow `p`-subgroup `P` is not cyclic, a `p`-group has an element
  of order `exp P`, and that element cannot generate `P`.

"ZM-group" is Mathlib's `IsZGroup` (all Sylow subgroups cyclic).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.TarnauceanuZMGroups

open Subgroup

/-- Tărnăuceanu's `φ(G) = |{a ∈ G | o(a) = exp(G)}|`: the number of elements
of `G` whose order equals the exponent of `G`. -/
noncomputable def tarnPhi (G : Type*) [Group G] : ℕ :=
  Nat.card {a : G // orderOf a = Monoid.exponent G}

/-- Tărnăuceanu's `S(G) = ∑_{H ≤ G} φ(H)` for a finite group `G`, the sum
running over all subgroups `H` of `G`. -/
noncomputable def tarnS (G : Type*) [Group G] [Finite G] : ℕ :=
  letI := Fintype.ofFinite (Subgroup G)
  ∑ H : Subgroup G, tarnPhi H

variable {G : Type*} [Group G]

/-- The disjoint union `⊔_{H ≤ G} {a ∈ H | o(a) = exp H}`, whose cardinality
is `S(G)`. -/
abbrev TarnSigma (G : Type*) [Group G] : Type _ :=
  Σ H : Subgroup G, {a : H // orderOf a = Monoid.exponent H}

/-- `S(G)` is the cardinality of the disjoint union `TarnSigma G`. -/
theorem tarnS_eq_card_sigma [Finite G] : tarnS G = Nat.card (TarnSigma G) := by
  letI := Fintype.ofFinite (Subgroup G)
  rw [Nat.card_sigma]
  rfl

/-- A generator `a` of `⟨a⟩` has order `exp ⟨a⟩`. -/
theorem orderOf_eq_exponent_zpowers (a : G) :
    orderOf (⟨a, mem_zpowers a⟩ : zpowers a) = Monoid.exponent (zpowers a) := by
  rw [orderOf_mk, IsCyclic.exponent_eq_card, Nat.card_zpowers]

/-- The map `a ↦ (⟨a⟩, a)` from `G` into `TarnSigma G`. -/
def toTarnSigma (a : G) : TarnSigma G :=
  ⟨zpowers a, ⟨a, mem_zpowers a⟩, orderOf_eq_exponent_zpowers a⟩

/-- The map `a ↦ (⟨a⟩, a)` is injective. -/
theorem toTarnSigma_injective : Function.Injective (toTarnSigma (G := G)) := by
  intro a b hab
  have h := congrArg (fun x : TarnSigma G => ((x.2.1 : x.1) : G)) hab
  simpa [toTarnSigma] using h

/-- The map `a ↦ (⟨a⟩, a)` is surjective iff every element `a ∈ H` whose order
is `exp H` generates `H`. -/
theorem toTarnSigma_surjective_iff :
    Function.Surjective (toTarnSigma (G := G)) ↔
      ∀ H : Subgroup G, ∀ a : H, orderOf a = Monoid.exponent H → zpowers (a : G) = H := by
  constructor
  · intro hsurj H a ha
    obtain ⟨b, hb⟩ := hsurj ⟨H, a, ha⟩
    have h1 : zpowers b = H := congrArg Sigma.fst hb
    have h2 : b = (a : G) := by
      subst h1
      have := congrArg (fun x : TarnSigma G => ((x.2.1 : x.1) : G)) hb
      simpa [toTarnSigma] using this
    rw [← h2, h1]
  · rintro hgen ⟨H, ⟨a, hmem⟩, ha⟩
    refine ⟨a, ?_⟩
    have h1 : zpowers a = H := hgen H ⟨a, hmem⟩ ha
    subst h1
    rfl

/-- **Theorem 1.1, inequality** (Tărnăuceanu, arXiv:1704.03083):
for a finite group `G`, `|G| ≤ S(G)`. -/
theorem card_le_tarnS [Finite G] : Nat.card G ≤ tarnS G := by
  rw [tarnS_eq_card_sigma]
  exact Nat.card_le_card_of_injective _ toTarnSigma_injective

/-- `S(G) = |G|` iff every element `a ∈ H ≤ G` with `o(a) = exp H` generates `H`. -/
theorem tarnS_eq_card_iff_forall_zpowers_eq [Finite G] :
    tarnS G = Nat.card G ↔
      ∀ H : Subgroup G, ∀ a : H, orderOf a = Monoid.exponent H → zpowers (a : G) = H := by
  rw [tarnS_eq_card_sigma, ← toTarnSigma_surjective_iff]
  constructor
  · intro hcard
    exact ((Nat.bijective_iff_injective_and_card toTarnSigma).mpr
      ⟨toTarnSigma_injective, hcard.symm⟩).2
  · intro hsurj
    exact (Nat.card_eq_of_bijective _ ⟨toTarnSigma_injective, hsurj⟩).symm

/-- In a finite Z-group, an element `a ∈ H` with `o(a) = exp H` generates `H`,
because `H` is again a Z-group and so `exp H = |H|`. -/
theorem zpowers_eq_of_isZGroup [Finite G] [IsZGroup G] (H : Subgroup G) (a : H)
    (ha : orderOf a = Monoid.exponent H) : zpowers (a : G) = H := by
  have hexp : Monoid.exponent H = Nat.card H := IsZGroup.exponent_eq_card H
  have hord : orderOf (a : G) = Nat.card H := by rw [orderOf_coe, ha, hexp]
  refine eq_of_le_of_card_ge (zpowers_le.mpr a.2) ?_
  rw [Nat.card_zpowers, hord]

/-- If every element `a ∈ H ≤ G` with `o(a) = exp H` generates `H`, then every
Sylow subgroup of the finite group `G` is cyclic: a `p`-group `P` has an
element of order `exp P`. -/
theorem isZGroup_of_forall_zpowers_eq [Finite G]
    (hgen : ∀ H : Subgroup G, ∀ a : H, orderOf a = Monoid.exponent H → zpowers (a : G) = H) :
    IsZGroup G := by
  refine ⟨fun p hp P => ?_⟩
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : Monoid.exponent P ∣ p ^ n := hn ▸ Group.exponent_dvd_nat_card
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent (P : Subgroup G)
  have hg' : orderOf g = Monoid.exponent P := by
    rw [hg, hk, hp.factorization_pow, Finsupp.single_eq_same]
  have hz : zpowers (g : G) = P := hgen P g hg'
  refine isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨g, ?_⟩
  rw [← orderOf_coe, ← Nat.card_zpowers, hz]

/-- **Theorem 1.1, equality case** (Tărnăuceanu, arXiv:1704.03083):
for a finite group `G`, `S(G) = |G|` iff `G` is a ZM-group (all Sylow subgroups
cyclic, Mathlib's `IsZGroup`). -/
theorem tarnS_eq_card_iff_isZGroup [Finite G] : tarnS G = Nat.card G ↔ IsZGroup G := by
  rw [tarnS_eq_card_iff_forall_zpowers_eq]
  exact ⟨isZGroup_of_forall_zpowers_eq, fun _ => zpowers_eq_of_isZGroup⟩

/-- **Theorem 1.1, strict form** (Tărnăuceanu, arXiv:1704.03083):
for a finite group `G`, `|G| < S(G)` iff some Sylow subgroup of `G` is not
cyclic. -/
theorem card_lt_tarnS_iff_not_isZGroup [Finite G] : Nat.card G < tarnS G ↔ ¬IsZGroup G := by
  rw [← tarnS_eq_card_iff_isZGroup, lt_iff_le_and_ne]
  exact ⟨fun h => fun he => h.2 he.symm, fun h => ⟨card_le_tarnS, fun he => h he.symm⟩⟩

/-- **Theorem 1.1** (Tărnăuceanu, arXiv:1704.03083): for a finite group `G`,
`|G| ≤ S(G)`, with equality iff all Sylow subgroups of `G` are cyclic. -/
theorem thm_1_1 [Finite G] : Nat.card G ≤ tarnS G ∧ (tarnS G = Nat.card G ↔ IsZGroup G) :=
  ⟨card_le_tarnS, tarnS_eq_card_iff_isZGroup⟩

/-- **Corollary 1.2** (Tărnăuceanu, arXiv:1704.03083; Conjecture 6 of
Tărnăuceanu, Asian-Eur. J. Math. 10 (2017) 1750008): for a finite nilpotent
group `G`, `|G| ≤ S(G)`, with equality iff `G` is cyclic. -/
theorem cor_1_2 [Finite G] [Group.IsNilpotent G] :
    Nat.card G ≤ tarnS G ∧ (tarnS G = Nat.card G ↔ IsCyclic G) := by
  refine ⟨card_le_tarnS, ?_⟩
  rw [tarnS_eq_card_iff_isZGroup]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-! ## Ground truth -/

/-- For a finite cyclic group of order `n`, `φ(G) = φ(n)` (Euler's totient). -/
theorem tarnPhi_eq_totient [Finite G] [IsCyclic G] : tarnPhi G = (Nat.card G).totient := by
  classical
  letI := Fintype.ofFinite G
  rw [tarnPhi, IsCyclic.exponent_eq_card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_orderOf_eq_totient dvd_rfl

/-- `φ(C₆) = 2`. -/
example : tarnPhi (Multiplicative (ZMod 6)) = 2 := by
  rw [tarnPhi_eq_totient, Nat.card_eq_fintype_card]
  rfl

/-- `S(S₃) = 6 = |S₃|`: `S₃` has order `6`, squarefree, so it is a Z-group
(`S(S₃) = 1 + 3·1 + 2 + 0`). -/
example : tarnS (Equiv.Perm (Fin 3)) = 6 := by
  have hZ : IsZGroup (Equiv.Perm (Fin 3)) := IsZGroup.of_squarefree (by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
      show Nat.factorial 3 = 2 * 3 from rfl]
    exact Nat.squarefree_mul_iff.mpr ⟨by decide, Nat.prime_two.squarefree,
      Nat.prime_three.squarefree⟩)
  rw [tarnS_eq_card_iff_isZGroup.mpr hZ, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

/-- The Klein four-group `V₄` has `|V₄| = 4 < S(V₄)` (indeed `S(V₄) = 1 + 3 + 3 = 7`),
since `exp V₄ = 2 ≠ 4` rules out the Z-group property. -/
example {V : Type*} [Group V] [Finite V] [IsKleinFour V] : Nat.card V < tarnS V := by
  refine card_lt_tarnS_iff_not_isZGroup.mpr fun hZ => ?_
  have h := IsZGroup.exponent_eq_card (G := V)
  rw [IsKleinFour.exponent_two, IsKleinFour.card_four] at h
  exact absurd h (by decide)

/-- The concrete Klein four-group `D₂` (dihedral group of order 4): `4 < S(D₂)`,
exhibiting a finite nilpotent non-cyclic group for Corollary 1.2. -/
example : Nat.card (DihedralGroup 2) < tarnS (DihedralGroup 2) := by
  refine card_lt_tarnS_iff_not_isZGroup.mpr fun hZ => ?_
  have h := IsZGroup.exponent_eq_card (DihedralGroup 2)
  rw [IsKleinFour.exponent_two, IsKleinFour.card_four] at h
  exact absurd h (by decide)

end Candidates.TarnauceanuZMGroups
