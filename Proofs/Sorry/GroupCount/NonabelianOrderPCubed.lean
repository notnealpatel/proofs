/-
# Nonabelian groups of order `p ^ 3`: structure and commuting probability

## Source (classical; recorded 2026-10-21)

Standard structure theory of groups of order `p ^ 3`: e.g. D. Gorenstein,
*Finite Groups* (1968), §5.5 (Thm 5.5.1 area); J. J. Rotman, *An Introduction to
the Theory of Groups*, 4th ed., Ch. 4 (center of `p`-groups, groups of order
`p ^ 3`).  The commuting-probability equality case is W. H. Gustafson, "What is
the probability that two group elements commute?", Amer. Math. Monthly 80
(1973) 1031–1034 (value `5 / 8` at `p = 2`).

## Informal statement (scout spec, verbatim)

```
If G is nonabelian of order p^3 (p prime), then |Z(G)| = p, G' = Z(G),
G/Z(G) ≅ C_p × C_p, k(G) = p^2 + p - 1, and commProb G = (p^2 + p - 1)/p^4
(so the Lescot bound is attained).
```

## Correction to the spec

The denominator `p ^ 4` in the spec is a typo: Mathlib's `commProb_def'` gives
`commProb G = k(G) / |G| = (p ^ 2 + p - 1) / p ^ 3` (at `p = 2` this is
Gustafson's `5 / 8`, not `5 / 16`).  The module proves the `p ^ 3` form.

## Mathlib absence check (2026-10-21)

`leandoc` searches "nonabelian group order p cubed center", "commProb card
prime pow three", "commutator eq center p group", "card center eq prime not
commutative" return only the order-`p ^ 2` results
(`IsPGroup.isMulCommutative_of_card_eq_prime_sq`,
`IsPGroup.card_center_eq_prime_pow`, `commProb_def'`); nothing about `p ^ 3`.

## Formal reading

`G` is a group with `Nat.card G = p ^ 3`, `p` prime (`[Fact p.Prime]`), and
nonabelian is `¬ IsMulCommutative G`.  `C_p` is `Multiplicative (ZMod p)`;
`k(G)` is `Nat.card (ConjClasses G)`; `commProb` is Mathlib's.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.NonabelianOrderPCubed

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]

/-- Every subgroup of a group of order `p ^ n` has order `p ^ k` for some `k ≤ n`. -/
theorem exists_card_subgroup_eq_prime_pow {n : ℕ} (hG : Nat.card G = p ^ n) (H : Subgroup G) :
    ∃ k ≤ n, Nat.card H = p ^ k := by
  have hdvd : Nat.card H ∣ p ^ n := hG ▸ Subgroup.card_subgroup_dvd_card H
  exact (Nat.dvd_prime_pow hp.out).mp hdvd

/-- In a nonabelian group of order `p ^ 3`, the center has order exactly `p`. -/
theorem card_center_eq_prime (hG : Nat.card G = p ^ 3) (hnc : ¬ IsMulCommutative G) :
    Nat.card (center G) = p := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hG (by norm_num)
  obtain ⟨k', hk'3, hk'⟩ := exists_card_subgroup_eq_prime_pow hG (center G)
  have hkk' : k = k' := Nat.pow_right_injective hp.out.two_le (hk.symm.trans hk')
  subst hkk'
  have hidx : (center G).index * p ^ k = p ^ 3 := by
    rw [← hk, ← hG, mul_comm]; exact (center G).card_mul_index
  interval_cases k
  · simpa using hk
  · -- `G ⧸ Z(G)` has order `p`, hence is cyclic and `G` is abelian
    have hq : Nat.card (G ⧸ center G) = p := by
      rw [← Subgroup.index]
      have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
      have : (center G).index * p ^ 2 = p * p ^ 2 := by rw [hidx]; ring
      exact Nat.eq_of_mul_eq_mul_right hp2 this
    have : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hq
    exact absurd (isMulCommutative_of_isCyclic_quotient_center_self G) hnc
  · -- `Z(G) = G`
    have htop : center G = ⊤ := Subgroup.eq_top_of_card_eq _ (hk.trans hG.symm)
    exact absurd ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)⟩⟩ hnc

/-- In a nonabelian group of order `p ^ 3`, the central quotient `G ⧸ Z(G)` has order `p ^ 2`. -/
theorem card_quotient_center (hG : Nat.card G = p ^ 3) (hnc : ¬ IsMulCommutative G) :
    Nat.card (G ⧸ center G) = p ^ 2 := by
  have hZ := card_center_eq_prime hG hnc
  have hmul : Nat.card (center G) * (center G).index = p ^ 3 := by
    rw [(center G).card_mul_index, hG]
  rw [← Subgroup.index]
  rw [hZ] at hmul
  have : p * (center G).index = p * p ^ 2 := by rw [hmul]; ring
  exact Nat.eq_of_mul_eq_mul_left hp.out.pos this

/-- In a nonabelian group of order `p ^ 3`, the derived subgroup equals the center. -/
theorem commutator_eq_center (hG : Nat.card G = p ^ 3) (hnc : ¬ IsMulCommutative G) :
    commutator G = center G := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  have hZ := card_center_eq_prime hG hnc
  have hQcomm : IsMulCommutative (G ⧸ center G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (card_quotient_center hG hnc)
  have hle : commutator G ≤ center G :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hQcomm
  have hne : commutator G ≠ ⊥ := by
    intro hbot
    rw [commutator_eq_bot_iff_center_eq_top] at hbot
    exact hnc ⟨⟨fun a b => Subgroup.mem_center_iff.mp (hbot ▸ Subgroup.mem_top b) a⟩⟩
  have hdvd : Nat.card (commutator G) ∣ p := hZ ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | hpc
  · exact absurd (Subgroup.card_eq_one.mp h1) hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hpc])

/-- In a nonabelian group of order `p ^ 3`, the centralizer of a noncentral element has order
`p ^ 2`. -/
theorem card_centralizer_of_not_mem_center (hG : Nat.card G = p ^ 3)
    (hnc : ¬ IsMulCommutative G) {x : G} (hx : x ∉ center G) :
    Nat.card (centralizer {x} : Subgroup G) = p ^ 2 := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  have hZ := card_center_eq_prime hG hnc
  set C : Subgroup G := centralizer {x} with hC
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hZC : center G ≤ C := Subgroup.center_le_centralizer _
  obtain ⟨j, hj3, hj⟩ := exists_card_subgroup_eq_prime_pow hG C
  have hgt : p < p ^ j := by
    by_contra hle
    have heq : center G = C :=
      Subgroup.eq_of_le_of_card_ge hZC (by rw [hZ, hj]; omega)
    exact hx (heq ▸ hxC)
  have hne : j ≠ 3 := by
    rintro rfl
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq _ (hj.trans hG.symm)
    refine hx (Subgroup.mem_center_iff.mpr fun g => ?_)
    have hg : g ∈ C := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    interval_cases j
    · have hp1 := hp.out.one_lt
      rw [pow_zero] at hgt
      omega
    · rw [pow_one] at hgt
      exact absurd hgt (lt_irrefl p)
  rw [hj, show j = 2 by omega]

/-- In a nonabelian group of order `p ^ 3`, the number of commuting pairs `(x, y)` is
`p ^ 3 * (p ^ 2 + p - 1)`, recorded subtraction-free as `N + p ^ 3 = p ^ 3 * (p ^ 2 + p)`. -/
theorem card_commute_add (hG : Nat.card G = p ^ 3) (hnc : ¬ IsMulCommutative G) :
    Nat.card { q : G × G // Commute q.1 q.2 } + p ^ 3 = p ^ 3 * (p ^ 2 + p) := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 3 hp.out.ne_zero)
  letI : Fintype G := Fintype.ofFinite G
  have hZ := card_center_eq_prime hG hnc
  have hsum : Nat.card { q : G × G // Commute q.1 q.2 } =
      ∑ x : G, Nat.card (centralizer {x} : Subgroup G) := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : G => Commute a b),
      Nat.card_sigma]
    refine Finset.sum_congr rfl fun x _ => Nat.card_congr ?_
    exact Equiv.subtypeEquivRight fun y => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact eq_comm
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset G)
    (fun x => x ∈ center G) (fun x => Nat.card (centralizer {x} : Subgroup G))
  have hin : ∑ x ∈ Finset.univ.filter (fun x => x ∈ center G),
      Nat.card (centralizer {x} : Subgroup G) =
      ∑ x ∈ Finset.univ.filter (fun x => x ∈ center G), p ^ 3 := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxZ : x ∈ center G := (Finset.mem_filter.mp hx).2
    have htop : (centralizer {x} : Subgroup G) = ⊤ := by
      refine eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_singleton_iff.mpr ?_
      exact Subgroup.mem_center_iff.mp hxZ g
    rw [htop, Subgroup.card_top, hG]
  have hout : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ center G),
      Nat.card (centralizer {x} : Subgroup G) =
      ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ center G), p ^ 2 :=
    Finset.sum_congr rfl fun x hx =>
      card_centralizer_of_not_mem_center hG hnc (Finset.mem_filter.mp hx).2
  have hcardZ : (Finset.univ.filter (fun x => x ∈ center G)).card = p := by
    rw [← hZ, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hcards := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
    (fun x => x ∈ center G)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hG, hcardZ] at hcards
  rw [hsum, ← hsplit, hin, hout, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
    hcardZ]
  set b := (Finset.univ.filter (fun x => ¬ x ∈ center G)).card
  have hb : p ^ 3 * (p ^ 2 + p) = p * p ^ 3 + p ^ 2 * (p + b) := by rw [hcards]; ring
  rw [hb]; ring

/-- **Class number.** A nonabelian group of order `p ^ 3` has exactly `p ^ 2 + p - 1` conjugacy
classes (subtraction-free form). -/
theorem card_conjClasses_add_one (hG : Nat.card G = p ^ 3) (hnc : ¬ IsMulCommutative G) :
    Nat.card (ConjClasses G) + 1 = p ^ 2 + p := by
  have hN := card_commute_add hG hnc
  rw [card_comm_eq_card_conjClasses_mul_card, hG] at hN
  have hp3 : 0 < p ^ 3 := pow_pos hp.out.pos 3
  have : (Nat.card (ConjClasses G) + 1) * p ^ 3 = (p ^ 2 + p) * p ^ 3 := by
    rw [add_mul, one_mul, hN]; ring
  exact Nat.eq_of_mul_eq_mul_right hp3 this

/-- **Class number.** A nonabelian group of order `p ^ 3` has exactly `p ^ 2 + p - 1` conjugacy
classes. (The natural subtraction is harmless: `1 ≤ p ^ 2 + p`.) -/
theorem card_conjClasses (hG : Nat.card G = p ^ 3) (hnc : ¬ IsMulCommutative G) :
    Nat.card (ConjClasses G) = p ^ 2 + p - 1 := by
  have := card_conjClasses_add_one hG hnc
  omega

/-- **Commuting probability.** A nonabelian group of order `p ^ 3` has commuting probability
`(p ^ 2 + p - 1) / p ^ 3`; for `p = 2` this is Gustafson's extremal value `5 / 8`. -/
theorem commProb_eq (hG : Nat.card G = p ^ 3) (hnc : ¬ IsMulCommutative G) :
    commProb G = ((p : ℚ) ^ 2 + p - 1) / p ^ 3 := by
  have hk : ((Nat.card (ConjClasses G) : ℕ) : ℚ) + 1 = (p : ℚ) ^ 2 + p := by
    exact_mod_cast card_conjClasses_add_one hG hnc
  rw [commProb_def', hG, Nat.cast_pow]
  congr 1
  linarith

/-- **Central quotient.** For a nonabelian group of order `p ^ 3`, `G ⧸ Z(G) ≅ C_p × C_p`. -/
theorem nonempty_quotient_center_mulEquiv (hG : Nat.card G = p ^ 3)
    (hnc : ¬ IsMulCommutative G) :
    Nonempty (G ⧸ center G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p)) := by
  have hQ := card_quotient_center hG hnc
  have : Finite (G ⧸ center G) := Nat.finite_of_card_ne_zero (hQ ▸ pow_ne_zero 2 hp.out.ne_zero)
  have hQcomm : IsMulCommutative (G ⧸ center G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  have hncyc : ¬ IsCyclic (G ⧸ center G) := fun hcyc =>
    hnc (isMulCommutative_of_isCyclic_quotient_center_self G)
  have hexp : Monoid.exponent (G ⧸ center G) = p :=
    (not_isCyclic_iff_exponent_eq_prime hp.out hQ).mp hncyc
  letI : CommGroup (G ⧸ center G) :=
    { (inferInstance : Group (G ⧸ center G)) with mul_comm := hQcomm.is_comm.comm }
  -- `haveI` (opaque) rather than `letI`: only the existence of the `ZMod p`-structure is used, and
  -- an unfolded `zmodModule` blocks instance unification with the field structure on `ZMod p`.
  haveI : Module (ZMod p) (Additive (G ⧸ center G)) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (Additive.toMul x ^ p) = 0
    rw [← hexp, Monoid.pow_exponent_eq_one]; rfl
  haveI : Module.Finite (ZMod p) (Additive (G ⧸ center G)) := Module.Finite.of_finite
  have hcardA : Nat.card (Additive (G ⧸ center G)) = p ^ 2 := hQ
  have hfin : Module.finrank (ZMod p) (Additive (G ⧸ center G)) = 2 := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (G ⧸ center G))
    rw [hcardA, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hp.out.two_le this).symm
  have hfin2 : Module.finrank (ZMod p) (ZMod p × ZMod p) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  let e := LinearEquiv.ofFinrankEq (Additive (G ⧸ center G)) (ZMod p × ZMod p)
    (hfin.trans hfin2.symm)
  exact ⟨(AddEquiv.toMultiplicativeRight e.toAddEquiv).trans (MulEquiv.prodMultiplicative _ _)⟩

/-- **Structure of nonabelian groups of order `p ^ 3`.** If `G` is nonabelian of order `p ^ 3`
with `p` prime, then `|Z(G)| = p`, `G' = Z(G)`, `G ⧸ Z(G) ≅ C_p × C_p`, `G` has `p ^ 2 + p - 1`
conjugacy classes, and `commProb G = (p ^ 2 + p - 1) / p ^ 3`. -/
theorem nonabelian_order_prime_pow_three (hG : Nat.card G = p ^ 3)
    (hnc : ¬ IsMulCommutative G) :
    Nat.card (center G) = p ∧ commutator G = center G ∧
      Nonempty (G ⧸ center G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p)) ∧
      Nat.card (ConjClasses G) = p ^ 2 + p - 1 ∧
      commProb G = ((p : ℚ) ^ 2 + p - 1) / p ^ 3 :=
  ⟨card_center_eq_prime hG hnc, commutator_eq_center hG hnc,
    nonempty_quotient_center_mulEquiv hG hnc, card_conjClasses hG hnc, commProb_eq hG hnc⟩

/-! ## Non-vacuity: the hypotheses hold jointly for the dihedral group of order `8` -/

/-- The dihedral group `D₄` has order `2 ^ 3`. -/
theorem card_dihedralGroup_four : Nat.card (DihedralGroup 4) = 2 ^ 3 :=
  DihedralGroup.nat_card.trans (by norm_num)

/-- The dihedral group `D₄` is nonabelian: `r 1 * sr 0 ≠ sr 0 * r 1`. -/
theorem not_isMulCommutative_dihedralGroup_four : ¬ IsMulCommutative (DihedralGroup 4) :=
  fun h => absurd (h.is_comm.comm (DihedralGroup.r 1) (DihedralGroup.sr 0)) (by decide)

/-- Instantiation at `D₄` (order `8`, `p = 2`): commuting probability `5 / 8`. -/
example : commProb (DihedralGroup 4) = 5 / 8 := by
  rw [commProb_eq (p := 2) card_dihedralGroup_four not_isMulCommutative_dihedralGroup_four]
  norm_num

/-- Instantiation at `D₄`: five conjugacy classes, centre of order `2`. -/
example : Nat.card (ConjClasses (DihedralGroup 4)) = 5 ∧
    Nat.card (center (DihedralGroup 4)) = 2 :=
  ⟨card_conjClasses (p := 2) card_dihedralGroup_four not_isMulCommutative_dihedralGroup_four,
    card_center_eq_prime (p := 2) card_dihedralGroup_four not_isMulCommutative_dihedralGroup_four⟩

end Candidates.NonabelianOrderPCubed
