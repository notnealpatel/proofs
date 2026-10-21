/-
# Hall–Paige necessity: cyclic nontrivial Sylow 2-subgroup forbids complete mappings

## Source

* MathOverflow question 322302, "Noteworthy, but not so famous conjectures resolved
  recent years", answer 322348 by Carl-Fredrik Nyberg Brodda (2019-02-03),
  https://mathoverflow.net/a/322348 . Verbatim (re-pulled 2026-10-21 via the
  StackExchange API):

  > The Hall-Paige conjecture, first posed in 1955 by Marshall Hall and L. J. Paige, is
  > the following:
  >
  >   A finite group $G$ has a complete mapping if and only if its Sylow $2$-subgroups
  >   are not cyclic.
  >
  > Note that a complete mapping is a bijection $\phi : G \to G$ such that the function
  > given by $\psi(g) = g \phi(g)$ is also a bijection. The above statement was shown to
  > be necessary by Hall and Paige, but its sufficiency remained open until very
  > recently; [...]

* M. Hall and L. J. Paige, *Complete mappings of finite groups*, Pacific J. Math. 5
  (1955) 541–549: the necessity half formalized here.
* arXiv:1811.12671, J. N. Bray, Q. Cai, P. J. Cameron, P. Spiga, H. Zhang, *The
  Hall–Paige conjecture, and synchronization for affine and diagonal groups*: completes
  sufficiency (the case `J₄`), after Wilcox (2009) and Evans (2009).

## Boundary convention

The MO wording "Sylow 2-subgroups are not cyclic" counts the trivial group as
non-cyclic; with Mathlib's `IsCyclic` the trivial Sylow 2-subgroup *is* cyclic, and odd
order groups do have a complete mapping (`φ = id`, see
`isCompleteMapping_id_of_odd_card`). The precise necessity statement therefore carries
the hypothesis `Nontrivial P`.

## Status (2026-10-21)

Proved in the literature (Hall–Paige 1955); the full conjecture is a theorem
(Wilcox, Evans, Bray et al.). This module is a kernel-checked proof of the necessity
half, built on Mathlib's Burnside transfer (`MonoidHom.transferSylow`,
`IsCyclic.normalizer_le_centralizer`).

## Proof

`|G|` is even, so `(Nat.card G).minFac = 2`; Burnside's transfer gives a surjection
`f : G →* P` (it is `x ↦ x ^ [G : P]` on `P`, a bijection since the index is odd) whose
kernel has odd order. A complete mapping `φ` forces `∏ g, f g = (∏ g, f g) ^ 2`, so
`∏ g, f g = 1`. But `∏ g, f g = (∏ a : P, a) ^ |ker f|`, and in a cyclic group of even
order `n` the product of all elements is `a ^ (n (n - 1) / 2)`, the involution, whose odd
powers are not `1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.HallPaigeNecessity


/-- A *complete mapping* of a group `G` is a bijection `φ : G → G` such that
`g ↦ g * φ g` is also a bijection (Hall–Paige 1955). -/
def IsCompleteMapping {G : Type*} [Group G] (φ : G → G) : Prop :=
  Function.Bijective φ ∧ Function.Bijective (fun g => g * φ g)

/-! ## Ground truth for the definition -/

/-- `C₃` has the complete mapping `id` (squaring is a bijection). -/
example : IsCompleteMapping (id : Multiplicative (ZMod 3) → Multiplicative (ZMod 3)) := by
  unfold IsCompleteMapping
  decide

/-- `C₂` has no complete mapping (checked over all four self-maps). -/
example : ¬ ∃ φ : Multiplicative (ZMod 2) → Multiplicative (ZMod 2), IsCompleteMapping φ := by
  unfold IsCompleteMapping
  decide

/-- `C₄` has no complete mapping (checked over all `256` self-maps). -/
example : ¬ ∃ φ : Multiplicative (ZMod 4) → Multiplicative (ZMod 4), IsCompleteMapping φ := by
  unfold IsCompleteMapping
  set_option maxRecDepth 8000 in decide

/-- The Klein four-group `C₂ × C₂` (non-cyclic Sylow 2-subgroup) has a complete mapping:
the linear map `(x, y) ↦ (y, x + y)`. -/
example : IsCompleteMapping (fun g : Multiplicative (ZMod 2 × ZMod 2) =>
    Multiplicative.ofAdd ((g.toAdd).2, (g.toAdd).1 + (g.toAdd).2)) := by
  unfold IsCompleteMapping
  decide

/-! ## The obstruction -/

/-- Product of all elements of a finite cyclic group of even order `n`, raised to an odd
power, is not `1` (the product is the unique involution `a ^ (n * (n - 1) / 2)`). -/
theorem prod_univ_pow_ne_one_of_even {A : Type*} [CommGroup A] [Fintype A] [IsCyclic A]
    (heven : Even (Fintype.card A)) {m : ℕ} (hm : Odd m) :
    (∏ a : A, a) ^ m ≠ 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  set n := Fintype.card A
  have hord : orderOf a = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective (fun i : Fin n => a ^ (i : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card, Fintype.card_fin]
    refine ⟨fun i j hij => Fin.ext ?_, rfl⟩
    refine pow_injOn_Iio_orderOf (x := a) ?_ ?_ hij
    · simp [hord]
    · simp [hord]
  have hprod : ∏ x : A, x = a ^ (∑ i ∈ Finset.range n, i) := by
    rw [← Fintype.prod_bijective _ hbij (fun i : Fin n => a ^ (i : ℕ)) (fun x => x)
      (fun _ => rfl), Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) n]
  obtain ⟨t, ht⟩ := heven
  obtain ⟨s, hs⟩ := hm
  have hsum : ∑ i ∈ Finset.range n, i = t * (2 * t - 1) := by
    have h2 := Finset.sum_range_id_mul_two n
    rw [ht] at h2 ⊢
    have : (t + t) * (t + t - 1) = t * (2 * t - 1) * 2 := by
      rcases t with _ | t
      · simp
      · rw [show t + 1 + (t + 1) - 1 = 2 * (t + 1) - 1 by omega]; ring
    omega
  rw [hprod, hsum, ← pow_mul]
  intro h1
  rw [← orderOf_dvd_iff_pow_eq_one, hord, ht, hs] at h1
  have htpos : 0 < t := by
    have : 0 < n := Fintype.card_pos
    omega
  have h2 : 2 ∣ (2 * t - 1) * (2 * s + 1) := by
    rw [show t + t = t * 2 by ring, mul_assoc] at h1
    exact (Nat.mul_dvd_mul_iff_left htpos).mp h1
  have hodd : Odd ((2 * t - 1) * (2 * s + 1)) :=
    Nat.odd_mul.mpr ⟨⟨t - 1, by omega⟩, ⟨s, rfl⟩⟩
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

/-- If `φ` is a complete mapping of a finite group `G` and `f : G →* A` is a homomorphism into
a commutative group, then the product of `f g` over all `g` is `1`. -/
theorem prod_map_eq_one_of_isCompleteMapping {G A : Type*} [Group G] [Fintype G] [CommGroup A]
    (f : G →* A) {φ : G → G} (hφ : IsCompleteMapping φ) : ∏ g, f g = 1 := by
  have h1 : ∏ g, f g = ∏ g, f (g * φ g) :=
    (Fintype.prod_bijective (fun g => g * φ g) hφ.2 (fun g => f (g * φ g)) (fun g => f g)
      (fun _ => rfl)).symm
  have h2 : ∏ g, f (φ g) = ∏ g, f g :=
    Fintype.prod_bijective φ hφ.1 (fun g => f (φ g)) (fun g => f g) (fun _ => rfl)
  rw [Fintype.prod_congr _ _ (fun g => map_mul f g (φ g)), Finset.prod_mul_distrib, h2] at h1
  exact left_eq_mul.mp h1

/-- For a surjective homomorphism `f : G →* A` of finite groups with `A` commutative, the
product of `f g` over all `g` is the product of all elements of `A`, raised to `|ker f|`. -/
theorem prod_map_eq_prod_pow_card_ker {G A : Type*} [Group G] [Fintype G] [CommGroup A]
    [Fintype A] (f : G →* A) (hf : Function.Surjective f) :
    ∏ g, f g = (∏ a : A, a) ^ Nat.card f.ker := by
  classical
  have hfib : ∀ a : A, (Finset.univ.filter (fun g => f g = a)).card = Nat.card f.ker := by
    intro a
    rw [MonoidHom.card_fiber_eq_of_mem_range f (hf a) (hf 1), Nat.card_eq_fintype_card,
      ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => f.mem_ker.symm)
  rw [← Finset.prod_fiberwise Finset.univ f (fun g => f g), ← Finset.prod_pow]
  refine Fintype.prod_congr _ _ (fun a => ?_)
  rw [Finset.prod_congr rfl (fun g hg => (Finset.mem_filter.mp hg).2), Finset.prod_const, hfib]

/-- Abstract form of the Hall–Paige obstruction: if a finite group `G` surjects onto a cyclic
group `A` of even order with kernel of odd order, then `G` has no complete mapping. -/
theorem not_isCompleteMapping_of_surjective {G A : Type*} [Group G] [Finite G] [Group A]
    [Finite A] [IsCyclic A] (f : G →* A) (hf : Function.Surjective f)
    (hA : Even (Nat.card A)) (hker : Odd (Nat.card f.ker)) (φ : G → G) :
    ¬ IsCompleteMapping φ := by
  classical
  intro hφ
  letI : CommGroup A := IsCyclic.commGroup
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype A := Fintype.ofFinite A
  have h1 : ∏ g, f g = 1 := prod_map_eq_one_of_isCompleteMapping f hφ
  rw [prod_map_eq_prod_pow_card_ker f hf] at h1
  exact prod_univ_pow_ne_one_of_even (by rwa [← Nat.card_eq_fintype_card]) hker h1

/-- **Hall–Paige necessity (1955).** A finite group whose Sylow `2`-subgroup is cyclic and
nontrivial has no complete mapping, i.e. there is no bijection `φ : G → G` such that
`g ↦ g * φ g` is also a bijection.  Source: M. Hall and L. J. Paige, *Complete mappings of
finite groups*, Pacific J. Math. 5 (1955); quoted in MathOverflow answer 322348. -/
theorem not_exists_isCompleteMapping {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcyc : IsCyclic P) (hnt : Nontrivial P) : ¬ ∃ φ : G → G, IsCompleteMapping φ := by
  rintro ⟨φ, hφ⟩
  have hevenP : Even (Nat.card P) := by
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    have hlt : 1 < Nat.card P := Finite.one_lt_card_iff_nontrivial.mpr hnt
    rcases k with _ | k
    · rw [hk, pow_zero] at hlt
      exact absurd hlt (lt_irrefl 1)
    · rw [hk, pow_succ]
      exact even_two.mul_left _
  have h2G : 2 ∣ Nat.card G :=
    (even_iff_two_dvd.mp hevenP).trans (Subgroup.card_subgroup_dvd_card _)
  have hp : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2G
  have hN := hcyc.normalizer_le_centralizer hp
  have hsurj : Function.Surjective (MonoidHom.transferSylow P hN) := by
    intro y
    have hb : Function.Bijective ((MonoidHom.transferSylow P hN).domRestrict (P : Subgroup G)) :=
      (MonoidHom.transferSylow_domRestrict_eq_pow P hN).symm ▸
        (P.2.powEquiv' P.not_dvd_index).bijective
    obtain ⟨x, hx⟩ := hb.2 y
    exact ⟨x, hx⟩
  have hker : Odd (Nat.card (MonoidHom.transferSylow P hN).ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hN))
  exact not_isCompleteMapping_of_surjective _ hsurj hevenP hker φ hφ

/-- Special case: a finite cyclic group of even order has no complete mapping. -/
theorem not_exists_isCompleteMapping_of_isCyclic {G : Type*} [Group G] [Finite G]
    [IsCyclic G] (h : Even (Nat.card G)) : ¬ ∃ φ : G → G, IsCompleteMapping φ := by
  rintro ⟨φ, hφ⟩
  have hker : Odd (Nat.card (MonoidHom.id G).ker) := by
    rw [MonoidHom.ker_id, Subgroup.card_bot]
    exact odd_one
  exact not_isCompleteMapping_of_surjective (MonoidHom.id G) Function.surjective_id h hker φ hφ

/-- Converse direction in the trivial case: a finite group of odd order has the complete
mapping `φ = id`, since `g ↦ g * g = g ^ 2` is a bijection. -/
theorem isCompleteMapping_id_of_odd_card {G : Type*} [Group G] [Finite G]
    (h : Odd (Nat.card G)) : IsCompleteMapping (id : G → G) := by
  refine ⟨Function.bijective_id, ?_⟩
  have hcop : (Nat.card G).Coprime 2 := Nat.coprime_two_right.mpr h
  have hsq : (fun g : G => g * id g) = powCoprime hcop := by
    funext g
    rw [powCoprime_apply, id, pow_two]
  rw [hsq]
  exact (powCoprime hcop).bijective

/-- Non-vacuity of `not_exists_isCompleteMapping`: in `C₂` the whole group is a cyclic,
nontrivial Sylow `2`-subgroup, so the theorem applies. -/
example : ¬ ∃ φ : Multiplicative (ZMod 2) → Multiplicative (ZMod 2), IsCompleteMapping φ := by
  have hcard : Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2))) =
      2 ^ (Nat.card (Multiplicative (ZMod 2))).factorization 2 := by
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [Subgroup.card_top, h2, Nat.Prime.factorization_self Nat.prime_two, pow_one]
  let P : Sylow 2 (Multiplicative (ZMod 2)) := Sylow.ofCard ⊤ hcard
  have hnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    show 1 < Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2)))
    rw [Subgroup.card_top, Nat.card_eq_fintype_card]
    exact Nat.one_lt_two
  have hcyc : IsCyclic P := by
    show IsCyclic (⊤ : Subgroup (Multiplicative (ZMod 2)))
    infer_instance
  exact not_exists_isCompleteMapping P hcyc hnt

end Candidates.HallPaigeNecessity
