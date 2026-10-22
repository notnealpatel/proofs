import Sorry.GroupTPP.MonomialRealization
import Sorry.GroupTPP.MonomialInterface
import Sorry.GroupTPP.MonomialSemanticConverse
import Sorry.GroupTPP.MonomialClassification
import Sorry.GroupTPP.MonomialTPPBridge
import Sorry.GroupTPP.MonomialTPPConstruction
import Sorry.GroupTPP.MonomialCapacity

set_option autoImplicit false

/-!
# Monomial realization sweep: dependency wrappers

The semantic converse is supplied by `MonomialSemanticConverse`; cyclic
rotation, injectivity, and index-cardinality bounds by `MonomialInterface`;
scalar minors, group normal form, and scalar gauge by `MonomialClassification`;
and the factorization-to-TPP bridge by `MonomialTPPBridge`.
`MonomialTPPConstruction` and `MonomialCapacity` supply `p1_c8` and `p1_c9`
directly in this namespace; the latter gives the volume-capacity bound.
-/

namespace GroupTPP.MonomialRealization

open GroupTPP.TPP Finset

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}
variable {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
variable {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}

/-- The coefficient identity implies the semantic trilinear identity. -/
theorem p1_c1 (h : IsMonomialRealization a b c α β γ) :
    IsSemanticMonomialRealization a b c α β γ := by
  exact h.toSemanticMonomialRealization

/-- Cyclic rotation preserves a monomial realization. -/
theorem p1_c2 (h : IsMonomialRealization a b c α β γ) :
    IsMonomialRealization b c a β γ α := by
  exact h.rotate

/-- In positive dimensions, all three index-pair maps are injective. -/
theorem p1_c3 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    Function.Injective (fun q : Fin n × Fin m => a q.1 q.2) ∧
    Function.Injective (fun q : Fin m × Fin p => b q.1 q.2) ∧
    Function.Injective (fun q : Fin p × Fin n => c q.1 q.2) := by
  exact index_maps_injective hn hm hp h

/-- A finite group supporting a positive-dimensional realization has cardinality
at least each index-pair cardinality. -/
theorem p1_c4 [Fintype G] (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    n * m ≤ Fintype.card G ∧ m * p ≤ Fintype.card G ∧ p * n ≤ Fintype.card G := by
  exact index_card_bounds hn hm hp h

/-- The scalar matrices of a positive-dimensional realization have balanced
multiplicative two-by-two minors. -/
theorem p1_c5 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    (∀ i i' j j', α i j * α i' j' = α i j' * α i' j) ∧
    (∀ j j' k k', β j k * β j' k' = β j k' * β j' k) ∧
    (∀ k k' i i', γ k i * γ k' i' = γ k i' * γ k' i) := by
  exact scalar_minors hn hm hp h

/-- The group labels of a positive-dimensional realization factor through
three one-variable maps in quotient normal form. -/
theorem p1_c6 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    ∃ (s : Fin n → G) (t : Fin m → G) (u : Fin p → G),
      (∀ i j, a i j = s i * (t j)⁻¹) ∧
      (∀ j k, b j k = t j * (u k)⁻¹) ∧
      (∀ k i, c k i = u k * (s i)⁻¹) := by
  exact group_normal_form hn hm hp h

/-- A supplied quotient factorization gives the triple product property
on the three images. -/
theorem p1_c7 [Fintype G] (h : IsMonomialRealization a b c α β γ)
    (s : Fin n → G) (t : Fin m → G) (u : Fin p → G)
    (ha : ∀ i j, a i j = s i * (t j)⁻¹)
    (hb : ∀ j k, b j k = t j * (u k)⁻¹)
    (hc : ∀ k i, c k i = u k * (s i)⁻¹) :
    TripleProductProperty (Finset.image s Finset.univ)
      (Finset.image t Finset.univ) (Finset.image u Finset.univ) := by
  exact tripleProductProperty_of_factorization h s t u ha hb hc

/-- Two positive-dimensional realizations with the same group labels differ
by a scalar gauge on the three index sets. -/
theorem p1_c10 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    {α' : Fin n → Fin m → F} {β' : Fin m → Fin p → F} {γ' : Fin p → Fin n → F}
    (h : IsMonomialRealization a b c α β γ)
    (h' : IsMonomialRealization a b c α' β' γ') :
    ∃ (u : Fin n → F) (v : Fin m → F) (w : Fin p → F),
      (∀ i j, α' i j = α i j * u i * v j) ∧
      (∀ j k, β' j k = β j k * (v j)⁻¹ * w k) ∧
      (∀ k i, γ' k i = γ k i * (w k)⁻¹ * (u i)⁻¹) := by
  exact scalar_gauge hn hm hp h h'

end GroupTPP.MonomialRealization
