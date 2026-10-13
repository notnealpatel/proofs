import GroupTPP.MonomialInterface
import GroupTPP.MonomialClassification
import GroupTPP.MonomialTPPBridge

set_option autoImplicit false

namespace GroupTPP.MonomialRealization

open GroupTPP.TPP Finset

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}
variable {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
variable {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}

/-- A positive-dimensional monomial realization has matrix multiplication
volume at most the triple product capacity of its finite group. -/
theorem p1_c9 [Fintype G] (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    n * m * p ≤ tppCapacity G := by
  obtain ⟨s, t, u, ha, hb, hc⟩ := group_normal_form hn hm hp h
  obtain ⟨hia, hib, hic⟩ := index_maps_injective hn hm hp h
  let i₀ : Fin n := ⟨0, hn⟩
  let j₀ : Fin m := ⟨0, hm⟩
  let k₀ : Fin p := ⟨0, hp⟩
  have hs : Function.Injective s := by
    intro i i' heq
    have heqa : a i j₀ = a i' j₀ := by rw [ha, ha, heq]
    exact congrArg Prod.fst (hia (a₁ := (i, j₀)) (a₂ := (i', j₀)) heqa)
  have ht : Function.Injective t := by
    intro j j' heq
    have heqb : b j k₀ = b j' k₀ := by rw [hb, hb, heq]
    exact congrArg Prod.fst (hib (a₁ := (j, k₀)) (a₂ := (j', k₀)) heqb)
  have hu : Function.Injective u := by
    intro k k' heq
    have heqc : c k i₀ = c k' i₀ := by rw [hc, hc, heq]
    exact congrArg Prod.fst (hic (a₁ := (k, i₀)) (a₂ := (k', i₀)) heqc)
  have hs_card : (image s univ).card = n := by
    rw [card_image_of_injective univ hs, card_univ, Fintype.card_fin]
  have ht_card : (image t univ).card = m := by
    rw [card_image_of_injective univ ht, card_univ, Fintype.card_fin]
  have hu_card : (image u univ).card = p := by
    rw [card_image_of_injective univ hu, card_univ, Fintype.card_fin]
  have hTPP := tripleProductProperty_of_factorization h s t u ha hb hc
  simpa only [hs_card, ht_card, hu_card] using le_tppCapacity hTPP

example :
    let a : Fin 1 → Fin 1 → Multiplicative (ZMod 2) := fun _ _ => 1
    let α : Fin 1 → Fin 1 → ℚ := fun _ _ => 1
    (0 < (1 : ℕ)) ∧ (0 < (1 : ℕ)) ∧ (0 < (1 : ℕ)) ∧
      IsMonomialRealization a a a α α α := by
  dsimp only
  refine ⟨by decide, by decide, by decide, ?_⟩
  constructor
  · intro i j
    exact one_ne_zero
  · intro j k
    exact one_ne_zero
  · intro k i
    exact one_ne_zero
  · intro i i' j j' k k'
    have hi : i = i' := Subsingleton.elim i i'
    have hj : j = j' := Subsingleton.elim j j'
    have hk : k = k' := Subsingleton.elim k k'
    simp [hi, hj, hk]

end GroupTPP.MonomialRealization
