import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic

set_option autoImplicit false

namespace GroupCount

private theorem fourth_power {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (hno : ∀ g : G, orderOf g ≠ 8) (g : G) : g ^ 4 = 1 := by
  have hd : orderOf g ∣ 8 := hcard ▸ orderOf_dvd_natCard g
  have hle : orderOf g ≤ 8 := Nat.le_of_dvd (by decide) hd
  have hn := hno g
  have hd4 : orderOf g ∣ 4 := by
    interval_cases h : orderOf g <;> norm_num [h] at hd <;>
      norm_num [h] at hn <;> norm_num [h]
  exact orderOf_dvd_iff_pow_eq_one.mp hd4

private theorem mem_four_powers {G : Type*} [Group G] [Finite G]
    (a x : G) (ha : orderOf a = 4) (hx : x ∈ Subgroup.zpowers a) :
    x = 1 ∨ x = a ∨ x = a ^ 2 ∨ x = a ^ 3 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha] at hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk4 : k < 4 := Finset.mem_range.mp hk
  interval_cases k <;> simp

/-- A group of order eight with an order-four element and no order-eight element
has an outside generator with the normalized commuting or inversion relations. -/
theorem normalized_order_eight_generators {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (a : G) (ha : orderOf a = 4)
    (hno : ∀ g : G, orderOf g ≠ 8) :
    ∃ b : G, b ∉ Subgroup.zpowers a ∧
      ((Commute a b ∧ b ^ 2 = 1) ∨
        (b * a * b⁻¹ = a⁻¹ ∧ (b ^ 2 = 1 ∨ b ^ 2 = a ^ 2))) := by
  let H := Subgroup.zpowers a
  have hH : Nat.card H = 4 := (Nat.card_zpowers a).trans ha
  have hi : H.index = 2 := by
    have he := H.index_mul_card
    rw [hH, hcard] at he
    omega
  have hnormal : H.Normal := H.normal_of_index_eq_two hi
  obtain ⟨c, hc, _⟩ := H.index_eq_two_iff_exists_notMem_and.mp hi
  have haH : a ∈ H := Subgroup.mem_zpowers a
  have ha4 : a ^ 4 = 1 := ha ▸ pow_orderOf_eq_one a
  have ha2 : a ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [ha] at hd
    norm_num at hd
  have hc4 : c ^ 4 = 1 := fourth_power hcard hno c
  have hs : c ^ 2 = 1 ∨ c ^ 2 = a ^ 2 := by
    have hm : c ^ 2 ∈ H := H.sq_mem_of_index_two hi c
    rcases mem_four_powers a (c ^ 2) ha hm with h | h | h | h
    · exact Or.inl h
    · exfalso
      apply ha2
      calc a ^ 2 = (c ^ 2) ^ 2 := by rw [h]
           _ = 1 := by simpa only [← pow_mul] using hc4
    · exact Or.inr h
    · exfalso
      have he : a ^ 6 = 1 := by
        calc a ^ 6 = (a ^ 3) ^ 2 := by rw [← pow_mul]
             _ = (c ^ 2) ^ 2 := by rw [h]
             _ = 1 := by simpa only [← pow_mul] using hc4
      have hd := orderOf_dvd_of_pow_eq_one he
      rw [ha] at hd
      norm_num at hd
  have hconj : c * a * c⁻¹ = a ∨ c * a * c⁻¹ = a⁻¹ := by
    have hm : c * a * c⁻¹ ∈ H := hnormal.conj_mem a haH c
    have hn : (c * a * c⁻¹) ^ 2 ≠ 1 := by
      intro he
      apply ha2
      have he' : c * a ^ 2 * c⁻¹ = 1 := by
        calc c * a ^ 2 * c⁻¹ = (c * a * c⁻¹) ^ 2 := conj_pow.symm
             _ = 1 := he
      calc a ^ 2 = c⁻¹ * (c * a ^ 2 * c⁻¹) * c := by group
           _ = 1 := by rw [he']; group
    rcases mem_four_powers a (c * a * c⁻¹) ha hm with h | h | h | h
    · exact False.elim (hn (by rw [h]; simp))
    · exact Or.inl h
    · exact False.elim (hn (by rw [h, ← pow_mul]; exact ha4))
    · right
      have hi3 : a ^ 3 = a⁻¹ := by
        have he : a ^ 3 * a = 1 := by simpa only [← pow_succ] using ha4
        exact mul_eq_one_iff_eq_inv.mp he
      exact h.trans hi3
  rcases hconj with hcomm | hinv
  · have hac : Commute a c := by
      change a * c = c * a
      calc a * c = (c * a * c⁻¹) * c := by rw [hcomm]
           _ = c * a := by group
    rcases hs with hs1 | hs2
    · exact ⟨c, hc, Or.inl ⟨hac, hs1⟩⟩
    · refine ⟨a * c, ?_, Or.inl ⟨?_, ?_⟩⟩
      · intro hm
        apply hc
        have he : a⁻¹ * (a * c) ∈ H := H.mul_mem (H.inv_mem haH) hm
        simpa using he
      · exact (Commute.refl a).mul_right hac
      · calc (a * c) ^ 2 = a ^ 2 * c ^ 2 := hac.mul_pow 2
             _ = a ^ 4 := by rw [hs2, ← pow_add]
             _ = 1 := ha4
  · exact ⟨c, hc, Or.inr ⟨hinv, hs⟩⟩

example : ∃ a : Multiplicative (ZMod 4 × ZMod 2),
    Nat.card (Multiplicative (ZMod 4 × ZMod 2)) = 8 ∧
    orderOf a = 4 ∧ (∀ g : Multiplicative (ZMod 4 × ZMod 2), orderOf g ≠ 8) := by
  refine ⟨Multiplicative.ofAdd (1, 0), ?_, ?_, ?_⟩
  · simp [Nat.card_eq_fintype_card, Fintype.card_prod]
  · apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
    constructor
    · decide
    · intro m hm hp
      interval_cases m <;> norm_num at hp ⊢ <;> decide
  · intro g he
    have hfour : ∀ g : Multiplicative (ZMod 4 × ZMod 2), g ^ 4 = 1 := by decide
    have hd := orderOf_dvd_of_pow_eq_one (hfour g)
    rw [he] at hd
    norm_num at hd

end GroupCount
