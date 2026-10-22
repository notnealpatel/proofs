import Sorry.GroupTPP.MonomialRealization

set_option autoImplicit false

namespace GroupTPP.MonomialRealization

open Finset

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}
variable {a : Fin n → Fin m → G} {b : Fin m → Fin p → G}
variable {c : Fin p → Fin n → G}
variable {α : Fin n → Fin m → F} {β : Fin m → Fin p → F}
variable {γ : Fin p → Fin n → F}

/-- A monomial realization with the supplied one-variable factorization gives
an honest left-quotient triple product property on the three images. No
positivity of the index dimensions or existence of a factorization is assumed. -/
theorem tripleProductProperty_of_factorization [Fintype G]
    (h : IsMonomialRealization a b c α β γ)
    (s : Fin n → G) (t : Fin m → G) (u : Fin p → G)
    (ha : ∀ i j, a i j = s i * (t j)⁻¹)
    (hb : ∀ j k, b j k = t j * (u k)⁻¹)
    (hc : ∀ k i, c k i = u k * (s i)⁻¹) :
    TPP.TripleProductProperty (image s univ) (image t univ) (image u univ) := by
  intro S hS S' hS' T hT T' hT' U hU U' hU' hQ
  obtain ⟨i, _, rfl⟩ := mem_image.mp hS
  obtain ⟨i', _, rfl⟩ := mem_image.mp hS'
  obtain ⟨j, _, rfl⟩ := mem_image.mp hT
  obtain ⟨j', _, rfl⟩ := mem_image.mp hT'
  obtain ⟨k, _, rfl⟩ := mem_image.mp hU
  obtain ⟨k', _, rfl⟩ := mem_image.mp hU'
  have hconj := congrArg (fun x : G => s i' * x * (s i')⁻¹) hQ
  have hcyclic :
      s i * (t j')⁻¹ * t j * (u k')⁻¹ * u k * (s i')⁻¹ = 1 := by
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using hconj
  have hcollision : a i j' * b j k' * c k i' = 1 := by
    rw [ha, hb, hc]
    simpa only [mul_assoc] using hcyclic
  obtain ⟨hj, hk, hi⟩ := no_cancellation
    (i := i) (i' := i') (j := j') (j' := j) (k := k') (k' := k) h hcollision
  exact ⟨congrArg s hi, congrArg t hj.symm, congrArg u hk.symm⟩

-- A nonempty concrete model jointly satisfies every premise of the bridge.
example :
    let s : Fin 1 → Multiplicative (ZMod 2) := fun _ => 1
    let a : Fin 1 → Fin 1 → Multiplicative (ZMod 2) := fun _ _ => 1
    let α : Fin 1 → Fin 1 → ℚ := fun _ _ => 1
    IsMonomialRealization a a a α α α ∧
      (∀ i j, a i j = s i * (s j)⁻¹) ∧
      (∀ j k, a j k = s j * (s k)⁻¹) ∧
      (∀ k i, a k i = s k * (s i)⁻¹) := by
  dsimp
  constructor
  · constructor
    · intro i j; norm_num
    · intro j k; norm_num
    · intro k i; norm_num
    · intro i i' j j' k k'
      have hi : i = i' := Subsingleton.elim i i'
      have hj : j = j' := Subsingleton.elim j j'
      have hk : k = k' := Subsingleton.elim k k'
      simp [hi, hj, hk]
  · simp

end GroupTPP.MonomialRealization
