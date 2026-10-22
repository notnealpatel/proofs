import Sorry.GroupTPP.MonomialRealization

set_option autoImplicit false

namespace GroupTPP.MonomialRealization

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}
variable {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
variable {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}

omit [DecidableEq G] in
private lemma cyclic_eq_one (x y z : G) :
    y * z * x = 1 ↔ x * y * z = 1 := by
  have cycle (u v w : G) (h : u * v * w = 1) : v * w * u = 1 := by
    calc
      v * w * u = u⁻¹ * (u * v * w) * u := by simp [mul_assoc]
      _ = 1 := by rw [h]; simp
  exact ⟨fun h => cycle z x y (cycle y z x h), cycle x y z⟩

/-- Cyclically rotating the three index maps and scalar maps preserves a
monomial realization, even when an index dimension is zero. -/
theorem IsMonomialRealization.rotate (h : IsMonomialRealization a b c α β γ) :
    IsMonomialRealization b c a β γ α where
  alpha_ne_zero := h.beta_ne_zero
  beta_ne_zero := h.gamma_ne_zero
  gamma_ne_zero := h.alpha_ne_zero
  coeff_identity := by
    intro j j' k k' i i'
    have key := h.coeff_identity i' i j' j k k'
    simp only [cyclic_eq_one (a i' j') (b j k) (c k' i)]
    simpa only [mul_comm, mul_left_comm, mul_assoc,
      eq_comm, and_comm, and_left_comm, and_assoc] using key

private lemma first_index_map_injective (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    Function.Injective (fun q : Fin n × Fin m => a q.1 q.2) := by
  intro q q' heq
  change a q.1 q.2 = a q'.1 q'.2 at heq
  let k : Fin p := ⟨0, hp⟩
  have hcol : a q.1 q.2 * b q'.2 k * c k q'.1 = 1 := by
    rw [heq]
    exact diagonal_group_prod_eq_one h q'.1 q'.2 k
  obtain ⟨hj, _, hi⟩ := no_cancellation h hcol
  exact Prod.ext hi hj

/-- In positive dimensions each index-pair map of a monomial realization
is injective. -/
theorem index_maps_injective (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    Function.Injective (fun q : Fin n × Fin m => a q.1 q.2) ∧
    Function.Injective (fun q : Fin m × Fin p => b q.1 q.2) ∧
    Function.Injective (fun q : Fin p × Fin n => c q.1 q.2) := by
  exact ⟨first_index_map_injective hp h,
    first_index_map_injective hn h.rotate,
    first_index_map_injective hm h.rotate.rotate⟩

/-- A finite group supporting a positive-dimensional monomial realization
has cardinality at least each of the three index-pair cardinalities. -/
theorem index_card_bounds [Fintype G] (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    n * m ≤ Fintype.card G ∧ m * p ≤ Fintype.card G ∧ p * n ≤ Fintype.card G := by
  obtain ⟨ha, hb, hc⟩ := index_maps_injective hn hm hp h
  refine ⟨?_, ?_, ?_⟩
  · simpa using Fintype.card_le_of_injective _ ha
  · simpa using Fintype.card_le_of_injective _ hb
  · simpa using Fintype.card_le_of_injective _ hc

end GroupTPP.MonomialRealization
