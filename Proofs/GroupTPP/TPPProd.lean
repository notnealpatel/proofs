import Mathlib
import GroupTPP.TPP

/-!
# TPP is closed under direct products

The triple product property is closed under finite group direct products:
a TPP triple in `G` and a TPP triple in `H` give a TPP triple of product
finsets in `G × H`, with cardinalities multiplying. This lifts to the
iterated power `Fin ℓ → G` via `Fintype.piFinset`.

## Main results

* `GroupTPP.TPP.TripleProductProperty.prod` — binary product closure.
* `GroupTPP.TPP.TripleProductProperty.piFinset` — iterated closure on `Fin ℓ → G`.
* `GroupTPP.TPP.card_piFinset_const_eq` — `(piFinset (fun _ => S)).card = S.card ^ ℓ`.
* `GroupTPP.TPP.le_tppCapacity_pi` — capacity corollary: TPP in `G` gives
  `(|S|·|T|·|U|)^ℓ ≤ β(Fin ℓ → G)`.
-/

namespace GroupTPP.TPP

/-! ### Binary product closure -/

/-- **Product closure of the TPP.** If `(S, T, U)` has the TPP in `G` and
`(S', T', U')` has the TPP in `H`, then `(S ×ˢ S', T ×ˢ T', U ×ˢ U')` has
the TPP in `G × H`. The proof projects the TPP hypothesis to each
coordinate. -/
theorem TripleProductProperty.prod
    {G : Type*} {H : Type*}
    [Group G] [DecidableEq G] [Group H] [DecidableEq H]
    {S T U : Finset G} {S' T' U' : Finset H}
    (hG : TripleProductProperty S T U)
    (hH : TripleProductProperty S' T' U') :
    TripleProductProperty (S ×ˢ S') (T ×ˢ T') (U ×ˢ U') := by
  intro s hs s' hs' t ht t' ht' u hu u' hu'
  rw [Finset.mem_product] at hs hs' ht ht' hu hu'
  intro heq
  have heq1 : s'.1⁻¹ * s.1 * t'.1⁻¹ * t.1 * u'.1⁻¹ * u.1 = 1 := by
    have := congr_arg Prod.fst heq
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.fst_one] at this
    exact this
  have heq2 : s'.2⁻¹ * s.2 * t'.2⁻¹ * t.2 * u'.2⁻¹ * u.2 = 1 := by
    have := congr_arg Prod.snd heq
    simp only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one] at this
    exact this
  obtain ⟨hs1, ht1, hu1⟩ := hG s.1 hs.1 s'.1 hs'.1 t.1 ht.1 t'.1 ht'.1
    u.1 hu.1 u'.1 hu'.1 heq1
  obtain ⟨hs2, ht2, hu2⟩ := hH s.2 hs.2 s'.2 hs'.2 t.2 ht.2 t'.2 ht'.2
    u.2 hu.2 u'.2 hu'.2 heq2
  exact ⟨Prod.ext hs1 hs2, Prod.ext ht1 ht2, Prod.ext hu1 hu2⟩

open scoped Pointwise in
/-- **Product closure of the right-quotient TPP.** If `(S, T, U)` has the
right-quotient TPP in `G` and `(S', T', U')` has the right-quotient TPP in `H`,
then `(S ×ˢ S', T ×ˢ T', U ×ˢ U')` has the right-quotient TPP in `G × H`. Via
the inversion bridge and the left-quotient `TripleProductProperty.prod`. -/
theorem TripleProductPropertyR.prod
    {G : Type*} {H : Type*}
    [Group G] [DecidableEq G] [Fintype G] [Group H] [DecidableEq H] [Fintype H]
    {S T U : Finset G} {S' T' U' : Finset H}
    (hG : TripleProductPropertyR S T U)
    (hH : TripleProductPropertyR S' T' U') :
    TripleProductPropertyR (S ×ˢ S') (T ×ˢ T') (U ×ˢ U') := by
  rw [tripleProductPropertyR_iff_inv] at hG hH ⊢
  convert (hG.prod hH) using 1 <;>
    ext ⟨a, b⟩ <;> simp [Finset.mem_inv', Finset.mem_product]

/-- Cardinality of a product finset: `(S ×ˢ S').card = S.card * S'.card`.
(Re-export of `Finset.card_product` for use in capacity arguments.) -/
theorem card_prod_eq {α β : Type*} (S : Finset α) (S' : Finset β) :
    (S ×ˢ S').card = S.card * S'.card :=
  Finset.card_product S S'

/-! ### Iterated product closure on `Fin ℓ → G` -/

/-- **Iterated product closure.** If `(S, T, U)` has the TPP in `G`, then
the constant-fibre `piFinset` triple has the TPP in `Fin ℓ → G`. -/
theorem TripleProductProperty.piFinset
    {G : Type*} [Group G] [DecidableEq G]
    {S T U : Finset G}
    (h : TripleProductProperty S T U) (ℓ : ℕ) :
    TripleProductProperty
      (Fintype.piFinset fun _ : Fin ℓ => S)
      (Fintype.piFinset fun _ : Fin ℓ => T)
      (Fintype.piFinset fun _ : Fin ℓ => U) := by
  intro s hs s' hs' t ht t' ht' u hu u' hu'
  rw [Fintype.mem_piFinset] at hs hs' ht ht' hu hu'
  intro heq
  have coord : ∀ i : Fin ℓ, (s' i)⁻¹ * s i * (t' i)⁻¹ * t i * (u' i)⁻¹ * u i = 1 := by
    intro i
    have := congr_fun heq i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] at this
    exact this
  refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
  · exact (h (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).1
  · exact (h (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).2.1
  · exact (h (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).2.2

/-- Cardinality of a constant `piFinset`:
`(piFinset (fun _ : Fin ℓ => S)).card = S.card ^ ℓ`. -/
theorem card_piFinset_const_eq
    {G : Type*} (S : Finset G) (ℓ : ℕ) :
    (Fintype.piFinset fun _ : Fin ℓ => S).card = S.card ^ ℓ :=
  Fintype.card_piFinset_const S ℓ

/-! ### Capacity corollary -/

/-- **Capacity corollary.** A TPP triple in `G` gives
`(|S| · |T| · |U|)^ℓ ≤ β(Fin ℓ → G)`. -/
theorem le_tppCapacity_pi
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {S T U : Finset G}
    (h : TripleProductProperty S T U) (ℓ : ℕ) :
    (S.card * T.card * U.card) ^ ℓ
      ≤ tppCapacity (Fin ℓ → G) := by
  have htpp := h.piFinset ℓ
  have hle := le_tppCapacity htpp
  rw [card_piFinset_const_eq, card_piFinset_const_eq, card_piFinset_const_eq] at hle
  rwa [← mul_pow, ← mul_pow] at hle

end GroupTPP.TPP
