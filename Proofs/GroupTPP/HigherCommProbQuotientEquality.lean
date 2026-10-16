import GroupTPP.HigherCommProb

set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Equality under a finite normal quotient, for tuples of length at least two,
means that the quotient map reflects commutation of every pair. -/
theorem higherCommProb_quotient_eq_iff (G : Type*) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (r : ℕ) (hr : 2 ≤ r) :
    higherCommProb (G ⧸ N) r = higherCommProb G r ↔
      ∀ a b : G, Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b) →
        Commute a b := by
  classical
  let π := QuotientGroup.mk' N
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  let σ := Function.surjInv hsurj
  have hσ : ∀ y, π (σ y) = y := Function.surjInv_eq hsurj
  have hmem : ∀ a : G, (σ (π a))⁻¹ * a ∈ N := by
    intro a
    have hk : (σ (π a))⁻¹ * a ∈ MonoidHom.ker π := by
      change π ((σ (π a))⁻¹ * a) = 1
      rw [map_mul, map_inv, hσ, inv_mul_cancel]
    simpa only [π, QuotientGroup.ker_mk'] using hk
  let φ : commTuples G r → commTuples (G ⧸ N) r × (Fin r → N) := fun g =>
    (⟨fun i => π (g.1 i), fun i j => (g.2 i j).map π⟩,
      fun i => ⟨(σ (π (g.1 i)))⁻¹ * g.1 i, hmem (g.1 i)⟩)
  let decode : commTuples (G ⧸ N) r × (Fin r → N) → Fin r → G :=
    fun p i => σ (p.1.1 i) * p.2 i
  have hdecode : ∀ g, decode (φ g) = g.1 := by
    intro g
    funext i
    exact mul_inv_cancel_left _ _
  have hinj : Function.Injective φ := by
    intro g h heq
    apply Subtype.ext
    calc g.1 = decode (φ g) := (hdecode g).symm
         _ = decode (φ h) := congrArg decode heq
         _ = h.1 := hdecode h
  have hπdecode : ∀ p i, π (decode p i) = p.1.1 i := by
    intro p i
    change π (σ (p.1.1 i) * (p.2 i : G)) = _
    rw [map_mul, hσ]
    have hn : π (p.2 i : G) = 1 := by
      exact (QuotientGroup.eq_one_iff _).2 (p.2 i).2
    rw [hn, mul_one]
  have hencode : ∀ (p) (hc : ∀ i j, Commute (decode p i) (decode p j)),
      φ ⟨decode p, hc⟩ = p := by
    intro p hc
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact hπdecode p i
    · funext i
      apply Subtype.ext
      change (σ (π (decode p i)))⁻¹ * decode p i = (p.2 i : G)
      rw [hπdecode]
      exact inv_mul_cancel_left _ _
  have hcard : higherCommProb (G ⧸ N) r = higherCommProb G r ↔
      Nat.card (commTuples G r) =
        Nat.card (commTuples (G ⧸ N) r × (Fin r → N)) := by
    rw [Nat.card_prod, card_funFin]
    have hG : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hQpos : 0 < (Nat.card (G ⧸ N) : ℚ) := by exact_mod_cast Finite.card_pos
    have hNpos : 0 < (Nat.card N : ℚ) := by exact_mod_cast Finite.card_pos
    have hGpos : 0 < (Nat.card G : ℚ) := by exact_mod_cast Finite.card_pos
    rw [higherCommProb_def, higherCommProb_def, div_eq_div_iff (by positivity) (by positivity)]
    have hGcast : (Nat.card G : ℚ) = Nat.card (G ⧸ N) * Nat.card N := by exact_mod_cast hG
    rw [hGcast, mul_pow]
    have hq : (Nat.card (G ⧸ N) : ℚ) ^ r ≠ 0 := by positivity
    constructor
    · intro h
      have hc : (Nat.card (commTuples G r) : ℚ) =
          Nat.card (commTuples (G ⧸ N) r) * (Nat.card N : ℚ) ^ r := by
        apply (mul_right_cancel₀ hq)
        calc _ = (Nat.card (commTuples (G ⧸ N) r) : ℚ) *
            ((Nat.card (G ⧸ N) : ℚ) ^ r * (Nat.card N : ℚ) ^ r) := h.symm
             _ = _ := by ring
      exact_mod_cast hc
    · intro h
      have hc : (Nat.card (commTuples G r) : ℚ) =
          Nat.card (commTuples (G ⧸ N) r) * (Nat.card N : ℚ) ^ r := by exact_mod_cast h
      rw [hc]
      ring
  have hbij : (Nat.card (commTuples G r) =
      Nat.card (commTuples (G ⧸ N) r × (Fin r → N))) ↔ Function.Bijective φ := by
    constructor
    · intro hc
      exact (Nat.bijective_iff_injective_and_card φ).2 ⟨hinj, hc⟩
    · intro hb
      exact ((Nat.bijective_iff_injective_and_card φ).1 hb).2
  rw [hcard, hbij]
  constructor
  · intro h a b hab
    let i₀ : Fin r := ⟨0, by omega⟩
    let i₁ : Fin r := ⟨1, by omega⟩
    let f : Fin r → G := fun i => if i = i₀ then a else if i = i₁ then b else 1
    have hf : ∀ i j, Commute (π (f i)) (π (f j)) := by
      intro i j
      dsimp [f]
      split_ifs <;> first
        | exact hab
        | exact hab.symm
        | exact Commute.refl _
        | simp
    let p : commTuples (G ⧸ N) r × (Fin r → N) :=
      (⟨fun i => π (f i), hf⟩, fun i => ⟨(σ (π (f i)))⁻¹ * f i, hmem (f i)⟩)
    obtain ⟨g, hg⟩ := h.2 p
    have hd : decode p = f := by
      funext i
      exact mul_inv_cancel_left _ _
    have hgf : g.1 = f := by
      calc g.1 = decode (φ g) := (hdecode g).symm
           _ = decode p := congrArg decode hg
           _ = f := hd
    have hc := g.2 i₀ i₁
    rw [hgf] at hc
    simpa [f, i₀, i₁] using hc
  · intro hreflect
    refine ⟨hinj, ?_⟩
    intro p
    have hc : ∀ i j, Commute (decode p i) (decode p j) := by
      intro i j
      apply hreflect
      change Commute (π (decode p i)) (π (decode p j))
      rw [hπdecode, hπdecode]
      exact p.1.2 i j
    exact ⟨⟨decode p, hc⟩, hencode p hc⟩

example : higherCommProb (Multiplicative (ZMod 2) ⧸
    (⊥ : Subgroup (Multiplicative (ZMod 2)))) 2 =
    higherCommProb (Multiplicative (ZMod 2)) 2 := by
  apply (higherCommProb_quotient_eq_iff _ _ 2 (by decide)).2
  intro a b _
  exact Commute.all a b

example : Nonempty (Fin 2) := ⟨0⟩

end
