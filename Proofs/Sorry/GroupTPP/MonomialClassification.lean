import Sorry.GroupTPP.MonomialRealization

set_option autoImplicit false

namespace GroupTPP.MonomialRealization

private theorem diagonal_normal_form {H : Type*} [Group H]
    {n m p : ℕ} (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (a : Fin n → Fin m → H) (b : Fin m → Fin p → H) (c : Fin p → Fin n → H)
    (hd : ∀ i j k, a i j * b j k * c k i = 1) :
    ∃ (s : Fin n → H) (t : Fin m → H) (u : Fin p → H),
      (∀ i j, a i j = s i * (t j)⁻¹) ∧
      (∀ j k, b j k = t j * (u k)⁻¹) ∧
      (∀ k i, c k i = u k * (s i)⁻¹) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let j₀ : Fin m := ⟨0, hm⟩
  let k₀ : Fin p := ⟨0, hp⟩
  let s := fun i => (c k₀ i)⁻¹
  let t := fun j => b j k₀
  let u := fun k => c k i₀ * (c k₀ i₀)⁻¹
  have ha : ∀ i j, a i j = s i * (t j)⁻¹ := by
    intro i j
    calc
      a i j = (a i j * b j k₀ * c k₀ i) * (c k₀ i)⁻¹ * (b j k₀)⁻¹ := by group
      _ = s i * (t j)⁻¹ := by rw [hd]; simp [s, t]
  have hb : ∀ j k, b j k = t j * (u k)⁻¹ := by
    intro j k
    calc
      b j k = (a i₀ j)⁻¹ * (a i₀ j * b j k * c k i₀) * (c k i₀)⁻¹ := by group
      _ = t j * (u k)⁻¹ := by rw [hd, ha]; simp [s, t, u, mul_assoc]
  have hc : ∀ k i, c k i = u k * (s i)⁻¹ := by
    intro k i
    calc
      c k i = (b j₀ k)⁻¹ * (a i j₀)⁻¹ * (a i j₀ * b j₀ k * c k i) := by group
      _ = u k * (s i)⁻¹ := by rw [hd, ha, hb]; simp [mul_assoc]
  exact ⟨s, t, u, ha, hb, hc⟩

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}
variable {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
variable {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}

/-- Every positive-dimensional monomial realization has group labels in the
normal form `a = s * t⁻¹`, `b = t * u⁻¹`, `c = u * s⁻¹`. -/
theorem group_normal_form (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    ∃ (s : Fin n → G) (t : Fin m → G) (u : Fin p → G),
      (∀ i j, a i j = s i * (t j)⁻¹) ∧
      (∀ j k, b j k = t j * (u k)⁻¹) ∧
      (∀ k i, c k i = u k * (s i)⁻¹) :=
  diagonal_normal_form hn hm hp a b c (diagonal_group_prod_eq_one h)

private theorem scalar_units_normal_form (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    ∃ (s : Fin n → Fˣ) (t : Fin m → Fˣ) (u : Fin p → Fˣ),
      (∀ i j, α i j = (s i : F) * ((t j)⁻¹ : Fˣ)) ∧
      (∀ j k, β j k = (t j : F) * ((u k)⁻¹ : Fˣ)) ∧
      (∀ k i, γ k i = (u k : F) * ((s i)⁻¹ : Fˣ)) := by
  let A := fun i j => Units.mk0 (α i j) (h.alpha_ne_zero i j)
  let B := fun j k => Units.mk0 (β j k) (h.beta_ne_zero j k)
  let C := fun k i => Units.mk0 (γ k i) (h.gamma_ne_zero k i)
  have hd : ∀ i j k, A i j * B j k * C k i = 1 := by
    intro i j k
    apply Units.ext
    exact diagonal_coeff h i j k
  obtain ⟨s, t, u, ha, hb, hc⟩ := diagonal_normal_form hn hm hp A B C hd
  refine ⟨s, t, u, ?_, ?_, ?_⟩
  · intro i j
    exact congrArg (fun x : Fˣ => (x : F)) (ha i j)
  · intro j k
    exact congrArg (fun x : Fˣ => (x : F)) (hb j k)
  · intro k i
    exact congrArg (fun x : Fˣ => (x : F)) (hc k i)

/-- The three scalar matrices of a positive-dimensional monomial realization
have balanced multiplicative two-by-two minors. -/
theorem scalar_minors (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    (∀ i i' j j', α i j * α i' j' = α i j' * α i' j) ∧
    (∀ j j' k k', β j k * β j' k' = β j k' * β j' k) ∧
    (∀ k k' i i', γ k i * γ k' i' = γ k i' * γ k' i) := by
  obtain ⟨s, t, u, ha, hb, hc⟩ := scalar_units_normal_form hn hm hp h
  refine ⟨?_, ?_, ?_⟩
  · intro i i' j j'
    simp only [ha]
    ring
  · intro j j' k k'
    simp only [hb]
    ring
  · intro k k' i i'
    simp only [hc]
    ring

/-- Two positive-dimensional monomial realizations with the same group labels
differ by a scalar gauge on the three index sets. -/
theorem scalar_gauge (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    {α' : Fin n → Fin m → F} {β' : Fin m → Fin p → F} {γ' : Fin p → Fin n → F}
    (h : IsMonomialRealization a b c α β γ)
    (h' : IsMonomialRealization a b c α' β' γ') :
    ∃ (u : Fin n → F) (v : Fin m → F) (w : Fin p → F),
      (∀ i j, α' i j = α i j * u i * v j) ∧
      (∀ j k, β' j k = β j k * (v j)⁻¹ * w k) ∧
      (∀ k i, γ' k i = γ k i * (w k)⁻¹ * (u i)⁻¹) := by
  obtain ⟨s, t, r, ha, hb, hc⟩ := scalar_units_normal_form hn hm hp h
  obtain ⟨s', t', r', ha', hb', hc'⟩ := scalar_units_normal_form hn hm hp h'
  refine ⟨(fun i => (s' i : F) / (s i : F)),
    (fun j => (t j : F) / (t' j : F)),
    (fun k => (r k : F) / (r' k : F)), ?_, ?_, ?_⟩
  · intro i j
    rw [ha, ha']
    field_simp
    simp
  · intro j k
    rw [hb, hb']
    field_simp
    simp
  · intro k i
    rw [hc, hc']
    field_simp
    simp

example :
    let g := fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚˣ)
    let f := fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ)
    (0 < (1 : ℕ)) ∧ (0 < (1 : ℕ)) ∧ (0 < (1 : ℕ)) ∧
      IsMonomialRealization g g g f f f ∧ IsMonomialRealization g g g f f f := by
  dsimp only
  refine ⟨by decide, by decide, by decide, ?_⟩
  suffices h : IsMonomialRealization
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚˣ))
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚˣ))
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚˣ))
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ))
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ))
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ)) by
    exact ⟨h, h⟩
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
