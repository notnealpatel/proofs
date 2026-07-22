import Mathlib

/-!
# Support-geometry foundation for the peeling-peak invariant

Formalization of five lemmas (L0–L5) about the combinatorial geometry
of the matrix-multiplication support `T n` and its F₂-decompositions
into indicator boxes.

## Setting

Over F₂, a rank-1 tensor is an indicator box: for nonempty
`U V W : Finset (Fin n × Fin n)`, its support is the product set
`U ×ˢ V ×ˢ W`, of size `|U|·|V|·|W|`. The matmul support is

  `T n = {((i,j), (j,k), (i,k)) : i j k : Fin n}`

with `|T n| = n³`. A decomposition of length `r` is a list of `r`
boxes whose iterated symmetric difference equals `T n` — equivalently,
every cell of `T n` lies in an odd number of the boxes and every other
cell in an even number.

## Main results

* `matmulSupport_card` — `|T n| = n³`.
* `line_property_12`, `line_property_23`, `line_property_13` (L1) —
  each axis line meets `T n` at most once.
* `shadow_bound_12`, `shadow_bound_23`, `shadow_bound_13` (L2) —
  `|supp τ ∩ T n| ≤ |U|·|V|` (and cyclic variants);
  `shadow_cube_bound` — `m³ ≤ |τ|²`.
* `cover_sum_ge` (L3) — `Σ mᵢ ≥ n³`; `cover_outmass_even` — total
  out-mass is even.
* `slack0_size_bound` (L4) — `|τ| ≤ 2m`; `slack0_m_le` — `m ≤ 4`;
  `slack0_tau_le` — `|τ| ≤ 8`.
* `outmass_ge_two` (L5) — any decomposition with `r < n³` has
  out-mass ≥ 2.
-/

namespace Xlib.PeelingSupport

open Finset
open scoped symmDiff

/-! ### Coordinate type and matmul support -/

/-- Index type for one axis of the matmul tensor. We encode the pair
`(i, j)` with `i j : Fin n` as a single element of `Fin n × Fin n`
rather than `Fin (n²)`, avoiding encoding overhead while preserving
all box-product structure. -/
abbrev Idx (n : ℕ) := Fin n × Fin n

/-- Triple type: an element of the 3-tensor space. -/
abbrev Triple (n : ℕ) := Idx n × Idx n × Idx n

/-- The matmul support `T n`: the set of triples
`((i,j), (j,k), (i,k))` for `i, j, k : Fin n`. -/
def matmulSupport (n : ℕ) : Finset (Triple n) :=
  (univ : Finset (Fin n × Fin n × Fin n)).image
    (fun ijk => ((ijk.1, ijk.2.1), (ijk.2.1, ijk.2.2), (ijk.1, ijk.2.2)))

/-- The embedding `Fin n × Fin n × Fin n → Triple n` that defines `T n`. -/
def matmulEmbed (n : ℕ) : Fin n × Fin n × Fin n → Triple n :=
  fun ijk => ((ijk.1, ijk.2.1), (ijk.2.1, ijk.2.2), (ijk.1, ijk.2.2))

lemma matmulEmbed_injective (n : ℕ) : Function.Injective (matmulEmbed n) := by
  intro ⟨i₁, j₁, k₁⟩ ⟨i₂, j₂, k₂⟩ h
  simp only [matmulEmbed, Prod.mk.injEq] at h
  obtain ⟨⟨hi, hj1⟩, ⟨_, hk⟩, ⟨_, _⟩⟩ := h
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨hi, Prod.mk.injEq _ _ _ _ |>.mpr ⟨hj1, hk⟩⟩

/-- `|T n| = n³`. -/
theorem matmulSupport_card (n : ℕ) :
    (matmulSupport n).card = n ^ 3 := by
  unfold matmulSupport
  have : (fun ijk : Fin n × Fin n × Fin n =>
      ((ijk.1, ijk.2.1), (ijk.2.1, ijk.2.2), (ijk.1, ijk.2.2))) =
    matmulEmbed n := rfl
  rw [this, card_image_of_injective _ (matmulEmbed_injective n)]
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Membership in `T n`. -/
theorem mem_matmulSupport {n : ℕ} {t : Triple n} :
    t ∈ matmulSupport n ↔
      ∃ i j k : Fin n, t = ((i, j), (j, k), (i, k)) := by
  simp only [matmulSupport, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, j, k⟩, h⟩
    exact ⟨i, j, k, h.symm⟩
  · rintro ⟨i, j, k, h⟩
    exact ⟨⟨i, j, k⟩, h.symm⟩

/-! ### L1: Line property -/

/-- **L1a.** For fixed first two coordinates `(a, b)`, there is at most
one third coordinate `c` such that `(a, b, c) ∈ T n`. -/
theorem line_property_12 {n : ℕ} {a b c₁ c₂ : Idx n}
    (h₁ : (a, b, c₁) ∈ matmulSupport n)
    (h₂ : (a, b, c₂) ∈ matmulSupport n) :
    c₁ = c₂ := by
  rw [mem_matmulSupport] at h₁ h₂
  obtain ⟨i₁, j₁, k₁, h₁⟩ := h₁
  obtain ⟨i₂, j₂, k₂, h₂⟩ := h₂
  -- h₁ : (a, b, c₁) = ((i₁, j₁), (j₁, k₁), (i₁, k₁))
  -- h₂ : (a, b, c₂) = ((i₂, j₂), (j₂, k₂), (i₂, k₂))
  have ha₁ := congr_arg Prod.fst h₁  -- a = (i₁, j₁)
  have hb₁ := congr_arg (fun x => x.2.1) h₁  -- b = (j₁, k₁)
  have hc₁ := congr_arg (fun x => x.2.2) h₁  -- c₁ = (i₁, k₁)
  have ha₂ := congr_arg Prod.fst h₂
  have hb₂ := congr_arg (fun x => x.2.1) h₂
  have hc₂ := congr_arg (fun x => x.2.2) h₂
  -- From a = (i₁, j₁) = (i₂, j₂), we get i₁ = i₂ and j₁ = j₂
  -- From b = (j₁, k₁) = (j₂, k₂), combined with j₁ = j₂, we get k₁ = k₂
  -- Then c₁ = (i₁, k₁) = (i₂, k₂) = c₂
  simp only at ha₁ hb₁ hc₁ ha₂ hb₂ hc₂
  rw [hc₁, hc₂]
  have : i₁ = i₂ := by
    have := congr_arg Prod.fst (ha₁.symm.trans ha₂)
    simpa using this
  have : k₁ = k₂ := by
    have := congr_arg Prod.snd (hb₁.symm.trans hb₂)
    simpa using this
  simp [*]

/-- **L1b.** For fixed second and third coordinates `(b, c)`, there is
at most one first coordinate `a`. -/
theorem line_property_23 {n : ℕ} {a₁ a₂ b c : Idx n}
    (h₁ : (a₁, b, c) ∈ matmulSupport n)
    (h₂ : (a₂, b, c) ∈ matmulSupport n) :
    a₁ = a₂ := by
  rw [mem_matmulSupport] at h₁ h₂
  obtain ⟨i₁, j₁, k₁, h₁⟩ := h₁
  obtain ⟨i₂, j₂, k₂, h₂⟩ := h₂
  have hb₁ := congr_arg (fun x => x.2.1) h₁
  have hc₁ := congr_arg (fun x => x.2.2) h₁
  have ha₁ := congr_arg Prod.fst h₁
  have hb₂ := congr_arg (fun x => x.2.1) h₂
  have hc₂ := congr_arg (fun x => x.2.2) h₂
  have ha₂ := congr_arg Prod.fst h₂
  simp only at ha₁ hb₁ hc₁ ha₂ hb₂ hc₂
  rw [ha₁, ha₂]
  have : j₁ = j₂ := by
    have := congr_arg Prod.fst (hb₁.symm.trans hb₂)
    simpa using this
  have : k₁ = k₂ := by
    have := congr_arg Prod.snd (hb₁.symm.trans hb₂)
    simpa using this
  simp [*]

/-- **L1c.** For fixed first and third coordinates `(a, c)`, there is
at most one second coordinate `b`. -/
theorem line_property_13 {n : ℕ} {a b₁ b₂ c : Idx n}
    (h₁ : (a, b₁, c) ∈ matmulSupport n)
    (h₂ : (a, b₂, c) ∈ matmulSupport n) :
    b₁ = b₂ := by
  rw [mem_matmulSupport] at h₁ h₂
  obtain ⟨i₁, j₁, k₁, h₁⟩ := h₁
  obtain ⟨i₂, j₂, k₂, h₂⟩ := h₂
  have ha₁ := congr_arg Prod.fst h₁
  have hb₁ := congr_arg (fun x => x.2.1) h₁
  have hc₁ := congr_arg (fun x => x.2.2) h₁
  have ha₂ := congr_arg Prod.fst h₂
  have hb₂ := congr_arg (fun x => x.2.1) h₂
  have hc₂ := congr_arg (fun x => x.2.2) h₂
  simp only at ha₁ hb₁ hc₁ ha₂ hb₂ hc₂
  rw [hb₁, hb₂]
  have : i₁ = i₂ := by
    have := congr_arg Prod.fst (ha₁.symm.trans ha₂)
    simpa using this
  have : k₁ = k₂ := by
    have := congr_arg Prod.snd (hc₁.symm.trans hc₂)
    simpa using this
  simp [*]

/-! ### Boxes and decompositions -/

/-- A **box** is a triple of finsets; its support is the product set. -/
structure Box (n : ℕ) where
  U : Finset (Idx n)
  V : Finset (Idx n)
  W : Finset (Idx n)

/-- The support of a box: `U ×ˢ V ×ˢ W`. -/
def Box.support (τ : Box n) : Finset (Triple n) :=
  τ.U ×ˢ (τ.V ×ˢ τ.W)

/-- The size of a box is `|U| * |V| * |W|`. -/
theorem Box.card_support (τ : Box n) :
    τ.support.card = τ.U.card * τ.V.card * τ.W.card := by
  simp [Box.support, card_product]
  ring

/-- The **intersection mass** of a box with `T n`. -/
def Box.mass (τ : Box n) : ℕ :=
  (τ.support ∩ matmulSupport n).card

/-- The **out-mass** of a box: `|τ| - m`. -/
def Box.outMass (τ : Box n) : ℕ :=
  τ.support.card - τ.mass

/-- An F₂-**decomposition** of `T n` is a list of boxes whose iterated
symmetric difference of supports equals `T n`. -/
def IsDecomp (n : ℕ) (L : List (Box n)) : Prop :=
  (L.map Box.support).foldl (· ∆ ·) ∅ = matmulSupport n

/-! ### L0: Bridge (decomposition ↔ parity condition) -/

/-- Count how many boxes in a list contain a given triple. -/
def coverCount (t : Triple n) (L : List (Box n)) : ℕ :=
  (L.filter (fun τ => t ∈ τ.support)).length

/-- **L0 (Bridge).** A list of boxes is a decomposition of `T n` iff
every cell of `T n` is covered an odd number of times and every
cell outside `T n` is covered an even number of times. -/
theorem isDecomp_iff_parity {n : ℕ} {L : List (Box n)} :
    IsDecomp n L ↔
      (∀ t, t ∈ matmulSupport n → Odd (coverCount t L)) ∧
      (∀ t, t ∉ matmulSupport n → Even (coverCount t L)) := by
  sorry

/-! ### L2: Shadow bound -/

/-- **L2a.** `|supp τ ∩ T n| ≤ |U| * |V|`. -/
theorem shadow_bound_12 {n : ℕ} (τ : Box n) :
    τ.mass ≤ τ.U.card * τ.V.card := by
  sorry

/-- **L2b.** `|supp τ ∩ T n| ≤ |V| * |W|`. -/
theorem shadow_bound_23 {n : ℕ} (τ : Box n) :
    τ.mass ≤ τ.V.card * τ.W.card := by
  sorry

/-- **L2c.** `|supp τ ∩ T n| ≤ |U| * |W|`. -/
theorem shadow_bound_13 {n : ℕ} (τ : Box n) :
    τ.mass ≤ τ.U.card * τ.W.card := by
  sorry

/-- **L2 (cube bound).** `m³ ≤ |τ|²`. -/
theorem shadow_cube_bound {n : ℕ} (τ : Box n) :
    τ.mass ^ 3 ≤ τ.support.card ^ 2 := by
  sorry

/-! ### L3: Cover parity -/

/-- Total mass: `Σ mᵢ`. -/
def totalMass (n : ℕ) (L : List (Box n)) : ℕ :=
  (L.map (fun τ => τ.mass)).sum

/-- Total out-mass: `Σ (|τᵢ| - mᵢ)`. -/
def totalOutMass (n : ℕ) (L : List (Box n)) : ℕ :=
  (L.map (fun τ => τ.outMass)).sum

/-- **L3a.** `Σ mᵢ ≥ n³`. -/
theorem cover_sum_ge {n : ℕ} {L : List (Box n)} (hd : IsDecomp n L) :
    n ^ 3 ≤ totalMass n L := by
  sorry

/-- **L3b.** The total out-mass is even. -/
theorem cover_outmass_even {n : ℕ} {L : List (Box n)} (hd : IsDecomp n L) :
    Even (totalOutMass n L) := by
  sorry

/-! ### L4: Slack-0 move bound -/

/-- **L4a.** If `|T n Δ supp τ| ≤ n³`, then `|τ| ≤ 2m`. -/
theorem slack0_size_bound {n : ℕ} (τ : Box n)
    (h : (matmulSupport n ∆ τ.support).card ≤ n ^ 3) :
    τ.support.card ≤ 2 * τ.mass := by
  sorry

/-- **L4b.** Under the same hypothesis, `m ≤ 4`. -/
theorem slack0_m_le {n : ℕ} (τ : Box n)
    (h : (matmulSupport n ∆ τ.support).card ≤ n ^ 3) :
    τ.mass ≤ 4 := by
  sorry

/-- **L4c.** Under the same hypothesis, `|τ| ≤ 8`. -/
theorem slack0_tau_le {n : ℕ} (τ : Box n)
    (h : (matmulSupport n ∆ τ.support).card ≤ n ^ 3) :
    τ.support.card ≤ 8 := by
  sorry

/-! ### L5: Out-mass ≥ 2 below n³ terms -/

/-- **L5.** Any decomposition with fewer than `n³` boxes has
out-mass ≥ 2. -/
theorem outmass_ge_two {n : ℕ} {L : List (Box n)}
    (hd : IsDecomp n L) (hr : L.length < n ^ 3) :
    2 ≤ totalOutMass n L := by
  sorry

end Xlib.PeelingSupport
