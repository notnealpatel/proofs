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
  have hj12 : j₁ = j₂ := by
    have := congr_arg Prod.fst (hb₁.symm.trans hb₂)
    simpa using this
  have hk12 : k₁ = k₂ := by
    have := congr_arg Prod.snd (hb₁.symm.trans hb₂)
    simpa using this
  have hi12 : i₁ = i₂ := by
    have := congr_arg Prod.fst (hc₁.symm.trans hc₂)
    simpa using this
  simp [hi12, hj12]

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
  have hi12 : i₁ = i₂ := by
    have := congr_arg Prod.fst (ha₁.symm.trans ha₂)
    simpa using this
  have hk12 : k₁ = k₂ := by
    have := congr_arg Prod.snd (hc₁.symm.trans hc₂)
    simpa using this
  have hj12 : j₁ = j₂ := by
    have := congr_arg Prod.snd (ha₁.symm.trans ha₂)
    simpa using this
  simp [hj12, hk12]

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

/-- If `x ∉ acc` and `x` is in none of the sets, then `x ∉ foldl Δ acc Ss`. -/
private lemma not_mem_foldl_symmDiff_of_not_mem [DecidableEq α] {x : α}
    {acc : Finset α} (ha : x ∉ acc)
    {Ss : List (Finset α)} (hSs : ∀ S ∈ Ss, x ∉ S) :
    x ∉ Ss.foldl (· ∆ ·) acc := by
  induction Ss generalizing acc with
  | nil => simpa [List.foldl]
  | cons S Ss ih =>
    simp only [List.foldl_cons]
    have hS_nmem : x ∉ S := hSs S (List.Mem.head _)
    have ha' : x ∉ acc ∆ S := by
      rw [Finset.mem_symmDiff]
      rintro (⟨hacc, _⟩ | ⟨hS, _⟩)
      · exact ha hacc
      · exact hS_nmem hS
    exact ih ha' (fun S' hS' => hSs S' (List.Mem.tail _ hS'))

/-- If `x ∈ foldl (· ∆ ·) ∅ Ss` then `x` is in some member of `Ss`. -/
private lemma exists_mem_of_mem_foldl_symmDiff [DecidableEq α] {x : α}
    {Ss : List (Finset α)} (h : x ∈ Ss.foldl (· ∆ ·) ∅) :
    ∃ S ∈ Ss, x ∈ S := by
  by_contra hall
  simp only [not_exists, not_and] at hall
  exact not_mem_foldl_symmDiff_of_not_mem (by simp) hall h

/-- Generalized: x ∈ foldl Δ acc Ss ↔ (Odd count ↔ x ∉ acc). -/
private lemma mem_foldl_symmDiff_iff [DecidableEq α] (x : α) (acc : Finset α)
    (Ss : List (Finset α)) :
    x ∈ Ss.foldl (· ∆ ·) acc ↔
      (Odd (Ss.countP (x ∈ ·)) ↔ x ∉ acc) := by
  induction Ss generalizing acc with
  | nil =>
    simp only [List.foldl_nil, List.countP_nil]
    tauto
  | cons S Ss ih =>
    simp only [List.foldl_cons, List.countP_cons]
    rw [ih]
    simp only [Finset.mem_symmDiff]
    by_cases hS : x ∈ S <;> by_cases ha : x ∈ acc <;>
      simp [hS, ha, Nat.odd_add, Nat.odd_one] <;> tauto

/-- Membership in iterated symmetric difference ↔ odd count. -/
private lemma mem_foldl_symmDiff [DecidableEq α] (x : α) (Ss : List (Finset α)) :
    x ∈ Ss.foldl (· ∆ ·) ∅ ↔ Odd (Ss.countP (x ∈ ·)) := by
  rw [mem_foldl_symmDiff_iff]
  simp

/-- **L0 (Bridge).** A list of boxes is a decomposition of `T n` iff
every cell of `T n` is covered an odd number of times and every
cell outside `T n` is covered an even number of times. -/
theorem isDecomp_iff_parity {n : ℕ} {L : List (Box n)} :
    IsDecomp n L ↔
      (∀ t, t ∈ matmulSupport n → Odd (coverCount t L)) ∧
      (∀ t, t ∉ matmulSupport n → Even (coverCount t L)) := by
  unfold IsDecomp coverCount
  constructor
  · intro hd
    constructor
    · intro t ht
      rw [← hd] at ht
      rw [mem_foldl_symmDiff] at ht
      convert ht using 1
      simp only [List.countP_map]
    · intro t ht
      rw [Nat.even_iff_not_odd]
      intro hodd
      apply ht
      rw [← hd]
      rw [mem_foldl_symmDiff]
      convert hodd using 1
      simp only [List.countP_map]
  · intro ⟨hodd, heven⟩
    ext t
    rw [mem_foldl_symmDiff]
    constructor
    · intro h
      have := hodd t
      have := heven t
      by_contra hnt
      have hev := heven t hnt
      rw [Nat.even_iff_not_odd] at hev
      have : Odd ((L.map Box.support).countP (t ∈ ·)) := h
      simp only [List.countP_map] at this
      exact hev this
    · intro ht
      have := hodd t ht
      simp only [List.countP_map]
      exact this

/-! ### L2: Shadow bound -/

/-- Auxiliary: rewrite a triple as nested pairs. -/
private lemma triple_eta (t : Triple n) : t = (t.1, t.2.1, t.2.2) := by
  obtain ⟨a, b, c⟩ := t; rfl

/-- Auxiliary: the projection `(a, b, c) ↦ (a, b)` is injective on `T n`. -/
lemma proj12_injOn_matmulSupport {n : ℕ} :
    Set.InjOn (fun (t : Triple n) => (t.1, t.2.1))
      (↑(matmulSupport n) : Set (Triple n)) := by
  intro t₁ ht₁ t₂ ht₂ heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨ha, hb⟩ := heq
  have hT₁ : (t₁.1, t₁.2.1, t₁.2.2) ∈ matmulSupport n := by
    rwa [← triple_eta t₁]
  have hT₂ : (t₁.1, t₁.2.1, t₂.2.2) ∈ matmulSupport n := by
    rw [ha, hb]; rwa [← triple_eta t₂]
  have hc := line_property_12 hT₁ hT₂
  rw [triple_eta t₁, triple_eta t₂, ha, hb, hc]

/-- **L2a.** `|supp τ ∩ T n| ≤ |U| * |V|`. -/
theorem shadow_bound_12 {n : ℕ} (τ : Box n) :
    τ.mass ≤ τ.U.card * τ.V.card := by
  unfold Box.mass
  rw [← card_product]
  apply card_le_card_of_injOn (fun t => (t.1, t.2.1))
  · intro t ht
    simp only [Finset.mem_coe, mem_inter, Box.support, mem_product] at ht ⊢
    exact ⟨ht.1.1, ht.1.2.1⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_coe, mem_inter] at ht₁ ht₂
    exact proj12_injOn_matmulSupport (Finset.mem_coe.mpr ht₁.2) (Finset.mem_coe.mpr ht₂.2) heq

/-- Auxiliary: the projection `(a, b, c) ↦ (b, c)` is injective on `T n`. -/
lemma proj23_injOn_matmulSupport {n : ℕ} :
    Set.InjOn (fun (t : Triple n) => t.2)
      (↑(matmulSupport n) : Set (Triple n)) := by
  intro t₁ ht₁ t₂ ht₂ heq
  have hb : t₁.2.1 = t₂.2.1 := congr_arg Prod.fst heq
  have hc : t₁.2.2 = t₂.2.2 := congr_arg Prod.snd heq
  have hT₁ : (t₁.1, t₁.2.1, t₁.2.2) ∈ matmulSupport n := by rwa [← triple_eta t₁]
  have hT₂ : (t₂.1, t₁.2.1, t₁.2.2) ∈ matmulSupport n := by
    rw [hb, hc]; rwa [← triple_eta t₂]
  have ha := line_property_23 hT₁ hT₂
  rw [triple_eta t₁, triple_eta t₂, ha, hb, hc]

/-- Auxiliary: the projection `(a, b, c) ↦ (a, c)` is injective on `T n`. -/
lemma proj13_injOn_matmulSupport {n : ℕ} :
    Set.InjOn (fun (t : Triple n) => (t.1, t.2.2))
      (↑(matmulSupport n) : Set (Triple n)) := by
  intro t₁ ht₁ t₂ ht₂ heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨ha, hc⟩ := heq
  have hT₁ : (t₁.1, t₁.2.1, t₁.2.2) ∈ matmulSupport n := by rwa [← triple_eta t₁]
  have hT₂ : (t₁.1, t₂.2.1, t₁.2.2) ∈ matmulSupport n := by
    rw [ha, hc]; rwa [← triple_eta t₂]
  have hb := line_property_13 hT₁ hT₂
  rw [triple_eta t₁, triple_eta t₂, ha, hb, hc]

/-- **L2b.** `|supp τ ∩ T n| ≤ |V| * |W|`. -/
theorem shadow_bound_23 {n : ℕ} (τ : Box n) :
    τ.mass ≤ τ.V.card * τ.W.card := by
  unfold Box.mass
  rw [← card_product]
  apply card_le_card_of_injOn (fun t => t.2)
  · intro t ht
    simp only [Finset.mem_coe, mem_inter, Box.support, mem_product] at ht ⊢
    exact ht.1.2
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_coe, mem_inter] at ht₁ ht₂
    exact proj23_injOn_matmulSupport (Finset.mem_coe.mpr ht₁.2) (Finset.mem_coe.mpr ht₂.2) heq

/-- **L2c.** `|supp τ ∩ T n| ≤ |U| * |W|`. -/
theorem shadow_bound_13 {n : ℕ} (τ : Box n) :
    τ.mass ≤ τ.U.card * τ.W.card := by
  unfold Box.mass
  rw [← card_product]
  apply card_le_card_of_injOn (fun t => (t.1, t.2.2))
  · intro t ht
    simp only [Finset.mem_coe, mem_inter, Box.support, mem_product] at ht ⊢
    exact ⟨ht.1.1, ht.1.2.2⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_coe, mem_inter] at ht₁ ht₂
    exact proj13_injOn_matmulSupport (Finset.mem_coe.mpr ht₁.2) (Finset.mem_coe.mpr ht₂.2) heq

/-- **L2 (cube bound).** `m³ ≤ |τ|²`. -/
theorem shadow_cube_bound {n : ℕ} (τ : Box n) :
    τ.mass ^ 3 ≤ τ.support.card ^ 2 := by
  -- m³ ≤ (|U|·|V|) · (|V|·|W|) · (|U|·|W|) = (|U|·|V|·|W|)² = |τ|²
  have h12 := shadow_bound_12 τ
  have h23 := shadow_bound_23 τ
  have h13 := shadow_bound_13 τ
  rw [τ.card_support]
  calc τ.mass ^ 3
      = τ.mass * τ.mass * τ.mass := by ring
    _ ≤ (τ.U.card * τ.V.card) * (τ.V.card * τ.W.card) * (τ.U.card * τ.W.card) :=
        Nat.mul_le_mul (Nat.mul_le_mul h12 h23) h13
    _ = (τ.U.card * τ.V.card * τ.W.card) ^ 2 := by ring

/-! ### L3: Cover parity -/

/-- Total mass: `Σ mᵢ`. -/
def totalMass (n : ℕ) (L : List (Box n)) : ℕ :=
  (L.map (fun τ => τ.mass)).sum

/-- Total out-mass: `Σ (|τᵢ| - mᵢ)`. -/
def totalOutMass (n : ℕ) (L : List (Box n)) : ℕ :=
  (L.map (fun τ => τ.outMass)).sum

/-- Each element of T is in some box support for any decomposition. -/
private lemma mem_some_support_of_isDecomp {n : ℕ} {L : List (Box n)}
    (hd : IsDecomp n L) {t : Triple n} (ht : t ∈ matmulSupport n) :
    ∃ τ ∈ L, t ∈ τ.support := by
  have hfold : t ∈ (L.map Box.support).foldl (· ∆ ·) ∅ := by
    rw [hd]; exact ht
  obtain ⟨S, hS_mem, hS⟩ := exists_mem_of_mem_foldl_symmDiff hfold
  rw [List.mem_map] at hS_mem
  obtain ⟨τ, hτ_mem, hτ_eq⟩ := hS_mem
  exact ⟨τ, hτ_mem, hτ_eq ▸ hS⟩

/-- Covering lemma: if `T ⊆ ⋃ Ss` then `|T| ≤ Σᵢ |Sᵢ ∩ T|`. -/
private lemma card_le_sum_card_inter [DecidableEq α] :
    ∀ (T : Finset α) (Ss : List (Finset α)),
    T ⊆ Ss.foldr (· ∪ ·) ∅ →
    T.card ≤ (Ss.map (fun S => (S ∩ T).card)).sum := by
  intro T Ss
  induction Ss generalizing T with
  | nil => intro h; simp at h; simp [h]
  | cons S Ss ih =>
    intro h
    simp only [List.foldr_cons] at h
    simp only [List.map_cons, List.sum_cons]
    have hTS := card_sdiff_add_card_inter T S
    rw [inter_comm] at hTS
    -- T \ S ⊆ ⋃ Ss (since everything in T is in S ∪ ⋃Ss)
    have hTmS : T \ S ⊆ Ss.foldr (· ∪ ·) ∅ := by
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      have := h hx.1
      simp only [Finset.mem_union] at this
      exact this.elim (absurd · hx.2) id
    calc T.card = (T \ S).card + (S ∩ T).card := by omega
      _ ≤ (Ss.map (fun S' => (S' ∩ (T \ S)).card)).sum + (S ∩ T).card := by
          exact Nat.add_le_add_right (ih (T \ S) hTmS) _
      _ ≤ (Ss.map (fun S' => (S' ∩ T).card)).sum + (S ∩ T).card := by
          apply Nat.add_le_add_right
          -- pointwise: (S' ∩ (T \ S)).card ≤ (S' ∩ T).card for each S' in Ss
          have : ∀ (L : List (Finset α)),
              (L.map (fun S' => (S' ∩ (T \ S)).card)).sum ≤
              (L.map (fun S' => (S' ∩ T).card)).sum := by
            intro L
            induction L with
            | nil => simp
            | cons S' L' ihL =>
              simp only [List.map_cons, List.sum_cons]
              apply Nat.add_le_add
              · apply card_le_card
                intro x hx
                simp only [mem_inter, mem_sdiff] at hx ⊢
                exact ⟨hx.1, hx.2.1⟩
              · exact ihL
          exact this Ss
      _ = (S ∩ T).card + (Ss.map (fun S' => (S' ∩ T).card)).sum := by omega

/-- **L3a.** `Σ mᵢ ≥ n³`. -/
theorem cover_sum_ge {n : ℕ} {L : List (Box n)} (hd : IsDecomp n L) :
    n ^ 3 ≤ totalMass n L := by
  rw [← matmulSupport_card n]
  unfold totalMass
  -- Show matmulSupport n ⊆ union of all supports
  have hcover : matmulSupport n ⊆
      (L.map Box.support).foldr (· ∪ ·) ∅ := by
    intro t ht
    obtain ⟨τ, hτ_mem, hτ⟩ := mem_some_support_of_isDecomp hd ht
    clear hd ht
    induction L with
    | nil => simp at hτ_mem
    | cons τ' L' ih =>
      simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
      rcases List.mem_cons.mp hτ_mem with rfl | hτ_mem'
      · left; exact hτ
      · right; exact ih hτ_mem'
  calc (matmulSupport n).card
      ≤ ((L.map Box.support).map (fun S => (S ∩ matmulSupport n).card)).sum :=
        card_le_sum_card_inter _ _ hcover
    _ = (L.map (fun τ => τ.mass)).sum := by
        simp only [List.map_map]; rfl

/-- **L3b.** The total out-mass is even. -/
theorem cover_outmass_even {n : ℕ} {L : List (Box n)} (hd : IsDecomp n L) :
    Even (totalOutMass n L) := by
  sorry

/-! ### L4: Slack-0 move bound -/

/-- The symmetric difference has card = |T \ S| + |S \ T|. -/
private lemma card_symmDiff [DecidableEq α] (s t : Finset α) :
    (s ∆ t).card = (s \ t).card + (t \ s).card := by
  rw [symmDiff_def, Finset.sup_eq_union,
      (card_union_eq_card_add_card).mpr disjoint_sdiff_sdiff]

/-- Mass is at most box size: `m ≤ |τ|`. -/
lemma mass_le_card_support (τ : Box n) : τ.mass ≤ τ.support.card :=
  card_le_card inter_subset_left

/-- Mass is at most `|T n|`: `m ≤ n³`. -/
lemma mass_le_matmulSupport_card (τ : Box n) :
    τ.mass ≤ (matmulSupport n).card :=
  card_le_card inter_subset_right

/-- **L4a.** If `|T n Δ supp τ| ≤ n³`, then `|τ| ≤ 2m`. -/
theorem slack0_size_bound {n : ℕ} (τ : Box n)
    (h : (matmulSupport n ∆ τ.support).card ≤ n ^ 3) :
    τ.support.card ≤ 2 * τ.mass := by
  -- |T Δ S| = |T \ S| + |S \ T|
  rw [card_symmDiff] at h
  -- |S \ T| + |S ∩ T| = |S|
  have hSt := card_sdiff_add_card_inter τ.support (matmulSupport n)
  -- |T \ S| + |T ∩ S| = |T|, and |T ∩ S| = |S ∩ T| = m
  have hTs := card_sdiff_add_card_inter (matmulSupport n) τ.support
  rw [matmulSupport_card] at hTs
  -- Note: mass = |S ∩ T| and inter_comm gives |S ∩ T| = |T ∩ S|
  have hmass : τ.mass = (τ.support ∩ matmulSupport n).card := rfl
  have hcomm : (τ.support ∩ matmulSupport n).card =
      (matmulSupport n ∩ τ.support).card := by rw [inter_comm]
  -- Now: (T\S).card + mass = n³, (S\T).card + mass = |S|
  -- And: (T\S).card + (S\T).card ≤ n³
  -- So: (S\T).card ≤ n³ - (T\S).card = mass
  -- Hence: |S| = (S\T).card + mass ≤ mass + mass = 2*mass
  omega

/-- **L4b.** Under the same hypothesis, `m ≤ 4`. -/
theorem slack0_m_le {n : ℕ} (τ : Box n)
    (h : (matmulSupport n ∆ τ.support).card ≤ n ^ 3) :
    τ.mass ≤ 4 := by
  -- From L4a: |τ| ≤ 2m. From L2: m³ ≤ |τ|².
  -- So m³ ≤ (2m)² = 4m², hence m ≤ 4.
  have hsz := slack0_size_bound τ h
  have hcube := shadow_cube_bound τ
  -- m³ ≤ |τ|² ≤ (2m)² = 4m²
  have h1 : τ.mass ^ 3 ≤ (2 * τ.mass) ^ 2 :=
    le_trans hcube (Nat.pow_le_pow_left hsz 2)
  -- m³ ≤ 4m² implies m ≤ 4
  -- (2m)² = 4m², so m³ ≤ 4m², i.e. m * m² ≤ 4 * m²
  -- Case m = 0: trivial. Case m > 0: cancel m² to get m ≤ 4.
  by_cases hm0 : τ.mass = 0
  · omega
  · -- m > 0, so m² > 0
    have hm_pos : 0 < τ.mass := Nat.pos_of_ne_zero hm0
    -- h1 : m³ ≤ (2m)² = 4m²
    -- i.e. m * m * m ≤ 4 * (m * m)
    -- Cancel m * m (positive) to get m ≤ 4
    have hmsq_pos : 0 < τ.mass ^ 2 := by positivity
    rw [show τ.mass ^ 3 = τ.mass * τ.mass ^ 2 from by ring,
        show (2 * τ.mass) ^ 2 = 4 * τ.mass ^ 2 from by ring] at h1
    exact le_of_mul_le_mul_right h1 hmsq_pos

/-- **L4c.** Under the same hypothesis, `|τ| ≤ 8`. -/
theorem slack0_tau_le {n : ℕ} (τ : Box n)
    (h : (matmulSupport n ∆ τ.support).card ≤ n ^ 3) :
    τ.support.card ≤ 8 := by
  calc τ.support.card ≤ 2 * τ.mass := slack0_size_bound τ h
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 (slack0_m_le τ h)
    _ = 8 := by norm_num

/-! ### L5: Out-mass ≥ 2 below n³ terms -/

/-- **L5.** Any decomposition with fewer than `n³` boxes has
out-mass ≥ 2. -/
theorem outmass_ge_two {n : ℕ} {L : List (Box n)}
    (hd : IsDecomp n L) (hr : L.length < n ^ 3) :
    2 ≤ totalOutMass n L := by
  sorry

end Xlib.PeelingSupport
