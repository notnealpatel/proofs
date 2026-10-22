/-
# VC-dimension of the linear Green–Sanders example

V. Gladkova, *On a conjecture of Terry and Wolf*, arXiv:2411.05612,
Definitions 1.1, 1.2, 2.1 and Theorems 2.2, 1.2. The upper bound 3 is
originally Terry–Wolf, Corollary A.10. The set GS(p,n) consists of vectors
whose first nonzero coordinate equals 1.

For odd primes the translate family has VC-dimension at most 3; for
`p ≥ 5`, `n ≥ 2` it has dimension exactly 2. Theorem 1.2 as printed omits
the necessary `n ≥ 2`: `GS(p,1) = {1}` has dimension at most 1, whereas
the paper's lower-bound witness `{0,w₂}` needs a second coordinate.

## Conventions

`A` shatters `S` (via translates) when for every `T ⊆ S` there is `y` with
`s + y ∈ A ↔ s ∈ T` for all `s ∈ S`; that is, the family
`{A - y : y ∈ G}` shatters `S` in the sense of Definition 2.1, equivalently
Definition 1.2 with `x_i` the elements of `S`.  The standard basis vector
`w_{i+1}` is `Pi.single i 1` (Lean indices start at `0`).
-/
import Mathlib

set_option autoImplicit false

namespace VcDimensionLinearGreenSanders

open Finset

/-- The linear Green-Sanders example `GS(p,n) ⊆ 𝔽_p^n`: the vectors whose
first non-zero coordinate equals `1` (Definition 1.1 of arXiv:2411.05612). -/
def GS (p n : ℕ) : Set (Fin n → ZMod p) :=
  {x | ∃ i, (∀ j < i, x j = 0) ∧ x i = 1}

/-- Translates of `A` shatter the finset `S`: every subset `T ⊆ S` is cut out
as `S ∩ (A - y)` for some `y`, i.e. `s + y ∈ A ↔ s ∈ T` for all `s ∈ S`
(Definitions 1.2 and 2.1 of arXiv:2411.05612). -/
def TranslShatters {G : Type*} [Add G] (A : Set G) (S : Finset G) : Prop :=
  ∀ T ⊆ S, ∃ y, ∀ s ∈ S, (s + y ∈ A ↔ s ∈ T)

/-- Membership in `GS(p,n)` is decidable (a finite search over the coordinates). -/
instance (p n : ℕ) : DecidablePred (· ∈ GS p n) := fun x =>
  inferInstanceAs (Decidable (∃ i, (∀ j < i, x j = 0) ∧ x i = 1))

/-! Examples of `GS` on small instances. -/

/-- `(1, 2) ∈ GS(3,2)`. -/
example : (![1, 2] : Fin 2 → ZMod 3) ∈ GS 3 2 := ⟨0, by decide, rfl⟩

/-- `(0, 1, 2) ∈ GS(5,3)`. -/
example : (![0, 1, 2] : Fin 3 → ZMod 5) ∈ GS 5 3 := ⟨1, by decide, rfl⟩

/-- `(0, 2) ∉ GS(3,2)`: the first non-zero coordinate is `2 ≠ 1`. -/
example : (![0, 2] : Fin 2 → ZMod 3) ∉ GS 3 2 := by unfold GS; decide

/-- `0 ∉ GS(3,2)`. -/
example : (0 : Fin 2 → ZMod 3) ∉ GS 3 2 := by unfold GS; decide

/-- `GS(3,2)` has exactly `3 + 1 = 4` elements: `(1,*)` and `(0,1)`. -/
example : (Finset.univ.filter fun x : Fin 2 → ZMod 3 => x ∈ GS 3 2).card = 4 := by
  decide

/-- Translates of `{1} ⊆ ZMod 3` shatter `{0}` but
not `{0, 1}`. -/
example : TranslShatters ({1} : Set (ZMod 3)) {0} := by
  intro T hT
  rcases Finset.subset_singleton_iff.1 hT with rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

/-- Translates of `{1} ⊆ ZMod 3` do not shatter `{0, 1}`. -/
example : ¬ TranslShatters ({1} : Set (ZMod 3)) {0, 1} := by
  intro h
  obtain ⟨y, hy⟩ := h {0, 1} subset_rfl
  revert y
  decide

/-- `x` has first non-zero coordinate at index `i`, with value `c`. -/
def IsLead {p n : ℕ} (x : Fin n → ZMod p) (i : Fin n) (c : ZMod p) : Prop :=
  (∀ j < i, x j = 0) ∧ x i = c ∧ c ≠ 0

section Lead

variable {p n : ℕ}

/-- Leading data is unique. -/
theorem IsLead.unique {x : Fin n → ZMod p} {i i' : Fin n} {c c' : ZMod p}
    (h : IsLead x i c) (h' : IsLead x i' c') : i = i' ∧ c = c' := by
  have hx : x i ≠ 0 := by rw [h.2.1]; exact h.2.2
  have hx' : x i' ≠ 0 := by rw [h'.2.1]; exact h'.2.2
  have hii : i = i' := by
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact absurd (h'.1 i hlt) hx
    · exact heq
    · exact absurd (h.1 i' hgt) hx'
  subst hii
  exact ⟨rfl, h.2.1.symm.trans h'.2.1⟩

/-- Every non-zero vector has a first non-zero coordinate. -/
theorem exists_isLead {x : Fin n → ZMod p} (hx : x ≠ 0) : ∃ i, IsLead x i (x i) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  obtain ⟨i, hi, hmin⟩ := (wellFounded_lt (α := Fin n)).has_min {i | x i ≠ 0} ⟨k, hk⟩
  refine ⟨i, fun j hj => ?_, rfl, hi⟩
  by_contra hne
  exact hmin j hne hj

/-- The zero vector has no leading coordinate. -/
theorem not_isLead_zero {i : Fin n} {c : ZMod p} : ¬ IsLead (0 : Fin n → ZMod p) i c :=
  fun h => h.2.2 (h.2.1.symm.trans rfl)

/-- Membership in `GS(p,n)` is decided by the leading coefficient. -/
theorem mem_GS_iff_of_isLead [Fact p.Prime] {x : Fin n → ZMod p} {i : Fin n} {c : ZMod p}
    (h : IsLead x i c) : x ∈ GS p n ↔ c = 1 := by
  constructor
  · rintro ⟨i', hlt, hi'⟩
    exact (IsLead.unique ⟨hlt, hi', one_ne_zero⟩ h).2.symm
  · rintro rfl
    exact ⟨i, h.1, h.2.1⟩

/-- The zero vector is not in `GS(p,n)`. -/
theorem zero_not_mem_GS [Fact p.Prime] : (0 : Fin n → ZMod p) ∉ GS p n := by
  rintro ⟨i, -, hi⟩
  exact one_ne_zero (hi.symm.trans rfl)

/-- Every vector of `GS(p,n)` is non-zero. -/
theorem ne_zero_of_mem_GS [Fact p.Prime] {x : Fin n → ZMod p} (hx : x ∈ GS p n) : x ≠ 0 := by
  rintro rfl
  exact zero_not_mem_GS hx

/-- If `a` leads strictly before `y`, then `a + y` has the leading data of `a`. -/
theorem IsLead.add_of_lt {a y : Fin n → ZMod p} {i j : Fin n} {c d : ZMod p}
    (ha : IsLead a i c) (hy : IsLead y j d) (hij : i < j) : IsLead (a + y) i c := by
  refine ⟨fun k hk => ?_, ?_, ha.2.2⟩
  · simp [ha.1 k hk, hy.1 k (hk.trans hij)]
  · simp [ha.2.1, hy.1 i hij]

/-- If `a` and `y` lead at the same index and the coefficients do not cancel,
`a + y` leads there with the summed coefficient. -/
theorem IsLead.add_of_eq {a y : Fin n → ZMod p} {i : Fin n} {c d : ZMod p}
    (ha : IsLead a i c) (hy : IsLead y i d) (hcd : c + d ≠ 0) : IsLead (a + y) i (c + d) := by
  refine ⟨fun k hk => ?_, ?_, hcd⟩
  · simp [ha.1 k hk, hy.1 k hk]
  · simp [ha.2.1, hy.2.1]

variable [Fact p.Prime]

/-- `a` leads before `y`: `a + y ∈ GS ↔ a ∈ GS`. -/
theorem add_mem_iff_of_lt {a y : Fin n → ZMod p} {i j : Fin n} {c d : ZMod p}
    (ha : IsLead a i c) (hy : IsLead y j d) (hij : i < j) :
    a + y ∈ GS p n ↔ a ∈ GS p n := by
  rw [mem_GS_iff_of_isLead (ha.add_of_lt hy hij), mem_GS_iff_of_isLead ha]

/-- `y` leads before `a`: `a + y ∈ GS ↔ y ∈ GS`. -/
theorem add_mem_iff_of_gt {a y : Fin n → ZMod p} {i j : Fin n} {c d : ZMod p}
    (ha : IsLead a i c) (hy : IsLead y j d) (hji : j < i) :
    a + y ∈ GS p n ↔ y ∈ GS p n := by
  rw [add_comm]
  exact add_mem_iff_of_lt hy ha hji

/-- Same leading index, non-cancelling coefficients. -/
theorem add_mem_iff_of_eq {a y : Fin n → ZMod p} {i : Fin n} {c d : ZMod p}
    (ha : IsLead a i c) (hy : IsLead y i d) (hcd : c + d ≠ 0) :
    a + y ∈ GS p n ↔ c + d = 1 :=
  mem_GS_iff_of_isLead (ha.add_of_eq hy hcd)

/-- If `a, y ∈ GS` but `a + y ∉ GS`, then `a` and `y` lead at the same index. -/
theorem lead_eq_of_mem_mem {a y : Fin n → ZMod p} {i j : Fin n} {c d : ZMod p}
    (ha : IsLead a i c) (hy : IsLead y j d) (hamem : a ∈ GS p n) (hymem : y ∈ GS p n)
    (hs : a + y ∉ GS p n) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd ((add_mem_iff_of_lt ha hy hlt).2 hamem) hs
  · exact heq
  · exact absurd ((add_mem_iff_of_gt ha hy hgt).2 hymem) hs

/-- If `a, y ∉ GS` but `a + y ∈ GS`, then `a` and `y` lead at the same index. -/
theorem lead_eq_of_not_mem_not_mem {a y : Fin n → ZMod p} {i j : Fin n} {c d : ZMod p}
    (ha : IsLead a i c) (hy : IsLead y j d) (hamem : a ∉ GS p n) (hymem : y ∉ GS p n)
    (hs : a + y ∈ GS p n) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd ((add_mem_iff_of_lt ha hy hlt).1 hs) hamem
  · exact heq
  · exact absurd ((add_mem_iff_of_gt ha hy hgt).1 hs) hymem

end Lead

/-- The eight membership patterns of `{0, a₁, a₂}` are all realised by translates of `A`
(the shattering of `{0, a₁, a₂}`, phrased with arbitrary propositions as targets). -/
def RealizesPatterns {G : Type*} [Add G] (A : Set G) (a₁ a₂ : G) : Prop :=
  ∀ P₀ P₁ P₂ : Prop, ∃ y, (y ∈ A ↔ P₀) ∧ (a₁ + y ∈ A ↔ P₁) ∧ (a₂ + y ∈ A ↔ P₂)

/-- Translation reduction: if translates of `A` shatter `S ∋ s₀, s₁, s₂` (distinct), then
all eight patterns of `{0, s₁ - s₀, s₂ - s₀}` are realised. -/
theorem realizesPatterns_of_translShatters {G : Type*} [AddCommGroup G] {A : Set G}
    {S : Finset G} (hS : TranslShatters A S) {s₀ s₁ s₂ : G} (h₀ : s₀ ∈ S) (h₁ : s₁ ∈ S)
    (h₂ : s₂ ∈ S) (h₀₁ : s₀ ≠ s₁) (h₀₂ : s₀ ≠ s₂) (h₁₂ : s₁ ≠ s₂) :
    RealizesPatterns A (s₁ - s₀) (s₂ - s₀) := by
  classical
  intro P₀ P₁ P₂
  obtain ⟨z, hz⟩ := hS (S.filter fun s => (s = s₀ ∧ P₀) ∨ (s = s₁ ∧ P₁) ∨ (s = s₂ ∧ P₂))
    (Finset.filter_subset _ _)
  refine ⟨s₀ + z, ?_, ?_, ?_⟩
  · rw [hz s₀ h₀]
    simp [h₀, h₀₁, h₀₂]
  · rw [show s₁ - s₀ + (s₀ + z) = s₁ + z by abel, hz s₁ h₁]
    simp [h₁, h₀₁.symm, h₁₂]
  · rw [show s₂ - s₀ + (s₀ + z) = s₂ + z by abel, hz s₂ h₂]
    simp [h₂, h₀₂.symm, h₁₂.symm]

section Core

variable {p n : ℕ} [Fact p.Prime]

/-- Case 1 of Theorem 2.2: two vectors of `GS` cannot both be paired with `0` in a
shattered triple (needs `2 ≠ 0`, i.e. `p` odd). -/
theorem false_of_mem_of_mem (h2 : (2 : ZMod p) ≠ 0) {a₁ a₂ : Fin n → ZMod p}
    (hR : RealizesPatterns (GS p n) a₁ a₂) (h₁ : a₁ ∈ GS p n) (h₂ : a₂ ∈ GS p n) : False := by
  obtain ⟨i₁, hl₁⟩ := exists_isLead (ne_zero_of_mem_GS h₁)
  obtain ⟨i₂, hl₂⟩ := exists_isLead (ne_zero_of_mem_GS h₂)
  have hc₁ : a₁ i₁ = 1 := (mem_GS_iff_of_isLead hl₁).1 h₁
  -- `y ∈ GS`, `a₁ + y ∉ GS`, `a₂ + y ∉ GS`
  obtain ⟨y, hy, hy₁, hy₂⟩ := hR True False False
  have hy : y ∈ GS p n := hy.2 trivial
  obtain ⟨j, hlj⟩ := exists_isLead (ne_zero_of_mem_GS hy)
  have e₁ : i₁ = j := lead_eq_of_mem_mem hl₁ hlj h₁ hy (fun h => hy₁.1 h)
  have e₂ : i₂ = j := lead_eq_of_mem_mem hl₂ hlj h₂ hy (fun h => hy₂.1 h)
  -- `y' ∈ GS`, `a₁ + y' ∈ GS`, `a₂ + y' ∉ GS`
  obtain ⟨y', hy', hy'₁, hy'₂⟩ := hR True True False
  have hy' : y' ∈ GS p n := hy'.2 trivial
  obtain ⟨j', hlj'⟩ := exists_isLead (ne_zero_of_mem_GS hy')
  have hd' : y' j' = 1 := (mem_GS_iff_of_isLead hlj').1 hy'
  have e₂' : i₂ = j' := lead_eq_of_mem_mem hl₂ hlj' h₂ hy' (fun h => hy'₂.1 h)
  have e₁' : i₁ = j' := e₁.trans (e₂.symm.trans e₂')
  subst e₁'
  have hsum : a₁ i₁ + y' i₁ = 2 := by rw [hc₁, hd']; norm_num
  have hmem := (add_mem_iff_of_eq hl₁ hlj' (by rw [hsum]; exact h2)).1 (hy'₁.2 trivial)
  rw [hsum] at hmem
  exact one_ne_zero (by linear_combination hmem)


/-- Leading coefficient `-1` step of Case 2: if `a₁, a₂ ∉ GS` lead at the same index, and
some `y' ∈ GS` has `a₁ + y' ∈ GS`, `a₂ + y' ∉ GS`, then `a₁` has leading coefficient `-1`. -/
theorem lead_coeff_eq_neg_one {a₁ a₂ y' : Fin n → ZMod p} {i : Fin n} {c₁ c₂ : ZMod p}
    (hl₁ : IsLead a₁ i c₁) (hl₂ : IsLead a₂ i c₂) (h₁ : a₁ ∉ GS p n)
    (hy' : y' ∈ GS p n) (hy'₁ : a₁ + y' ∈ GS p n) (hy'₂ : a₂ + y' ∉ GS p n) : c₁ = -1 := by
  obtain ⟨j', hlj'⟩ := exists_isLead (ne_zero_of_mem_GS hy')
  have hd' : y' j' = 1 := (mem_GS_iff_of_isLead hlj').1 hy'
  rw [hd'] at hlj'
  have hj' : i = j' := by
    rcases lt_trichotomy i j' with hlt | heq | hgt
    · exact absurd ((add_mem_iff_of_lt hl₁ hlj' hlt).1 hy'₁) h₁
    · exact heq
    · exact absurd ((add_mem_iff_of_gt hl₂ hlj' hgt).2 hy') hy'₂
  subst hj'
  by_contra hne
  have hcd : c₁ + 1 ≠ 0 := fun h => hne (by linear_combination h)
  have hmem := (add_mem_iff_of_eq hl₁ hlj' hcd).1 hy'₁
  exact hl₁.2.2 (by linear_combination hmem)

/-- Case 2 of Theorem 2.2: two non-zero vectors outside `GS` cannot both be paired with
`0` in a shattered triple. -/
theorem false_of_not_mem_of_not_mem {a₁ a₂ : Fin n → ZMod p}
    (hR : RealizesPatterns (GS p n) a₁ a₂) (hz₁ : a₁ ≠ 0) (hz₂ : a₂ ≠ 0)
    (h₁ : a₁ ∉ GS p n) (h₂ : a₂ ∉ GS p n) : False := by
  obtain ⟨i₁, hl₁⟩ := exists_isLead hz₁
  obtain ⟨i₂, hl₂⟩ := exists_isLead hz₂
  -- `y ∉ GS`, `a₁ + y ∈ GS`, `a₂ + y ∈ GS`
  obtain ⟨y, hy, hy₁, hy₂⟩ := hR False True True
  have hyz : y ≠ 0 := by
    rintro rfl
    exact h₁ (by simpa using hy₁.2 trivial)
  obtain ⟨j, hlj⟩ := exists_isLead hyz
  have e₁ : i₁ = j := lead_eq_of_not_mem_not_mem hl₁ hlj h₁ (fun h => hy.1 h) (hy₁.2 trivial)
  have e₂ : i₂ = j := lead_eq_of_not_mem_not_mem hl₂ hlj h₂ (fun h => hy.1 h) (hy₂.2 trivial)
  have e : i₂ = i₁ := e₂.trans e₁.symm
  rw [e] at hl₂
  -- leading coefficients are both `-1`
  obtain ⟨y', hy', hy'₁, hy'₂⟩ := hR True True False
  have hc₁ : a₁ i₁ = -1 := lead_coeff_eq_neg_one hl₁ hl₂ h₁ (hy'.2 trivial) (hy'₁.2 trivial)
    (fun h => hy'₂.1 h)
  obtain ⟨y'', hy'', hy''₁, hy''₂⟩ := hR True False True
  have hc₂ : a₂ i₁ = -1 := lead_coeff_eq_neg_one hl₂ hl₁ h₂ (hy''.2 trivial)
    (hy''₂.2 trivial) (fun h => hy''₁.1 h)
  rw [hc₁] at hl₁
  rw [hc₂] at hl₂
  -- `y₃ ∉ GS`, `a₁ + y₃ ∉ GS`, `a₂ + y₃ ∈ GS`
  obtain ⟨y₃, hy₃, hy₃₁, hy₃₂⟩ := hR False False True
  have hy₃z : y₃ ≠ 0 := by
    rintro rfl
    exact h₂ (by simpa using hy₃₂.2 trivial)
  obtain ⟨j₃, hlj₃⟩ := exists_isLead hy₃z
  have e₃ : i₁ = j₃ :=
    lead_eq_of_not_mem_not_mem hl₂ hlj₃ h₂ (fun h => hy₃.1 h) (hy₃₂.2 trivial)
  subst e₃
  by_cases hcd : -1 + y₃ i₁ = 0
  · have hd : y₃ i₁ = 1 := by linear_combination hcd
    rw [hd] at hlj₃
    exact hy₃.1 ((mem_GS_iff_of_isLead hlj₃).2 rfl)
  · have hm₂ := (add_mem_iff_of_eq hl₂ hlj₃ hcd).1 (hy₃₂.2 trivial)
    exact hy₃₁.1 ((add_mem_iff_of_eq hl₁ hlj₃ hcd).2 hm₂)


/-- The extra case in the proof of Theorem 1.2 (`p ≥ 5`): a vector of `GS` and a non-zero
vector outside `GS` cannot be paired with `0` in a shattered triple. -/
theorem false_of_mem_of_not_mem (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0)
    {a₁ a₂ : Fin n → ZMod p} (hR : RealizesPatterns (GS p n) a₁ a₂)
    (h₁ : a₁ ∈ GS p n) (hz₂ : a₂ ≠ 0) (h₂ : a₂ ∉ GS p n) : False := by
  obtain ⟨i₁, hl₁⟩ := exists_isLead (ne_zero_of_mem_GS h₁)
  obtain ⟨i₂, hl₂⟩ := exists_isLead hz₂
  have hc₁ : a₁ i₁ = 1 := (mem_GS_iff_of_isLead hl₁).1 h₁
  rw [hc₁] at hl₁
  -- `y ∉ GS`, `a₁ + y ∉ GS`, `a₂ + y ∈ GS`: forces `i₂ ≤ i₁`
  obtain ⟨y, hy, hy₁, hy₂⟩ := hR False False True
  have hyz : y ≠ 0 := by
    rintro rfl
    exact h₂ (by simpa using hy₂.2 trivial)
  obtain ⟨j, hlj⟩ := exists_isLead hyz
  have e₂ : i₂ = j := lead_eq_of_not_mem_not_mem hl₂ hlj h₂ (fun h => hy.1 h) (hy₂.2 trivial)
  have hle₂₁ : i₂ ≤ i₁ := by
    rw [e₂]
    by_contra hlt
    exact hy₁.1 ((add_mem_iff_of_lt hl₁ hlj (not_le.1 hlt)).2 h₁)
  -- `y' ∈ GS`, `a₁ + y' ∉ GS`, `a₂ + y' ∈ GS`: forces `i₁ ≤ i₂`
  obtain ⟨y', hy', hy'₁, hy'₂⟩ := hR True False True
  have hy'm : y' ∈ GS p n := hy'.2 trivial
  obtain ⟨j', hlj'⟩ := exists_isLead (ne_zero_of_mem_GS hy'm)
  have hd' : y' j' = 1 := (mem_GS_iff_of_isLead hlj').1 hy'm
  rw [hd'] at hlj'
  have e₁ : i₁ = j' := lead_eq_of_mem_mem hl₁ hlj' h₁ hy'm (fun h => hy'₁.1 h)
  have hle₁₂ : i₁ ≤ i₂ := by
    rw [e₁]
    by_contra hlt
    exact h₂ ((add_mem_iff_of_lt hl₂ hlj' (not_le.1 hlt)).1 (hy'₂.2 trivial))
  have e : i₂ = i₁ := le_antisymm hle₂₁ hle₁₂
  subst e₁ e
  -- the leading coefficient of `a₂` is `-1`
  have hc₂ : a₂ i₂ = -1 := by
    by_contra hne
    have hcd : a₂ i₂ + 1 ≠ 0 := fun h => hne (by linear_combination h)
    have hm := (add_mem_iff_of_eq hl₂ hlj' hcd).1 (hy'₂.2 trivial)
    exact hl₂.2.2 (by linear_combination hm)
  rw [hc₂] at hl₂
  -- `y'' ∉ GS`, `a₁ + y'' ∈ GS`, `a₂ + y'' ∈ GS`: impossible when `p ≥ 5`
  obtain ⟨y'', hy'', hy''₁, hy''₂⟩ := hR False True True
  have hy''z : y'' ≠ 0 := by
    rintro rfl
    exact h₂ (by simpa using hy''₂.2 trivial)
  obtain ⟨j'', hlj''⟩ := exists_isLead hy''z
  have e'' : i₂ = j'' :=
    lead_eq_of_not_mem_not_mem hl₂ hlj'' h₂ (fun h => hy''.1 h) (hy''₂.2 trivial)
  subst e''
  by_cases hcd : 1 + y'' i₂ = 0
  · have hcd₂ : -1 + y'' i₂ ≠ 0 := fun h => h2 (by linear_combination hcd - h)
    have hm := (add_mem_iff_of_eq hl₂ hlj'' hcd₂).1 (hy''₂.2 trivial)
    exact h3 (by linear_combination hcd - hm)
  · have hm := (add_mem_iff_of_eq hl₁ hlj'' hcd).1 (hy''₁.2 trivial)
    exact hlj''.2.2 (by linear_combination hm)

end Core

section Main

variable {p n : ℕ} [hp : Fact p.Prime]

include hp in
/-- For an odd prime `p`, `2 ≠ 0` in `ZMod p`. -/
theorem two_ne_zero_of_two_lt (h : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h0)
  have := Nat.le_of_dvd two_pos hdvd
  omega

include hp in
/-- For a prime `p ≥ 5`, `3 ≠ 0` in `ZMod p`. -/
theorem three_ne_zero_of_five_le (h : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h0)
  have := Nat.le_of_dvd three_pos hdvd
  omega

/-- In a set shattered by translates of `GS(p,n)` (`p` odd), the differences `s₁ - s₀` and
`s₂ - s₀` of three distinct elements lie on opposite sides of `GS(p,n)`. -/
theorem not_iff_of_translShatters (h : 2 < p) {S : Finset (Fin n → ZMod p)}
    (hS : TranslShatters (GS p n) S) {s₀ s₁ s₂ : Fin n → ZMod p} (h₀ : s₀ ∈ S) (h₁ : s₁ ∈ S)
    (h₂ : s₂ ∈ S) (h₀₁ : s₀ ≠ s₁) (h₀₂ : s₀ ≠ s₂) (h₁₂ : s₁ ≠ s₂) :
    ¬ (s₁ - s₀ ∈ GS p n ↔ s₂ - s₀ ∈ GS p n) := by
  intro hiff
  have hR := realizesPatterns_of_translShatters hS h₀ h₁ h₂ h₀₁ h₀₂ h₁₂
  have hz₁ : s₁ - s₀ ≠ 0 := sub_ne_zero.2 h₀₁.symm
  have hz₂ : s₂ - s₀ ≠ 0 := sub_ne_zero.2 h₀₂.symm
  by_cases hm : s₁ - s₀ ∈ GS p n
  · exact false_of_mem_of_mem (two_ne_zero_of_two_lt h) hR hm (hiff.1 hm)
  · exact false_of_not_mem_of_not_mem hR hz₁ hz₂ hm (fun h' => hm (hiff.2 h'))

/-- **Theorem 2.2** of arXiv:2411.05612 (Terry-Wolf, Corollary A.10): for every prime
`p > 2` and every `n`, if translates of `GS(p,n)` shatter a finite set `S ⊆ 𝔽_p^n`, then
`|S| ≤ 3`; i.e. `GS(p,n)` has VC-dimension at most `3`. -/
theorem card_le_three_of_translShatters (h : 2 < p) {S : Finset (Fin n → ZMod p)}
    (hS : TranslShatters (GS p n) S) : S.card ≤ 3 := by
  by_contra! hlt
  obtain ⟨s₀, h₀⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hcard : 2 < (S.erase s₀).card := by
    rw [Finset.card_erase_of_mem h₀]
    omega
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, h₁₂, h₁₃, h₂₃⟩ := Finset.two_lt_card.1 hcard
  rw [Finset.mem_erase] at h₁ h₂ h₃
  have n₁₂ := not_iff_of_translShatters h hS h₀ h₁.2 h₂.2 h₁.1.symm h₂.1.symm h₁₂
  have n₁₃ := not_iff_of_translShatters h hS h₀ h₁.2 h₃.2 h₁.1.symm h₃.1.symm h₁₃
  have n₂₃ := not_iff_of_translShatters h hS h₀ h₂.2 h₃.2 h₂.1.symm h₃.1.symm h₂₃
  tauto

/-- Upper bound in **Theorem 1.2** of arXiv:2411.05612: for every prime `p ≥ 5` and every
`n`, if translates of `GS(p,n)` shatter a finite set `S`, then `|S| ≤ 2`. -/
theorem card_le_two_of_translShatters (h : 5 ≤ p) {S : Finset (Fin n → ZMod p)}
    (hS : TranslShatters (GS p n) S) : S.card ≤ 2 := by
  by_contra! hlt
  obtain ⟨s₀, h₀, s₁, h₁, s₂, h₂, h₀₁, h₀₂, h₁₂⟩ := Finset.two_lt_card.1 hlt
  have h2 := two_ne_zero_of_two_lt (p := p) (by omega)
  have h3 := three_ne_zero_of_five_le (p := p) h
  have hz₁ : s₁ - s₀ ≠ 0 := sub_ne_zero.2 h₀₁.symm
  have hz₂ : s₂ - s₀ ≠ 0 := sub_ne_zero.2 h₀₂.symm
  have hn := not_iff_of_translShatters (by omega) hS h₀ h₁ h₂ h₀₁ h₀₂ h₁₂
  by_cases hm : s₁ - s₀ ∈ GS p n
  · have hR := realizesPatterns_of_translShatters hS h₀ h₁ h₂ h₀₁ h₀₂ h₁₂
    exact false_of_mem_of_not_mem h2 h3 hR hm hz₂ (fun h' => hn ⟨fun _ => h', fun _ => hm⟩)
  · have hR := realizesPatterns_of_translShatters hS h₀ h₂ h₁ h₀₂ h₀₁ h₁₂.symm
    have hm₂ : s₂ - s₀ ∈ GS p n := by tauto
    exact false_of_mem_of_not_mem h2 h3 hR hm₂ hz₁ hm

end Main

section Witness

variable {p n : ℕ}

/-- A standard basis vector scaled by `c ≠ 0` leads at its own index. -/
theorem isLead_single {i : Fin n} {c : ZMod p} (hc : c ≠ 0) :
    IsLead (Pi.single i c : Fin n → ZMod p) i c :=
  ⟨fun _ hj => Pi.single_eq_of_ne hj.ne _, Pi.single_eq_same _ _, hc⟩

/-- Negation negates the leading coefficient. -/
theorem IsLead.neg {x : Fin n → ZMod p} {i : Fin n} {c : ZMod p} (h : IsLead x i c) :
    IsLead (-x) i (-c) :=
  ⟨fun j hj => by simp [h.1 j hj], by simp [h.2.1], neg_ne_zero.2 h.2.2⟩

variable [Fact p.Prime]

/-- Lower bound in **Theorem 1.2** of arXiv:2411.05612: for an odd prime `p` and `n ≥ 2`,
translates of `GS(p,n)` shatter `{0, w₂}` (`w₂` the second standard basis vector), using the
translates `y ∈ {0, w₁, -w₁, w₂}`. -/
theorem translShatters_pair (h : 2 < p) (hn : 2 ≤ n) :
    TranslShatters (GS p n) {0, Pi.single (⟨1, by omega⟩ : Fin n) 1} := by
  have h2 := two_ne_zero_of_two_lt (p := p) h
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ < i₁ := by simp [hi₀, hi₁, Fin.lt_def]
  set w : Fin n → ZMod p := Pi.single i₀ 1 with hw
  set e : Fin n → ZMod p := Pi.single i₁ 1 with he
  have lw : IsLead w i₀ 1 := isLead_single one_ne_zero
  have le : IsLead e i₁ 1 := isLead_single one_ne_zero
  have hne : (-1 : ZMod p) ≠ 1 := fun h' => h2 (by linear_combination -h')
  have m_w : w ∈ GS p n := (mem_GS_iff_of_isLead lw).2 rfl
  have m_e : e ∈ GS p n := (mem_GS_iff_of_isLead le).2 rfl
  have m_ew : e + w ∈ GS p n := by
    rw [add_comm]
    exact (mem_GS_iff_of_isLead (lw.add_of_lt le h01)).2 rfl
  have m_ee : e + e ∉ GS p n := by
    rw [mem_GS_iff_of_isLead (le.add_of_eq le (by rw [one_add_one_eq_two]; exact h2))]
    intro h'
    exact one_ne_zero (by linear_combination h')
  have m_nw : -w ∉ GS p n := by
    rw [mem_GS_iff_of_isLead lw.neg]
    exact hne
  have m_enw : e + -w ∉ GS p n := by
    rw [add_comm, mem_GS_iff_of_isLead (lw.neg.add_of_lt le h01)]
    exact hne
  intro T hT
  by_cases h0 : (0 : Fin n → ZMod p) ∈ T <;> by_cases hT₁ : e ∈ T
  · refine ⟨w, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, zero_add]
    exact ⟨iff_of_true m_w h0, iff_of_true m_ew hT₁⟩
  · refine ⟨e, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, zero_add]
    exact ⟨iff_of_true m_e h0, iff_of_false m_ee hT₁⟩
  · refine ⟨0, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, add_zero]
    exact ⟨iff_of_false zero_not_mem_GS h0, iff_of_true m_e hT₁⟩
  · refine ⟨-w, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, zero_add]
    exact ⟨iff_of_false m_nw h0, iff_of_false m_enw hT₁⟩

/-- Lower bound in Section 2 of arXiv:2411.05612 for `p = 3`: for `n ≥ 3`, translates of
`GS(3,n)` shatter the three-element set `{0, w₂, -w₂}` (`w₂` the second standard basis vector),
so `GS(3,n)` has VC-dimension exactly `3` (with Theorem 2.2). -/
theorem translShatters_triple_three (hn : 3 ≤ n) :
    TranslShatters (GS 3 n)
      {0, Pi.single (⟨1, by omega⟩ : Fin n) 1, -Pi.single (⟨1, by omega⟩ : Fin n) 1} := by
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin n := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ < i₁ := by simp [hi₀, hi₁, Fin.lt_def]
  have h12 : i₁ < i₂ := by simp [hi₁, hi₂, Fin.lt_def]
  set w : Fin n → ZMod 3 := Pi.single i₀ 1 with hw
  set e : Fin n → ZMod 3 := Pi.single i₁ 1 with he
  set u : Fin n → ZMod 3 := Pi.single i₂ 1 with hu
  have lw : IsLead w i₀ 1 := isLead_single one_ne_zero
  have le : IsLead e i₁ 1 := isLead_single one_ne_zero
  have lu : IsLead u i₂ 1 := isLead_single one_ne_zero
  have lne : IsLead (-e) i₁ (-1) := le.neg
  have lee : IsLead (e + e) i₁ (1 + 1) := le.add_of_eq le (by decide)
  have lnene : IsLead (-e + -e) i₁ (-1 + -1) := lne.add_of_eq lne (by decide)
  -- membership facts
  have m_w : w ∈ GS 3 n := (mem_GS_iff_of_isLead lw).2 rfl
  have m_nw : -w ∉ GS 3 n := by rw [mem_GS_iff_of_isLead lw.neg]; decide
  have m_e : e ∈ GS 3 n := (mem_GS_iff_of_isLead le).2 rfl
  have m_ne : -e ∉ GS 3 n := by rw [mem_GS_iff_of_isLead lne]; decide
  have m_u : u ∈ GS 3 n := (mem_GS_iff_of_isLead lu).2 rfl
  have m_ee : e + e ∉ GS 3 n := by rw [mem_GS_iff_of_isLead lee]; decide
  have m_nene : -e + -e ∈ GS 3 n := by rw [mem_GS_iff_of_isLead lnene]; decide
  have m_eu : e + u ∈ GS 3 n := (mem_GS_iff_of_isLead (le.add_of_lt lu h12)).2 rfl
  have m_neu : -e + u ∉ GS 3 n := by
    rw [mem_GS_iff_of_isLead (lne.add_of_lt lu h12)]; decide
  have m_eeu : e + e + u ∉ GS 3 n := by
    rw [mem_GS_iff_of_isLead (lee.add_of_lt lu h12)]; decide
  have m_neneu : -e + -e + u ∈ GS 3 n := by
    rw [mem_GS_iff_of_isLead (lnene.add_of_lt lu h12)]; decide
  have m_xw : ∀ x : Fin n → ZMod 3, (x = e ∨ x = -e) → x + w ∈ GS 3 n := by
    rintro x (rfl | rfl)
    · rw [add_comm]; exact (mem_GS_iff_of_isLead (lw.add_of_lt le h01)).2 rfl
    · rw [add_comm]; exact (mem_GS_iff_of_isLead (lw.add_of_lt lne h01)).2 rfl
  have m_xnw : ∀ x : Fin n → ZMod 3, (x = e ∨ x = -e) → x + -w ∉ GS 3 n := by
    rintro x (rfl | rfl)
    · rw [add_comm, mem_GS_iff_of_isLead (lw.neg.add_of_lt le h01)]; decide
    · rw [add_comm, mem_GS_iff_of_isLead (lw.neg.add_of_lt lne h01)]; decide
  intro T hT
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, zero_add]
  by_cases h0 : (0 : Fin n → ZMod 3) ∈ T <;> by_cases hT₁ : e ∈ T <;> by_cases hT₂ : -e ∈ T
  · exact ⟨w, iff_of_true m_w h0, iff_of_true (m_xw e (Or.inl rfl)) hT₁,
      iff_of_true (m_xw (-e) (Or.inr rfl)) hT₂⟩
  · exact ⟨u, iff_of_true m_u h0, iff_of_true m_eu hT₁, iff_of_false m_neu hT₂⟩
  · refine ⟨e + u, iff_of_true m_eu h0, iff_of_false ?_ hT₁, iff_of_true ?_ hT₂⟩
    · rwa [← add_assoc]
    · rwa [← add_assoc, neg_add_cancel, zero_add]
  · refine ⟨e, iff_of_true m_e h0, iff_of_false m_ee hT₁, iff_of_false ?_ hT₂⟩
    rw [neg_add_cancel]; exact zero_not_mem_GS
  · refine ⟨-e + u, iff_of_false m_neu h0, iff_of_true ?_ hT₁, iff_of_true ?_ hT₂⟩
    · rwa [← add_assoc, add_neg_cancel, zero_add]
    · rwa [← add_assoc]
  · exact ⟨0, iff_of_false zero_not_mem_GS h0, iff_of_true (by rwa [add_zero]) hT₁,
      iff_of_false (by rwa [add_zero]) hT₂⟩
  · refine ⟨-e, iff_of_false m_ne h0, iff_of_false ?_ hT₁, iff_of_true m_nene hT₂⟩
    rw [add_neg_cancel]; exact zero_not_mem_GS
  · exact ⟨-w, iff_of_false m_nw h0, iff_of_false (m_xnw e (Or.inl rfl)) hT₁,
      iff_of_false (m_xnw (-e) (Or.inr rfl)) hT₂⟩

end Witness

section VCDim

/-- The family `{A - y : y ∈ G}` of all translates of `A ⊆ G`, as a finset of finsets of the
finite group `G` (the family of Definition 2.1 attached to `A` in arXiv:2411.05612). -/
noncomputable def translates {G : Type*} [AddCommGroup G] [Fintype G] (A : Set G) :
    Finset (Finset G) := by
  classical
  exact Finset.univ.image fun y => Finset.univ.filter fun x => x + y ∈ A

/-- Membership in the family of translates: `u = A - y` for some `y`. -/
theorem mem_translates {G : Type*} [AddCommGroup G] [Fintype G] (A : Set G) (u : Finset G) :
    u ∈ translates A ↔ ∃ y, ∀ x, x ∈ u ↔ x + y ∈ A := by
  classical
  unfold translates
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, fun x => by simp⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by ext x; simp [hy]⟩

/-- `TranslShatters` agrees with Mathlib's `Finset.Shatters` for the family of translates. -/
theorem translShatters_iff_shatters {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Set G) (S : Finset G) : TranslShatters A S ↔ (translates A).Shatters S := by
  constructor
  · intro hS T hT
    obtain ⟨y, hy⟩ := hS T hT
    classical
    refine ⟨Finset.univ.filter fun x => x + y ∈ A, (mem_translates A _).2 ⟨y, fun x => ?_⟩, ?_⟩
    · simp
    · ext x
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hx, hxy⟩
        exact (hy x hx).1 hxy
      · intro hx
        exact ⟨hT hx, (hy x (hT hx)).2 hx⟩
  · intro hS T hT
    obtain ⟨u, hu, hSu⟩ := hS hT
    obtain ⟨y, hy⟩ := (mem_translates A u).1 hu
    refine ⟨y, fun s hs => ?_⟩
    rw [← hSu, Finset.mem_inter, hy]
    exact ⟨fun h => ⟨hs, h⟩, And.right⟩

variable {p n : ℕ} [Fact p.Prime]

/-- Boundary case `n = 1` (why Theorem 1.2 needs `n ≥ 2`): `GS(p,1) = {1}`, and its translates
shatter no two-element set, so its VC-dimension is at most `1`. -/
theorem card_le_one_of_translShatters_one {S : Finset (Fin 1 → ZMod p)}
    (hS : TranslShatters (GS p 1) S) : S.card ≤ 1 := by
  by_contra! hlt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hlt
  obtain ⟨y, hy⟩ := hS S subset_rfl
  have key : ∀ x : Fin 1 → ZMod p, x ∈ GS p 1 → x 0 = 1 := by
    rintro x ⟨i, -, hi⟩
    rwa [Subsingleton.elim i 0] at hi
  have ha' := key _ ((hy a ha).2 ha)
  have hb' := key _ ((hy b hb).2 hb)
  apply hab
  funext i
  rw [Subsingleton.elim i 0]
  simp only [Pi.add_apply] at ha' hb'
  linear_combination ha' - hb'

/-- **Theorem 2.2** of arXiv:2411.05612, stated with Mathlib's `Finset.vcDim`: for every
prime `p > 2` and every `n`, the family of translates of `GS(p,n)` has VC-dimension `≤ 3`. -/
theorem vcDim_translates_GS_le_three (h : 2 < p) : (translates (GS p n)).vcDim ≤ 3 :=
  Finset.sup_le fun S hS =>
    card_le_three_of_translShatters h
      ((translShatters_iff_shatters _ S).2 (Finset.mem_shatterer.1 hS))

/-- **Theorem 1.2** of arXiv:2411.05612, with the hypothesis `n ≥ 2` that the printed
statement omits (for `n = 1` the VC-dimension is at most `1`): for every prime `p ≥ 5` and `n ≥ 2`,
the family of translates of `GS(p,n)` has VC-dimension exactly `2`. -/
theorem vcDim_translates_GS_eq_two (h : 5 ≤ p) (hn : 2 ≤ n) :
    (translates (GS p n)).vcDim = 2 := by
  apply le_antisymm
  · exact Finset.sup_le fun S hS =>
      card_le_two_of_translShatters h
        ((translShatters_iff_shatters _ S).2 (Finset.mem_shatterer.1 hS))
  · have hsh := (translShatters_iff_shatters _ _).1 (translShatters_pair (p := p) (by omega) hn)
    refine le_of_eq_of_le ?_ hsh.card_le_vcDim
    rw [Finset.card_pair]
    intro h0
    have h₁ := congrFun h0 ⟨1, by omega⟩
    simp at h₁

/-- `GS(3,n)` has VC-dimension exactly `3` for `n ≥ 3` (Section 2 of arXiv:2411.05612,
lower bound from Terry-Wolf, upper bound Theorem 2.2). -/
theorem vcDim_translates_GS_three_eq_three (hn : 3 ≤ n) :
    (translates (GS 3 n)).vcDim = 3 := by
  apply le_antisymm (vcDim_translates_GS_le_three (by norm_num))
  have hsh := (translShatters_iff_shatters _ _).1 (translShatters_triple_three hn)
  refine le_of_eq_of_le ?_ hsh.card_le_vcDim
  set e : Fin n → ZMod 3 := Pi.single ⟨1, by omega⟩ 1 with he
  have h1 : e ⟨1, by omega⟩ = 1 := by simp [he]
  refine (Finset.card_eq_three.2 ⟨0, e, -e, fun h' => ?_, fun h' => ?_, fun h' => ?_, rfl⟩).symm
  · have h₀ := congrFun h' ⟨1, by omega⟩
    rw [Pi.zero_apply, h1] at h₀
    exact absurd h₀ (by decide)
  · have h₀ := congrFun h' ⟨1, by omega⟩
    rw [Pi.zero_apply, Pi.neg_apply, h1] at h₀
    exact absurd h₀ (by decide)
  · have h₀ := congrFun h' ⟨1, by omega⟩
    rw [Pi.neg_apply, h1] at h₀
    exact absurd h₀ (by decide)

/-- `GS(p,1)` has VC-dimension at most `1`, so Theorem 1.2 of arXiv:2411.05612 fails as
printed at `n = 1`. -/
theorem vcDim_translates_GS_one_le_one : (translates (GS p 1)).vcDim ≤ 1 :=
  Finset.sup_le fun S hS =>
    card_le_one_of_translShatters_one
      ((translShatters_iff_shatters _ S).2 (Finset.mem_shatterer.1 hS))

/-- Paper alias: **Theorem 2.2** of arXiv:2411.05612 (VC-dimension of `GS(p,n)` at most `3`
for every prime `p > 2` and every `n`). -/
theorem thm_2_2 (h : 2 < p) : (translates (GS p n)).vcDim ≤ 3 :=
  vcDim_translates_GS_le_three h

/-- Paper alias: **Theorem 1.2** of arXiv:2411.05612, corrected to `n ≥ 2` (VC-dimension of
`GS(p,n)` equal to `2` for every prime `p ≥ 5`). -/
theorem thm_1_2 (h : 5 ≤ p) (hn : 2 ≤ n) : (translates (GS p n)).vcDim = 2 :=
  vcDim_translates_GS_eq_two h hn

end VCDim

end VcDimensionLinearGreenSanders
