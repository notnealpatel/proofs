import Mathlib
import Xlib.TPP

/-!
# The subset triple-product-property ratio of dihedral groups is at most 4/3

For finite subsets `S T U` of the dihedral group `D_{2n}` satisfying the
triple product property (TPP, right-quotient convention `Q(X) = X * X⁻¹`),

    3 * (|S| * |T| * |U|) ≤ 8 * n,

i.e. `ρ(D_{2n}) ≤ 4/3`.  This is the dihedral case of Hedtke–Murthy
(Groups Complexity Cryptology 4 (2012), Conjectures 7.5/7.6, subset
version) and the `p = 2` dihedral case of Murthy (arXiv:2512.16730,
Conjecture 5.1); the subgroup version is Murthy's Theorem 4.1.  The bound
is sharp: for `3 ∣ n` the triple `(⟨r³, f⟩, ⟨fr⟩, ⟨fr²⟩)` attains it.

## Proof idea

Write elements of `DihedralGroup n` as rotations `r i` and reflections
`sr i` and split each of `S, T, U` into its rotation part (`rotPart`) and
reflection part (`refPart`), subsets of `ZMod n`.  The quotient set
`X * X⁻¹` has rotation exponents `(A - A) ∪ (B - B)` and reflection
exponents `B - A`, where `A = rotPart X`, `B = refPart X`.  For a *type
vector* `τ ∈ {0,1}³` the *type product* is `P_τ = c₁ * c₂ * c₃` where
`c_i = |A_i|` or `|B_i|` according to `τ_i`; then
`|S| * |T| * |U| = Σ_τ P_τ`.

**Key lemma.** For any three distinct type vectors of equal parity,
`P_τ + P_τ' + P_τ'' ≤ n`.  Indeed there is a single linear form
`x₁ ± x₂ ± x₃` (signs depending only on the triple) which is injective
on each of the three type products and whose three images are pairwise
disjoint in `ZMod n`: any coincidence produces `q₁ ∈ Q(S)`, `q₂ ∈ Q(T)`,
`q₃ ∈ Q(U)` with `q₁ * q₂ * q₃ = 1` and at least one `q_i` a reflection
(hence `≠ 1`), contradicting the TPP.

Each parity class has four type products, and summing its four 3-subset
inequalities gives `3 * (class sum) ≤ 4n`; adding the two classes yields
the theorem.

Everything is elementary.  The argument uses only that the index-2
subgroup is abelian and inverted by reflections, so it applies verbatim
to any generalized dihedral group.
-/

open Finset
open scoped Pointwise

namespace DihedralTPP

/-- The triple product property for finset triples in a group, in the
right-quotient convention of Neumann and Hedtke–Murthy: whenever
`q₁ ∈ S * S⁻¹`, `q₂ ∈ T * T⁻¹`, `q₃ ∈ U * U⁻¹` multiply to `1`, all
three are `1`. -/
def IsTPP {G : Type*} [Group G] [DecidableEq G] (S T U : Finset G) : Prop :=
  ∀ q₁ ∈ S * S⁻¹, ∀ q₂ ∈ T * T⁻¹, ∀ q₃ ∈ U * U⁻¹,
    q₁ * q₂ * q₃ = 1 → q₁ = 1 ∧ q₂ = 1 ∧ q₃ = 1

variable {n : ℕ} [NeZero n]

/-- Exponents of the rotations belonging to `X`. -/
def rotPart (X : Finset (DihedralGroup n)) : Finset (ZMod n) :=
  univ.filter fun i => DihedralGroup.r i ∈ X

/-- Exponents of the reflections belonging to `X`. -/
def refPart (X : Finset (DihedralGroup n)) : Finset (ZMod n) :=
  univ.filter fun i => DihedralGroup.sr i ∈ X

@[simp] lemma mem_rotPart {X : Finset (DihedralGroup n)} {i : ZMod n} :
    i ∈ rotPart X ↔ DihedralGroup.r i ∈ X := by simp [rotPart]

@[simp] lemma mem_refPart {X : Finset (DihedralGroup n)} {i : ZMod n} :
    i ∈ refPart X ↔ DihedralGroup.sr i ∈ X := by simp [refPart]

section QuotientMembership

variable {X : Finset (DihedralGroup n)} {x y : ZMod n}

private lemma mul_inv_mem {G : Type*} [Group G] [DecidableEq G] {X : Finset G} {a b : G}
    (ha : a ∈ X) (hb : b ∈ X) : a * b⁻¹ ∈ X * X⁻¹ :=
  Finset.mul_mem_mul ha (Finset.inv_mem_inv hb)

/-- Differences of rotation exponents give rotations in the quotient set. -/
lemma r_sub_mem_rot (hx : x ∈ rotPart X) (hy : y ∈ rotPart X) :
    DihedralGroup.r (x - y) ∈ X * X⁻¹ := by
  have h := mul_inv_mem (mem_rotPart.mp hx) (mem_rotPart.mp hy)
  simpa [DihedralGroup.inv_r, DihedralGroup.r_mul_r, sub_eq_add_neg] using h

/-- Differences of reflection exponents give rotations in the quotient set:
`sr y * (sr x)⁻¹ = sr y * sr x = r (x - y)`. -/
lemma r_sub_mem_ref (hx : x ∈ refPart X) (hy : y ∈ refPart X) :
    DihedralGroup.r (x - y) ∈ X * X⁻¹ := by
  have h := mul_inv_mem (mem_refPart.mp hy) (mem_refPart.mp hx)
  simpa [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr] using h

/-- Same-part differences give rotations in the quotient set (uniform form). -/
lemma r_sub_mem_samePart {C : Finset (ZMod n)}
    (hC : C = rotPart X ∨ C = refPart X) (hx : x ∈ C) (hy : y ∈ C) :
    DihedralGroup.r (x - y) ∈ X * X⁻¹ := by
  rcases hC with rfl | rfl
  · exact r_sub_mem_rot hx hy
  · exact r_sub_mem_ref hx hy

/-- Mixed pairs give reflections in the quotient set:
`r x * (sr y)⁻¹ = r x * sr y = sr (y - x)`. -/
lemma sr_mem_mixed (hx : x ∈ rotPart X) (hy : y ∈ refPart X) :
    DihedralGroup.sr (y - x) ∈ X * X⁻¹ := by
  have h := mul_inv_mem (mem_rotPart.mp hx) (mem_refPart.mp hy)
  simpa [DihedralGroup.inv_sr, DihedralGroup.r_mul_sr] using h

end QuotientMembership

omit [NeZero n] in
/-- Reflections are never the identity. -/
lemma sr_ne_one (e : ZMod n) : DihedralGroup.sr e ≠ 1 := by
  rw [DihedralGroup.one_def]
  exact fun hcon => by injection hcon

/-- A finset of `DihedralGroup n` splits into its rotation and reflection
parts. -/
lemma card_eq_parts (X : Finset (DihedralGroup n)) :
    X.card = (rotPart X).card + (refPart X).card := by
  have himg : X = (rotPart X).image DihedralGroup.r ∪ (refPart X).image DihedralGroup.sr := by
    ext g
    cases g with
    | r i => simp
    | sr i => simp
  have hdisj : Disjoint ((rotPart X).image DihedralGroup.r)
      ((refPart X).image DihedralGroup.sr) := by
    rw [Finset.disjoint_left]
    rintro g hg₁ hg₂
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg₁
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hg₂
    exact absurd hj (by simp)
  have hinjr : Function.Injective (DihedralGroup.r (n := n)) := fun a b hab => by
    injection hab
  have hinjsr : Function.Injective (DihedralGroup.sr (n := n)) := fun a b hab => by
    injection hab
  calc X.card
      = ((rotPart X).image DihedralGroup.r ∪ (refPart X).image DihedralGroup.sr).card := by
        rw [← himg]
    _ = (rotPart X).card + (refPart X).card := by
        rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ hinjr, Finset.card_image_of_injective _ hinjsr]

/-! ## The signed linear forms -/

/-- The linear form `x₁ + ε₂·x₂ + ε₃·x₃` on triples. -/
def form (ε₂ ε₃ : ZMod n) (p : ZMod n × ZMod n × ZMod n) : ZMod n :=
  p.1 + ε₂ * p.2.1 + ε₃ * p.2.2

section Kernels

variable {S T U : Finset (DihedralGroup n)}

/-- **Injectivity kernel.** Any signed form is injective on any type
product. -/
lemma injOn_form (h : IsTPP S T U)
    {C₁ C₂ C₃ : Finset (ZMod n)}
    (hC₁ : C₁ = rotPart S ∨ C₁ = refPart S)
    (hC₂ : C₂ = rotPart T ∨ C₂ = refPart T)
    (hC₃ : C₃ = rotPart U ∨ C₃ = refPart U)
    {ε₂ ε₃ : ZMod n} (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1) :
    Set.InjOn (form ε₂ ε₃) ↑(C₁ ×ˢ C₂ ×ˢ C₃) := by
  rintro ⟨x₁, x₂, x₃⟩ hx ⟨y₁, y₂, y₃⟩ hy hxy
  simp only [Finset.mem_coe, Finset.mem_product] at hx hy
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy
  have hxy' : x₁ + ε₂ * x₂ + ε₃ * x₃ = y₁ + ε₂ * y₂ + ε₃ * y₃ := by
    simpa [form] using hxy
  have hq₁ : DihedralGroup.r (x₁ - y₁) ∈ S * S⁻¹ := r_sub_mem_samePart hC₁ hx₁ hy₁
  have hq₂ : DihedralGroup.r (ε₂ * (x₂ - y₂)) ∈ T * T⁻¹ := by
    rcases hε₂ with rfl | rfl
    · simpa using r_sub_mem_samePart hC₂ hx₂ hy₂
    · have h' := r_sub_mem_samePart hC₂ hy₂ hx₂
      have hy' : (-1 : ZMod n) * (x₂ - y₂) = y₂ - x₂ := by ring
      rwa [hy']
  have hq₃ : DihedralGroup.r (ε₃ * (x₃ - y₃)) ∈ U * U⁻¹ := by
    rcases hε₃ with rfl | rfl
    · simpa using r_sub_mem_samePart hC₃ hx₃ hy₃
    · have h' := r_sub_mem_samePart hC₃ hy₃ hx₃
      have hy' : (-1 : ZMod n) * (x₃ - y₃) = y₃ - x₃ := by ring
      rwa [hy']
  have hsum : x₁ - y₁ + ε₂ * (x₂ - y₂) + ε₃ * (x₃ - y₃) = 0 := by
    linear_combination hxy'
  have hone : DihedralGroup.r (x₁ - y₁) * DihedralGroup.r (ε₂ * (x₂ - y₂)) *
      DihedralGroup.r (ε₃ * (x₃ - y₃)) = 1 := by
    rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, hsum, DihedralGroup.one_def]
  obtain ⟨h₁, h₂, h₃⟩ := h _ hq₁ _ hq₂ _ hq₃ hone
  rw [DihedralGroup.one_def] at h₁ h₂ h₃
  simp only [DihedralGroup.r.injEq] at h₁ h₂ h₃
  have e₁ : x₁ = y₁ := sub_eq_zero.mp h₁
  have e₂ : x₂ = y₂ := by
    rcases hε₂ with rfl | rfl
    · exact sub_eq_zero.mp (by linear_combination h₂)
    · exact sub_eq_zero.mp (by linear_combination -h₂)
  have e₃ : x₃ = y₃ := by
    rcases hε₃ with rfl | rfl
    · exact sub_eq_zero.mp (by linear_combination h₃)
    · exact sub_eq_zero.mp (by linear_combination -h₃)
  rw [e₁, e₂, e₃]

/-- **Disjointness kernel, pure axis 3** (the two types differ at axes 1, 2
and agree at axis 3).  `γ₁, γ₂` record the mixed-axis orientations via
`hmix₁, hmix₂`; the compatibility condition is `ε₂ * γ₂ = -γ₁`. -/
lemma disjoint_images_pure3 (h : IsTPP S T U)
    {c₁ c₂ c₁' c₂' C₃ : Finset (ZMod n)} {ε₂ ε₃ γ₁ γ₂ : ZMod n}
    (hγ₁ : γ₁ = 1 ∨ γ₁ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hC₃ : C₃ = rotPart U ∨ C₃ = refPart U)
    (hmix₁ : ∀ x ∈ c₁, ∀ y ∈ c₁', ∃ e : ZMod n,
      DihedralGroup.sr e ∈ S * S⁻¹ ∧ x - y = γ₁ * e)
    (hmix₂ : ∀ x ∈ c₂, ∀ y ∈ c₂', ∃ e : ZMod n,
      DihedralGroup.sr e ∈ T * T⁻¹ ∧ x - y = γ₂ * e)
    (hcond : ε₂ * γ₂ = -γ₁) :
    Disjoint ((c₁ ×ˢ c₂ ×ˢ C₃).image (form ε₂ ε₃))
      ((c₁' ×ˢ c₂' ×ˢ C₃).image (form ε₂ ε₃)) := by
  rw [Finset.disjoint_left]
  rintro v hv₁ hv₂
  obtain ⟨⟨x₁, x₂, x₃⟩, hxmem, hxv⟩ := Finset.mem_image.mp hv₁
  obtain ⟨⟨y₁, y₂, y₃⟩, hymem, hyv⟩ := Finset.mem_image.mp hv₂
  simp only [Finset.mem_product] at hxmem hymem
  obtain ⟨hx₁, hx₂, hx₃⟩ := hxmem
  obtain ⟨hy₁, hy₂, hy₃⟩ := hymem
  have hcol : x₁ + ε₂ * x₂ + ε₃ * x₃ = y₁ + ε₂ * y₂ + ε₃ * y₃ := by
    simpa [form] using hxv.trans hyv.symm
  obtain ⟨e₁, hqe₁, he₁⟩ := hmix₁ x₁ hx₁ y₁ hy₁
  obtain ⟨e₂, hqe₂, he₂⟩ := hmix₂ x₂ hx₂ y₂ hy₂
  -- exponent form of the collision: γ₁·(e₁ - e₂) + ε₃·(x₃ - y₃) = 0
  have hkey : γ₁ * (e₁ - e₂) + ε₃ * (x₃ - y₃) = 0 := by
    linear_combination hcol - he₁ - ε₂ * he₂ - e₂ * hcond
  have hq₃ : DihedralGroup.r (e₁ - e₂) ∈ U * U⁻¹ := by
    rcases hγ₁ with rfl | rfl <;> rcases hε₃ with rfl | rfl
    · have hd : e₁ - e₂ = y₃ - x₃ := by linear_combination hkey
      rw [hd]; exact r_sub_mem_samePart hC₃ hy₃ hx₃
    · have hd : e₁ - e₂ = x₃ - y₃ := by linear_combination hkey
      rw [hd]; exact r_sub_mem_samePart hC₃ hx₃ hy₃
    · have hd : e₁ - e₂ = x₃ - y₃ := by linear_combination -hkey
      rw [hd]; exact r_sub_mem_samePart hC₃ hx₃ hy₃
    · have hd : e₁ - e₂ = y₃ - x₃ := by linear_combination -hkey
      rw [hd]; exact r_sub_mem_samePart hC₃ hy₃ hx₃
  have hz : e₂ - e₁ + (e₁ - e₂) = 0 := by ring
  have hone : DihedralGroup.sr e₁ * DihedralGroup.sr e₂ * DihedralGroup.r (e₁ - e₂) = 1 := by
    rw [DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r, hz, DihedralGroup.one_def]
  exact sr_ne_one e₁ (h _ hqe₁ _ hqe₂ _ hq₃ hone).1

/-- **Disjointness kernel, pure axis 2** (types differ at axes 1, 3);
compatibility condition `ε₃ * γ₃ = -γ₁`. -/
lemma disjoint_images_pure2 (h : IsTPP S T U)
    {c₁ c₃ c₁' c₃' C₂ : Finset (ZMod n)} {ε₂ ε₃ γ₁ γ₃ : ZMod n}
    (hγ₁ : γ₁ = 1 ∨ γ₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hC₂ : C₂ = rotPart T ∨ C₂ = refPart T)
    (hmix₁ : ∀ x ∈ c₁, ∀ y ∈ c₁', ∃ e : ZMod n,
      DihedralGroup.sr e ∈ S * S⁻¹ ∧ x - y = γ₁ * e)
    (hmix₃ : ∀ x ∈ c₃, ∀ y ∈ c₃', ∃ e : ZMod n,
      DihedralGroup.sr e ∈ U * U⁻¹ ∧ x - y = γ₃ * e)
    (hcond : ε₃ * γ₃ = -γ₁) :
    Disjoint ((c₁ ×ˢ C₂ ×ˢ c₃).image (form ε₂ ε₃))
      ((c₁' ×ˢ C₂ ×ˢ c₃').image (form ε₂ ε₃)) := by
  rw [Finset.disjoint_left]
  rintro v hv₁ hv₂
  obtain ⟨⟨x₁, x₂, x₃⟩, hxmem, hxv⟩ := Finset.mem_image.mp hv₁
  obtain ⟨⟨y₁, y₂, y₃⟩, hymem, hyv⟩ := Finset.mem_image.mp hv₂
  simp only [Finset.mem_product] at hxmem hymem
  obtain ⟨hx₁, hx₂, hx₃⟩ := hxmem
  obtain ⟨hy₁, hy₂, hy₃⟩ := hymem
  have hcol : x₁ + ε₂ * x₂ + ε₃ * x₃ = y₁ + ε₂ * y₂ + ε₃ * y₃ := by
    simpa [form] using hxv.trans hyv.symm
  obtain ⟨e₁, hqe₁, he₁⟩ := hmix₁ x₁ hx₁ y₁ hy₁
  obtain ⟨e₃, hqe₃, he₃⟩ := hmix₃ x₃ hx₃ y₃ hy₃
  -- collision: γ₁·(e₁ - e₃) + ε₂·(x₂ - y₂) = 0
  have hkey : γ₁ * (e₁ - e₃) + ε₂ * (x₂ - y₂) = 0 := by
    linear_combination hcol - he₁ - ε₃ * he₃ - e₃ * hcond
  have hq₂ : DihedralGroup.r (e₃ - e₁) ∈ T * T⁻¹ := by
    rcases hγ₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl
    · have hd : e₃ - e₁ = x₂ - y₂ := by linear_combination -hkey
      rw [hd]; exact r_sub_mem_samePart hC₂ hx₂ hy₂
    · have hd : e₃ - e₁ = y₂ - x₂ := by linear_combination -hkey
      rw [hd]; exact r_sub_mem_samePart hC₂ hy₂ hx₂
    · have hd : e₃ - e₁ = y₂ - x₂ := by linear_combination hkey
      rw [hd]; exact r_sub_mem_samePart hC₂ hy₂ hx₂
    · have hd : e₃ - e₁ = x₂ - y₂ := by linear_combination hkey
      rw [hd]; exact r_sub_mem_samePart hC₂ hx₂ hy₂
  have hz : e₃ - (e₁ + (e₃ - e₁)) = 0 := by ring
  have hone : DihedralGroup.sr e₁ * DihedralGroup.r (e₃ - e₁) * DihedralGroup.sr e₃ = 1 := by
    rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, hz, DihedralGroup.one_def]
  exact sr_ne_one e₁ (h _ hqe₁ _ hq₂ _ hqe₃ hone).1

/-- **Disjointness kernel, pure axis 1** (types differ at axes 2, 3);
compatibility condition `ε₂ * γ₂ = -(ε₃ * γ₃)`. -/
lemma disjoint_images_pure1 (h : IsTPP S T U)
    {c₂ c₃ c₂' c₃' C₁ : Finset (ZMod n)} {ε₂ ε₃ γ₂ γ₃ : ZMod n}
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hγ₂ : γ₂ = 1 ∨ γ₂ = -1)
    (hC₁ : C₁ = rotPart S ∨ C₁ = refPart S)
    (hmix₂ : ∀ x ∈ c₂, ∀ y ∈ c₂', ∃ e : ZMod n,
      DihedralGroup.sr e ∈ T * T⁻¹ ∧ x - y = γ₂ * e)
    (hmix₃ : ∀ x ∈ c₃, ∀ y ∈ c₃', ∃ e : ZMod n,
      DihedralGroup.sr e ∈ U * U⁻¹ ∧ x - y = γ₃ * e)
    (hcond : ε₂ * γ₂ = -(ε₃ * γ₃)) :
    Disjoint ((C₁ ×ˢ c₂ ×ˢ c₃).image (form ε₂ ε₃))
      ((C₁ ×ˢ c₂' ×ˢ c₃').image (form ε₂ ε₃)) := by
  rw [Finset.disjoint_left]
  rintro v hv₁ hv₂
  obtain ⟨⟨x₁, x₂, x₃⟩, hxmem, hxv⟩ := Finset.mem_image.mp hv₁
  obtain ⟨⟨y₁, y₂, y₃⟩, hymem, hyv⟩ := Finset.mem_image.mp hv₂
  simp only [Finset.mem_product] at hxmem hymem
  obtain ⟨hx₁, hx₂, hx₃⟩ := hxmem
  obtain ⟨hy₁, hy₂, hy₃⟩ := hymem
  have hcol : x₁ + ε₂ * x₂ + ε₃ * x₃ = y₁ + ε₂ * y₂ + ε₃ * y₃ := by
    simpa [form] using hxv.trans hyv.symm
  obtain ⟨e₂, hqe₂, he₂⟩ := hmix₂ x₂ hx₂ y₂ hy₂
  obtain ⟨e₃, hqe₃, he₃⟩ := hmix₃ x₃ hx₃ y₃ hy₃
  -- collision: (x₁ - y₁) + (ε₂·γ₂)·(e₂ - e₃) = 0
  have hkey : (x₁ - y₁) + (ε₂ * γ₂) * (e₂ - e₃) = 0 := by
    linear_combination hcol - ε₂ * he₂ - ε₃ * he₃ - e₃ * hcond
  have hq₁ : DihedralGroup.r (e₂ - e₃) ∈ S * S⁻¹ := by
    rcases hε₂ with rfl | rfl <;> rcases hγ₂ with rfl | rfl
    · have hd : e₂ - e₃ = y₁ - x₁ := by linear_combination hkey
      rw [hd]; exact r_sub_mem_samePart hC₁ hy₁ hx₁
    · have hd : e₂ - e₃ = x₁ - y₁ := by linear_combination -hkey
      rw [hd]; exact r_sub_mem_samePart hC₁ hx₁ hy₁
    · have hd : e₂ - e₃ = x₁ - y₁ := by linear_combination -hkey
      rw [hd]; exact r_sub_mem_samePart hC₁ hx₁ hy₁
    · have hd : e₂ - e₃ = y₁ - x₁ := by linear_combination hkey
      rw [hd]; exact r_sub_mem_samePart hC₁ hy₁ hx₁
  have hz : e₃ - (e₂ - (e₂ - e₃)) = 0 := by ring
  have hone : DihedralGroup.r (e₂ - e₃) * DihedralGroup.sr e₂ * DihedralGroup.sr e₃ = 1 := by
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr, hz, DihedralGroup.one_def]
  exact sr_ne_one e₂ (h _ hq₁ _ hqe₂ _ hqe₃ hone).2.1

end Kernels

/-! ## Counting -/

/-- Three pairwise disjoint finsets in a fintype have total card at most the
cardinality of the type. -/
lemma sum_card_le_of_pairwise_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    {F G H : Finset α} (hFG : Disjoint F G) (hFH : Disjoint F H) (hGH : Disjoint G H) :
    F.card + G.card + H.card ≤ Fintype.card α := by
  have h₁ : (F ∪ G ∪ H).card = F.card + G.card + H.card := by
    rw [Finset.card_union_of_disjoint (by rw [Finset.disjoint_union_left]; exact ⟨hFH, hGH⟩),
      Finset.card_union_of_disjoint hFG]
  calc F.card + G.card + H.card = (F ∪ G ∪ H).card := h₁.symm
    _ ≤ Fintype.card α := Finset.card_le_univ _

omit [NeZero n] in
/-- Card of the image of a type product under an injective form. -/
lemma card_image_form {c₁ c₂ c₃ : Finset (ZMod n)} {ε₂ ε₃ : ZMod n}
    (hinj : Set.InjOn (form ε₂ ε₃) ↑(c₁ ×ˢ c₂ ×ˢ c₃)) :
    ((c₁ ×ˢ c₂ ×ˢ c₃).image (form ε₂ ε₃)).card = c₁.card * c₂.card * c₃.card := by
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_product, mul_assoc]

section Systems

variable {S T U : Finset (DihedralGroup n)}

/-- Generic assembly: three type products with a common injective form and
pairwise disjoint images sum to at most `n`. -/
private lemma three_le (p₁ q₁ w₁ p₂ q₂ w₂ p₃ q₃ w₃ : Finset (ZMod n)) {ε₂ ε₃ : ZMod n}
    (i₁ : Set.InjOn (form ε₂ ε₃) ↑(p₁ ×ˢ q₁ ×ˢ w₁))
    (i₂ : Set.InjOn (form ε₂ ε₃) ↑(p₂ ×ˢ q₂ ×ˢ w₂))
    (i₃ : Set.InjOn (form ε₂ ε₃) ↑(p₃ ×ˢ q₃ ×ˢ w₃))
    (d₁₂ : Disjoint ((p₁ ×ˢ q₁ ×ˢ w₁).image (form ε₂ ε₃)) ((p₂ ×ˢ q₂ ×ˢ w₂).image (form ε₂ ε₃)))
    (d₁₃ : Disjoint ((p₁ ×ˢ q₁ ×ˢ w₁).image (form ε₂ ε₃)) ((p₃ ×ˢ q₃ ×ˢ w₃).image (form ε₂ ε₃)))
    (d₂₃ : Disjoint ((p₂ ×ˢ q₂ ×ˢ w₂).image (form ε₂ ε₃)) ((p₃ ×ˢ q₃ ×ˢ w₃).image (form ε₂ ε₃))) :
    p₁.card * q₁.card * w₁.card + p₂.card * q₂.card * w₂.card
      + p₃.card * q₃.card * w₃.card ≤ n := by
  have hle := sum_card_le_of_pairwise_disjoint d₁₂ d₁₃ d₂₃
  rw [card_image_form i₁, card_image_form i₂, card_image_form i₃, ZMod.card] at hle
  exact hle

/- The mixed-axis witnesses.  Direction rot→ref carries `γ = -1`, direction
ref→rot carries `γ = 1`. -/

private lemma mixS_rr :
    ∀ x ∈ rotPart S, ∀ y ∈ refPart S, ∃ e : ZMod n,
      DihedralGroup.sr e ∈ S * S⁻¹ ∧ x - y = (-1 : ZMod n) * e :=
  fun x hx y hy => ⟨y - x, sr_mem_mixed hx hy, by ring⟩

private lemma mixS_fr :
    ∀ x ∈ refPart S, ∀ y ∈ rotPart S, ∃ e : ZMod n,
      DihedralGroup.sr e ∈ S * S⁻¹ ∧ x - y = (1 : ZMod n) * e :=
  fun x hx y hy => ⟨x - y, sr_mem_mixed hy hx, by ring⟩

private lemma mixT_rr :
    ∀ x ∈ rotPart T, ∀ y ∈ refPart T, ∃ e : ZMod n,
      DihedralGroup.sr e ∈ T * T⁻¹ ∧ x - y = (-1 : ZMod n) * e :=
  fun x hx y hy => ⟨y - x, sr_mem_mixed hx hy, by ring⟩

private lemma mixT_fr :
    ∀ x ∈ refPart T, ∀ y ∈ rotPart T, ∃ e : ZMod n,
      DihedralGroup.sr e ∈ T * T⁻¹ ∧ x - y = (1 : ZMod n) * e :=
  fun x hx y hy => ⟨x - y, sr_mem_mixed hy hx, by ring⟩

private lemma mixU_rr :
    ∀ x ∈ rotPart U, ∀ y ∈ refPart U, ∃ e : ZMod n,
      DihedralGroup.sr e ∈ U * U⁻¹ ∧ x - y = (-1 : ZMod n) * e :=
  fun x hx y hy => ⟨y - x, sr_mem_mixed hx hy, by ring⟩

private lemma mixU_fr :
    ∀ x ∈ refPart U, ∀ y ∈ rotPart U, ∃ e : ZMod n,
      DihedralGroup.sr e ∈ U * U⁻¹ ∧ x - y = (1 : ZMod n) * e :=
  fun x hx y hy => ⟨x - y, sr_mem_mixed hy hx, by ring⟩

/-! The eight same-parity systems.  Types are written `τ₁τ₂τ₃` with
`0 ↦ rotPart`, `1 ↦ refPart`; each system uses the single linear form
recorded in its docstring, and each pairwise disjointness instantiates
the kernel of the pure axis of that pair. -/

/-- Even system `{000, 110, 101}`, form `x₁ - x₂ - x₃`. -/
private lemma sysE1 (h : IsTPP S T U) :
    (rotPart S).card * (rotPart T).card * (rotPart U).card
    + (refPart S).card * (refPart T).card * (rotPart U).card
    + (refPart S).card * (rotPart T).card * (refPart U).card ≤ n := by
  have hm : (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 := Or.inr rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hm hm)
    (injOn_form h (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) hm hm)
    (injOn_form h (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) hm hm)
    ?_ ?_ ?_
  · -- (000,110): pure axis 3, γ₁ = γ₂ = -1; ε₂γ₂ = 1 = -γ₁
    exact disjoint_images_pure3 h hm hm (Or.inl rfl) mixS_rr mixT_rr (by ring)
  · -- (000,101): pure axis 2, γ₁ = γ₃ = -1; ε₃γ₃ = 1 = -γ₁
    exact disjoint_images_pure2 h hm hm (Or.inl rfl) mixS_rr mixU_rr (by ring)
  · -- (110,101): pure axis 1 (= refPart S), γ₂ = 1, γ₃ = -1; ε₂γ₂ = -1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hm (Or.inl rfl) (Or.inr rfl) mixT_fr mixU_rr (by ring)

/-- Even system `{000, 110, 011}`, form `x₁ - x₂ + x₃`. -/
private lemma sysE2 (h : IsTPP S T U) :
    (rotPart S).card * (rotPart T).card * (rotPart U).card
    + (refPart S).card * (refPart T).card * (rotPart U).card
    + (rotPart S).card * (refPart T).card * (refPart U).card ≤ n := by
  have hm : (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 := Or.inr rfl
  have hp : (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 := Or.inl rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hm hp)
    (injOn_form h (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) hm hp)
    (injOn_form h (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) hm hp)
    ?_ ?_ ?_
  · -- (000,110): pure axis 3, γ₁ = γ₂ = -1; ε₂γ₂ = 1 = -γ₁
    exact disjoint_images_pure3 h hm hp (Or.inl rfl) mixS_rr mixT_rr (by ring)
  · -- (000,011): pure axis 1 (= rotPart S), γ₂ = γ₃ = -1; ε₂γ₂ = 1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hm hm (Or.inl rfl) mixT_rr mixU_rr (by ring)
  · -- (110,011): pure axis 2 (= refPart T), γ₁ = 1, γ₃ = -1; ε₃γ₃ = -1 = -γ₁
    exact disjoint_images_pure2 h hp hm (Or.inr rfl) mixS_fr mixU_rr (by ring)

/-- Even system `{000, 101, 011}`, form `x₁ + x₂ - x₃`. -/
private lemma sysE3 (h : IsTPP S T U) :
    (rotPart S).card * (rotPart T).card * (rotPart U).card
    + (refPart S).card * (rotPart T).card * (refPart U).card
    + (rotPart S).card * (refPart T).card * (refPart U).card ≤ n := by
  have hm : (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 := Or.inr rfl
  have hp : (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 := Or.inl rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hp hm)
    (injOn_form h (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) hp hm)
    (injOn_form h (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) hp hm)
    ?_ ?_ ?_
  · -- (000,101): pure axis 2 (= rotPart T), γ₁ = γ₃ = -1; ε₃γ₃ = 1 = -γ₁
    exact disjoint_images_pure2 h hm hp (Or.inl rfl) mixS_rr mixU_rr (by ring)
  · -- (000,011): pure axis 1 (= rotPart S), γ₂ = γ₃ = -1; ε₂γ₂ = -1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hp hm (Or.inl rfl) mixT_rr mixU_rr (by ring)
  · -- (101,011): pure axis 3 (= refPart U), γ₁ = 1, γ₂ = -1; ε₂γ₂ = -1 = -γ₁
    exact disjoint_images_pure3 h hp hm (Or.inr rfl) mixS_fr mixT_rr (by ring)

/-- Even system `{110, 101, 011}`, form `x₁ + x₂ + x₃`. -/
private lemma sysE4 (h : IsTPP S T U) :
    (refPart S).card * (refPart T).card * (rotPart U).card
    + (refPart S).card * (rotPart T).card * (refPart U).card
    + (rotPart S).card * (refPart T).card * (refPart U).card ≤ n := by
  have hp : (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 := Or.inl rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) hp hp)
    (injOn_form h (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) hp hp)
    (injOn_form h (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) hp hp)
    ?_ ?_ ?_
  · -- (110,101): pure axis 1 (= refPart S), γ₂ = 1, γ₃ = -1; ε₂γ₂ = 1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hp hp (Or.inr rfl) mixT_fr mixU_rr (by ring)
  · -- (110,011): pure axis 2 (= refPart T), γ₁ = 1, γ₃ = -1; ε₃γ₃ = -1 = -γ₁
    exact disjoint_images_pure2 h hp hp (Or.inr rfl) mixS_fr mixU_rr (by ring)
  · -- (101,011): pure axis 3 (= refPart U), γ₁ = 1, γ₂ = -1; ε₂γ₂ = -1 = -γ₁
    exact disjoint_images_pure3 h hp hp (Or.inr rfl) mixS_fr mixT_rr (by ring)

/-- Odd system `{100, 010, 001}`, form `x₁ + x₂ + x₃`. -/
private lemma sysO1 (h : IsTPP S T U) :
    (refPart S).card * (rotPart T).card * (rotPart U).card
    + (rotPart S).card * (refPart T).card * (rotPart U).card
    + (rotPart S).card * (rotPart T).card * (refPart U).card ≤ n := by
  have hp : (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 := Or.inl rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) hp hp)
    (injOn_form h (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) hp hp)
    (injOn_form h (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) hp hp)
    ?_ ?_ ?_
  · -- (100,010): pure axis 3 (= rotPart U), γ₁ = 1, γ₂ = -1; ε₂γ₂ = -1 = -γ₁
    exact disjoint_images_pure3 h hp hp (Or.inl rfl) mixS_fr mixT_rr (by ring)
  · -- (100,001): pure axis 2 (= rotPart T), γ₁ = 1, γ₃ = -1; ε₃γ₃ = -1 = -γ₁
    exact disjoint_images_pure2 h hp hp (Or.inl rfl) mixS_fr mixU_rr (by ring)
  · -- (010,001): pure axis 1 (= rotPart S), γ₂ = 1, γ₃ = -1; ε₂γ₂ = 1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hp hp (Or.inl rfl) mixT_fr mixU_rr (by ring)

/-- Odd system `{100, 010, 111}`, form `x₁ + x₂ - x₃`. -/
private lemma sysO2 (h : IsTPP S T U) :
    (refPart S).card * (rotPart T).card * (rotPart U).card
    + (rotPart S).card * (refPart T).card * (rotPart U).card
    + (refPart S).card * (refPart T).card * (refPart U).card ≤ n := by
  have hm : (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 := Or.inr rfl
  have hp : (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 := Or.inl rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) hp hm)
    (injOn_form h (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) hp hm)
    (injOn_form h (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) hp hm)
    ?_ ?_ ?_
  · -- (100,010): pure axis 3 (= rotPart U), γ₁ = 1, γ₂ = -1; ε₂γ₂ = -1 = -γ₁
    exact disjoint_images_pure3 h hp hm (Or.inl rfl) mixS_fr mixT_rr (by ring)
  · -- (100,111): pure axis 1 (= refPart S), γ₂ = γ₃ = -1; ε₂γ₂ = -1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hp hm (Or.inr rfl) mixT_rr mixU_rr (by ring)
  · -- (010,111): pure axis 2 (= refPart T), γ₁ = -1, γ₃ = -1; ε₃γ₃ = 1 = -γ₁
    exact disjoint_images_pure2 h hm hp (Or.inr rfl) mixS_rr mixU_rr (by ring)

/-- Odd system `{100, 001, 111}`, form `x₁ - x₂ + x₃`. -/
private lemma sysO3 (h : IsTPP S T U) :
    (refPart S).card * (rotPart T).card * (rotPart U).card
    + (rotPart S).card * (rotPart T).card * (refPart U).card
    + (refPart S).card * (refPart T).card * (refPart U).card ≤ n := by
  have hm : (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 := Or.inr rfl
  have hp : (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 := Or.inl rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) hm hp)
    (injOn_form h (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) hm hp)
    (injOn_form h (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) hm hp)
    ?_ ?_ ?_
  · -- (100,001): pure axis 2 (= rotPart T), γ₁ = 1, γ₃ = -1; ε₃γ₃ = -1 = -γ₁
    exact disjoint_images_pure2 h hp hm (Or.inl rfl) mixS_fr mixU_rr (by ring)
  · -- (100,111): pure axis 1 (= refPart S), γ₂ = γ₃ = -1; ε₂γ₂ = 1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hm hm (Or.inr rfl) mixT_rr mixU_rr (by ring)
  · -- (001,111): pure axis 3 (= refPart U), γ₁ = γ₂ = -1; ε₂γ₂ = 1 = -γ₁
    exact disjoint_images_pure3 h hm hp (Or.inr rfl) mixS_rr mixT_rr (by ring)

/-- Odd system `{010, 001, 111}`, form `x₁ - x₂ - x₃`. -/
private lemma sysO4 (h : IsTPP S T U) :
    (rotPart S).card * (refPart T).card * (rotPart U).card
    + (rotPart S).card * (rotPart T).card * (refPart U).card
    + (refPart S).card * (refPart T).card * (refPart U).card ≤ n := by
  have hm : (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 := Or.inr rfl
  refine three_le _ _ _ _ _ _ _ _ _
    (injOn_form h (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) hm hm)
    (injOn_form h (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) hm hm)
    (injOn_form h (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) hm hm)
    ?_ ?_ ?_
  · -- (010,001): pure axis 1 (= rotPart S), γ₂ = 1, γ₃ = -1; ε₂γ₂ = -1 = -(ε₃γ₃)
    exact disjoint_images_pure1 h hm (Or.inl rfl) (Or.inl rfl) mixT_fr mixU_rr (by ring)
  · -- (010,111): pure axis 2 (= refPart T), γ₁ = -1, γ₃ = -1; ε₃γ₃ = 1 = -γ₁
    exact disjoint_images_pure2 h hm hm (Or.inr rfl) mixS_rr mixU_rr (by ring)
  · -- (001,111): pure axis 3 (= refPart U), γ₁ = -1, γ₂ = -1; ε₂γ₂ = 1 = -γ₁
    exact disjoint_images_pure3 h hm hm (Or.inr rfl) mixS_rr mixT_rr (by ring)

end Systems

/-- **Main theorem.**  Any triple of finsets in the dihedral group of order
`2n` satisfying the triple product property has
`3 * |S| * |T| * |U| ≤ 8 * n`; that is, the subset TPP ratio of `D_{2n}`
is at most `4/3`.  (Dihedral subset case of the Hedtke–Murthy conjectures;
sharp iff `3 ∣ n`.) -/
theorem card_mul_le_of_isTPP {S T U : Finset (DihedralGroup n)} (h : IsTPP S T U) :
    3 * (S.card * T.card * U.card) ≤ 8 * n := by
  have e1 := sysE1 h
  have e2 := sysE2 h
  have e3 := sysE3 h
  have e4 := sysE4 h
  have o1 := sysO1 h
  have o2 := sysO2 h
  have o3 := sysO3 h
  have o4 := sysO4 h
  rw [card_eq_parts S, card_eq_parts T, card_eq_parts U]
  set a₁ := (rotPart S).card
  set b₁ := (refPart S).card
  set a₂ := (rotPart T).card
  set b₂ := (refPart T).card
  set a₃ := (rotPart U).card
  set b₃ := (refPart U).card
  have expand : (a₁ + b₁) * (a₂ + b₂) * (a₃ + b₃)
      = (a₁ * a₂ * a₃ + b₁ * b₂ * a₃ + b₁ * a₂ * b₃ + a₁ * b₂ * b₃)
        + (b₁ * a₂ * a₃ + a₁ * b₂ * a₃ + a₁ * a₂ * b₃ + b₁ * b₂ * b₃) := by ring
  rw [expand]
  linarith

/-- The bound in terms of the group order: `3 |S| |T| |U| ≤ 4 |D_{2n}|`. -/
theorem card_mul_le_of_isTPP' {S T U : Finset (DihedralGroup n)} (h : IsTPP S T U) :
    3 * (S.card * T.card * U.card) ≤ 4 * Fintype.card (DihedralGroup n) := by
  have hb := card_mul_le_of_isTPP h
  rw [DihedralGroup.card]
  linarith

/-! ## Re-homing onto the canonical `Xlib.TPP` API

`IsTPP` above is byte-identical to the right-quotient TPP
`Xlib.TPP.TripleProductPropertyR`, while the canonical definition is the
left-quotient `Xlib.TPP.TripleProductProperty`.  On the *same* ordered
triple the two conventions differ, but they transfer through the inversion
bridge `Xlib.TPP.tripleProductProperty_iff_inv`, and `Finset.card_inv`
preserves all three cardinalities.  This section re-homes the 4/3 bound
onto the canonical definition and derives the capacity bound
`3 * β(D_{2n}) ≤ 8 * n`. -/

/-- `IsTPP` is definitionally the right-quotient TPP
`Xlib.TPP.TripleProductPropertyR` (in any group). -/
theorem isTPP_iff {G : Type*} [Group G] [DecidableEq G] (S T U : Finset G) :
    IsTPP S T U ↔ Xlib.TPP.TripleProductPropertyR S T U :=
  Iff.rfl

/-- **Main theorem, canonical convention.**  Any triple of finsets in the
dihedral group of order `2n` satisfying the (left-quotient) triple product
property `Xlib.TPP.TripleProductProperty` has
`3 * (|S| * |T| * |U|) ≤ 8 * n`.  Transfer from `card_mul_le_of_isTPP`
through the inversion bridge: `(S, T, U)` is left-TPP iff
`(S⁻¹, T⁻¹, U⁻¹)` is right-TPP, and inversion preserves cardinalities. -/
theorem card_mul_le_of_tripleProductProperty {S T U : Finset (DihedralGroup n)}
    (h : Xlib.TPP.TripleProductProperty S T U) :
    3 * (S.card * T.card * U.card) ≤ 8 * n := by
  have hR : IsTPP S⁻¹ T⁻¹ U⁻¹ :=
    (isTPP_iff _ _ _).mpr (Xlib.TPP.tripleProductProperty_iff_inv.mp h)
  have hb := card_mul_le_of_isTPP hR
  simpa only [Finset.card_inv] using hb

/-- The canonical-convention bound in terms of the group order:
`3 |S| |T| |U| ≤ 4 |D_{2n}|`. -/
theorem card_mul_le_of_tripleProductProperty' {S T U : Finset (DihedralGroup n)}
    (h : Xlib.TPP.TripleProductProperty S T U) :
    3 * (S.card * T.card * U.card) ≤ 4 * Fintype.card (DihedralGroup n) := by
  have hb := card_mul_le_of_tripleProductProperty h
  rw [DihedralGroup.card]
  linarith

/-- **Capacity form of the 4/3 bound:** the TPP capacity of the dihedral
group satisfies `3 * β(D_{2n}) ≤ 8 * n`, i.e. `ρ(D_{2n}) ≤ 4/3`.  Since
`β` is a `Finset.sup` and the bound `8 * n` is not divisible by `3` in
general, we extract a triple attaining the sup and apply the per-triple
bound. -/
theorem three_mul_tppCapacity_le :
    3 * Xlib.TPP.tppCapacity (DihedralGroup n) ≤ 8 * n := by
  obtain ⟨⟨S, T, U⟩, hmem, hsup⟩ :=
    Finset.exists_mem_eq_sup (Xlib.TPP.tppTriples (DihedralGroup n))
      ⟨(Finset.univ, {1}, {1}), Xlib.TPP.mem_tppTriples.mpr Xlib.TPP.tpp_trivial⟩
      (fun p => p.1.card * p.2.1.card * p.2.2.card)
  have hcap : Xlib.TPP.tppCapacity (DihedralGroup n) = S.card * T.card * U.card := hsup
  rw [hcap]
  exact card_mul_le_of_tripleProductProperty (Xlib.TPP.mem_tppTriples.mp hmem)

end DihedralTPP
