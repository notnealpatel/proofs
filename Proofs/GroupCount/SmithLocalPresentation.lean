/-
# Smith's 1950 conjecture: local presentations recover only `1`, `C₂`, `C₃`

## Source

arXiv:2610.10586, Yu Pan, "Local Presentations of Groups: Completion and
Smith's Conjecture".  Retrieved 2026-10-21.

* Statement: Theorem 1.1 (classification), Section 1.  The definitions of a
  domain, of `U(X)`, of `π_X` and of `P(G)` are in Section 1, display (1.1).
* Proof route formalized here: Section 2 (Lemma 2.2, Theorem 2.3
  (iii) ⇒ (i), the Zorn completion of local maps) and Section 5 (Lemma 5.2,
  Lemma 5.3, the obstructions of Theorem 5.4), plus the converse in the
  proof of Theorem 1.1.

Verbatim informal claim (Section 1):

  "Let `G` be a group.  A subset `X ⊆ G` is symmetric if `X⁻¹ = X`. ...  a
  domain means a symmetric subset containing `1` ...
  `U(X) = ⟨ [x] (x ∈ X) | [1] = 1, [x][y] = [xy] whenever x, y, xy ∈ X ⟩`.
  ... `π_X : U(X) → ⟨X⟩, [x] ↦ x` ...  We write `P(G)` if
  `π_X : U(X) → G` is an isomorphism for every domain `X` generating `G`."

  "Theorem 1.1. For an arbitrary group `G`, the following are equivalent:
  (i) `P(G)` holds; (ii) `G ≅ 1`, `C₂`, or `C₃`."

Status: proved in the paper (Smith conjectured it in 1950, p. 438).

## Formalization notes

* `P(G)` asks for an isomorphism onto `G`; surjectivity is automatic for a
  generating `X` (`surjective_evalU`), so `SmithP` records injectivity.
* "`G ≅ 1`, `C₂` or `C₃`" is rendered as `Finite G ∧ Nat.card G ≤ 3`; a group
  of order at most three is trivial or cyclic of prime order.  The `Finite`
  conjunct guards the junk value `Nat.card G = 0` for infinite `G`.
* The paper's affine target over `ℚ̄` is replaced by `Aff` over `ℂ`, as the
  paper's countability is not used.  For the first three obstructions the
  abelian target `ℂˣ` suffices.  The infinite-order obstruction uses the
  values `s² ↦ -1`, `s³ ↦ 1` in place of the paper's `s² ↦ 1`, `s³ ↦ ζ₃`; the
  finite-order obstruction uses `s ↦ 2` in place of `ζ_{n+1}`.
-/
import Mathlib

set_option autoImplicit false

namespace SmithLocalPresentation

variable {G : Type*} [Group G] {K : Type*} [Group K]

/-! ## Definitions (Section 1) -/

/-- A *domain* of `G` (Section 1): a subset containing `1` and closed under
inversion. -/
def IsDom (X : Set G) : Prop := (1 : G) ∈ X ∧ ∀ x ∈ X, x⁻¹ ∈ X

/-- The defining relators of `U(X)` (display (1.1)): `[x][y][z]⁻¹` whenever
`x, y, z ∈ X` and `x y = z`, together with `[1]` when `1 ∈ X`. -/
def localRels (X : Set G) : Set (FreeGroup X) :=
  {r | ∃ x y z : X, (x : G) * y = z ∧
      r = FreeGroup.of x * FreeGroup.of y * (FreeGroup.of z)⁻¹} ∪
    {r | ∃ h : (1 : G) ∈ X, r = FreeGroup.of ⟨1, h⟩}

/-- The universal local presentation `U(X)` of a subset `X` (display (1.1)). -/
abbrev U (X : Set G) : Type _ := PresentedGroup (localRels X)

/-- A map `f : G → K` is *local* on `X` (Definition 2.1): `f 1 = 1` and
`f (x y) = f x * f y` whenever `x, y, x y ∈ X`.  Only the values on `X`
matter. -/
def IsLocal (X : Set G) (f : G → K) : Prop :=
  f 1 = 1 ∧ ∀ x ∈ X, ∀ y ∈ X, x * y ∈ X → f (x * y) = f x * f y

/-- A local map respects the defining relators of `U(X)`. -/
theorem lift_localRels (X : Set G) (f : G → K) (hf : IsLocal X f) :
    ∀ r ∈ localRels X, FreeGroup.lift (fun x : X => f x) r = 1 := by
  rintro r (⟨x, y, z, hxyz, rfl⟩ | ⟨h, rfl⟩)
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [← hxyz, hf.2 x x.2 y y.2 (hxyz ▸ z.2), mul_inv_cancel]
  · simpa using hf.1

/-- The homomorphism `U(X) → K`, `[x] ↦ f x`, induced by a local map. -/
def toU (X : Set G) (f : G → K) (hf : IsLocal X f) : U X →* K :=
  PresentedGroup.toGroup (lift_localRels X f hf)

/-- The inclusion of `G` into itself is local on every subset. -/
theorem isLocal_id (X : Set G) : IsLocal X (id : G → G) := ⟨rfl, fun _ _ _ _ _ => rfl⟩

/-- The evaluation map `π_X : U(X) → G`, `[x] ↦ x` (Section 1). -/
def evalU (X : Set G) : U X →* G := toU X id (isLocal_id X)

/-- The induced homomorphism sends a generator `[x]` to `f x`. -/
theorem toU_of (X : Set G) (f : G → K) (hf : IsLocal X f) (x : X) :
    toU X f hf (PresentedGroup.of x) = f x :=
  PresentedGroup.toGroup.of (lift_localRels X f hf)

/-- `π_X [x] = x`. -/
theorem evalU_of (X : Set G) (x : X) : evalU X (PresentedGroup.of x) = x :=
  toU_of X id (isLocal_id X) x

/-- Smith's property `P(G)` (Section 1): for every domain `X` generating `G`,
the evaluation map `π_X : U(X) → G` is injective (hence, by
`surjective_evalU`, an isomorphism). -/
def SmithP (G : Type*) [Group G] : Prop :=
  ∀ X : Set G, IsDom X → Subgroup.closure X = ⊤ → Function.Injective (evalU X)

/-- `π_X` is surjective when `X` generates `G`. -/
theorem surjective_evalU {X : Set G} (hgen : Subgroup.closure X = ⊤) :
    Function.Surjective (evalU X) := by
  refine MonoidHom.range_eq_top.1 (eq_top_iff.2 ?_)
  rw [← hgen, Subgroup.closure_le]
  intro x hx
  exact ⟨PresentedGroup.of ⟨x, hx⟩, evalU_of X ⟨x, hx⟩⟩

/-! ## Completion of local maps (Section 2) -/

/-- A relation `Γ ⊆ G × K` is the graph of a local map on a domain: it contains
`(1, 1)`, is closed under coordinatewise inversion, and `r.2 = p.2 * q.2`
whenever `p.1 * q.1 = r.1`.  Used for the Zorn argument of Theorem 2.3. -/
def IsLocalGraph (Γ : Set (G × K)) : Prop :=
  ((1 : G), (1 : K)) ∈ Γ ∧ (∀ p ∈ Γ, (p.1⁻¹, p.2⁻¹) ∈ Γ) ∧
    ∀ p ∈ Γ, ∀ q ∈ Γ, ∀ r ∈ Γ, p.1 * q.1 = r.1 → r.2 = p.2 * q.2

/-- A local graph is functional. -/
theorem IsLocalGraph.functional {Γ : Set (G × K)} (hΓ : IsLocalGraph Γ) {g : G} {k k' : K}
    (hk : (g, k) ∈ Γ) (hk' : (g, k') ∈ Γ) : k = k' := by
  have h := hΓ.2.2 (g, k) hk (1, 1) hΓ.1 (g, k') hk' (mul_one g)
  simpa using h.symm

/-- **Lemma 2.2** in graph form.  If `t ∉ ⟨dom Γ⟩` and `b` is a square root of
the value at `t²` when `t² ∈ dom Γ` (and `b = 1` otherwise), adjoining
`(t, b)` and `(t⁻¹, b⁻¹)` keeps the graph local. -/
theorem isLocalGraph_extend {Γ : Set (G × K)} (hΓ : IsLocalGraph Γ) {t : G}
    (ht : t ∉ Subgroup.closure (Prod.fst '' Γ)) {b : K}
    (hb : ∀ k, (t * t, k) ∈ Γ → k = b * b) (hb1 : (∀ k, (t * t, k) ∉ Γ) → b = 1) :
    IsLocalGraph (insert (t, b) (insert (t⁻¹, b⁻¹) Γ)) := by
  set H := Subgroup.closure (Prod.fst '' Γ) with hH
  have hmem : ∀ p ∈ Γ, p.1 ∈ H := fun p hp => Subgroup.subset_closure ⟨p, hp, rfl⟩
  have ht' : t⁻¹ ∉ H := fun h => ht (by simpa using H.inv_mem h)
  have ht1 : t ≠ 1 := fun h => ht (h ▸ H.one_mem)
  have hone : ∀ k, ((1 : G), k) ∈ Γ → k = 1 := fun k hk => hΓ.functional hk hΓ.1
  have hsq : t * t ∉ H → b = 1 := fun h => hb1 (fun k hk => h (hmem _ hk))
  have hsq' : ∀ r ∈ Γ, r.1 = t * t → r.2 = b * b := by
    intro r hr h
    exact hb r.2 (by rw [← h]; exact hr)
  have hinv : ∀ r ∈ Γ, r.1⁻¹ = t * t → r.2 = b⁻¹ * b⁻¹ := by
    intro r hr h
    have h2 := hsq' _ (hΓ.2.1 r hr) h
    rw [← inv_inv r.2, show r.2⁻¹ = b * b from h2]
    group
  have hone' : ∀ r ∈ Γ, r.1 = 1 → r.2 = 1 := by
    intro r hr h
    exact hone r.2 (by rw [← h]; exact hr)
  refine ⟨?_, ?_, ?_⟩
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hΓ.1)
  · rintro p (rfl | rfl | hp)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · simp
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (hΓ.2.1 p hp))
  · intro p hp q hq r hr hxyz
    rcases hp with rfl | rfl | hp <;> rcases hq with rfl | rfl | hq <;>
      rcases hr with rfl | rfl | hr <;> try simp only at hxyz ⊢
    -- PPP
    · exact absurd (by simpa using hxyz) ht1
    -- PPM
    · have h3 : t * t ∉ H := by rw [hxyz]; exact ht'
      simp [hsq h3]
    -- PPO
    · exact hsq' r hr hxyz.symm
    -- PMP
    · exact absurd (by simpa using hxyz.symm) ht1
    -- PMM
    · exact absurd (by simpa using hxyz.symm) ht1
    -- PMO
    · rw [hone' r hr (by rw [← hxyz]; group)]; group
    -- POP
    · rw [hone' q hq (by simpa using hxyz)]; group
    -- POM
    · rw [hinv q hq (by
        calc q.1⁻¹ = (t⁻¹ * (t * q.1))⁻¹ := by group
          _ = t * t := by rw [hxyz, mul_inv_rev, inv_inv])]
      group
    -- POO
    · exact absurd (show t ∈ H by
        rw [show t = r.1 * q.1⁻¹ by rw [← hxyz]; group]
        exact H.mul_mem (hmem r hr) (H.inv_mem (hmem q hq))) ht
    -- MPP
    · exact absurd (by simpa using hxyz.symm) ht1
    -- MPM
    · exact absurd (by simpa using hxyz) ht1
    -- MPO
    · rw [hone' r hr (by rw [← hxyz]; group)]; group
    -- MMP
    · have h3 : t * t ∉ H := by
        rw [show t * t = t⁻¹ by
          calc t * t = (t⁻¹ * t⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
            _ = t⁻¹ := by rw [hxyz]]
        exact ht'
      simp [hsq h3]
    -- MMM
    · exact absurd (by simpa using hxyz) ht1
    -- MMO
    · exact hinv r hr (by rw [← hxyz, mul_inv_rev, inv_inv])
    -- MOP
    · rw [hsq' q hq (by rw [show q.1 = t * (t⁻¹ * q.1) by group, hxyz])]; group
    -- MOM
    · rw [hone' q hq (by simpa using hxyz)]; group
    -- MOO
    · exact absurd (show t⁻¹ ∈ H by
        rw [show t⁻¹ = r.1 * q.1⁻¹ by rw [← hxyz]; group]
        exact H.mul_mem (hmem r hr) (H.inv_mem (hmem q hq))) ht'
    -- OPP
    · rw [hone' p hp (by simpa using hxyz)]; group
    -- OPM
    · rw [hinv p hp (by
        calc p.1⁻¹ = ((p.1 * t) * t⁻¹)⁻¹ := by group
          _ = t * t := by rw [hxyz, mul_inv_rev, inv_inv])]
      group
    -- OPO
    · exact absurd (show t ∈ H by
        rw [show t = p.1⁻¹ * r.1 by rw [← hxyz]; group]
        exact H.mul_mem (H.inv_mem (hmem p hp)) (hmem r hr)) ht
    -- OMP
    · rw [hsq' p hp (by rw [show p.1 = p.1 * t⁻¹ * t by group, hxyz])]; group
    -- OMM
    · rw [hone' p hp (by simpa using hxyz)]; group
    -- OMO
    · exact absurd (show t⁻¹ ∈ H by
        rw [show t⁻¹ = p.1⁻¹ * r.1 by rw [← hxyz]; group]
        exact H.mul_mem (H.inv_mem (hmem p hp)) (hmem r hr)) ht'
    -- OOP
    · exact absurd (show t ∈ H by rw [← hxyz]; exact H.mul_mem (hmem p hp) (hmem q hq)) ht
    -- OOM
    · exact absurd (show t⁻¹ ∈ H by rw [← hxyz]; exact H.mul_mem (hmem p hp) (hmem q hq)) ht'
    -- OOO
    · exact hΓ.2.2 p hp q hq r hr hxyz


/-- A local map preserves inverses on a domain (Section 2, after
Definition 2.1). -/
theorem IsLocal.map_inv {X : Set G} {f : G → K} (hf : IsLocal X f) (hX : IsDom X) {x : G}
    (hx : x ∈ X) : f x⁻¹ = (f x)⁻¹ := by
  have h := hf.2 x hx x⁻¹ (hX.2 x hx) (by rw [mul_inv_cancel]; exact hX.1)
  rw [mul_inv_cancel, hf.1] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

/-- The graph of a local map on a domain is a local graph. -/
theorem isLocalGraph_graph {X : Set G} {f : G → K} (hX : IsDom X) (hf : IsLocal X f) :
    IsLocalGraph {p : G × K | p.1 ∈ X ∧ p.2 = f p.1} := by
  refine ⟨⟨hX.1, hf.1.symm⟩, ?_, ?_⟩
  · rintro p ⟨hx, ha⟩
    refine ⟨hX.2 p.1 hx, ?_⟩
    rw [hf.map_inv hX hx, ha]
  · rintro p ⟨hp, hpa⟩ q ⟨hq, hqa⟩ r ⟨hr, hra⟩ hpqr
    rw [hra, hpa, hqa, ← hpqr]
    exact hf.2 p.1 hp q.1 hq (hpqr ▸ hr)

/-- The union of a nonempty chain of local graphs is a local graph. -/
theorem isLocalGraph_sUnion {c : Set (Set (G × K))} (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (hloc : ∀ Γ ∈ c, IsLocalGraph Γ) : IsLocalGraph (⋃₀ c) := by
  have hdir := hc.directedOn
  obtain ⟨Γ₀, hΓ₀⟩ := hne
  refine ⟨⟨Γ₀, hΓ₀, (hloc Γ₀ hΓ₀).1⟩, ?_, ?_⟩
  · rintro p ⟨Γ, hΓ, hp⟩
    exact ⟨Γ, hΓ, (hloc Γ hΓ).2.1 p hp⟩
  · rintro p ⟨Γ₁, hΓ₁, hp⟩ q ⟨Γ₂, hΓ₂, hq⟩ r ⟨Γ₃, hΓ₃, hr⟩ hpqr
    obtain ⟨Γ₄, hΓ₄, h14, h24⟩ := hdir Γ₁ hΓ₁ Γ₂ hΓ₂
    obtain ⟨Γ₅, hΓ₅, h45, h35⟩ := hdir Γ₄ hΓ₄ Γ₃ hΓ₃
    exact (hloc Γ₅ hΓ₅).2.2 p (h45 (h14 hp)) q (h45 (h24 hq)) r (h35 hr) hpqr

/-- **Theorem 2.3, (iii) ⇒ (i)** (completion).  If squaring on `K` is surjective,
every local map `f₀ : X₀ → K` on a domain `X₀ ⊆ G` extends to a local map on
some generating domain `X ⊇ X₀`.  Proof by Zorn's lemma and Lemma 2.2. -/
theorem exists_isLocal_generating (hK : ∀ k : K, ∃ r, r ^ 2 = k) {X₀ : Set G} (hX₀ : IsDom X₀)
    {f₀ : G → K} (hf₀ : IsLocal X₀ f₀) :
    ∃ X : Set G, X₀ ⊆ X ∧ IsDom X ∧ Subgroup.closure X = ⊤ ∧
      ∃ f : G → K, IsLocal X f ∧ Set.EqOn f f₀ X₀ := by
  set Γ₀ : Set (G × K) := {p | p.1 ∈ X₀ ∧ p.2 = f₀ p.1} with hΓ₀
  set S : Set (Set (G × K)) := {Γ | Γ₀ ⊆ Γ ∧ IsLocalGraph Γ} with hS
  obtain ⟨Γ, -, hΓmax⟩ := zorn_subset_nonempty S (fun c hcS hc hne =>
      ⟨⋃₀ c, ⟨fun p hp => ⟨hne.some, hne.some_mem, (hcS hne.some_mem).1 hp⟩,
        isLocalGraph_sUnion hc hne (fun Γ hΓ => (hcS hΓ).2)⟩,
        fun Γ hΓ => Set.subset_sUnion_of_mem hΓ⟩) Γ₀
      ⟨subset_rfl, isLocalGraph_graph hX₀ hf₀⟩
  have hΓ : IsLocalGraph Γ := hΓmax.prop.2
  have hgen : Subgroup.closure (Prod.fst '' Γ) = ⊤ := by
    by_contra hne
    obtain ⟨t, ht⟩ : ∃ t, t ∉ Subgroup.closure (Prod.fst '' Γ) := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.2 fun t _ => h t)
    obtain ⟨b, hb, hb1⟩ : ∃ b : K, (∀ k, (t * t, k) ∈ Γ → k = b * b) ∧
        ((∀ k, (t * t, k) ∉ Γ) → b = 1) := by
      by_cases h : ∃ k, (t * t, k) ∈ Γ
      · obtain ⟨k, hk⟩ := h
        obtain ⟨r, hr⟩ := hK k
        refine ⟨r, fun k' hk' => ?_, fun h' => absurd hk (h' k)⟩
        rw [hΓ.functional hk' hk, ← hr, pow_two]
      · push Not at h
        exact ⟨1, fun k hk => absurd hk (h k), fun _ => rfl⟩
    have hΓ' := isLocalGraph_extend hΓ ht hb hb1
    have hsub : Γ ⊆ insert (t, b) (insert (t⁻¹, b⁻¹) Γ) :=
      (Set.subset_insert _ _).trans (Set.subset_insert _ _)
    have hle := hΓmax.2 ⟨hΓmax.prop.1.trans hsub, hΓ'⟩ hsub
    exact ht (Subgroup.subset_closure ⟨(t, b), hle (Set.mem_insert _ _), rfl⟩)
  classical
  let f : G → K := fun g => if h : ∃ k, (g, k) ∈ Γ then h.choose else 1
  have hf : ∀ g k, (g, k) ∈ Γ → f g = k := by
    intro g k hk
    have h : ∃ k, (g, k) ∈ Γ := ⟨k, hk⟩
    simp only [f, dif_pos h]
    exact hΓ.functional h.choose_spec hk
  refine ⟨Prod.fst '' Γ, fun x hx => ⟨(x, f₀ x), hΓmax.prop.1 ⟨hx, rfl⟩, rfl⟩, ⟨⟨(1, 1), hΓ.1, rfl⟩,
    ?_⟩, hgen, f, ⟨hf 1 1 hΓ.1, ?_⟩, fun x hx => hf x (f₀ x) (hΓmax.prop.1 ⟨hx, rfl⟩)⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(p.1⁻¹, p.2⁻¹), hΓ.2.1 p hp, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ ⟨r, hr, hrpq⟩
    rw [← hrpq, hf r.1 r.2 hr, hf p.1 p.2 hp, hf q.1 q.2 hq]
    exact hΓ.2.2 p hp q hq r hr hrpq.symm


/-! ## Obstructions give nontrivial kernels (Lemma 5.2) -/

/-- **Lemma 5.2.** If every element of `K` has a square root and the local map
`f₀ : X₀ → K` on a domain `X₀` is an obstruction (no homomorphism `G → K`
extends it), then `P(G)` fails. -/
theorem not_smithP_of_obstruction (hK : ∀ k : K, ∃ r, r ^ 2 = k) {X₀ : Set G} (hX₀ : IsDom X₀)
    {f₀ : G → K} (hf₀ : IsLocal X₀ f₀) (hobs : ∀ φ : G →* K, ¬ Set.EqOn φ f₀ X₀) :
    ¬ SmithP G := by
  intro hP
  obtain ⟨X, hX₀X, hX, hgen, f, hf, hff₀⟩ := exists_isLocal_generating hK hX₀ hf₀
  let e : U X ≃* G := MulEquiv.ofBijective (evalU X) ⟨hP X hX hgen, surjective_evalU hgen⟩
  refine hobs ((toU X f hf).comp e.symm.toMonoidHom) (fun x hx => ?_)
  have he : e.symm x = PresentedGroup.of ⟨x, hX₀X hx⟩ :=
    e.symm_apply_eq.2 (evalU_of X ⟨x, hX₀X hx⟩).symm
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, he, toU_of]
  exact hff₀ hx

/-! ## Local maps on small domains -/

open scoped Classical in
/-- The map on `{1, c, c⁻¹}` sending `c ↦ l` and `c⁻¹ ↦ l⁻¹`, and every
other element to `1`. -/
noncomputable def cyc (c : G) (l : K) : G → K :=
  fun g => if g = c then l else if g = c⁻¹ then l⁻¹ else 1

/-- `{1, c, c⁻¹}` is a domain. -/
theorem isDom_cyc (c : G) : IsDom ({1, c, c⁻¹} : Set G) := by
  refine ⟨Set.mem_insert _ _, ?_⟩
  rintro x (rfl | rfl | rfl) <;> simp

/-- The relations visible in `D_c = {1, c, c⁻¹}` (Theorem 5.4, proof): `c ↦ l` is
local on `D_c` provided `l² = 1` when `c² = 1` and `l³ = 1` when `c³ = 1`. -/
theorem isLocal_cyc {c : G} (hc : c ≠ 1) (l : K) (h2 : c ^ 2 = 1 → l ^ 2 = 1)
    (h3 : c ^ 3 = 1 → l ^ 3 = 1) : IsLocal ({1, c, c⁻¹} : Set G) (cyc c l) := by
  have h1c : (1 : G) ≠ c := Ne.symm hc
  have h1c' : (1 : G) ≠ c⁻¹ := by simpa [eq_comm] using hc
  have hone : cyc c l 1 = 1 := by simp [cyc, h1c, h1c']
  refine ⟨hone, ?_⟩
  have hcl : cyc c l c = l := by simp [cyc]
  have hsq : c * c ≠ c := fun h => hc (by simpa using h)
  have hinvl : c⁻¹ = c → cyc c l c⁻¹ = l := fun h => by rw [h, hcl]
  have hinvr : c⁻¹ ≠ c → cyc c l c⁻¹ = l⁻¹ := fun h => by simp [cyc, h]
  have hinvsq : c⁻¹ = c → l * l = 1 := fun h => by
    rw [← pow_two]
    exact h2 (by rw [pow_two]; nth_rewrite 2 [← h]; exact mul_inv_cancel c)
  rintro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx | hx <;> subst x <;> rcases hy with hy | hy | hy <;> subst y
  all_goals try simp only [one_mul, mul_one, hone]
  · -- c * c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
    rw [hcl]
    rcases hxy with h | h | h
    · rw [h, hone, ← pow_two, h2 (by rw [pow_two, h])]
    · exact absurd h hsq
    · have hne : c⁻¹ ≠ c := fun h' => hsq (h.trans h')
      have hl3 : l ^ 3 = 1 := h3 (by rw [pow_succ, pow_two, h, inv_mul_cancel])
      rw [h, hinvr hne]
      exact (eq_inv_of_mul_eq_one_left (by rw [← hl3, pow_succ, pow_two])).symm
  · -- c * c⁻¹
    rw [mul_inv_cancel, hone, hcl]
    by_cases hne : c⁻¹ = c
    · rw [hinvl hne, hinvsq hne]
    · rw [hinvr hne, mul_inv_cancel]
  · -- c⁻¹ * c
    rw [inv_mul_cancel, hone, hcl]
    by_cases hne : c⁻¹ = c
    · rw [hinvl hne, hinvsq hne]
    · rw [hinvr hne, inv_mul_cancel]
  · -- c⁻¹ * c⁻¹
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
    by_cases hne : c⁻¹ = c
    · rw [hne, hcl]
      rcases hxy with h | h | h
      · rw [hne] at h
        rw [h, hone, hinvsq hne]
      · rw [hne] at h
        exact absurd h hsq
      · rw [hne] at h
        exact absurd h hsq
    · rw [hinvr hne]
      rcases hxy with h | h | h
      · have hc2 : c ^ 2 = 1 := by
          rw [pow_two, ← inv_inj, mul_inv_rev, h, inv_one]
        rw [h, hone, ← mul_inv_rev, ← pow_two, h2 hc2, inv_one]
      · have hl3 : l ^ 3 = 1 := h3 (by
          calc c ^ 3 = c * c * c := by rw [pow_succ, pow_two]
            _ = c * c * (c⁻¹ * c⁻¹) := by rw [h]
            _ = 1 := by group)
        rw [h, hcl, ← mul_inv_rev]
        exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc, ← hl3, pow_succ, pow_two])
      · exact absurd (by simpa using h) hc

open scoped Classical in
/-- The map equal to `f` on `X` and to `g` elsewhere. -/
noncomputable def glue (X : Set G) (f g : G → K) : G → K := fun z => if z ∈ X then f z else g z

/-- The union of two domains is a domain. -/
theorem isDom_union {X Y : Set G} (hX : IsDom X) (hY : IsDom Y) : IsDom (X ∪ Y) :=
  ⟨Or.inl hX.1, fun x hx => hx.elim (fun h => Or.inl (hX.2 x h)) (fun h => Or.inr (hY.2 x h))⟩

/-- Gluing local maps on two domains `X`, `Y` that meet each other's generated
subgroups only in `1` gives a local map on `X ∪ Y`: no mixed product of
nontrivial elements lies in `X ∪ Y`. -/
theorem isLocal_glue {X Y : Set G} {f g : G → K} (hX : IsDom X) (hY : IsDom Y)
    (hf : IsLocal X f) (hg : IsLocal Y g)
    (hXY : ∀ y ∈ Y, y ∈ Subgroup.closure X → y = 1)
    (hYX : ∀ x ∈ X, x ∈ Subgroup.closure Y → x = 1) : IsLocal (X ∪ Y) (glue X f g) := by
  have sc : ∀ {S : Set G} {z : G}, z ∈ S → z ∈ Subgroup.closure S :=
    fun h => Subgroup.subset_closure h
  have hFX : ∀ x ∈ X, glue X f g x = f x := fun x hx => by simp [glue, hx]
  have hFY : ∀ y ∈ Y, glue X f g y = g y := by
    intro y hy
    by_cases hyX : y ∈ X
    · have h1 : y = 1 := hXY y hy (sc hyX)
      rw [hFX y hyX, h1, hf.1, hg.1]
    · simp [glue, hyX]
  have hF1 : glue X f g 1 = 1 := by rw [hFX 1 hX.1, hf.1]
  refine ⟨hF1, ?_⟩
  intro x hx y hy hxy
  by_cases hx1 : x = 1
  · subst hx1
    rw [one_mul, hF1, one_mul]
  by_cases hy1 : y = 1
  · subst hy1
    rw [mul_one, hF1, mul_one]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hxyX : x * y ∈ X := by
      rcases hxy with h | h
      · exact h
      · rw [hXY _ h (Subgroup.mul_mem _ (sc hx) (sc hy))]
        exact hX.1
    rw [hFX _ hxyX, hFX _ hx, hFX _ hy]
    exact hf.2 x hx y hy hxyX
  · exfalso
    rcases hxy with h | h
    · refine hy1 (hXY y hy ?_)
      rw [show y = x⁻¹ * (x * y) by group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (sc hx)) (sc h)
    · refine hx1 (hYX x hx ?_)
      rw [show x = (x * y) * y⁻¹ by group]
      exact Subgroup.mul_mem _ (sc h) (Subgroup.inv_mem _ (sc hy))
  · exfalso
    rcases hxy with h | h
    · refine hx1 (hXY x hx ?_)
      rw [show x = (x * y) * y⁻¹ by group]
      exact Subgroup.mul_mem _ (sc h) (Subgroup.inv_mem _ (sc hy))
    · refine hy1 (hYX y hy ?_)
      rw [show y = x⁻¹ * (x * y) by group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (sc hx)) (sc h)
  · have hxyY : x * y ∈ Y := by
      rcases hxy with h | h
      · rw [hYX _ h (Subgroup.mul_mem _ (sc hx) (sc hy))]
        exact hY.1
      · exact h
    rw [hFY _ hxyY, hFY _ hx, hFY _ hy]
    exact hg.2 x hx y hy hxyY

/-! ## Targets with square roots (Lemma 5.3) -/

/-- Every element of `ℂˣ` has a square root. -/
theorem units_complex_exists_sq (k : ℂˣ) : ∃ r : ℂˣ, r ^ 2 = k := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (k : ℂ) two_pos
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← hz]; ring)
  exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩

/-- A primitive cube root of unity `ω`, with `1 + ω + ω² = 0`. -/
theorem exists_cube_root_unity : ∃ ω : ℂ, ω ≠ 1 ∧ ω ^ 3 = 1 ∧ 1 + ω + ω ^ 2 = 0 := by
  have hω := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  set ω := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  refine ⟨ω, h1, h3, ?_⟩
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h1)

/-- The affine group of the complex line, `z ↦ a z + b` with `a ≠ 0`. -/
@[ext]
structure Aff where
  /-- The multiplier `a`. -/
  a : ℂˣ
  /-- The translation part `b`. -/
  b : ℂ

/-- Composition of affine maps: `h_{a,b} ∘ h_{c,d} = h_{ac, ad+b}`. -/
instance : Group Aff where
  mul p q := ⟨p.a * q.a, p.a * q.b + p.b⟩
  one := ⟨1, 0⟩
  inv p := ⟨p.a⁻¹, -((p.a⁻¹ : ℂˣ) * p.b)⟩
  mul_assoc p q r := by
    ext
    · exact mul_assoc _ _ _
    · show ((p.a * q.a : ℂˣ) : ℂ) * r.b + (p.a * q.b + p.b) = p.a * (q.a * r.b + q.b) + p.b
      push_cast; ring
  one_mul p := by
    ext
    · exact one_mul _
    · show ((1 : ℂˣ) : ℂ) * p.b + 0 = p.b
      simp
  mul_one p := by
    ext
    · exact mul_one _
    · show (p.a : ℂ) * 0 + p.b = p.b
      simp
  inv_mul_cancel p := by
    ext
    · show ((p.a⁻¹ * p.a : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [inv_mul_cancel]
    · show ((p.a⁻¹ : ℂˣ) : ℂ) * p.b + -((p.a⁻¹ : ℂˣ) * p.b) = 0
      ring

/-- The product formula in `Aff`. -/
theorem Aff.mul_def (p q : Aff) : p * q = ⟨p.a * q.a, p.a * q.b + p.b⟩ := rfl

/-- The identity of `Aff` is `z ↦ z`. -/
theorem Aff.one_def : (1 : Aff) = ⟨1, 0⟩ := rfl

/-- **Lemma 5.3** (square roots): every element of `Aff` has a square root,
`q(z) = u z + b / (u + 1)` with `u² = a`, `u ≠ -1`. -/
theorem Aff.exists_sq (h : Aff) : ∃ r : Aff, r ^ 2 = h := by
  obtain ⟨u₀, hu₀⟩ := units_complex_exists_sq h.a
  obtain ⟨u, hu, hu1⟩ : ∃ u : ℂˣ, u ^ 2 = h.a ∧ (u : ℂ) + 1 ≠ 0 := by
    by_cases hc : (u₀ : ℂ) + 1 = 0
    · refine ⟨-u₀, by rw [neg_sq, hu₀], ?_⟩
      push_cast
      intro h'
      have : (2 : ℂ) = 0 := by linear_combination h' + hc
      norm_num at this
    · exact ⟨u₀, hu₀, hc⟩
  refine ⟨⟨u, h.b / (u + 1)⟩, ?_⟩
  rw [pow_two, Aff.mul_def]
  ext
  · rw [← hu]
    push_cast
    ring
  · show (u : ℂ) * (h.b / (u + 1)) + h.b / (u + 1) = h.b
    field_simp

/-! ## The four obstructions (Theorem 5.4) -/

/-- The subgroup generated by `{1, c, c⁻¹}` is `⟨c⟩`. -/
theorem closure_dom_cyc (c : G) :
    Subgroup.closure ({1, c, c⁻¹} : Set G) = Subgroup.zpowers c := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers x
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

/-- If `x² = 1` or `x³ = 1`, then every power of `x` lies in `{1, x, x⁻¹}`. -/
theorem zpow_mem_dom_cyc {x : G} (hx : x ^ 2 = 1 ∨ x ^ 3 = 1) (k : ℤ) :
    x ^ k ∈ ({1, x, x⁻¹} : Set G) := by
  rcases hx with hx | hx
  · have hx' : x ^ (2 : ℤ) = 1 := by exact_mod_cast hx
    rw [zpow_eq_zpow_emod k hx']
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  · have hx' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
    rw [zpow_eq_zpow_emod k hx']
    obtain ⟨r, hr⟩ : ∃ r, r = k % 3 := ⟨_, rfl⟩
    have h0 : 0 ≤ r := hr ▸ Int.emod_nonneg k (by norm_num)
    have h1 : r < 3 := hr ▸ Int.emod_lt_of_pos k (by norm_num)
    rw [← hr]
    interval_cases r
    · simp
    · simp
    · have h2 : x ^ (2 : ℤ) = x⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
        exact hx'
      rw [h2]
      simp

omit [Group G] [Group K] in
/-- Off the left domain, the glued map takes the right-hand values. -/
theorem glue_of_notMem {X : Set G} {f g : G → K} {y : G} (hy : y ∉ X) :
    glue X f g y = g y := by
  simp [glue, hy]

omit [Group G] [Group K] in
/-- On the left domain, the glued map takes the left-hand values. -/
theorem glue_of_mem {X : Set G} {f g : G → K} {x : G} (hx : x ∈ X) :
    glue X f g x = f x := by
  simp [glue, hx]

/-- `cyc c l` sends `c` to `l`. -/
theorem cyc_self (c : G) (l : K) : cyc c l c = l := by
  simp [cyc]

/-- **Case 3 of Theorem 5.4** (an element of infinite order).  With the domain
`{1, s^{±2}, s^{±3}}` and the local map `s^{±2} ↦ -1`, `s^{±3} ↦ 1` into `ℂˣ`,
`P(G)` fails. -/
theorem not_smithP_of_not_isOfFinOrder {s : G} (hs : ¬ IsOfFinOrder s) : ¬ SmithP G := by
  have hinj : Function.Injective (fun n : ℤ => s ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.2 hs
  have hpow : ∀ m n : ℤ, s ^ m = s ^ n → m = n := fun m n h => hinj h
  have hne : ∀ n : ℤ, n ≠ 0 → s ^ n ≠ 1 := fun n hn h => hn (hpow n 0 (by simpa using h))
  set D₂ : Set G := {1, s ^ (2 : ℤ), (s ^ (2 : ℤ))⁻¹} with hD₂
  set D₃ : Set G := {1, s ^ (3 : ℤ), (s ^ (3 : ℤ))⁻¹} with hD₃
  have hloc₂ : IsLocal D₂ (cyc (s ^ (2 : ℤ)) (-1 : ℂˣ)) :=
    isLocal_cyc (hne 2 (by norm_num)) (-1 : ℂˣ) (fun _ => by simp)
      (fun h => absurd (by rw [← zpow_natCast, ← zpow_mul] at h; exact h) (hne 6 (by norm_num)))
  have hloc₃ : IsLocal D₃ (cyc (s ^ (3 : ℤ)) (1 : ℂˣ)) :=
    isLocal_cyc (hne 3 (by norm_num)) (1 : ℂˣ) (fun _ => one_pow _) (fun _ => one_pow _)
  have hmemz : ∀ a b : ℤ, s ^ a ∈ Subgroup.zpowers (s ^ b) → b ∣ a := by
    intro a b h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [← zpow_mul] at hk
    exact ⟨k, (hpow _ _ hk).symm⟩
  have h23 : ∀ y ∈ D₃, y ∈ Subgroup.closure D₂ → y = 1 := by
    rw [closure_dom_cyc]
    rintro y (rfl | rfl | rfl) hy
    · rfl
    · exact absurd (hmemz 3 2 hy) (by decide)
    · rw [← zpow_neg] at hy
      exact absurd (hmemz (-3) 2 hy) (by decide)
  have h32 : ∀ x ∈ D₂, x ∈ Subgroup.closure D₃ → x = 1 := by
    rw [closure_dom_cyc]
    rintro x (rfl | rfl | rfl) hx
    · rfl
    · exact absurd (hmemz 2 3 hx) (by decide)
    · rw [← zpow_neg] at hx
      exact absurd (hmemz (-2) 3 hx) (by decide)
  refine not_smithP_of_obstruction units_complex_exists_sq
    (isDom_union (isDom_cyc _) (isDom_cyc _))
    (isLocal_glue (isDom_cyc _) (isDom_cyc _) hloc₂ hloc₃ h23 h32) ?_
  intro φ hφ
  have hs2 : φ (s ^ (2 : ℤ)) = -1 := by
    have h := hφ (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) :
      s ^ (2 : ℤ) ∈ D₂ ∪ D₃)
    rw [h, glue_of_mem (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), cyc_self]
  have hs3 : φ (s ^ (3 : ℤ)) = 1 := by
    have h3D₂ : s ^ (3 : ℤ) ∉ D₂ := fun h =>
      hne 3 (by norm_num) (h23 _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Subgroup.subset_closure h))
    have h := hφ (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) :
      s ^ (3 : ℤ) ∈ D₂ ∪ D₃)
    rw [h, glue_of_notMem h3D₂, cyc_self]
  rw [map_zpow] at hs2 hs3
  have h2 : ((φ s : ℂˣ) : ℂ) ^ 2 = -1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hs2
    simpa using this
  have h3 : ((φ s : ℂˣ) : ℂ) ^ 3 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hs3
    simpa using this
  have hu : ((φ s : ℂˣ) : ℂ) = -1 := by linear_combination -h3 + (φ s : ℂ) * h2
  rw [hu] at h2
  norm_num at h2

/-- **Case 2 of Theorem 5.4** (an element of finite order `n ≥ 4`, i.e. with
`s² ≠ 1` and `s³ ≠ 1`).  The local map `s ↦ 2`, `s⁻¹ ↦ 2⁻¹` into `ℂˣ` on
`{1, s, s⁻¹}` is an obstruction, so `P(G)` fails. -/
theorem not_smithP_of_isOfFinOrder {s : G} (hfin : IsOfFinOrder s) (h2 : s ^ 2 ≠ 1)
    (h3 : s ^ 3 ≠ 1) : ¬ SmithP G := by
  let two : ℂˣ := Units.mk0 2 two_ne_zero
  have hs1 : s ≠ 1 := fun h => h2 (by rw [h, one_pow])
  refine not_smithP_of_obstruction units_complex_exists_sq (isDom_cyc s)
    (isLocal_cyc hs1 two (fun h => absurd h h2) (fun h => absurd h h3)) ?_
  intro φ hφ
  have hφs : φ s = two := by
    rw [hφ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), cyc_self]
  have hn := hfin.orderOf_pos
  have hpow : two ^ orderOf s = 1 := by
    rw [← hφs, ← map_pow, pow_orderOf_eq_one, map_one]
  have hC : (2 : ℂ) ^ orderOf s = 1 := by
    simpa [two] using congrArg (fun u : ℂˣ => (u : ℂ)) hpow
  have hR : (2 : ℝ) ^ orderOf s = 1 := by exact_mod_cast hC
  exact absurd hR (one_lt_pow₀ (by norm_num) hn.ne').ne'

/-- For `x ≠ 1` with `x² = 1` or `x³ = 1` there is a unit `l ≠ 1` of `ℂ`
satisfying the corresponding relation (`l = -1` or a primitive cube root of
unity). -/
theorem exists_unit_of_small {x : G} (hx1 : x ≠ 1) (hx : x ^ 2 = 1 ∨ x ^ 3 = 1) :
    ∃ l : ℂˣ, (l : ℂ) ≠ 1 ∧ (x ^ 2 = 1 → l ^ 2 = 1 ∧ (l : ℂ) + 1 = 0) ∧
      (x ^ 3 = 1 → l ^ 3 = 1 ∧ 1 + (l : ℂ) + (l : ℂ) ^ 2 = 0) := by
  by_cases h : x ^ 2 = 1
  · refine ⟨-1, by norm_num, fun _ => ⟨by simp, by simp⟩, fun h3 => absurd ?_ hx1⟩
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h]; group
  · have h3 := hx.resolve_left h
    obtain ⟨ω, hω1, hω3, hωs⟩ := exists_cube_root_unity
    have hω0 : ω ≠ 0 := by
      rintro rfl
      norm_num at hω3
    refine ⟨Units.mk0 ω hω0, hω1, fun h' => absurd h' h, fun _ => ⟨?_, hωs⟩⟩
    exact Units.ext (by simpa using hω3)

/-- **Case 1 of Theorem 5.4** (`G` nonabelian), under the standing assumption
of that stage of the case split that every element satisfies `x² = 1` or
`x³ = 1`.  A nontrivial commutator `c` gives the obstruction `c ↦ l ≠ 1` into
the abelian group `ℂˣ`. -/
theorem not_smithP_of_not_commute {g h : G} (hgh : g * h ≠ h * g)
    (hsmall : ∀ x : G, x ^ 2 = 1 ∨ x ^ 3 = 1) : ¬ SmithP G := by
  set c : G := g * h * g⁻¹ * h⁻¹ with hc_def
  have hc : c ≠ 1 := by
    intro hc
    apply hgh
    have h1 : g * h * g⁻¹ = h := mul_inv_eq_one.1 hc
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨l, hl1, hl2, hl3⟩ := exists_unit_of_small hc (hsmall c)
  refine not_smithP_of_obstruction units_complex_exists_sq (isDom_cyc c)
    (isLocal_cyc hc l (fun h2 => (hl2 h2).1) (fun h3 => (hl3 h3).1)) ?_
  intro φ hφ
  have hφc : φ c = l := by
    rw [hφ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), cyc_self]
  have hφc1 : φ c = 1 := by
    rw [hc_def, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (φ g) (φ h)]
    group
  apply hl1
  rw [← hφc, hφc1, Units.val_one]

/-- **Case 4 of Theorem 5.4** (`G` abelian, every element satisfies `x² = 1`
or `x³ = 1`, and `G` is not of order at most three).  Two elements `a, b`
with `b ∉ {1, a, a⁻¹}` go to the noncommuting affine maps `z ↦ λ_a z` and
`z ↦ λ_b z + 1`. -/
theorem not_smithP_of_commutative (hcomm : ∀ x y : G, x * y = y * x)
    (hsmall : ∀ x : G, x ^ 2 = 1 ∨ x ^ 3 = 1) (hbig : ¬ (Finite G ∧ Nat.card G ≤ 3)) :
    ¬ SmithP G := by
  obtain ⟨a, ha1⟩ : ∃ a : G, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton G := ⟨fun x y => (h x).trans (h y).symm⟩
    have : Finite G := Finite.of_subsingleton
    exact hbig ⟨this, (Finite.card_le_one_iff_subsingleton.2 inferInstance).trans (by norm_num)⟩
  set Da : Set G := {1, a, a⁻¹} with hDa
  obtain ⟨b, hb⟩ : ∃ b : G, b ∉ Da := by
    by_contra h
    push Not at h
    have hfin : (Set.univ : Set G).Finite := (Set.toFinite Da).subset (fun x _ => h x)
    have : Finite G := Set.finite_univ_iff.1 hfin
    refine hbig ⟨this, ?_⟩
    rw [← Set.ncard_univ]
    calc (Set.univ : Set G).ncard ≤ Da.ncard :=
          Set.ncard_le_ncard (fun x _ => h x) (Set.toFinite Da)
      _ ≤ 3 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
          rw [Set.ncard_singleton]
  set Db : Set G := {1, b, b⁻¹} with hDb
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Set.mem_insert _ _)
  have haDb : a ∉ Db := by
    rintro (h | h | h)
    · exact ha1 h
    · exact hb (h ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff] at h
      exact hb (by
        rw [show b = a⁻¹ by rw [h, inv_inv]]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  obtain ⟨la, hla1, hla2, hla3⟩ := exists_unit_of_small ha1 (hsmall a)
  obtain ⟨lb, -, hlb2, hlb3⟩ := exists_unit_of_small hb1 (hsmall b)
  let A : Aff := ⟨la, 0⟩
  let B : Aff := ⟨lb, 1⟩
  have hA : IsLocal Da (cyc a A) := by
    refine isLocal_cyc ha1 A (fun h2 => ?_) (fun h3 => ?_)
    · rw [pow_two]
      refine Aff.ext (Units.ext ?_) (by simp [A, Aff.mul_def, Aff.one_def])
      simpa [A, Aff.mul_def, Aff.one_def, pow_two] using congrArg Units.val (hla2 h2).1
    · rw [pow_succ, pow_two]
      refine Aff.ext (Units.ext ?_) (by simp [A, Aff.mul_def, Aff.one_def])
      simpa [A, Aff.mul_def, Aff.one_def, pow_succ, pow_two] using
        congrArg Units.val (hla3 h3).1
  have hB : IsLocal Db (cyc b B) := by
    refine isLocal_cyc hb1 B (fun h2 => ?_) (fun h3 => ?_)
    · rw [pow_two]
      refine Aff.ext (Units.ext ?_) ?_
      · simpa [B, Aff.mul_def, Aff.one_def, pow_two] using congrArg Units.val (hlb2 h2).1
      · simpa [B, Aff.mul_def, Aff.one_def] using (hlb2 h2).2
    · rw [pow_succ, pow_two]
      refine Aff.ext (Units.ext ?_) ?_
      · simpa [B, Aff.mul_def, Aff.one_def, pow_succ, pow_two] using
          congrArg Units.val (hlb3 h3).1
      · simp only [B, Aff.mul_def, Aff.one_def, Units.val_mul]
        linear_combination (hlb3 h3).2
  have hab : ∀ y ∈ Db, y ∈ Subgroup.closure Da → y = 1 := by
    rw [closure_dom_cyc]
    rintro y (rfl | rfl | rfl) hy
    · rfl
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact absurd (hk ▸ zpow_mem_dom_cyc (hsmall a) k) hb
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.inv_mem _ hy)
      rw [inv_inv] at hk
      exact absurd (hk ▸ zpow_mem_dom_cyc (hsmall a) k) hb
  have hba : ∀ x ∈ Da, x ∈ Subgroup.closure Db → x = 1 := by
    rw [closure_dom_cyc]
    rintro x (rfl | rfl | rfl) hx
    · rfl
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact absurd (hk ▸ zpow_mem_dom_cyc (hsmall b) k) haDb
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.inv_mem _ hx)
      rw [inv_inv] at hk
      exact absurd (hk ▸ zpow_mem_dom_cyc (hsmall b) k) haDb
  refine not_smithP_of_obstruction Aff.exists_sq (isDom_union (isDom_cyc a) (isDom_cyc b))
    (isLocal_glue (isDom_cyc a) (isDom_cyc b) hA hB hab hba) ?_
  intro φ hφ
  have hφa : φ a = A := by
    have ha : a ∈ Da := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    rw [hφ (Or.inl ha), glue_of_mem ha, cyc_self]
  have hφb : φ b = B := by
    rw [hφ (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert _ _))), glue_of_notMem hb, cyc_self]
  have hAB : A * B = B * A := by rw [← hφa, ← hφb, ← map_mul, ← map_mul, hcomm]
  have hb' := congrArg Aff.b hAB
  simp only [A, B, Aff.mul_def, mul_one, add_zero, mul_zero, zero_add] at hb'
  exact hla1 hb'

/-! ## The converse: groups of order at most three (proof of Theorem 1.1) -/

/-- In a finite group of order at most three, every generating domain is the
whole group. -/
theorem mem_of_isDom_of_closure_eq_top [Finite G] (hcard : Nat.card G ≤ 3) {X : Set G}
    (hX : IsDom X) (hgen : Subgroup.closure X = ⊤) (g : G) : g ∈ X := by
  by_contra hg
  by_cases hX1 : ∀ x ∈ X, x = 1
  · have hbot : Subgroup.closure X ≤ ⊥ :=
      (Subgroup.closure_le _).2 (fun x hx => Subgroup.mem_bot.2 (hX1 x hx))
    rw [hgen] at hbot
    have hg1 : g = 1 := Subgroup.mem_bot.1 (hbot (Subgroup.mem_top g))
    exact hg (hg1 ▸ hX.1)
  push Not at hX1
  obtain ⟨x, hxX, hx1⟩ := hX1
  have hdvd : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hord : orderOf x = Nat.card G ∧ (orderOf x = 2 ∨ orderOf x = 3) := by
    obtain ⟨n, hn⟩ : ∃ n, n = Nat.card G := ⟨_, rfl⟩
    rw [← hn] at hdvd hcard hpos ⊢
    interval_cases n
    · exact absurd (Nat.dvd_one.1 hdvd) hne1
    · have := (Nat.dvd_prime Nat.prime_two).1 hdvd
      omega
    · have := (Nat.dvd_prime Nat.prime_three).1 hdvd
      omega
  have hsmall : x ^ 2 = 1 ∨ x ^ 3 = 1 := by
    rcases hord.2 with h | h
    · left
      rw [← h]
      exact pow_orderOf_eq_one x
    · right
      rw [← h]
      exact pow_orderOf_eq_one x
  have htop : Subgroup.zpowers x = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord.1])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top g)
  have hgD : g ∈ ({1, x, x⁻¹} : Set G) := hk ▸ zpow_mem_dom_cyc hsmall k
  rcases hgD with h | h | h
  · exact hg (h ▸ hX.1)
  · exact hg (h ▸ hxX)
  · rw [Set.mem_singleton_iff] at h
    exact hg (h ▸ hX.2 x hxX)

/-- If the domain `X` is all of `G`, then `π_X` is injective: `g ↦ [g]` is a
homomorphism `G → U(X)` left inverse to `π_X`. -/
theorem injective_evalU_of_forall_mem {X : Set G} (hall : ∀ g, g ∈ X) :
    Function.Injective (evalU X) := by
  let σ : G →* U X :=
    { toFun := fun g => PresentedGroup.of ⟨g, hall g⟩
      map_one' := PresentedGroup.one_of_mem (Or.inr ⟨hall 1, rfl⟩)
      map_mul' := fun x y => by
        have hr : FreeGroup.of (⟨x, hall x⟩ : X) * FreeGroup.of ⟨y, hall y⟩ *
            (FreeGroup.of ⟨x * y, hall (x * y)⟩)⁻¹ ∈ localRels X :=
          Or.inl ⟨⟨x, hall x⟩, ⟨y, hall y⟩, ⟨x * y, hall (x * y)⟩, rfl, rfl⟩
        have h1 := PresentedGroup.one_of_mem hr
        rw [map_mul, map_mul, map_inv] at h1
        exact (mul_inv_eq_one.1 h1).symm }
  have hleft : σ.comp (evalU X) = MonoidHom.id (U X) :=
    PresentedGroup.ext (fun x => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, evalU_of, MonoidHom.id_apply]
      rfl)
  intro u v huv
  have h := congrArg σ huv
  rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, hleft, MonoidHom.id_apply,
    MonoidHom.id_apply] at h

/-- Groups of order at most three satisfy `P(G)` (converse half of
Theorem 1.1). -/
theorem smithP_of_card_le_three [Finite G] (hcard : Nat.card G ≤ 3) : SmithP G :=
  fun _ hX hgen => injective_evalU_of_forall_mem (mem_of_isDom_of_closure_eq_top hcard hX hgen)

/-! ## Main theorem -/

/-- **Theorem 1.1** of arXiv:2610.10586 (Smith's 1950 conjecture).  For an
arbitrary group `G`, `P(G)` holds (every generating domain `X` has injective,
hence bijective, evaluation map `π_X : U(X) → G`) if and only if `G` is finite
of order at most three, i.e. `G ≅ 1`, `C₂` or `C₃`. -/
theorem smithP_iff : SmithP G ↔ Finite G ∧ Nat.card G ≤ 3 := by
  constructor
  · intro hP
    by_contra hbig
    by_cases hI : ∃ s : G, ¬ IsOfFinOrder s
    · obtain ⟨s, hs⟩ := hI
      exact not_smithP_of_not_isOfFinOrder hs hP
    push Not at hI
    by_cases hII : ∃ s : G, s ^ 2 ≠ 1 ∧ s ^ 3 ≠ 1
    · obtain ⟨s, h2, h3⟩ := hII
      exact not_smithP_of_isOfFinOrder (hI s) h2 h3 hP
    push Not at hII
    have hsmall : ∀ x : G, x ^ 2 = 1 ∨ x ^ 3 = 1 := fun x =>
      (em (x ^ 2 = 1)).imp id (hII x)
    by_cases hIII : ∃ g h : G, g * h ≠ h * g
    · obtain ⟨g, h, hgh⟩ := hIII
      exact not_smithP_of_not_commute hgh hsmall hP
    push Not at hIII
    exact not_smithP_of_commutative hIII hsmall hbig hP
  · rintro ⟨hfin, hcard⟩
    exact smithP_of_card_le_three hcard

/-- Paper alias for `smithP_iff` (Theorem 1.1 of arXiv:2610.10586). -/
theorem thm_1_1 : SmithP G ↔ Finite G ∧ Nat.card G ≤ 3 := smithP_iff

/-! ## Ground-truth checks on small instances -/

/-- The paper's sanity check (triage): in `C₄ = ⟨g⟩` the generating domain
`{1, g, g⁻¹}` sees no relation beyond inverses, so `[g]⁴ ≠ 1` in `U(X)`
although `π_X [g]⁴ = g⁴ = 1`.  This is checked directly from the definitions,
independently of `smithP_iff`, via the local map `g ↦ 1 ∈ ℤ` into
`Multiplicative ℤ`. -/
theorem not_injective_evalU_C4 :
    ¬ Function.Injective (evalU ({1, Multiplicative.ofAdd (1 : ZMod 4),
      (Multiplicative.ofAdd (1 : ZMod 4))⁻¹} : Set (Multiplicative (ZMod 4)))) := by
  set g : Multiplicative (ZMod 4) := Multiplicative.ofAdd 1 with hg
  set X : Set (Multiplicative (ZMod 4)) := {1, g, g⁻¹} with hX
  have hg1 : g ≠ 1 := by decide
  have hg2 : g ^ 2 ≠ 1 := by decide
  have hg3 : g ^ 3 ≠ 1 := by decide
  have hloc := isLocal_cyc hg1 (Multiplicative.ofAdd (1 : ℤ)) (fun h => absurd h hg2)
    (fun h => absurd h hg3)
  have hgX : g ∈ X := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  intro hinj
  have hev : evalU X ((PresentedGroup.of ⟨g, hgX⟩) ^ 4) = evalU X 1 := by
    rw [map_pow, evalU_of, map_one]
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 = 1)
  have h1 := congrArg (toU X _ hloc) (hinj hev)
  rw [map_one (toU X _ hloc), map_pow, toU_of, cyc_self] at h1
  exact absurd h1 (by decide)

/-- `{1, g, g⁻¹}` generates `C₄`, so `not_injective_evalU_C4` refutes `P(C₄)`
directly from the definitions. -/
theorem not_smithP_C4 : ¬ SmithP (Multiplicative (ZMod 4)) := by
  intro hP
  refine not_injective_evalU_C4 (hP _ (isDom_cyc _) ?_)
  rw [closure_dom_cyc, eq_top_iff]
  rintro x -
  refine Subgroup.mem_zpowers_iff.2 ⟨(Multiplicative.toAdd x).val, ?_⟩
  revert x
  decide

/-- `P(C₃)` holds (non-vacuity of the right-to-left direction). -/
example : SmithP (Multiplicative (ZMod 3)) :=
  smithP_iff.2 ⟨inferInstance, by simp [Nat.card_eq_fintype_card]⟩

/-- The trivial domain `{1}` is a domain, and `G` itself is one. -/
example : IsDom ({1} : Set G) ∧ IsDom (Set.univ : Set G) :=
  ⟨⟨rfl, fun x hx => by rw [Set.mem_singleton_iff.1 hx, inv_one]; rfl⟩,
    ⟨trivial, fun _ _ => trivial⟩⟩

/-- `{1, g}` with `g = 1 ∈ C₄` written additively as `ofAdd 1` is not a domain:
it is not closed under inversion. -/
example : ¬ IsDom ({1, Multiplicative.ofAdd (1 : ZMod 4)} : Set (Multiplicative (ZMod 4))) := by
  rintro ⟨-, h⟩
  have := h _ (Set.mem_insert_of_mem _ rfl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  revert this
  decide

end SmithLocalPresentation
