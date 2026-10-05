import Erdos.Erdos64.RetainedDegreeSuppression

/-!
# Concrete incidences of retained-vertex suppression

The equivalence below uses the unique original first edge of each suppressed
edge. It does not choose an unspecified neighbor equivalence.

The four structural premises are jointly nonvacuous: subdivide every edge of
`K₄,₄` once. The eight original vertices have degree four; the sixteen new
vertices have degree two and are independent. Every edge joins an original
vertex to a new one, so triangles are absent. Distinct endpoints have at most
one degree-two intermediate because each original edge was subdivided once.
Thus retained vertices and their incident neighbors are both nonempty; the
suppressed graph is `K₄,₄`. This is a mathematical model, not a formal fixture.
-/

set_option autoImplicit false

namespace Erdos64.RetainedSuppressionIncidence

open SimpleGraph
open Erdos64.RetainedDegreeSuppression

universe u
variable {V : Type u} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- An original incident edge starts either a direct suppressed edge or its
length-two degree-two corridor. -/
def FirstStep (x y : Retained H) (w : V) : Prop :=
  H.Adj x.val w ∧ (w = y.val ∨ (H.degree w = 2 ∧ H.Adj w y.val))

example : FirstStep (⊤ : SimpleGraph (Fin 5))
    ⟨0, by decide⟩ ⟨1, by decide⟩ 1 := ⟨by decide, Or.inl rfl⟩

/-- Triangle exclusion and corridor uniqueness determine the unique original
first step of any suppressed edge. -/
theorem existsUnique_firstStep
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x y : Retained H) (hxy : (suppression H).Adj x y) :
    ∃! w, FirstStep H x y w := by
  have hex : ∃ w, FirstStep H x y w := by
    rcases hxy.2 with hd | ⟨m, hm, hxm, hmy⟩
    · exact ⟨y.val, hd, Or.inl rfl⟩
    · exact ⟨m, hxm, Or.inr ⟨hm, hmy⟩⟩
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, hw, ?_⟩
  intro z hz
  rcases hz with ⟨hxz, hz | ⟨hz2, hzy⟩⟩ <;>
    rcases hw with ⟨hxw, hw | ⟨hw2, hwy⟩⟩
  · exact hz.trans hw.symm
  · subst z
    exact False.elim (htri _ _ _ hxz hwy.symm hxw.symm)
  · subst w
    exact False.elim (htri _ _ _ hxw hzy.symm hxz.symm)
  · exact hunique _ _ _ _ (fun he => hxy.1 (Subtype.ext he))
      hz2 hw2 hxz hzy hxw hwy

/-- The specified original neighbor underlying a suppressed edge. The choice
is from a unique first-step relation, not from an unspecified equivalence. -/
noncomputable def firstStep
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x y : Retained H) (hxy : (suppression H).Adj x y) : H.neighborSet x.val :=
  ⟨Classical.choose (existsUnique_firstStep H htri hunique x y hxy),
    (Classical.choose_spec (existsUnique_firstStep H htri hunique x y hxy)).1.1⟩

/-- The chosen neighbor satisfies the concrete first-step relation. -/
theorem firstStep_spec
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x y : Retained H) (hxy : (suppression H).Adj x y) :
    FirstStep H x y (firstStep H htri hunique x y hxy).val :=
  (Classical.choose_spec (existsUnique_firstStep H htri hunique x y hxy)).1

/-- Any concrete first-step witness equals the value chosen by `firstStep`. -/
theorem firstStep_eq_of_spec
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x y : Retained H) (hxy : (suppression H).Adj x y)
    {w : V} (hw : FirstStep H x y w) :
    (firstStep H htri hunique x y hxy).val = w :=
  ((Classical.choose_spec (existsUnique_firstStep H htri hunique x y hxy)).2 w hw).symm

private theorem degreeTwoMate {m x : V} (hm : H.degree m = 2) (hx : H.Adj m x) :
    ∃! y, H.Adj m y ∧ y ≠ x := by
  classical
  have hc : (H.neighborFinset m).card = 2 := hm
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc
  have mem_iff (z : V) : H.Adj m z ↔ z = a ∨ z = b := by
    rw [← H.mem_neighborFinset m z, hs]
    simp
  rcases (mem_iff x).mp hx with hxa | hxb
  · subst x
    refine ⟨b, ⟨(mem_iff b).mpr (Or.inr rfl), hab.symm⟩, ?_⟩
    intro z hz
    rcases (mem_iff z).mp hz.1 with hza | hzb
    · exact False.elim (hz.2 hza)
    · exact hzb
  · subst x
    refine ⟨a, ⟨(mem_iff a).mpr (Or.inl rfl), hab⟩, ?_⟩
    intro z hz
    rcases (mem_iff z).mp hz.1 with hza | hzb
    · exact hza
    · exact False.elim (hz.2 hzb)

private theorem firstStep_bijective
    (hmin : ∀ v, 2 ≤ H.degree v)
    (hind : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x : Retained H) :
    Function.Bijective (fun y : (suppression H).neighborSet x =>
      firstStep H htri hunique x y.val y.property) := by
  constructor
  · intro y z he
    have hy := firstStep_spec H htri hunique x y.val y.property
    have hz := firstStep_spec H htri hunique x z.val z.property
    have hv := congrArg Subtype.val he
    rw [← hv] at hz
    apply Subtype.ext
    apply Subtype.ext
    rcases hy.2 with hy | ⟨hm, hy⟩ <;> rcases hz.2 with hz | ⟨hm', hz⟩
    · exact hy.symm.trans hz
    · have hge := y.val.property
      rw [← hy] at hge
      have hbad : 3 ≤ 2 := hm' ▸ hge
      omega
    · have hge := z.val.property
      rw [← hz] at hge
      have hbad : 3 ≤ 2 := hm ▸ hge
      omega
    · obtain ⟨w, _, hw⟩ := degreeTwoMate H hm
        (firstStep H htri hunique x y.val y.property).property.symm
      have hyx : y.val.val ≠ x.val := fun he => y.property.1 (Subtype.ext he.symm)
      have hzx : z.val.val ≠ x.val := fun he => z.property.1 (Subtype.ext he.symm)
      exact (hw _ ⟨hy, hyx⟩).trans (hw _ ⟨hz, hzx⟩).symm
  · intro w
    by_cases hw : 3 ≤ H.degree w.val
    · let y : Retained H := ⟨w.val, hw⟩
      have hxy : (suppression H).Adj x y :=
        ⟨fun he => w.property.ne (congrArg Subtype.val he), Or.inl w.property⟩
      refine ⟨⟨y, hxy⟩, Subtype.ext ?_⟩
      exact firstStep_eq_of_spec H htri hunique x y hxy ⟨w.property, Or.inl rfl⟩
    · have hw2 : H.degree w.val = 2 := by
        have hlow := hmin w.val
        omega
      obtain ⟨z, hz, _⟩ := degreeTwoMate H hw2 w.property.symm
      have hz3 : 3 ≤ H.degree z := by
        have hlow := hmin z
        have hnot : H.degree z ≠ 2 := fun he => hind w.val z hz.1 hw2 he
        omega
      let y : Retained H := ⟨z, hz3⟩
      have hxy : (suppression H).Adj x y := by
        refine ⟨?_, Or.inr ⟨w.val, hw2, w.property, hz.1⟩⟩
        intro he
        exact hz.2 (congrArg Subtype.val he).symm
      refine ⟨⟨y, hxy⟩, Subtype.ext ?_⟩
      exact firstStep_eq_of_spec H htri hunique x y hxy
        ⟨w.property, Or.inr ⟨hw2, hz.1⟩⟩

/-- Suppressed incidences correspond to original incidences by their actual first
edge, under minimum degree two, independent degree-two vertices, triangle
exclusion, and uniqueness of degree-two corridors. -/
noncomputable def incidenceEquiv
    (hmin : ∀ v, 2 ≤ H.degree v)
    (hind : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x : Retained H) : (suppression H).neighborSet x ≃ H.neighborSet x.val :=
  Equiv.ofBijective (fun y => firstStep H htri hunique x y.val y.property)
    (firstStep_bijective H hmin hind htri hunique x)

/-- The forward incidence equivalence is precisely the specified first-step map. -/
theorem incidenceEquiv_apply
    (hmin : ∀ v, 2 ≤ H.degree v)
    (hind : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x : Retained H) (y : (suppression H).neighborSet x) :
    incidenceEquiv H hmin hind htri hunique x y =
      firstStep H htri hunique x y.val y.property := rfl

/-- Every image incidence starts the corresponding concrete original edge or
length-two corridor. -/
theorem incidenceEquiv_spec
    (hmin : ∀ v, 2 ≤ H.degree v)
    (hind : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x : Retained H) (y : (suppression H).neighborSet x) :
    FirstStep H x y.val (incidenceEquiv H hmin hind htri hunique x y).val :=
  firstStep_spec H htri hunique x y.val y.property

end Erdos64.RetainedSuppressionIncidence
