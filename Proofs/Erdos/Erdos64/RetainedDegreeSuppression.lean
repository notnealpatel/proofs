import Erdos.Erdos64.Basic

set_option autoImplicit false

namespace Erdos64.RetainedDegreeSuppression

open SimpleGraph

universe u
variable {V : Type u} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The carrier retained by standard suppression consists of vertices of degree at least three. -/
abbrev Retained := {x : V // 3 ≤ H.degree x}

example : (⟨0, by decide⟩ : Retained (⊤ : SimpleGraph (Fin 5))).val = 0 := rfl

/-- Standard simple suppression keeps direct edges and joins distinct retained endpoints
across a single degree-two intermediate. It does not impose a cubic degree bound. -/
def suppression : SimpleGraph (Retained H) where
  Adj x y := x ≠ y ∧ (H.Adj x.val y.val ∨
    ∃ m, H.degree m = 2 ∧ H.Adj x.val m ∧ H.Adj m y.val)
  symm := ⟨by
    intro x y h
    rcases h with ⟨hne, hd | ⟨m, hm, hxm, hmy⟩⟩
    · exact ⟨hne.symm, Or.inl hd.symm⟩
    · exact ⟨hne.symm, Or.inr ⟨m, hm, hmy.symm, hxm.symm⟩⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- The adjacency formula for standard suppression, in terms of the original graph. -/
theorem suppression_adj_iff (x y : Retained H) :
    (suppression H).Adj x y ↔ x ≠ y ∧ (H.Adj x.val y.val ∨
      ∃ m, H.degree m = 2 ∧ H.Adj x.val m ∧ H.Adj m y.val) := Iff.rfl

example : (suppression (⊤ : SimpleGraph (Fin 5))).Adj
    ⟨0, by decide⟩ ⟨1, by decide⟩ := ⟨by decide, Or.inl (by decide)⟩

/-- The retained carrier has a classical finite enumeration. -/
noncomputable instance retainedFintype : Fintype (Retained H) := Fintype.ofFinite _

private theorem mate {m x : V} (hm : H.degree m = 2) (hx : H.Adj m x) :
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

/-- Suppression gives a bijection of incident neighbors at each retained vertex when
minimum degree is two, degree-two vertices are independent, triangles are absent, and
 distinct endpoints have at most one degree-two intermediate. No connectivity is needed. -/
theorem neighbor_equiv
    (hmin : ∀ v, 2 ≤ H.degree v)
    (hind : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x : Retained H) :
    Nonempty (H.neighborSet x.val ≃ (suppression H).neighborSet x) := by
  classical
  let R : H.neighborSet x.val → (suppression H).neighborSet x → Prop := fun m y =>
    m.val = y.val.val ∨ (H.degree m.val = 2 ∧ H.Adj m.val y.val.val)
  have total (m : H.neighborSet x.val) : ∃ y, R m y := by
    by_cases hm : 3 ≤ H.degree m.val
    · let y : Retained H := ⟨m.val, hm⟩
      have hedge : (suppression H).Adj x y :=
        ⟨fun he => m.property.ne (congrArg Subtype.val he), Or.inl m.property⟩
      exact ⟨⟨y, hedge⟩, Or.inl rfl⟩
    · have hm2 : H.degree m.val = 2 := by have hlow := hmin m.val; omega
      obtain ⟨z, hz, _⟩ := mate H hm2 m.property.symm
      have hz3 : 3 ≤ H.degree z := by
        have hlow := hmin z
        have hnot : H.degree z ≠ 2 := fun he => hind m.val z hz.1 hm2 he
        omega
      let y : Retained H := ⟨z, hz3⟩
      have hedge : (suppression H).Adj x y := by
        refine ⟨?_, Or.inr ⟨m.val, hm2, m.property, hz.1⟩⟩
        intro he
        exact hz.2 (congrArg Subtype.val he).symm
      exact ⟨⟨y, hedge⟩, Or.inr ⟨hm2, hz.1⟩⟩
  have functional (m : H.neighborSet x.val) (y z : (suppression H).neighborSet x)
      (hy : R m y) (hz : R m z) : y = z := by
    apply Subtype.ext
    apply Subtype.ext
    rcases hy with hy | ⟨hm, hy⟩ <;> rcases hz with hz | ⟨hm', hz⟩
    · exact hy.symm.trans hz
    · have hge := y.val.property; rw [← hy] at hge; omega
    · have hge := z.val.property; rw [← hz] at hge; omega
    · obtain ⟨w, _, hw⟩ := mate H hm m.property.symm
      have hyx : y.val.val ≠ x.val := fun he => y.property.1 (Subtype.ext he.symm)
      have hzx : z.val.val ≠ x.val := fun he => z.property.1 (Subtype.ext he.symm)
      exact (hw _ ⟨hy, hyx⟩).trans (hw _ ⟨hz, hzx⟩).symm
  let f : H.neighborSet x.val → (suppression H).neighborSet x :=
    fun m => Classical.choose (total m)
  have spec (m : H.neighborSet x.val) : R m (f m) := Classical.choose_spec (total m)
  have inj : Function.Injective f := by
    intro m n he
    have hn : R n (f m) := he.symm ▸ spec n
    rcases spec m with hm | ⟨hm2, hmy⟩ <;> rcases hn with hn | ⟨hn2, hny⟩
    · exact Subtype.ext (hm.trans hn.symm)
    · have hxy : H.Adj x.val (f m).val.val := hm ▸ m.property
      exact False.elim (htri _ _ _ hxy hny.symm n.property.symm)
    · have hxy : H.Adj x.val (f m).val.val := hn ▸ n.property
      exact False.elim (htri _ _ _ hxy hmy.symm m.property.symm)
    · have hne : x.val ≠ (f m).val.val := fun he => (f m).property.1 (Subtype.ext he)
      exact Subtype.ext (hunique _ _ _ _ hne hm2 hn2 m.property hmy n.property hny)
  have surj : Function.Surjective f := by
    intro y
    rcases y.property.2 with hd | ⟨m, hm, hxm, hmy⟩
    · let n : H.neighborSet x.val := ⟨y.val.val, hd⟩
      exact ⟨n, functional n (f n) y (spec n) (Or.inl rfl)⟩
    · let n : H.neighborSet x.val := ⟨m, hxm⟩
      exact ⟨n, functional n (f n) y (spec n) (Or.inr ⟨hm, hmy⟩)⟩
  exact ⟨Equiv.ofBijective f ⟨inj, surj⟩⟩

/-- Standard suppression preserves the original degree of every retained vertex. -/
theorem degree_eq [DecidableRel (suppression H).Adj]
    (hmin : ∀ v, 2 ≤ H.degree v)
    (hind : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x : Retained H) : (suppression H).degree x = H.degree x.val := by
  obtain ⟨e⟩ := neighbor_equiv H hmin hind htri hunique x
  have hc := Fintype.card_congr e
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hc.symm

/-- The suppressed graph has minimum degree at least three under the structural premises. -/
theorem degree_ge_three [DecidableRel (suppression H).Adj]
    (hmin : ∀ v, 2 ≤ H.degree v)
    (hind : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hunique : ∀ a b c d, a ≠ b → H.degree c = 2 → H.degree d = 2 →
      H.Adj a c → H.Adj c b → H.Adj a d → H.Adj d b → c = d)
    (x : Retained H) : 3 ≤ (suppression H).degree x := by
  rw [degree_eq H hmin hind htri hunique x]
  exact x.property

/-- Suppression cannot increase the number of vertices. -/
theorem card_le : Fintype.card (Retained H) ≤ Fintype.card V :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- An explicit vertex of degree at least three witnesses a nonempty suppressed carrier. -/
theorem nonempty {v : V} (hv : 3 ≤ H.degree v) : Nonempty (Retained H) :=
  ⟨⟨v, hv⟩⟩

end Erdos64.RetainedDegreeSuppression
