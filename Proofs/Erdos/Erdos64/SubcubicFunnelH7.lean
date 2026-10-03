import Erdos.Erdos64.SubcubicFunnelFoundation

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- The nine undirected H7 edges in the ordering `(s,t,a,a',b,c,c')`.
This is the aligned form of the source gadget, not a claim of a source dichotomy. -/
def h7 : SimpleGraph (Fin 7) where
  Adj i j := (i, j) ∈ ([(0,2), (0,3), (2,3), (2,4), (4,5),
    (1,5), (1,6), (5,6), (3,6)] : List (Fin 7 × Fin 7)) ∨
    (j, i) ∈ ([(0,2), (0,3), (2,3), (2,4), (4,5),
    (1,5), (1,6), (5,6), (3,6)] : List (Fin 7 × Fin 7))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; fin_cases i <;> decide⟩

instance : DecidableRel h7.Adj := fun i j => inferInstanceAs (Decidable (_ ∨ _))

/-- Ground-truth bridge: H7 adjacency is exactly the specified nine unordered pairs. -/
theorem h7_adj_iff (i j : Fin 7) : h7.Adj i j ↔
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) ∨
    (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 5) ∨ (i = 1 ∧ j = 5) ∨
    (i = 1 ∧ j = 6) ∨ (i = 5 ∧ j = 6) ∨ (i = 3 ∧ j = 6) ∨
    (j = 0 ∧ i = 2) ∨ (j = 0 ∧ i = 3) ∨ (j = 2 ∧ i = 3) ∨
    (j = 2 ∧ i = 4) ∨ (j = 4 ∧ i = 5) ∨ (j = 1 ∧ i = 5) ∨
    (j = 1 ∧ i = 6) ∨ (j = 5 ∧ i = 6) ∨ (j = 3 ∧ i = 6) := by
  fin_cases i <;> fin_cases j <;> decide

/-- An induced H7 whose ordered ports zero and one are the prescribed endpoints.
A standard graph embedding preserves and reflects every adjacency. -/
def AlignedH7 (G : SimpleGraph V) (s t : V) : Prop :=
  ∃ f : h7 ↪g G, f 0 = s ∧ f 1 = t

/-- Ground-truth bridge to a seven-vertex injection with exact induced adjacency. -/
theorem alignedH7_iff : AlignedH7 G s t ↔
    ∃ f : Fin 7 → V, Function.Injective f ∧ f 0 = s ∧ f 1 = t ∧
      ∀ i j, G.Adj (f i) (f j) ↔ h7.Adj i j := by
  constructor
  · rintro ⟨f, hs, ht⟩
    exact ⟨f, f.injective, hs, ht, fun i j => f.map_rel_iff⟩
  · rintro ⟨f, hi, hs, ht, he⟩
    exact ⟨⟨⟨f, hi⟩, fun {i j} => he i j⟩, hs, ht⟩

/-- The first of the three four-edge paths that certify H7 nonfactorization. -/
def h7PathP : Path4 h7 0 1 :=
  ⟨2, 4, 5, by decide, by decide, by decide, by decide, by decide⟩

/-- The left-detour four-edge path in H7. -/
def h7PathL : Path4 h7 0 1 :=
  ⟨2, 3, 6, by decide, by decide, by decide, by decide, by decide⟩

/-- The right-detour four-edge path in H7. -/
def h7PathR : Path4 h7 0 1 :=
  ⟨3, 6, 5, by decide, by decide, by decide, by decide, by decide⟩

example : h7PathP.Internal 4 ∧ h7PathL.Internal 3 ∧ h7PathR.Internal 6 := by
  unfold Path4.Internal h7PathP h7PathL h7PathR
  decide

/-- The three displayed H7 paths have empty total internal intersection. -/
theorem h7_paths_no_common :
    ¬ ∃ z, h7PathP.Internal z ∧ h7PathL.Internal z ∧ h7PathR.Internal z := by
  unfold Path4.Internal h7PathP h7PathL h7PathR
  decide

/-- Mapping a tuple along a standard graph embedding preserves simple four-paths. -/
def Path4.map {W : Type*} {H : SimpleGraph W} (p : Path4 G s t) (f : G ↪g H) :
    Path4 H (f s) (f t) where
  first := f p.first
  middle := f p.middle
  last := f p.last
  edge₀ := f.map_rel_iff.mpr p.edge₀
  edge₁ := f.map_rel_iff.mpr p.edge₁
  edge₂ := f.map_rel_iff.mpr p.edge₂
  edge₃ := f.map_rel_iff.mpr p.edge₃
  distinct := by
    exact List.Nodup.map f.injective p.distinct

/-- Ground truth for embedding transport: internal vertices are exactly mapped
internal vertices, including the backward direction. -/
theorem Path4.map_internal_iff {W : Type*} {H : SimpleGraph W}
    (p : Path4 G s t) (f : G ↪g H) (z : W) :
    (p.map f).Internal z ↔ ∃ x, p.Internal x ∧ f x = z := by
  simp only [Path4.Internal, Path4.map]
  constructor
  · rintro (h | h | h)
    · exact ⟨p.first, Or.inl rfl, h.symm⟩
    · exact ⟨p.middle, Or.inr (Or.inl rfl), h.symm⟩
    · exact ⟨p.last, Or.inr (Or.inr rfl), h.symm⟩
  · rintro ⟨x, (rfl | rfl | rfl), h⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)

/-- An aligned induced H7 precludes a common internal vertex in the full tuple family.
Only the three explicit paths are needed for this direction. -/
theorem AlignedH7.no_common_internal (h : AlignedH7 G s t) :
    ¬ ∃ z, ∀ p : Path4 G s t, p.Internal z := by
  obtain ⟨f, rfl, rfl⟩ := h
  rintro ⟨z, hz⟩
  obtain ⟨x, hx, hfx⟩ := (h7PathP.map_internal_iff f z).mp (hz (h7PathP.map f))
  obtain ⟨y, hy, hfy⟩ := (h7PathL.map_internal_iff f z).mp (hz (h7PathL.map f))
  obtain ⟨w, hw, hfw⟩ := (h7PathR.map_internal_iff f z).mp (hz (h7PathR.map f))
  have hxy : x = y := f.injective (hfx.trans hfy.symm)
  have hxw : x = w := f.injective (hfx.trans hfw.symm)
  exact h7_paths_no_common ⟨x, hx, hxy ▸ hy, hxw ▸ hw⟩

/-- The induced-H7 alternative excludes a common internal vertex for all Mathlib
simple four-edge walks. This converse does not require degree or cycle hypotheses. -/
theorem AlignedH7.no_common_walk_internal (h : AlignedH7 G s t) :
    ¬ ∃ z, ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
      z ∈ w.support ∧ z ≠ s ∧ z ≠ t := by
  rintro ⟨z, hz⟩
  exact h.no_common_internal ⟨z, (common_internal_iff z).mpr hz⟩

/-- The H7 graph itself is an aligned induced witness. -/
theorem h7_aligned : AlignedH7 h7 0 1 := by
  exact ⟨RelEmbedding.refl _, rfl, rfl⟩

/-- The explicit H7 family is nonempty, and has no common internal vertex. -/
theorem h7_nonfactor : Nonempty (Path4 h7 0 1) ∧
    ¬ ∃ z, ∀ p : Path4 h7 0 1, p.Internal z :=
  ⟨⟨h7PathP⟩, h7_aligned.no_common_internal⟩

end Erdos64.SubcubicFunnel
