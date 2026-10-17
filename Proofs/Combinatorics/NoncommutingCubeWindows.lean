import Combinatorics.NoncommutingDenseWindow
import Combinatorics.NoncommutingProjectionHoles
import Combinatorics.NoncommutingCoveringDensity

set_option autoImplicit false

namespace NoncommutingCubeWindows

noncomputable section

open NoncommutingDense

/-- The integer interval of length `N` starting at `a` (used with `1 ≤ N`). -/
def C (a N : ℤ) : Finset ℤ := Finset.Icc a (a + N - 1)

/-- The actual overlap of two equal-sided intervals at sum parameter `s`. -/
def O (a b N s : ℤ) : Finset ℤ :=
  C a N ∩ (C b N).image (fun z => s - z)

/-- The translated normalized endpoint mark; the first translation cancels
from its source alternatives. -/
def mark (a b N s : ℤ) : ℤ := a + overlapMark N N (s - a - b)

example : C 10 1 = {10} := by decide
example : O 10 20 1 30 = {10} := by decide
example : mark 10 20 1 30 = 10 := by decide

/-- Membership in an actual overlap is given by four endpoint inequalities. -/
theorem mem_O (a b N s x : ℤ) :
    x ∈ O a b N s ↔ a ≤ x ∧ x ≤ a + N - 1 ∧ b ≤ s - x ∧ s - x ≤ b + N - 1 := by
  simp only [O, C, Finset.mem_inter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hl,hu⟩,z,⟨hzl,hzu⟩,he⟩
    exact ⟨hl,hu,by omega,by omega⟩
  · rintro ⟨hl,hu,hzl,hzu⟩
    exact ⟨⟨hl,hu⟩,s-x,⟨hzl,hzu⟩,by omega⟩

/-- Actual overlaps are translates of the normalized equal-sided overlaps. -/
theorem O_eq_image_overlap (a b N s : ℤ) :
    O a b N s = (overlap N N (s-a-b)).image (fun x => a+x) := by
  ext x
  rw [mem_O]
  simp only [Finset.mem_image, overlap, Finset.mem_inter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨x-a,⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩,by omega⟩
  · rintro ⟨y,⟨⟨h1,h2⟩,⟨h3,h4⟩⟩,he⟩
    exact ⟨by omega,by omega,by omega,by omega⟩

/-- The explicit interval endpoints of an actual overlap, including empty ones. -/
theorem O_eq_Icc (a b N s : ℤ) :
    O a b N s = Finset.Icc (max a (s-b-N+1)) (min (a+N-1) (s-b)) := by
  ext x
  simp only [mem_O, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

/-- Nonempty overlaps supply exactly the normalized parameter guards. -/
theorem O_guards (a b N s : ℤ) (h : (O a b N s).Nonempty) :
    0 ≤ s-a-b ∧ s-a-b ≤ 2*N-2 := by
  obtain ⟨x,hx⟩ := h
  rw [mem_O] at hx
  omega

/-- An actual overlap stays in its first fixed interval. -/
theorem O_subset_C (a b N s : ℤ) : O a b N s ⊆ C a N :=
  Finset.inter_subset_left

/-- In a nonempty equal-sided overlap the mark lies in the overlap itself. -/
theorem mark_mem_O (a b N s : ℤ) (hN : 1 ≤ N) (h : (O a b N s).Nonempty) :
    mark a b N s ∈ O a b N s := by
  obtain ⟨hl,hu⟩ := O_guards a b N s h
  have hg := (overlapWindow_geometry N N (s-a-b) hN hN hl (by omega)).2.1
  rw [overlapWindow_eq_overlap_of_eq_sides] at hg
  rw [O_eq_image_overlap]
  exact Finset.mem_image_of_mem (fun x => a+x) hg

/-- Negating a length-`N` interval gives the signed grid with start `-a-N+1`. -/
theorem neg_C (a N : ℤ) :
    (C a N).image Neg.neg = C (-a-N+1) N := by
  ext x
  simp only [C, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y,⟨hl,hu⟩,he⟩
    change -y = x at he
    omega
  · rintro ⟨hl,hu⟩
    exact ⟨-x,⟨by omega,by omega⟩,by simp⟩

/-- A translated mark has sources `q+b` or `q+b+N-1`, with no `a` term. -/
theorem mark_sources (a b N s q : ℤ) (h : mark a b N s = q) :
    s = q+b ∨ s = q+b+N-1 := by
  have hn : overlapMark N N (s-a-b) = q-a := by
    unfold mark at h
    omega
  have hs := overlapMark_sources N N (s-a-b) (q-a) hn
  omega

/-- The actual two-coordinate mark map has at most four preimages in any
finite set of source pairs. No reflection multiplicity is charged. -/
theorem card_mark_pair_fiber_le_four (a b c d N : ℤ) (q : ℤ × ℤ)
    (T : Finset (ℤ × ℤ)) :
    (T.filter (fun p => (mark a b N p.1, mark c d N p.2) = q)).card ≤ 4 := by
  have hsub : T.filter (fun p => (mark a b N p.1, mark c d N p.2) = q) ⊆
      ({q.1+b,q.1+b+N-1} ×ˢ {q.2+d,q.2+d+N-1}) := by
    intro p hp
    have he := (Finset.mem_filter.mp hp).2
    have h1 := mark_sources a b N p.1 q.1 (congrArg Prod.fst he)
    have h2 := mark_sources c d N p.2 q.2 (congrArg Prod.snd he)
    simpa only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] using And.intro h1 h2
  have c1 : ({q.1+b,q.1+b+N-1} : Finset ℤ).card ≤ 2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  have c2 : ({q.2+d,q.2+d+N-1} : Finset ℤ).card ≤ 2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ = _ := Finset.card_product _ _
    _ ≤ 4 := by nlinarith

/-- A dense actual rectangle certificate keeps its two nonempty integer
interval factors in the same signed grid and its mark in the rectangle.
The hole set is not enlarged or transported. -/
def RectangleCertificate (X Y : Finset ℤ) (H : Finset (ℤ × ℤ))
    (U V : Finset ℤ) (p : ℤ × ℤ) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧
  (∃ l u : ℤ, l ≤ u ∧ X = Finset.Icc l u) ∧
  (∃ l u : ℤ, l ≤ u ∧ Y = Finset.Icc l u) ∧
  X ⊆ U ∧ Y ⊆ V ∧ p ∈ X ×ˢ Y ∧
  (X ×ˢ Y).card ≤ 3 * (H ∩ (X ×ˢ Y)).card

example : RectangleCertificate {10} {20} {(10,20)} {10} {20} (10,20) := by
  refine ⟨by decide, by decide, ⟨10,10,by decide,by decide⟩,
    ⟨20,20,by decide,by decide⟩,by decide,by decide,by decide,by decide⟩

/-- A nonempty overlap has ordered explicit max/min interval endpoints. -/
theorem O_interval (a b N s : ℤ) (h : (O a b N s).Nonempty) :
    max a (s-b-N+1) ≤ min (a+N-1) (s-b) ∧
    O a b N s = Finset.Icc (max a (s-b-N+1)) (min (a+N-1) (s-b)) := by
  refine ⟨?_, O_eq_Icc a b N s⟩
  obtain ⟨x,hx⟩ := h
  rw [O_eq_Icc, Finset.mem_Icc] at hx
  exact hx.1.trans hx.2

/-- Equal-sided overlap geometry converts actual density to an interval
certificate in the original fixed grid, with no area loss. -/
theorem certificate_of_density (a b c d N s t : ℤ) (H : Finset (ℤ × ℤ))
    (hN : 1 ≤ N) (hs : (O a b N s).Nonempty) (ht : (O c d N t).Nonempty)
    (hd : ((O a b N s) ×ˢ (O c d N t)).card ≤
      3 * (H ∩ ((O a b N s) ×ˢ (O c d N t))).card) :
    RectangleCertificate (O a b N s) (O c d N t) H (C a N) (C c N)
      (mark a b N s, mark c d N t) := by
  obtain ⟨hlo,he⟩ := O_interval a b N s hs
  obtain ⟨hlo',he'⟩ := O_interval c d N t ht
  exact ⟨hs,ht,⟨_,_,hlo,he⟩,⟨_,_,hlo',he'⟩,
    O_subset_C a b N s, O_subset_C c d N t,
    Finset.mem_product.mpr ⟨mark_mem_O a b N s hN hs, mark_mem_O c d N t hN ht⟩,hd⟩

private theorem image_add_eq_sub_neg (I : Finset ℤ) (s : ℤ) :
    I.image (fun x => s+x) = (I.image Neg.neg).image (fun z => s-z) := by
  rw [Finset.image_image]
  simp only [Function.comp_def, sub_neg_eq_add]

/-- Every missing output of an actual translated equal-sided cube supplies
one of the three actual dense rectangle certificates. The signed grids and
holes are precisely the original projection grids and complements of `A`.
The corresponding output pairs are `(s₁,s₂)`, `(s₁,s₃)`, `(s₂,s₃)`. -/
theorem missing_output_certificate (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ (C r1 N) ×ˢ ((C r2 N) ×ˢ (C r3 N))) (s : ℤ × ℤ × ℤ)
    (hs : s ∈ NoncommutingFiber.mixedSum ((C r1 N) ×ˢ ((C r2 N) ×ˢ (C r3 N))))
    (hm : s ∉ NoncommutingFiber.mixedSum A) :
    RectangleCertificate (O r2 r3 N s.1) (O (-r1-N+1) r3 N s.2.1)
      (NoncommutingProjectionHoles.H0 (C r1 N) (C r2 N) A)
      (C r2 N) (C (-r1-N+1) N)
      (mark r2 r3 N s.1, mark (-r1-N+1) r3 N s.2.1) ∨
    RectangleCertificate (O r3 r2 N s.1) (O (-r1-N+1) (-r2-N+1) N s.2.2)
      (NoncommutingProjectionHoles.H1 (C r1 N) (C r3 N) A)
      (C r3 N) (C (-r1-N+1) N)
      (mark r3 r2 N s.1, mark (-r1-N+1) (-r2-N+1) N s.2.2) ∨
    RectangleCertificate (O r3 (-r1-N+1) N s.2.1)
      (O (-r2-N+1) (-r1-N+1) N s.2.2)
      (NoncommutingProjectionHoles.H2 (C r2 N) (C r3 N) A)
      (C r3 N) (C (-r2-N+1) N)
      (mark r3 (-r1-N+1) N s.2.1, mark (-r2-N+1) (-r1-N+1) N s.2.2) := by
  have hp0 : NoncommutingProjectionHoles.p0 = (fun t : ℤ × ℤ × ℤ => (t.2.1,-t.1)) := rfl
  have hp1 : NoncommutingProjectionHoles.p1 = (fun t : ℤ × ℤ × ℤ => (t.2.2,-t.1)) := rfl
  have hp2 : NoncommutingProjectionHoles.p2 = (fun t : ℤ × ℤ × ℤ => (t.2.2,-t.2.1)) := rfl
  have hd := NoncommutingCoveringDensity.missing_output_rectangle_density
    (C r1 N) (C r2 N) (C r3 N) A hA s hs hm
  have hi := NoncommutingCoveringDensity.rectangle_factor_identifications
    (C r1 N) (C r2 N) (C r3 N) s
  dsimp only at hd
  rw [hi.1, hi.2.1, hi.2.2] at hd
  simp only [image_add_eq_sub_neg, neg_C] at hd
  obtain ⟨n1,n2,n3,nr0,nr1,nr2,hd⟩ := hd
  rcases hd with hd0 | hd1 | hd2
  · apply Or.inl
    apply certificate_of_density _ _ _ _ _ _ _ _ hN n1 n2
    simpa only [NoncommutingProjectionHoles.H0, NoncommutingProjectionHoles.G0,
      hp0, neg_C, O] using hd0
  · have nf := (Finset.nonempty_product.mp nr1).1
    apply Or.inr ∘ Or.inl
    apply certificate_of_density _ _ _ _ _ _ _ _ hN nf n3
    simpa only [NoncommutingProjectionHoles.H1, NoncommutingProjectionHoles.G1,
      hp1, neg_C, O] using hd1
  · obtain ⟨nf,ng⟩ := Finset.nonempty_product.mp nr2
    apply Or.inr ∘ Or.inr
    apply certificate_of_density _ _ _ _ _ _ _ _ hN nf ng
    simpa only [NoncommutingProjectionHoles.H2, NoncommutingProjectionHoles.G2,
      hp2, neg_C, O] using hd2

example : 1 ≤ (1 : ℤ) ∧
    (∅ : Finset (ℤ × ℤ × ℤ)) ⊆ (C 10 1) ×ˢ ((C 20 1) ×ˢ (C 30 1)) ∧
    (50,20,-30) ∈ NoncommutingFiber.mixedSum ((C 10 1) ×ˢ ((C 20 1) ×ˢ (C 30 1))) ∧
    (50,20,-30) ∉ NoncommutingFiber.mixedSum (∅ : Finset (ℤ × ℤ × ℤ)) ∧
    (C 10 1).Nonempty ∧ (C 20 1).Nonempty ∧ (C 30 1).Nonempty := by decide

example : 1 ≤ (2 : ℤ) ∧
    ({(10,20,30)} : Finset (ℤ × ℤ × ℤ)) ⊆ (C 10 2) ×ˢ ((C 20 2) ×ˢ (C 30 2)) ∧
    (52,20,-32) ∈ NoncommutingFiber.mixedSum ((C 10 2) ×ˢ ((C 20 2) ×ˢ (C 30 2))) ∧
    (52,20,-32) ∉ NoncommutingFiber.mixedSum {(10,20,30)} ∧
    (C 10 2).Nonempty ∧ (C 20 2).Nonempty ∧ (C 30 2).Nonempty := by decide

end
end NoncommutingCubeWindows
