import Combinatorics.NoncommutingProductDownset

set_option autoImplicit false

namespace NoncommutingDownsetSharpEight

open NoncommutingFiber NoncommutingCubeCounting
open scoped Pointwise

/-- Actual three-map membership in a nonnegative downset is equivalent to three
independently realizable coordinate-plane witnesses, with the middle output
coordinate clamped at its smallest possible nonnegative inputs. -/
theorem mem_mixedSum_iff_clamped (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (p q t : ℤ) :
    (p, q, -t) ∈ mixedSum A ↔ ∃ x y z : ℤ,
      (max 0 (-q), y, 0) ∈ A ∧ (x, 0, z) ∈ A ∧
      (0, t-x, max 0 q) ∈ A ∧ y+z=p := by
  constructor
  · intro hs
    obtain ⟨ab, hab, c, hc, he⟩ := Finset.mem_add.mp hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hab
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    have hspos := hpos s hs
    have hwpos := hpos w hw
    have hvpos := hpos v hv
    have he1 := congrArg Prod.fst he
    have he2 := congrArg (fun r : ℤ × ℤ × ℤ => r.2.1) he
    have he3 := congrArg (fun r : ℤ × ℤ × ℤ => r.2.2) he
    simp only [L0, L1, L2, Prod.mk_add_mk, Prod.fst, Prod.snd,
      add_zero, zero_add] at he1 he2 he3
    refine ⟨w.1, s.2.1, w.2.2, ?_, ?_, ?_, he1⟩
    · apply hdown s hs <;> simp only [Prod.fst, Prod.snd] <;> omega
    · apply hdown w hw <;> simp only [Prod.fst, Prod.snd] <;> omega
    · apply hdown v hv <;> simp only [Prod.fst, Prod.snd] <;> omega
  · rintro ⟨x, y, z, hs, hw, hv, hp⟩
    have he : L0 (max 0 (-q), y, 0) + L1 (x, 0, z) +
        L2 (0, t-x, max 0 q) = (p, q, -t) := by
      simp only [L0, L1, L2, Prod.mk_add_mk, add_zero, zero_add]
      apply Prod.ext hp
      apply Prod.ext <;> dsimp <;> omega
    rw [← he]
    exact Finset.add_mem_add
      (Finset.add_mem_add (Finset.mem_image_of_mem L0 hs)
        (Finset.mem_image_of_mem L1 hw)) (Finset.mem_image_of_mem L2 hv)

/-- Given the three actual anchored roof intervals at a signed slice, its first
output coordinate is exactly the interval from zero to the sum of the first two
roof lengths minus two. No cardinality identity is assumed. -/
theorem mem_mixedSum_signed_slice (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (p q t u v k : ℤ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hv : 1 ≤ v) (hk : 1 ≤ k)
    (hf : ∀ y : ℤ, (max 0 (-q), y, 0) ∈ A ↔ 0 ≤ y ∧ y < u)
    (hg : ∀ z : ℤ, (max 0 (t-k+1), 0, z) ∈ A ↔ 0 ≤ z ∧ z < v)
    (hh : ∀ y : ℤ, (0, y, max 0 q) ∈ A ↔ 0 ≤ y ∧ y < k) :
    (p, q, -t) ∈ mixedSum A ↔ 0 ≤ p ∧ p ≤ u+v-2 := by
  rw [mem_mixedSum_iff_clamped A hpos hdown]
  constructor
  · rintro ⟨x, y, z, hxy, hxz, hyq, he⟩
    have hy := (hf y).mp hxy
    have hyq' := (hh (t-x)).mp hyq
    have hxzpos := hpos _ hxz
    dsimp at hxzpos
    have hx : max 0 (t-k+1) ≤ x := by omega
    have hzmem : (max 0 (t-k+1), 0, z) ∈ A := by
      apply hdown _ hxz <;> simp only [Prod.fst, Prod.snd] <;> omega
    have hz := (hg z).mp hzmem
    omega
  · rintro ⟨hp, hp'⟩
    let y := max 0 (p-v+1)
    let z := p-y
    refine ⟨max 0 (t-k+1), y, z, (hf y).mpr ?_, (hg z).mpr ?_,
      (hh (t-max 0 (t-k+1))).mpr ?_, ?_⟩
    · dsimp [y]
      omega
    · dsimp [y, z]
      omega
    · omega
    · dsimp [z]
      omega

/-- The actual finite output fiber at a signed slice has the exact interval
length supplied by its two roof lengths. -/
theorem card_mixedSum_signed_slice (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (q t u v k : ℤ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hv : 1 ≤ v) (hk : 1 ≤ k)
    (hf : ∀ y : ℤ, (max 0 (-q), y, 0) ∈ A ↔ 0 ≤ y ∧ y < u)
    (hg : ∀ z : ℤ, (max 0 (t-k+1), 0, z) ∈ A ↔ 0 ≤ z ∧ z < v)
    (hh : ∀ y : ℤ, (0, y, max 0 q) ∈ A ↔ 0 ≤ y ∧ y < k) :
    (((mixedSum A).filter (fun s => s.2.1 = q ∧ s.2.2 = -t)).card : ℤ) =
      u+v-1 := by
  have heq : (mixedSum A).filter (fun s => s.2.1 = q ∧ s.2.2 = -t) =
      (Finset.Icc 0 (u+v-2)).image (fun p : ℤ => (p,q,-t)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hs, hq, hr⟩
      have he : s = (s.1, q, -t) := Prod.ext rfl (Prod.ext hq hr)
      rw [he] at hs
      have hp := (mem_mixedSum_signed_slice A hpos hdown s.1 q t u v k
        ht hu hv hk hf hg hh).mp hs
      exact ⟨s.1, hp, he.symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(mem_mixedSum_signed_slice A hpos hdown p q t u v k
        ht hu hv hk hf hg hh).mpr hp, rfl, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (by
    intro p r he
    exact congrArg Prod.fst he), Int.card_Icc]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ u+v-2+1-0)]
  omega

example :
    let A : Finset (ℤ × ℤ × ℤ) := {(0,0,0)}
    (∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2) ∧
    (∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) ∧
    (∀ y : ℤ, (max 0 (-(0 : ℤ)), y, 0) ∈ A ↔ 0 ≤ y ∧ y < 1) ∧
    (∀ z : ℤ, (max 0 ((0 : ℤ)-1+1), 0, z) ∈ A ↔ 0 ≤ z ∧ z < 1) ∧
    (∀ y : ℤ, (0, y, max 0 (0 : ℤ)) ∈ A ↔ 0 ≤ y ∧ y < 1) := by
  dsimp
  simp only [Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro s rfl
    norm_num
  constructor
  · rintro s rfl ⟨x,y,z⟩ hx hx' hy hy' hz hz'
    simp only [Prod.mk.injEq]
    dsimp at *
    omega
  norm_num
  intro y
  omega

/-- The actual anchored fiber with variable second coordinate. -/
def horizontalFiber (A : Finset (ℤ × ℤ × ℤ)) (x z : ℤ) : Finset ℤ :=
  (A.filter (fun s => s.1 = x ∧ s.2.2 = z)).image (fun s => s.2.1)

/-- The actual anchored fiber with variable third coordinate. -/
def verticalFiber (A : Finset (ℤ × ℤ × ℤ)) (x y : ℤ) : Finset ℤ :=
  (A.filter (fun s => s.1 = x ∧ s.2.1 = y)).image (fun s => s.2.2)

example : horizontalFiber {(0,0,0)} 0 0 = {0} := by decide
example : verticalFiber {(0,0,0)} 0 0 = {0} := by decide

/-- Horizontal fiber membership is precisely actual point membership. -/
theorem mem_horizontalFiber (A : Finset (ℤ × ℤ × ℤ)) (x y z : ℤ) :
    y ∈ horizontalFiber A x z ↔ (x,y,z) ∈ A := by
  simp only [horizontalFiber, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a,b,c⟩, ⟨hs, hx, hz⟩, hy⟩
    dsimp at hx hz hy
    subst a
    subst b
    subst c
    exact hs
  · intro hs
    exact ⟨(x,y,z), ⟨hs, rfl, rfl⟩, rfl⟩

/-- Vertical fiber membership is precisely actual point membership. -/
theorem mem_verticalFiber (A : Finset (ℤ × ℤ × ℤ)) (x y z : ℤ) :
    z ∈ verticalFiber A x y ↔ (x,y,z) ∈ A := by
  simp only [verticalFiber, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a,b,c⟩, ⟨hs, hx, hy⟩, hz⟩
    dsimp at hx hy hz
    subst a
    subst b
    subst c
    exact hs
  · intro hs
    exact ⟨(x,y,z), ⟨hs, rfl, rfl⟩, rfl⟩

private theorem ideal_mem_iff (S : Finset ℤ)
    (hpos : ∀ x ∈ S, 0 ≤ x)
    (hdown : ∀ x ∈ S, ∀ y : ℤ, 0 ≤ y → y ≤ x → y ∈ S) (x : ℤ) :
    x ∈ S ↔ 0 ≤ x ∧ x < (S.card : ℤ) := by
  by_cases hne : S.Nonempty
  · conv_lhs => rw [NoncommutingProductDownset.ideal_eq_Icc_card S hne hpos hdown]
    rw [Finset.mem_Icc]
    omega
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

/-- Every actual horizontal fiber of a nonnegative downset is its intrinsic
initial interval, including empty fibers. -/
theorem horizontalFiber_interval (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (x y z : ℤ) :
    (x,y,z) ∈ A ↔ 0 ≤ y ∧ y < ((horizontalFiber A x z).card : ℤ) := by
  rw [← mem_horizontalFiber]
  apply ideal_mem_iff
  · intro r hr
    exact (hpos _ ((mem_horizontalFiber A x r z).mp hr)).2.1
  · intro r hr s hs hsr
    have hp := (mem_horizontalFiber A x r z).mp hr
    have hnonneg := hpos _ hp
    apply (mem_horizontalFiber A x s z).mpr
    exact hdown _ hp _ hnonneg.1 (le_refl x) hs hsr hnonneg.2.2 (le_refl z)

/-- Every actual vertical fiber of a nonnegative downset is its intrinsic
initial interval, including empty fibers. -/
theorem verticalFiber_interval (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (x y z : ℤ) :
    (x,y,z) ∈ A ↔ 0 ≤ z ∧ z < ((verticalFiber A x y).card : ℤ) := by
  rw [← mem_verticalFiber]
  apply ideal_mem_iff
  · intro r hr
    exact (hpos _ ((mem_verticalFiber A x y r).mp hr)).2.2
  · intro r hr s hs hsr
    have hp := (mem_verticalFiber A x y r).mp hr
    have hnonneg := hpos _ hp
    apply (mem_verticalFiber A x y s).mpr
    exact hdown _ hp _ hnonneg.1 (le_refl x) hnonneg.2.1 (le_refl y) hs hsr

/-- The first-coordinate image of a nonnegative downset is exactly its
anchored first axis and is the interval determined by its true extent. -/
theorem firstAxis_interval (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) (x : ℤ) :
    (x,0,0) ∈ A ↔ 0 ≤ x ∧ x < ((A.image Prod.fst).card : ℤ) := by
  have haxis (r : ℤ) : r ∈ A.image Prod.fst ↔ (r,0,0) ∈ A := by
    constructor
    · rintro hr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      have hp := hpos s hs
      exact hdown s hs _ hp.1 (le_refl _) (by norm_num) hp.2.1
        (by norm_num) hp.2.2
    · intro hr
      exact Finset.mem_image.mpr ⟨(r,0,0),hr,rfl⟩
  rw [← haxis]
  apply ideal_mem_iff
  · intro r hr
    exact (hpos _ ((haxis r).mp hr)).1
  · intro r hr s hs hsr
    apply (haxis s).mpr
    exact hdown _ ((haxis r).mp hr) _ hs hsr (by norm_num) (le_refl 0)
      (by norm_num) (le_refl 0)

/-- A nonempty nonnegative downset contains the origin. -/
theorem origin_mem (A : Finset (ℤ × ℤ × ℤ)) (hne : A.Nonempty)
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) : (0,0,0) ∈ A := by
  obtain ⟨s,hs⟩ := hne
  have hp := hpos s hs
  exact hdown s hs _ (by norm_num) hp.1 (by norm_num) hp.2.1
    (by norm_num) hp.2.2

/-- The exact signed-slice interval with all roof hypotheses discharged by
intrinsic actual fibers. Only the natural signed support inequalities remain. -/
theorem mem_mixedSum_intrinsic_slice (A : Finset (ℤ × ℤ × ℤ)) (hne : A.Nonempty)
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (p q t : ℤ)
    (hqlo : -((A.image Prod.fst).card : ℤ)+1 ≤ q)
    (hqhi : q ≤ ((verticalFiber A 0 0).card : ℤ)-1)
    (htlo : 0 ≤ t)
    (hthi : t ≤ ((A.image Prod.fst).card : ℤ) +
      ((horizontalFiber A 0 (max 0 q)).card : ℤ)-2) :
    (p,q,-t) ∈ mixedSum A ↔ 0 ≤ p ∧ p ≤
      ((horizontalFiber A (max 0 (-q)) 0).card : ℤ) +
      ((verticalFiber A
        (max 0 (t-((horizontalFiber A 0 (max 0 q)).card : ℤ)+1)) 0).card : ℤ)-2 := by
  have hz := origin_mem A hne hpos hdown
  have ha := ((firstAxis_interval A hpos hdown 0).mp hz).2
  have hc := ((verticalFiber_interval A hpos hdown 0 0 0).mp hz).2
  have hxmem : (max 0 (-q),0,0) ∈ A :=
    (firstAxis_interval A hpos hdown _).mpr ⟨by positivity, by omega⟩
  have hzmem : (0,0,max 0 q) ∈ A :=
    (verticalFiber_interval A hpos hdown _ _ _).mpr ⟨by positivity, by omega⟩
  have hu := ((horizontalFiber_interval A hpos hdown _ _ _).mp hxmem).2
  have hk := ((horizontalFiber_interval A hpos hdown _ _ _).mp hzmem).2
  have hx'mem : (max 0 (t-((horizontalFiber A 0 (max 0 q)).card : ℤ)+1),0,0) ∈ A :=
    (firstAxis_interval A hpos hdown _).mpr ⟨by positivity, by omega⟩
  have hv := ((verticalFiber_interval A hpos hdown _ _ _).mp hx'mem).2
  exact mem_mixedSum_signed_slice A hpos hdown p q t _ _ _ htlo
    (by omega) (by omega) (by omega)
    (fun y => horizontalFiber_interval A hpos hdown _ y _)
    (fun z => verticalFiber_interval A hpos hdown _ _ z)
    (fun y => horizontalFiber_interval A hpos hdown _ y _)

/-- Every actual output satisfies the exact signed support bounds in terms
of the true first extent, third extent, and actual horizontal roof. -/
theorem mixedSum_intrinsic_support (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (p q t : ℤ) (hs : (p,q,-t) ∈ mixedSum A) :
    -((A.image Prod.fst).card : ℤ)+1 ≤ q ∧
    q ≤ ((verticalFiber A 0 0).card : ℤ)-1 ∧ 0 ≤ t ∧
    t ≤ ((A.image Prod.fst).card : ℤ) +
      ((horizontalFiber A 0 (max 0 q)).card : ℤ)-2 := by
  obtain ⟨x,y,z,hf,hg,hh,he⟩ :=
    (mem_mixedSum_iff_clamped A hpos hdown p q t).mp hs
  have hfpos := hpos _ hf
  have hgpos := hpos _ hg
  have hhpos := hpos _ hh
  dsimp at hfpos hgpos hhpos
  have hx0 : (max 0 (-q),0,0) ∈ A := by
    apply hdown _ hf <;> dsimp <;> omega
  have hx : (x,0,0) ∈ A := by
    apply hdown _ hg <;> dsimp <;> omega
  have hz : (0,0,max 0 q) ∈ A := by
    apply hdown _ hh <;> dsimp <;> omega
  have hxa := ((firstAxis_interval A hpos hdown _).mp hx0).2
  have hxb := ((firstAxis_interval A hpos hdown _).mp hx).2
  have hzc := ((verticalFiber_interval A hpos hdown _ _ _).mp hz).2
  have htk := ((horizontalFiber_interval A hpos hdown _ _ _).mp hh).2
  omega

/-- Complete actual-output characterization for a nonempty downset: the signed
support and the slice roof are all intrinsic, with no external profile premises. -/
theorem mem_mixedSum_intrinsic_iff (A : Finset (ℤ × ℤ × ℤ)) (hne : A.Nonempty)
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (p q t : ℤ) :
    (p,q,-t) ∈ mixedSum A ↔
    -((A.image Prod.fst).card : ℤ)+1 ≤ q ∧
    q ≤ ((verticalFiber A 0 0).card : ℤ)-1 ∧ 0 ≤ t ∧
    t ≤ ((A.image Prod.fst).card : ℤ) +
      ((horizontalFiber A 0 (max 0 q)).card : ℤ)-2 ∧
    0 ≤ p ∧ p ≤ ((horizontalFiber A (max 0 (-q)) 0).card : ℤ) +
      ((verticalFiber A
        (max 0 (t-((horizontalFiber A 0 (max 0 q)).card : ℤ)+1)) 0).card : ℤ)-2 := by
  constructor
  · intro hs
    obtain ⟨hqlo,hqhi,htlo,hthi⟩ := mixedSum_intrinsic_support A hpos hdown p q t hs
    exact ⟨hqlo,hqhi,htlo,hthi,
      (mem_mixedSum_intrinsic_slice A hne hpos hdown p q t hqlo hqhi htlo hthi).mp hs⟩
  · rintro ⟨hqlo,hqhi,htlo,hthi,hp⟩
    exact (mem_mixedSum_intrinsic_slice A hne hpos hdown p q t hqlo hqhi htlo hthi).mpr hp

/-- Actual intrinsic signed slices have their exact roof-sum cardinality. -/
theorem card_mixedSum_intrinsic_slice (A : Finset (ℤ × ℤ × ℤ)) (hne : A.Nonempty)
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A)
    (q t : ℤ)
    (hqlo : -((A.image Prod.fst).card : ℤ)+1 ≤ q)
    (hqhi : q ≤ ((verticalFiber A 0 0).card : ℤ)-1)
    (htlo : 0 ≤ t)
    (hthi : t ≤ ((A.image Prod.fst).card : ℤ) +
      ((horizontalFiber A 0 (max 0 q)).card : ℤ)-2) :
    (((mixedSum A).filter (fun s => s.2.1 = q ∧ s.2.2 = -t)).card : ℤ) =
      ((horizontalFiber A (max 0 (-q)) 0).card : ℤ) +
      ((verticalFiber A
        (max 0 (t-((horizontalFiber A 0 (max 0 q)).card : ℤ)+1)) 0).card : ℤ)-1 := by
  let u : ℤ := (horizontalFiber A (max 0 (-q)) 0).card
  let v : ℤ := (verticalFiber A
    (max 0 (t-((horizontalFiber A 0 (max 0 q)).card : ℤ)+1)) 0).card
  have hmem (p : ℤ) : (p,q,-t) ∈ mixedSum A ↔ 0 ≤ p ∧ p ≤ u+v-2 :=
    mem_mixedSum_intrinsic_slice A hne hpos hdown p q t hqlo hqhi htlo hthi
  have hz := origin_mem A hne hpos hdown
  have ha := ((firstAxis_interval A hpos hdown 0).mp hz).2
  have hc := ((verticalFiber_interval A hpos hdown 0 0 0).mp hz).2
  have hxmem : (max 0 (-q),0,0) ∈ A :=
    (firstAxis_interval A hpos hdown _).mpr ⟨by positivity, by omega⟩
  have hzmem : (0,0,max 0 q) ∈ A :=
    (verticalFiber_interval A hpos hdown _ _ _).mpr ⟨by positivity, by omega⟩
  have hu : 0 < u := ((horizontalFiber_interval A hpos hdown _ _ _).mp hxmem).2
  have hk := ((horizontalFiber_interval A hpos hdown _ _ _).mp hzmem).2
  have hx'mem : (max 0 (t-((horizontalFiber A 0 (max 0 q)).card : ℤ)+1),0,0) ∈ A :=
    (firstAxis_interval A hpos hdown _).mpr ⟨by positivity, by omega⟩
  have hv : 0 < v := ((verticalFiber_interval A hpos hdown _ _ _).mp hx'mem).2
  have heq : (mixedSum A).filter (fun s => s.2.1 = q ∧ s.2.2 = -t) =
      (Finset.Icc 0 (u+v-2)).image (fun p : ℤ => (p,q,-t)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hs,hq,hr⟩
      have he : s = (s.1,q,-t) := Prod.ext rfl (Prod.ext hq hr)
      rw [he] at hs
      exact ⟨s.1, (hmem s.1).mp hs, he.symm⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨(hmem p).mpr hp,rfl,rfl⟩
  change _ = u+v-1
  rw [heq, Finset.card_image_of_injective _ (by
    intro p r he
    exact congrArg Prod.fst he), Int.card_Icc,
    Int.toNat_of_nonneg (by omega : 0 ≤ u+v-2+1-0)]
  omega

/-- Exact double-slice count for the actual mixed sum of an arbitrary nonempty
nonnegative downset, using only its intrinsic coordinate fibers. -/
theorem card_mixedSum_eq_roof_sum (A : Finset (ℤ × ℤ × ℤ)) (hne : A.Nonempty)
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    ((mixedSum A).card : ℤ) =
    ∑ q ∈ Finset.Icc (-((A.image Prod.fst).card : ℤ)+1)
        (((verticalFiber A 0 0).card : ℤ)-1),
      ∑ t ∈ Finset.Icc 0 (((A.image Prod.fst).card : ℤ) +
          ((horizontalFiber A 0 (max 0 q)).card : ℤ)-2),
        (((horizontalFiber A (max 0 (-q)) 0).card : ℤ) +
          ((verticalFiber A
            (max 0 (t-((horizontalFiber A 0 (max 0 q)).card : ℤ)+1)) 0).card : ℤ)-1) := by
  let J := Finset.Icc (-((A.image Prod.fst).card : ℤ)+1)
    (((verticalFiber A 0 0).card : ℤ)-1)
  have houter : (mixedSum A).card =
      ∑ q ∈ J, ((mixedSum A).filter (fun s => s.2.1 = q)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro s hs
    have hb := mixedSum_intrinsic_support A hpos hdown s.1 s.2.1 (-s.2.2) (by
      simpa using hs)
    exact Finset.mem_Icc.mpr ⟨hb.1,hb.2.1⟩
  rw [houter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_Icc.mp hq
  let K := Finset.Icc 0 (((A.image Prod.fst).card : ℤ) +
    ((horizontalFiber A 0 (max 0 q)).card : ℤ)-2)
  have hinner : ((mixedSum A).filter (fun s => s.2.1 = q)).card =
      ∑ t ∈ K, (((mixedSum A).filter (fun s => s.2.1 = q)).filter
        (fun s => -s.2.2 = t)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro s hs
    obtain ⟨hs,hseq⟩ := Finset.mem_filter.mp hs
    have hb := mixedSum_intrinsic_support A hpos hdown s.1 q (-s.2.2) (by
      simpa [← hseq] using hs)
    exact Finset.mem_Icc.mpr ⟨hb.2.2.1,hb.2.2.2⟩
  rw [hinner, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_Icc.mp ht
  have hfilter : ((mixedSum A).filter (fun s => s.2.1 = q)).filter
      (fun s => -s.2.2 = t) =
      (mixedSum A).filter (fun s => s.2.1 = q ∧ s.2.2 = -t) := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hs,hq⟩,ht⟩
      exact ⟨hs,hq,by omega⟩
    · rintro ⟨hs,hq,ht⟩
      exact ⟨⟨hs,hq⟩,by omega⟩
  rw [hfilter]
  exact card_mixedSum_intrinsic_slice A hne hpos hdown q t
    hq'.1 hq'.2 ht'.1 ht'.2

private theorem sum_Icc_split_at (f : ℤ → ℤ) (lo cut hi : ℤ)
    (hlo : lo ≤ cut+1) (hhi : cut ≤ hi) :
    ∑ x ∈ Finset.Icc lo hi, f x =
      (∑ x ∈ Finset.Icc lo cut, f x) + ∑ x ∈ Finset.Icc (cut+1) hi, f x := by
  have he : Finset.Icc lo hi = Finset.Icc lo cut ∪ Finset.Icc (cut+1) hi := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc lo cut) (Finset.Icc (cut+1) hi) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := Finset.mem_Icc.mp hx
    have hy' := Finset.mem_Icc.mp hy
    omega
  rw [he, Finset.sum_union hd]

private theorem card_Icc_int (lo hi : ℤ) (h : lo ≤ hi+1) :
    ((Finset.Icc lo hi).card : ℤ) = hi+1-lo := by
  rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]

/-- The clamped roof sum in a signed slice consists of k copies of the first
column followed by the remaining actual roof columns. -/
theorem sum_clamped_roof (g : ℤ → ℤ) (a k : ℤ) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 0 (a+k-2), g (max 0 (t-k+1))) =
      k*g 0 + ∑ x ∈ Finset.Icc 1 (a-1), g x := by
  rw [sum_Icc_split_at _ 0 (k-1) (a+k-2) (by omega) (by omega)]
  have hhead : (∑ t ∈ Finset.Icc 0 (k-1), g (max 0 (t-k+1))) = k*g 0 := by
    calc
      _ = ∑ _t ∈ Finset.Icc 0 (k-1), g 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := Finset.mem_Icc.mp ht
        rw [max_eq_left (by omega : t-k+1 ≤ 0)]
      _ = k*g 0 := by
        rw [Finset.sum_const, nsmul_eq_mul, card_Icc_int _ _ (by omega)]
        ring
  rw [hhead]
  congr 1
  apply Finset.sum_bij (fun t _ => t-k+1)
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    simp only [Finset.mem_Icc]
    omega
  · intro t ht s hs he
    omega
  · intro x hx
    have hx' := Finset.mem_Icc.mp hx
    refine ⟨x+k-1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    rw [max_eq_right (by omega : 0 ≤ t-k+1)]

/-- Evaluation of the entire inner signed-slice sum. The total roof sum and
first roof value are written intrinsically, not supplied as counting oracles. -/
theorem sum_signed_slice_lengths (g : ℤ → ℤ) (a k u : ℤ)
    (ha : 1 ≤ a) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 0 (a+k-2), (u+g (max 0 (t-k+1))-1)) =
      (a+k-1)*(u-1)+k*g 0+(∑ x ∈ Finset.Icc 0 (a-1), g x)-g 0 := by
  have htotal : (∑ x ∈ Finset.Icc 0 (a-1), g x) =
      g 0 + ∑ x ∈ Finset.Icc 1 (a-1), g x := by
    rw [sum_Icc_split_at _ 0 0 (a-1) (by omega) (by omega)]
    simp
  have hs : (∑ t ∈ Finset.Icc 0 (a+k-2), (u+g (max 0 (t-k+1))-1)) =
      (∑ _t ∈ Finset.Icc 0 (a+k-2), (u-1)) +
        ∑ t ∈ Finset.Icc 0 (a+k-2), g (max 0 (t-k+1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hs, sum_clamped_roof g a k ha hk, Finset.sum_const, nsmul_eq_mul,
    card_Icc_int _ _ (by omega), htotal]
  ring

/-- A pair set is counted by its actual second-coordinate fibers over any
finite first-coordinate support. -/
theorem card_pair_eq_sum_fibers (P : Finset (ℤ × ℤ)) (I : Finset ℤ)
    (B : ℤ → Finset ℤ) (hI : ∀ s ∈ P, s.1 ∈ I)
    (hB : ∀ x y : ℤ, y ∈ B x ↔ (x,y) ∈ P) :
    (P.card : ℤ) = ∑ x ∈ I, ((B x).card : ℤ) := by
  have he : P.card = ∑ x ∈ I, (P.filter (fun s => s.1 = x)).card :=
    Finset.card_eq_sum_card_fiberwise hI
  rw [he, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.card_bij (fun s _ => s.2)
  · intro s hs
    obtain ⟨hs,he⟩ := Finset.mem_filter.mp hs
    apply (hB x s.2).mpr
    simpa [← he] using hs
  · intro s hs t ht he
    have hs' := (Finset.mem_filter.mp hs).2
    have ht' := (Finset.mem_filter.mp ht).2
    exact Prod.ext (hs'.trans ht'.symm) he
  · intro y hy
    exact ⟨(x,y), Finset.mem_filter.mpr ⟨(hB x y).mp hy,rfl⟩,rfl⟩

/-- The first-second actual pair-projection area is the sum of the intrinsic
horizontal roofs over the true first extent. -/
theorem card_projection01_eq_roof_sum (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    ((A.image (fun s => (s.1,s.2.1))).card : ℤ) =
      ∑ x ∈ Finset.Icc 0 (((A.image Prod.fst).card : ℤ)-1),
        ((horizontalFiber A x 0).card : ℤ) := by
  apply card_pair_eq_sum_fibers
  · intro s hs
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
    have hp := hpos w hw
    have hx : (w.1,0,0) ∈ A := hdown w hw _ hp.1 (le_refl _)
      (by norm_num) hp.2.1 (by norm_num) hp.2.2
    have hb := (firstAxis_interval A hpos hdown _).mp hx
    exact Finset.mem_Icc.mpr ⟨hb.1,by omega⟩
  · intro x y
    rw [mem_horizontalFiber]
    constructor
    · intro hs
      exact Finset.mem_image.mpr ⟨(x,y,0),hs,rfl⟩
    · intro hs
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hs
      have hp := hpos w hw
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp at he1 he2
      apply hdown w hw <;> dsimp <;> omega

/-- The first-third actual pair-projection area is the sum of the intrinsic
vertical roofs over the true first extent. -/
theorem card_projection02_eq_roof_sum (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    ((A.image (fun s => (s.1,s.2.2))).card : ℤ) =
      ∑ x ∈ Finset.Icc 0 (((A.image Prod.fst).card : ℤ)-1),
        ((verticalFiber A x 0).card : ℤ) := by
  apply card_pair_eq_sum_fibers
  · intro s hs
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
    have hp := hpos w hw
    have hx : (w.1,0,0) ∈ A := hdown w hw _ hp.1 (le_refl _)
      (by norm_num) hp.2.1 (by norm_num) hp.2.2
    have hb := (firstAxis_interval A hpos hdown _).mp hx
    exact Finset.mem_Icc.mpr ⟨hb.1,by omega⟩
  · intro x z
    rw [mem_verticalFiber]
    constructor
    · intro hs
      exact Finset.mem_image.mpr ⟨(x,0,z),hs,rfl⟩
    · intro hs
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hs
      have hp := hpos w hw
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp at he1 he2
      apply hdown w hw <;> dsimp <;> omega

/-- The second-third actual pair-projection area is the sum of horizontal
roofs over the true third extent, with projection swapping preserving area. -/
theorem card_projection12_eq_roof_sum (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    ((A.image (fun s => (s.2.1,s.2.2))).card : ℤ) =
      ∑ z ∈ Finset.Icc 0 (((verticalFiber A 0 0).card : ℤ)-1),
        ((horizontalFiber A 0 z).card : ℤ) := by
  have he : (A.image (fun s => (s.2.2,s.2.1))).card =
      (A.image (fun s => (s.2.1,s.2.2))).card := by
    have heq : A.image (fun s => (s.2.2,s.2.1)) =
        (A.image (fun s => (s.2.1,s.2.2))).image Prod.swap := by
      rw [Finset.image_image]
      rfl
    rw [heq, Finset.card_image_of_injective _ Prod.swap_injective]
  rw [← he]
  apply card_pair_eq_sum_fibers
  · intro s hs
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
    have hp := hpos w hw
    have hz : (0,0,w.2.2) ∈ A := hdown w hw _ (by norm_num) hp.1
      (by norm_num) hp.2.1 hp.2.2 (le_refl _)
    have hb := (verticalFiber_interval A hpos hdown _ _ _).mp hz
    exact Finset.mem_Icc.mpr ⟨hb.1,by omega⟩
  · intro z y
    rw [mem_horizontalFiber]
    constructor
    · intro hs
      exact Finset.mem_image.mpr ⟨(0,y,z),hs,rfl⟩
    · intro hs
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hs
      have hp := hpos w hw
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp at he1 he2
      apply hdown w hw <;> dsimp <;> omega

/-- The actual double-slice count collapses to a single signed-roof sum, with
the first-third contribution identified with its actual pair-projection area. -/
theorem card_mixedSum_eq_single_roof_sum (A : Finset (ℤ × ℤ × ℤ)) (hne : A.Nonempty)
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    ((mixedSum A).card : ℤ) =
      ∑ q ∈ Finset.Icc (-((A.image Prod.fst).card : ℤ)+1)
          (((verticalFiber A 0 0).card : ℤ)-1),
        ((((A.image Prod.fst).card : ℤ)+
          ((horizontalFiber A 0 (max 0 q)).card : ℤ)-1)*
          (((horizontalFiber A (max 0 (-q)) 0).card : ℤ)-1) +
        ((horizontalFiber A 0 (max 0 q)).card : ℤ)*((verticalFiber A 0 0).card : ℤ) +
        ((A.image (fun s => (s.1,s.2.2))).card : ℤ)-((verticalFiber A 0 0).card : ℤ)) := by
  rw [card_mixedSum_eq_roof_sum A hne hpos hdown]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_Icc.mp hq
  have hz := origin_mem A hne hpos hdown
  have ha := ((firstAxis_interval A hpos hdown 0).mp hz).2
  have hc := ((verticalFiber_interval A hpos hdown 0 0 0).mp hz).2
  have hzmem : (0,0,max 0 q) ∈ A :=
    (verticalFiber_interval A hpos hdown _ _ _).mpr ⟨by positivity,by omega⟩
  have hk := ((horizontalFiber_interval A hpos hdown _ _ _).mp hzmem).2
  rw [sum_signed_slice_lengths
    (fun x => ((verticalFiber A x 0).card : ℤ)) _ _ _ (by omega) (by omega),
    ← card_projection02_eq_roof_sum A hpos hdown]

private theorem sum_affine (S : Finset ℤ) (f : ℤ → ℤ) (α β : ℤ) :
    (∑ i ∈ S, (α*f i+β)) = α*(∑ i ∈ S, f i)+(S.card : ℤ)*β := by
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]

/-- Evaluation of the remaining signed roof sum. The two roof totals are
explicit finite sums, so this lemma assumes no geometric cardinality oracle. -/
theorem sum_signed_roofs (f k : ℤ → ℤ) (a b c G : ℤ)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hf : f 0 = b) (hk : k 0 = b) :
    (∑ q ∈ Finset.Icc (-a+1) (c-1),
      ((a+k (max 0 q)-1)*(f (max 0 (-q))-1)+k (max 0 q)*c+G-c)) =
      (a+b-1)*(∑ x ∈ Finset.Icc 0 (a-1), f x) +
      (a+c-1)*G + (b+c-1)*(∑ z ∈ Finset.Icc 0 (c-1), k z) +
      2*a*b*c-(a+b+c-1)^2 := by
  rw [sum_Icc_split_at _ (-a+1) (-1) (c-1) (by omega) (by omega)]
  have hneg : (∑ q ∈ Finset.Icc (-a+1) (-1),
      ((a+k (max 0 q)-1)*(f (max 0 (-q))-1)+k (max 0 q)*c+G-c)) =
      (a+b-1)*(∑ x ∈ Finset.Icc 1 (a-1), f x) +
      (a-1)*(-(a+b-1)+b*c+G-c) := by
    calc
      _ = ∑ x ∈ Finset.Icc 1 (a-1),
          ((a+b-1)*f x+(-(a+b-1)+b*c+G-c)) := by
        apply Finset.sum_bij (fun q _ => -q)
        · intro q hq
          have hq' := Finset.mem_Icc.mp hq
          exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
        · intro q hq r hr he
          omega
        · intro x hx
          have hx' := Finset.mem_Icc.mp hx
          exact ⟨-x, Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
        · intro q hq
          have hq' := Finset.mem_Icc.mp hq
          rw [max_eq_left (by omega : q ≤ 0),
            max_eq_right (by omega : 0 ≤ -q),hk]
          ring
      _ = _ := by
        rw [sum_affine, card_Icc_int _ _ (by omega)]
        ring
  have hnonneg : (∑ q ∈ Finset.Icc 0 (c-1),
      ((a+k (max 0 q)-1)*(f (max 0 (-q))-1)+k (max 0 q)*c+G-c)) =
      (b+c-1)*(∑ q ∈ Finset.Icc 0 (c-1), k q) +
      c*((a-1)*(b-1)+G-c) := by
    calc
      _ = ∑ q ∈ Finset.Icc 0 (c-1),
          ((b+c-1)*k q+((a-1)*(b-1)+G-c)) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq' := Finset.mem_Icc.mp hq
        rw [max_eq_right hq'.1,max_eq_left (by omega : -q ≤ 0),hf]
        ring
      _ = _ := by
        rw [sum_affine, card_Icc_int _ _ (by omega)]
        ring
  have hF : (∑ x ∈ Finset.Icc 0 (a-1), f x) =
      b + ∑ x ∈ Finset.Icc 1 (a-1), f x := by
    rw [sum_Icc_split_at _ 0 0 (a-1) (by omega) (by omega)]
    simp [hf]
  norm_num only at *
  rw [hneg, hnonneg,hF]
  ring

/-- Exact general-downset cardinality formula for the actual three-map mixed
sum, in terms of true positive coordinate extents and actual pair projections. -/
theorem card_mixedSum_exact (A : Finset (ℤ × ℤ × ℤ)) (hne : A.Nonempty)
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    let a : ℤ := (A.image Prod.fst).card
    let b : ℤ := (horizontalFiber A 0 0).card
    let c : ℤ := (verticalFiber A 0 0).card
    let F : ℤ := (A.image (fun s => (s.1,s.2.1))).card
    let G : ℤ := (A.image (fun s => (s.1,s.2.2))).card
    let H : ℤ := (A.image (fun s => (s.2.1,s.2.2))).card
    ((mixedSum A).card : ℤ) =
      (a+b-1)*F+(a+c-1)*G+(b+c-1)*H+2*a*b*c-(a+b+c-1)^2 := by
  dsimp only
  have hz := origin_mem A hne hpos hdown
  have ha := ((firstAxis_interval A hpos hdown 0).mp hz).2
  have hc := ((verticalFiber_interval A hpos hdown 0 0 0).mp hz).2
  rw [card_mixedSum_eq_single_roof_sum A hne hpos hdown,
    sum_signed_roofs
      (fun x => ((horizontalFiber A x 0).card : ℤ))
      (fun z => ((horizontalFiber A 0 z).card : ℤ)) _ _ _ _
      (by omega) (by omega) rfl rfl,
    ← card_projection01_eq_roof_sum A hpos hdown,
    ← card_projection12_eq_roof_sum A hpos hdown]

/-- Nonnegative downclosure identifies the true coordinate images with the
anchored second and third axes. -/
theorem coordinate_images (A : Finset (ℤ × ℤ × ℤ))
    (hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    A.image (fun s => s.2.1) = horizontalFiber A 0 0 ∧
    A.image (fun s => s.2.2) = verticalFiber A 0 0 := by
  constructor
  · ext y
    rw [mem_horizontalFiber]
    constructor
    · rintro hy
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hy
      have hp := hpos s hs
      exact hdown s hs _ (by norm_num) hp.1 hp.2.1 (le_refl _)
        (by norm_num) hp.2.2
    · intro hy
      exact Finset.mem_image.mpr ⟨(0,y,0),hy,rfl⟩
  · ext z
    rw [mem_verticalFiber]
    constructor
    · rintro hz
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
      have hp := hpos s hs
      exact hdown s hs _ (by norm_num) hp.1 (by norm_num) hp.2.1
        hp.2.2 (le_refl _)
    · intro hz
      exact Finset.mem_image.mpr ⟨(0,0,z),hz,rfl⟩

/-- A finite three-coordinate set has at most the product of its coordinate
image sizes and at most each pair-projection size times the remaining image. -/
theorem card_volume_bounds (A : Finset (ℤ × ℤ × ℤ)) :
    A.card ≤ (A.image Prod.fst).card * (A.image (fun s => s.2.1)).card *
      (A.image (fun s => s.2.2)).card ∧
    A.card ≤ (A.image (fun s => (s.1,s.2.1))).card * (A.image (fun s => s.2.2)).card ∧
    A.card ≤ (A.image (fun s => (s.1,s.2.2))).card * (A.image (fun s => s.2.1)).card ∧
    A.card ≤ (A.image (fun s => (s.2.1,s.2.2))).card * (A.image Prod.fst).card := by
  constructor
  · have hs : A ⊆ (A.image Prod.fst) ×ˢ
        ((A.image (fun s => s.2.1)) ×ˢ (A.image (fun s => s.2.2))) := by
      intro s hs
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hs,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hs,Finset.mem_image_of_mem _ hs⟩⟩
    have hc := Finset.card_le_card hs
    simp only [Finset.card_product] at hc
    nlinarith only [hc]
  constructor
  · have hc := Finset.card_le_card_of_injOn (s := A)
        (t := (A.image (fun s => (s.1,s.2.1))) ×ˢ (A.image (fun s => s.2.2)))
        (fun s => ((s.1,s.2.1),s.2.2)) (by
          intro s hs
          exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hs,Finset.mem_image_of_mem _ hs⟩)
        (by
          intro s hs t ht he
          rcases s with ⟨sx,sy,sz⟩
          rcases t with ⟨tx,ty,tz⟩
          simp only [Prod.mk.injEq] at he ⊢
          tauto)
    simpa only [Finset.card_product] using hc
  constructor
  · have hc := Finset.card_le_card_of_injOn (s := A)
        (t := (A.image (fun s => (s.1,s.2.2))) ×ˢ (A.image (fun s => s.2.1)))
        (fun s => ((s.1,s.2.2),s.2.1)) (by
          intro s hs
          exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hs,Finset.mem_image_of_mem _ hs⟩)
        (by
          intro s hs t ht he
          rcases s with ⟨sx,sy,sz⟩
          rcases t with ⟨tx,ty,tz⟩
          simp only [Prod.mk.injEq] at he ⊢
          tauto)
    simpa only [Finset.card_product] using hc
  · have hc := Finset.card_le_card_of_injOn (s := A)
        (t := (A.image (fun s => (s.2.1,s.2.2))) ×ˢ (A.image Prod.fst))
        (fun s => ((s.2.1,s.2.2),s.1)) (by
          intro s hs
          exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hs,Finset.mem_image_of_mem _ hs⟩)
        (by
          intro s hs t ht he
          rcases s with ⟨sx,sy,sz⟩
          rcases t with ⟨tx,ty,tz⟩
          simp only [Prod.mk.injEq] at he ⊢
          tauto)
    simpa only [Finset.card_product] using hc

/-- The integer polynomial deficit estimate follows from the four actual
volume bounds, by a division-free sum of nonnegative terms. -/
theorem scalar_deficit (a b c d F G H : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 0 ≤ d)
    (hdP : d ≤ a*b*c) (hdF : d ≤ c*F) (hdG : d ≤ b*G) (hdH : d ≤ a*H) :
    8*d-(a*b+a*c+b*c+(a+b+c-1)^2) ≤
      (a+b-1)*F+(a+c-1)*G+(b+c-1)*H+2*a*b*c-(a+b+c-1)^2 := by
  let P := a*b*c
  let W := a*b+a*c+b*c
  let M := (a+b-1)*F+(a+c-1)*G+(b+c-1)*H+2*a*b*c-(a+b+c-1)^2
  have hid : P*(M-8*d+W+(a+b+c-1)^2) =
      a*b*(a+b-1)*(c*F-d)+a*c*(a+c-1)*(b*G-d)+b*c*(b+c-1)*(a*H-d)+
      d*(c*(a-b)^2+b*(a-c)^2+a*(b-c)^2)+(2*P+W)*(P-d) := by
    dsimp [P,W,M]
    ring
  have hP : 0 < P := by dsimp [P]; positivity
  have hF : 0 ≤ c*F-d := sub_nonneg.mpr hdF
  have hG : 0 ≤ b*G-d := sub_nonneg.mpr hdG
  have hH : 0 ≤ a*H-d := sub_nonneg.mpr hdH
  have hV : 0 ≤ P-d := sub_nonneg.mpr hdP
  have hab : 0 ≤ a+b-1 := by omega
  have hac : 0 ≤ a+c-1 := by omega
  have hbc : 0 ≤ b+c-1 := by omega
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hprod : 0 ≤ P*(M-8*d+W+(a+b+c-1)^2) := by
    rw [hid]
    positivity
  have hbound : 0 ≤ M-8*d+W+(a+b+c-1)^2 := by
    nlinarith only [hprod,hP]
  change 8*d-(W+(a+b+c-1)^2) ≤ M
  linarith only [hbound]

/-- The boundary polynomial is maximized by the containing cube. -/
theorem boundary_le_cube (a b c N : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (haN : a ≤ N) (hbN : b ≤ N) (hcN : c ≤ N) :
    a*b+a*c+b*c+(a+b+c-1)^2 ≤ 12*N^2-6*N+1 := by
  have hN : 0 ≤ N := by omega
  have hab := mul_le_mul haN hbN (by omega : 0 ≤ b) hN
  have hac := mul_le_mul haN hcN (by omega : 0 ≤ c) hN
  have hbc := mul_le_mul hbN hcN (by omega : 0 ≤ c) hN
  have hT : 0 ≤ (3*N-1)-(a+b+c-1) := by omega
  have hS : 0 ≤ (3*N-1)+(a+b+c-1) := by omega
  have hs := mul_nonneg hT hS
  nlinarith only [hab,hac,hbc,hs]

/-- Every coordinate-downclosed subset of a positive origin cube loses at most
eight actual mixed-sum outputs per missing input point. -/
theorem mixedSum_cube_deficit_le (N : ℤ) (hN : 1 ≤ N)
    (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ cube 0 0 0 N)
    (hdown : ∀ s ∈ A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ A) :
    (mixedSum (cube 0 0 0 N) \ mixedSum A).card ≤ 8*(cube 0 0 0 N \ A).card := by
  have hcube : ((cube 0 0 0 N).card : ℤ) = N^3 := by
    rw [NoncommutingCubeCardinality.card_cube _ _ _ _ hN]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ N)]
  have hmix : ((mixedSum (cube 0 0 0 N)).card : ℤ) = (2*N-1)^3 := by
    rw [NoncommutingCubeCardinality.card_mixedSum_cube _ _ _ _ hN]
    rw [Nat.cast_pow, Int.toNat_of_nonneg (by omega : 0 ≤ 2*N-1)]
  have hsplitA := Finset.card_sdiff_add_card_eq_card hA
  have hsplitM := Finset.card_sdiff_add_card_eq_card
    (NoncommutingCubeCardinality.mixedSum_mono hA)
  have htarget : (2*N-1)^3 ≤ 8*(N^3-(A.card : ℤ)) + ((mixedSum A).card : ℤ) := by
    by_cases hne : A.Nonempty
    · have hpos : ∀ s ∈ A, 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2 := by
        intro s hs
        have hp := hA hs
        simp only [cube, Finset.mem_product, Finset.mem_Icc] at hp
        exact ⟨hp.1.1,hp.2.1.1,hp.2.2.1⟩
      let a : ℤ := (A.image Prod.fst).card
      let b : ℤ := (horizontalFiber A 0 0).card
      let c : ℤ := (verticalFiber A 0 0).card
      let F : ℤ := (A.image (fun s => (s.1,s.2.1))).card
      let G : ℤ := (A.image (fun s => (s.1,s.2.2))).card
      let H : ℤ := (A.image (fun s => (s.2.1,s.2.2))).card
      have hz := origin_mem A hne hpos hdown
      have ha : 1 ≤ a := by
        have hh := ((firstAxis_interval A hpos hdown 0).mp hz).2
        dsimp [a]
        omega
      have hb : 1 ≤ b := by
        have hh := ((horizontalFiber_interval A hpos hdown 0 0 0).mp hz).2
        dsimp [b]
        omega
      have hc : 1 ≤ c := by
        have hh := ((verticalFiber_interval A hpos hdown 0 0 0).mp hz).2
        dsimp [c]
        omega
      have haN : a ≤ N := by
        have hx := hA ((firstAxis_interval A hpos hdown (a-1)).mpr ⟨by omega,by omega⟩)
        simp only [cube, Finset.mem_product, Finset.mem_Icc] at hx
        omega
      have hbN : b ≤ N := by
        have hx := hA ((horizontalFiber_interval A hpos hdown 0 (b-1) 0).mpr ⟨by omega,by omega⟩)
        simp only [cube, Finset.mem_product, Finset.mem_Icc] at hx
        omega
      have hcN : c ≤ N := by
        have hx := hA ((verticalFiber_interval A hpos hdown 0 0 (c-1)).mpr ⟨by omega,by omega⟩)
        simp only [cube, Finset.mem_product, Finset.mem_Icc] at hx
        omega
      have hv := card_volume_bounds A
      obtain ⟨hy,hz⟩ := coordinate_images A hpos hdown
      rw [hy,hz] at hv
      have hdP : (A.card : ℤ) ≤ a*b*c := by
        dsimp [a,b,c]
        exact_mod_cast hv.1
      have hdF : (A.card : ℤ) ≤ c*F := by
        have hh : (A.card : ℤ) ≤ F*c := by
          dsimp [F,c]
          exact_mod_cast hv.2.1
        simpa only [mul_comm] using hh
      have hdG : (A.card : ℤ) ≤ b*G := by
        have hh : (A.card : ℤ) ≤ G*b := by
          dsimp [G,b]
          exact_mod_cast hv.2.2.1
        simpa only [mul_comm] using hh
      have hdH : (A.card : ℤ) ≤ a*H := by
        have hh : (A.card : ℤ) ≤ H*a := by
          dsimp [H,a]
          exact_mod_cast hv.2.2.2
        simpa only [mul_comm] using hh
      have hscalar := scalar_deficit a b c A.card F G H ha hb hc
        (by positivity) hdP hdF hdG hdH
      have heq : ((mixedSum A).card : ℤ) =
          (a+b-1)*F+(a+c-1)*G+(b+c-1)*H+2*a*b*c-(a+b+c-1)^2 :=
        card_mixedSum_exact A hne hpos hdown
      have hboundary := boundary_le_cube a b c N ha hb hc haN hbN hcN
      rw [← heq] at hscalar
      nlinarith only [hscalar,hboundary]
    · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      simp only [Finset.card_empty, Nat.cast_zero, sub_zero]
      have hnonneg : 0 ≤ 12*N^2-6*N+1 := by nlinarith [sq_nonneg N]
      nlinarith only [hnonneg]
  have hsA : ((cube 0 0 0 N \ A).card : ℤ)+(A.card : ℤ) = N^3 := by
    have hh := congrArg (fun n : ℕ => (n : ℤ)) hsplitA
    push_cast at hh
    exact hh.trans hcube
  have hsM : ((mixedSum (cube 0 0 0 N) \ mixedSum A).card : ℤ)+
      ((mixedSum A).card : ℤ) = (2*N-1)^3 := by
    have hh := congrArg (fun n : ℕ => (n : ℤ)) hsplitM
    push_cast at hh
    exact hh.trans hmix
  have hfinal : ((mixedSum (cube 0 0 0 N) \ mixedSum A).card : ℤ) ≤
      8*((cube 0 0 0 N \ A).card : ℤ) := by omega
  exact_mod_cast hfinal

example :
    1 ≤ (1 : ℤ) ∧ ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)) ⊆ cube 0 0 0 1 ∧
    (∀ s ∈ ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)), ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ ({(0,0,0)} : Finset (ℤ × ℤ × ℤ))) := by
  refine ⟨by norm_num, by decide, ?_⟩
  simp only [Finset.mem_singleton]
  rintro s rfl ⟨x,y,z⟩ hx hx' hy hy' hz hz'
  dsimp at *
  apply Prod.ext <;> simp only [Prod.mk.injEq] <;> omega

end NoncommutingDownsetSharpEight
