import Combinatorics.NoncommutingFiber
import Mathlib.Data.Int.Interval

set_option autoImplicit false

namespace NoncommutingCubeCounting

open NoncommutingFiber
open scoped Pointwise

/-- The integer cube with lower corner `(r1,r2,r3)` and integer side length `N`.
For `1 ≤ N` each factor has `N` integer points. -/
noncomputable def cube (r1 r2 r3 N : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc r1 (r1 + N - 1) ×ˢ
    (Finset.Icc r2 (r2 + N - 1) ×ˢ Finset.Icc r3 (r3 + N - 1))

example : cube 1 2 3 1 = {(1,2,3)} := by decide
example : cube 1 2 3 0 = ∅ := by decide

/-- The lower corner belongs to every positive-side cube, so these cubes are nonempty. -/
theorem corner_mem_cube (r1 r2 r3 N : ℤ) (hN : 1 ≤ N) :
    (r1,r2,r3) ∈ cube r1 r2 r3 N := by
  simp only [cube, Finset.mem_product, Finset.mem_Icc]
  omega

/-- Actual mixed-sum outputs have the three signed coordinate ranges determined by
`L0(x,y,z)=(y,-x,0)`, `L1(x,y,z)=(z,0,-x)`, and `L2(x,y,z)=(0,z,-y)`. -/
theorem mixedSum_cube_ranges (r1 r2 r3 N : ℤ) (_hN : 1 ≤ N)
    (s : ℤ × ℤ × ℤ) (hs : s ∈ mixedSum (cube r1 r2 r3 N)) :
    s.1 ∈ Finset.Icc (r2 + r3) (r2 + r3 + 2*N - 2) ∧
    s.2.1 ∈ Finset.Icc (-r1 + r3 - N + 1) (-r1 + r3 + N - 1) ∧
    s.2.2 ∈ Finset.Icc (-r1 - r2 - 2*N + 2) (-r1 - r2) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hs
  obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_add.mp hu
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
  simp only [cube, Finset.mem_product, Finset.mem_Icc] at hx hy hz
  simp only [L0, L1, L2, Prod.fst_add, Prod.snd_add, Finset.mem_Icc]
  omega

/-- The three actual output intervals all contain exactly `2*N-1` integers. -/
theorem output_interval_cards (r1 r2 r3 N : ℤ) (_hN : 1 ≤ N) :
    (Finset.Icc (r2 + r3) (r2 + r3 + 2*N - 2)).card = (2*N-1).toNat ∧
    (Finset.Icc (-r1 + r3 - N + 1) (-r1 + r3 + N - 1)).card =
      (2*N-1).toNat ∧
    (Finset.Icc (-r1 - r2 - 2*N + 2) (-r1 - r2)).card = (2*N-1).toNat := by
  simp only [Int.card_Icc]
  constructor
  · congr 1
    ring
  constructor
  · congr 1
    ring
  · congr 1
    ring

/-- Counting by coordinates one and two: pair with the unused third coordinate
injects into `T × U`. No independence of coordinates is assumed. -/
theorem card_le_pair12 (S : Finset (ℤ × ℤ × ℤ))
    (T : Finset (ℤ × ℤ)) (U : Finset ℤ)
    (hT : ∀ s ∈ S, (s.1,s.2.1) ∈ T) (hU : ∀ s ∈ S, s.2.2 ∈ U) :
    S.card ≤ U.card * T.card := by
  have hcount : S.card ≤ (T ×ˢ U).card := by
    apply Finset.card_le_card_of_injOn (fun s => ((s.1,s.2.1),s.2.2))
    · intro s hs
      exact Finset.mem_product.mpr ⟨hT s hs, hU s hs⟩
    · rintro ⟨a,b,c⟩ _ ⟨a',b',c'⟩ _ he
      simpa only [Prod.mk.injEq, and_assoc] using he
  simpa only [Finset.card_product, Nat.mul_comm] using hcount

/-- Counting by coordinates one and three, with the unused second coordinate. -/
theorem card_le_pair13 (S : Finset (ℤ × ℤ × ℤ))
    (T : Finset (ℤ × ℤ)) (U : Finset ℤ)
    (hT : ∀ s ∈ S, (s.1,s.2.2) ∈ T) (hU : ∀ s ∈ S, s.2.1 ∈ U) :
    S.card ≤ U.card * T.card := by
  have hcount : S.card ≤ (T ×ˢ U).card := by
    apply Finset.card_le_card_of_injOn (fun s => ((s.1,s.2.2),s.2.1))
    · intro s hs
      exact Finset.mem_product.mpr ⟨hT s hs, hU s hs⟩
    · rintro ⟨a,b,c⟩ _ ⟨a',b',c'⟩ _ he
      simpa only [Prod.mk.injEq, and_assoc, and_left_comm, and_comm] using he
  simpa only [Finset.card_product, Nat.mul_comm] using hcount

/-- Counting by coordinates two and three, with the unused first coordinate. -/
theorem card_le_pair23 (S : Finset (ℤ × ℤ × ℤ))
    (T : Finset (ℤ × ℤ)) (U : Finset ℤ)
    (hT : ∀ s ∈ S, (s.2.1,s.2.2) ∈ T) (hU : ∀ s ∈ S, s.1 ∈ U) :
    S.card ≤ U.card * T.card := by
  have hcount : S.card ≤ (T ×ˢ U).card := by
    apply Finset.card_le_card_of_injOn (fun s => ((s.2.1,s.2.2),s.1))
    · intro s hs
      exact Finset.mem_product.mpr ⟨hT s hs, hU s hs⟩
    · rintro ⟨a,b,c⟩ _ ⟨a',b',c'⟩ _ he
      simpa only [Prod.mk.injEq, and_assoc, and_left_comm, and_comm] using he
  simpa only [Finset.card_product, Nat.mul_comm] using hcount

/-- A pair constraint on coordinates one and two costs at most `2*N-1`
actual mixed-sum outputs per pair. -/
theorem card_le_cube_pair12 (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (S : Finset (ℤ × ℤ × ℤ)) (T : Finset (ℤ × ℤ))
    (hS : S ⊆ mixedSum (cube r1 r2 r3 N))
    (hT : ∀ s ∈ S, (s.1,s.2.1) ∈ T) :
    S.card ≤ (2*N-1).toNat * T.card := by
  have hc := card_le_pair12 S T
    (Finset.Icc (-r1-r2-2*N+2) (-r1-r2)) hT
    (fun s hs => (mixedSum_cube_ranges r1 r2 r3 N hN s (hS hs)).2.2)
  rw [(output_interval_cards r1 r2 r3 N hN).2.2] at hc
  exact hc

/-- The same output-counting bound for constraints on coordinates one and three. -/
theorem card_le_cube_pair13 (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (S : Finset (ℤ × ℤ × ℤ)) (T : Finset (ℤ × ℤ))
    (hS : S ⊆ mixedSum (cube r1 r2 r3 N))
    (hT : ∀ s ∈ S, (s.1,s.2.2) ∈ T) :
    S.card ≤ (2*N-1).toNat * T.card := by
  have hc := card_le_pair13 S T
    (Finset.Icc (-r1+r3-N+1) (-r1+r3+N-1)) hT
    (fun s hs => (mixedSum_cube_ranges r1 r2 r3 N hN s (hS hs)).2.1)
  rw [(output_interval_cards r1 r2 r3 N hN).2.1] at hc
  exact hc

/-- The same output-counting bound for constraints on coordinates two and three. -/
theorem card_le_cube_pair23 (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (S : Finset (ℤ × ℤ × ℤ)) (T : Finset (ℤ × ℤ))
    (hS : S ⊆ mixedSum (cube r1 r2 r3 N))
    (hT : ∀ s ∈ S, (s.2.1,s.2.2) ∈ T) :
    S.card ≤ (2*N-1).toNat * T.card := by
  have hc := card_le_pair23 S T
    (Finset.Icc (r2+r3) (r2+r3+2*N-2)) hT
    (fun s hs => (mixedSum_cube_ranges r1 r2 r3 N hN s (hS hs)).1)
  rw [(output_interval_cards r1 r2 r3 N hN).1] at hc
  exact hc

/-- A finite set covered by three pair-lifts has cardinality at most the sum
of the three pair counts times their respective unused-coordinate counts.
The coordinate ranges may differ and the three lifts need not be disjoint. -/
theorem card_le_pair_lift_union (S : Finset (ℤ × ℤ × ℤ))
    (T0 T1 T2 : Finset (ℤ × ℤ)) (Q0 Q1 Q2 : Finset ℤ)
    (hcover : ∀ s ∈ S,
      ((s.1,s.2.1) ∈ T0 ∧ s.2.2 ∈ Q0) ∨
      ((s.1,s.2.2) ∈ T1 ∧ s.2.1 ∈ Q1) ∨
      ((s.2.1,s.2.2) ∈ T2 ∧ s.1 ∈ Q2)) :
    S.card ≤ Q0.card * T0.card + Q1.card * T1.card + Q2.card * T2.card := by
  let E0 := S.filter (fun s => (s.1,s.2.1) ∈ T0 ∧ s.2.2 ∈ Q0)
  let E1 := S.filter (fun s => (s.1,s.2.2) ∈ T1 ∧ s.2.1 ∈ Q1)
  let E2 := S.filter (fun s => (s.2.1,s.2.2) ∈ T2 ∧ s.1 ∈ Q2)
  have hS : S ⊆ E0 ∪ E1 ∪ E2 := by
    intro s hs
    rcases hcover s hs with h0 | h1 | h2
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs,h0⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,h1⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,h2⟩)
  have c0 : E0.card ≤ Q0.card * T0.card :=
    card_le_pair12 E0 T0 Q0
      (fun _ hs => (Finset.mem_filter.mp hs).2.1)
      (fun _ hs => (Finset.mem_filter.mp hs).2.2)
  have c1 : E1.card ≤ Q1.card * T1.card :=
    card_le_pair13 E1 T1 Q1
      (fun _ hs => (Finset.mem_filter.mp hs).2.1)
      (fun _ hs => (Finset.mem_filter.mp hs).2.2)
  have c2 : E2.card ≤ Q2.card * T2.card :=
    card_le_pair23 E2 T2 Q2
      (fun _ hs => (Finset.mem_filter.mp hs).2.1)
      (fun _ hs => (Finset.mem_filter.mp hs).2.2)
  calc
    S.card ≤ (E0 ∪ E1 ∪ E2).card := Finset.card_le_card hS
    _ ≤ (E0 ∪ E1).card + E2.card := Finset.card_union_le _ _
    _ ≤ (E0.card + E1.card) + E2.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add c0 c1) c2

/-- Actual cube outputs attributed to any of three output-pair sets have
cardinality at most `(2*N-1)` times the sum of the pair-set cardinalities.
This supplies counting only: geometric pair attribution remains an explicit premise. -/
theorem card_le_cube_pair_union (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (S : Finset (ℤ × ℤ × ℤ)) (T0 T1 T2 : Finset (ℤ × ℤ))
    (hS : S ⊆ mixedSum (cube r1 r2 r3 N))
    (hcover : ∀ s ∈ S, (s.1,s.2.1) ∈ T0 ∨
      (s.1,s.2.2) ∈ T1 ∨ (s.2.1,s.2.2) ∈ T2) :
    S.card ≤ (2*N-1).toNat * (T0.card + T1.card + T2.card) := by
  have hc := card_le_pair_lift_union S T0 T1 T2
    (Finset.Icc (-r1-r2-2*N+2) (-r1-r2))
    (Finset.Icc (-r1+r3-N+1) (-r1+r3+N-1))
    (Finset.Icc (r2+r3) (r2+r3+2*N-2)) (by
      intro s hs
      have hr := mixedSum_cube_ranges r1 r2 r3 N hN s (hS hs)
      rcases hcover s hs with h0 | h1 | h2
      · exact Or.inl ⟨h0,hr.2.2⟩
      · exact Or.inr (Or.inl ⟨h1,hr.2.1⟩)
      · exact Or.inr (Or.inr ⟨h2,hr.1⟩))
  obtain ⟨c1,c2,c3⟩ := output_interval_cards r1 r2 r3 N hN
  rw [c1,c2,c3] at hc
  simpa only [Nat.mul_add] using hc

example :
    (1 : ℤ) ≤ 1 ∧
    (5,2,-3) ∈ mixedSum (cube 1 2 3 1) ∧
    ({(5,2,-3)} : Finset (ℤ × ℤ × ℤ)) ⊆ mixedSum (cube 1 2 3 1) ∧
    (∀ s ∈ ({(5,2,-3)} : Finset (ℤ × ℤ × ℤ)),
      (s.1,s.2.1) ∈ ({(5,2)} : Finset (ℤ × ℤ)) ∧
      (s.1,s.2.2) ∈ ({(5,-3)} : Finset (ℤ × ℤ)) ∧
      (s.2.1,s.2.2) ∈ ({(2,-3)} : Finset (ℤ × ℤ)) ∧
      s.1 ∈ ({5} : Finset ℤ) ∧ s.2.1 ∈ ({2} : Finset ℤ) ∧
      s.2.2 ∈ ({-3} : Finset ℤ)) := by decide

example : ({(5,2,-3)} : Finset (ℤ × ℤ × ℤ)).card ≤
    (2*(1 : ℤ)-1).toNat *
      (({(5,2)} : Finset (ℤ × ℤ)).card +
       ({(5,-3)} : Finset (ℤ × ℤ)).card +
       ({(2,-3)} : Finset (ℤ × ℤ)).card) :=
  card_le_cube_pair_union 1 2 3 1 (by decide) _ _ _ _
    (by decide) (by decide)

end NoncommutingCubeCounting
