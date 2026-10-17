import BilinearComplexity.BooleanRankGeneric

set_option autoImplicit false

namespace BilinearComplexity
namespace BooleanRankIrreducibles

open Finset

/-- The columns where a Boolean row is one. -/
def oneSupport {n : ℕ} (v : Fin n → BoolSemiring) : Finset (Fin n) :=
  univ.filter (fun j => v j = 1)

/-- Distinct nonempty supports of the displayed rows; zero rows are discarded. -/
def supportFamily {m n : ℕ} (A : BoolMatrix m n) : Finset (Finset (Fin n)) :=
  (univ.image (fun i => oneSupport (A i))).filter (fun S => S.Nonempty)

/-- Members not expressible as a union of a subfamily of the other members. -/
def irreducibleFamily {α : Type*} [DecidableEq α] (F : Finset (Finset α)) :
    Finset (Finset α) :=
  F.filter (fun S => ¬ ∃ G ⊆ F.erase S, G.biUnion id = S)

example : oneSupport (fun _ : Fin 2 => (1 : BoolSemiring)) = univ := by decide
example : supportFamily (0 : BoolMatrix 2 2) = ∅ := by decide
example : supportFamily (fun _ _ => 1 : BoolMatrix 2 2) = {univ} := by decide
example : irreducibleFamily ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) =
    {{0}, {1}} := by decide

/-- Equality of supports detects equality of Boolean rows. -/
theorem oneSupport_injective {n : ℕ} :
    Function.Injective (@oneSupport n) := by
  intro u v h
  funext j
  have hj : u j = 1 ↔ v j = 1 := by
    have := Finset.ext_iff.mp h j
    simpa [oneSupport] using this
  have hu := BoolSemiring.eq_zero_or_eq_one (u j)
  have hv := BoolSemiring.eq_zero_or_eq_one (v j)
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp_all

/-- Support turns the actual Boolean row sum into finite union, including the empty sum. -/
theorem oneSupport_rowsSum {m n : ℕ} (A : BoolMatrix m n) (T : Finset (Fin m)) :
    oneSupport (rowsSum A T) = T.biUnion (fun i => oneSupport (A i)) := by
  ext j
  simp only [oneSupport, mem_filter, mem_univ, true_and, mem_biUnion,
    rowsSum, BoolSemiring.sum_eq_one_iff]

/-- Every member of a finite family is a union of its irreducible members,
provided all members are nonempty. -/
theorem generated_by_irreducibles {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (_hne : ∀ S ∈ F, S.Nonempty) :
    ∀ S ∈ F, ∃ G ⊆ irreducibleFamily F, G.biUnion id = S := by
  classical
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hSF
    by_cases hJ : S ∈ irreducibleFamily F
    · exact ⟨{S}, singleton_subset_iff.mpr hJ, by simp⟩
    · have hred : ∃ G ⊆ F.erase S, G.biUnion id = S := by
        simpa [irreducibleFamily, hSF] using hJ
      obtain ⟨G, hGF, hGS⟩ := hred
      have hsmall : ∀ T ∈ G, T ⊂ S := by
        intro T hTG
        have hTF := mem_erase.mp (hGF hTG)
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, hTF.1⟩
        intro x hx
        rw [← hGS]
        exact mem_biUnion.mpr ⟨T, hTG, hx⟩
      have hex : ∀ T ∈ G, ∃ K ⊆ irreducibleFamily F, K.biUnion id = T := by
        intro T hTG
        exact ih T (hsmall T hTG) (mem_erase.mp (hGF hTG)).2
      choose K hKsub hKeq using hex
      refine ⟨G.biUnion (fun T => if h : T ∈ G then K T h else ∅), ?_, ?_⟩
      · intro T hT
        obtain ⟨U, hUG, hTU⟩ := mem_biUnion.mp hT
        simp only [dif_pos hUG] at hTU
        exact hKsub U hUG hTU
      · ext x
        constructor
        · intro hx
          obtain ⟨T, hTK, hxT⟩ := mem_biUnion.mp hx
          obtain ⟨U, hUG, hTU⟩ := mem_biUnion.mp hTK
          simp only [dif_pos hUG] at hTU
          rw [← hGS]
          exact mem_biUnion.mpr ⟨U, hUG, by
            rw [← hKeq U hUG]
            exact mem_biUnion.mpr ⟨T, hTU, hxT⟩⟩
        · intro hx
          rw [← hGS] at hx
          obtain ⟨U, hUG, hxU⟩ := mem_biUnion.mp hx
          rw [← hKeq U hUG] at hxU
          obtain ⟨T, hTU, hxT⟩ := mem_biUnion.mp hxU
          exact mem_biUnion.mpr ⟨T, mem_biUnion.mpr
            ⟨U, hUG, by simpa only [dif_pos hUG] using hTU⟩, hxT⟩

/-- Unions of unions from a family are again unions from that family. -/
theorem union_of_generated {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset β) (f : β → Finset α) (F : Finset (Finset α))
    (h : ∀ i ∈ I, ∃ G ⊆ F, G.biUnion id = f i) :
    ∃ G ⊆ F, G.biUnion id = I.biUnion f := by
  classical
  choose G hsub heq using h
  refine ⟨I.biUnion (fun i => if hi : i ∈ I then G i hi else ∅), ?_, ?_⟩
  · intro S hS
    obtain ⟨i, hi, hSi⟩ := mem_biUnion.mp hS
    simp only [dif_pos hi] at hSi
    exact hsub i hi hSi
  · ext x
    simp only [mem_biUnion, id_eq]
    constructor
    · rintro ⟨S, ⟨i, hi, hSi⟩, hx⟩
      simp only [dif_pos hi] at hSi
      exact ⟨i, hi, by rw [← heq i hi]; exact mem_biUnion.mpr ⟨S, hSi, hx⟩⟩
    · rintro ⟨i, hi, hx⟩
      rw [← heq i hi] at hx
      obtain ⟨S, hSi, hxS⟩ := mem_biUnion.mp hx
      exact ⟨S, ⟨i, hi, by simpa only [dif_pos hi] using hSi⟩, hxS⟩

/-- A vector is in the actual row span exactly when its support is a union
of supports of rows from the selected index family. -/
theorem mem_rowSpan_iff_support {m n : ℕ} (A : BoolMatrix m n)
    (I : Finset (Fin m)) (v : Fin n → BoolSemiring) :
    v ∈ rowSpan A I ↔ ∃ G ⊆ I.image (fun i => oneSupport (A i)),
      G.biUnion id = oneSupport v := by
  classical
  constructor
  · rintro hv
    obtain ⟨T, hT, hTv⟩ := mem_image.mp hv
    refine ⟨T.image (fun i => oneSupport (A i)), image_subset_image (mem_powerset.mp hT), ?_⟩
    rw [← hTv, oneSupport_rowsSum]
    ext j
    simp
  · rintro ⟨G, hG, hGv⟩
    let T := I.filter (fun i => oneSupport (A i) ∈ G)
    have hsum : oneSupport (rowsSum A T) = oneSupport v := by
      rw [oneSupport_rowsSum, ← hGv]
      ext j
      simp only [mem_biUnion, T, mem_filter, id_eq]
      constructor
      · rintro ⟨i, ⟨hi, hiG⟩, hj⟩
        exact ⟨oneSupport (A i), hiG, hj⟩
      · rintro ⟨S, hSG, hjS⟩
        obtain ⟨i, hi, rfl⟩ := mem_image.mp (hG hSG)
        exact ⟨i, ⟨hi, hSG⟩, hjS⟩
    exact mem_image.mpr ⟨T, mem_powerset.mpr (filter_subset _ _),
      oneSupport_injective hsum⟩

/-- Spanning every displayed row suffices to span all subset sums, not just
the total OR of the matrix. -/
theorem rowSpan_eq_of_rows_mem {m n : ℕ} (A : BoolMatrix m n)
    (I : Finset (Fin m)) (h : ∀ i, A i ∈ rowSpan A I) :
    rowSpan A I = rowSpan A univ := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨T, mem_powerset.mpr (subset_univ T), rfl⟩
  · intro v hv
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hv
    rw [mem_rowSpan_iff_support, oneSupport_rowsSum]
    exact union_of_generated T (fun i => oneSupport (A i))
      (I.image (fun i => oneSupport (A i)))
      (fun i _ => (mem_rowSpan_iff_support A I (A i)).mp (h i))

/-- A spanning displayed-index family contains each irreducible nonempty
support among its own row supports, even when rows repeat. -/
theorem irreducibles_subset_image_of_span_eq {m n : ℕ} (A : BoolMatrix m n)
    (I : Finset (Fin m)) (hspan : rowSpan A I = rowSpan A univ) :
    irreducibleFamily (supportFamily A) ⊆ I.image (fun i => oneSupport (A i)) := by
  classical
  intro S hSJ
  obtain ⟨hSF, hirr⟩ := mem_filter.mp hSJ
  obtain ⟨hSimage, hSne⟩ := mem_filter.mp hSF
  obtain ⟨i, hi, hSi⟩ := mem_image.mp hSimage
  have hrow : A i ∈ rowSpan A I := by
    rw [hspan]
    exact mem_rowSpan_self A (mem_univ i)
  obtain ⟨G, hG, hGS⟩ := (mem_rowSpan_iff_support A I (A i)).mp hrow
  rw [hSi] at hGS
  by_contra hnot
  apply hirr
  refine ⟨G.erase ∅, ?_, ?_⟩
  · intro T hT
    obtain ⟨hTne, hTG⟩ := mem_erase.mp hT
    refine mem_erase.mpr ⟨?_, ?_⟩
    · intro hTS
      exact hnot (hTS ▸ hG hTG)
    · obtain ⟨k, hk, hkT⟩ := mem_image.mp (hG hTG)
      exact mem_filter.mpr ⟨mem_image.mpr ⟨k, mem_univ k, hkT⟩,
        Finset.nonempty_iff_ne_empty.mpr hTne⟩
  · rw [← hGS]
    ext j
    simp only [mem_biUnion, mem_erase, id_eq]
    constructor
    · rintro ⟨T, ⟨hTne, hTG⟩, hjT⟩
      exact ⟨T, hTG, hjT⟩
    · rintro ⟨T, hTG, hjT⟩
      exact ⟨T, ⟨by intro he; simp_all, hTG⟩, hjT⟩

/-- Every spanning displayed-index family has at least as many indices
as there are distinct irreducible nonempty supports. -/
theorem irreducibles_card_le_of_span_eq {m n : ℕ} (A : BoolMatrix m n)
    (I : Finset (Fin m)) (hspan : rowSpan A I = rowSpan A univ) :
    (irreducibleFamily (supportFamily A)).card ≤ I.card := by
  exact (card_le_card (irreducibles_subset_image_of_span_eq A I hspan)).trans
    (card_image_le)

/-- Selecting one displayed representative per irreducible support gives
a spanning family of at most that cardinality. -/
theorem boolRowRankLE_irreducibles_card {m n : ℕ} (A : BoolMatrix m n) :
    BoolRowRankLE A (irreducibleFamily (supportFamily A)).card := by
  classical
  let J := irreducibleFamily (supportFamily A)
  have hrep : ∀ S : J, ∃ i : Fin m, oneSupport (A i) = S.val := by
    intro S
    have hSF := (mem_filter.mp S.property).1
    obtain ⟨i, hi, hSi⟩ := mem_image.mp (mem_filter.mp hSF).1
    exact ⟨i, hSi⟩
  choose rep hrep using hrep
  let I := J.attach.image rep
  have himage : I.image (fun i => oneSupport (A i)) = J := by
    ext S
    constructor
    · intro hS
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hS
      obtain ⟨T, hT, rfl⟩ := mem_image.mp hi
      rw [hrep T]
      exact T.property
    · intro hS
      exact mem_image.mpr ⟨rep ⟨S, hS⟩,
        mem_image.mpr ⟨⟨S, hS⟩, mem_attach _ _, rfl⟩, hrep ⟨S, hS⟩⟩
  refine ⟨I, ?_, rowSpan_eq_of_rows_mem A I ?_⟩
  · calc I.card ≤ J.attach.card := card_image_le
         _ = J.card := card_attach
  · intro i
    rw [mem_rowSpan_iff_support, himage]
    by_cases hzero : oneSupport (A i) = ∅
    · exact ⟨∅, empty_subset J, by simpa using hzero.symm⟩
    · apply generated_by_irreducibles (supportFamily A)
        (fun S hS => (mem_filter.mp hS).2)
      exact mem_filter.mpr ⟨mem_image.mpr ⟨i, mem_univ i, rfl⟩,
        Finset.nonempty_iff_ne_empty.mpr hzero⟩

/-- For every rectangular Boolean matrix, including empty dimensions,
the actual Boolean row rank equals the number of distinct nonempty
displayed supports not expressible as a union of other displayed supports. -/
theorem boolRowRank_eq_irreducibles_card {m n : ℕ} (A : BoolMatrix m n) :
    boolRowRank A = (irreducibleFamily (supportFamily A)).card := by
  apply Nat.le_antisymm
  · exact boolRowRank_le_of_boolRowRankLE (boolRowRankLE_irreducibles_card A)
  · obtain ⟨I, hcard, hspan⟩ := boolRowRankLE_boolRowRank A
    exact (irreducibles_card_le_of_span_eq A I hspan).trans hcard

example : boolRowRank (0 : BoolMatrix 0 2) = 0 := by
  rw [boolRowRank_eq_irreducibles_card]
  decide

example : boolRowRank (0 : BoolMatrix 2 0) = 0 := by
  rw [boolRowRank_eq_irreducibles_card]
  decide

example : boolRowRank (0 : BoolMatrix 0 0) = 0 := by
  rw [boolRowRank_eq_irreducibles_card]
  decide

example : boolRowRank (0 : BoolMatrix 2 3) = 0 := by
  rw [boolRowRank_eq_irreducibles_card]
  decide

example : boolRowRank (fun _ _ => 1 : BoolMatrix 3 2) = 1 := by
  rw [boolRowRank_eq_irreducibles_card]
  decide

example : boolRowRank (fun i _ => if i = 0 then 0 else 1 : BoolMatrix 3 2) = 1 := by
  rw [boolRowRank_eq_irreducibles_card]
  decide

example : boolRowRank (boolId 2) = 2 := by
  rw [boolRowRank_eq_irreducibles_card]
  decide

example : ∃ G ⊆ irreducibleFamily (supportFamily (boolId 2)),
    G.biUnion id = oneSupport (boolId 2 0) := by
  apply generated_by_irreducibles (supportFamily (boolId 2))
  · decide
  · decide

example : ∃ G ⊆ ({{0}, {1}} : Finset (Finset (Fin 2))),
    G.biUnion id = ({0, 1} : Finset (Fin 2)) := by
  exact union_of_generated ({0, 1} : Finset (Fin 2)) (fun i => {i})
    {{0}, {1}} (by decide)

example : (irreducibleFamily (supportFamily (boolId 2))).card ≤
    (univ : Finset (Fin 2)).card :=
  irreducibles_card_le_of_span_eq (boolId 2) univ rfl

example : rowSpan (boolId 2) univ = rowSpan (boolId 2) univ :=
  rowSpan_eq_of_rows_mem (boolId 2) univ
    (fun i => mem_rowSpan_self (boolId 2) (mem_univ i))

end BooleanRankIrreducibles
end BilinearComplexity
