/-
The elementary pair-cover lower bound for the Erdős–Lovász number.

Pair distinct edges and choose a common vertex for each pair; a possible
unpaired edge needs one more vertex. Strong induction implements this
without choosing an ordering or a partition into pairs. The structural
lemma works on arbitrary ground types, including empty and infinite ones.
The covering-number corollary uses the existing finite-ground definition.
No archived literature theorem from `ErdosLovasz` is used.
-/
import Erdos.ErdosLovasz

set_option autoImplicit false

/- Joint satisfiability: a singleton edge, and two distinct intersecting
edges, satisfy the structural hypotheses. The singleton is also an actual
Erdős–Lovász family at the first intended parameter. -/
example : (∅ : Finset (Fin 1)) ∉ ({({0} : Finset (Fin 1))} : Finset (Finset (Fin 1))) ∧
    (∀ A ∈ ({({0} : Finset (Fin 1))} : Finset (Finset (Fin 1))),
      ∀ B ∈ ({({0} : Finset (Fin 1))} : Finset (Finset (Fin 1))),
        A ≠ B → ¬ Disjoint A B) := by
  decide

example : (∅ : Finset (Fin 3)) ∉ ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))) ∧
    (∀ A ∈ ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))),
      ∀ B ∈ ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))),
        A ≠ B → ¬ Disjoint A B) := by
  decide

example : IsErdosLovaszFamily 1 ({({0} : Finset (Fin 1))} : Finset (Finset (Fin 1))) := by
  unfold IsErdosLovaszFamily
  decide

/-- A finite family of nonempty edges whose distinct members intersect has
a transversal `T` with `2 * T.card ≤ F.card + 1`. The ground type need not
be finite or inhabited; the empty family is covered by the empty set. -/
theorem exists_isTransversal_two_mul_card_le {α : Type*} {F : Finset (Finset α)}
    (h : ∅ ∉ F) (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ Disjoint A B) :
    ∃ T : Finset α, IsTransversal F T ∧ 2 * T.card ≤ F.card + 1 := by
  classical
  revert h hint
  refine Finset.strongInductionOn F ?_
  intro G ih h hint
  rcases Finset.eq_empty_or_nonempty G with rfl | hGne
  · exact ⟨∅, isTransversal_empty_left ∅, by simp⟩
  by_cases hsmall : G.card ≤ 1
  · have hcard : G.card = 1 := by
      have hpos : 0 < G.card := Finset.card_pos.mpr hGne
      omega
    obtain ⟨A, rfl⟩ := Finset.card_eq_one.mp hcard
    have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro hA
      exact h (by simp [hA]))
    obtain ⟨x, hx⟩ := hAne
    refine ⟨{x}, ?_, by simp⟩
    intro B hB
    have hBA : B = A := Finset.mem_singleton.mp hB
    exact ⟨x, hBA ▸ hx, Finset.mem_singleton_self x⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < G.card)
  obtain ⟨x, hxA, hxB⟩ := Finset.not_disjoint_iff.mp (hint A hA B hB hAB)
  let H := (G.erase A).erase B
  have hHsub : H ⊆ G := fun C hC =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
  have hHssub : H ⊂ G :=
    Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset B (G.erase A))
      (Finset.erase_ssubset hA)
  have hHempty : ∅ ∉ H := fun hmem => h (hHsub hmem)
  have hHint : ∀ C ∈ H, ∀ D ∈ H, C ≠ D → ¬ Disjoint C D :=
    fun C hC D hD hCD => hint C (hHsub hC) D (hHsub hD) hCD
  obtain ⟨T, hT, hTcard⟩ := ih H hHssub hHempty hHint
  have hins : IsTransversal G (insert x T) := by
    intro C hC
    by_cases hCA : C = A
    · exact ⟨x, hCA ▸ hxA, Finset.mem_insert_self x T⟩
    by_cases hCB : C = B
    · exact ⟨x, hCB ▸ hxB, Finset.mem_insert_self x T⟩
    · have hCH : C ∈ H :=
        Finset.mem_erase.mpr ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hC⟩⟩
      obtain ⟨y, hyC, hyT⟩ := hT C hCH
      exact ⟨y, hyC, Finset.mem_insert_of_mem hyT⟩
  have hBerase : B ∈ G.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hcardA : (G.erase A).card + 1 = G.card := Finset.card_erase_add_one hA
  have hcardB : H.card + 1 = (G.erase A).card := Finset.card_erase_add_one hBerase
  have hcardH : H.card + 2 = G.card := by omega
  have hcardins : (insert x T).card ≤ T.card + 1 := Finset.card_insert_le x T
  exact ⟨insert x T, hins, by omega⟩

/-- The transversal number of an intersecting finite family satisfies
`2 * coveringNumber F ≤ F.card + 1`. The explicit no-empty-edge guard
excludes the junk value of `coveringNumber` when no transversal exists. -/
theorem two_mul_coveringNumber_le_card_add_one {α : Type*} [DecidableEq α] [Fintype α]
    {F : Finset (Finset α)} (h : ∅ ∉ F)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ Disjoint A B) :
    2 * coveringNumber F ≤ F.card + 1 := by
  obtain ⟨T, hT, hTcard⟩ := exists_isTransversal_two_mul_card_le h hint
  have hcover : coveringNumber F ≤ T.card := coveringNumber_le_card hT
  omega

/-- An Erdős–Lovász family of `r`-sets has at least `2 * r - 1` edges,
in subtraction-free form. This holds on arbitrary ground types; at `r = 0`
it merely states a nonnegative bound, and does not assume an inhabited type. -/
theorem IsErdosLovaszFamily.two_mul_le_card_add_one {α : Type*} {r : ℕ}
    {F : Finset (Finset α)} (hF : IsErdosLovaszFamily r F) :
    2 * r ≤ F.card + 1 := by
  obtain ⟨T, hT, hTcard⟩ := exists_isTransversal_two_mul_card_le hF.empty_notMem
    (fun A hA B hB _ => hF.2.1 A hA B hB)
  have hrT : r ≤ T.card := by
    by_contra hnot
    have hsmall : T.card < r := by omega
    obtain ⟨A, hA, hdisj⟩ := hF.2.2 T hsmall
    obtain ⟨x, hxA, hxT⟩ := hT A hA
    exact Finset.disjoint_left.mp hdisj hxA hxT
  omega

/-- For positive `r`, every Erdős–Lovász family of `r`-sets has at least
`2 * r - 1` edges. Positivity keeps natural subtraction untruncated. -/
theorem IsErdosLovaszFamily.two_mul_sub_one_le_card {α : Type*} {r : ℕ}
    {F : Finset (Finset α)} (hF : IsErdosLovaszFamily r F) (hr : 0 < r) :
    2 * r - 1 ≤ F.card := by
  have hbound : 2 * r ≤ F.card + 1 := hF.two_mul_le_card_add_one
  omega

/-- The elementary pair-cover Erdős–Lovász lower bound: `2 * r - 1 ≤ g(r)`
for every positive integer `r`. The minimum is attained by an actual family,
so the proof never uses the default value of an empty infimum. -/
theorem two_mul_sub_one_le_erdosLovaszNum {r : ℕ} (hr : 0 < r) :
    2 * r - 1 ≤ erdosLovaszNum r := by
  obtain ⟨N, F, hF, hcard⟩ := erdosLovaszNum_mem hr
  exact hcard ▸ hF.two_mul_sub_one_le_card hr

/- Boundary checks: empty and infinite ground types, an even pair of edges,
and the sharp odd triangle; the lower bound is sharp at r = 1 and r = 2. -/
example : ∃ T : Finset (Fin 0), IsTransversal ∅ T ∧ 2 * T.card ≤ 1 := by
  exact exists_isTransversal_two_mul_card_le (by simp) (by simp)

example : 2 * coveringNumber (∅ : Finset (Finset (Fin 0))) ≤ 0 + 1 := by
  decide

example : ∃ T : Finset ℕ, IsTransversal {{0, 1}, {1, 2}} T ∧ 2 * T.card ≤ 3 := by
  exact exists_isTransversal_two_mul_card_le (by decide) (by decide)

example : 2 * coveringNumber ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))) ≤ 2 + 1 := by
  decide

example : 2 * coveringNumber ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))) = 3 + 1 := by
  decide

example : 2 * 1 - 1 = erdosLovaszNum 1 := by rw [erdosLovaszNum_one]
example : 2 * 2 - 1 = erdosLovaszNum 2 := by rw [erdosLovaszNum_two]

#check @exists_isTransversal_two_mul_card_le
#check @two_mul_coveringNumber_le_card_add_one
#check @IsErdosLovaszFamily.two_mul_le_card_add_one
#check @IsErdosLovaszFamily.two_mul_sub_one_le_card
#check @two_mul_sub_one_le_erdosLovaszNum

#print axioms exists_isTransversal_two_mul_card_le
#print axioms two_mul_coveringNumber_le_card_add_one
#print axioms IsErdosLovaszFamily.two_mul_le_card_add_one
#print axioms IsErdosLovaszFamily.two_mul_sub_one_le_card
#print axioms two_mul_sub_one_le_erdosLovaszNum
