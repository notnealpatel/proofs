import Combinatorics.PermutationEndpointOverlapBound
import Combinatorics.PermutationEndpointOverlapTail
import Combinatorics.PermutationMixedEndpointBound
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

set_option autoImplicit false

namespace PermutationSameEdgeAvoidance

open PermutationEndpointCounting PermutationOverlapBound

attribute [local instance] Classical.propDecidable

/-- Positions other than the endpoints in the two short boundary windows. -/
noncomputable def shortBoundary (n K : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p =>
    (1 ≤ p.val ∧ p.val ≤ K - 2) ∨ (n - K + 1 ≤ p.val ∧ p.val ≤ n - 2))

/-- The boundary definition uses precisely the two closed integer intervals. -/
theorem mem_shortBoundary {n K : ℕ} (p : Fin n) :
    p ∈ shortBoundary n K ↔
      (1 ≤ p.val ∧ p.val ≤ K - 2) ∨ (n - K + 1 ≤ p.val ∧ p.val ≤ n - 2) := by
  simp [shortBoundary]

example : shortBoundary 6 3 = {1, 4} := by decide +kernel

/-- Both short boundary windows avoid zero and the terminal position. -/
theorem shortBoundary_interior {n K : ℕ} (hK : 3 ≤ K) (hn : 2 * K ≤ n)
    (q : Fin n) (hq : q.val + 1 = n) (p : Fin n) (hp : p ∈ shortBoundary n K) :
    p.val ≠ 0 ∧ p ≠ q := by
  have hp' := (mem_shortBoundary p).mp hp
  constructor
  · omega
  · intro he
    have hv := congrArg Fin.val he
    omega

/-- Under separation, the two short windows contain exactly `2*K-4` positions. -/
theorem card_shortBoundary {n K : ℕ} (hK : 3 ≤ K) (hn : 2 * K ≤ n) :
    (shortBoundary n K).card = 2 * K - 4 := by
  classical
  let a : Fin n := ⟨1, by omega⟩
  let b : Fin n := ⟨K - 2, by omega⟩
  let c : Fin n := ⟨n - K + 1, by omega⟩
  let d : Fin n := ⟨n - 2, by omega⟩
  have heq : shortBoundary n K = Finset.Icc a b ∪ Finset.Icc c d := by
    ext p
    simp [mem_shortBoundary, Fin.le_def, a, b, c, d]
  have hd : Disjoint (Finset.Icc a b) (Finset.Icc c d) := by
    apply Finset.disjoint_left.mpr
    intro p hp1 hp2
    simp only [Finset.mem_Icc, Fin.le_def] at hp1 hp2
    dsimp [a, b, c, d] at hp1 hp2
    omega
  rw [heq, Finset.card_union_of_disjoint hd, Fin.card_Icc, Fin.card_Icc]
  dsimp [a, b, c, d]
  omega

/-- If every short boundary label exceeds both endpoints, no short overlap occurs.
The witness comparison is the first versus last coordinate of the window. -/
theorem not_overlap_of_boundary_large {n K : ℕ} [NeZero n]
    (hK : 3 ≤ K) (hn : 2 * K ≤ n) (q m l : Fin n) (hq : q.val + 1 = n)
    (π : FixedTwo (0 : Fin n) q m l)
    (hlarge : ∀ p ∈ shortBoundary n K, max m.val l.val < (π.val p).val)
    (k : ℕ) (hk : 2 ≤ k) (hkK : k < K) (hkn : k < n) :
    ¬ Overlap hkn π.val := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨k - 1, by omega⟩
  let p : Fin n := ⟨k - 1, by omega⟩
  let r : Fin n := ⟨n - k, by omega⟩
  have hp : p ∈ shortBoundary n K := by
    apply (mem_shortBoundary p).mpr
    left
    dsimp [p]
    omega
  have hr : r ∈ shortBoundary n K := by
    apply (mem_shortBoundary r).mpr
    right
    dsimp [r]
    omega
  have hpLarge := hlarge p hp
  have hrLarge := hlarge r hr
  have hleft : π.val (0 : Fin n) < π.val p := by
    rw [π.property.1]
    change m.val < (π.val p).val
    exact lt_of_le_of_lt (le_max_left _ _) hpLarge
  have hright : ¬ π.val r < π.val q := by
    rw [π.property.2]
    change ¬ (π.val r).val < l.val
    have hl := le_max_right m.val l.val
    omega
  intro hov
  have hcomp := hov i j
  have hi0 : (⟨i.val, lt_trans i.isLt hkn⟩ : Fin n) = 0 := by
    apply Fin.ext
    rfl
  have hjp : (⟨j.val, lt_trans j.isLt hkn⟩ : Fin n) = p := rfl
  have hiVal : i.val = 0 := rfl
  have hjVal : j.val = k - 1 := rfl
  have hir : (⟨i.val + (n - k), by omega⟩ : Fin n) = r := by
    apply Fin.ext
    change i.val + (n - k) = n - k
    omega
  have hjq : (⟨j.val + (n - k), by omega⟩ : Fin n) = q := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [hi0, hjp, hir, hjq] at hcomp
  exact hright (hcomp.mp hleft)

example : 3 ≤ (3 : ℕ) ∧ 2 * 3 ≤ (6 : ℕ) ∧
    (5 : Fin 6).val + 1 = 6 ∧ (0 : Fin 6) ≠ 1 ∧
    Nonempty (FixedTwo (0 : Fin 6) 5 0 1) := by
  exact ⟨by decide, by decide, rfl, by decide,
    fixedTwo_nonempty 0 5 0 1 (by decide) (by decide)⟩

/-- Every actual overlap is either witnessed by a low short-boundary label or has
length at least `K`; no independence or counting assumption is used. -/
theorem overlap_boundary_or_long {n K : ℕ} [NeZero n]
    (hK : 3 ≤ K) (hn : 2 * K ≤ n) (q m l : Fin n) (hq : q.val + 1 = n)
    (π : FixedTwo (0 : Fin n) q m l)
    (hov : ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val) :
    (∃ p ∈ shortBoundary n K, (π.val p).val ≤ max m.val l.val) ∨
      (∃ k, K ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val) := by
  classical
  by_cases hbad : ∃ p ∈ shortBoundary n K, (π.val p).val ≤ max m.val l.val
  · exact Or.inl hbad
  · right
    obtain ⟨k, hk, hkn, hkπ⟩ := hov
    have hlarge : ∀ p ∈ shortBoundary n K, max m.val l.val < (π.val p).val := by
      intro p hp
      exact lt_of_not_ge (fun hle => hbad ⟨p, hp, hle⟩)
    have hkK : K ≤ k := by
      by_contra h
      exact not_overlap_of_boundary_large hK hn q m l hq π hlarge k hk
        (Nat.lt_of_not_ge h) hkn hkπ
    exact ⟨k, hkK, hkn, hkπ⟩

example : ∃ π : FixedTwo (0 : Fin 6) 5 0 1,
    ∀ p ∈ shortBoundary 6 3, max (0 : Fin 6).val (1 : Fin 6).val < (π.val p).val := by
  refine ⟨⟨Equiv.swap 1 5, by decide, by decide⟩, ?_⟩
  decide +kernel

/-- Exactly `M-1` labels at most the larger endpoint remain after deleting the
 two distinct prescribed labels; labels are zero-based. -/
theorem card_remaining_labels {n : ℕ} (m l : Fin n) (hml : m ≠ l) :
    (Finset.univ.filter (fun r : Fin n =>
      r.val ≤ max m.val l.val ∧ r ≠ m ∧ r ≠ l)).card = max m.val l.val - 1 := by
  classical
  have hmax : (max m l).val = max m.val l.val := by
    by_cases h : m ≤ l
    · rw [max_eq_right h, max_eq_right (show m.val ≤ l.val from h)]
    · have h' : l ≤ m := le_of_not_ge h
      rw [max_eq_left h', max_eq_left (show l.val ≤ m.val from h')]
  have hm : m ∈ Finset.Iic (max m l) := Finset.mem_Iic.mpr (le_max_left _ _)
  have hl : l ∈ (Finset.Iic (max m l)).erase m := by
    simp [hml.symm]
  have heq : Finset.univ.filter (fun r : Fin n =>
      r.val ≤ max m.val l.val ∧ r ≠ m ∧ r ≠ l) =
      ((Finset.Iic (max m l)).erase m).erase l := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Finset.mem_Iic, Fin.le_def]
    simp only [hmax]
    tauto
  rw [heq, Finset.card_erase_of_mem hl, Finset.card_erase_of_mem hm, Fin.card_Iic]
  rw [hmax]
  omega

example : (Finset.univ.filter (fun r : Fin 6 =>
    r.val ≤ max (0 : Fin 6).val (1 : Fin 6).val ∧ r ≠ 0 ∧ r ≠ 1)).card = 0 := by
  decide

/-- The actual fixed-endpoint permutations having some low label in a short
boundary position. -/
noncomputable def boundaryBadFinset {n : ℕ} [NeZero n] (K : ℕ) (q m l : Fin n) :
    Finset (FixedTwo (0 : Fin n) q m l) := by
  classical
  exact Finset.univ.filter (fun π =>
    ∃ p ∈ shortBoundary n K, (π.val p).val ≤ max m.val l.val)

/-- Boundary-bad membership is precisely the existence of a low boundary label. -/
theorem mem_boundaryBadFinset {n : ℕ} [NeZero n] (K : ℕ) (q m l : Fin n)
    (π : FixedTwo (0 : Fin n) q m l) :
    π ∈ boundaryBadFinset K q m l ↔
      ∃ p ∈ shortBoundary n K, (π.val p).val ≤ max m.val l.val := by
  classical
  simp [boundaryBadFinset]

/-- The boundary event satisfies the finite union bound over its actual positions. -/
theorem card_boundaryBadFinset_le {n : ℕ} [NeZero n] (K : ℕ) (q m l : Fin n) :
    (boundaryBadFinset K q m l).card ≤
      ∑ p ∈ shortBoundary n K,
        Fintype.card {π : FixedTwo (0 : Fin n) q m l //
          (π.val p).val ≤ max m.val l.val} := by
  classical
  let E : Fin n → Finset (FixedTwo (0 : Fin n) q m l) := fun p =>
    Finset.univ.filter (fun π => (π.val p).val ≤ max m.val l.val)
  have heq : boundaryBadFinset K q m l = (shortBoundary n K).biUnion E := by
    ext π
    simp [mem_boundaryBadFinset, E]
  rw [heq]
  calc
    _ ≤ ∑ p ∈ shortBoundary n K, (E p).card := Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      symm
      exact Fintype.card_subtype _

example : (boundaryBadFinset 3 (5 : Fin 6) 0 1).card ≤
    ∑ p ∈ shortBoundary 6 3,
      Fintype.card {π : FixedTwo (0 : Fin 6) 5 0 1 //
        (π.val p).val ≤ 1} := card_boundaryBadFinset_le 3 5 0 1

/-- Every fixed-fiber permutation with an actual overlap belongs to the union
of the boundary-bad event and the adopted actual long-overlap event. -/
theorem overlap_mem_boundary_union {n K : ℕ} [NeZero n]
    (hK : 3 ≤ K) (hn : 2 * K ≤ n) (q m l : Fin n) (hq : q.val + 1 = n)
    (π : FixedTwo (0 : Fin n) q m l)
    (hov : ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val) :
    π ∈ boundaryBadFinset K q m l ∪
      PermutationEndpointOverlapTail.longOverlapTwoFinset K q m l := by
  rcases overlap_boundary_or_long hK hn q m l hq π hov with hbad | hlong
  · exact Finset.mem_union.mpr (Or.inl ((mem_boundaryBadFinset K q m l π).mpr hbad))
  · exact Finset.mem_union.mpr (Or.inr
      ((PermutationEndpointOverlapTail.mem_longOverlapTwoFinset K q m l π).mpr hlong))

/-- Removing two distinct labels leaves exactly `n-2` labels. -/
theorem card_other_labels {n : ℕ} (m l : Fin n) (hml : m ≠ l) :
    Fintype.card {a : Fin n // a ≠ m ∧ a ≠ l} = n - 2 := by
  classical
  rw [Fintype.card_subtype]
  have heq : Finset.univ.filter (fun a : Fin n => a ≠ m ∧ a ≠ l) =
      ((Finset.univ : Finset (Fin n)).erase m).erase l := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [heq, Finset.card_erase_of_mem (by simp [hml.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
  omega

example : Fintype.card {a : Fin 6 // a ≠ 0 ∧ a ≠ 1} = 4 := by decide

set_option maxHeartbeats 800000 in
/-- The fraction with any actual overlap is bounded by the boundary-bad fraction
plus the adopted factorial long-tail estimate. -/
theorem overlap_fraction_le_boundary_add_tail {n K : ℕ} [NeZero n]
    (hK : 3 ≤ K) (hn : 2 * K ≤ n) (q m l : Fin n) (hq : q.val + 1 = n)
    (hml : m ≠ l) :
    (Fintype.card {π : FixedTwo (0 : Fin n) q m l //
      ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val} : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
      (boundaryBadFinset K q m l).card /
        (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) +
        6 / (K / 3).factorial := by
  classical
  have hpq : (0 : Fin n) ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) := fixedTwo_nonempty 0 q m l hpq hml
  have hpos : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast Fintype.card_pos
  let E : Finset (FixedTwo (0 : Fin n) q m l) := Finset.univ.filter
    (fun π => ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val)
  have hsub : E ⊆ boundaryBadFinset K q m l ∪
      PermutationEndpointOverlapTail.longOverlapTwoFinset K q m l := by
    intro π hπ
    exact overlap_mem_boundary_union hK hn q m l hq π (Finset.mem_filter.mp hπ).2
  have hcard : E.card ≤ (boundaryBadFinset K q m l).card +
      (PermutationEndpointOverlapTail.longOverlapTwoFinset K q m l).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hEc : Fintype.card {π : FixedTwo (0 : Fin n) q m l //
      ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val} = E.card :=
    Fintype.card_subtype _
  rw [hEc]
  calc
    _ ≤ ((boundaryBadFinset K q m l).card +
        (PermutationEndpointOverlapTail.longOverlapTwoFinset K q m l).card : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpos.le
    _ = _ + (PermutationEndpointOverlapTail.longOverlapTwoFinset K q m l).card /
        (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) := add_div _ _ _
    _ ≤ _ := add_le_add (le_refl _)
      (PermutationEndpointOverlapTail.longOverlapTwo_fraction_le (by omega) K hK q hq m l hml)

/-- An interior coordinate in the actual two-endpoint fiber has exact low-label
fraction `(M-1)/(n-2)`, by the adopted exchange-count marginal. -/
theorem low_label_fraction {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (q m l p : Fin n) (hq : q.val + 1 = n) (hml : m ≠ l)
    (hp0 : p ≠ 0) (hpq : p ≠ q) :
    (Fintype.card {π : FixedTwo (0 : Fin n) q m l //
      (π.val p).val ≤ max m.val l.val} : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) =
      ((max m.val l.val - 1 : ℕ) : ℝ) / (n - 2 : ℕ) := by
  classical
  have h0q : (0 : Fin n) ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) := fixedTwo_nonempty 0 q m l h0q hml
  have hF : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < (n - 2 : ℕ) := by exact_mod_cast (show 0 < n - 2 by omega)
  have hlabels : Fintype.card {a : Fin n //
      (a ≠ m ∧ a ≠ l) ∧ a.val ≤ max m.val l.val} = max m.val l.val - 1 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun a : Fin n =>
        (a ≠ m ∧ a ≠ l) ∧ a.val ≤ max m.val l.val) =
        Finset.univ.filter (fun a : Fin n =>
          a.val ≤ max m.val l.val ∧ a ≠ m ∧ a ≠ l) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [heq]
    exact card_remaining_labels m l hml
  have hc := PermutationMixedEndpointBound.marginal_card 0 q p m l hp0 hpq
    (fun a => a.val ≤ max m.val l.val)
  rw [card_other_labels m l hml] at hc
  have hc' : Fintype.card {π : FixedTwo (0 : Fin n) q m l //
      (π.val p).val ≤ max m.val l.val} * (n - 2) =
      Fintype.card (FixedTwo (0 : Fin n) q m l) * (max m.val l.val - 1) := by
    rw [← hlabels]
    convert hc using 1
    · congr 1
      exact @Fintype.card_congr
        {π : FixedTwo (0 : Fin n) q m l // (π.val p).val ≤ max m.val l.val}
        {π : FixedTwo (0 : Fin n) q m l // (π.val p).val ≤ max m.val l.val}
        inferInstance
        (@Subtype.fintype _ _ (fun _ => Classical.propDecidable _) inferInstance)
        (Equiv.refl _)
    · congr 1
      exact @Fintype.card_congr
        {a : Fin n // (a ≠ m ∧ a ≠ l) ∧ a.val ≤ max m.val l.val}
        {a : Fin n // (a ≠ m ∧ a ≠ l) ∧ a.val ≤ max m.val l.val}
        inferInstance
        (@Subtype.fintype _ _ (fun a =>
          @instDecidableAnd (a ≠ m ∧ a ≠ l) (a.val ≤ max m.val l.val)
            inferInstance (Classical.propDecidable _)) inferInstance)
        (Equiv.refl _)
  apply (div_eq_div_iff hF.ne' hD.ne').mpr
  have hcR : (Fintype.card {π : FixedTwo (0 : Fin n) q m l //
      (π.val p).val ≤ max m.val l.val} : ℝ) * (n - 2 : ℕ) =
      (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) * (max m.val l.val - 1 : ℕ) := by
    exact_mod_cast hc'
  simpa only [mul_comm] using hcR

/-- The union of low short-boundary coordinates has fraction at most
`(2*K-4)*(M-1)/(n-2)` in the nonempty actual endpoint fiber. -/
theorem boundaryBad_fraction_le {n K : ℕ} [NeZero n]
    (hK : 3 ≤ K) (hn : 2 * K ≤ n) (q m l : Fin n) (hq : q.val + 1 = n)
    (hml : m ≠ l) :
    ((boundaryBadFinset K q m l).card : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
      (2 * (K : ℝ) - 4) * (((max m.val l.val : ℕ) : ℝ) - 1) / ((n : ℝ) - 2) := by
  classical
  have h0q : (0 : Fin n) ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) := fixedTwo_nonempty 0 q m l h0q hml
  have hF : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast Fintype.card_pos
  have hM : 1 ≤ max m.val l.val := by
    by_contra h
    have he : m = l := Fin.ext (by omega)
    exact hml he
  have hcard : ((boundaryBadFinset K q m l).card : ℝ) ≤
      ∑ p ∈ shortBoundary n K, (Fintype.card {π : FixedTwo (0 : Fin n) q m l //
        (π.val p).val ≤ max m.val l.val} : ℝ) := by
    exact_mod_cast card_boundaryBadFinset_le K q m l
  calc
    _ ≤ (∑ p ∈ shortBoundary n K, (Fintype.card {π : FixedTwo (0 : Fin n) q m l //
        (π.val p).val ≤ max m.val l.val} : ℝ)) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) :=
      div_le_div_of_nonneg_right hcard hF.le
    _ = ∑ p ∈ shortBoundary n K, (Fintype.card {π : FixedTwo (0 : Fin n) q m l //
        (π.val p).val ≤ max m.val l.val} : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = ∑ _p ∈ shortBoundary n K, ((max m.val l.val - 1 : ℕ) : ℝ) / (n - 2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hp0, hpq⟩ := shortBoundary_interior hK hn q hq p hp
      exact low_label_fraction (by omega) q m l p hq hml
        (fun he => hp0 (congrArg Fin.val he)) hpq
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, card_shortBoundary hK hn]
      rw [Nat.cast_sub (by omega : 4 ≤ 2 * K), Nat.cast_sub hM,
        Nat.cast_sub (by omega : 2 ≤ n)]
      push_cast
      ring

/-- Actual all-length avoiders and permutations with some proper overlap
partition the actual two-endpoint fiber. -/
theorem card_avoidTwo_add_card_overlap {n : ℕ} [NeZero n] (q m l : Fin n) :
    Fintype.card (PermutationMixedEndpointBound.AvoidTwo q m l) +
      Fintype.card {π : FixedTwo (0 : Fin n) q m l //
        ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val} =
      Fintype.card (FixedTwo (0 : Fin n) q m l) := by
  classical
  let e : PermutationMixedEndpointBound.AvoidTwo q m l ≃
      {π : FixedTwo (0 : Fin n) q m l //
        ¬ ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val} :=
    { toFun := fun π => ⟨⟨π.val, π.property.1⟩, by
        rintro ⟨k, hk, hkn, hov⟩
        exact π.property.2 k hk hkn hov⟩
      invFun := fun π => ⟨π.val.val, π.val.property, by
        intro k hk hkn hov
        exact π.property ⟨k, hk, hkn, hov⟩⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl]
  exact Nat.sub_add_cancel (Fintype.card_subtype_le _)

/-- Finite same-edge avoidance estimate for the actual all-overlap avoiders:
for two distinct small endpoint labels, the failure fraction is at most the
short-boundary term plus `6/(K/3)!`. All labels are zero-based. -/
theorem actualAvoid_fraction_bound {n : ℕ} [NeZero n] (K : ℕ)
    (hK : 3 ≤ K) (hn : 2 * K ≤ n) (q : Fin n) (hq : q.val + 1 = n)
    (m l : Fin n) (hml : m ≠ l) :
    1 - (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q m l) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
      (2 * (K : ℝ) - 4) * (((max m.val l.val : ℕ) : ℝ) - 1) / ((n : ℝ) - 2) +
        6 / (K / 3).factorial := by
  have h0q : (0 : Fin n) ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) := fixedTwo_nonempty 0 q m l h0q hml
  have hF : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast Fintype.card_pos
  have hpartition :
      (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q m l) : ℝ) +
        Fintype.card {π : FixedTwo (0 : Fin n) q m l //
          ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val} =
        Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast card_avoidTwo_add_card_overlap q m l
  have hfraction :
      1 - (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q m l) : ℝ) /
          Fintype.card (FixedTwo (0 : Fin n) q m l) =
        (Fintype.card {π : FixedTwo (0 : Fin n) q m l //
          ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val} : ℝ) /
          Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    apply (eq_div_iff hF.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hF.ne', one_mul]
    linarith
  rw [hfraction]
  exact (overlap_fraction_le_boundary_add_tail hK hn q m l hq hml).trans
    (add_le_add (boundaryBad_fraction_le hK hn q m l hq hml) (le_refl _))

example :
    1 - (Fintype.card (PermutationMixedEndpointBound.AvoidTwo (5 : Fin 6) 0 1) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin 6) 5 0 1) ≤
      (2 * (3 : ℝ) - 4) * (((max (0 : Fin 6).val (1 : Fin 6).val : ℕ) : ℝ) - 1) /
        ((6 : ℝ) - 2) + 6 / (3 / 3 : ℕ).factorial :=
  actualAvoid_fraction_bound 3 (by decide) (by decide) 5 rfl 0 1 (by decide)

end PermutationSameEdgeAvoidance
