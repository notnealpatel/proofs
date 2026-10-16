import Combinatorics.PermutationAvoidanceCovariance
import Combinatorics.PermutationOverlapTail

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PermutationAvoidanceCovariance

open PermutationOrderCounting PermutationOverlapBound PermutationOverlapTail
attribute [local instance] Classical.propDecidable

/-- Averaging bounds in all fibers of a finite map gives the same unconditional bound. -/
theorem fraction_le_of_fibers {Ω B : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype B] [DecidableEq B] (f : Ω → B) (E : Finset Ω) (c : ℝ)
    (h : ∀ b, ((E.filter (fun x => f x = b)).card : ℝ) ≤
      c * ((Finset.univ.filter (fun x => f x = b)).card : ℝ)) :
    (E.card : ℝ) / Fintype.card Ω ≤ c := by
  classical
  have he := Finset.card_eq_sum_card_fiberwise
    (s := E) (t := Finset.univ) (f := f) (by intro x hx; simp)
  have hu := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := f) (by intro x hx; simp)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun b _ => h b)
  have hcard : (E.card : ℝ) ≤ c * Fintype.card Ω := by
    rw [he]
    push_cast
    calc
      _ ≤ ∑ b : B, c * ((Finset.univ.filter (fun x => f x = b)).card : ℝ) := hb
      _ = c * Fintype.card Ω := by
        rw [← Finset.mul_sum, ← Nat.cast_sum, ← hu, Finset.card_univ]
  exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card Ω)).mpr hcard

/-- The actual unconditional event of some overlap at length at least `K`. -/
def longOverlaps (n K : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun π => ∃ k, K ≤ k ∧ ∃ hkn : k < n, Overlap hkn π

example : longOverlaps 1 2 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro π
  simp only [longOverlaps, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨k, hk, hkn, _⟩
  omega

/-- The actual unconditional long-overlap fraction is bounded by averaging the existing fibers. -/
theorem longOverlaps_fraction_le {n : ℕ} [NeZero n] (K : ℕ) (hK : 4 ≤ K) :
    ((longOverlaps n K).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) ≤
      4 / (K / 2).factorial := by
  classical
  apply fraction_le_of_fibers (fun π : Equiv.Perm (Fin n) => π 0)
  intro m
  have he : ((longOverlaps n K).filter (fun π => π 0 = m)).card =
      (longOverlapFinset K m).card := by
    apply Finset.card_bij (fun π hπ => (⟨π, (Finset.mem_filter.mp hπ).2⟩ : FixedFirst 0 m))
    · intro π hπ
      simpa only [mem_longOverlapFinset, LongOverlap] using
        (Finset.mem_filter.mp (Finset.mem_filter.mp hπ).1).2
    · intro π hπ ρ hρ heq
      exact congrArg Subtype.val heq
    · intro π hπ
      refine ⟨π.val, ?_, Subtype.ext rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, longOverlaps]
      exact ⟨(mem_longOverlapFinset K m π).mp hπ, π.property⟩
  have hu : (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π 0 = m)).card =
      Fintype.card (FixedFirst (0 : Fin n) m) := by
    symm
    exact Fintype.card_of_subtype _ (by intro π; simp)
  have hf := longOverlap_fraction_le K hK m
  have hp : (0 : ℝ) < Fintype.card (FixedFirst (0 : Fin n) m) := by
    rw [card_fixedFirst]
    positivity
  have heR := congrArg (fun t : ℕ => (t : ℝ)) he
  have huR := congrArg (fun t : ℕ => (t : ℝ)) hu
  rw [heR, huR]
  exact (div_le_iff₀ hp).mp hf

/-- Disjoint actual prefix and suffix overlap has probability at most `1/k!`.
The fixed label is at the last position and the reordered block is the prefix. -/
theorem overlap_fraction_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (hdis : 2 * k ≤ n) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => Overlap hkn π)).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin n)) ≤ 1 / (k.factorial : ℝ) := by
  classical
  let a : Fin k ↪ Fin n := ⟨fun i => ⟨i.val, by omega⟩, by intro i j he; apply Fin.ext; exact congrArg (fun x : Fin n => x.val) he⟩
  let b : Fin k ↪ Fin n := ⟨fun i => ⟨i.val + (n-k), by omega⟩, by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    dsimp at hh
    omega⟩
  let p : Fin n := ⟨n-1, by omega⟩
  have hpa : p ∉ Set.range a := by
    rintro ⟨i, hi⟩
    have hh := congrArg Fin.val hi
    change i.val = n-1 at hh
    have hi' := i.isLt
    omega
  have hab : Disjoint (Set.range a) (Set.range b) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val + (n-k) = i.val at hh
    have hi := i.isLt
    omega
  apply fraction_le_of_fibers (fun π : Equiv.Perm (Fin n) => π p)
  intro m
  have he : ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => Overlap hkn π)).filter
      (fun π => π p = m)).card = Fintype.card (Agreement p m a b) := by
    symm
    apply Fintype.card_of_subtype
    intro π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change Overlap hkn π ∧ π p = m ↔ π p = m ∧ Overlap hkn π
    exact and_comm
  have hu : (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π p = m)).card =
      Fintype.card (FixedFirst p m) := by
    symm
    exact Fintype.card_of_subtype _ (by intro π; simp)
  have hf := agreement_fraction p m a b hpa hab
  have hp : (0 : ℝ) < Fintype.card (FixedFirst p m) := by rw [card_fixedFirst]; positivity
  have hb := (div_le_iff₀ hp).mp hf.le
  have heR := congrArg (fun t : ℕ => (t : ℝ)) he
  have huR := congrArg (fun t : ℕ => (t : ℝ)) hu
  rw [heR, huR]
  exact hb

/-- An actual overlap event, empty when its length is not proper. -/
def overlapAt (n k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  if hkn : k < n then Finset.univ.filter (Overlap hkn) else ∅

/-- Exact membership in the length-indexed overlap event. -/
theorem mem_overlapAt {n k : ℕ} (π : Equiv.Perm (Fin n)) :
    π ∈ overlapAt n k ↔ ∃ hkn : k < n, Overlap hkn π := by
  by_cases hkn : k < n <;> simp [overlapAt, hkn]

/-- The unconditional actual overlap tail from length four has the required numerical bound. -/
theorem all_tail_fraction_le {n : ℕ} (hn : 30 ≤ n) :
    ((longOverlaps n 4).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) ≤ 2609 / 50400 := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let S := (Finset.Ico 4 16).biUnion (overlapAt n)
  have hsub : longOverlaps n 4 ⊆ S ∪ longOverlaps n 16 := by
    intro π hπ
    obtain ⟨k, hk, hkn, hπk⟩ := (Finset.mem_filter.mp hπ).2
    by_cases h16 : k < 16
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Ico.mpr ⟨hk, h16⟩,
        (mem_overlapAt π).mpr ⟨hkn, hπk⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ π, k, by omega, hkn, hπk⟩
  have hcard : (longOverlaps n 4).card ≤
      (∑ k ∈ Finset.Ico 4 16, (overlapAt n k).card) + (longOverlaps n 16).card :=
    (Finset.card_le_card hsub).trans
      (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_right (Finset.card_biUnion_le) _))
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by exact_mod_cast Fintype.card_pos
  have hs : (∑ k ∈ Finset.Ico 4 16, ((overlapAt n k).card : ℝ)) /
      Fintype.card (Equiv.Perm (Fin n)) ≤ 31 / 600 := by
    rw [Finset.sum_div]
    calc
      _ ≤ ∑ k ∈ Finset.Ico 4 16, (1 : ℝ) / k.factorial := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_Ico.mp hk
        have hkn : k < n := by omega
        simpa only [overlapAt, dif_pos hkn] using
          overlap_fraction_le (by omega : 1 ≤ k) hkn (by omega : 2*k ≤ n)
      _ ≤ _ := by norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, Nat.factorial]
  have hl := longOverlaps_fraction_le (n := n) 16 (by omega)
  have hb : ((longOverlaps n 4).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) ≤
      (∑ k ∈ Finset.Ico 4 16, ((overlapAt n k).card : ℝ)) / Fintype.card (Equiv.Perm (Fin n)) +
      ((longOverlaps n 16).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hp.le
    exact_mod_cast hcard
  norm_num [Nat.factorial] at hl
  linarith

/-- Removing all remaining overlaps loses at most one quarter of their actual probability. -/
theorem centered_short_le_full_add_tail {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (∑ π ∈ shortAvoiding n, (coordinate i π - 1/2)*(coordinate j π - 1/2)) ≤
      (∑ π ∈ avoiding n, (coordinate i π - 1/2)*(coordinate j π - 1/2)) +
        (1/4 : ℝ) * (longOverlaps n 4).card := by
  classical
  let W : Equiv.Perm (Fin n) → ℝ := fun π => (coordinate i π - 1/2)*(coordinate j π - 1/2)
  have hsub : avoiding n ⊆ shortAvoiding n := by
    intro π hπ
    simp only [shortAvoiding, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk _ hkn
    exact (mem_avoiding π).mp hπ k hk hkn
  have hdiff : shortAvoiding n \ avoiding n ⊆ longOverlaps n 4 := by
    intro π hπ
    obtain ⟨hA, hH⟩ := Finset.mem_sdiff.mp hπ
    have hA' : ∀ k, 2 ≤ k → k ≤ 3 → ∀ hkn : k < n, ¬ Overlap hkn π := by
      simpa only [shortAvoiding, Finset.mem_filter, Finset.mem_univ, true_and] using hA
    have hH' : ¬ (∀ k, 2 ≤ k → ∀ hkn : k < n, ¬ Overlap hkn π) := by
      simpa only [mem_avoiding] using hH
    push Not at hH'
    obtain ⟨k, hk, hkn, hO⟩ := hH'
    have hk4 : 4 ≤ k := by
      by_contra he
      exact hA' k hk (by omega) hkn hO
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ π, k, hk4, hkn, hO⟩
  have hw (π : Equiv.Perm (Fin n)) : W π ≤ 1/4 := by
    obtain ⟨hi0, hi1⟩ := coordinate_bounds hn i π
    obtain ⟨hj0, hj1⟩ := coordinate_bounds hn j π
    dsimp only [W]
    nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hj1), mul_nonneg (sub_nonneg.mpr hi1) hj0]
  have hs : (∑ π ∈ shortAvoiding n \ avoiding n, W π) ≤
      (1/4 : ℝ) * (longOverlaps n 4).card := by
    calc
      _ ≤ ∑ π ∈ shortAvoiding n \ avoiding n, (1/4 : ℝ) := Finset.sum_le_sum (fun π _ => hw π)
      _ = (1/4 : ℝ) * (shortAvoiding n \ avoiding n).card := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hdiff) (by norm_num)
  have he := Finset.sum_sdiff hsub (f := W)
  change (∑ π ∈ shortAvoiding n, W π) ≤ (∑ π ∈ avoiding n, W π) + _
  linarith

/-- Staged final consumer: the actual short-event centered lower bound implies
nonemptiness and the required bound on actual covariance. Its short-moment input
is explicit and must be discharged before this is a full-target theorem. -/
theorem covariance_lower_of_short_lower {n : ℕ} (hn : 30 ≤ n) (i j : Fin n)
    (hshort : (1/72 : ℝ) ≤
      (∑ π ∈ shortAvoiding n, (coordinate i π - 1/2)*(coordinate j π - 1/2)) /
        Fintype.card (Equiv.Perm (Fin n))) :
    (avoiding n).Nonempty ∧ (191/201600 : ℝ) ≤ covariance i j := by
  have hn2 : 2 ≤ n := by omega
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by exact_mod_cast Fintype.card_pos
  have hsum := centered_short_le_full_add_tail hn2 i j
  have hdiv := div_le_div_of_nonneg_right hsum hp.le
  rw [add_div, mul_div_assoc] at hdiv
  have htail := all_tail_fraction_le hn
  have hfull : (191/201600 : ℝ) ≤
      (∑ π ∈ avoiding n, (coordinate i π - 1/2)*(coordinate j π - 1/2)) /
        Fintype.card (Equiv.Perm (Fin n)) := by linarith
  exact covariance_lower_of_centered_lower hn2 i j _ (by norm_num) hfull

/-- The target covariance constant strictly improves `1/1152`. -/
theorem target_constant_strict : (1/1152 : ℝ) < 191/201600 := by norm_num

end PermutationAvoidanceCovariance
