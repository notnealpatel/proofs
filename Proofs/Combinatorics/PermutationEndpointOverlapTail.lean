import Combinatorics.PermutationEndpointOverlapBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators
open Filter Topology

namespace PermutationEndpointOverlapTail

open PermutationEndpointCounting

/-- The residue-adjusted telescoping potential for the two-endpoint tail. -/
private noncomputable def potential (k : ℕ) : ℝ :=
  (if k % 3 = 0 then 6 else if k % 3 = 1 then 5 else 4) / (k / 3).factorial

example : potential 3 = 6 := by norm_num [potential]
example : potential 4 = 5 := by norm_num [potential]
example : potential 5 = 4 := by norm_num [potential]
example : potential 6 = 3 := by norm_num [potential]

private theorem weight_le_potential_sub (k : ℕ) (hk : 3 ≤ k) :
    (1 : ℝ) / (k / 3).factorial ≤ potential k - potential (k + 1) := by
  have hf : (0 : ℝ) < (k / 3).factorial := by positivity
  by_cases h0 : k % 3 = 0
  · have hn0 : (k + 1) % 3 ≠ 0 := by omega
    have hn1 : (k + 1) % 3 = 1 := by omega
    have hd : (k + 1) / 3 = k / 3 := by omega
    simp only [potential, if_pos h0, if_neg hn0, if_pos hn1, hd]
    field_simp
    linarith
  · by_cases h1 : k % 3 = 1
    · have hn0 : (k + 1) % 3 ≠ 0 := by omega
      have hn1 : (k + 1) % 3 ≠ 1 := by omega
      have hd : (k + 1) / 3 = k / 3 := by omega
      simp only [potential, if_neg h0, if_pos h1, if_neg hn0, if_neg hn1, hd]
      field_simp
      linarith
    · have hn0 : (k + 1) % 3 = 0 := by omega
      have hd : (k + 1) / 3 = k / 3 + 1 := by omega
      have hq : (1 : ℝ) ≤ ((k / 3 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ k / 3 by omega)
      simp only [potential, if_neg h0, if_neg h1, if_pos hn0, hd,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      apply (le_sub_iff_add_le).2
      have hqpos : (0 : ℝ) < ((k / 3 : ℕ) : ℝ) + 1 := by positivity
      field_simp
      nlinarith

/-- Every finite reciprocal-factorial tail starting at `K ≥ 3` is at most
`6/(K/3)!`, including all three residues and empty intervals. -/
theorem sum_Ico_le (K N : ℕ) (hK : 3 ≤ K) :
    ∑ k ∈ Finset.Ico K N, (1 : ℝ) / (k / 3).factorial ≤
      6 / (K / 3).factorial := by
  by_cases hKN : K ≤ N
  · have hs := Finset.sum_le_sum (s := Finset.Ico K N)
      (fun k hk => weight_le_potential_sub k (le_trans hK (Finset.mem_Ico.mp hk).1))
    have ht : ∑ k ∈ Finset.Ico K N, (potential k - potential (k + 1)) =
        potential K - potential N := by
      simpa only [← Finset.sum_neg_distrib, neg_sub] using
        congrArg Neg.neg (Finset.sum_Ico_sub potential hKN)
    rw [ht] at hs
    have hp : 0 ≤ potential N := by unfold potential; positivity
    have hb : potential K ≤ 6 / (K / 3).factorial := by
      unfold potential
      split_ifs <;> apply div_le_div_of_nonneg_right <;> norm_num
    linarith
  · have hempty : Finset.Ico K N = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-- The uniform two-endpoint tail majorant tends to zero. -/
theorem tendsto_bound :
    Tendsto (fun K : ℕ => (6 : ℝ) / (K / 3).factorial) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_natCast_atTop_atTop.comp
    (factorial_tendsto_atTop.comp (Nat.tendsto_div_const_atTop (by decide : 3 ≠ 0)))

attribute [local instance] Classical.propDecidable

/-- A permutation in the actual two-label fiber has a long overlap if some
length in `[K,n)` has the shared prefix/suffix order overlap. -/
def LongOverlapTwo {n : ℕ} [NeZero n] (K : ℕ) (q m l : Fin n)
    (π : FixedTwo (0 : Fin n) q m l) : Prop :=
  ∃ k, K ≤ k ∧ ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val

example {n : ℕ} [NeZero n] (K : ℕ) (q m l : Fin n)
    (π : FixedTwo (0 : Fin n) q m l) :
    LongOverlapTwo K q m l π ↔
      ∃ k, K ≤ k ∧ ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val := Iff.rfl

/-- All permutations in the prescribed two-label fiber with a long overlap. -/
noncomputable def longOverlapTwoFinset {n : ℕ} [NeZero n] (K : ℕ) (q m l : Fin n) :
    Finset (FixedTwo (0 : Fin n) q m l) :=
  Finset.univ.filter (LongOverlapTwo K q m l)

/-- Membership is exactly the actual existential long-overlap predicate. -/
theorem mem_longOverlapTwoFinset {n : ℕ} [NeZero n] (K : ℕ) (q m l : Fin n)
    (π : FixedTwo (0 : Fin n) q m l) :
    π ∈ longOverlapTwoFinset K q m l ↔ LongOverlapTwo K q m l π := by
  simp [longOverlapTwoFinset]

/-- The actual single-length overlap event in the two-label fiber. -/
private noncomputable def overlapFinset {n : ℕ} [NeZero n] (q m l : Fin n) (k : ℕ) :
    Finset (FixedTwo (0 : Fin n) q m l) :=
  if hkn : k < n then Finset.univ.filter (fun π => PermutationOverlapBound.Overlap hkn π.val)
  else ∅

private theorem mem_overlapFinset {n : ℕ} [NeZero n] (q m l : Fin n) (k : ℕ)
    (π : FixedTwo (0 : Fin n) q m l) :
    π ∈ overlapFinset q m l k ↔
      ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val := by
  by_cases hkn : k < n <;> simp [overlapFinset, hkn]

private theorem card_overlapFinset {n : ℕ} [NeZero n] (q m l : Fin n) (k : ℕ)
    (hkn : k < n) :
    (overlapFinset q m l k).card =
      Fintype.card (PermutationEndpointOverlapBound.EventTwo hkn q m l) := by
  classical
  let e : (↥(overlapFinset q m l k)) ≃ PermutationEndpointOverlapBound.EventTwo hkn q m l :=
    { toFun := fun π => ⟨π.val.val, π.val.property,
        (mem_overlapFinset q m l k π.val).mp π.property |>.choose_spec⟩
      invFun := fun π => ⟨⟨π.val, π.property.1⟩,
        (mem_overlapFinset q m l k _).mpr ⟨hkn, π.property.2⟩⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)

/-- Uniformly over every pair of distinct prescribed endpoint labels, the fraction
of actual permutations with any overlap in `[K,n)` is at most `6/(K/3)!`.
Only finite-union subadditivity is used, not independence. -/
theorem longOverlapTwo_fraction_le {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (K : ℕ) (hK : 3 ≤ K) (q : Fin n) (hq : q.val + 1 = n)
    (m l : Fin n) (hml : m ≠ l) :
    ((longOverlapTwoFinset K q m l).card : ℝ) /
      Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
      6 / (K / 3).factorial := by
  classical
  have hpq : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) := fixedTwo_nonempty 0 q m l hpq hml
  have hpos : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast Fintype.card_pos
  have hunion : longOverlapTwoFinset K q m l =
      @Finset.biUnion ℕ (FixedTwo (0 : Fin n) q m l)
        (Classical.decEq _) (Finset.Ico K n) (overlapFinset q m l) := by
    ext π
    simp only [mem_longOverlapTwoFinset, LongOverlapTwo, Finset.mem_biUnion,
      Finset.mem_Ico, mem_overlapFinset]
    constructor
    · rintro ⟨k, hk, hkn, hπ⟩
      exact ⟨k, ⟨hk, hkn⟩, hkn, hπ⟩
    · rintro ⟨k, ⟨hk, hkn⟩, _, hπ⟩
      exact ⟨k, hk, hkn, hπ⟩
  rw [hunion]
  have hcard : ((@Finset.biUnion ℕ (FixedTwo (0 : Fin n) q m l)
      (Classical.decEq _) (Finset.Ico K n) (overlapFinset q m l)).card : ℝ) ≤
      ∑ k ∈ Finset.Ico K n, ((overlapFinset q m l k).card : ℝ) := by
    exact_mod_cast (@Finset.card_biUnion_le ℕ (FixedTwo (0 : Fin n) q m l)
      (Classical.decEq _) (Finset.Ico K n) (overlapFinset q m l))
  calc
    _ ≤ (∑ k ∈ Finset.Ico K n, ((overlapFinset q m l k).card : ℝ)) /
        (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) :=
      div_le_div_of_nonneg_right hcard hpos.le
    _ = ∑ k ∈ Finset.Ico K n, (overlapFinset q m l k).card /
        (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.Ico K n, (1 : ℝ) / (k / 3).factorial := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := (Finset.mem_Ico.mp hk).2
      rw [card_overlapFinset q m l k hkn]
      exact PermutationEndpointOverlapBound.eventTwo_fraction_le k
        (le_trans hK (Finset.mem_Ico.mp hk).1) hkn q hq m l hml
    _ ≤ _ := sum_Ico_le K n hK

/-- No admissible overlap length exists once the cutoff reaches the size. -/
theorem longOverlapTwoFinset_eq_empty {n : ℕ} [NeZero n] (K : ℕ) (hK : n ≤ K)
    (q m l : Fin n) : longOverlapTwoFinset K q m l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro π hπ
  obtain ⟨k, hk, hkn, _⟩ := (mem_longOverlapTwoFinset K q m l π).mp hπ
  omega

example : 3 ≤ (7 : ℕ) ∧ 3 ≤ (6 : ℕ) ∧ (6 : Fin 7).val + 1 = 7 ∧
    (0 : Fin 7) ≠ 6 ∧
    ∃ π : FixedTwo (0 : Fin 7) 6 0 6, LongOverlapTwo 6 6 0 6 π := by
  refine ⟨by decide, by decide, rfl, by decide, ⟨⟨Equiv.refl _, rfl, rfl⟩, ?_⟩⟩
  refine ⟨6, le_refl _, by decide, ?_⟩
  intro i j
  change i.val < j.val ↔ i.val + (7 - 6) < j.val + (7 - 6)
  omega

example : longOverlapTwoFinset 7 (6 : Fin 7) 0 6 = ∅ :=
  longOverlapTwoFinset_eq_empty 7 (le_refl _) 6 0 6

end PermutationEndpointOverlapTail
