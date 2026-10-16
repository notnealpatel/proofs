import Combinatorics.PermutationOverlapBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators
open Filter Topology

namespace PermutationOverlapTail

/-- A parity-adjusted telescoping majorant for the reciprocal-factorial weights. -/
private noncomputable def potential (k : ℕ) : ℝ :=
  (if k % 2 = 0 then 4 else 3) / (k / 2).factorial

example : potential 4 = 2 := by norm_num [potential]
example : potential 5 = 3 / 2 := by norm_num [potential]

private theorem weight_le_potential_sub (k : ℕ) (hk : 4 ≤ k) :
    (1 : ℝ) / (k / 2).factorial ≤ potential k - potential (k + 1) := by
  have hf : (0 : ℝ) < (k / 2).factorial := by positivity
  by_cases he : k % 2 = 0
  · have hn : (k + 1) % 2 ≠ 0 := by omega
    have hd : (k + 1) / 2 = k / 2 := by omega
    simp only [potential, if_pos he, if_neg hn, hd]
    field_simp
    linarith
  · have hn : (k + 1) % 2 = 0 := by omega
    have hd : (k + 1) / 2 = k / 2 + 1 := by omega
    have hq : (2 : ℝ) ≤ ((k / 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k / 2 by omega)
    simp only [potential, if_neg he, if_pos hn, hd, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    apply (le_sub_iff_add_le).2
    have hqpos : (0 : ℝ) < ((k / 2 : ℕ) : ℝ) + 1 := by positivity
    field_simp
    nlinarith

/-- The finite reciprocal-factorial overlap tail is bounded by four times its first factorial scale, including odd starts and empty intervals. -/
theorem sum_Ico_le (K N : ℕ) (hK : 4 ≤ K) :
    ∑ k ∈ Finset.Ico K N, (1 : ℝ) / (k / 2).factorial ≤
      4 / (K / 2).factorial := by
  by_cases hKN : K ≤ N
  · have hs := Finset.sum_le_sum (s := Finset.Ico K N)
      (fun k hk => weight_le_potential_sub k (le_trans hK (Finset.mem_Ico.mp hk).1))
    have ht : ∑ k ∈ Finset.Ico K N, (potential k - potential (k + 1)) =
        potential K - potential N := by
      simpa only [← Finset.sum_neg_distrib, neg_sub] using
        congrArg Neg.neg (Finset.sum_Ico_sub potential hKN)
    rw [ht] at hs
    have hp : 0 ≤ potential N := by unfold potential; positivity
    have hb : potential K ≤ 4 / (K / 2).factorial := by
      unfold potential
      split_ifs <;> apply div_le_div_of_nonneg_right <;> norm_num
    linarith
  · have hempty : Finset.Ico K N = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-- The uniform factorial-tail bound tends to zero as the starting index tends to infinity. -/
theorem tendsto_bound :
    Tendsto (fun K : ℕ => (4 : ℝ) / (K / 2).factorial) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_natCast_atTop_atTop.comp
    (factorial_tendsto_atTop.comp (Nat.tendsto_div_const_atTop (by decide : 2 ≠ 0)))

/-- A union of finitely many events obeys the factorial-tail bound whenever each event has the corresponding normalized cardinal bound. No independence is assumed. -/
theorem normalized_biUnion_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : ℕ → Finset Ω) (K N : ℕ) (hK : 4 ≤ K)
    (hE : ∀ k ∈ Finset.Ico K N,
      (E k).card / (Fintype.card Ω : ℝ) ≤ (1 : ℝ) / (k / 2).factorial) :
    (@Finset.biUnion ℕ Ω (Classical.decEq Ω) (Finset.Ico K N) E).card /
      (Fintype.card Ω : ℝ) ≤
      4 / (K / 2).factorial := by
  classical
  have hcard : (((Finset.Ico K N).biUnion E).card : ℝ) ≤
      ∑ k ∈ Finset.Ico K N, ((E k).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := Finset.Ico K N) (t := E))
  have hpos : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (∑ k ∈ Finset.Ico K N, ((E k).card : ℝ)) / (Fintype.card Ω : ℝ) :=
      div_le_div_of_nonneg_right hcard hpos.le
    _ = ∑ k ∈ Finset.Ico K N, (E k).card / (Fintype.card Ω : ℝ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.Ico K N, (1 : ℝ) / (k / 2).factorial :=
      Finset.sum_le_sum hE
    _ ≤ _ := sum_Ico_le K N hK

/-- An integral cardinal-times-factorial estimate for each event implies the normalized finite-union tail bound. -/
theorem normalized_biUnion_le_of_card_mul {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : ℕ → Finset Ω) (K N : ℕ) (hK : 4 ≤ K)
    (hE : ∀ k ∈ Finset.Ico K N,
      (E k).card * (k / 2).factorial ≤ Fintype.card Ω) :
    (@Finset.biUnion ℕ Ω (Classical.decEq Ω) (Finset.Ico K N) E).card /
      (Fintype.card Ω : ℝ) ≤
      4 / (K / 2).factorial := by
  apply normalized_biUnion_le E K N hK
  intro k hk
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hf : (0 : ℝ) < (k / 2).factorial := by positivity
  apply (div_le_div_iff₀ hpos hf).2
  simpa only [one_mul, Nat.cast_mul] using
    (show (((E k).card * (k / 2).factorial : ℕ) : ℝ) ≤ Fintype.card Ω by
      exact_mod_cast hE k hk)

example : ∀ k ∈ Finset.Ico 5 9,
    ((∅ : Finset Unit).card : ℝ) / Fintype.card Unit ≤
      (1 : ℝ) / (k / 2).factorial := by
  intros
  simp only [Finset.card_empty, Nat.cast_zero, zero_div]
  positivity

example : ∀ k ∈ Finset.Ico 4 8,
    (∅ : Finset Unit).card * (k / 2).factorial ≤ Fintype.card Unit := by
  intros
  simp

attribute [local instance] Classical.propDecidable

/-- A fixed-first permutation has a long overlap when an actual prefix/suffix comparison overlap occurs at some length in `[K,n)`. -/
def LongOverlap {n : ℕ} [NeZero n] (K : ℕ) (m : Fin n)
    (π : PermutationOrderCounting.FixedFirst (0 : Fin n) m) : Prop :=
  ∃ k, K ≤ k ∧ ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val

example {n : ℕ} [NeZero n] (K : ℕ) (m : Fin n)
    (π : PermutationOrderCounting.FixedFirst (0 : Fin n) m) :
    LongOverlap K m π ↔
      ∃ k, K ≤ k ∧ ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val := Iff.rfl

/-- The finite set of all fixed-first permutations with an overlap of length at least `K` and strictly less than `n`. -/
noncomputable def longOverlapFinset {n : ℕ} [NeZero n] (K : ℕ) (m : Fin n) :
    Finset (PermutationOrderCounting.FixedFirst (0 : Fin n) m) :=
  Finset.univ.filter (LongOverlap K m)

/-- Membership in the long-overlap finset is precisely the actual long-overlap predicate. -/
theorem mem_longOverlapFinset {n : ℕ} [NeZero n] (K : ℕ) (m : Fin n)
    (π : PermutationOrderCounting.FixedFirst (0 : Fin n) m) :
    π ∈ longOverlapFinset K m ↔ LongOverlap K m π := by
  simp [longOverlapFinset]

/-- The actual length-`k` overlap event inside a fixed-first fiber, empty for inadmissible lengths. -/
private noncomputable def overlapFinset {n : ℕ} [NeZero n] (m : Fin n) (k : ℕ) :
    Finset (PermutationOrderCounting.FixedFirst (0 : Fin n) m) :=
  if hkn : k < n then Finset.univ.filter (fun π => PermutationOverlapBound.Overlap hkn π.val)
  else ∅

private theorem mem_overlapFinset {n : ℕ} [NeZero n] (m : Fin n) (k : ℕ)
    (π : PermutationOrderCounting.FixedFirst (0 : Fin n) m) :
    π ∈ overlapFinset m k ↔ ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val := by
  by_cases hkn : k < n <;> simp [overlapFinset, hkn]

private theorem card_overlapFinset {n : ℕ} [NeZero n] (m : Fin n) (k : ℕ) (hkn : k < n) :
    (overlapFinset m k).card = Fintype.card (PermutationOverlapBound.Event hkn m) := by
  classical
  let e : (↥(overlapFinset m k)) ≃ PermutationOverlapBound.Event hkn m :=
    { toFun := fun π => ⟨π.val.val, π.val.property,
        (mem_overlapFinset m k π.val).mp π.property |>.choose_spec⟩
      invFun := fun π => ⟨⟨π.val, π.property.1⟩,
        (mem_overlapFinset m k _).mpr ⟨hkn, π.property.2⟩⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)

/-- In every prescribed-first-label fiber, the fraction of permutations having any actual overlap of length in `[K,n)` is at most `4/(K/2)!`, without an independence assumption. -/
theorem longOverlap_fraction_le {n : ℕ} [NeZero n] (K : ℕ) (hK : 4 ≤ K) (m : Fin n) :
    ((longOverlapFinset K m).card : ℝ) /
      Fintype.card (PermutationOrderCounting.FixedFirst (0 : Fin n) m) ≤
      4 / (K / 2).factorial := by
  classical
  letI : Nonempty (PermutationOrderCounting.FixedFirst (0 : Fin n) m) :=
    PermutationOrderCounting.fixedFirst_nonempty 0 m
  have hunion : longOverlapFinset K m =
      @Finset.biUnion ℕ (PermutationOrderCounting.FixedFirst (0 : Fin n) m)
        (Classical.decEq _) (Finset.Ico K n) (overlapFinset m) := by
    ext π
    simp only [mem_longOverlapFinset, LongOverlap, Finset.mem_biUnion,
      Finset.mem_Ico, mem_overlapFinset]
    constructor
    · rintro ⟨k, hk, hkn, hπ⟩
      exact ⟨k, ⟨hk, hkn⟩, hkn, hπ⟩
    · rintro ⟨k, ⟨hk, hkn⟩, _, hπ⟩
      exact ⟨k, hk, hkn, hπ⟩
  rw [hunion]
  apply normalized_biUnion_le (overlapFinset m) K n hK
  intro k hk
  have hkn : k < n := (Finset.mem_Ico.mp hk).2
  rw [card_overlapFinset m k hkn]
  exact PermutationOverlapBound.event_fraction_le k (by have := (Finset.mem_Ico.mp hk).1; omega) hkn m

example : Nonempty (PermutationOrderCounting.FixedFirst (0 : Fin 5) 0) ∧
    4 ≤ (4 : ℕ) := ⟨PermutationOrderCounting.fixedFirst_nonempty 0 0, by decide⟩

end PermutationOverlapTail
