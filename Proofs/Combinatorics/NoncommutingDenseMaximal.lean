import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false

namespace NoncommutingDense

noncomputable section

/-- The integer interval specified by an ordered pair of endpoints. -/
def endpointInterval (p : ℤ × ℤ) : Finset ℤ := Finset.Icc p.1 p.2

/-- The interval obtained by adding one original diameter at each end. -/
def tripleInterval (p : ℤ × ℤ) : Finset ℤ :=
  Finset.Icc (2 * p.1 - p.2) (2 * p.2 - p.1)

example : endpointInterval (2,4) = {2,3,4} := by decide
example : endpointInterval (1,0) = ∅ := by decide
example : tripleInterval (2,4) = {0,1,2,3,4,5,6} := by decide
example : tripleInterval (3,3) = {3} := by decide

/-- An intersecting interval no longer than `I` lies in its triple enlargement. -/
theorem endpointInterval_subset_tripleInterval (p q : ℤ × ℤ)
    (hp : p.1 ≤ p.2) (hq : q.1 ≤ q.2)
    (hsize : (endpointInterval p).card ≤ (endpointInterval q).card)
    (hinter : ¬Disjoint (endpointInterval p) (endpointInterval q)) :
    endpointInterval p ⊆ tripleInterval q := by
  obtain ⟨z, hzp, hzq⟩ := Finset.not_disjoint_iff.mp hinter
  simp only [endpointInterval, Finset.mem_Icc] at hzp hzq
  simp only [endpointInterval, Int.card_Icc] at hsize
  intro x hx
  simp only [endpointInterval, tripleInterval, Finset.mem_Icc] at hx ⊢
  omega

example : (0 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 2 ∧
    (endpointInterval (0,1)).card ≤ (endpointInterval (1,2)).card ∧
    ¬Disjoint (endpointInterval (0,1)) (endpointInterval (1,2)) := by decide

/-- Triple enlargement has at most three times the original interval cardinality. -/
theorem card_tripleInterval_le (p : ℤ × ℤ) (hp : p.1 ≤ p.2) :
    (tripleInterval p).card ≤ 3 * (endpointInterval p).card := by
  simp only [tripleInterval, endpointInterval, Int.card_Icc]
  omega

/-- A finite family of nonempty integer intervals admits a disjoint subfamily
whose triple enlargements cover every interval in the original family. Selection
is by maximal cardinality, recursively discarding all intersecting intervals. -/
theorem exists_disjoint_interval_cover (S : Finset (ℤ × ℤ))
    (hS : ∀ p ∈ S, p.1 ≤ p.2) :
    ∃ T ⊆ S, (↑T : Set (ℤ × ℤ)).PairwiseDisjoint endpointInterval ∧
      ∀ p ∈ S, ∃ q ∈ T, endpointInterval p ⊆ tripleInterval q := by
  classical
  revert hS
  refine Finset.strongInductionOn S ?_
  intro S ih hS
  by_cases hne : S.Nonempty
  · obtain ⟨q, hq, hmax⟩ := S.exists_max_image (fun p => (endpointInterval p).card) hne
    let R := S.filter (fun p => Disjoint (endpointInterval p) (endpointInterval q))
    have hRS : R ⊆ S := Finset.filter_subset _ _
    have hqR : q ∉ R := by
      intro hqr
      have hd := (Finset.mem_filter.mp hqr).2
      have hpoint : q.1 ∈ endpointInterval q := by
        simp only [endpointInterval, Finset.mem_Icc]
        exact ⟨le_refl _, hS q hq⟩
      exact Finset.disjoint_left.mp hd hpoint hpoint
    have hstrict : R ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hRS, by
      intro heq
      exact hqR (heq.symm ▸ hq)⟩
    obtain ⟨T, hTR, hdisj, hcover⟩ := ih R hstrict (fun p hp => hS p (hRS hp))
    refine ⟨insert q T, ?_, ?_, ?_⟩
    · exact Finset.insert_subset_iff.mpr ⟨hq, hTR.trans hRS⟩
    · rw [Finset.coe_insert]
      exact hdisj.insert (fun p hp _ => ((Finset.mem_filter.mp (hTR hp)).2).symm)
    · intro p hp
      by_cases hd : Disjoint (endpointInterval p) (endpointInterval q)
      · obtain ⟨r, hr, hpr⟩ := hcover p (Finset.mem_filter.mpr ⟨hp, hd⟩)
        exact ⟨r, Finset.mem_insert_of_mem hr, hpr⟩
      · exact ⟨q, Finset.mem_insert_self _ _,
          endpointInterval_subset_tripleInterval p q (hS p hp) (hS q hq) (hmax p hp) hd⟩
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩

example : ∀ p ∈ ({(0,0),(0,1),(2,2)} : Finset (ℤ × ℤ)), p.1 ≤ p.2 := by
  decide

/-- The finite uncentered maximal level set: a point belongs when some nonempty
integer subinterval with endpoints in `X` has average at least `τ`. The density
condition is written without division. -/
def intervalMaximalHalo (X : Finset ℤ) (f : ℤ → ℝ) (τ : ℝ) : Finset ℤ := by
  classical
  exact X.filter (fun x => ∃ a ∈ X, ∃ b ∈ X, a ≤ b ∧ x ∈ Finset.Icc a b ∧
    τ * (Finset.Icc a b).card ≤ ∑ y ∈ Finset.Icc a b, f y)

example : intervalMaximalHalo {0} (fun _ => 1) 1 = {0} := by
  ext x
  by_cases hx : x = 0
  · subst x
    simp [intervalMaximalHalo]
  · simp [intervalMaximalHalo, hx]

example : intervalMaximalHalo {0} (fun _ => 0) 1 = ∅ := by
  ext x
  simp [intervalMaximalHalo]

example (f : ℤ → ℝ) (τ : ℝ) : intervalMaximalHalo ∅ f τ = ∅ := by
  simp [intervalMaximalHalo]

/-- On a nonempty finite integer interval, the uncentered maximal level set of
a nonnegative real-valued function obeys the constant-three weak estimate.
The positivity of `τ` guards the intended average threshold. -/
theorem intervalMaximalHalo_weak_bound (a0 b0 : ℤ) (_hab : a0 ≤ b0)
    (f : ℤ → ℝ) (hf : ∀ x ∈ Finset.Icc a0 b0, 0 ≤ f x)
    (τ : ℝ) (hτ : 0 < τ) :
    τ * (intervalMaximalHalo (Finset.Icc a0 b0) f τ).card ≤
      3 * ∑ x ∈ Finset.Icc a0 b0, f x := by
  classical
  let X := Finset.Icc a0 b0
  let S := (X ×ˢ X).filter (fun p => p.1 ≤ p.2 ∧
    τ * (endpointInterval p).card ≤ ∑ y ∈ endpointInterval p, f y)
  have hvalid : ∀ p ∈ S, p.1 ≤ p.2 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hcontained : ∀ p ∈ S, endpointInterval p ⊆ X := by
    intro p hp x hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    simp only [X, Finset.mem_Icc] at ha hb ⊢
    simp only [endpointInterval, Finset.mem_Icc] at hx
    omega
  obtain ⟨T, hTS, hdisj, hcover⟩ := exists_disjoint_interval_cover S hvalid
  have hhalo : intervalMaximalHalo X f τ ⊆ T.biUnion tripleInterval := by
    intro x hx
    obtain ⟨_, a, ha, b, hb, hab, hxI, hmean⟩ := Finset.mem_filter.mp hx
    have habS : (a,b) ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hab, hmean⟩
    obtain ⟨q, hq, hsub⟩ := hcover (a,b) habS
    exact Finset.mem_biUnion.mpr ⟨q, hq, hsub hxI⟩
  have hcountNat : (intervalMaximalHalo X f τ).card ≤
      3 * ∑ p ∈ T, (endpointInterval p).card := by
    calc
      _ ≤ (T.biUnion tripleInterval).card := Finset.card_le_card hhalo
      _ ≤ ∑ p ∈ T, (tripleInterval p).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ T, 3 * (endpointInterval p).card :=
        Finset.sum_le_sum (fun p hp => card_tripleInterval_le p (hvalid p (hTS hp)))
      _ = _ := (Finset.mul_sum T (fun p => (endpointInterval p).card) 3).symm
  have hcount : ((intervalMaximalHalo X f τ).card : ℝ) ≤
      3 * ∑ p ∈ T, ((endpointInterval p).card : ℝ) := by
    exact_mod_cast hcountNat
  have hunion : T.biUnion endpointInterval ⊆ X := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
    exact hcontained p (hTS hp) hxp
  have hmass : τ * (∑ p ∈ T, ((endpointInterval p).card : ℝ)) ≤ ∑ x ∈ X, f x := by
    calc
      _ = ∑ p ∈ T, τ * (endpointInterval p).card := Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ T, ∑ y ∈ endpointInterval p, f y :=
        Finset.sum_le_sum (fun p hp => (Finset.mem_filter.mp (hTS hp)).2.2)
      _ = ∑ y ∈ T.biUnion endpointInterval, f y := (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑ x ∈ X, f x :=
        Finset.sum_le_sum_of_subset_of_nonneg hunion (fun x hx _ => hf x hx)
  calc
    _ ≤ τ * (3 * ∑ p ∈ T, ((endpointInterval p).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount hτ.le
    _ = 3 * (τ * ∑ p ∈ T, ((endpointInterval p).card : ℝ)) := by ring
    _ ≤ 3 * ∑ x ∈ X, f x := mul_le_mul_of_nonneg_left hmass (by norm_num)

example : (0 : ℤ) ≤ 0 ∧ (∀ x ∈ Finset.Icc (0 : ℤ) 0, (0 : ℝ) ≤ 1) ∧
    (0 : ℝ) < 1 := by norm_num

example : (1 : ℝ) * (intervalMaximalHalo (Finset.Icc (0 : ℤ) 0) (fun _ => 1) 1).card ≤
    3 * ∑ _x ∈ Finset.Icc (0 : ℤ) 0, (1 : ℝ) :=
  intervalMaximalHalo_weak_bound 0 0 (by norm_num) (fun _ => 1)
    (by intros; norm_num) 1 (by norm_num)

example : (1 : ℝ) * (intervalMaximalHalo (Finset.Icc (0 : ℤ) 0) (fun _ => 0) 1).card ≤
    3 * ∑ _x ∈ Finset.Icc (0 : ℤ) 0, (0 : ℝ) :=
  intervalMaximalHalo_weak_bound 0 0 (by norm_num) (fun _ => 0)
    (by intros; norm_num) 1 (by norm_num)

end

end NoncommutingDense
