import Combinatorics.PermutationCornerStandardization
import Combinatorics.PermutationSameEdgeLimit
import Combinatorics.PermutationOppositeCornerTruncation
import Combinatorics.PermutationEndpointReflection
import Combinatorics.PermutationEndpointProfileReversal
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

/-!
# The actual opposite-corner first-order law

The actual canonical permutation fractions converge to a universal constant
at least `1/8`. For every pair of fixed natural offsets, the actual endpoint
avoidance fraction, multiplied by size, converges to their sum times that
same constant. The proof uses the exact disjoint rare-branch partition,
reverse-complement, finite standardization, and ordered three-term tail bounds.
Initial invalid sizes are handled by explicit eventual guards.
-/

open Filter Topology

namespace PermutationOppositeCornerLimit

open PermutationCornerStandardization PermutationEndpointZeroTwoExact
open PermutationOverlapBound PermutationEndpointCounting

attribute [local instance] Classical.propDecidable

/-- Enlarging the inclusive forbidden-length interval can only decrease a triple fraction. -/
theorem tripleFraction_mono_cutoff {n : ℕ} (hn : 3 ≤ n) (a r h : Fin n)
    (L K J : ℕ) (hKJ : K ≤ J) :
    tripleFraction hn a r h L J ≤ tripleFraction hn a r h L K := by
  unfold tripleFraction
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Fintype.card_le_of_injective
    (fun (π : {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r h // AvoidThrough L J π.val}) => (⟨π.val, fun k hkL hkK hkn =>
      π.property k hkL (hkK.trans hKJ) hkn⟩ :
      {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r h // AvoidThrough L K π.val}))
    (fun x y he => Subtype.ext (congrArg
      (fun z : {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r h // AvoidThrough L K π.val} => z.val) he))

/-- The paid finite consumer has exactly zero error for the canonical endpoint labels. -/
theorem canonical_tripleFraction_eq (K n : ℕ) (hK : 3 ≤ K) (hn : 2 * K ≤ n) :
    tripleFraction (n := n) (by omega) ⟨1, by omega⟩ ⟨0, by omega⟩
      ⟨n - 1, by omega⟩ 3 K = canonicalFraction K hK := by
  have h := finiteConsumer_proof K n 1 0 0 hK hn (by omega) (by omega)
    (by omega) 3 (by simp)
  have hz : |tripleFraction (n := n) (by omega) ⟨1, by omega⟩ ⟨0, by omega⟩
      ⟨n - 1, by omega⟩ 3 K - canonicalFraction K hK| ≤ 0 := by
    simpa only [Nat.sub_zero, Nat.cast_one, Nat.cast_zero, add_zero, sub_self,
      mul_zero, zero_div] using h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- The actual canonical fractions decrease when the cutoff increases by one. -/
theorem canonicalFraction_succ_le (K : ℕ) (hK : 3 ≤ K) :
    canonicalFraction (K + 1) (by omega) ≤ canonicalFraction K hK := by
  rw [← canonical_tripleFraction_eq K (2 * (K + 1)) hK (by omega)]
  exact tripleFraction_mono_cutoff (by omega) _ _ _ 3 K (K + 1) (by omega)

/-- Every actual triple avoidance fraction is nonnegative, including empty fibers. -/
theorem tripleFraction_nonneg {n : ℕ} (hn : 3 ≤ n) (a r h : Fin n) (L K : ℕ) :
    0 ≤ tripleFraction hn a r h L K := by
  unfold tripleFraction
  positivity

/-- The canonical sequence has an actual real limit, obtained from monotonicity and its lower bound. -/
theorem exists_canonical_limit : ∃ C : ℝ, 0 ≤ C ∧
    Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C) := by
  let f : ℕ → ℝ := fun K => canonicalFraction (K + 3) (by omega)
  have ha : Antitone f := by
    apply antitone_nat_of_succ_le
    intro K
    exact canonicalFraction_succ_le (K + 3) (by omega)
  have hn : ∀ K, 0 ≤ f K := fun K => tripleFraction_nonneg _ _ _ _ _ _
  have hb : BddBelow (Set.range f) := ⟨0, by rintro x ⟨K, rfl⟩; exact hn K⟩
  exact ⟨⨅ K, f K, le_ciInf hn, tendsto_atTop_ciInf ha hb⟩

/-- The actual all-length avoidance fraction on a three-anchor fiber. -/
noncomputable def actualTripleFraction {n : ℕ} (hn : 3 ≤ n) (a r h : Fin n) : ℝ :=
  (Fintype.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
    ⟨n - 1, by omega⟩ a r h //
      ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val} : ℝ) /
    Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r h)

example : actualTripleFraction (by decide : 3 ≤ 3) (0 : Fin 3) 1 2 = 0 := by
  have he : IsEmpty {π : FixedThree (0 : Fin 3) 1 2 0 1 2 //
      ∀ k, 2 ≤ k → ∀ hk : k < 3, ¬ Overlap hk π.val} := by
    refine ⟨fun π => π.property 2 (by decide) (by decide) ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [π.val.property.1.1, π.val.property.1.2, π.val.property.2]
  letI := he
  simp [actualTripleFraction]

/-- Aligning the strict source cutoff with the inclusive consumer retains all three tail terms. -/
theorem actualTripleFraction_truncation {n K D : ℕ}
    (hK : 3 ≤ K) (hKn : 2 * (K + 1) ≤ n) (hD : 2 ≤ D) (hDn : 2 * D < n)
    (a r h : Fin n) (hra : r < a) (hah : a < h) :
    tripleFraction (by omega) a r h 2 K - actualTripleFraction (by omega) a r h ≤
      2 / (K.factorial : ℝ) + (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) +
        2 / ((D + 1).factorial : ℝ) := by
  have ht := PermutationOppositeCornerTruncation.actual_avoidance_truncation_bound
    (K := K + 1) (by omega) hKn hD hDn a r h hra hah
  have hw : (∀ (π : Equiv.Perm (Fin n)),
      (∀ k, 2 ≤ k → k < K + 1 → ∀ hk : k < n, ¬ Overlap hk π) ↔
      AvoidThrough 2 K π) := by
    intro π
    constructor
    · intro hp k hk hkK hkn
      exact hp k hk (by omega) hkn
    · intro hp k hk hkK hkn
      exact hp k hk (by omega) hkn
  simpa only [actualTripleFraction, tripleFraction, Nat.add_sub_cancel,
    Fintype.card_subtype, hw, Finset.card_filter, add_assoc] using ht.2

/-- The all-length event is contained in each finite-window event. -/
theorem actualTripleFraction_le {n : ℕ} (hn : 3 ≤ n) (a r h : Fin n) (K : ℕ) :
    actualTripleFraction hn a r h ≤ tripleFraction hn a r h 2 K := by
  unfold actualTripleFraction tripleFraction
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Fintype.card_le_of_injective
    (fun (π : {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r h // ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val}) =>
      (⟨π.val, fun k hk _ hkn => π.property k hk hkn⟩ :
      {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩ a r h //
        AvoidThrough 2 K π.val}))
    (fun x y he => Subtype.ext (congrArg (fun z :
      {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩ a r h //
        AvoidThrough 2 K π.val} => z.val) he))

/-- A natural-indexed actual low-triple fraction, zero only outside the valid low-branch guard. -/
noncomputable def lowFraction (n a r b : ℕ) : ℝ :=
  if H : 3 ≤ n ∧ r < a ∧ a < n - 1 - b then
    actualTripleFraction H.1 ⟨a, by omega⟩ ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩
  else 0

/-- On its explicit guard the natural low fraction is the unchanged actual cardinal ratio. -/
theorem lowFraction_eq {n a r b : ℕ} (hn : 3 ≤ n) (hr : r < a) (ha : a < n - 1 - b) :
    lowFraction n a r b = actualTripleFraction hn ⟨a, by omega⟩ ⟨r, by omega⟩
      ⟨n - 1 - b, by omega⟩ := by
  have H : 3 ≤ n ∧ r < a ∧ a < n - 1 - b := ⟨hn, hr, ha⟩
  simp only [lowFraction, dif_pos H]

example : lowFraction 3 0 0 0 = 0 := by simp [lowFraction]
example : lowFraction 6 1 0 0 = actualTripleFraction (by decide) (1 : Fin 6) 0 5 :=
  lowFraction_eq (by decide) (by decide) (by decide)

/-- Every fixed low branch converges to the same actual canonical limit, using ordered cutoff, tail, then size choices. -/
theorem tendsto_lowFraction {C : ℝ}
    (hC : Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C))
    (a r b : ℕ) (hr : r < a) :
    Tendsto (fun n => lowFraction n a r b) atTop (𝓝 C) := by
  have hfac (c : ℝ) : Tendsto (fun j : ℕ => c / (j.factorial : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 6 := by linarith
  obtain ⟨J, hJc, hJf⟩ := ((Metric.tendsto_nhds.mp hC (ε / 6) he).and
    (Metric.tendsto_nhds.mp ((hfac 2).comp (tendsto_add_atTop_nat 3)) (ε / 6) he)).exists
  let K := J + 3
  have hK : 3 ≤ K := by omega
  have hcan : |canonicalFraction K hK - C| < ε / 6 := hJc
  have htailK : 2 / (K.factorial : ℝ) < ε / 6 := by
    exact lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero, Function.comp_def] using hJf)
  obtain ⟨D, hD, hDf⟩ := ((eventually_ge_atTop 2).and
    (Metric.tendsto_nhds.mp ((hfac 2).comp (tendsto_add_atTop_nat 1)) (ε / 6) he)).exists
  have htailD : 2 / ((D + 1).factorial : ℝ) < ε / 6 :=
    lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero, Function.comp_def] using hDf)
  have hsub : Tendsto (fun n : ℕ => n - 3) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N + 3)] with n hn
    omega
  have hmiddle := (hfac (2 * (D - 1))).comp
    ((Nat.tendsto_div_const_atTop (by omega : D ≠ 0)).comp hsub)
  have hsmall : Tendsto (fun n : ℕ =>
      ((2 * K : ℝ) - 3) * ((a : ℝ) + b - 1) / ((n : ℝ) - 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      apply tendsto_atTop.mpr
      intro z
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually (eventually_ge_atTop (z + 3))]
        with n hn
      linarith)
  filter_upwards [eventually_ge_atTop (2 * (K + 1) + 2 * D + a + b + 10),
    Metric.tendsto_nhds.mp hmiddle (ε / 6) he,
    Metric.tendsto_nhds.mp hsmall (ε / 6) he] with n hn hm hs
  have hn3 : 3 ≤ n := by omega
  have ha : a < n - 1 - b := by omega
  rw [lowFraction_eq hn3 hr ha, Real.dist_eq]
  let p := actualTripleFraction hn3 ⟨a, by omega⟩ ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩
  let q := tripleFraction hn3 ⟨a, by omega⟩ ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩ 2 K
  have hpq : p ≤ q := actualTripleFraction_le hn3 _ _ _ K
  have htail := actualTripleFraction_truncation hK (by omega) hD (by omega)
    (⟨a, by omega⟩ : Fin n) ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩ hr ha
  have hfinite := finiteConsumer_proof K n a b r hK (by omega) hr ha (by omega) 2 (by simp)
  have hmid : (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) < ε / 6 :=
    lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero, Function.comp_def] using hm)
  have hsm : ((2 * K : ℝ) - 3) * ((a : ℝ) + b - 1) / ((n : ℝ) - 3) < ε / 6 :=
    lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using hs)
  have hf := abs_le.mp hfinite
  have hc := abs_lt.mp hcan
  apply abs_lt.mpr
  change -ε < p - C ∧ p - C < ε
  constructor <;> dsimp [p, q] at * <;> linarith

/-- Reverse both positions and labels; this maps an upper penultimate branch to a lower second branch. -/
def reverseComplement {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  PermutationEndpointReflection.complement (PermutationEndpointProfile.reversePositions π)

example {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    reverseComplement π i = (π i.rev).rev := rfl

/-- Reverse-complement is an involution on actual permutations. -/
theorem reverseComplement_involutive {n : ℕ} :
    Function.Involutive (@reverseComplement n) := by
  intro π
  apply Equiv.ext
  intro i
  change (π i.rev.rev).rev.rev = π i
  simp

/-- Reverse-complement preserves every proper overlap, not just short or disjoint ones. -/
theorem overlap_reverseComplement_iff {n k : ℕ} (hkn : k < n)
    (π : Equiv.Perm (Fin n)) : Overlap hkn (reverseComplement π) ↔ Overlap hkn π := by
  exact (PermutationEndpointReflection.overlap_complement_iff hkn _).trans
    (PermutationEndpointProfile.overlap_reversePositions_iff hkn π)

/-- Reverse-complement reverses the order of three anchors and complements their labels. -/
def fixedThreeReverseComplementEquiv {n : ℕ} (p q t a r h : Fin n) :
    FixedThree p q t a r h ≃ FixedThree t.rev q.rev p.rev h.rev r.rev a.rev where
  toFun π := ⟨reverseComplement π.val, by
    change ((π.val t.rev.rev).rev = h.rev ∧ (π.val q.rev.rev).rev = r.rev) ∧
      (π.val p.rev.rev).rev = a.rev
    simp only [Fin.rev_rev, π.property.1.1, π.property.1.2, π.property.2, and_self]⟩
  invFun π := ⟨reverseComplement π.val, by
    change ((π.val p.rev).rev = a ∧ (π.val q.rev).rev = r) ∧ (π.val t.rev).rev = h
    simp only [π.property.1.1, π.property.1.2, π.property.2, Fin.rev_rev, and_self]⟩
  left_inv π := Subtype.ext (reverseComplement_involutive π.val)
  right_inv π := Subtype.ext (reverseComplement_involutive π.val)

example {n : ℕ} (p q t a r h : Fin n) (π : FixedThree p q t a r h) :
    (fixedThreeReverseComplementEquiv p q t a r h π).val = reverseComplement π.val := rfl

/-- The full-avoidance subtypes of the reverse-complement triple fibers are equivalent. -/
def avoidThreeReverseComplementEquiv {n : ℕ} (p q t a r h : Fin n) :
    {π : FixedThree p q t a r h // ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val} ≃
    {π : FixedThree t.rev q.rev p.rev h.rev r.rev a.rev //
      ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val} :=
  (fixedThreeReverseComplementEquiv p q t a r h).subtypeEquiv (by
    intro π
    constructor
    · intro hp k hk hkn ho
      exact hp k hk hkn ((overlap_reverseComplement_iff hkn π.val).mp ho)
    · intro hp k hk hkn ho
      exact hp k hk hkn ((overlap_reverseComplement_iff hkn π.val).mpr ho))

example {n : ℕ} (p q t a r h : Fin n)
    (π : {π : FixedThree p q t a r h //
      ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val}) :
    (avoidThreeReverseComplementEquiv p q t a r h π).val.val =
      reverseComplement π.val.val := rfl

/-- Two descending boundary pairs force the actual length-two overlap. -/
theorem overlap_two_of_descending {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (π : Equiv.Perm (Fin n))
    (hl : π ⟨1, by omega⟩ < π 0)
    (hr : π ⟨n - 1, by omega⟩ < π ⟨n - 2, by omega⟩) :
    Overlap (by omega : 2 < n) π := by
  have he : (⟨1 + (n - 2), by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    change 1 + (n - 2) = n - 1
    omega
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Nat.zero_add]
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · change π 0 < π ⟨1, by omega⟩ ↔ π ⟨n - 2, by omega⟩ < π ⟨1 + (n - 2), by omega⟩
    rw [he]
    exact iff_of_false (not_lt_of_gt hl) (not_lt_of_gt hr)
  · change π ⟨1, by omega⟩ < π 0 ↔ π ⟨1 + (n - 2), by omega⟩ < π ⟨n - 2, by omega⟩
    rw [he]
    exact iff_of_true hl hr
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)

/-- The two rare boundary orientations are disjoint inside actual full avoidance. -/
theorem avoidTwo_branches_disjoint {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (a h : Fin n) (π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h)
    (hl : π.val ⟨1, by omega⟩ < a) : ¬ h < π.val ⟨n - 2, by omega⟩ := by
  intro hr
  apply π.property.2 2 (by omega) (by omega)
  apply overlap_two_of_descending hn π.val
  · simpa only [π.property.1.1] using hl
  · simpa only [π.property.1.2] using hr

/-- Actual avoidance is exactly the disjoint sum of its low-second and high-penultimate branches. -/
noncomputable def avoidTwoBranchesEquiv {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n) :
    PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h ≃
      ({π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h //
        π.val ⟨1, by omega⟩ < a} ⊕
       {π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h //
        h < π.val ⟨n - 2, by omega⟩}) where
  toFun π := if hl : π.val ⟨1, by omega⟩ < a then Sum.inl ⟨π, hl⟩
    else Sum.inr ⟨π, (PermutationMixedEndpointBound.avoidTwo_mem_union hn
      ⟨n - 1, by omega⟩ (by dsimp; omega) a h π).resolve_left hl⟩
  invFun x := x.elim Subtype.val Subtype.val
  left_inv π := by dsimp; split_ifs <;> rfl
  right_inv x := by
    cases x with
    | inl π => simp [π.property]
    | inr π =>
      have hnlow : ¬ π.val.val ⟨1, by omega⟩ < a := by
        intro hl
        exact avoidTwo_branches_disjoint hn a h π.val hl π.property
      simp [hnlow]

/-- The low branch is the disjoint union of its actual three-anchor fibers, indexed by every label below `a`. -/
def lowBranchEquiv {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n) :
    {π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h //
      π.val ⟨1, by omega⟩ < a} ≃
    (Σ r : Fin a.val,
      {π : FixedThree (0 : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩
        a ⟨r.val, r.isLt.trans a.isLt⟩ h //
        ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val}) where
  toFun π := ⟨⟨(π.val.val ⟨1, by omega⟩).val, π.property⟩,
    ⟨⟨π.val.val, ⟨π.val.property.1.1, rfl⟩, π.val.property.1.2⟩, π.val.property.2⟩⟩
  invFun x := ⟨⟨x.2.val.val, ⟨x.2.val.property.1.1, x.2.val.property.2⟩,
    x.2.property⟩, by
      change x.2.val.val ⟨1, by omega⟩ < a
      rw [x.2.val.property.1.2]
      exact x.1.isLt⟩
  left_inv π := rfl
  right_inv x := by
    rcases x with ⟨⟨r, hr⟩, ⟨⟨ρ, hρ⟩, havoid⟩⟩
    have hv : (ρ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hn⟩).val = r :=
      congrArg Fin.val hρ.1.2
    subst r
    rfl

example {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n)
    (π : {π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h //
      π.val ⟨1, by omega⟩ < a}) :
    (lowBranchEquiv hn a h π).1.val = (π.val.val ⟨1, by omega⟩).val := rfl

/-- Reverse-complement bijects actual endpoint-conditioned full avoiders. -/
def avoidTwoReverseComplementEquiv {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n) :
    PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h ≃
    PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ h.rev a.rev where
  toFun π := ⟨reverseComplement π.val, by
    have hz : (0 : Fin n).rev = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_zero]
    have hl : (⟨n - 1, by omega⟩ : Fin n).rev = 0 := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_zero]
      omega
    refine ⟨?_, fun k hk hkn ho => π.property.2 k hk hkn
      ((overlap_reverseComplement_iff hkn π.val).mp ho)⟩
    change (π.val (0 : Fin n).rev).rev = h.rev ∧
      (π.val (⟨n - 1, by omega⟩ : Fin n).rev).rev = a.rev
    rw [hz, hl, π.property.1.1, π.property.1.2]
    exact ⟨rfl, rfl⟩⟩
  invFun π := ⟨reverseComplement π.val, by
    have hz : (0 : Fin n).rev = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_zero]
    have hl : (⟨n - 1, by omega⟩ : Fin n).rev = 0 := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_zero]
      omega
    refine ⟨?_, fun k hk hkn ho => π.property.2 k hk hkn
      ((overlap_reverseComplement_iff hkn π.val).mp ho)⟩
    change (π.val (0 : Fin n).rev).rev = a ∧
      (π.val (⟨n - 1, by omega⟩ : Fin n).rev).rev = h
    rw [hz, hl, π.property.1.1, π.property.1.2, Fin.rev_rev, Fin.rev_rev]
    exact ⟨rfl, rfl⟩⟩
  left_inv π := Subtype.ext (reverseComplement_involutive π.val)
  right_inv π := Subtype.ext (reverseComplement_involutive π.val)

example {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n)
    (π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h) :
    (avoidTwoReverseComplementEquiv hn a h π).val = reverseComplement π.val := rfl

/-- The high penultimate branch becomes exactly the low second branch after reverse-complement. -/
def highBranchEquivLow {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n) :
    {π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h //
      h < π.val ⟨n - 2, by omega⟩} ≃
    {π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ h.rev a.rev //
      π.val ⟨1, by omega⟩ < h.rev} :=
  (avoidTwoReverseComplementEquiv hn a h).subtypeEquiv (by
    intro π
    change h < π.val ⟨n - 2, by omega⟩ ↔
      (π.val (⟨1, by omega⟩ : Fin n).rev).rev < h.rev
    have he : (⟨1, by omega⟩ : Fin n).rev = ⟨n - 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
    rw [he, Fin.rev_lt_rev])

example {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n)
    (π : {π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h //
      h < π.val ⟨n - 2, by omega⟩}) :
    (highBranchEquivLow hn a h π).val.val = reverseComplement π.val.val := rfl

/-- Counting the exact disjoint branches gives two sums of actual triple avoidance cardinalities. -/
theorem card_avoidTwo_eq_sum {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n) :
    Fintype.card (PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h) =
      (∑ r : Fin a.val,
        Fintype.card {π : FixedThree (0 : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩
          a ⟨r.val, r.isLt.trans a.isLt⟩ h //
          ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val}) +
      (∑ s : Fin h.rev.val,
        Fintype.card {π : FixedThree (0 : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩
          h.rev ⟨s.val, s.isLt.trans h.rev.isLt⟩ a.rev //
          ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val}) := by
  have hl := Fintype.card_congr (lowBranchEquiv hn a h)
  have hh := Fintype.card_congr ((highBranchEquivLow hn a h).trans
    (lowBranchEquiv hn h.rev a.rev))
  have hc := Fintype.card_congr (avoidTwoBranchesEquiv hn a h)
  rw [Fintype.card_sum, hl, hh, Fintype.card_sigma, Fintype.card_sigma] at hc
  exact hc

/-- Each low triple fiber has exactly one `(n-2)`th of its endpoint fiber's mass. -/
theorem card_lowTriple_mul {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a r h : Fin n)
    (hra : r < a) (hah : a < h) :
    Fintype.card (FixedThree (0 : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩ a r h) *
      (n - 2) = Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a h) := by
  have he : Fintype.card (FixedThree (0 : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩ a r h) =
      Fintype.card (FixedThree (0 : Fin n) ⟨n - 1, by omega⟩ ⟨1, by omega⟩ a h r) := by
    apply Fintype.card_congr
    exact {
      toFun := fun π => ⟨π.val, ⟨π.property.1.1, π.property.2⟩, π.property.1.2⟩
      invFun := fun π => ⟨π.val, ⟨π.property.1.1, π.property.2⟩, π.property.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he]
  apply card_fixedThree_mul
  · intro hi
    have hv := congrArg Fin.val hi
    change 1 = 0 at hv
    omega
  · intro hi
    have hv := congrArg Fin.val hi
    change 1 = n - 1 at hv
    omega
  · exact ne_of_lt hah
  · exact ne_of_lt hra
  · exact ne_of_lt (hra.trans hah)

/-- The cardinal weight turns a low-triple conditional fraction into its endpoint-fiber contribution. -/
theorem lowTriple_fraction_weight {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a r h : Fin n)
    (hra : r < a) (hah : a < h) :
    (Fintype.card {π : FixedThree (0 : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩ a r h //
      ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val} : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a h) =
      actualTripleFraction hn a r h / ((n : ℝ) - 2) := by
  have hz : (0 : Fin n) = ⟨0, by omega⟩ := by
    apply Fin.ext
    exact Fin.val_zero n
  rw [← card_lowTriple_mul hn a r h hra hah]
  simp only [actualTripleFraction, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_ofNat, div_div, hz]
  rfl

/-- The genuine disjoint branch count gives an exact sum of conditional low-triple fractions. -/
theorem actual_fraction_eq_sum {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n)
    (hah : a < h) :
    (Fintype.card (PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h) : ℝ) /
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a h) =
    ((∑ r : Fin a.val, actualTripleFraction hn a ⟨r.val, r.isLt.trans a.isLt⟩ h) +
      (∑ s : Fin h.rev.val, actualTripleFraction hn h.rev ⟨s.val, s.isLt.trans h.rev.isLt⟩ a.rev)) /
        ((n : ℝ) - 2) := by
  have hz : (0 : Fin n).rev = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_zero]
  have hden : Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a h) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ h.rev a.rev) := by
    let e : FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a h ≃
        FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ h a := by
      simpa only [hz] using PermutationEndpointProfile.fixedTwoReverseEquiv a h
    exact Fintype.card_congr (e.trans
      (PermutationEndpointReflection.fixedTwoComplementEquiv _ _ h a))
  have hc := card_avoidTwo_eq_sum hn a h
  have hcR := congrArg (fun j : ℕ => (j : ℝ)) hc
  push_cast at hcR
  rw [hcR]
  simp only [add_div, Finset.sum_div]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r _
    exact lowTriple_fraction_weight hn a _ h r.isLt hah
  · apply Finset.sum_congr rfl
    intro s _
    rw [hden]
    exact lowTriple_fraction_weight hn h.rev _ a.rev s.isLt (Fin.rev_lt_rev.mpr hah)

/-- For all sufficiently separated natural endpoints, actual avoidance is exactly the two low-branch sums. -/
theorem F_eq_low_sums {n a b : ℕ} (hn : 3 ≤ n) (hab : a + b + 1 < n) :
    PermutationSameEdgeLimit.F n a (n - 1 - b) =
      ((∑ r : Fin a, lowFraction n a r.val b) +
        (∑ s : Fin b, lowFraction n b s.val a)) / ((n : ℝ) - 2) := by
  letI : NeZero n := ⟨by omega⟩
  let A : Fin n := ⟨a, by omega⟩
  let H : Fin n := ⟨n - 1 - b, by omega⟩
  have hrev : H.rev = ⟨b, by omega⟩ := by
    apply Fin.ext
    dsimp [H]
    omega
  have arev : A.rev = ⟨n - 1 - a, by omega⟩ := by
    apply Fin.ext
    dsimp [A]
    omega
  rw [PermutationSameEdgeLimit.F_eq_actual (by omega) (by omega) (by omega) (by omega)]
  have hg := actual_fraction_eq_sum hn A H (by change a < n - 1 - b; omega)
  simp only [hrev, arev] at hg
  dsimp [A, H] at hg
  rw [hg]
  congr 1
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r _
    exact (lowFraction_eq (a := a) (b := b) hn r.isLt (by omega)).symm
  · let e : Fin H.rev.val ≃ Fin b := finCongr (congrArg Fin.val hrev)
    apply Finset.sum_equiv e (by intro s; simp)
    intro s _
    have hs : s.val < b := lt_of_lt_of_eq s.isLt (congrArg Fin.val hrev)
    simpa [e] using (lowFraction_eq (a := b) (b := a) hn hs (by omega)).symm

/-- The real first-order normalization tends to one, independently of invalid initial sizes. -/
theorem tendsto_normalization :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 2)) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) - 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      apply tendsto_atTop.mpr
      intro z
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually (eventually_ge_atTop (z + 2))]
        with n hn
      linarith)
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) + 2 / ((n : ℝ) - 2)) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hsmall
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hne : (n : ℝ) - 2 ≠ 0 := by
    have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [hne]
  <;> ring

/-- Every actual opposite-corner first-order sequence has the canonical limit times its two branch counts. -/
theorem tendsto_corner {C : ℝ}
    (hC : Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C))
    (a b : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * PermutationSameEdgeLimit.F n a (n - 1 - b))
      atTop (𝓝 (((a : ℝ) + (b : ℝ)) * C)) := by
  have hl := tendsto_finsetSum Finset.univ (fun r (_ : r ∈ (Finset.univ : Finset (Fin a))) =>
    tendsto_lowFraction hC a r.val b r.isLt)
  have hh := tendsto_finsetSum Finset.univ (fun s (_ : s ∈ (Finset.univ : Finset (Fin b))) =>
    tendsto_lowFraction hC b s.val a s.isLt)
  have hs : Tendsto (fun n => (∑ r : Fin a, lowFraction n a r.val b) +
      (∑ s : Fin b, lowFraction n b s.val a)) atTop (𝓝 (((a : ℝ) + b) * C)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      add_mul] using hl.add hh
  have ht := tendsto_normalization.mul hs
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (a + b + 4)] with n hn
  rw [F_eq_low_sums (by omega) (by omega)]
  ring

/-- The canonical limit inherits the actual first-order lower bound from the corner `(1,0)`. -/
theorem canonical_limit_lower_bound {C : ℝ}
    (hC : Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C)) :
    (1 / 8 : ℝ) ≤ C := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ) * PermutationSameEdgeLimit.F n 1 (n - 1))
      atTop (𝓝 C) := by
    simpa only [Nat.sub_zero, Nat.cast_one, Nat.cast_zero, add_zero, one_mul] using
      tendsto_corner hC 1 0
  have hl : Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) - 2)) / 8)
      atTop (𝓝 (1 / 8 : ℝ)) := tendsto_normalization.div_const 8
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_ge_atTop 24] with n hn
  have hb := PermutationOppositeCornerTruncation.one_div_eight_mul_sub_le_F hn
  have hmul := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  convert hmul using 1
  rw [div_div, mul_comm ((n : ℝ) - 2) 8, mul_one_div]

/-- The whole actual opposite-corner first-order law has one universal positive canonical limit. -/
theorem exists_opposite_corner_limit : ∃ C : ℝ, (1 / 8 : ℝ) ≤ C ∧
    Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C) ∧
    ∀ a b : ℕ, Tendsto (fun n : ℕ => (n : ℝ) *
      PermutationSameEdgeLimit.F n a (n - 1 - b)) atTop (𝓝 (((a : ℝ) + (b : ℝ)) * C)) := by
  obtain ⟨C, _, hC⟩ := exists_canonical_limit
  exact ⟨C, canonical_limit_lower_bound hC, hC, tendsto_corner hC⟩

/-- With the extreme endpoints zero and last, both rare branches are empty and actual avoidance is impossible. -/
theorem F_zero_last {n : ℕ} (hn : 3 ≤ n) :
    PermutationSameEdgeLimit.F n 0 (n - 1) = 0 := by
  letI : NeZero n := ⟨by omega⟩
  letI : IsEmpty (PermutationMixedEndpointBound.AvoidTwo
      (⟨n - 1, by omega⟩ : Fin n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩) := by
    refine ⟨fun π => ?_⟩
    obtain hl | hr := PermutationMixedEndpointBound.avoidTwo_mem_union hn
      ⟨n - 1, by omega⟩ (by dsimp; omega) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ π
    · change (π.val ⟨1, by omega⟩).val < 0 at hl
      omega
    · change n - 1 < (π.val ⟨n - 2, by omega⟩).val at hr
      have hb := (π.val ⟨n - 2, by omega⟩).isLt
      omega
  rw [PermutationSameEdgeLimit.F_eq_actual (by omega) (by omega) (by omega) (by omega)]
  simp only [Fintype.card_of_isEmpty, Nat.cast_zero, zero_div]

/-- The double-empty opposite corner has an identically zero eventual first-order sequence. -/
theorem tendsto_zero_corner :
    Tendsto (fun n : ℕ => (n : ℝ) * PermutationSameEdgeLimit.F n 0 (n - 1 - 0))
      atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  simp only [Nat.sub_zero, F_zero_last hn, mul_zero]

example {n : ℕ} [NeZero n] (hn : 3 ≤ n) (a h : Fin n)
    (π : PermutationMixedEndpointBound.AvoidTwo ⟨n - 1, by omega⟩ a h)
    (hl : π.val ⟨1, by omega⟩ < a) :
    avoidTwoBranchesEquiv hn a h π = Sum.inl ⟨π, hl⟩ := by
  simp [avoidTwoBranchesEquiv, hl]

example : Nonempty (FixedThree (0 : Fin 8) 1 7 2 0 6) := by
  exact ⟨⟨(Equiv.swap 0 2).trans ((Equiv.swap 1 0).trans (Equiv.swap 7 6)), by decide⟩⟩

example : Nonempty (FixedThree (0 : Fin 6) 1 5 1 0 5) :=
  ⟨⟨Equiv.swap 0 1, by decide⟩⟩

end PermutationOppositeCornerLimit
