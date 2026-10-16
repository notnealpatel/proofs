import Combinatorics.PermutationBoundaryPerturbation
import Combinatorics.PermutationOverlapTail

set_option autoImplicit false

namespace PermutationFixedFirstLimit

open PermutationOrderCounting PermutationBoundaryStandardization
open PermutationBoundaryPerturbation PermutationOverlapTail
open Filter Topology

attribute [local instance] Classical.propDecidable

/-- Actual avoidance of every nontrivial proper prefix/suffix overlap. -/
def FullAvoid {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, 2 ≤ k → ∀ hkn : k < n, ¬ PermutationOverlapBound.Overlap hkn π

example (π : Equiv.Perm (Fin 2)) : FullAvoid π := by
  intro k hk hkn
  omega

/-- The canonical full avoidance fraction, zero when the size or label is inadmissible. -/
noncomputable def A (n a : ℕ) : ℝ :=
  if h : 1 ≤ n ∧ a < n then
    (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) ⟨a, h.2⟩ // FullAvoid π.val} : ℝ) /
      Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) ⟨a, h.2⟩)
  else 0

example : A 0 0 = 0 := by simp [A]
example : A 2 2 = 0 := by simp [A]
example (n a : ℕ) (h : 1 ≤ n ∧ a < n) :
    A n a = (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) ⟨a, h.2⟩ // FullAvoid π.val} : ℝ) /
      Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) ⟨a, h.2⟩) := by
  simp only [A, dif_pos h]

private theorem event_le {X : Type*} [Finite X] (P Q : X → Prop)
    (h : ∀ x, P x → Q x) : Nat.card {x // P x} ≤ Nat.card {x // Q x} :=
  Nat.card_le_card_of_injective (fun x => ⟨x.val, h x.val x.property⟩)
    (by intro x y hxy; exact Subtype.ext (congrArg (fun z : {x // Q x} => z.val) hxy))

/-- Every canonical fraction lies in the probability interval. -/
theorem A_mem (n a : ℕ) : A n a ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases h : 1 ≤ n ∧ a < n
  · rw [A, dif_pos h]
    let X := FixedFirst (⟨0, by omega⟩ : Fin n) ⟨a, h.2⟩
    have hp : (0 : ℝ) < Nat.card X := by
      exact_mod_cast (Nat.card_pos_iff.mpr ⟨fixedFirst_nonempty _ _, inferInstance⟩ : 0 < Nat.card X)
    have hc : Nat.card {π : X // FullAvoid π.val} ≤ Nat.card X :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    constructor
    · positivity
    · apply (div_le_one hp).mpr
      exact_mod_cast hc
  · simp [A, h]

private theorem sandwich (K n : ℕ) (hK : 4 ≤ K) (hn : 2 * K - 2 ≤ n)
    (m : Fin n) :
    |A n m.val -
      (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) m // ShortAvoid K π.val} : ℝ) /
      Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) m)| ≤ 4 / (K / 2).factorial := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let X := FixedFirst (0 : Fin n) m
  let P : X → Prop := fun π => FullAvoid π.val
  let Q : X → Prop := fun π => ShortAvoid K π.val
  let D : X → Prop := LongOverlap K m
  have hPQ : ∀ π, P π → Q π := by
    intro π hp k hk hkK hkn
    exact hp k hk hkn
  have hQD : ∀ π, Q π → P π ∨ D π := by
    intro π hq
    by_cases hp : P π
    · exact Or.inl hp
    · right
      simp only [P, FullAvoid, not_forall] at hp
      obtain ⟨k, hk, hkn, ho⟩ := hp
      refine ⟨k, ?_, hkn, by simpa using ho⟩
      by_contra h
      exact hq k hk (by omega) hkn (by simpa using ho)
  have hc₁ := event_le P Q hPQ
  have hc₂ : Nat.card {π // Q π} ≤ Nat.card {π // P π} + Nat.card {π // D π} := by
    have hh := event_le Q (fun π => P π ∨ D π) hQD
    exact hh.trans (by simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_or P D)
  have hd : Nat.card {π // D π} = (longOverlapFinset K m).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype _ (fun π => mem_longOverlapFinset K m π)
  have ht := longOverlap_fraction_le K hK m
  simp only [← Nat.card_eq_fintype_card] at ht
  rw [← hd] at ht
  have hp : (0 : ℝ) < Nat.card X := by
    exact_mod_cast (Nat.card_pos_iff.mpr ⟨fixedFirst_nonempty _ _, inferInstance⟩ : 0 < Nat.card X)
  have hr₁ : (Nat.card {π // P π} : ℝ) ≤ Nat.card {π // Q π} := by exact_mod_cast hc₁
  have hr₂ : (Nat.card {π // Q π} : ℝ) ≤ Nat.card {π // P π} + Nat.card {π // D π} := by exact_mod_cast hc₂
  rw [A, dif_pos (show 1 ≤ n ∧ m.val < n from ⟨by omega, m.isLt⟩)]
  change |(Nat.card {π // P π} : ℝ) / Nat.card X - (Nat.card {π // Q π} : ℝ) / Nat.card X| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hp, abs_of_nonpos (by linarith : (Nat.card {π // P π} : ℝ) - Nat.card {π // Q π} ≤ 0)]
  apply le_trans _ ht
  apply (div_le_div_iff_of_pos_right hp).mpr
  linarith

/-- The minimum-first short-avoidance fraction on the boundary size. -/
private noncomputable def b (K : ℕ) (hK : 4 ≤ K) : ℝ :=
  (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩ //
    ShortAvoid K π.val} : ℝ) /
    Nat.card (FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩)

example (K : ℕ) (hK : 4 ≤ K) : b K hK =
    (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩ //
      ShortAvoid K π.val} : ℝ) /
      Nat.card (FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩) := rfl

private theorem approximation (K n a : ℕ) (hK : 4 ≤ K)
    (hn : 2 * K - 2 ≤ n) (ha : a < n) :
    |A n a - b K hK| ≤ 4 / (K / 2).factorial +
      ((2 * K : ℝ) - 3) * a / ((n : ℝ) - 1) := by
  let m : Fin n := ⟨a, ha⟩
  let s : ℝ := (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) m // ShortAvoid K π.val} : ℝ) /
    Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) m)
  have h₁ : |A n a - s| ≤ 4 / (K / 2).factorial := sandwich K n hK hn m
  have h₂ : |s - b K hK| ≤ ((2 * K : ℝ) - 3) * a / ((n : ℝ) - 1) := by
    simpa only [s, b, Nat.card_eq_fintype_card] using
      shortAvoid_fraction_perturbation K n hK hn m
  calc
    |A n a - b K hK| ≤ |A n a - s| + |s - b K hK| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add h₁ h₂

private theorem error_tendsto (K a : ℕ) :
    Tendsto (fun n : ℕ => ((2 * K : ℝ) - 3) * a / ((n : ℝ) - 1)) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro M
    have hn : ∀ᶠ n : ℕ in atTop, M + 1 ≤ (n : ℝ) :=
      (Filter.tendsto_atTop.mp tendsto_natCast_atTop_atTop) (M + 1)
    filter_upwards [hn] with n hn
    linarith
  exact tendsto_const_nhds.div_atTop hd

private theorem small_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 4 ≤ K ∧ (4 : ℝ) / (K / 2).factorial < ε := by
  have ht := (tendsto_order.mp tendsto_bound).2 ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 ht
  exact ⟨max K 4, le_max_right _ _, hK _ (le_max_left _ _)⟩

private theorem minimum_cauchy : CauchySeq (fun n : ℕ => A n 0) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨K, hK, ht⟩ := small_tail (ε / 2) (by positivity)
  refine ⟨2 * K - 2, ?_⟩
  intro n hn m hm
  have h₁ := approximation K n 0 hK hn (by omega)
  have h₂ := approximation K m 0 hK hm (by omega)
  simp only [Nat.cast_zero, mul_zero, zero_div, add_zero] at h₁ h₂
  rw [Real.dist_eq]
  have hab := abs_sub_le (A n 0) (b K hK) (A m 0)
  rw [abs_sub_comm (b K hK) (A m 0)] at hab
  linarith

/-- A single probability is the full avoidance limit for every fixed natural first label. -/
theorem common_fixed_first_limit :
    ∃ p : ℝ, p ∈ Set.Icc 0 1 ∧
      ∀ a : ℕ, Tendsto (fun n : ℕ => A n a) atTop (𝓝 p) := by
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete minimum_cauchy
  refine ⟨p, isClosed_Icc.mem_of_tendsto hp (Eventually.of_forall (fun n => A_mem n 0)), ?_⟩
  intro a
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK, ht⟩ := small_tail (ε / 8) (by positivity)
  have he := (tendsto_order.mp (error_tendsto K a)).2 (ε / 4) (by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 he
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hp (ε / 4) (by positivity)
  refine ⟨max (max N₁ N₂) (max (2 * K - 2) (a + 1)), ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnK : 2 * K - 2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hna : a < n := by have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn; omega
  have h₁ := approximation K n a hK hnK hna
  have h₂ := approximation K n 0 hK hnK (by omega)
  simp only [Nat.cast_zero, mul_zero, zero_div, add_zero] at h₂
  have h₃ := hN₁ n hn₁
  have h₄ := hN₂ n hn₂
  rw [Real.dist_eq] at h₄ ⊢
  have htri₁ := abs_sub_le (A n a) (b K hK) (A n 0)
  rw [abs_sub_comm (b K hK) (A n 0)] at htri₁
  have htri₂ := abs_sub_le (A n a) (A n 0) p
  linarith

private theorem full_le_short (K n : ℕ) (hK : 4 ≤ K) (hn : 2 * K - 2 ≤ n)
    (m : Fin n) :
    A n m.val ≤
      (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) m // ShortAvoid K π.val} : ℝ) /
        Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) m) := by
  rw [A, dif_pos (show 1 ≤ n ∧ m.val < n from ⟨by omega, m.isLt⟩)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast event_le (fun π : FixedFirst (⟨0, by omega⟩ : Fin n) m => FullAvoid π.val)
    (fun π => ShortAvoid K π.val)
    (fun π hp k hk _ hkn => hp k hk hkn)

private theorem minimum_short (K n : ℕ) (hK : 4 ≤ K) (hn : 2 * K - 2 ≤ n) :
    (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) ⟨0, by omega⟩ // ShortAvoid K π.val} : ℝ) /
      Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) ⟨0, by omega⟩) = b K hK := by
  simpa only [b, Nat.card_eq_fintype_card] using shortAvoid_fraction K n (by omega) hn

private theorem b_mem (K : ℕ) (hK : 4 ≤ K) : b K hK ∈ Set.Icc (0 : ℝ) 1 := by
  unfold b
  constructor
  · positivity
  · have hp : (0 : ℝ) < Nat.card (FixedFirst
        (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩) := by
      exact_mod_cast (Nat.card_pos_iff.mpr
        ⟨fixedFirst_nonempty _ _, inferInstance⟩ : 0 < Nat.card (FixedFirst
          (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩))
    apply (div_le_one hp).mpr
    exact_mod_cast Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- The common limit is the infimum of the stabilized minimum-first short fractions. -/
noncomputable def L0 : ℝ := sInf (Set.range (fun K : {K : ℕ // 4 ≤ K} => b K.val K.property))

example : L0 = sInf (Set.range (fun K : {K : ℕ // 4 ≤ K} => b K.val K.property)) := rfl

private theorem b_bdd : BddBelow (Set.range (fun K : {K : ℕ // 4 ≤ K} => b K.val K.property)) :=
  ⟨0, by rintro x ⟨K, rfl⟩; exact (b_mem K.val K.property).1⟩

private theorem b_nonempty : (Set.range (fun K : {K : ℕ // 4 ≤ K} => b K.val K.property)).Nonempty :=
  ⟨b 4 (by decide), ⟨⟨4, by decide⟩, rfl⟩⟩

/-- The explicitly constructed common limit belongs to the probability interval. -/
theorem L0_mem : L0 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csInf b_nonempty (by rintro x ⟨K, rfl⟩; exact (b_mem K.val K.property).1)
  · exact (csInf_le b_bdd (Set.mem_range_self (⟨4, by decide⟩ : {K : ℕ // 4 ≤ K}))).trans
      (b_mem 4 (by decide)).2

private theorem b_sub_le (K J : ℕ) (hK : 4 ≤ K) (hJ : 4 ≤ J) :
    b K hK - b J hJ ≤ 4 / (K / 2).factorial := by
  let n := max (2 * K - 2) (2 * J - 2)
  have hnK : 2 * K - 2 ≤ n := le_max_left _ _
  have hnJ : 2 * J - 2 ≤ n := le_max_right _ _
  have hs := sandwich K n hK hnK (⟨0, by omega⟩ : Fin n)
  rw [minimum_short K n hK hnK] at hs
  have hl := full_le_short J n hJ hnJ (⟨0, by omega⟩ : Fin n)
  rw [minimum_short J n hJ hnJ] at hl
  have hs' := (abs_le.mp hs).1
  change -(4 / (K / 2).factorial : ℝ) ≤ A n 0 - b K hK at hs'
  change A n 0 ≤ b J hJ at hl
  linarith

private theorem b_L0 (K : ℕ) (hK : 4 ≤ K) :
    0 ≤ b K hK - L0 ∧ b K hK - L0 ≤ 4 / (K / 2).factorial := by
  constructor
  · exact sub_nonneg.mpr (csInf_le b_bdd (Set.mem_range_self (⟨K, hK⟩ : {K : ℕ // 4 ≤ K})))
  · have hl : b K hK - 4 / (K / 2).factorial ≤ L0 := by
      apply le_csInf b_nonempty
      rintro x ⟨J, rfl⟩
      have hb := b_sub_le K J.val hK J.property
      linarith
    linarith

/-- Uniform finite error for actual full avoidance, with the same infimum limit. -/
theorem moving_bound (K n a : ℕ) (hK : 4 ≤ K)
    (hn : 2 * K - 2 ≤ n) (ha : a < n) :
    |A n a - L0| ≤ ((2 * K : ℝ) - 3) * a / ((n : ℝ) - 1) +
      4 / (K / 2).factorial := by
  let m : Fin n := ⟨a, ha⟩
  let s : ℝ := (Nat.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) m // ShortAvoid K π.val} : ℝ) /
    Nat.card (FixedFirst (⟨0, by omega⟩ : Fin n) m)
  have hs : |A n a - s| ≤ 4 / (K / 2).factorial := sandwich K n hK hn m
  have hle : A n a ≤ s := full_le_short K n hK hn m
  have hb := b_L0 K hK
  have hp : |s - b K hK| ≤ ((2 * K : ℝ) - 3) * a / ((n : ℝ) - 1) := by
    simpa only [s, b, Nat.card_eq_fintype_card] using shortAvoid_fraction_perturbation K n hK hn m
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp hs
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem moving_error_tendsto (K : ℕ) (n m : ℕ → ℕ)
    (hn : Tendsto n atTop atTop)
    (hr : Tendsto (fun j => (m j : ℝ) / (n j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => ((2 * K : ℝ) - 3) * (m j : ℝ) / ((n j : ℝ) - 1)) atTop (𝓝 0) := by
  have hd : Tendsto (fun j => (n j : ℝ) - 1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro M
    have he := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hn).eventually_ge_atTop (M + 1)
    filter_upwards [he] with j hj
    change M + 1 ≤ (n j : ℝ) at hj
    linarith
  have hi : Tendsto (fun j => ((n j : ℝ) - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hd
  have hp : Tendsto (fun j => (m j : ℝ) / (n j : ℝ) *
      (1 + ((n j : ℝ) - 1)⁻¹)) atTop (𝓝 0) := by
    simpa using hr.mul (tendsto_const_nhds.add hi)
  have hratio : Tendsto (fun j => (m j : ℝ) / ((n j : ℝ) - 1)) atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [hn.eventually_ge_atTop 2] with j hj
    have hpos : (0 : ℝ) < n j := by exact_mod_cast (by omega : 0 < n j)
    have hne : (n j : ℝ) - 1 ≠ 0 := by
      have hh : (2 : ℝ) ≤ n j := by exact_mod_cast hj
      linarith
    field_simp
    ring
  simpa only [mul_zero, mul_div_assoc] using hratio.const_mul ((2 * K : ℝ) - 3)

/-- For every growing size sequence and every eventually admissible sublinear first label,
the actual full avoidance fractions converge to the same explicitly constructed `L0`. -/
theorem moving_first_limit (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hvalid : ∀ᶠ j in atTop, m j < n j)
    (hr : Tendsto (fun j => (m j : ℝ) / (n j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => A (n j) (m j)) atTop (𝓝 L0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK, htail⟩ := small_tail (ε / 2) (by positivity)
  have he := (tendsto_order.mp (moving_error_tendsto K n m hn hr)).2 (ε / 2) (by positivity)
  filter_upwards [hn.eventually_ge_atTop (2 * K - 2), hvalid, he] with j hj hv herr
  rw [Real.dist_eq]
  have hb := moving_bound K (n j) (m j) hK hj hv
  linarith

example : Tendsto (fun j : ℕ => j + 2) atTop atTop ∧
    (∀ j : ℕ, 0 < j + 2) ∧
    Tendsto (fun j : ℕ => (0 : ℝ) / ((j + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  refine ⟨?_, by omega, ?_⟩
  · apply Filter.tendsto_atTop.mpr
    intro b
    exact Filter.eventually_atTop.2 ⟨b, by intro j hj; omega⟩
  · simp

/-- Every fixed natural first label has the same explicitly defined infimum limit. -/
theorem fixed_first_limit (a : ℕ) :
    Tendsto (fun n : ℕ => A n a) atTop (𝓝 L0) := by
  apply moving_first_limit (fun n => n) (fun _ => a) tendsto_id
  · exact Filter.eventually_atTop.2 ⟨a + 1, by intro n hn; omega⟩
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

end PermutationFixedFirstLimit
