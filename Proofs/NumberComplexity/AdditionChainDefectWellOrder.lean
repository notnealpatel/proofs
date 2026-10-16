import NumberComplexity.AdditionChainWeightBound
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.WellQuasiOrder
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.WithBot

set_option autoImplicit false
open scoped BigOperators
namespace NumberComplexity

/-- The actual addition-chain defect, with its usual totalized value at zero. -/
noncomputable def additionChainDefect (n : ℕ) : ℝ := (l n : ℝ) - Real.logb 2 n

example : additionChainDefect 1 = 0 := by simp [additionChainDefect, l_one]
example : additionChainDefect 0 = 0 := by simp [additionChainDefect, l_zero]

/-- Defects of positive integers; the totalized value at zero is excluded. -/
def additionChainDefects : Set ℝ := {d | ∃ n : ℕ, 0 < n ∧ d = additionChainDefect n}

example : (0 : ℝ) ∈ additionChainDefects := ⟨1, by decide, by simp [additionChainDefect, l_one]⟩

private noncomputable def dyadicTerm : WithTop ℕ → ℝ
  | ⊤ => 0
  | (e : ℕ) => ((2 : ℝ) ^ e)⁻¹

example : dyadicTerm (0 : ℕ) = 1 := by norm_num [dyadicTerm]
example : dyadicTerm ⊤ = 0 := rfl

private theorem dyadicTerm_antitone : Antitone dyadicTerm := by
  intro a b hab
  cases a using WithTop.recTopCoe with
  | top => have hb : b = ⊤ := top_le_iff.mp hab; subst b; exact le_rfl
  | coe a =>
    cases b using WithTop.recTopCoe with
    | top => exact le_of_lt (by dsimp [dyadicTerm]; positivity)
    | coe b =>
      have hab' : a ≤ b := by exact_mod_cast hab
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hab')

private theorem tuple_sums_pwo (K : ℕ) :
    (Set.range (fun t : Fin K → WithTop ℕ =>
      (∑ i, dyadicTerm (t i) : ℝᵒᵈ))).IsPWO := by
  have hm : Monotone (fun t : Fin K → WithTop ℕ =>
      (∑ i, dyadicTerm (t i) : ℝᵒᵈ)) := by
    intro a b hab
    exact Finset.sum_le_sum fun i _ => dyadicTerm_antitone (hab i)
  simpa using (Set.isPWO_of_wellQuasiOrderedLE
    (Set.univ : Set (Fin K → WithTop ℕ))).image_of_monotone hm

private theorem list_tuple (es : List ℕ) (K : ℕ) (h : es.length ≤ K) :
    ∃ t : Fin K → WithTop ℕ, ∑ i, dyadicTerm (t i) =
      (es.map (fun e => ((2 : ℝ) ^ e)⁻¹)).sum := by
  induction K generalizing es with
  | zero =>
    have he : es = [] := List.length_eq_zero_iff.mp (by omega)
    subst es
    exact ⟨Fin.elim0, by simp⟩
  | succ K ih =>
    cases es with
    | nil => exact ⟨fun _ => ⊤, by simp [dyadicTerm]⟩
    | cons e es =>
      obtain ⟨t, ht⟩ := ih es (by simpa using Nat.le_of_succ_le_succ h)
      refine ⟨Fin.cons (e : WithTop ℕ) t, ?_⟩
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, List.map_cons,
        List.sum_cons]
      rw [ht]
      rfl

private theorem normalized_tuple (n K : ℕ) (hw : binaryWeight n ≤ K) :
    ∃ t : Fin K → WithTop ℕ, ∑ i, dyadicTerm (t i) =
      (n : ℝ) / 2 ^ Nat.log 2 n := by
  let m := Nat.log 2 n
  let es := n.bitIndices.map (fun i => m - i)
  obtain ⟨t, ht⟩ := list_tuple es K (by simpa [es] using hw)
  refine ⟨t, ht.trans ?_⟩
  have hterms : ∀ i ∈ n.bitIndices,
      ((2 : ℝ) ^ (m - i))⁻¹ = (2 : ℝ) ^ i * ((2 : ℝ) ^ m)⁻¹ := by
    intro i hi
    have him : i ≤ m := Nat.le_log_of_pow_le (by decide)
      (Nat.two_pow_le_of_mem_bitIndices hi)
    have hp : (2 : ℝ) ^ m = 2 ^ (m - i) * 2 ^ i := by
      rw [← pow_add, Nat.sub_add_cancel him]
    rw [hp, mul_inv_rev]
    field_simp
  have hmap : es.map (fun e => ((2 : ℝ) ^ e)⁻¹) =
      n.bitIndices.map (fun i => (2 : ℝ) ^ i * ((2 : ℝ) ^ m)⁻¹) := by
    simp only [es, List.map_map]
    exact List.map_congr_left hterms
  rw [hmap, List.sum_map_mul_right]
  have hsum : (n.bitIndices.map (fun i => (2 : ℝ) ^ i)).sum = n := by
    have cast_sum : ∀ L : List ℕ,
        (L.map (fun i => (2 : ℝ) ^ i)).sum =
          (((L.map (fun i => (2 : ℕ) ^ i)).sum : ℕ) : ℝ) := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih =>
        simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add, Nat.cast_pow,
          Nat.cast_ofNat]
    calc
      _ = (((n.bitIndices.map (fun i => (2 : ℕ) ^ i)).sum : ℕ) : ℝ) := cast_sum _
      _ = n := by rw [Nat.sum_map_two_pow_bitIndices]
  rw [hsum]
  rfl

private theorem normalized_bounds (n : ℕ) (hn : 0 < n) :
    1 ≤ (n : ℝ) / 2 ^ Nat.log 2 n ∧ (n : ℝ) / 2 ^ Nat.log 2 n < 2 := by
  have hlo : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  have hhi : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  constructor
  · exact (le_div_iff₀ (by positivity)).2 (by simpa using hlo)
  · apply (div_lt_iff₀ (by positivity)).2
    simpa [pow_succ, mul_comm] using hhi

private theorem defect_normalized (n : ℕ) (hn : 0 < n) :
    additionChainDefect n = ((l n - Nat.log 2 n : ℕ) : ℝ) -
      Real.logb 2 ((n : ℝ) / 2 ^ Nat.log 2 n) := by
  have hl := log_two_le_l n hn
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_sub hl]
  unfold additionChainDefect
  ring

private theorem defect_interval (n : ℕ) (hn : 0 < n) :
    ((l n - Nat.log 2 n : ℕ) : ℝ) - 1 < additionChainDefect n ∧
      additionChainDefect n ≤ ((l n - Nat.log 2 n : ℕ) : ℝ) := by
  obtain ⟨hlo, hhi⟩ := normalized_bounds n hn
  have hpos : 0 < (n : ℝ) / 2 ^ Nat.log 2 n := lt_of_lt_of_le zero_lt_one hlo
  have hloglo : 0 ≤ Real.logb 2 ((n : ℝ) / 2 ^ Nat.log 2 n) :=
    Real.logb_nonneg (by norm_num) hlo
  have hloghi : Real.logb 2 ((n : ℝ) / 2 ^ Nat.log 2 n) < 1 := by
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hpos hhi
  rw [defect_normalized n hn]
  constructor <;> linarith

/-- The defects whose integer chain-length excess is exactly `k`. -/
private def defectSlice (k : ℕ) : Set ℝ :=
  {d | ∃ n : ℕ, 0 < n ∧ k = l n - Nat.log 2 n ∧ d = additionChainDefect n}

example : (0 : ℝ) ∈ defectSlice 0 := by
  refine ⟨1, by decide, ?_, ?_⟩
  · simp [l_one]
  · simp [additionChainDefect, l_one]

private theorem defectSlice_isWF (k : ℕ) : (defectSlice k).IsWF := by
  let K := 2 ^ (4 * k)
  let U : Set ℝᵒᵈ := {x | x ∈ Set.range (fun t : Fin K → WithTop ℕ =>
    (∑ i, dyadicTerm (t i) : ℝᵒᵈ)) ∧ 0 < OrderDual.ofDual x}
  let f : ℝᵒᵈ → ℝ := fun x => (k : ℝ) - Real.logb 2 (OrderDual.ofDual x)
  have hU : U.IsPWO := (tuple_sums_pwo K).mono (fun _ hx => hx.1)
  have hf : MonotoneOn f U := by
    intro x hx y hy hxy
    apply sub_le_sub_left
    exact (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hy.2 hx.2).2 hxy
  have himage : (f '' U).IsWF := (hU.image_of_monotoneOn hf).isWF
  apply himage.mono
  intro d hd
  obtain ⟨n, hn, hk, hd⟩ := hd
  have hl := log_two_le_l n hn
  have hw : binaryWeight n ≤ K :=
    binaryWeight_le_two_pow_four_mul_of_l_le n (Nat.log 2 n) k
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)) (by omega)
  obtain ⟨t, ht⟩ := normalized_tuple n K hw
  refine ⟨OrderDual.toDual ((n : ℝ) / 2 ^ Nat.log 2 n), ?_, ?_⟩
  · exact ⟨⟨t, ht⟩, by dsimp; positivity⟩
  · change (k : ℝ) - Real.logb 2 ((n : ℝ) / 2 ^ Nat.log 2 n) = d
    rw [hd, defect_normalized n hn, ← hk]

/-- The set of all actual addition-chain defects is well-founded under `<`. -/
theorem additionChainDefects_isWF : additionChainDefects.IsWF := by
  classical
  change Set.WellFoundedOn additionChainDefects (· < ·)
  rw [Set.wellFoundedOn_iff, WellFounded.wellFounded_iff_has_min]
  intro A hA
  by_cases hAD : (A ∩ additionChainDefects).Nonempty
  · let P : ℕ → Prop := fun k => ∃ d, d ∈ A ∧ d ∈ defectSlice k
    have hP : ∃ k, P k := by
      obtain ⟨d, hdA, hdD⟩ := hAD
      obtain ⟨n, hn, hd⟩ := hdD
      refine ⟨l n - Nat.log 2 n, d, hdA, ⟨n, hn, rfl, hd⟩⟩
    let k := Nat.find hP
    have hk : P k := Nat.find_spec hP
    obtain ⟨d₀, hd₀A, hd₀S⟩ := hk
    let T : Set ℝ := A ∩ defectSlice k
    have hT : T.Nonempty := ⟨d₀, hd₀A, hd₀S⟩
    have hTwf : T.IsWF := (defectSlice_isWF k).mono Set.inter_subset_right
    let m := hTwf.min hT
    have hmT : m ∈ T := hTwf.min_mem hT
    refine ⟨m, hmT.1, ?_⟩
    intro x hxA hx
    obtain ⟨hxlt, hxD, hmD⟩ := hx
    obtain ⟨n, hn, hxn⟩ := hxD
    let j := l n - Nat.log 2 n
    have hjS : additionChainDefect n ∈ defectSlice j := ⟨n, hn, rfl, rfl⟩
    have hjP : P j := ⟨additionChainDefect n, hxn ▸ hxA, hjS⟩
    have hkj : k ≤ j := Nat.find_min' hP hjP
    by_cases hEq : k = j
    · have hxT : additionChainDefect n ∈ T := ⟨hxn ▸ hxA, hEq ▸ hjS⟩
      have hxm : additionChainDefect n < m := by simpa [hxn] using hxlt
      exact (hTwf.not_lt_min hT hxT) hxm
    · have hkj' : k < j := lt_of_le_of_ne hkj hEq
      have hkm : m ≤ (k : ℝ) := by
        obtain ⟨q, hq, hqk, hmq⟩ := hmT.2
        calc
          m = additionChainDefect q := hmq
          _ ≤ ((l q - Nat.log 2 q : ℕ) : ℝ) := (defect_interval q hq).2
          _ = (k : ℝ) := by rw [← hqk]
      have hjx : (j : ℝ) - 1 < additionChainDefect n :=
        (defect_interval n hn).1
      have hkjreal : (k : ℝ) ≤ (j : ℝ) - 1 := by
        have hkjNat : k + 1 ≤ j := (Nat.succ_le_iff).2 hkj'
        have hkjReal' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkjNat
        linarith
      have hmx : m < additionChainDefect n := lt_of_le_of_lt
        (hkm.trans hkjreal) hjx
      exact (not_lt_of_ge (le_of_lt hmx)) (by simpa [hxn] using hxlt)
  · obtain ⟨a, ha⟩ := hA
    refine ⟨a, ha, ?_⟩
    intro x hxA hx
    exact hAD ⟨a, ha, hx.2.2⟩

end NumberComplexity
