import NumberComplexity.AdditionChainGoldenBound
import NumberComplexity.KnuthStolarsky

set_option autoImplicit false

namespace NumberComplexity

private theorem weight_bit_false (n : ℕ) : binaryWeight (Nat.bit false n) = binaryWeight n := by
  simp [binaryWeight]

private theorem weight_bit_true (n : ℕ) : binaryWeight (Nat.bit true n) = binaryWeight n + 1 := by
  simp [binaryWeight]

private theorem weight_succ_le (n : ℕ) : binaryWeight (n + 1) ≤ binaryWeight n + 1 := by
  induction n using Nat.binaryRec with
  | zero => decide
  | bit b n ih =>
    cases b with
    | false =>
      rw [show Nat.bit false n + 1 = Nat.bit true n by simp [Nat.bit],
        weight_bit_true, weight_bit_false]
    | true =>
      rw [show Nat.bit true n + 1 = Nat.bit false (n + 1) by simp [Nat.bit]; omega,
        weight_bit_false, weight_bit_true]
      omega

/-- Binary weight is subadditive: carries cannot increase the total number of ones. -/
theorem binaryWeight_add_le (x y : ℕ) :
    binaryWeight (x + y) ≤ binaryWeight x + binaryWeight y := by
  induction x using Nat.binaryRec generalizing y with
  | zero => simp [binaryWeight]
  | bit b x ih =>
    induction y using Nat.binaryRec with
    | zero => simp [binaryWeight]
    | bit c y _ =>
      cases b <;> cases c
      · rw [show Nat.bit false x + Nat.bit false y = Nat.bit false (x + y) by simp [Nat.bit]; omega,
          weight_bit_false, weight_bit_false, weight_bit_false]
        exact ih y
      · rw [show Nat.bit false x + Nat.bit true y = Nat.bit true (x + y) by simp [Nat.bit]; omega,
          weight_bit_true, weight_bit_false, weight_bit_true]
        exact Nat.add_le_add_right (ih y) 1
      · rw [show Nat.bit true x + Nat.bit false y = Nat.bit true (x + y) by simp [Nat.bit]; omega,
          weight_bit_true, weight_bit_true, weight_bit_false]
        have h := ih y
        omega
      · rw [show Nat.bit true x + Nat.bit true y = Nat.bit false (x + (y + 1)) by simp [Nat.bit]; omega,
          weight_bit_false, weight_bit_true, weight_bit_true]
        have h := ih (y + 1)
        have hs := weight_succ_le y
        omega

example : binaryWeight (7 + 9) ≤ binaryWeight 7 + binaryWeight 9 := binaryWeight_add_le 7 9

private def weightPrefixD (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k => 0 < k ∧ a k = 2 * a (k - 1)).card

example : weightPrefixD (fun k => 2 ^ k) 4 = 3 := by decide

private theorem weightPrefixD_one (a : ℕ → ℕ) : weightPrefixD a 1 = 0 := by
  simp [weightPrefixD, Finset.range_one]

private theorem weightPrefixD_succ (a : ℕ → ℕ) (i : ℕ) :
    weightPrefixD a (i + 2) = weightPrefixD a (i + 1) +
      if a (i + 1) = 2 * a i then 1 else 0 := by
  unfold weightPrefixD
  rw [show i + 2 = (i + 1) + 1 by omega, Finset.range_add_one, Finset.filter_insert]
  by_cases he : a (i + 1) = 2 * a i
  · simp [he, Finset.mem_filter, Finset.mem_range]
  · simp [he]

private theorem weightPrefixD_le (a : ℕ → ℕ) (i : ℕ) : weightPrefixD a (i + 1) ≤ i := by
  induction i with
  | zero => simp [weightPrefixD_one]
  | succ i ih =>
    rw [weightPrefixD_succ]
    split <;> omega

private theorem weight_core (a : ℕ → ℕ) (N : ℕ) (hzero : a 0 = 1)
    (hstep : ∀ i, i < N → ∃ j k, j ≤ i ∧ k ≤ i ∧ a (i + 1) = a j + a k) :
    ∀ i, i ≤ N → ∀ k, k ≤ i →
      binaryWeight (a k) ≤ 2 ^ (i - weightPrefixD a (i + 1)) := by
  intro i
  induction i with
  | zero =>
    intro _ k hk
    have hk0 : k = 0 := by omega
    simp [hk0, hzero, weightPrefixD_one, binaryWeight]
  | succ i ih =>
    intro hi k hk
    have hold := ih (by omega)
    have hdle := weightPrefixD_le a i
    by_cases he : a (i + 1) = 2 * a i
    · have hc : weightPrefixD a (i + 2) = weightPrefixD a (i + 1) + 1 := by
        simp [weightPrefixD_succ, he]
      have hq : i + 1 - weightPrefixD a (i + 2) = i - weightPrefixD a (i + 1) := by
        omega
      rw [show i + 1 + 1 = i + 2 by omega, hq]
      by_cases hki : k = i + 1
      · rw [hki, he, show 2 * a i = Nat.bit false (a i) by simp [Nat.bit], weight_bit_false]
        exact hold i le_rfl
      · exact hold k (by omega)
    · have hc : weightPrefixD a (i + 2) = weightPrefixD a (i + 1) := by
        simp [weightPrefixD_succ, he]
      have hq : i + 1 - weightPrefixD a (i + 2) = (i - weightPrefixD a (i + 1)) + 1 := by
        omega
      rw [show i + 1 + 1 = i + 2 by omega, hq, pow_succ]
      by_cases hki : k = i + 1
      · obtain ⟨j, t, hj, ht, hadd⟩ := hstep i (by omega)
        rw [hki, hadd]
        calc binaryWeight (a j + a t)
            ≤ binaryWeight (a j) + binaryWeight (a t) := binaryWeight_add_le _ _
          _ ≤ 2 ^ (i - weightPrefixD a (i + 1)) * 2 := by
            have hjw := hold j hj
            have htw := hold t ht
            omega
      · have hkw := hold k (by omega)
        omega

/-- On an actual ascending chain, binary weight is at most `2^Q`, where
`Q` counts all adjacent current-maximum value nondoublings, not log-scale small steps. -/
theorem IsAscAddChain.binaryWeight_le_two_pow_nondoublings {n : ℕ} {s : List ℕ}
    (h : IsAscAddChain n s) :
    binaryWeight n ≤ 2 ^ (s.length - 1 - ascDoublingCount s) := by
  let a : ℕ → ℕ := fun k => s.getD k 0
  let N := s.length - 1
  have hlen : 0 < s.length := List.length_pos_of_ne_nil h.ne_nil
  have hN : N + 1 = s.length := by dsimp [N]; omega
  have ha (k : ℕ) (hk : k < s.length) : a k = s.get ⟨k, hk⟩ := by
    exact List.getD_eq_getElem s 0 hk
  have hzero : a 0 = 1 := by
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp h.head_eq_one
    simp [a, ht]
  have hstep : ∀ i, i < N → ∃ j k, j ≤ i ∧ k ≤ i ∧ a (i + 1) = a j + a k := by
    intro i hi
    obtain ⟨j, k, hj, hk, he⟩ := h.get_eq_add ⟨i + 1, by omega⟩ (show 0 < i + 1 by omega)
    refine ⟨j.val, k.val, by change j.val < i + 1 at hj; omega,
      by change k.val < i + 1 at hk; omega, ?_⟩
    rw [ha (i + 1) (by omega), ha j.val j.isLt, ha k.val k.isLt]
    exact he
  have hend : a N = n := by
    rw [ha N (by omega)]
    have hl := h.getLast_eq
    rw [List.getLast?_eq_some_getLast h.ne_nil, Option.some_inj,
      List.getLast_eq_getElem] at hl
    exact hl
  have hcount : weightPrefixD a (N + 1) = ascDoublingCount s := by
    simp only [weightPrefixD, ascDoublingCount, hN, a]
  have hb := weight_core a N hzero hstep N le_rfl N le_rfl
  rw [hend, hcount] at hb
  exact hb

example : IsAscAddChain 1 [1] := by decide
example : IsAscAddChain 15 [1, 2, 3, 6, 12, 15] := by decide
example : binaryWeight 15 ≤ 2 ^ (6 - 1 - ascDoublingCount [1, 2, 3, 6, 12, 15]) :=
  (show IsAscAddChain 15 [1, 2, 3, 6, 12, 15] by decide).binaryWeight_le_two_pow_nondoublings

private theorem golden_fourth_le (D Q : ℕ) :
    ((2 : ℝ) ^ D * Real.goldenRatio ^ Q) ^ 4 ≤ 2 ^ (4 * D + 3 * Q) := by
  have hphi : Real.goldenRatio ^ 4 ≤ (2 : ℝ) ^ 3 := by
    calc Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 := by ring
      _ = 3 * Real.goldenRatio + 2 := by
        rw [Real.goldenRatio_sq]
        nlinarith [Real.goldenRatio_sq]
      _ ≤ (2 : ℝ) ^ 3 := by linarith [Real.goldenRatio_lt_two]
  calc ((2 : ℝ) ^ D * Real.goldenRatio ^ Q) ^ 4
      = ((2 : ℝ) ^ 4) ^ D * (Real.goldenRatio ^ 4) ^ Q := by
        rw [mul_pow]
        simp only [← pow_mul]
        congr 1 <;> congr 1 <;> omega
    _ ≤ ((2 : ℝ) ^ 4) ^ D * ((2 : ℝ) ^ 3) ^ Q :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hphi Q) (by positivity)
    _ = (2 : ℝ) ^ (4 * D + 3 * Q) := by rw [← pow_mul, ← pow_mul, ← pow_add]

/-- A number reached in at most `m+r` additions and at least `2^m` has
binary weight at most `2^(4*r)`. Both chain estimates use one shortest
ascending chain; this is a coarse bound, not the Knuth–Stolarsky conjecture. -/
theorem binaryWeight_le_two_pow_four_mul_of_l_le (n m r : ℕ)
    (hm : 2 ^ m ≤ n) (hl : l n ≤ m + r) :
    binaryWeight n ≤ 2 ^ (4 * r) := by
  have hn : n ≠ 0 := by have hp := Nat.two_pow_pos m; omega
  obtain ⟨s, hs⟩ := exists_chainSteps_eq_lAsc hn
  have hsteps : s.val.length - 1 = l n := by
    simpa only [chainSteps, List.length_tail, ← l_eq_lAsc] using hs
  let N := s.val.length - 1
  let D := ascDoublingCount s.val
  let Q := N - D
  have hlen : 0 < s.val.length := List.length_pos_of_ne_nil s.property.ne_nil
  have hN : N + 1 = s.val.length := by dsimp [N]; omega
  have hd : D ≤ N := by
    have hc : weightPrefixD (fun k => s.val.getD k 0) (N + 1) = D := by
      simp only [weightPrefixD, ascDoublingCount, hN, D]
    rw [← hc]
    exact weightPrefixD_le _ N
  have hsum : D + Q = N := by dsimp [Q]; omega
  have hgold : (n : ℝ) ≤ (2 : ℝ) ^ D * Real.goldenRatio ^ Q :=
    s.property.le_two_pow_mul_goldenRatio_pow
  have hmR : (2 : ℝ) ^ m ≤ n := by exact_mod_cast hm
  have hfour : (2 : ℝ) ^ (4 * m) ≤ 2 ^ (4 * D + 3 * Q) := by
    calc (2 : ℝ) ^ (4 * m) = ((2 : ℝ) ^ m) ^ 4 := by
          rw [← pow_mul, Nat.mul_comm m 4]
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hmR 4
      _ ≤ ((2 : ℝ) ^ D * Real.goldenRatio ^ Q) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hgold 4
      _ ≤ (2 : ℝ) ^ (4 * D + 3 * Q) := golden_fourth_le D Q
  have hexp : 4 * m ≤ 4 * D + 3 * Q :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hfour
  have hbudget : N ≤ m + r := by dsimp [N]; omega
  have hQ : Q ≤ 4 * r := by omega
  calc binaryWeight n ≤ 2 ^ Q := s.property.binaryWeight_le_two_pow_nondoublings
    _ ≤ 2 ^ (4 * r) := Nat.pow_le_pow_right (by norm_num) hQ

example : 2 ^ 0 ≤ (1 : ℕ) ∧ l 1 ≤ 0 + 0 := by simp [l_one]
example : binaryWeight 1 ≤ 2 ^ (4 * 0) :=
  binaryWeight_le_two_pow_four_mul_of_l_le 1 0 0 (by decide) (by simp [l_one])
example : 2 ^ 3 ≤ (15 : ℕ) ∧ l 15 ≤ 3 + 2 := by
  exact ⟨by decide, l_le_of_isAddChain [15, 12, 6, 3, 2, 1] (by decide) rfl (by decide)⟩
example : binaryWeight 15 ≤ 2 ^ (4 * 2) :=
  binaryWeight_le_two_pow_four_mul_of_l_le 15 3 2 (by decide)
    (l_le_of_isAddChain [15, 12, 6, 3, 2, 1] (by decide) rfl (by decide))

end NumberComplexity
