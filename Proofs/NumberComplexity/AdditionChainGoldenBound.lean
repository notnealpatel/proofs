import NumberComplexity.AdditionChain

/-!
# The golden-ratio bound for ascending addition chains

The classical two-coordinate invariant bounds a chain by a factor `2` for
value-doublings and a factor `φ` for every other step. Doublings are counted
from adjacent values, independently of the chosen addition witnesses.
This is the known global mechanism (cf. arXiv:2504.07332, lines 260–290),
not a novelty claim.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- Number of value-doubling indices `0 < k < s.length` in the ascending list.
The default value of `getD` is irrelevant on these indices and predecessors. -/
def ascDoublingCount (s : List ℕ) : ℕ :=
  ((Finset.range s.length).filter fun k =>
    0 < k ∧ s.getD k 0 = 2 * s.getD (k - 1) 0).card

example : ascDoublingCount [] = 0 := by decide
example : ascDoublingCount [1] = 0 := by decide
example : ascDoublingCount [1, 2, 3, 6, 12, 15] = 3 := by decide

private def prefixD (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k => 0 < k ∧ a k = 2 * a (k - 1)).card

example : prefixD (fun k => 2 ^ k) 4 = 3 := by decide

private theorem prefixD_one (a : ℕ → ℕ) : prefixD a 1 = 0 := by
  simp [prefixD, Finset.range_one]

private theorem prefixD_succ (a : ℕ → ℕ) (i : ℕ) :
    prefixD a (i + 2) = prefixD a (i + 1) +
      if a (i + 1) = 2 * a i then 1 else 0 := by
  unfold prefixD
  rw [show i + 2 = (i + 1) + 1 by omega, Finset.range_add_one, Finset.filter_insert]
  by_cases he : a (i + 1) = 2 * a i
  · simp [he, Finset.mem_filter, Finset.mem_range]
  · simp [he]

private theorem prefixD_le (a : ℕ → ℕ) (i : ℕ) : prefixD a (i + 1) ≤ i := by
  induction i with
  | zero => simp [prefixD_one]
  | succ i ih =>
    rw [prefixD_succ]
    split <;> omega

private theorem golden_core (a : ℕ → ℕ) (N : ℕ)
    (hzero : a 0 = 1) (hfirst : 0 < N → a 1 = 2)
    (hstep : ∀ i, 0 < i → i < N → a (i + 1) ≠ 2 * a i →
      a (i + 1) ≤ a i + a (i - 1)) :
    (a N : ℝ) ≤ 2 ^ prefixD a (N + 1) *
      Real.goldenRatio ^ (N - prefixD a (N + 1)) := by
  let φ := Real.goldenRatio
  have hp : 0 < φ := Real.goldenRatio_pos
  have hs : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  have ht : φ < 2 := Real.goldenRatio_lt_two
  have hinv : ∀ i, i + 1 ≤ N →
      (a (i + 1) : ℝ) ≤ 2 ^ prefixD a (i + 2) * φ ^ (i + 1 - prefixD a (i + 2)) ∧
      φ * a i ≤ 2 ^ prefixD a (i + 2) * φ ^ (i + 1 - prefixD a (i + 2)) := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hf : a 1 = 2 := hfirst (by omega)
      have hd : prefixD a 2 = 1 := by
        rw [prefixD_succ, prefixD_one, hzero, hf]
        norm_num
      simp only [hd, hf, hzero, pow_one, Nat.sub_self, pow_zero, mul_one,
        Nat.cast_ofNat, Nat.cast_one]
      exact ⟨le_rfl, by linarith⟩
    | succ i ih =>
      intro hi
      obtain ⟨ha, hb⟩ := ih (by omega)
      let d := prefixD a (i + 2)
      let q := i + 1 - d
      let B : ℝ := 2 ^ d * φ ^ q
      have ha' : (a (i + 1) : ℝ) ≤ B := ha
      have hb' : φ * a i ≤ B := hb
      have hdle : d ≤ i + 1 := prefixD_le a (i + 1)
      have hB : 0 ≤ B := le_of_lt (mul_pos (pow_pos (by norm_num) _) (pow_pos hp _))
      by_cases he : a (i + 2) = 2 * a (i + 1)
      · have hc : prefixD a (i + 3) = d + 1 := by
          rw [show i + 3 = (i + 1) + 2 by omega, prefixD_succ]
          simp [he, d]
        have hq : i + 2 - (d + 1) = q := by dsimp [q]; omega
        rw [show i + 1 + 1 + 1 = i + 3 by omega, hc, hq, pow_succ]
        have hnext : (a (i + 1 + 1) : ℝ) = 2 * a (i + 1) := by
          exact_mod_cast he
        constructor
        · rw [hnext]
          dsimp [B] at ha'
          nlinarith
        · dsimp [B] at ha' hB
          nlinarith [mul_nonneg (le_of_lt hp) (Nat.cast_nonneg (a (i + 1)))]
      · have hc : prefixD a (i + 3) = d := by
          rw [show i + 3 = (i + 1) + 2 by omega, prefixD_succ]
          simp [he, d]
        have hq : i + 2 - d = q + 1 := by dsimp [q]; omega
        have hn : (a (i + 2) : ℝ) ≤ a (i + 1) + a i := by
          exact_mod_cast hstep (i + 1) (by omega) (by omega) he
        rw [show i + 1 + 1 + 1 = i + 3 by omega, hc, hq, pow_succ]
        have hmul : φ * (a (i + 2) : ℝ) ≤ φ ^ 2 * B := by
          nlinarith [mul_le_mul_of_nonneg_left hn (le_of_lt hp),
            mul_le_mul_of_nonneg_left ha' (le_of_lt hp)]
        constructor
        · have hid : φ ^ 2 * B = φ * (2 ^ d * (φ ^ q * φ)) := by dsimp [B]; ring
          rw [hid] at hmul
          exact (mul_le_mul_iff_right₀ hp).mp hmul
        · dsimp [B] at ha'
          nlinarith [mul_le_mul_of_nonneg_left ha' (le_of_lt hp)]
  cases N with
  | zero => simp [hzero, prefixD_one]
  | succ i => exact (hinv i le_rfl).1

/-- The classical global golden-ratio bound: an ascending addition chain with
`D` adjacent value-doublings has endpoint at most `2^D φ^(length-1-D)`.
The zero-step chain `[1]` is included, with bound exactly `1`. -/
theorem IsAscAddChain.le_two_pow_mul_goldenRatio_pow {n : ℕ} {s : List ℕ}
    (h : IsAscAddChain n s) :
    (n : ℝ) ≤ (2 : ℝ) ^ ascDoublingCount s *
      Real.goldenRatio ^ (s.length - 1 - ascDoublingCount s) := by
  let a : ℕ → ℕ := fun k => s.getD k 0
  let N := s.length - 1
  have hlen : 0 < s.length := List.length_pos_of_ne_nil h.ne_nil
  have hN : N + 1 = s.length := by dsimp [N]; omega
  have ha (k : ℕ) (hk : k < s.length) : a k = s.get ⟨k, hk⟩ := by
    exact List.getD_eq_getElem s 0 hk
  have hzero : a 0 = 1 := by
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp h.head_eq_one
    simp [a, ht]
  have hmono (j k : ℕ) (hjk : j ≤ k) (hk : k < s.length) : a j ≤ a k := by
    rw [ha j (by omega), ha k hk]
    exact h.sortedLT.strictMono_get.monotone (show (⟨j, by omega⟩ : Fin s.length) ≤ ⟨k, hk⟩ from hjk)
  have hfirst : 0 < N → a 1 = 2 := by
    intro hpos
    obtain ⟨j, k, hj, hk, he⟩ := h.get_eq_add ⟨1, by omega⟩ (by norm_num)
    change j.val < 1 at hj
    change k.val < 1 at hk
    have hj0 : j.val = 0 := by omega
    have hk0 : k.val = 0 := by omega
    have he' : a 1 = a j.val + a k.val := by
      rw [ha 1 (by omega), ha j.val j.isLt, ha k.val k.isLt]
      exact he
    rw [hj0, hk0, hzero] at he'
    exact he'
  have hstep : ∀ i, 0 < i → i < N → a (i + 1) ≠ 2 * a i →
      a (i + 1) ≤ a i + a (i - 1) := by
    intro i hi hiN hnd
    obtain ⟨j, k, hj, hk, he⟩ := h.get_eq_add ⟨i + 1, by omega⟩ (show 0 < i + 1 by omega)
    change j.val < i + 1 at hj
    change k.val < i + 1 at hk
    have he' : a (i + 1) = a j.val + a k.val := by
      rw [ha (i + 1) (by omega), ha j.val j.isLt, ha k.val k.isLt]
      exact he
    have hjle : a j.val ≤ a i := hmono j.val i (by omega) (by omega)
    have hkle : a k.val ≤ a i := hmono k.val i (by omega) (by omega)
    by_cases hji : j.val = i
    · by_cases hki : k.val = i
      · rw [hji, hki] at he'
        omega
      · have hprev : a k.val ≤ a (i - 1) := hmono k.val (i - 1) (by omega) (by omega)
        omega
    · have hprev : a j.val ≤ a (i - 1) := hmono j.val (i - 1) (by omega) (by omega)
      omega
  have hend : a N = n := by
    rw [ha N (by omega)]
    have hl := h.getLast_eq
    rw [List.getLast?_eq_some_getLast h.ne_nil, Option.some_inj,
      List.getLast_eq_getElem] at hl
    exact hl
  have hcount : prefixD a (N + 1) = ascDoublingCount s := by
    simp only [prefixD, ascDoublingCount, hN, a]
  have hb := golden_core a N hzero hfirst hstep
  rw [hend, hcount] at hb
  exact hb

example : IsAscAddChain 1 [1] := by decide
example : IsAscAddChain 15 [1, 2, 3, 6, 12, 15] := by decide
example : (15 : ℝ) ≤ (2 : ℝ) ^ ascDoublingCount [1, 2, 3, 6, 12, 15] *
    Real.goldenRatio ^ (6 - 1 - ascDoublingCount [1, 2, 3, 6, 12, 15]) :=
  (show IsAscAddChain 15 [1, 2, 3, 6, 12, 15] by decide).le_two_pow_mul_goldenRatio_pow

end NumberComplexity
