import Combinatorics.SelfridgeLacampagneFamilyDigits

set_option autoImplicit false

namespace SelfridgeLacampagne

private theorem peel_initial (x u : Bool) (W : ℤ)
    (h : 4 * (if x then 1 else 0) + 16 * (if u then 1 else 0) + 3 * W = -5) :
    W = -(3 + 4 * (if u then 1 else 0)) := by
  cases x <;> cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

private theorem peel_pair (p x y u v : Bool) (T V W : ℤ)
    (h : 4 * ((if x then 1 else 0) + 3 * (if y then 1 else 0) + 9 * T) +
      16 * ((if u then 1 else 0) + 3 * (if v then 1 else 0) + 9 * V) + 9 * W =
        -(3 + 4 * (if p then 1 else 0))) :
    4 * T + 16 * V + W = -(3 + 4 * (if v then 1 else 0)) := by
  cases p <;> cases x <;> cases y <;> cases u <;> cases v <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

/-- At every odd column through `m`, peeling the genuine digits gives the exact
residual equation. Its small constant is the ordinary early carry information. -/
theorem sparse_encoding_odd_residual (L U : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5))
    (k : ℕ) (hk : 2 * k + 1 ≤ m) :
    4 * ternary01 (U.drop (2 * k + 1)) +
      16 * ternary01 ((L.map Bool.not).drop (2 * k + 1)) +
      4 * (3 : ℤ) ^ (m - (2 * k + 1)) * ternary01 (L.map Bool.not) =
        4 * (3 : ℤ) ^ (L.length - (2 * k + 1)) -
          (3 : ℤ) ^ (m - (2 * k + 1)) -
          (3 + 4 * (if (L.map Bool.not).getD (2 * k) false then 1 else 0)) := by
  have hn := sparse_encoding_length_lower L U m hm heq
  induction k with
  | zero =>
    have hS := ternary01_drop_step (L.map Bool.not) 0
    have hT := ternary01_drop_step U 0
    simp only [List.drop_zero, Nat.reduceAdd, Nat.reduceMul] at hS hT ⊢
    have hpm : (3 : ℤ) ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
    have hpn : (3 : ℤ) ^ L.length = 3 * 3 ^ (L.length - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ L.length)]
    rw [hpm, hpn] at heq
    have hp := peel_initial (U.getD 0 false) ((L.map Bool.not).getD 0 false)
      (4 * ternary01 (U.drop 1) + 16 * ternary01 ((L.map Bool.not).drop 1) +
        4 * (3 : ℤ) ^ (m - 1) * ternary01 (L.map Bool.not) -
        4 * (3 : ℤ) ^ (L.length - 1) + (3 : ℤ) ^ (m - 1))
      (by nlinarith [hS, hT, heq])
    linarith
  | succ k ih =>
    have hprev := ih (by omega)
    let i := 2 * k + 1
    have hi : i + 2 ≤ m := by dsimp [i]; omega
    have hS0 := ternary01_drop_step (L.map Bool.not) i
    have hS1 := ternary01_drop_step (L.map Bool.not) (i + 1)
    have hT0 := ternary01_drop_step U i
    have hT1 := ternary01_drop_step U (i + 1)
    have hpm : (3 : ℤ) ^ (m - i) = 9 * 3 ^ (m - (i + 2)) := by
      rw [show m - i = 2 + (m - (i + 2)) by omega, pow_add]
      norm_num
    have hpn : (3 : ℤ) ^ (L.length - i) = 9 * 3 ^ (L.length - (i + 2)) := by
      rw [show L.length - i = 2 + (L.length - (i + 2)) by omega, pow_add]
      norm_num
    have hprev' : 4 * ternary01 (U.drop i) +
        16 * ternary01 ((L.map Bool.not).drop i) +
        4 * (3 : ℤ) ^ (m - i) * ternary01 (L.map Bool.not) =
          4 * (3 : ℤ) ^ (L.length - i) - (3 : ℤ) ^ (m - i) -
          (3 + 4 * (if (L.map Bool.not).getD (2 * k) false then 1 else 0)) := hprev
    rw [hpm, hpn] at hprev'
    have hp := peel_pair ((L.map Bool.not).getD (2 * k) false)
      (U.getD i false) (U.getD (i + 1) false)
      ((L.map Bool.not).getD i false) ((L.map Bool.not).getD (i + 1) false)
      (ternary01 (U.drop (i + 2))) (ternary01 ((L.map Bool.not).drop (i + 2)))
      (4 * (3 : ℤ) ^ (m - (i + 2)) * ternary01 (L.map Bool.not) -
        4 * (3 : ℤ) ^ (L.length - (i + 2)) + (3 : ℤ) ^ (m - (i + 2)))
      (by nlinarith [hS0, hS1, hT0, hT1, hprev'])
    have hi2 : i + 2 = 2 * (k + 1) + 1 := by dsimp [i]; omega
    have hi1 : i + 1 = 2 * (k + 1) := by dsimp [i]; omega
    rw [hi2, hi1] at hp
    linarith

/-- At the delayed term's first column, the ordinary carry is exactly zero,
expressed as an exact equality of four genuine suffix values. -/
theorem sparse_encoding_middle_residual (L U : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (hodd : Odd m)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5)) :
    ternary01 (U.drop m) + ternary01 ((L.map Bool.not).drop m) +
      ternary01 ((L.map Bool.not).drop (m - 1)) + ternary01 (L.map Bool.not) =
        (3 : ℤ) ^ (L.length - m) - 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hi : 2 * k + 1 = m := by omega
  have hr := sparse_encoding_odd_residual L U m hm heq k (by omega)
  rw [hi] at hr
  have hidx : 2 * k = m - 1 := by omega
  rw [hidx] at hr
  simp only [Nat.sub_self, pow_zero, mul_one] at hr
  have hs := ternary01_drop_step (L.map Bool.not) (m - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hs
  omega

private theorem peel_late (t x y z : Bool) (W : ℤ)
    (h : (if t then 1 else 0) + (if x then 1 else 0) +
      (if y then 1 else 0) + (if z then 1 else 0) + 3 * W = -1) :
    W = -1 ∧ ¬ (z = y ∧ y = x) := by
  cases t <;> cases x <;> cases y <;> cases z <;>
    simp_all <;> omega

/-- Every later column retains zero carry, as an equality of suffix values. -/
theorem sparse_encoding_late_residual (L U : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (hodd : Odd m)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5))
    (j : ℕ) (hj : m + j ≤ L.length) :
    ternary01 (U.drop (m + j)) + ternary01 ((L.map Bool.not).drop (m + j)) +
      ternary01 ((L.map Bool.not).drop (m + j - 1)) +
      ternary01 ((L.map Bool.not).drop j) = (3 : ℤ) ^ (L.length - (m + j)) - 1 := by
  induction j with
  | zero => simpa using sparse_encoding_middle_residual L U m hm hodd heq
  | succ j ih =>
    have hr := ih (by omega)
    let i := m + j
    have hT := ternary01_drop_step U i
    have hS := ternary01_drop_step (L.map Bool.not) i
    have hP := ternary01_drop_step (L.map Bool.not) (i - 1)
    have hD := ternary01_drop_step (L.map Bool.not) j
    rw [Nat.sub_add_cancel (by dsimp [i]; omega : 1 ≤ i)] at hP
    have hpow : (3 : ℤ) ^ (L.length - i) = 3 * 3 ^ (L.length - (i + 1)) := by
      rw [← pow_succ', show L.length - (i + 1) + 1 = L.length - i by dsimp [i]; omega]
    have hr' : ternary01 (U.drop i) + ternary01 ((L.map Bool.not).drop i) +
        ternary01 ((L.map Bool.not).drop (i - 1)) + ternary01 ((L.map Bool.not).drop j) =
          (3 : ℤ) ^ (L.length - i) - 1 := hr
    rw [hpow] at hr'
    have hp := (peel_late (U.getD i false) ((L.map Bool.not).getD i false)
      ((L.map Bool.not).getD (i - 1) false) ((L.map Bool.not).getD j false)
      (ternary01 (U.drop (i + 1)) + ternary01 ((L.map Bool.not).drop (i + 1)) +
        ternary01 ((L.map Bool.not).drop i) + ternary01 ((L.map Bool.not).drop (j + 1)) -
        (3 : ℤ) ^ (L.length - (i + 1))) (by linarith [hT, hS, hP, hD, hr'])).1
    have hi : m + (j + 1) = i + 1 := by dsimp [i]; omega
    rw [hi, Nat.add_sub_cancel]
    linarith

/-- Every actual post-prefix column has a nonmonochromatic delayed/current/previous triple. -/
theorem sparse_encoding_nae (L U : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (hodd : Odd m)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5))
    (j : ℕ) (hj : j < L.length - m) :
    ¬ ((L.map Bool.not).getD j false = (L.map Bool.not).getD (j + m - 1) false ∧
      (L.map Bool.not).getD (j + m - 1) false = (L.map Bool.not).getD (j + m) false) := by
  have hr := sparse_encoding_late_residual L U m hm hodd heq j (by omega)
  let i := m + j
  have hT := ternary01_drop_step U i
  have hS := ternary01_drop_step (L.map Bool.not) i
  have hP := ternary01_drop_step (L.map Bool.not) (i - 1)
  have hD := ternary01_drop_step (L.map Bool.not) j
  rw [Nat.sub_add_cancel (by dsimp [i]; omega : 1 ≤ i)] at hP
  have hpow : (3 : ℤ) ^ (L.length - i) = 3 * 3 ^ (L.length - (i + 1)) := by
    rw [← pow_succ', show L.length - (i + 1) + 1 = L.length - i by dsimp [i]; omega]
  have hr' : ternary01 (U.drop i) + ternary01 ((L.map Bool.not).drop i) +
      ternary01 ((L.map Bool.not).drop (i - 1)) + ternary01 ((L.map Bool.not).drop j) =
        (3 : ℤ) ^ (L.length - i) - 1 := hr
  rw [hpow] at hr'
  have hp := (peel_late (U.getD i false) ((L.map Bool.not).getD i false)
    ((L.map Bool.not).getD (i - 1) false) ((L.map Bool.not).getD j false)
    (ternary01 (U.drop (i + 1)) + ternary01 ((L.map Bool.not).drop (i + 1)) +
      ternary01 ((L.map Bool.not).drop i) + ternary01 ((L.map Bool.not).drop (j + 1)) -
      (3 : ℤ) ^ (L.length - (i + 1))) (by linarith [hT, hS, hP, hD, hr'])).2
  simpa only [i, Nat.add_comm m j] using hp

end SelfridgeLacampagne
