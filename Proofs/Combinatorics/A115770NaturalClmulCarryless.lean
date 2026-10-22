/-
# A115770 — carryless multiplication and binary runs

Antti Karttunen (OEIS A115770, Dec 21 2025) conjectured that
`7*k = A048720(11,k)` iff `5*k = A048720(13,k)`, equivalently that rows
7 and 5 of A115872 coincide. A048720 is carryless base-2 multiplication.
The analogous conjecture in A115801 equates `9*k = A048720(25,k)` with
`15*k = A048720(19,k)`. These are the cases `m = 3, 4` of the general
equivalence below. Both solution sets are characterized by windows of
`m + 1` bits changing value at most once.

## Proof outline

With `E = k ⊕ 2k`, the identity `x + y = (x ⊕ y) + 2 (x ∧ y)` turns
`(2^m - 1) k = E ⊕ 2^m k` into the bitwise identity `E ∧ 2^m k = 2k ⊕ (k ∧ 2k)` and
`(2^(m-1) + 1) k = k ⊕ 2^(m-1) E` into `k ∧ 2^(m-1) E = 2^(m-1) (k ⊕ (k ∧ 2k))`. Both are
conditions on the window `kᵢ, …, kᵢ₋ₘ` at each position `i`. The first propagates the
"at most one change" invariant upward from the zero bits below position `0`; the second
propagates it downward from the zero bits above the top bit of `k`; conversely the
invariant implies both local conditions.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A115770NaturalClmulCarryless

/-- Carryless base-2 multiplication (OEIS A048720): the XOR of the shifts `k <<< i` over
the set bits `i` of `a`. Bits of `a` at positions `≥ a` vanish, so `List.range a` covers
every set bit. -/
def clmul (a k : ℕ) : ℕ :=
  (List.range a).foldl (fun acc i => if a.testBit i then acc ^^^ (k <<< i) else acc) 0

/-- `x ^^^ y + 2 * (x &&& y) = x + y`: addition is XOR plus doubled carries. -/
theorem xor_add_two_mul_and (x y : ℕ) : (x ^^^ y) + 2 * (x &&& y) = x + y := by
  induction x using Nat.binaryRec generalizing y with
  | zero => simp
  | bit a m ih =>
    rw [← Nat.bit_bodd_div2 y, Nat.xor_bit, Nat.land_bit]
    have hih := ih y.div2
    set_option linter.unusedSimpArgs false in
    cases a <;> cases y.bodd <;> simp only [Nat.bit_val, Bool.toNat, Bool.bne_true,
      Bool.bne_false, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      cond_true, cond_false] <;> omega

/-- If the bits of `y` are among those of `z`, then `x + y = z` iff `x = z ^^^ y`. -/
theorem add_eq_iff_eq_xor_of_and_eq {x y z : ℕ} (hyz : z &&& y = y) :
    x + y = z ↔ x = z ^^^ y := by
  have h := xor_add_two_mul_and z y
  rw [hyz] at h
  omega

/-- The bit `i` of `k <<< (n + 1)` at position `i + 1` is the bit of `k <<< n` at `i`. -/
theorem testBit_shiftLeft_succ_succ (k n i : ℕ) :
    (k <<< (n + 1)).testBit (i + 1) = (k <<< n).testBit i := by
  simp only [Nat.testBit_shiftLeft]
  by_cases h : n ≤ i
  · have h' : n + 1 ≤ i + 1 := by omega
    simp [h, h', show i + 1 - (n + 1) = i - n by omega]
  · have h' : ¬ n + 1 ≤ i + 1 := by omega
    simp [h, h']

/-- `k <<< (n + 1)` has bit `0` clear. -/
theorem testBit_shiftLeft_succ_zero (k n : ℕ) : (k <<< (n + 1)).testBit 0 = false := by
  simp

/-- `k <<< n` has no set bits at positions `≥ k + n`. -/
theorem testBit_shiftLeft_of_le (k n i : ℕ) (h : k + n ≤ i) : (k <<< n).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  calc k <<< n = k * 2 ^ n := Nat.shiftLeft_eq k n
    _ < 2 ^ k * 2 ^ n := Nat.mul_lt_mul_of_pos_right hk (by positivity)
    _ = 2 ^ (k + n) := (pow_add 2 k n).symm
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h

/-- `clmul 11 k = k ⊕ 2k ⊕ 8k`, since `11 = 1011₂`. -/
theorem clmul_eleven (k : ℕ) : clmul 11 k = k ^^^ (k <<< 1) ^^^ (k <<< 3) := by
  have hb : (List.range 11).map (Nat.testBit 11) =
      [true, true, false, true, false, false, false, false, false, false, false] := by decide
  simp only [clmul, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq] at hb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hb
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, if_true, if_false, Bool.false_eq_true,
    Nat.zero_xor, Nat.shiftLeft_zero]

/-- `clmul 13 k = k ⊕ 4k ⊕ 8k`, since `13 = 1101₂`. -/
theorem clmul_thirteen (k : ℕ) : clmul 13 k = k ^^^ (k <<< 2) ^^^ (k <<< 3) := by
  have hb : (List.range 13).map (Nat.testBit 13) =
      [true, false, true, true, false, false, false, false, false, false, false, false,
        false] := by decide
  simp only [clmul, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq] at hb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := hb
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, if_true, if_false,
    Bool.false_eq_true, Nat.zero_xor, Nat.shiftLeft_zero]

/-! ## Reduction of the carryless products to three shifts -/

/-- Splitting the guard `s < n + 1` into `s < n` and `n = s`, XOR-wise. -/
theorem ite_lt_succ_eq_xor (s n x : ℕ) :
    (if s < n + 1 then x else 0) = (if s < n then x else 0) ^^^ (if n = s then x else 0) := by
  by_cases h1 : s < n
  · simp [h1, show s < n + 1 by omega, show n ≠ s by omega]
  · by_cases h2 : n = s
    · simp [h2]
    · simp [h1, h2, show ¬ s < n + 1 by omega]

/-- The partial carryless product over the bits `< n` of an `a` with exactly three set bits
`p < q < r`. -/
theorem foldl_range_of_three_bits (a k p q r : ℕ) (hpq : p < q) (hqr : q < r)
    (ha : ∀ j, a.testBit j = true ↔ (j = p ∨ j = q ∨ j = r)) (n : ℕ) :
    (List.range n).foldl (fun acc i => if a.testBit i then acc ^^^ (k <<< i) else acc) 0 =
      (if p < n then k <<< p else 0) ^^^ (if q < n then k <<< q else 0) ^^^
        (if r < n then k <<< r else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      ite_lt_succ_eq_xor p, ite_lt_succ_eq_xor q, ite_lt_succ_eq_xor r]
    by_cases hp : n = p
    · subst hp
      simp only [(ha n).mpr (Or.inl rfl), if_true, show n ≠ q by omega, show n ≠ r by omega,
        if_false, Nat.xor_zero]
      ac_rfl
    by_cases hq : n = q
    · subst hq
      simp only [(ha n).mpr (Or.inr (Or.inl rfl)), if_true, hp, show n ≠ r by omega,
        if_false, Nat.xor_zero]
      ac_rfl
    by_cases hr : n = r
    · subst hr
      simp only [(ha n).mpr (Or.inr (Or.inr rfl)), if_true, hp, hq, if_false, Nat.xor_zero]
      ac_rfl
    have hn : a.testBit n = false := by
      rcases hb : a.testBit n with _ | _
      · rfl
      · rcases (ha n).mp hb with h | h | h <;> contradiction
    simp only [hn, hp, hq, hr, Bool.false_eq_true, if_false, Nat.xor_zero]

/-- Carryless product by an `a` with exactly three set bits `p < q < r`. -/
theorem clmul_of_three_bits (a k p q r : ℕ) (hpq : p < q) (hqr : q < r)
    (ha : ∀ j, a.testBit j = true ↔ (j = p ∨ j = q ∨ j = r)) :
    clmul a k = (k <<< p) ^^^ (k <<< q) ^^^ (k <<< r) := by
  have hra : r < a := by
    by_contra hcon
    have hbit : a.testBit r = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have htrue := (ha r).mpr (Or.inr (Or.inr rfl))
    rw [hbit] at htrue
    exact Bool.false_ne_true htrue
  rw [clmul, foldl_range_of_three_bits a k p q r hpq hqr ha a]
  simp [show p < a by omega, show q < a by omega, hra]

/-- The set bits of `3` are `0` and `1`. -/
theorem testBit_three_iff (j : ℕ) : (3 : ℕ).testBit j = true ↔ (j = 0 ∨ j = 1) := by
  rcases j with _ | _ | j
  · decide
  · decide
  · have h3 : (3 : ℕ) < 2 ^ (j + 2) := by
      calc (3 : ℕ) < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [Nat.testBit_lt_two_pow h3]

/-- For `m ≥ 2` the set bits of `2^m + 3` are `0`, `1`, `m`. -/
theorem testBit_two_pow_add_three_iff (m : ℕ) (hm : 2 ≤ m) (j : ℕ) :
    (2 ^ m + 3).testBit j = true ↔ (j = 0 ∨ j = 1 ∨ j = m) := by
  have h3 : 3 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm :
    2 ^ 2 ≤ 2 ^ m)
  rw [show 2 ^ m + 3 = 2 ^ m * 1 + 3 by ring, Nat.testBit_two_pow_mul_add 1 h3 j]
  split_ifs with hj
  · rw [testBit_three_iff]
    omega
  · rw [Nat.testBit_one_eq_true_iff_self_eq_zero]
    omega

/-- For `m ≥ 2` the set bits of `2^m + 2^(m-1) + 1` are `0`, `m - 1`, `m`. -/
theorem testBit_two_pow_add_two_pow_add_one_iff (m : ℕ) (hm : 2 ≤ m) (j : ℕ) :
    (2 ^ m + 2 ^ (m - 1) + 1).testBit j = true ↔ (j = 0 ∨ j = m - 1 ∨ j = m) := by
  have h1 : 1 < 2 ^ (m - 1) := Nat.one_lt_two_pow (by omega)
  have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [show 2 ^ m + 2 ^ (m - 1) + 1 = 2 ^ (m - 1) * 3 + 1 by rw [hpow]; ring,
    Nat.testBit_two_pow_mul_add 3 h1 j]
  split_ifs with hj
  · rw [Nat.testBit_one_eq_true_iff_self_eq_zero]
    omega
  · rw [testBit_three_iff]
    omega

/-- The window of bits `kᵢ, kᵢ₋₁, …` at position `i`: entry `n` is bit `i - n` of `k`, read
as `false` when `n > i` (bit `i` of `k <<< n`). -/
def window (k i n : ℕ) : Bool := (k <<< n).testBit i

/-- The first `m + 1` entries of `w` change value at most once: no pattern `x, y, x` with
`y ≠ x` occurs at positions `p ≤ q ≤ r ≤ m`. -/
def AtMostOneChange (m : ℕ) (w : ℕ → Bool) : Prop :=
  ∀ p q r, p ≤ q → q ≤ r → r ≤ m → w p = w r → w q = w p

/-- General-`m` arithmetic-to-bitwise bridge for `(2^m - 1) k = clmul (2^m + 3) k`. -/
theorem two_pow_sub_one_mul_eq_clmul_iff (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (2 ^ m - 1) * k = clmul (2 ^ m + 3) k ↔
      ∀ i, ((window k i 0 ^^ window k i 1) && window k i m) =
        (window k i 1 ^^ (window k i 0 && window k i 1)) := by
  rw [clmul_of_three_bits _ k 0 1 m (by omega) (by omega) (testBit_two_pow_add_three_iff m hm),
    Nat.shiftLeft_zero]
  have hmul : (2 ^ m - 1) * k + k = k <<< m := by
    rw [← add_one_mul, Nat.sub_add_cancel Nat.one_le_two_pow, Nat.shiftLeft_eq, mul_comm]
  have hs1 : k <<< 1 = 2 * k := by rw [Nat.shiftLeft_eq]; ring
  have h1 := xor_add_two_mul_and k (k <<< 1)
  have h2 := xor_add_two_mul_and (k ^^^ (k <<< 1)) (k <<< m)
  have hsub : (k <<< 1) &&& (k &&& (k <<< 1)) = k &&& (k <<< 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases k.testBit i <;> cases (k <<< 1).testBit i <;> rfl
  have hstep : (2 ^ m - 1) * k = (k ^^^ (k <<< 1)) ^^^ (k <<< m) ↔
      ((k ^^^ (k <<< 1)) &&& (k <<< m)) + (k &&& (k <<< 1)) = k <<< 1 := by
    constructor <;> intro h <;> omega
  rw [hstep, add_eq_iff_eq_xor_of_and_eq hsub]
  constructor
  · intro h i
    have hi := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_xor] at hi
    simp only [window, Nat.shiftLeft_zero]
    exact hi
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := h i
    simp only [window, Nat.shiftLeft_zero] at hi
    simp only [Nat.testBit_and, Nat.testBit_xor]
    exact hi

/-- General-`m` arithmetic-to-bitwise bridge for
`(2^(m-1) + 1) k = clmul (2^m + 2^(m-1) + 1) k`. -/
theorem two_pow_pred_add_one_mul_eq_clmul_iff (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (2 ^ (m - 1) + 1) * k = clmul (2 ^ m + 2 ^ (m - 1) + 1) k ↔
      ∀ i, (window k i 0 && (window k i (m - 1) ^^ window k i m)) =
        (window k i (m - 1) ^^ (window k i (m - 1) && window k i m)) := by
  rw [clmul_of_three_bits _ k 0 (m - 1) m (by omega) (by omega)
    (testBit_two_pow_add_two_pow_add_one_iff m hm), Nat.shiftLeft_zero, Nat.xor_assoc]
  have hmul : (2 ^ (m - 1) + 1) * k = (k <<< (m - 1)) + k := by
    rw [Nat.shiftLeft_eq]; ring
  have hsm : k <<< m = 2 * (k <<< (m - 1)) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, show m = (m - 1) + 1 by omega, pow_succ]
    simp only [show m - 1 + 1 - 1 = m - 1 by omega]
    ring
  have h1 := xor_add_two_mul_and k ((k <<< (m - 1)) ^^^ (k <<< m))
  have h2 := xor_add_two_mul_and (k <<< (m - 1)) (k <<< m)
  have hsub : (k <<< (m - 1)) &&& ((k <<< (m - 1)) &&& (k <<< m)) =
      (k <<< (m - 1)) &&& (k <<< m) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases (k <<< (m - 1)).testBit i <;> cases (k <<< m).testBit i <;> rfl
  have hstep : (2 ^ (m - 1) + 1) * k = k ^^^ ((k <<< (m - 1)) ^^^ (k <<< m)) ↔
      (k &&& ((k <<< (m - 1)) ^^^ (k <<< m))) + ((k <<< (m - 1)) &&& (k <<< m)) =
        k <<< (m - 1) := by
    constructor <;> intro h <;> omega
  rw [hstep, add_eq_iff_eq_xor_of_and_eq hsub]
  constructor
  · intro h i
    have hi := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_xor] at hi
    simp only [window, Nat.shiftLeft_zero]
    exact hi
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := h i
    simp only [window, Nat.shiftLeft_zero] at hi
    simp only [Nat.testBit_and, Nat.testBit_xor]
    exact hi

/-- A window whose entries `1, …, m` are `false` changes at most once. -/
theorem atMostOneChange_of_false_of_pos (m : ℕ) (w : ℕ → Bool)
    (hw : ∀ n, 1 ≤ n → n ≤ m → w n = false) : AtMostOneChange m w := by
  intro p q r hpq hqr hrm hpr
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [show p = 0 by omega]
  · rw [hw q hq (by omega)]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      rw [hpr, hw r (by omega) hrm]
    · rw [hw p hp (by omega)]

/-- Forward step: prepending a new top bit `w' 0` to a window `w` with at most one change keeps
at most one change, provided the local condition of `(2^m - 1) k = clmul (2^m + 3) k` holds at
the new window. -/
theorem atMostOneChange_step_up (m : ℕ) (hm : 1 ≤ m) (w w' : ℕ → Bool)
    (hsh : ∀ n, w' (n + 1) = w n) (hG : AtMostOneChange m w)
    (hA : ((w' 0 ^^ w' 1) && w' m) = (w' 1 ^^ (w' 0 && w' 1))) :
    AtMostOneChange m w' := by
  intro p q r hpq hqr hrm hpr
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [show p = 0 by omega]
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [hsh q']
  rw [hsh r'] at hpr
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    by_cases he : w' 0 = w 0
    · rw [he] at hpr ⊢
      exact hG 0 q' r' (by omega) (by omega) (by omega) hpr
    · exfalso
      have hw1 : w' 1 = w 0 := hsh 0
      have hwm : w' m = w (m - 1) := by
        have hs := hsh (m - 1)
        rwa [Nat.sub_add_cancel hm] at hs
      rw [hw1, hwm] at hA
      have hend : w (m - 1) = w 0 := by
        revert hA he
        cases w' 0 <;> cases w 0 <;> cases w (m - 1) <;> decide
      have hmid := hG 0 r' (m - 1) (by omega) (by omega) (by omega) hend.symm
      exact he (hpr.trans hmid)
  · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [hsh p'] at hpr ⊢
    exact hG p' q' r' (by omega) (by omega) (by omega) hpr

/-- Backward step: appending a new bottom entry `w m` to the window `w' = (·, w 0, …, w (m-1))`
with at most one change keeps at most one change, provided the local condition of
`(2^(m-1) + 1) k = clmul (2^m + 2^(m-1) + 1) k` holds at `w`. -/
theorem atMostOneChange_step_down (m : ℕ) (hm : 1 ≤ m) (w w' : ℕ → Bool)
    (hsh : ∀ n, w' (n + 1) = w n) (hG' : AtMostOneChange m w')
    (hB : (w 0 && (w (m - 1) ^^ w m)) = (w (m - 1) ^^ (w (m - 1) && w m))) :
    AtMostOneChange m w := by
  have hsub : ∀ p q r, p ≤ q → q ≤ r → r ≤ m - 1 → w p = w r → w q = w p := by
    intro p q r hpq hqr hrm hpr
    have hs := hG' (p + 1) (q + 1) (r + 1) (by omega) (by omega) (by omega)
      (by rw [hsh, hsh]; exact hpr)
    rwa [hsh, hsh] at hs
  intro p q r hpq hqr hrm hpr
  by_cases hr : r ≤ m - 1
  · exact hsub p q r hpq hqr hr hpr
  obtain rfl : r = m := by omega
  by_cases hq : q = r
  · subst hq
    exact hpr.symm
  by_cases hc : w (r - 1) = w r
  · exact hsub p q (r - 1) hpq (by omega) le_rfl (hpr.trans hc.symm)
  · exfalso
    have h0 : w 0 = w (r - 1) := by
      revert hB hc
      cases w 0 <;> cases w (r - 1) <;> cases w r <;> decide
    have hp := hsub 0 p (r - 1) (by omega) (by omega) le_rfl h0
    exact hc (h0.symm.trans (hp.symm.trans hpr))

/-- A window with at most one change satisfies the local condition of
`(2^m - 1) k = clmul (2^m + 3) k`. -/
theorem okA_of_atMostOneChange (m : ℕ) (hm : 1 ≤ m) (w : ℕ → Bool)
    (hG : AtMostOneChange m w) : ((w 0 ^^ w 1) && w m) = (w 1 ^^ (w 0 && w 1)) := by
  have h := hG 0 1 m (by omega) hm le_rfl
  revert h
  cases w 0 <;> cases w 1 <;> cases w m <;> decide

/-- A window with at most one change satisfies the local condition of
`(2^(m-1) + 1) k = clmul (2^m + 2^(m-1) + 1) k`. -/
theorem okB_of_atMostOneChange (m : ℕ) (w : ℕ → Bool)
    (hG : AtMostOneChange m w) :
    (w 0 && (w (m - 1) ^^ w m)) = (w (m - 1) ^^ (w (m - 1) && w m)) := by
  have h := hG 0 (m - 1) m (by omega) (by omega) le_rfl
  revert h
  cases w 0 <;> cases w (m - 1) <;> cases w m <;> decide

/-- Upward induction: the local `(2^m - 1)`-condition at every position forces every window to
change at most once. -/
theorem atMostOneChange_of_okA (m : ℕ) (hm : 1 ≤ m) (k : ℕ)
    (h : ∀ i, ((window k i 0 ^^ window k i 1) && window k i m) =
      (window k i 1 ^^ (window k i 0 && window k i 1))) :
    ∀ i, AtMostOneChange m (window k i) := by
  intro i
  induction i with
  | zero =>
    apply atMostOneChange_of_false_of_pos
    intro n hn _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact testBit_shiftLeft_succ_zero k n'
  | succ i ih =>
    exact atMostOneChange_step_up m hm (window k i) (window k (i + 1))
      (fun n => testBit_shiftLeft_succ_succ k n i) ih (h (i + 1))

/-- Downward induction: the local `(2^(m-1) + 1)`-condition at every position forces every
window to change at most once. -/
theorem atMostOneChange_of_okB (m : ℕ) (hm : 1 ≤ m) (k : ℕ)
    (h : ∀ i, (window k i 0 && (window k i (m - 1) ^^ window k i m)) =
      (window k i (m - 1) ^^ (window k i (m - 1) && window k i m))) :
    ∀ i, AtMostOneChange m (window k i) := by
  have key : ∀ j i, k + m ≤ i + j → AtMostOneChange m (window k i) := by
    intro j
    induction j with
    | zero =>
      intro i hi
      apply atMostOneChange_of_false_of_pos
      intro n _ hnm
      exact testBit_shiftLeft_of_le k n i (by omega)
    | succ j ih =>
      intro i hi
      exact atMostOneChange_step_down m hm (window k i) (window k (i + 1))
        (fun n => testBit_shiftLeft_succ_succ k n i) (ih (i + 1) (by omega)) (h i)
  intro i
  exact key (k + m) i (by omega)

/-- **Characterization, general `m ≥ 2`.** `(2^m - 1) k = clmul (2^m + 3) k` iff every window
`kᵢ, kᵢ₋₁, …, kᵢ₋ₘ` of `m + 1` consecutive bits of `k` (bits at negative positions read as `0`)
changes value at most once; equivalently every maximal run of `1`s of `k` has length `≥ m` and
every run of `0`s between two `1`s has length `≥ m`. -/
theorem two_pow_sub_one_mul_eq_clmul_iff_atMostOneChange (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (2 ^ m - 1) * k = clmul (2 ^ m + 3) k ↔ ∀ i, AtMostOneChange m (window k i) := by
  rw [two_pow_sub_one_mul_eq_clmul_iff m hm]
  exact ⟨atMostOneChange_of_okA m (by omega) k,
    fun h i => okA_of_atMostOneChange m (by omega) (window k i) (h i)⟩

/-- **Characterization, general `m ≥ 2`.** `(2^(m-1) + 1) k = clmul (2^m + 2^(m-1) + 1) k` iff
every window of `m + 1` consecutive bits of `k` changes value at most once. -/
theorem two_pow_pred_add_one_mul_eq_clmul_iff_atMostOneChange (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (2 ^ (m - 1) + 1) * k = clmul (2 ^ m + 2 ^ (m - 1) + 1) k ↔
      ∀ i, AtMostOneChange m (window k i) := by
  rw [two_pow_pred_add_one_mul_eq_clmul_iff m hm]
  exact ⟨atMostOneChange_of_okB m (by omega) k,
    fun h i => okB_of_atMostOneChange m (window k i) (h i)⟩

/-- **The stronger form, general `m ≥ 2`.** For every `k`,
`(2^m - 1) k = clmul (2^m + 3) k` iff `(2^(m-1) + 1) k = clmul (2^m + 2^(m-1) + 1) k`. The case
`m = 3` is A115770 (Karttunen's conjecture), `m = 4` is the analogous row pair for A115801. -/
theorem two_pow_sub_one_mul_eq_clmul_iff_two_pow_pred_add_one_mul_eq_clmul (m : ℕ)
    (hm : 2 ≤ m) (k : ℕ) :
    (2 ^ m - 1) * k = clmul (2 ^ m + 3) k ↔
      (2 ^ (m - 1) + 1) * k = clmul (2 ^ m + 2 ^ (m - 1) + 1) k := by
  rw [two_pow_sub_one_mul_eq_clmul_iff_atMostOneChange m hm,
    two_pow_pred_add_one_mul_eq_clmul_iff_atMostOneChange m hm]

/-! ## The conjectures -/

/-- **Karttunen's conjecture for A115770 (Dec 21 2025).** For every natural `k`,
`7 * k = A048720(11, k)` iff `5 * k = A048720(13, k)`; equivalently rows 7 and 5 of A115872
coincide. This is the case `m = 3` of
`two_pow_sub_one_mul_eq_clmul_iff_two_pow_pred_add_one_mul_eq_clmul`. -/
theorem seven_mul_eq_clmul_eleven_iff_five_mul_eq_clmul_thirteen (k : ℕ) :
    7 * k = clmul 11 k ↔ 5 * k = clmul 13 k := by
  have h := two_pow_sub_one_mul_eq_clmul_iff_two_pow_pred_add_one_mul_eq_clmul 3
    (by norm_num) k
  rwa [show (2 : ℕ) ^ 3 + 2 ^ (3 - 1) + 1 = 13 by norm_num, show (2 : ℕ) ^ 3 - 1 = 7 by norm_num,
    show (2 : ℕ) ^ 3 + 3 = 11 by norm_num, show (2 : ℕ) ^ (3 - 1) + 1 = 5 by norm_num] at h

/-- **Characterization of A115770.** `7 * k = A048720(11, k)` iff every window of four
consecutive bits `kᵢ, kᵢ₋₁, kᵢ₋₂, kᵢ₋₃` of `k` (negative positions read as `0`) changes value at
most once, i.e. every maximal run of `1`s in binary `k` has length `≥ 3` and every run of `0`s
between two `1`s has length `≥ 3`. -/
theorem seven_mul_eq_clmul_eleven_iff_atMostOneChange (k : ℕ) :
    7 * k = clmul 11 k ↔ ∀ i, AtMostOneChange 3 (window k i) := by
  have h := two_pow_sub_one_mul_eq_clmul_iff_atMostOneChange 3 (by norm_num) k
  rwa [show (2 : ℕ) ^ 3 - 1 = 7 by norm_num, show (2 : ℕ) ^ 3 + 3 = 11 by norm_num] at h

/-- **Karttunen's conjecture for A115801 (Dec 21 2025).** For every natural `k`, `9 * k = A048720(25, k)` iff
`15 * k = A048720(19, k)`. This is the case `m = 4` of
`two_pow_sub_one_mul_eq_clmul_iff_two_pow_pred_add_one_mul_eq_clmul`. -/
theorem nine_mul_eq_clmul_twentyfive_iff_fifteen_mul_eq_clmul_nineteen (k : ℕ) :
    9 * k = clmul 25 k ↔ 15 * k = clmul 19 k := by
  have h := two_pow_sub_one_mul_eq_clmul_iff_two_pow_pred_add_one_mul_eq_clmul 4
    (by norm_num) k
  rw [show (2 : ℕ) ^ 4 + 2 ^ (4 - 1) + 1 = 25 by norm_num, show (2 : ℕ) ^ 4 - 1 = 15 by norm_num,
    show (2 : ℕ) ^ 4 + 3 = 19 by norm_num, show (2 : ℕ) ^ (4 - 1) + 1 = 9 by norm_num] at h
  exact h.symm

/-! ## Examples -/

-- `clmul` agrees with the first 91 terms (antidiagonals 0..12) of the A048720 table.
example : ((List.range 13).flatMap fun n => (List.range (n + 1)).map fun i => clmul i (n - i)) =
    [0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 3, 4, 3, 0, 0, 4, 6, 6, 4, 0, 0, 5, 8, 5, 8, 5, 0, 0, 6,
      10, 12, 12, 10, 6, 0, 0, 7, 12, 15, 16, 15, 12, 7, 0, 0, 8, 14, 10, 20, 20, 10, 14, 8, 0,
      0, 9, 16, 9, 24, 17, 24, 9, 16, 9, 0, 0, 10, 18, 24, 28, 30, 30, 28, 24, 18, 10, 0, 0, 11,
      20, 27, 32, 27, 20, 27, 32, 27, 20, 11, 0] := by
  decide

-- The defining predicate of A115770 reproduces the listed terms below `512`.
set_option maxRecDepth 20000 in
example : (List.range 512).filter (fun k => 7 * k == clmul 11 k) =
    [0, 7, 14, 15, 28, 30, 31, 56, 60, 62, 63, 112, 120, 124, 126, 127, 224, 240, 248, 252,
      254, 255, 448, 455, 480, 496, 504, 508, 510, 511] := by
  decide

-- The conjectured alternative predicate gives the same terms below `512`.
set_option maxRecDepth 20000 in
example : (List.range 512).filter (fun k => 5 * k == clmul 13 k) =
    [0, 7, 14, 15, 28, 30, 31, 56, 60, 62, 63, 112, 120, 124, 126, 127, 224, 240, 248, 252,
      254, 255, 448, 455, 480, 496, 504, 508, 510, 511] := by
  decide

-- The defining predicate of A115801 reproduces the listed terms below `512`.
set_option maxRecDepth 20000 in
example : (List.range 512).filter (fun k => 9 * k == clmul 25 k) =
    [0, 15, 30, 31, 60, 62, 63, 120, 124, 126, 127, 240, 248, 252, 254, 255, 480, 496, 504,
      508, 510, 511] := by
  decide

-- Both sides of the conjecture are nontrivial: true at `k = 7`, false at `k = 5`.
example : 7 * 7 = clmul 11 7 ∧ 5 * 7 = clmul 13 7 := by decide
example : 7 * 5 ≠ clmul 11 5 ∧ 5 * 5 ≠ clmul 13 5 := by decide

-- `window k i` lists `kᵢ, kᵢ₋₁, …` with `0` below position `0`: for `k = 5 = 101₂`, `i = 2`.
example : (List.range 4).map (window 5 2) = [true, false, true, false] := by decide

-- `AtMostOneChange` is not vacuous: the window `1, 0, 1` of `k = 5` violates it.
example : ¬ AtMostOneChange 3 (window 5 2) := by
  intro h
  have h' := h 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by decide)
  revert h'
  decide

-- The general theorem's hypotheses are jointly satisfiable (`m = 3`, `k = 7`, both sides true).
example : (2 ^ 3 - 1) * 7 = clmul (2 ^ 3 + 3) 7 ∧
    (2 ^ (3 - 1) + 1) * 7 = clmul (2 ^ 3 + 2 ^ (3 - 1) + 1) 7 := by decide

end Candidates.A115770NaturalClmulCarryless
