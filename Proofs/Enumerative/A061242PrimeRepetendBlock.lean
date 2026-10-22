/-
# A061242: the least left-rotation number

OEIS A061242, Doug Bell (Mar 23 2009).
For prime `p = 9x - 1`, the repetend block of `x/p` is the least positive
integer whose left rotation is `(x+1)/x` times itself.
The proof uses decimal length and the multiplicative order of `10` modulo `p`.
Bell's separate claim that these are the only possible `x`, refuted in the
entry by Giovanni Resta (Jul 28 2015), is not formalized.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A061242PrimeRepetendBlock

/-! ## Definitions -/

/-- Left digit rotation of `N` in base `10`: the most significant decimal digit
is moved to the units place (e.g. `1176470588235294 ↦ 1764705882352941`,
`105 ↦ 051 = 51`).  `Nat.digits 10 N` is little-endian, so moving the last list
entry to the front is `List.rotate` by `length - 1`. -/
def rotL (N : ℕ) : ℕ :=
  Nat.ofDigits 10 ((Nat.digits 10 N).rotate ((Nat.digits 10 N).length - 1))

/-- The `i`-th decimal digit after the point of the fraction `x / p`
(`i ≥ 1`), namely `⌊x · 10^i / p⌋ mod 10`. -/
def decimalDigit (x p i : ℕ) : ℕ := x * 10 ^ i / p % 10

/-- The first `n` decimal digits after the point of `x / p`, listed
little-endian (digit `n` first, digit `1` last), so that `Nat.ofDigits 10`
reads them as the integer formed by those digits. -/
def decimalDigits (x p : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => decimalDigit x p (n + 1) :: decimalDigits x p n

/-- The repetend block of `x / p`: the integer formed by one period of the
decimal expansion, i.e. by its first `ord_p(10)` digits after the point (the
expansion is purely periodic when `p` is a prime other than `2, 5`). -/
noncomputable def repetendBlock (x p : ℕ) : ℕ :=
  Nat.ofDigits 10 (decimalDigits x p (orderOf (10 : ZMod p)))

/-! ## Examples -/

-- Rotation examples from the entry (Bell's and Resta's) and a zero-digit case.
example : rotL 1176470588235294 = 1764705882352941 := by decide
example : rotL 230769 = 307692 := by decide
example : rotL 105 = 51 := by decide

-- `2/17 = 0.1176470588235294...`, period `16`, as stated in the entry.
example : decimalDigits 2 17 4 = [6, 7, 1, 1] := by decide
example : orderOf (10 : ZMod 17) = 16 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide
example : repetendBlock 2 17 = 1176470588235294 := by
  have hord : orderOf (10 : ZMod 17) = 16 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  rw [repetendBlock, hord]
  decide

-- Bell's example: `1176470588235294 * 3/2 = rotL 1176470588235294`.
example : 2 * rotL 1176470588235294 = (2 + 1) * 1176470588235294 := by decide

/-! ## Helper lemmas -/

/-- The integer formed by the first `n` decimal digits of `x / p` (for `x < p`)
is `⌊x · 10^n / p⌋`. -/
theorem ofDigits_decimalDigits {x p : ℕ} (hxp : x < p) (n : ℕ) :
    Nat.ofDigits 10 (decimalDigits x p n) = x * 10 ^ n / p := by
  induction n with
  | zero => simp [decimalDigits, Nat.div_eq_of_lt hxp]
  | succ n ih =>
    rw [decimalDigits, Nat.ofDigits_cons, ih, decimalDigit]
    have hdiv : x * 10 ^ (n + 1) / p / 10 = x * 10 ^ n / p := by
      rw [Nat.div_div_eq_div_mul, pow_succ, ← mul_assoc,
        Nat.mul_div_mul_right _ _ (by norm_num)]
    have h := Nat.mod_add_div (x * 10 ^ (n + 1) / p) 10
    rw [hdiv] at h
    exact_mod_cast h

/-- Arithmetic form of the rotation: if `N` has `k + 1` decimal digits, its left
rotation is `(leading digit) + 10 · (N mod 10^k)`. -/
theorem rotL_eq_of_length {N k : ℕ} (hk : (Nat.digits 10 N).length = k + 1) :
    rotL N = N / 10 ^ k + 10 * (N % 10 ^ k) := by
  unfold rotL
  rw [hk, Nat.add_sub_cancel, List.rotate_eq_drop_append_take (by omega),
    Nat.ofDigits_append, ← Nat.self_div_pow_eq_ofDigits_drop _ _ (by norm_num),
    ← Nat.self_mod_pow_eq_ofDigits_take _ _ (by norm_num), List.length_drop, hk]
  simp

/-- A number with `k + 1` decimal digits lies in `[10^k, 10^(k+1))`. -/
theorem pow_le_and_lt_of_length {N k : ℕ} (hk : (Nat.digits 10 N).length = k + 1) :
    10 ^ k ≤ N ∧ N < 10 ^ (k + 1) :=
  ⟨(Nat.lt_digits_length_iff (by norm_num) N).mp (by omega),
    (Nat.digits_length_le_iff (by norm_num) N).mp hk.le⟩

/-! ## The conjecture -/

/-- Bell's A061242 conjecture: for prime `p` with `p+1 = 9x`, the repetend
block of `x/p` is the least positive `N` satisfying `x*rotL(N) = (x+1)*N`.
The block has `ord_p(10)` digits. Positivity excludes the trivial solution
`N = 0`, and `p+1 = 9x` avoids natural subtraction in `p = 9x-1`.
The rational formulation is `bell_conjecture_rat`. -/
theorem bell_conjecture (x p : ℕ) (hp : p.Prime) (hpx : p + 1 = 9 * x) :
    IsLeast {N : ℕ | 0 < N ∧ x * rotL N = (x + 1) * N} (repetendBlock x p) := by
  have hx2 : 2 ≤ x := by
    by_contra hcon
    interval_cases x
    · omega
    · have hp8 : p = 8 := by omega
      subst hp8
      norm_num at hp
  have hxp : x < p := by omega
  have hp17 : 17 ≤ p := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast_ne : ∀ m : ℕ, 0 < m → m < p → (m : ZMod p) ≠ 0 := by
    intro m hm hmp h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hm h) (by omega)
  have h10 : (10 : ZMod p) ≠ 0 := by
    have h10' := hcast_ne 10 (by norm_num) (by omega)
    exact_mod_cast h10'
  set d := orderOf (10 : ZMod p) with hd_def
  have hdpos : 0 < d :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one h10⟩)
  -- the block identity `p * B + x = x * 10 ^ d`
  set B := repetendBlock x p with hB_def
  have hBval : B = x * 10 ^ d / p := by
    rw [hB_def, repetendBlock, ofDigits_decimalDigits hxp]
  have hmod : x * 10 ^ d % p = x := by
    have h1 : ((x * 10 ^ d : ℕ) : ZMod p) = ((x : ℕ) : ZMod p) := by
      push_cast
      rw [hd_def, pow_orderOf_eq_one, mul_one]
    rw [ZMod.natCast_eq_natCast_iff] at h1
    rw [h1, Nat.mod_eq_of_lt hxp]
  have hBid : p * B + x = x * 10 ^ d := by
    rw [hBval]
    have hdm := Nat.div_add_mod (x * 10 ^ d) p
    rw [hmod] at hdm
    exact hdm
  constructor
  · -- membership: `B` has `d` digits, leading digit `1`, and solves the equation
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
    rw [he] at hBid
    have hDpos : 0 < 10 ^ e := by positivity
    have hlow : 10 ^ e ≤ B := by
      by_contra hcon
      have hlt := Nat.lt_of_not_le hcon
      have hmul : p * B < p * 10 ^ e := Nat.mul_lt_mul_of_pos_left hlt (by omega)
      rw [pow_succ] at hBid
      nlinarith
    have hhigh : B < 2 * 10 ^ e := by
      by_contra hcon
      have hge := Nat.le_of_not_lt hcon
      have hmul : p * (2 * 10 ^ e) ≤ p * B := Nat.mul_le_mul_left p hge
      rw [pow_succ] at hBid
      nlinarith
    have hlen : (Nat.digits 10 B).length = e + 1 := by
      apply le_antisymm
      · exact (Nat.digits_length_le_iff (by norm_num) B).mpr (by rw [pow_succ]; omega)
      · exact (Nat.lt_digits_length_iff (by norm_num) B).mpr hlow
    have hlead : B / 10 ^ e = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    refine ⟨by omega, ?_⟩
    rw [rotL_eq_of_length hlen, hlead]
    have hdecomp := Nat.div_add_mod B (10 ^ e)
    rw [hlead] at hdecomp
    set r := B % 10 ^ e
    rw [pow_succ] at hBid
    zify at hBid hdecomp hpx ⊢
    have hp' : (p : ℤ) = 9 * x - 1 := by linarith
    rw [hp'] at hBid
    rw [← hdecomp] at hBid ⊢
    linear_combination hBid
  · -- lower bound: every solution `N` satisfies `B ≤ N`
    rintro N ⟨hNpos, hNrot⟩
    obtain ⟨k, hk⟩ : ∃ k, (Nat.digits 10 N).length = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero
        (by rw [Ne, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]; omega)
    obtain ⟨hNlo, hNhi⟩ := pow_le_and_lt_of_length hk
    rw [rotL_eq_of_length hk] at hNrot
    set a := N / 10 ^ k with ha_def
    set r := N % 10 ^ k with hr_def
    have hdecomp : 10 ^ k * a + r = N := Nat.div_add_mod N (10 ^ k)
    have ha1 : 1 ≤ a := (Nat.one_le_div_iff (by positivity)).mpr hNlo
    have ha9 : a < 10 := by
      rw [ha_def, Nat.div_lt_iff_lt_mul (by positivity)]
      rw [pow_succ] at hNhi
      linarith
    -- the rotation equation forces `p * N + x * a = x * a * 10 ^ (k + 1)`
    have hkey : p * N + x * a = x * a * 10 ^ (k + 1) := by
      zify at hNrot hdecomp hpx ⊢
      have hp' : (p : ℤ) = 9 * x - 1 := by linarith
      rw [hp', pow_succ]
      linear_combination hNrot - 10 * (x : ℤ) * hdecomp
    -- hence `10 ^ (k + 1) = 1` in `ZMod p`, so `d ∣ k + 1`
    have hpow : (10 : ZMod p) ^ (k + 1) = 1 := by
      have h1 := congrArg (fun n : ℕ => (n : ZMod p)) hkey
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        ZMod.natCast_self, zero_mul, zero_add] at h1
      have hxa : ((x : ZMod p) * (a : ZMod p)) ≠ 0 :=
        mul_ne_zero (hcast_ne x (by omega) hxp) (hcast_ne a (by omega) (by omega))
      have h2 : ((x : ZMod p) * (a : ZMod p)) * ((10 : ZMod p) ^ (k + 1) - 1) = 0 := by
        rw [mul_sub, mul_one, ← h1, sub_self]
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hxa
      · exact sub_eq_zero.mp h
    have hdk : d ≤ k + 1 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hpow)
    have hpowle : 10 ^ d ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) hdk
    have hdpow : 1 ≤ 10 ^ d := Nat.one_le_pow _ _ (by norm_num)
    -- compare `p * B = x * (10 ^ d - 1)` with `p * N = x * a * (10 ^ (k + 1) - 1)`
    have hle : p * B ≤ p * N := by
      have h3 : x * (a - 1) * (10 ^ (k + 1) - 1) + x * (10 ^ (k + 1) - 10 ^ d) + p * B
          = p * N := by
        zify [ha1, hpowle, Nat.one_le_pow (k + 1) 10 (by norm_num)] at hkey hBid ⊢
        linear_combination hBid - hkey
      omega
    exact Nat.le_of_mul_le_mul_left hle (by omega)

/-- **Bell's conjecture, rational form.**  Same statement as `bell_conjecture`
with the entry's wording "(x+1)/x times larger" kept literally:
`rotL N = ((x + 1) / x) · N` in `ℚ`.  The hypothesis `p + 1 = 9x` with `p`
prime forces `x ≥ 2`, so the division is not the junk value at `x = 0`. -/
theorem bell_conjecture_rat (x p : ℕ) (hp : p.Prime) (hpx : p + 1 = 9 * x) :
    IsLeast {N : ℕ | 0 < N ∧ (rotL N : ℚ) = ((x + 1 : ℚ) / x) * N}
      (repetendBlock x p) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    have hx : x ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast hx
  have hset : {N : ℕ | 0 < N ∧ (rotL N : ℚ) = ((x + 1 : ℚ) / x) * N}
      = {N : ℕ | 0 < N ∧ x * rotL N = (x + 1) * N} := by
    ext N
    simp only [Set.mem_ofPred_eq]
    rw [div_mul_eq_mul_div, eq_div_iff hx0]
    constructor
    · rintro ⟨hN, h⟩
      refine ⟨hN, ?_⟩
      exact_mod_cast (by linarith : (x : ℚ) * rotL N = (x + 1) * N)
    · rintro ⟨hN, h⟩
      refine ⟨hN, ?_⟩
      have hq : (x : ℚ) * rotL N = (x + 1) * N := by exact_mod_cast h
      linarith
  rw [hset]
  exact bell_conjecture x p hp hpx

/-! ## Satisfiability -/

-- The hypotheses are jointly satisfiable (`x = 2`, `p = 17`), and the solution
-- set is nonempty there, as the conclusion then shows.
example : Nat.Prime 17 ∧ 17 + 1 = 9 * 2 := ⟨by norm_num, by norm_num⟩

example : IsLeast {N : ℕ | 0 < N ∧ 2 * rotL N = (2 + 1) * N} 1176470588235294 := by
  have hB : repetendBlock 2 17 = 1176470588235294 := by
    have hord : orderOf (10 : ZMod 17) = 16 := by
      rw [orderOf_eq_iff (by norm_num)]
      decide
    rw [repetendBlock, hord]
    decide
  rw [← hB]
  exact bell_conjecture 2 17 (by norm_num) (by norm_num)

end Candidates.A061242PrimeRepetendBlock
