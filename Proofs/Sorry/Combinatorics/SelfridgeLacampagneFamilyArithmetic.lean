import Sorry.Combinatorics.SelfridgeLacampagne
import Mathlib.Tactic

set_option autoImplicit false

namespace SelfridgeLacampagne

/-- Every sign word lies strictly between the two half-powers determined by its length. -/
theorem btVal_two_mul_bounds (L : List Bool) :
    -((3 : ℤ) ^ L.length - 1) ≤ 2 * btVal L ∧
      2 * btVal L ≤ (3 : ℤ) ^ L.length - 1 := by
  induction L with
  | nil => simp [btVal]
  | cons b t ih =>
    simp only [List.length_cons, pow_succ, btVal]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> omega

/-- A positive sign word has the sharp lower bound forced by its positive leading digit. -/
theorem btVal_pos_lower (L : List Bool) (hp : 0 < btVal L) :
    (3 : ℤ) ^ (L.length - 1) + 1 ≤ 2 * btVal L := by
  induction L with
  | nil => simp [btVal] at hp
  | cons b t ih =>
    cases t with
    | nil =>
      cases b
      · change 0 < (-1 : ℤ) at hp
        omega
      · norm_num [btVal]
    | cons c u =>
      have hne : btVal (c :: u) ≠ 0 := btVal_ne_zero _ (List.cons_ne_nil _ _)
      have ht : 0 < btVal (c :: u) := by
        change 0 < (if b then 1 else -1) + 3 * btVal (c :: u) at hp
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp <;> omega
      have hl := ih ht
      simp only [List.length_cons, Nat.add_sub_cancel] at hl
      change (3 : ℤ) ^ (u.length + 1) + 1 ≤
        2 * ((if b then 1 else -1) + 3 * btVal (c :: u))
      rw [pow_succ]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The parity of a sign word is the parity of its length. -/
theorem btVal_mod_two (L : List Bool) : btVal L % 2 = (L.length : ℤ) % 2 := by
  induction L with
  | nil => rfl
  | cons b t ih =>
    simp only [btVal, List.length_cons, Nat.cast_add, Nat.cast_one]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

example : 0 < btVal [true] ∧ (3 : ℤ) ^ (([true] : List Bool).length - 1) + 1 ≤
    2 * btVal [true] := by decide

/-- Multiplication by `3^m+4` allows only the two adjacent length jumps `m` and `m+1`. -/
theorem btVal_sparse_length_bounds (L M : List Bool) (m : ℕ) (hm : 1 ≤ m)
    (hp : 0 < btVal L) (heq : btVal M = ((3 : ℤ) ^ m + 4) * btVal L) :
    L.length + m ≤ M.length ∧ M.length ≤ L.length + m + 1 := by
  have hL : L ≠ [] := by
    intro hz
    simp [hz, btVal] at hp
  obtain ⟨r, hr⟩ : ∃ r, L.length = r + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by simpa using hL)
  have hp3 : 0 < (3 : ℤ) ^ m := pow_pos (by norm_num) _
  have h3 : (3 : ℤ) ≤ 3 ^ m := by
    simpa using pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num) hm
  have hk : (3 : ℤ) ^ m + 4 < 3 ^ (m + 1) := by
    rw [pow_succ]
    omega
  have hpM : 0 < btVal M := mul_pos (by omega) hp |>.trans_eq heq.symm
  have hlowL := btVal_pos_lower L hp
  have huppL := (btVal_two_mul_bounds L).2
  have hlowM := btVal_pos_lower M hpM
  have huppM := (btVal_two_mul_bounds M).2
  rw [hr, Nat.add_sub_cancel] at hlowL
  rw [hr] at huppL ⊢
  constructor
  · by_contra hn
    have hexp : M.length ≤ r + m := by omega
    have hpow := pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num) hexp
    rw [pow_add] at hpow
    have hmul := mul_le_mul_of_nonneg_left hlowL (show 0 ≤ (3 : ℤ) ^ m + 4 by omega)
    rw [heq] at huppM
    nlinarith [pow_pos (show (0 : ℤ) < 3 by norm_num) r]
  · by_contra hn
    have hexp : r + m + 2 ≤ M.length - 1 := by omega
    have hpow := pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num) hexp
    have hmul := mul_le_mul_of_nonneg_left huppL (show 0 ≤ (3 : ℤ) ^ m + 4 by omega)
    have hscale := mul_lt_mul_of_pos_right hk (show 0 < 2 * btVal L by omega)
    rw [heq] at hlowM
    have hupper : 2 * btVal M < (3 : ℤ) ^ (r + 1) * 3 ^ (m + 1) := by
      rw [heq]
      nlinarith [mul_nonneg (show 0 ≤ (3 : ℤ) ^ (m + 1) by positivity)
        (show 0 ≤ (3 : ℤ) ^ (r + 1) - 1 - 2 * btVal L by omega)]
    have hpoweq : (3 : ℤ) ^ (r + m + 2) = 3 ^ (r + 1) * 3 ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpoweq] at hpow
    omega

/-- For odd shifts, parity selects the longer of the two possible length jumps. -/
theorem btVal_sparse_length (L M : List Bool) (m : ℕ) (hm : 1 ≤ m)
    (hodd : Odd m) (hp : 0 < btVal L)
    (heq : btVal M = ((3 : ℤ) ^ m + 4) * btVal L) :
    M.length = L.length + m + 1 := by
  have hb := btVal_sparse_length_bounds L M m hm hp heq
  have hk : (((3 : ℤ) ^ m + 4) % 2) = 1 := by
    have hpow : ∀ t : ℕ, (3 : ℤ) ^ t % 2 = 1 := by
      intro t
      induction t with
      | zero => norm_num
      | succ t ih => simp [pow_succ, Int.mul_emod, ih]
    norm_num [Int.add_emod, hpow m]
  have hv : btVal M % 2 = btVal L % 2 := by
    rw [heq, Int.mul_emod, hk]
    omega
  rw [btVal_mod_two, btVal_mod_two] at hv
  have hmod : m % 2 = 1 := Nat.odd_iff.mp hodd
  omega

example : 1 ≤ (1 : ℕ) ∧ Odd (1 : ℕ) ∧ 0 < btVal [true] ∧
    btVal [true, false, true] = ((3 : ℤ) ^ (1 : ℕ) + 4) * btVal [true] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Little-endian ordinary ternary restricted to the digits zero and one. -/
def ternary01 : List Bool → ℤ
  | [] => 0
  | b :: t => (if b then 1 else 0) + 3 * ternary01 t

example : ternary01 [true, false, true] = 10 := rfl
example : ternary01 [] = 0 := rfl

/-- Restricted ternary words are nonnegative and bounded by the all-one word. -/
theorem ternary01_bounds (L : List Bool) :
    0 ≤ ternary01 L ∧ 2 * ternary01 L ≤ (3 : ℤ) ^ L.length - 1 := by
  induction L with
  | nil => norm_num [ternary01]
  | cons b t ih =>
    simp only [ternary01, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> omega

/-- Negative signs encode the difference from the all-positive balanced word. -/
theorem btVal_negative_encoding (L : List Bool) :
    2 * btVal L = (3 : ℤ) ^ L.length - 1 - 4 * ternary01 (L.map Bool.not) := by
  induction L with
  | nil => norm_num [btVal, ternary01]
  | cons b t ih =>
    simp only [btVal, List.length_cons, pow_succ, List.map_cons, ternary01]
    cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
      omega

/-- Positive signs encode the difference from the all-negative balanced word. -/
theorem btVal_positive_encoding (L : List Bool) :
    2 * btVal L = 4 * ternary01 L - ((3 : ℤ) ^ L.length - 1) := by
  induction L with
  | nil => norm_num [btVal, ternary01]
  | cons b t ih =>
    simp only [btVal, List.length_cons, pow_succ, ternary01]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A final sign contributes its power of three to the balanced value. -/
theorem btVal_append_singleton (L : List Bool) (b : Bool) :
    btVal (L ++ [b]) = btVal L + (3 : ℤ) ^ L.length * (if b then 1 else -1) := by
  induction L with
  | nil => simp [btVal]
  | cons c t ih =>
    simp only [List.cons_append, btVal, List.length_cons, pow_succ, ih]
    ring

/-- A positive balanced word has positive final sign. -/
theorem btVal_pos_append_true (M : List Bool) (hp : 0 < btVal M) :
    ∃ U : List Bool, M = U ++ [true] := by
  induction M using List.reverseRecOn with
  | nil => simp [btVal] at hp
  | append_singleton U b _ =>
    cases b
    · have hb := (btVal_two_mul_bounds U).2
      rw [btVal_append_singleton] at hp
      simp only [Bool.false_eq_true, ↓reduceIte] at hp
      nlinarith [pow_pos (show (0 : ℤ) < 3 by norm_num) U.length]
    · exact ⟨U, rfl⟩

/-- The positive leading sign leaves a zero/one ternary word on the lower positions. -/
theorem btVal_lower_positive_encoding (U : List Bool) :
    2 * btVal (U ++ [true]) = (3 : ℤ) ^ U.length + 1 + 4 * ternary01 U := by
  rw [btVal_append_singleton]
  have h := btVal_positive_encoding U
  simp only [↓reduceIte]
  omega

/-- The multiplication equation becomes an exact identity of restricted ternary values,
with no division or rounding. The witness is precisely the lower word of the numerator. -/
theorem btVal_sparse_encoding (L M : List Bool) (m : ℕ) (hm : 1 ≤ m)
    (hodd : Odd m) (hp : 0 < btVal L)
    (heq : btVal M = ((3 : ℤ) ^ m + 4) * btVal L) :
    ∃ U : List Bool, M = U ++ [true] ∧ U.length = L.length + m ∧
      4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
        4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5) := by
  have hlen := btVal_sparse_length L M m hm hodd hp heq
  have hpM : 0 < btVal M := by
    rw [heq]
    exact mul_pos (by positivity) hp
  obtain ⟨U, hU⟩ := btVal_pos_append_true M hpM
  have hlenU : U.length = L.length + m := by
    rw [hU, List.length_append, List.length_singleton] at hlen
    omega
  refine ⟨U, hU, hlenU, ?_⟩
  have hneg := btVal_negative_encoding L
  have hpos := btVal_lower_positive_encoding U
  rw [hlenU, pow_add, ← hU, heq] at hpos
  have hscaled := congrArg (fun z : ℤ => ((3 : ℤ) ^ m + 4) * z) hneg
  nlinarith [hscaled]

/-- The exact identity bounds both restricted ternary summands strictly below `3^n`. -/
theorem sparse_encoding_bounds (L U : List Bool) (m : ℕ)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5)) :
    ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) < (3 : ℤ) ^ L.length ∧
      ternary01 U < (3 : ℤ) ^ L.length := by
  have hS := (ternary01_bounds (L.map Bool.not)).1
  have hT := (ternary01_bounds U).1
  have hpow : 0 < (3 : ℤ) ^ m := by positivity
  constructor <;> nlinarith

/-- A true digit contributes its full power of three to a restricted ternary value. -/
theorem ternary01_pow_le_of_getD (L : List Bool) (i : ℕ)
    (hi : L.getD i false = true) : (3 : ℤ) ^ i ≤ ternary01 L := by
  induction L generalizing i with
  | nil => simp at hi
  | cons b t ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hi
      subst b
      have hnonneg := (ternary01_bounds t).1
      simp only [ternary01, ↓reduceIte, pow_zero]
      omega
    | succ i =>
      rw [List.getD_cons_succ] at hi
      have htail := ih i hi
      simp only [ternary01, pow_succ]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A strict power bound forces every digit at or above the cutoff to vanish. -/
theorem ternary01_getD_false_of_lt_pow (L : List Bool) (q i : ℕ)
    (hbound : ternary01 L < (3 : ℤ) ^ q) (hi : q ≤ i) : L.getD i false = false := by
  cases hd : L.getD i false with
  | false => rfl
  | true =>
    have hlower := ternary01_pow_le_of_getD L i hd
    have hpow := pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num) hi
    omega

/-- Once the denominator length reaches `m`, its last `m` negative-sign bits vanish. -/
theorem sparse_encoding_terminal (L U : List Bool) (m : ℕ) (hmn : m ≤ L.length)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5)) :
    ∀ j : ℕ, j < m → (L.map Bool.not).getD (L.length - m + j) false = false := by
  have hb := (sparse_encoding_bounds L U m heq).1
  have hS := (ternary01_bounds (L.map Bool.not)).1
  have hpow : (3 : ℤ) ^ L.length = 3 ^ m * 3 ^ (L.length - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  have hcut : ternary01 (L.map Bool.not) < (3 : ℤ) ^ (L.length - m) := by
    rw [hpow] at hb
    have hp : 0 < (3 : ℤ) ^ m := by positivity
    nlinarith
  intro j _
  exact ternary01_getD_false_of_lt_pow _ _ _ hcut (by omega)

/-- Restricted ternary numbers have a residue at most thirteen modulo twenty-seven. -/
theorem ternary01_mod_twenty_seven (L : List Bool) : ternary01 L % 27 ≤ 13 := by
  cases L with
  | nil => norm_num [ternary01]
  | cons b t =>
    cases t with
    | nil => cases b <;> norm_num [ternary01]
    | cons c u =>
      cases u with
      | nil => cases b <;> cases c <;> norm_num [ternary01]
      | cons d v =>
        change ((if b then 1 else 0) + 3 * ((if c then 1 else 0) +
          3 * ((if d then 1 else 0) + 3 * ternary01 v))) % 27 ≤ 13
        cases b <;> cases c <;> cases d <;>
          simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- For `m ≥ 5`, the exact binary encoding rules out every denominator length at most `m`.
The two borderline lengths fail because their lower numerator has residue nineteen modulo 27. -/
theorem sparse_encoding_length_lower (L U : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5)) : m + 1 ≤ L.length := by
  have hS := (ternary01_bounds (L.map Bool.not)).1
  have hT := (ternary01_bounds U).1
  have hpm : 0 < (3 : ℤ) ^ m := by positivity
  have hpn : 0 < (3 : ℤ) ^ L.length := by positivity
  have hnear : m ≤ L.length + 1 := by
    by_contra hn
    have hexp : L.length + 2 ≤ m := by omega
    have hpow := pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num) hexp
    rw [pow_add] at hpow
    norm_num at hpow
    nlinarith
  by_contra hn
  have hnm : L.length ≤ m := by omega
  have hpownm := pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num) hnm
  have hb := (sparse_encoding_bounds L U m heq).1
  have hz : ternary01 (L.map Bool.not) = 0 := by
    by_contra hz
    have hposS : 1 ≤ ternary01 (L.map Bool.not) := by omega
    nlinarith
  rw [hz] at heq
  have hdiv : ∀ t : ℕ, 3 ≤ t → (3 : ℤ) ^ t % 27 = 0 := by
    intro t ht
    have hpow : (3 : ℤ) ^ t = 27 * 3 ^ (t - 3) := by
      rw [show t = 3 + (t - 3) by omega, pow_add]
      norm_num
    rw [hpow]
    omega
  have hnmod := hdiv L.length (by omega)
  have hmmod := hdiv m (by omega)
  have hTmod := ternary01_mod_twenty_seven U
  omega

example : 4 * ternary01 [true, false] +
    4 * ((3 : ℤ) ^ (1 : ℕ) + 4) * ternary01 (([true] : List Bool).map Bool.not) =
      4 * (3 : ℤ) ^ ([true] : List Bool).length - ((3 : ℤ) ^ (1 : ℕ) + 5) := by decide

/-- A genuine positive multiplication witness forces a denominator longer than `m`. -/
theorem btVal_sparse_denominator_length (L M : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (hodd : Odd m) (hp : 0 < btVal L)
    (heq : btVal M = ((3 : ℤ) ^ m + 4) * btVal L) : m + 1 ≤ L.length := by
  obtain ⟨U, _, _, hencoding⟩ := btVal_sparse_encoding L M m (by omega) hodd hp heq
  exact sparse_encoding_length_lower L U m hm hencoding

/-- The actual negative-sign digits of a multiplication witness have a terminal block
of `m` zeros starting at `length L - m`, including overlapping-window cases. -/
theorem btVal_sparse_terminal (L M : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (hodd : Odd m) (hp : 0 < btVal L)
    (heq : btVal M = ((3 : ℤ) ^ m + 4) * btVal L) :
    ∀ j : ℕ, j < m → (L.map Bool.not).getD (L.length - m + j) false = false := by
  obtain ⟨U, _, _, hencoding⟩ := btVal_sparse_encoding L M m (by omega) hodd hp heq
  have hlen := sparse_encoding_length_lower L U m hm hencoding
  exact sparse_encoding_terminal L U m (by omega) hencoding

end SelfridgeLacampagne
