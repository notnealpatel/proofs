/-
# A110734: an unbounded family of zeros

OEIS A110734, the conjecture that digit-interleaving multiples eventually
exist; heuristic discussion by Franklin T. Adams-Watters (Sep 25 2006).
For every `j ≥ 1`, `a(2*10^j - 1) = 0`, refuting eventual nonvanishing.
Writing `X = 10^j`, a candidate multiple of `2X-1` must lie in `[X²,2X²)`;
its prescribed digits contradict the resulting quotient bounds.
The argument uses the literal finite insertion range, not a probability model.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A110734Refutation

/-! ## Definitions -/

/-- The number `k` of decimal digits of `n` (for `n ≥ 1`). -/
def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-- `Weave k n m`: writing `n = a_1 a_2 … a_k` in decimal (`k` digits), `m` is
of the form `a_1 b_1 a_2 b_2 … b_{k-1} a_k` for some digits `b_i`.  Encoded
arithmetically: `m` has exactly `2k - 1` digits (`10^(2k-2) ≤ m < 10^(2k-1)`),
and the digit of `m` at position `2i` (counting from the units digit, position
`0`) equals the digit of `n` at position `i`, for every `i < k`.  The odd
positions of `m` (the inserted `b_i`) are unconstrained. -/
def Weave (k n m : ℕ) : Prop :=
  10 ^ (2 * k - 2) ≤ m ∧ m < 10 ^ (2 * k - 1) ∧
    ∀ i < k, m / 10 ^ (2 * i) % 10 = n / 10 ^ i % 10

instance (k n m : ℕ) : Decidable (Weave k n m) := by
  unfold Weave
  infer_instance

/-- `IsWeave n m`: `m` is obtained from `n` by inserting one digit in each of
the `k - 1` gaps between consecutive decimal digits of `n`. -/
def IsWeave (n m : ℕ) : Prop := Weave (numDigits n) n m

instance (n m : ℕ) : Decidable (IsWeave n m) := by
  unfold IsWeave
  infer_instance

/-- **A110734.** `a n` is the least multiple of `n` of the form
`a_1 b_1 a_2 … b_{k-1} a_k` (`IsWeave n m`), or `0` if there is none.  Every
such `m` is `< 10^(2k-1)`, so scanning `0, 1, …, 10^(2k-1) - 1` in increasing
order and taking the first hit gives the least one. -/
def a (n : ℕ) : ℕ :=
  let k := numDigits n
  ((List.range (10 ^ (2 * k - 1))).find? (fun m => decide (Weave k n m ∧ n ∣ m))).getD 0

/-! ## Examples against the OEIS DATA line (offset 1) -/

-- Checked in blocks of ten: a single `decide +kernel` over all 65 terms
-- exhausts memory, while each block below checks in about two seconds.
example : (List.range' 1 9).map a = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide +kernel
example : (List.range' 10 10).map a = [100, 121, 132, 143, 154, 105, 176, 187, 108, 0] := by
  decide +kernel
example : (List.range' 20 10).map a = [200, 231, 242, 253, 264, 225, 286, 297, 0, 0] := by
  decide +kernel
example : (List.range' 30 10).map a = [300, 341, 352, 363, 374, 315, 396, 0, 0, 0] := by
  decide +kernel
example : (List.range' 40 10).map a = [400, 451, 462, 473, 484, 405, 0, 0, 0, 0] := by
  decide +kernel
example : (List.range' 50 10).map a = [500, 561, 572, 583, 594, 0, 0, 0, 0, 0] := by
  decide +kernel
example : (List.range' 60 6).map a = [600, 671, 682, 693, 0, 0] := by decide +kernel

/- Non-vacuity of the weave predicate on the zero family: `109` and `199`
are weaves of `19` (the candidates exist; none is a multiple of `19`). -/
example : IsWeave 19 109 ∧ IsWeave 19 199 := by decide +kernel

/-! ## Arithmetic of `n = 2·10^j - 1` -/

/-- Long division: `(2PQ - 1) / P = 2Q - 1` for `P, Q ≥ 1`. -/
theorem two_mul_sub_one_div {P Q : ℕ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) :
    (2 * (P * Q) - 1) / P = 2 * Q - 1 := by
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul]
    have h1 : 2 * Q * P = 2 * (P * Q) := by ring
    omega
  · rw [Nat.sub_add_cancel (by omega)]
    have h1 : 2 * Q * P = 2 * (P * Q) := by ring
    have h2 : 1 ≤ P * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega

/-- The decimal digits of `2·10^j - 1 = 199…9`: digit `9` at positions `i < j`. -/
theorem digit_lt (j i : ℕ) (hi : i < j) : (2 * 10 ^ j - 1) / 10 ^ i % 10 = 9 := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
  rw [pow_add, two_mul_sub_one_div (Nat.one_le_pow _ _ (by norm_num))
    (Nat.one_le_pow _ _ (by norm_num)), pow_succ]
  have h : 1 ≤ 10 ^ d := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- The leading decimal digit of `2·10^j - 1` (position `j`) is `1`. -/
theorem digit_top (j : ℕ) : (2 * 10 ^ j - 1) / 10 ^ j % 10 = 1 := by
  have h := two_mul_sub_one_div (P := 10 ^ j) (Q := 1) (Nat.one_le_pow _ _ (by norm_num)) le_rfl
  rw [mul_one] at h
  rw [h]

/-- `2·10^j - 1` has `j + 1` decimal digits. -/
theorem numDigits_two_mul_ten_pow_sub_one (j : ℕ) : numDigits (2 * 10 ^ j - 1) = j + 1 := by
  have h : 1 ≤ 10 ^ j := Nat.one_le_pow _ _ (by norm_num)
  unfold numDigits
  rw [Nat.length_digits 10 _ (by norm_num) (by omega)]
  congr 1
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]
    omega

/-! ## The core division argument -/

/-- No multiple `C = (2X - 1) q` of `2X - 1` with `X = 10^j`, `j ≥ 1`, can
satisfy `X² ≤ C < 2X²` together with the digit constraints "digit `9` at every
even position `< 2j`" (only positions `0`, `j - 1` (odd `j`) and `j` (even `j`)
are used). -/
theorem core (j : ℕ) (hj : 1 ≤ j) (q : ℕ)
    (hlo : 10 ^ j * 10 ^ j ≤ (2 * 10 ^ j - 1) * q)
    (hhi : (2 * 10 ^ j - 1) * q < 2 * (10 ^ j * 10 ^ j))
    (hdig : ∀ i < j, (2 * 10 ^ j - 1) * q / 10 ^ (2 * i) % 10 = 9) : False := by
  have hXZ : 10 ^ j = 10 * 10 ^ (j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  set Z := 10 ^ (j - 1) with hZdef
  have hZ : 1 ≤ Z := Nat.one_le_pow _ _ (by norm_num)
  set X := 10 ^ j with hXdef
  set n := 2 * X - 1 with hndef
  have hn : n + 1 = 2 * X := by omega
  -- bounds on the quotient `q`
  have hqX : q ≤ X := by
    by_contra h
    push Not at h
    have h1 : n * (X + 1) ≤ n * q := Nat.mul_le_mul_left n h
    have h2 : X ≤ n := by omega
    nlinarith
  have hXq : X < 2 * q := by
    by_contra h
    push Not at h
    have h1 : n * (2 * q) ≤ n * X := Nat.mul_le_mul_left n h
    nlinarith
  obtain ⟨r, hr⟩ : ∃ r, X = q + r := ⟨X - q, by omega⟩
  obtain ⟨p, hp⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hr2 : 2 * r < X := by omega
  have hn' : n = 2 * p + 2 * r + 1 := by omega
  -- the block decomposition `C = (2p+1)·X + r`
  have hC : n * q = (2 * p + 1) * X + r := by
    rw [hn', hp, hr, hp]
    ring
  have hC10 : n * q = 10 * ((2 * p + 1) * Z) + r := by
    rw [hC, hXZ]
    ring
  have hunit : n * q % 10 = 9 := by
    simpa using hdig 0 (by omega)
  have hr9 : r % 10 = 9 := by omega
  rcases Nat.even_or_odd' j with ⟨i, hi | hi⟩
  · -- `j = 2i`: the digit at position `j` is the units digit of `2p+1`
    have hij : i < j := by omega
    have hd := hdig i hij
    rw [← hi] at hd
    have hdiv : n * q / X = 2 * p + 1 := by
      rw [hC, add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
      ring
    rw [hdiv] at hd
    omega
  · -- `j = 2i+1`: the digit at position `j - 1` is the leading digit of `r`
    have hij : i < j := by omega
    have hd := hdig i hij
    have hZi : 10 ^ (2 * i) = Z := by rw [hZdef]; congr 1; omega
    rw [hZi] at hd
    have hdiv : n * q / Z = r / Z + 10 * (2 * p + 1) := by
      rw [hC, hXZ, add_comm, show (2 * p + 1) * (10 * Z) = 10 * (2 * p + 1) * Z by ring,
        Nat.add_mul_div_right _ _ (by omega)]
    rw [hdiv] at hd
    have h9 : 9 ≤ r / Z := by
      generalize r / Z = w at hd
      omega
    rw [Nat.le_div_iff_mul_le (by omega)] at h9
    omega

/-! ## The zero family and the refutation -/

/-- **Zero family.** For every `j ≥ 1`, no weave of `n = 2·10^j - 1 = 199…9`
is a multiple of `n`. -/
theorem not_dvd_of_isWeave (j : ℕ) (hj : 1 ≤ j) (m : ℕ)
    (hm : IsWeave (2 * 10 ^ j - 1) m) : ¬ (2 * 10 ^ j - 1) ∣ m := by
  rintro ⟨q, rfl⟩
  obtain ⟨hlo, hhi, hdig⟩ := hm
  rw [numDigits_two_mul_ten_pow_sub_one] at hlo hhi hdig
  have hsq : 10 ^ (2 * j) = 10 ^ j * 10 ^ j := by rw [← pow_add]; congr 1; ring
  have hlo' : 2 * (j + 1) - 2 = 2 * j := by omega
  have hhi' : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [hlo', hsq] at hlo
  rw [hhi'] at hhi
  apply core j hj q hlo
  · -- the leading digit (position `2j`) is `1`, so `C < 2·10^(2j)`
    have htop := hdig j (by omega)
    rw [digit_top] at htop
    have hlt : (2 * 10 ^ j - 1) * q / 10 ^ (2 * j) < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ']
      exact hhi
    have h1 : (2 * 10 ^ j - 1) * q / 10 ^ (2 * j) < 2 := by omega
    rw [Nat.div_lt_iff_lt_mul (by positivity), hsq] at h1
    linarith
  · intro i hi
    rw [hdig i (by omega), digit_lt j i hi]

/-- **Zero family.** `a(2·10^j - 1) = 0` for every `j ≥ 1` (`a(19) = a(199) =
a(1999) = … = 0`). -/
theorem a_two_mul_ten_pow_sub_one (j : ℕ) (hj : 1 ≤ j) : a (2 * 10 ^ j - 1) = 0 := by
  unfold a
  dsimp only
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro m _ hm
    rw [decide_eq_true_eq] at hm
    exact not_dvd_of_isWeave j hj m hm.1 hm.2

/-- **The A110734 conjecture is false.**  The entry's comment "Conjecture: for
large n, a(n) is nonzero" asserts `∃ N, ∀ n ≥ N, a n ≠ 0`; this is refuted by
the family `n = 2·10^j - 1`. -/
theorem not_conjecture : ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n ≠ 0 := by
  rintro ⟨N, hN⟩
  have hlt : N + 1 < 10 ^ (N + 1) := Nat.lt_pow_self (by norm_num : 1 < 10)
  exact hN (2 * 10 ^ (N + 1) - 1) (by omega) (a_two_mul_ten_pow_sub_one (N + 1) (by omega))

end Candidates.A110734Refutation
