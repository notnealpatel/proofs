/-
Existence for the even-even digit-sum property (OEIS A189202;
Vladimir Shevelev, May 02 2011; “A new digital problem”, SeqFan, Apr 2011).

For every n≥2 there is positive m with s₂(m(n-1)) even and
s_n(2m(n-1))/(n-1) even. The quotient is proved integral.
Thus the least-witness-or-zero sequence is positive on its source domain n≥2;
no claim is made about the totalized definitions at smaller bases.
The construction uses separated powers with additive digit sums and
pigeonhole on their residues.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A189202SuchEvenEven

/-! ## Definition layer -/

/-- The base-`k` digit sum `s_k(x)` of the entry, via Mathlib's `Nat.digits`
(least significant digit first). -/
def digitSum (k x : ℕ) : ℕ := (Nat.digits k x).sum

/-- `m` has the even-even property for `n` (A189202): `s_2(m*(n-1))` is even
and `s_n(2*m*(n-1))/(n-1)` is even.  The division is exact
(`sub_one_dvd_digitSum`), so the truncating `ℕ` division agrees with the
entry's quotient. -/
def IsSolution (n m : ℕ) : Prop :=
  Even (digitSum 2 (m * (n - 1))) ∧ Even (digitSum n (2 * m * (n - 1)) / (n - 1))

instance (n m : ℕ) : Decidable (IsSolution n m) := by
  unfold IsSolution digitSum
  infer_instance

open Classical in
/-- A189202: `a(n)` is the least `m > 0` with the even-even property for `n`,
or `0` if no such `m` exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ m, 0 < m ∧ IsSolution n m then Nat.find h else 0

/-- Characterisation of `a n = k` by minimality, used for the examples: if `k > 0` has the property and no smaller positive `m` does, then
`a n = k`. -/
theorem a_eq_of_isLeast (n k : ℕ) (hk : 0 < k) (hgood : IsSolution n k)
    (hmin : ∀ m < k, 0 < m → ¬ IsSolution n m) : a n = k := by
  classical
  have hex : ∃ m, 0 < m ∧ IsSolution n m := ⟨k, hk, hgood⟩
  unfold a
  rw [dif_pos hex, Nat.find_eq_iff]
  exact ⟨⟨hk, hgood⟩, fun m hm hms => hmin m hm hms.1 hms.2⟩

/-! ## The first listed terms `a(2..7) = 3,5,5,3,13,4` and `a(15) = 47` -/

example : digitSum 2 6 = 2 := by decide
example : digitSum 10 1234 = 10 := by decide

example : a 2 = 3 := a_eq_of_isLeast 2 3 (by norm_num) (by decide) (by decide)
example : a 3 = 5 := a_eq_of_isLeast 3 5 (by norm_num) (by decide) (by decide)
example : a 4 = 5 := a_eq_of_isLeast 4 5 (by norm_num) (by decide) (by decide)
example : a 5 = 3 := a_eq_of_isLeast 5 3 (by norm_num) (by decide) (by decide)
example : a 6 = 13 := a_eq_of_isLeast 6 13 (by norm_num) (by decide) (by decide)
example : a 7 = 4 := a_eq_of_isLeast 7 4 (by norm_num) (by decide) (by decide)
example : a 15 = 47 := a_eq_of_isLeast 15 47 (by norm_num) (by decide) (by decide)

/-! ## Helper lemmas -/

/-- Separation lemma: if `x < b^k`, the base-`b` digits of `x + b^k * y` are
those of `x` (padded with zeros) followed by those of `y`, so the digit sums
add. -/
theorem digitSum_add_pow_mul {b k x y : ℕ} (hb : 1 < b) (hx : x < b ^ k) :
    digitSum b (x + b ^ k * y) = digitSum b x + digitSum b y := by
  unfold digitSum
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  have hlen : (Nat.digits b x).length ≤ k := (Nat.digits_length_le_iff hb x).mpr hx
  have key := Nat.digits_append_zeroes_append_digits (k := k - (Nat.digits b x).length)
    (n := x) hb hy
  rw [Nat.add_sub_cancel' hlen] at key
  rw [← key]
  simp

/-- Doubling does not change the binary digit sum. -/
theorem digitSum_two_two_mul (k : ℕ) : digitSum 2 (2 * k) = digitSum 2 k := by
  unfold digitSum
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [Nat.digits_def' (by norm_num) (by omega)]
  simp

/-- Digit-sum congruence: `x ≡ s_n(x) (mod n - 1)` for `2 ≤ n`, including
the trivial modulus `1` at `n = 2`. -/
theorem modEq_digitSum (n x : ℕ) (hn : 2 ≤ n) : x ≡ digitSum n x [MOD n - 1] := by
  rcases (by omega : n = 2 ∨ 2 < n) with rfl | h2
  · exact Nat.modEq_one
  · have hmod : n % (n - 1) = 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    exact Nat.modEq_digits_sum (n - 1) n hmod x

/-- The quotient in the entry is exact: `(n - 1) ∣ s_n(2 * m * (n - 1))`. -/
theorem sub_one_dvd_digitSum (n m : ℕ) (hn : 2 ≤ n) :
    n - 1 ∣ digitSum n (2 * m * (n - 1)) := by
  have hcong := modEq_digitSum n (2 * m * (n - 1)) hn
  exact (Nat.modEq_zero_iff_dvd).mp
    (hcong.symm.trans ((Nat.modEq_zero_iff_dvd).mpr (Dvd.intro_left _ rfl)))

/-- Pigeonhole: for any `S : ℕ → ℕ` and modulus `q > 0`, some residue `β` is
attained by `S g` modulo `q` for arbitrarily large `g`. -/
theorem exists_residue_unbounded (S : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    ∃ β, ∀ B, ∃ g, B < g ∧ S g ≡ β [MOD q] := by
  let f : ℕ → Fin q := fun g => ⟨S g % q, Nat.mod_lt _ hq⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  refine ⟨y.val, fun B => ?_⟩
  obtain ⟨g, hg, hBg⟩ := (Set.infinite_coe_iff.mp hy).exists_gt B
  refine ⟨g, hBg, ?_⟩
  have hfg : f g = y := hg
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt y.isLt]
  exact congrArg Fin.val hfg

/-- Piece construction: given exponents `g` (arbitrarily large) with
`s_2(n^g) ≡ α (mod 2)` and exponents `h` (arbitrarily large) with
`s_n(2^h) ≡ β (mod q)`, for every `r` there is `X`, a sum of `r` pieces
`2^h * n^g`, with `s_2(X) ≡ r α (mod 2)`, `s_n(X) ≡ r β (mod q)`,
`2^c ∣ X`, and `0 < X` when `0 < r`. -/
theorem exists_pieces (n : ℕ) (hn : 2 ≤ n) (α β c q : ℕ)
    (hG : ∀ B, ∃ g, B < g ∧ digitSum 2 (n ^ g) ≡ α [MOD 2])
    (hH : ∀ B, ∃ h, B < h ∧ digitSum n (2 ^ h) ≡ β [MOD q]) (r : ℕ) :
    ∃ X, digitSum 2 X ≡ r * α [MOD 2] ∧ digitSum n X ≡ r * β [MOD q] ∧
      2 ^ c ∣ X ∧ (0 < r → 0 < X) := by
  induction r with
  | zero => exact ⟨0, by simp [Nat.ModEq, digitSum]⟩
  | succ r ih =>
    obtain ⟨X, h2, hb, hc, -⟩ := ih
    obtain ⟨g, hXg, hg⟩ := hG X
    obtain ⟨h, hXh, hh⟩ := hH (X + c)
    have hXn : X < n ^ g := hXg.trans (Nat.lt_pow_self (by omega))
    have hX2 : X < 2 ^ h := (by omega : X < h).trans Nat.lt_two_pow_self
    refine ⟨X + 2 ^ h * n ^ g, ?_, ?_, ?_, fun _ => ?_⟩
    · rw [digitSum_add_pow_mul (by norm_num) hX2, Nat.succ_mul]
      exact h2.add hg
    · rw [mul_comm (2 ^ h), digitSum_add_pow_mul (by omega) hXn, Nat.succ_mul]
      exact hb.add hh
    · exact dvd_add hc (dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _)
    · have hpiece : 0 < 2 ^ h * n ^ g := by positivity
      omega

/-! ## The conjecture -/

/-- Existence form of the A189202 conjecture: for every `n ≥ 2` there is
`m > 0` such that `s_2(m*(n-1))` and `s_n(2*m*(n-1))/(n-1)` are both even. -/
theorem exists_isSolution (n : ℕ) (hn : 2 ≤ n) : ∃ m, 0 < m ∧ IsSolution n m := by
  set N := n - 1 with hNdef
  have hN : 0 < N := by omega
  obtain ⟨v, o, ho, hNo⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  obtain ⟨α, hα⟩ := exists_residue_unbounded (fun g => digitSum 2 (n ^ g)) two_pos
  obtain ⟨β, hβ⟩ := exists_residue_unbounded (fun h => digitSum n (2 ^ h))
    (by omega : 0 < 2 * N)
  obtain ⟨X, h2, hb, hc, hpos⟩ := exists_pieces n hn α β (v + 1) (2 * N) hα hβ (2 * N)
  have hXpos : 0 < X := hpos (by omega)
  -- Both digit sums vanish modulo `2` and `2N` respectively.
  have h2dvd : 2 ∣ digitSum 2 X := by
    refine (Nat.modEq_zero_iff_dvd).mp (h2.trans ?_)
    exact (Nat.modEq_zero_iff_dvd).mpr (Dvd.intro (N * α) (by ring))
  have hqdvd : 2 * N ∣ digitSum n X := by
    refine (Nat.modEq_zero_iff_dvd).mp (hb.trans ?_)
    exact (Nat.modEq_zero_iff_dvd).mpr (Dvd.intro β rfl)
  -- `N ∣ X` from the digit-sum congruence, then `2N ∣ X` via the power of two.
  have hNX : N ∣ X :=
    (Nat.modEq_zero_iff_dvd).mp ((modEq_digitSum n X hn).trans
      ((Nat.modEq_zero_iff_dvd).mpr (dvd_of_mul_left_dvd hqdvd)))
  have h2NX : 2 * N ∣ X := by
    have hcop : Nat.Coprime (2 ^ (v + 1)) o :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
    have hsplit : 2 * N = 2 ^ (v + 1) * o := by rw [hNo]; ring
    rw [hsplit]
    exact hcop.mul_dvd_of_dvd_of_dvd hc (dvd_trans (Dvd.intro_left _ hNo.symm) hNX)
  obtain ⟨m, hm⟩ := h2NX
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  refine ⟨m, hmpos, ?_, ?_⟩
  · have hX : X = 2 * (m * N) := by rw [hm]; ring
    rw [← digitSum_two_two_mul, ← hX]
    exact even_iff_two_dvd.mpr h2dvd
  · have hX : 2 * m * N = X := by rw [hm]; ring
    rw [hX]
    obtain ⟨t, ht⟩ := hqdvd
    rw [ht, show 2 * N * t = N * (2 * t) by ring, Nat.mul_div_cancel_left _ hN]
    exact even_two_mul t

/-- The least even-even digit-sum witness is positive for every source base `n≥2`. -/
theorem a_pos (n : ℕ) (hn : 2 ≤ n) : 0 < a n := by
  classical
  have hex := exists_isSolution n hn
  unfold a
  rw [dif_pos hex]
  exact (Nat.find_spec hex).1

end Candidates.A189202SuchEvenEven
