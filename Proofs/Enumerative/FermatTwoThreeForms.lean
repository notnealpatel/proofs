/-
Fermat's prime representations by x²+2y² and x²+3y².

For prime p and natural x,y, representability by x²+2y² is equivalent to
p=2 or p≡1,3 (mod 8); representability by x²+3y² is equivalent to
p=3 or p≡1 (mod 3). The exceptional primes are included.
Sources: Fermat's letters (1654), Euler's proofs, and D. A. Cox,
Primes of the Form x²+ny², §§1–2.

The proof uses Thue's approximation lemma (1902): for prime p and a∈ZMod p,
there are natural x,y with 0<y, x²<p, y²<p and ay=±x modulo p.
Pigeonhole proves this lemma. Square roots of -2 and -3 then give a small
multiple of p, reduced by parity and divisibility; the converses use residues.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FermatTwoThreeForms

/-! ## Thue's lemma -/

/-- **Thue's lemma.** For a prime `p` and `a : ZMod p` there are naturals `x, y`
with `0 < y`, `x ^ 2 < p`, `y ^ 2 < p`, and `a * y = x` or `a * y = -x` in
`ZMod p`. -/
theorem thue {p : ℕ} [hp : Fact p.Prime] (a : ZMod p) :
    ∃ x y : ℕ, 0 < y ∧ x ^ 2 < p ∧ y ^ 2 < p ∧
      ((a * y : ZMod p) = x ∨ (a * y : ZMod p) = -x) := by
  set m := Nat.sqrt p with hm
  have hm_le : m ^ 2 ≤ p := Nat.sqrt_le' p
  have hm_ne : m ^ 2 ≠ p := by
    intro h
    have hsq : IsSquare p := ⟨m, by rw [← h, sq]⟩
    exact hsq.not_prime (Nat.prime_iff.mp hp.out)
  have hm_lt : m ^ 2 < p := lt_of_le_of_ne hm_le hm_ne
  have hp_lt : p < (m + 1) ^ 2 := Nat.lt_succ_sqrt' p
  have hm_lt_p : m < p := by
    have h1 : m ≤ m ^ 2 := by nlinarith
    omega
  -- Pigeonhole
  let f : Fin (m + 1) × Fin (m + 1) → ZMod p := fun uv => (uv.1 : ℕ) - a * (uv.2 : ℕ)
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    simp only [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  obtain ⟨⟨u₁, v₁⟩, ⟨u₂, v₂⟩, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hu₁ := u₁.isLt
  have hu₂ := u₂.isLt
  have hv₁ := v₁.isLt
  have hv₂ := v₂.isLt
  set X : ℤ := (u₁ : ℕ) - (u₂ : ℕ) with hX
  set Y : ℤ := (v₁ : ℕ) - (v₂ : ℕ) with hY
  have hXY : (X : ZMod p) = a * (Y : ZMod p) := by
    simp only [f] at hfeq
    rw [hX, hY]
    push_cast
    linear_combination hfeq
  have hYne : Y ≠ 0 := by
    intro hY0
    have hX0 : (X : ZMod p) = 0 := by rw [hXY, hY0]; simp
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hX0
    have hXabs : |X| < (p : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have hXz : X = 0 := Int.eq_zero_of_abs_lt_dvd hX0 hXabs
    apply hne
    have h1 : (u₁ : ℕ) = u₂ := by omega
    have h2 : (v₁ : ℕ) = v₂ := by omega
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  have hxle : X.natAbs ≤ m := by omega
  have hyle : Y.natAbs ≤ m := by omega
  refine ⟨X.natAbs, Y.natAbs, by omega,
    lt_of_le_of_lt (Nat.pow_le_pow_left hxle 2) hm_lt,
    lt_of_le_of_lt (Nat.pow_le_pow_left hyle 2) hm_lt, ?_⟩
  have hXc : ((X.natAbs : ℕ) : ZMod p) = X ∨ ((X.natAbs : ℕ) : ZMod p) = -X := by
    rcases Int.natAbs_eq X with h | h
    · left; conv_rhs => rw [h]
      simp
    · right; conv_rhs => rw [h]
      simp
  have hYc : ((Y.natAbs : ℕ) : ZMod p) = Y ∨ ((Y.natAbs : ℕ) : ZMod p) = -Y := by
    rcases Int.natAbs_eq Y with h | h
    · left; conv_rhs => rw [h]
      simp
    · right; conv_rhs => rw [h]
      simp
  rcases hXc with hx | hx <;> rcases hYc with hy | hy <;> rw [hx, hy]
  · left; rw [hXY]
  · right; rw [hXY]; ring
  · right; rw [hXY]; ring
  · left; rw [hXY]; ring

/-! ## From a square root of `-n` to a small multiple of `p` -/

/-- If `-n` is a square modulo the prime `p`, then Thue's lemma gives naturals
`x, y` with `0 < y`, `x ^ 2 < p`, `y ^ 2 < p` and `p ∣ x ^ 2 + n * y ^ 2`. -/
theorem exists_dvd_sq_add_mul_sq {p : ℕ} [Fact p.Prime] (n : ℕ)
    (hsq : IsSquare (-(n : ZMod p))) :
    ∃ x y : ℕ, 0 < y ∧ x ^ 2 < p ∧ y ^ 2 < p ∧ p ∣ x ^ 2 + n * y ^ 2 := by
  obtain ⟨a, ha⟩ := hsq
  obtain ⟨x, y, hy, hx, hyp, hxy⟩ := thue a
  refine ⟨x, y, hy, hx, hyp, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have hx2 : (x : ZMod p) ^ 2 = (a * y) ^ 2 := by
    rcases hxy with h | h
    · rw [h]
    · rw [h]; ring
  linear_combination hx2 - (y : ZMod p) ^ 2 * ha

/-- `-3` is a square modulo a prime `p ≡ 1 (mod 3)`: if `ω` is a primitive cube
root of unity in `ZMod p` then `(2ω + 1)^2 = -3`. -/
theorem isSquare_neg_three_of_mod_three_eq_one {p : ℕ} [Fact p.Prime] (h : p % 3 = 1) :
    IsSquare (-3 : ZMod p) := by
  have h3 : 3 ∣ Fintype.card (ZMod p)ˣ := by rw [ZMod.card_units]; omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hω3 : (g : ZMod p) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hω1 : (g : ZMod p) ≠ 1 := by
    intro h1
    have hg1 : g = 1 := Units.ext h1
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hcyc : (g : ZMod p) ^ 2 + g + 1 = 0 := by
    have hprod : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + g + 1) = 0 := by
      linear_combination hω3
    rcases mul_eq_zero.mp hprod with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hω1
    · exact h0
  exact ⟨2 * (g : ZMod p) + 1, by linear_combination (-4 : ZMod p) * hcyc⟩

/-! ## The form `x^2 + 2y^2` -/

/-- A prime `p ≡ 1, 3 (mod 8)` is of the form `x ^ 2 + 2 * y ^ 2`. -/
theorem exists_sq_add_two_mul_sq_of_mod_eight {p : ℕ} (hp : p.Prime)
    (h : p % 8 = 1 ∨ p % 8 = 3) : ∃ x y : ℕ, p = x ^ 2 + 2 * y ^ 2 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at h
  have hsq : IsSquare (-((2 : ℕ) : ZMod p)) := by
    push_cast
    exact (ZMod.exists_sq_eq_neg_two_iff hp2).mpr h
  obtain ⟨x, y, hy, hx, hyp, ⟨k, hk⟩⟩ := exists_dvd_sq_add_mul_sq 2 hsq
  have hy2 : 0 < y ^ 2 := by positivity
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk; omega
    · exact h0
  have hk3 : k < 3 := by nlinarith
  interval_cases k
  · exact ⟨x, y, by omega⟩
  · -- `x ^ 2 + 2 y ^ 2 = 2 p`: then `x` is even and `p = y ^ 2 + 2 (x / 2) ^ 2`.
    have hxe : Even (x ^ 2) := ⟨p - y ^ 2, by omega⟩
    obtain ⟨t, rfl⟩ := (Nat.even_pow' two_ne_zero).mp hxe
    exact ⟨y, t, by ring_nf at hk; omega⟩

/-- A prime of the form `x ^ 2 + 2 * y ^ 2` is `2` or `≡ 1, 3 (mod 8)`. -/
theorem mod_eight_of_eq_sq_add_two_mul_sq {p x y : ℕ} (hp : p.Prime)
    (hxy : p = x ^ 2 + 2 * y ^ 2) : p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3 := by
  rcases hp.eq_two_or_odd with h2 | hodd
  · exact Or.inl h2
  right
  have hmod : p % 8 = ((x % 8) ^ 2 + 2 * (y % 8) ^ 2) % 8 := by
    rw [hxy]; simp [Nat.add_mod, Nat.pow_mod, Nat.mul_mod]
  have hx8 : x % 8 < 8 := Nat.mod_lt x (by norm_num)
  have hy8 : y % 8 < 8 := Nat.mod_lt y (by norm_num)
  interval_cases hxr : x % 8 <;> interval_cases hyr : y % 8 <;> omega

/-- **Fermat's two-form theorem.** A prime `p` is `x ^ 2 + 2 * y ^ 2` for some
naturals `x, y` iff `p = 2` or `p ≡ 1, 3 (mod 8)`. -/
theorem exists_sq_add_two_mul_sq_iff {p : ℕ} (hp : p.Prime) :
    (∃ x y : ℕ, p = x ^ 2 + 2 * y ^ 2) ↔ p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact mod_eight_of_eq_sq_add_two_mul_sq hp hxy
  · rintro (h2 | h)
    · exact ⟨0, 1, by rw [h2]; norm_num⟩
    · exact exists_sq_add_two_mul_sq_of_mod_eight hp h

/-! ## The form `x^2 + 3y^2` -/

/-- A prime `p ≡ 1 (mod 3)` is of the form `x ^ 2 + 3 * y ^ 2`. -/
theorem exists_sq_add_three_mul_sq_of_mod_three {p : ℕ} (hp : p.Prime)
    (h : p % 3 = 1) : ∃ x y : ℕ, p = x ^ 2 + 3 * y ^ 2 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at h
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hsq : IsSquare (-((3 : ℕ) : ZMod p)) := by
    push_cast
    exact isSquare_neg_three_of_mod_three_eq_one h
  obtain ⟨x, y, hy, hx, hyp, ⟨k, hk⟩⟩ := exists_dvd_sq_add_mul_sq 3 hsq
  have hy2 : 0 < y ^ 2 := by positivity
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk; omega
    · exact h0
  have hk4 : k < 4 := by nlinarith
  interval_cases k
  · exact ⟨x, y, by omega⟩
  · -- `x ^ 2 + 3 y ^ 2 = 2 p` is impossible for odd `p`: the left side is `≡ 0 (mod 4)`
    -- or odd.
    exfalso
    rcases Nat.even_or_odd' x with ⟨s, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' y with ⟨t, rfl | rfl⟩ <;>
      · ring_nf at hk; omega
  · -- `x ^ 2 + 3 y ^ 2 = 3 p`: then `3 ∣ x` and `p = y ^ 2 + 3 (x / 3) ^ 2`.
    have h3x2 : 3 ∣ x ^ 2 := ⟨p - y ^ 2, by omega⟩
    obtain ⟨t, rfl⟩ := Nat.prime_three.dvd_of_dvd_pow h3x2
    exact ⟨y, t, by ring_nf at hk; omega⟩

/-- A prime of the form `x ^ 2 + 3 * y ^ 2` is `3` or `≡ 1 (mod 3)`. -/
theorem mod_three_of_eq_sq_add_three_mul_sq {p x y : ℕ} (hp : p.Prime)
    (hxy : p = x ^ 2 + 3 * y ^ 2) : p = 3 ∨ p % 3 = 1 := by
  have hmod : p % 3 = ((x % 3) ^ 2) % 3 := by
    rw [hxy]; simp [Nat.add_mod, Nat.pow_mod]
  have hx3 : x % 3 < 3 := Nat.mod_lt x (by norm_num)
  interval_cases hxr : x % 3
  · left
    have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
  · right; omega
  · right; omega

/-- **Fermat's three-form theorem.** A prime `p` is `x ^ 2 + 3 * y ^ 2` for some
naturals `x, y` iff `p = 3` or `p ≡ 1 (mod 3)`. -/
theorem exists_sq_add_three_mul_sq_iff {p : ℕ} (hp : p.Prime) :
    (∃ x y : ℕ, p = x ^ 2 + 3 * y ^ 2) ↔ p = 3 ∨ p % 3 = 1 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact mod_three_of_eq_sq_add_three_mul_sq hp hxy
  · rintro (h3 | h)
    · exact ⟨0, 1, by rw [h3]; norm_num⟩
    · exact exists_sq_add_three_mul_sq_of_mod_three hp h

/-! ## Examples -/

example : Nat.Prime 11 ∧ 11 % 8 = 3 ∧ 11 = 3 ^ 2 + 2 * 1 ^ 2 := by norm_num
example : Nat.Prime 17 ∧ 17 % 8 = 1 ∧ 17 = 3 ^ 2 + 2 * 2 ^ 2 := by norm_num
example : Nat.Prime 7 ∧ 7 % 3 = 1 ∧ 7 = 2 ^ 2 + 3 * 1 ^ 2 := by norm_num
example : Nat.Prime 13 ∧ 13 % 3 = 1 ∧ 13 = 1 ^ 2 + 3 * 2 ^ 2 := by norm_num
/-- `5 ≡ 5 (mod 8)` is not of the form `x^2 + 2y^2` (a negative instance). -/
example : ¬ ∃ x y : ℕ, 5 = x ^ 2 + 2 * y ^ 2 := by
  rw [exists_sq_add_two_mul_sq_iff (by norm_num)]; norm_num
/-- `5 ≡ 2 (mod 3)` is not of the form `x^2 + 3y^2`. -/
example : ¬ ∃ x y : ℕ, 5 = x ^ 2 + 3 * y ^ 2 := by
  rw [exists_sq_add_three_mul_sq_iff (by norm_num)]; norm_num
example : ∃ x y : ℕ, 0 < y ∧ x ^ 2 < 7 ∧ y ^ 2 < 7 ∧
    (((3 : ZMod 7) * y : ZMod 7) = x ∨ ((3 : ZMod 7) * y : ZMod 7) = -x) :=
  ⟨1, 2, by norm_num, by norm_num, by norm_num, Or.inr (by decide)⟩

end Candidates.FermatTwoThreeForms
