/-
Residues of OEIS A365771 modulo 5 (Paul D. Hanna, Oct 10 2023).

For a(n)=Catalan(n)*C(3n-1,n), let B be five times the numbers whose base-5
digits are 0 or 1 (A033042). At positive n, a(n)≡4 if n∈B and a(n)≡0
if neither n nor n-1 lies in B. For m∈B, a(m+1)≡2, including m=0.
Thus all three source residue assertions hold. The Catalan quotient formula
is bridged to the definition; Lucas's theorem supplies the digit criterion.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A365771PaulHannaCatalan

/-- A365771: `a(n) = binomial(2n+1, n)/(2n+1) * binomial(3n-1, n)`. -/
def a (n : ℕ) : ℕ := (2 * n + 1).choose n / (2 * n + 1) * (3 * n - 1).choose n

example : a 0 = 1 := by decide
example : a 1 = 2 := by decide
example : a 2 = 20 := by decide
example : a 3 = 280 := by decide
example : a 4 = 4620 := by decide
example : a 5 = 84084 := by decide

/-- Lucas's theorem for `p = 5`, one digit at a time, in `ZMod 5`. -/
theorem choose_five_mul_add (x y s r : ℕ) (hs : s < 5) (hr : r < 5) :
    ((5 * x + s).choose (5 * y + r) : ZMod 5) = (s.choose r : ZMod 5) * (x.choose y : ZMod 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 5 * x + s) (k := 5 * y + r) (p := 5)
  rw [← ZMod.natCast_eq_natCast_iff] at h
  have h1 : (5 * x + s) % 5 = s := by omega
  have h2 : (5 * y + r) % 5 = r := by omega
  have h3 : (5 * x + s) / 5 = x := by omega
  have h4 : (5 * y + r) / 5 = y := by omega
  rw [h1, h2, h3, h4] at h
  push_cast at h
  exact h

/-- `n` has all base-5 digits in `{0, 1}`, i.e. `n` is a sum of distinct powers of 5
(OEIS A033042 together with `0`). -/
def AllDigitsLeOne (n : ℕ) : Prop := ∀ d ∈ Nat.digits 5 n, d ≤ 1

/-- `AllDigitsLeOne` is decidable (bounded quantifier over a list). -/
instance (n : ℕ) : Decidable (AllDigitsLeOne n) :=
  inferInstanceAs (Decidable (∀ d ∈ Nat.digits 5 n, d ≤ 1))

/-- Membership in Hanna's set `B = 5 * {numbers whose base-5 digits are all 0 or 1}`. -/
def InB (n : ℕ) : Prop := 5 ∣ n ∧ AllDigitsLeOne (n / 5)

example : AllDigitsLeOne 0 := by simp [AllDigitsLeOne]
example : InB 0 ∧ InB 5 ∧ InB 30 ∧ InB 130 := by
  norm_num [InB, AllDigitsLeOne]
example : ¬ InB 10 ∧ ¬ InB 6 ∧ ¬ InB 55 := by
  norm_num [InB, AllDigitsLeOne]

-- Examples against A033042 (sums of distinct powers of 5): 0,1,5,6,25,26,30,31.
example : (Finset.range 32).filter AllDigitsLeOne = {0, 1, 5, 6, 25, 26, 30, 31} := by
  decide

/-- Peeling off the last base-5 digit of a positive number. -/
theorem allDigitsLeOne_five_mul_add (q r : ℕ) (hr : r < 5) (hpos : 0 < 5 * q + r) :
    AllDigitsLeOne (5 * q + r) ↔ r ≤ 1 ∧ AllDigitsLeOne q := by
  have h1 : (5 * q + r) % 5 = r := by omega
  have h2 : (5 * q + r) / 5 = q := by omega
  unfold AllDigitsLeOne
  rw [Nat.digits_def' (by norm_num) hpos, h1, h2, List.forall_mem_cons]

/-- Lucas consequence: `C(2n,n) C(3n,n) ≡ 1 (mod 5)` if all base-5 digits of `n` are
`0` or `1`, and `≡ 0` otherwise. -/
theorem centralBinom_mul_choose_three (n : ℕ) :
    ((2 * n).choose n : ZMod 5) * ((3 * n).choose n : ZMod 5) =
      if AllDigitsLeOne n then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [AllDigitsLeOne]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 5 ∧ n = 5 * q + r := ⟨n / 5, n % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [if_congr (allDigitsLeOne_five_mul_add q r hr hpos) rfl rfl]
  interval_cases r
  · have hq : q < 5 * q + 0 := by omega
    have ihq := ih q hq
    rw [show 2 * (5 * q + 0) = 5 * (2 * q) + 0 by ring, show 3 * (5 * q + 0) = 5 * (3 * q) + 0 by ring,
      choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num),
      choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num)]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, zero_le_one, true_and]
    exact ihq
  · have hq : q < 5 * q + 1 := by omega
    have ihq := ih q hq
    rw [show 2 * (5 * q + 1) = 5 * (2 * q) + 2 by ring, show 3 * (5 * q + 1) = 5 * (3 * q) + 3 by ring,
      choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num),
      choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num)]
    simp only [le_refl, true_and]
    rw [← ihq]
    have h6 : ((Nat.choose 2 1 : ℕ) : ZMod 5) * ((Nat.choose 3 1 : ℕ) : ZMod 5) = 1 := by decide
    linear_combination (((2 * q).choose q : ZMod 5) * ((3 * q).choose q : ZMod 5)) * h6
  · rw [show 3 * (5 * q + 2) = 5 * (3 * q + 1) + 1 by ring,
      choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num),
      Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2)]
    simp
  · rw [show 2 * (5 * q + 3) = 5 * (2 * q + 1) + 1 by ring,
      choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num),
      Nat.choose_eq_zero_of_lt (by norm_num : 1 < 3)]
    simp
  · rw [show 2 * (5 * q + 4) = 5 * (2 * q + 1) + 3 by ring,
      choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num),
      Nat.choose_eq_zero_of_lt (by norm_num : 3 < 4)]
    simp

/-- `binomial(2n+1, n) = (2n+1) * Catalan(n)`. -/
theorem choose_two_mul_add_one_eq (n : ℕ) :
    (2 * n + 1).choose n = (2 * n + 1) * catalan n := by
  have h1 := Nat.add_one_mul_choose_eq (2 * n) n
  have h2 := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  rw [Nat.choose_symm_half] at h1
  have h3 : (2 * n + 1).choose n * (n + 1) = (2 * n + 1) * catalan n * (n + 1) := by
    rw [← h1, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) h3

/-- The entry's definition factors as `a(n) = Catalan(n) * binomial(3n-1, n)`. -/
theorem a_eq_catalan_mul (n : ℕ) : a n = catalan n * (3 * n - 1).choose n := by
  rw [a, choose_two_mul_add_one_eq, Nat.mul_div_cancel_left _ (Nat.succ_pos _)]

/-- `3 * binomial(3n-1, n) = 2 * binomial(3n, n)` for `n ≥ 1`. -/
theorem choose_three_mul_sub_one_mul_three (n : ℕ) (hn : 0 < n) :
    (3 * n - 1).choose n * 3 = 2 * (3 * n).choose n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := Nat.choose_mul_succ_eq (3 * m + 2) (m + 1)
  rw [show 3 * (m + 1) - 1 = 3 * m + 2 by omega, show 3 * (m + 1) = 3 * m + 2 + 1 by ring]
  rw [show 3 * m + 2 + 1 - (m + 1) = 2 * (m + 1) by omega] at h
  have h' : (3 * m + 2).choose (m + 1) * 3 * (m + 1) =
      2 * (3 * m + 2 + 1).choose (m + 1) * (m + 1) := by
    calc (3 * m + 2).choose (m + 1) * 3 * (m + 1)
        = (3 * m + 2).choose (m + 1) * (3 * m + 2 + 1) := by ring
      _ = (3 * m + 2 + 1).choose (m + 1) * (2 * (m + 1)) := h
      _ = 2 * (3 * m + 2 + 1).choose (m + 1) * (m + 1) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) h'

/-- The key identity `3 (n+1) a(n) = 2 binomial(2n,n) binomial(3n,n)` for `n ≥ 1`. -/
theorem three_mul_succ_mul_a (n : ℕ) (hn : 0 < n) :
    3 * (n + 1) * a n = 2 * ((2 * n).choose n * (3 * n).choose n) := by
  have h1 := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h1
  have h2 := choose_three_mul_sub_one_mul_three n hn
  rw [a_eq_catalan_mul, ← h1]
  calc 3 * (n + 1) * (catalan n * (3 * n - 1).choose n)
      = (n + 1) * catalan n * ((3 * n - 1).choose n * 3) := by ring
    _ = (n + 1) * catalan n * (2 * (3 * n).choose n) := by rw [h2]
    _ = 2 * ((n + 1) * catalan n * (3 * n).choose n) := by ring

/-- If `n ≡ 4 (mod 5)` then `5 ∣ binomial(3n-1, n)`, hence `5 ∣ a(n)`. -/
theorem a_cast_eq_zero_of_mod_eq_four (n : ℕ) (h : n % 5 = 4) : (a n : ZMod 5) = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, n = 5 * q + 4 := ⟨n / 5, by omega⟩
  rw [a_eq_catalan_mul, show 3 * (5 * q + 4) - 1 = 5 * (3 * q + 2) + 1 by omega, Nat.cast_mul,
    choose_five_mul_add _ _ _ _ (by norm_num) (by norm_num),
    Nat.choose_eq_zero_of_lt (by norm_num : 1 < 4)]
  simp

/-- For `n ≥ 1`, `3 (n+1) a(n) ≡ 2` or `0 (mod 5)` according as all base-5 digits of `n`
lie in `{0,1}` or not. -/
theorem three_mul_succ_mul_a_cast (n : ℕ) (hn : 0 < n) :
    (3 * (n + 1) : ZMod 5) * (a n : ZMod 5) = if AllDigitsLeOne n then 2 else 0 := by
  have h := congrArg (fun x : ℕ => (x : ZMod 5)) (three_mul_succ_mul_a n hn)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  rw [h, centralBinom_mul_choose_three]
  split_ifs <;> simp

/-- Casting `5q + r` into `ZMod 5` keeps only the last digit. -/
theorem cast_five_mul_add (q r : ℕ) : ((5 * q + r : ℕ) : ZMod 5) = (r : ZMod 5) := by
  push_cast
  rw [show (5 : ZMod 5) = 0 from rfl]
  ring

/-- Reading off a residue mod 5 from the value in `ZMod 5`. -/
theorem mod_five_eq_of_cast {m : ℕ} {k : ZMod 5} (h : (m : ZMod 5) = k) : m % 5 = k.val := by
  rw [← ZMod.val_natCast, h]

/-- Hanna's part (1): `a(n) ≡ 4 (mod 5)` for `n ∈ B`, `n > 0`. -/
theorem a_mod_five_of_inB (n : ℕ) (hn : 0 < n) (hB : InB n) : a n % 5 = 4 := by
  obtain ⟨⟨q, rfl⟩, hq⟩ := hB
  have hq' : (5 * q) / 5 = q := by omega
  rw [hq'] at hq
  have hD : AllDigitsLeOne (5 * q + 0) :=
    (allDigitsLeOne_five_mul_add q 0 (by norm_num) (by omega)).2 ⟨by norm_num, hq⟩
  have h := three_mul_succ_mul_a_cast (5 * q + 0) (by omega)
  rw [if_pos hD, cast_five_mul_add] at h
  rw [show 5 * q = 5 * q + 0 from rfl]
  apply mod_five_eq_of_cast (k := 4)
  generalize (a (5 * q + 0) : ZMod 5) = x at h ⊢
  revert x
  decide

/-- Hanna's part (2) in successor form: `a(m+1) ≡ 2 (mod 5)` for every `m ∈ B`
(including `m = 0`, where `a(1) = 2`). -/
theorem a_succ_mod_five_of_inB (m : ℕ) (hB : InB m) : a (m + 1) % 5 = 2 := by
  obtain ⟨⟨q, rfl⟩, hq⟩ := hB
  have hq' : (5 * q) / 5 = q := by omega
  rw [hq'] at hq
  have hD : AllDigitsLeOne (5 * q + 1) :=
    (allDigitsLeOne_five_mul_add q 1 (by norm_num) (by omega)).2 ⟨le_refl 1, hq⟩
  have h := three_mul_succ_mul_a_cast (5 * q + 1) (by omega)
  rw [if_pos hD, cast_five_mul_add] at h
  apply mod_five_eq_of_cast (k := 2)
  generalize (a (5 * q + 1) : ZMod 5) = x at h ⊢
  revert x
  decide

/-- Hanna's part (2): `a(n) ≡ 2 (mod 5)` for `n - 1 ∈ B`, `n > 1`. -/
theorem a_mod_five_of_inB_sub_one (n : ℕ) (hn : 1 < n) (hB : InB (n - 1)) : a n % 5 = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hB
  exact a_succ_mod_five_of_inB m hB

/-- Hanna's part (3): `a(n) ≡ 0 (mod 5)` for `n > 0` with `n ∉ B` and `n - 1 ∉ B`. -/
theorem a_mod_five_of_not_inB (n : ℕ) (hn : 0 < n) (hB : ¬ InB n) (hB' : ¬ InB (n - 1)) :
    a n % 5 = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 5 ∧ n = 5 * q + r :=
    ⟨n / 5, n % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  apply mod_five_eq_of_cast (k := 0)
  by_cases h4 : r = 4
  · exact a_cast_eq_zero_of_mod_eq_four _ (by omega)
  have hD : ¬ AllDigitsLeOne (5 * q + r) := by
    rw [allDigitsLeOne_five_mul_add q r hr hn]
    rintro ⟨hr1, hq⟩
    interval_cases r
    · exact hB ⟨⟨q, rfl⟩, by rwa [show (5 * q + 0) / 5 = q by omega]⟩
    · exact hB' ⟨⟨q, by omega⟩, by rwa [show (5 * q + 1 - 1) / 5 = q by omega]⟩
  have h := three_mul_succ_mul_a_cast (5 * q + r) hn
  rw [if_neg hD, cast_five_mul_add] at h
  generalize (a (5 * q + r) : ZMod 5) = x at h ⊢
  have hr4 : r < 4 := by omega
  interval_cases r <;> revert x <;> decide

/-- **Hanna's conjecture (A365771, Paul D. Hanna, 2023)**, all three parts: with
`a(n) = Catalan(n) * binomial(3n-1, n)` and `B = 5 * {numbers whose base-5 digits are 0 or 1}`,
(1) `a(n) ≡ 4 (mod 5)` for `n ∈ B`, `n > 0`; (2) `a(n) ≡ 2 (mod 5)` for `n - 1 ∈ B`, `n > 1`;
(3) `a(n) ≡ 0 (mod 5)` for all other `n > 0`. -/
theorem hanna_conjecture :
    (∀ n : ℕ, 0 < n → InB n → a n % 5 = 4) ∧
    (∀ n : ℕ, 1 < n → InB (n - 1) → a n % 5 = 2) ∧
    (∀ n : ℕ, 0 < n → ¬ InB n → ¬ InB (n - 1) → a n % 5 = 0) :=
  ⟨a_mod_five_of_inB, a_mod_five_of_inB_sub_one, a_mod_five_of_not_inB⟩

-- Each part's hypotheses are jointly satisfiable.
example : 0 < 5 ∧ InB 5 := ⟨by norm_num, by norm_num [InB, AllDigitsLeOne]⟩
example : 1 < 6 ∧ InB (6 - 1) := ⟨by norm_num, by norm_num [InB, AllDigitsLeOne]⟩
example : 0 < 2 ∧ ¬ InB 2 ∧ ¬ InB (2 - 1) := by norm_num [InB]

-- Spot checks against the listed terms: a(5) = 84084 ≡ 4, a(6) = 1633632 ≡ 2, a(2) = 20 ≡ 0.
example : a 5 % 5 = 4 ∧ a 6 % 5 = 2 ∧ a 2 % 5 = 0 := by decide

end Candidates.A365771PaulHannaCatalan
