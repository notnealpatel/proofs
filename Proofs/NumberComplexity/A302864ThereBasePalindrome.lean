/-
# A302864 — every 2-adic valuation is attained by a decimal palindrome

OEIS A302864: every nonnegative 2-adic valuation is attained by a
positive decimal palindrome. Thus the least such palindrome, defined
as `0` if none exists, is always positive.

1. By induction there is an `n`-digit number `N` with all digits in `{1, 2}`
   and `2 ^ n ∣ N` (prepend the digit `d ∈ {1, 2}` making
   `N / 2 ^ n + d * 5 ^ n` even).
2. With `l` the little-endian digit list of `N` and `d ∈ {1, 2}`, the list
   `l ++ [d] ++ l.reverse` is a palindrome whose entries are digits and whose
   leading entry is nonzero, so it is the decimal expansion of
   `P = N + 10 ^ n * (d + 10 * rev(N))`.
3. Writing `N = 2 ^ n * q`, `P = 2 ^ n * (q + 5 ^ n * (d + 10 * rev(N)))`, and
   choosing `d = 1` for even `q` and `d = 2` for odd `q` makes the cofactor
   odd, so `v₂(P) = n` exactly.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A302864ThereBasePalindrome

/-! ## Definitions -/

/-- `P` is a base-10 palindrome: its decimal digit list reads the same
backwards (Mathlib's `List.Palindrome` on `Nat.digits 10 P`). -/
def IsPalindrome10 (P : ℕ) : Prop := List.Palindrome (Nat.digits 10 P)

/-- The positive base-10 palindromes whose binary expansion ends in exactly
`n` zeros, i.e. whose 2-adic valuation is exactly `n`. -/
def palSet (n : ℕ) : Set ℕ := {P | 0 < P ∧ IsPalindrome10 P ∧ padicValNat 2 P = n}

/-- OEIS A302864: `a n` is the smallest positive palindrome whose binary
expansion ends in exactly `n` zeros, or `0` if there is none (`sInf ∅ = 0`
on `ℕ`). -/
noncomputable def a (n : ℕ) : ℕ := sInf (palSet n)

/-! ## Basic bridges -/

/-- For positive `P`, the binary expansion of `P` ends in exactly `n` zeros
iff `2 ^ n ∣ P` and `¬ 2 ^ (n + 1) ∣ P`. -/
theorem padicValNat_two_eq_iff {P n : ℕ} (hP : P ≠ 0) :
    padicValNat 2 P = n ↔ 2 ^ n ∣ P ∧ ¬ 2 ^ (n + 1) ∣ P := by
  rw [padicValNat_dvd_iff_le hP, padicValNat_dvd_iff_le hP]
  omega

/-- A decimal palindrome test through list reversal. -/
theorem isPalindrome10_iff (P : ℕ) :
    IsPalindrome10 P ↔ (Nat.digits 10 P).reverse = Nat.digits 10 P :=
  List.Palindrome.iff_reverse_eq

/-! ## Examples -/

/-- Membership test for `palSet` through divisibility. -/
theorem mem_palSet_iff {n P : ℕ} :
    P ∈ palSet n ↔ 0 < P ∧ (Nat.digits 10 P).reverse = Nat.digits 10 P ∧
      2 ^ n ∣ P ∧ ¬ 2 ^ (n + 1) ∣ P := by
  constructor
  · rintro ⟨hpos, hpal, hv⟩
    exact ⟨hpos, (isPalindrome10_iff P).1 hpal, (padicValNat_two_eq_iff hpos.ne').1 hv⟩
  · rintro ⟨hpos, hpal, hdvd⟩
    exact ⟨hpos, (isPalindrome10_iff P).2 hpal, (padicValNat_two_eq_iff hpos.ne').2 hdvd⟩

example : a 0 = 1 := by
  apply IsLeast.csInf_eq
  refine ⟨mem_palSet_iff.2 (by norm_num), fun P hP => (mem_palSet_iff.1 hP).1⟩

example : a 1 = 2 := by
  apply IsLeast.csInf_eq
  refine ⟨mem_palSet_iff.2 (by norm_num), fun P hP => ?_⟩
  obtain ⟨hpos, -, hdvd, -⟩ := mem_palSet_iff.1 hP
  simpa using Nat.le_of_dvd hpos hdvd

example : a 2 = 4 := by
  apply IsLeast.csInf_eq
  refine ⟨mem_palSet_iff.2 (by norm_num), fun P hP => ?_⟩
  obtain ⟨hpos, -, hdvd, -⟩ := mem_palSet_iff.1 hP
  simpa using Nat.le_of_dvd hpos hdvd

example : a 3 = 8 := by
  apply IsLeast.csInf_eq
  refine ⟨mem_palSet_iff.2 (by norm_num), fun P hP => ?_⟩
  obtain ⟨hpos, -, hdvd, -⟩ := mem_palSet_iff.1 hP
  simpa using Nat.le_of_dvd hpos hdvd

example : a 4 = 272 := by
  apply IsLeast.csInf_eq
  refine ⟨mem_palSet_iff.2 (by norm_num), fun P hP => ?_⟩
  obtain ⟨hpos, hpal, h16, h32⟩ := mem_palSet_iff.1 hP
  by_contra hle
  have hlt : P < 272 := not_le.1 hle
  interval_cases P <;> simp_all

/-! ## The construction -/

/-- Step 1: for every `n` there is a little-endian digit list `l` of length
`n`, with every entry `1` or `2`, whose value `Nat.ofDigits 10 l` is divisible
by `2 ^ n`. -/
theorem exists_digits_one_two (n : ℕ) :
    ∃ l : List ℕ, l.length = n ∧ (∀ x ∈ l, x = 1 ∨ x = 2) ∧
      2 ^ n ∣ Nat.ofDigits 10 l := by
  induction n with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨l, hlen, hdig, q, hq⟩ := ih
    have hodd5 : Odd (5 ^ n) := Odd.pow (by decide)
    -- choose the new leading digit so that `q + d * 5 ^ n` is even
    obtain ⟨d, hd, hdeven⟩ : ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ Even (q + d * 5 ^ n) := by
      rcases Nat.even_or_odd q with hq' | hq'
      · refine ⟨2, Or.inr rfl, ?_⟩
        exact hq'.add (by rw [Nat.even_mul]; exact Or.inl (by decide))
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [one_mul]
        exact hq'.add_odd hodd5
    obtain ⟨r, hr⟩ := hdeven
    refine ⟨l ++ [d], by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hdig x hx
      · rw [List.mem_singleton.1 hx]; exact hd
    · have hval : Nat.ofDigits 10 (l ++ [d]) = 2 ^ n * (q + d * 5 ^ n) := by
        rw [Nat.ofDigits_append, hq, hlen, Nat.ofDigits_singleton,
          show (10 : ℕ) ^ n = 2 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
        ring
      rw [hval, hr, pow_succ]
      exact ⟨r, by ring⟩

/-- Steps 2–3: for every `n` there is a positive base-10 palindrome `P` with
`2 ^ n ∣ P` and `¬ 2 ^ (n + 1) ∣ P`. -/
theorem exists_palindrome_dvd (n : ℕ) :
    ∃ P : ℕ, 0 < P ∧ (Nat.digits 10 P).reverse = Nat.digits 10 P ∧
      2 ^ n ∣ P ∧ ¬ 2 ^ (n + 1) ∣ P := by
  obtain ⟨l, hlen, hdig, q, hq⟩ := exists_digits_one_two n
  obtain ⟨d, hd, hodd⟩ : ∃ d : ℕ, (d = 1 ∨ d = 2) ∧
      Odd (q + 5 ^ n * (d + 10 * Nat.ofDigits 10 l.reverse)) := by
    have hodd5 : Odd (5 ^ n) := Odd.pow (by decide)
    have heven10 : Even (5 ^ n * (10 * Nat.ofDigits 10 l.reverse)) :=
      (Nat.even_mul.2 (Or.inl (by decide))).mul_left _
    rcases Nat.even_or_odd q with hq' | hq'
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [mul_add, ← add_assoc, mul_one]
      exact (hq'.add_odd hodd5).add_even heven10
    · refine ⟨2, Or.inr rfl, ?_⟩
      rw [mul_add, ← add_assoc]
      have h2 : Even (5 ^ n * 2) := (even_two).mul_left _
      exact (hq'.add_even h2).add_even heven10
  set L : List ℕ := l ++ [d] ++ l.reverse with hL
  have hmemL : ∀ x ∈ L, x = 1 ∨ x = 2 := by
    intro x hx
    simp only [hL, List.mem_append, List.mem_reverse, List.mem_singleton] at hx
    rcases hx with (hx | hx) | hx
    · exact hdig x hx
    · rw [hx]; exact hd
    · exact hdig x hx
  have hdigits : Nat.digits 10 (Nat.ofDigits 10 L) = L := by
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro x hx
      rcases hmemL x hx with h | h <;> omega
    · intro hne
      rcases hmemL _ (List.getLast_mem hne) with h | h <;> omega
  have hrev : L.reverse = L := by simp [hL]
  have hval : Nat.ofDigits 10 L =
      2 ^ n * (q + 5 ^ n * (d + 10 * Nat.ofDigits 10 l.reverse)) := by
    rw [hL, List.append_assoc, Nat.ofDigits_append, hq, hlen, List.singleton_append, Nat.ofDigits_cons,
      show (10 : ℕ) ^ n = 2 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
    ring
  obtain ⟨k, hk⟩ := hodd
  refine ⟨Nat.ofDigits 10 L, ?_, by rw [hdigits, hrev], ?_, ?_⟩
  · rw [hval, hk]; positivity
  · rw [hval]; exact Dvd.intro _ rfl
  · rw [hval, hk, pow_succ]
    intro hdvd
    have h := Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd
    omega

/-- Every exponent is attained: for every `n` there is a positive base-10
palindrome `P` whose binary expansion ends in exactly `n` zeros. -/
theorem exists_mem_palSet (n : ℕ) : (palSet n).Nonempty := by
  obtain ⟨P, hP⟩ := exists_palindrome_dvd n
  exact ⟨P, mem_palSet_iff.2 hP⟩

/-- The conjecture in A302864 (unattributed): for every `n ≥ 0`,
`a(n)` is positive, since some positive decimal palindrome has
2-adic valuation exactly `n`. -/
theorem a_pos (n : ℕ) : 0 < a n :=
  (Nat.sInf_mem (exists_mem_palSet n)).1

end Candidates.A302864ThereBasePalindrome
