/-
# A006364: Yanev's binary-digit formula

OEIS A006364, Velin Yanev (Dec 21 2016); Ralf Stephan's description
(Oct 17 2003) as the union of `2*A001969` and `2*A001969 + 1`.
Membership means that `k/2` has even binary digit sum (A000120).
The offset is `1`, with `a(1) = 0`. A strictly increasing, surjective
explicit enumeration gives Yanev's formula for every `n ≥ 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A006364WhoseBinaryExpansion

/-! ## Definitions -/

/-- The binary digit sum `s₂(k)` (OEIS A000120). -/
def s2 (k : ℕ) : ℕ := (Nat.digits 2 k).sum

/-- Membership in A006364: the binary expansion of `k` with its last bit
removed (that is, `k / 2`) has an even number of 1's. -/
def IsMember (k : ℕ) : Prop := Even (s2 (k / 2))

instance : DecidablePred IsMember := fun k =>
  inferInstanceAs (Decidable (Even (s2 (k / 2))))

/-- `a n` is the `n`-th member of A006364 with the entry's offset 1, so
`a 1 = 0`.  The value `a 0` is a junk value (equal to `a 1`) and is never used
by the statements below, which all assume `1 ≤ n`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsMember (n - 1)

/-! ## Examples -/

example : s2 0 = 0 ∧ s2 1 = 1 ∧ s2 6 = 2 ∧ s2 7 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [s2]

example : (List.range 38).filter (fun k => decide (IsMember k)) =
    [0, 1, 6, 7, 10, 11, 12, 13, 18, 19, 20, 21, 24, 25, 30, 31, 34, 35, 36, 37] := by
  decide +kernel

/-! ## Proofs -/

/-- Appending a bit: `s₂(2j + r) = s₂(j) + r` for `r < 2`. -/
theorem s2_two_mul_add (j r : ℕ) (hr : r < 2) : s2 (2 * j + r) = s2 j + r := by
  rcases Nat.eq_zero_or_pos (2 * j + r) with h0 | hpos
  · have hj : j = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hj hr0
    simp [s2]
  · have hmod : (2 * j + r) % 2 = r := by omega
    have hdiv : (2 * j + r) / 2 = j := by omega
    simp only [s2]
    rw [Nat.digits_def' (by norm_num) hpos, List.sum_cons, hmod, hdiv]
    omega

/-- The binary digit sum of `k` is at most `k`. -/
theorem s2_le (k : ℕ) : s2 k ≤ k := Nat.digit_sum_le 2 k

/-- The explicit enumeration (zero-based): `g i = 4⌊i/2⌋ + 2 (s₂(⌊i/2⌋) mod 2) + (i mod 2)`,
i.e. `2·A001969(⌊i/2⌋) + (i mod 2)`. -/
def g (i : ℕ) : ℕ := 4 * (i / 2) + 2 * (s2 (i / 2) % 2) + i % 2

/-- `g` is strictly increasing. -/
theorem g_strictMono : StrictMono g := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : 2 * m / 2 = m := by omega
    simp only [g, h1, h2]
    omega
  · have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    simp only [g, h1, h2]
    have hb : s2 m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

/-- Every value of `g` is a member of A006364. -/
theorem isMember_g (i : ℕ) : IsMember (g i) := by
  have hdiv : g i / 2 = 2 * (i / 2) + s2 (i / 2) % 2 := by
    simp only [g]
    omega
  have hs : s2 (g i / 2) = s2 (i / 2) + s2 (i / 2) % 2 := by
    rw [hdiv]
    exact s2_two_mul_add _ _ (Nat.mod_lt _ (by norm_num))
  show Even (s2 (g i / 2))
  rw [hs, Nat.even_iff]
  omega

/-- Every member of A006364 is a value of `g`. -/
theorem mem_range_g_of_isMember (k : ℕ) (hk : IsMember k) : k ∈ Set.range g := by
  refine ⟨2 * (k / 4) + k % 2, ?_⟩
  have hi2 : (2 * (k / 4) + k % 2) / 2 = k / 4 := by omega
  have hi2' : (2 * (k / 4) + k % 2) % 2 = k % 2 := by omega
  have hk2 : k / 2 = 2 * (k / 4) + (k / 2) % 2 := by omega
  have hs : s2 (k / 2) = s2 (k / 4) + (k / 2) % 2 := by
    rw [hk2]
    have hdiv : (2 * (k / 4) + k / 2 % 2) / 2 = k / 4 := by omega
    rw [s2_two_mul_add _ _ (Nat.mod_lt _ (by norm_num))]
    omega
  have hev : (s2 (k / 4) + (k / 2) % 2) % 2 = 0 := by
    rw [← hs]
    exact Nat.even_iff.mp hk
  simp only [g, hi2, hi2']
  omega

/-- `Nat.nth IsMember` coincides with the explicit enumeration `g`. -/
theorem nth_isMember_eq_g (i : ℕ) : Nat.nth IsMember i = g i := by
  have hinf : (Set.ofPred IsMember).Infinite := by
    refine Set.infinite_of_injective_forall_mem g_strictMono.injective fun i => ?_
    exact isMember_g i
  have h := Nat.nth_comp_of_strictMono (p := IsMember) (n := i) g_strictMono
    mem_range_g_of_isMember (fun hfin => absurd hfin hinf)
  have htrue : Nat.nth (fun j => IsMember (g j)) i = i :=
    Nat.nth_of_forall fun j _ => isMember_g j
  rw [htrue] at h
  exact h.symm

/-- Parity form of `(-1)^k` in `ℤ`. -/
theorem neg_one_pow_eq (k : ℕ) : (-1 : ℤ) ^ k = 1 - 2 * ((k % 2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, Nat.even_iff.mp hk]
    norm_num
  · rw [hk.neg_one_pow, Nat.odd_iff.mp hk]
    norm_num

/-! ## The conjecture -/

/-- Yanev's formula for the offset-one enumeration of A006364:
`a(n) = 2n + (-1)^(n-s₂(n-1)) - (3+(-1)^n)/2`, for `n ≥ 1`.
Here `s₂ = A000120`; the exponent subtraction is untruncated because
`s₂(n-1) ≤ n-1`, and the integer division is exact since `3+(-1)^n ∈ {2,4}`. -/
theorem yanev_formula (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = 2 * n + (-1) ^ (n - s2 (n - 1)) - (3 + (-1) ^ n) / 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hidx : i + 1 - 1 = i := by omega
  simp only [a, hidx, nth_isMember_eq_g, g]
  have hsi : s2 i = s2 (i / 2) + i % 2 := by
    conv_lhs => rw [← Nat.div_add_mod i 2]
    exact s2_two_mul_add _ _ (Nat.mod_lt _ (by norm_num))
  have hle : s2 i ≤ i := s2_le i
  rw [neg_one_pow_eq, neg_one_pow_eq]
  push_cast
  omega

/-! ## Examples -/

-- Examples for `a`, independent of the closed form: `a 3 = 6` since `6`
-- is a member preceded by exactly two members (`0, 1`).
example : a 3 = 6 := by
  have hc : Nat.count IsMember 6 = 2 := by decide +kernel
  have hm : IsMember 6 := by decide +kernel
  simp only [a, show 3 - 1 = 2 from rfl, ← hc]
  exact Nat.nth_count hm

-- Non-vacuity: the hypothesis `1 ≤ n` is satisfiable and the formula gives the
-- listed terms `a 1 = 0`, `a 2 = 1`, `a 3 = 6`.
example : (a 1 : ℤ) = 0 ∧ (a 2 : ℤ) = 1 ∧ (a 3 : ℤ) = 6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [yanev_formula 1 le_rfl]; decide +kernel
  · rw [yanev_formula 2 (by norm_num)]; decide +kernel
  · rw [yanev_formula 3 (by norm_num)]; decide +kernel

end Candidates.A006364WhoseBinaryExpansion
