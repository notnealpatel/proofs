/-
# A363166 — Bouton numbers and A063915

Alan Michael Gómez Calderón (OEIS A363166, Sep 18 2025) conjectured
`a(n) = A000217(n) - A063915(n-1)` for `n ≥ 1`. Bouton numbers count
unordered P-positions of three-heap Nim with nonzero heaps at most `n`.
A063915 is defined below by Kevin Ryde's closed form (Nov 27 2020).

## Proof outline

P-positions are unordered triples `{x < y < z}` of distinct positive heap sizes
with `x ^^^ y ^^^ z = 0` (zero Nim sum forces distinctness once heaps are
nonzero, so sets and multisets agree).  Fibre over the largest heap `z`: the
fibre is `{x < z : x < x ^^^ z < z}`.  Write `z = 2^k + r` with
`r < 2^k`.  Such `x` are exactly the `x < 2^k` with `x ^^^ r < r`, and
`x ↦ x ^^^ r` is a bijection from them onto `[0, r)`.  So the fibre has
`z - 2^⌊log₂ z⌋` elements, and summing gives `T(n) - ∑_{j ≤ n} msb j`.
Ryde's closed form of A063915 telescopes to `∑_{j ≤ m+1} msb j`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A363166CountSetsHeap

/-! ## Definitions -/

/-- A363166 (Bouton numbers): the number of P-positions of three-heap Nim with
nonzero heaps of size at most `n`, counted as sets `{x < y < z} ⊆ [1, n]` with
Nim sum `x ^^^ y ^^^ z = 0`. -/
def bouton (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 ^^^ t.2.1 ^^^ t.2.2 = 0).card

/-- A063915, by Kevin Ryde's closed form from the entry:
`a(m) = (m+2) 2^k - (2·4^k + 1)/3` with `k = ⌊log₂(m+2)⌋`.

The division is exact (`4^k ≡ 1 mod 3`) and the natural subtraction never
truncates (`(m+2) 2^k ≥ 4^k`); `a063915_eq_sum` identifies this with the
partial sums of A053644, so no junk value enters. -/
def a063915 (m : ℕ) : ℕ :=
  (m + 2) * 2 ^ Nat.log 2 (m + 2) - (2 * 4 ^ Nat.log 2 (m + 2) + 1) / 3

-- The first 16 listed terms of A363166 (offset 1), covering the
-- plateaus at `n = 7, 8` and `n = 15, 16`.
example : (List.range 16).map (fun i => bouton (i + 1)) =
    [0, 0, 1, 1, 2, 4, 7, 7, 8, 10, 13, 17, 22, 28, 35, 35] := by
  decide +kernel

-- The 55 listed terms of A063915 (offset 0).
example : (List.range 55).map a063915 =
    [1, 3, 5, 9, 13, 17, 21, 29, 37, 45, 53, 61, 69, 77, 85, 101, 117, 133, 149,
      165, 181, 197, 213, 229, 245, 261, 277, 293, 309, 325, 341, 373, 405, 437,
      469, 501, 533, 565, 597, 629, 661, 693, 725, 757, 789, 821, 853, 885, 917,
      949, 981, 1013, 1045, 1077, 1109] := by
  decide +kernel

/-! ## Bit lemmas -/

/-- Adding a value below `2^k` to `2^k` is the same as xoring it in. -/
theorem two_pow_xor_eq_add {k w : ℕ} (hw : w < 2 ^ k) : 2 ^ k ^^^ w = 2 ^ k + w := by
  have hor : 2 ^ k + w = 2 ^ k ||| w := by
    simpa using Nat.two_pow_add_eq_or_of_lt (i := k) hw 1
  rw [hor]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hik : k = i
  · subst hik
    have hwk : w.testBit k = false := Nat.testBit_lt_two_pow hw
    simp [hwk]
  · simp [hik]

/-- Zero Nim sum of three heaps determines the middle heap: `a ^^^ b ^^^ c = 0`
iff `b = a ^^^ c`. -/
theorem xor_xor_eq_zero_iff (a b c : ℕ) : a ^^^ b ^^^ c = 0 ↔ b = a ^^^ c := by
  constructor
  · intro h
    have hab : a ^^^ b = c := Nat.eq_of_xor_eq_zero h
    rw [← hab, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · rintro rfl
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_self]

/-! ## The fibre count (load-bearing step) -/

/-- For `z ≥ 1`, the number of `x < z` with `x < x ^^^ z < z` (P-positions whose
largest heap is `z`) equals `z - 2^⌊log₂ z⌋`, i.e. `z - A053644(z)`. -/
theorem card_filter_xor_lt (z : ℕ) (hz : 1 ≤ z) :
    ((Finset.range z).filter fun x => x < x ^^^ z ∧ x ^^^ z < z).card
      = z - 2 ^ Nat.log 2 z := by
  set k := Nat.log 2 z with hk
  set P := 2 ^ k with hPdef
  have hPz : P ≤ z := Nat.pow_log_le_self 2 (by omega)
  have hz2 : z < 2 * P := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) z
    rw [pow_succ, ← hk, ← hPdef] at h
    omega
  set r := z - P with hrdef
  have hr : r < P := by omega
  have hzx : z = P ^^^ r := by rw [hPdef, two_pow_xor_eq_add hr]; omega
  have hxz : ∀ x, x ^^^ z = P ^^^ (x ^^^ r) := by
    intro x
    rw [hzx, ← Nat.xor_assoc, Nat.xor_comm x P, Nat.xor_assoc]
  have hset : ((Finset.range z).filter fun x => x < x ^^^ z ∧ x ^^^ z < z)
      = (Finset.range P).filter fun x => x ^^^ r < r := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hxlt, hxy, hyz⟩
      by_cases hxP : x < P
      · have hxr : x ^^^ r < P := Nat.xor_lt_two_pow hxP hr
        rw [hxz, hPdef, two_pow_xor_eq_add hxr] at hyz
        exact ⟨hxP, by omega⟩
      · -- a smallest heap carrying the top bit of `z` would exceed the middle heap
        exfalso
        obtain ⟨x', hx'def⟩ : ∃ x', x' = x - P := ⟨_, rfl⟩
        have hx' : x' < P := by omega
        have hxeq : x = P ^^^ x' := by rw [hPdef, two_pow_xor_eq_add hx']; omega
        have hy : x ^^^ z = x' ^^^ r := by
          rw [hxz, hxeq, ← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        have hlt : x' ^^^ r < P := Nat.xor_lt_two_pow hx' hr
        omega
    · rintro ⟨hxP, hxr⟩
      have hxr' : x ^^^ r < P := Nat.xor_lt_two_pow hxP hr
      rw [hxz, hPdef, two_pow_xor_eq_add hxr']
      omega
  rw [hset]
  have hcard : ((Finset.range P).filter fun x => x ^^^ r < r).card
      = (Finset.range r).card := by
    apply Finset.card_nbij' (fun x => x ^^^ r) (fun y => y ^^^ r)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_range,
        Set.mem_Iio] at hx ⊢
      exact hx.2
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_range,
        Set.mem_Iio] at hy ⊢
      refine ⟨Nat.xor_lt_two_pow (by omega) hr, ?_⟩
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      exact hy
    · intro x _
      simp
    · intro y _
      simp
  rw [hcard, Finset.card_range]

/-- Fibre decomposition over the largest heap: `a(n)` is the sum over `z ∈ [1, n]`
of the number of `x < z` with `x < x ^^^ z < z`. -/
theorem bouton_eq_sum (n : ℕ) :
    bouton n = ∑ z ∈ Finset.Icc 1 n,
      ((Finset.range z).filter fun x => x < x ^^^ z ∧ x ^^^ z < z).card := by
  unfold bouton
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t.2.2) (t := Finset.Icc 1 n)]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.mem_Icc] at hz
    apply Finset.card_nbij' (fun t => t.1) (fun x => (x, x ^^^ z, z))
    · rintro ⟨x, y, w⟩ ht
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Set.mem_ofPred_eq, xor_xor_eq_zero_iff] at ht ⊢
      obtain ⟨⟨⟨⟨_, _⟩, -, -, -⟩, hxy, hyw, rfl⟩, rfl⟩ := ht
      exact ⟨Finset.mem_range.mpr (by omega), hxy, hyw⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Set.mem_ofPred_eq, xor_xor_eq_zero_iff, Finset.mem_range] at hx ⊢
      obtain ⟨hxz, hxy, hyz⟩ := hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [Nat.zero_xor] at hyz
        omega
      exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hz.1, hz.2⟩, hxy, hyz, trivial⟩,
        trivial⟩
    · rintro ⟨x, y, w⟩ ht
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Set.mem_ofPred_eq, xor_xor_eq_zero_iff] at ht
      obtain ⟨⟨-, -, -, rfl⟩, rfl⟩ := ht
      rfl
    · intro x _
      rfl
  · rintro ⟨x, y, w⟩ ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc] at ht ⊢
    exact ht.1.2.2

/-! ## Ryde's closed form of A063915 as partial sums of A053644 -/

/-- Cleared-denominator form of Ryde's formula: with `k = ⌊log₂(m+2)⌋`,
`3 ∑_{j=1}^{m+1} 2^⌊log₂ j⌋ + 2·4^k + 1 = 3 (m+2) 2^k`. -/
theorem sum_msb_closed (m : ℕ) :
    3 * ∑ j ∈ Finset.Icc 1 (m + 1), 2 ^ Nat.log 2 j + 2 * 4 ^ Nat.log 2 (m + 2) + 1
      = 3 * (m + 2) * 2 ^ Nat.log 2 (m + 2) := by
  induction m with
  | zero =>
    have hl2 : Nat.log 2 2 = 1 := by simpa using Nat.log_pow (b := 2) (by norm_num) 1
    simp [hl2]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set k := Nat.log 2 (m + 2) with hk
    have h1 : 2 ^ k ≤ m + 2 := Nat.pow_log_le_self 2 (by omega)
    have h2 : m + 2 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h4 : ∀ j, 4 ^ j = 2 ^ j * 2 ^ j := fun j => by
      rw [← mul_pow]
      norm_num
    rcases Nat.lt_or_ge (m + 3) (2 ^ (k + 1)) with hlt | hge
    · -- `m + 3` has the same top bit as `m + 2`
      have hlog : Nat.log 2 (m + 1 + 2) = k :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
      rw [hlog]
      rw [h4] at ih ⊢
      zify at ih ⊢
      linear_combination ih
    · -- `m + 3` is a power of two
      have heq : m + 3 = 2 ^ (k + 1) := by omega
      have hlog : Nat.log 2 (m + 1 + 2) = k + 1 := by
        rw [show m + 1 + 2 = m + 3 by omega, heq, Nat.log_pow (by norm_num)]
      rw [hlog]
      rw [h4] at ih ⊢
      rw [pow_succ] at heq ⊢
      zify at ih heq ⊢
      linear_combination ih - 3 * (2 : ℤ) ^ k * heq

/-- A063915 (Ryde's closed form) equals the partial sums of A053644:
`A063915(m) = ∑_{j=1}^{m+1} 2^⌊log₂ j⌋`. -/
theorem a063915_eq_sum (m : ℕ) :
    a063915 m = ∑ j ∈ Finset.Icc 1 (m + 1), 2 ^ Nat.log 2 j := by
  have h := sum_msb_closed m
  unfold a063915
  generalize ∑ j ∈ Finset.Icc 1 (m + 1), 2 ^ Nat.log 2 j = S at h ⊢
  generalize 4 ^ Nat.log 2 (m + 2) = Q at h ⊢
  rw [mul_assoc] at h
  generalize (m + 2) * 2 ^ Nat.log 2 (m + 2) = A at h ⊢
  omega

/-- Gauss: `2 ∑_{z=1}^{n} z = n (n+1)`. -/
theorem sum_Icc_id_mul_two (n : ℕ) : (∑ z ∈ Finset.Icc 1 n, z) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    ring

/-! ## The conjecture -/

/-- **Gómez Calderón's conjecture for A363166 (Sep 18 2025).**

For every `n ≥ 1`, the number of P-positions `{x < y < z}` of three-heap Nim
with nonzero heaps at most `n` equals `n(n+1)/2 - A063915(n-1)`, with A063915
given by Ryde's closed form.  The statement is in `ℤ` (cast before
subtracting); the guard `1 ≤ n` keeps `n - 1` off its truncated value and is
load-bearing: at `n = 0` the right side is `0 - A063915(0) = -1`. -/
theorem bouton_eq_triangular_sub_a063915 (n : ℕ) (hn : 1 ≤ n) :
    (bouton n : ℤ) = ((n * (n + 1) / 2 : ℕ) : ℤ) - (a063915 (n - 1) : ℤ) := by
  have hmsb : ∀ z ∈ Finset.Icc 1 n, 2 ^ Nat.log 2 z ≤ z := fun z hz =>
    Nat.pow_log_le_self 2 (by rw [Finset.mem_Icc] at hz; omega)
  have hsum : bouton n = ∑ z ∈ Finset.Icc 1 n, (z - 2 ^ Nat.log 2 z) := by
    rw [bouton_eq_sum]
    apply Finset.sum_congr rfl
    intro z hz
    exact card_filter_xor_lt z (Finset.mem_Icc.mp hz).1
  have hT : n * (n + 1) / 2 = ∑ z ∈ Finset.Icc 1 n, z := by
    have hgauss := sum_Icc_id_mul_two n
    omega
  have hA : a063915 (n - 1) = ∑ z ∈ Finset.Icc 1 n, 2 ^ Nat.log 2 z := by
    rw [a063915_eq_sum, Nat.sub_add_cancel hn]
  rw [hsum, hT, hA, Nat.cast_sum, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Nat.cast_sub (hmsb z hz)]

/-! ## Examples -/

-- Satisfiability / non-vacuity: the hypothesis holds at `n = 3`, where the
-- unique P-position is `{1, 2, 3}`.
example : (bouton 3 : ℤ) = ((3 * (3 + 1) / 2 : ℕ) : ℤ) - (a063915 (3 - 1) : ℤ) :=
  bouton_eq_triangular_sub_a063915 3 (by norm_num)

-- The guard `1 ≤ n` is load-bearing: the identity fails at `n = 0`.
example : (bouton 0 : ℤ) ≠ ((0 * (0 + 1) / 2 : ℕ) : ℤ) - (a063915 (0 - 1) : ℤ) := by
  decide +kernel

end Candidates.A363166CountSetsHeap
