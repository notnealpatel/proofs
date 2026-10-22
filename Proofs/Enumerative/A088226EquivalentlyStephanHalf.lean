/-
Block formula and shifted distance interpretation for OEIS A088226
(Ralf Stephan, Sep 23 2013).

For a(1)=a(2)=0, a(3)=1 and a(n)=|a(n-1)-a(n-2)-a(n-3)|,
 a(k²+2m+1)=m and a(k²+2m+2)=k-m for 0≤m≤k.
It follows that 2a(n+1), not 2a(n), is the smallest even distance from n
to a square. The source's unshifted literal comment fails at n=2;
Stephan's PARI formula has the same one-index shift.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A088226EquivalentlyStephanHalf

/-- OEIS A088226, 1-indexed as in the entry: `a 1 = 0`, `a 2 = 0`, `a 3 = 1`
and `a n = |a (n-1) - a (n-2) - a (n-3)|` for `n > 3`.  The value `a 0 = 0`
is outside the entry's domain and never feeds the recurrence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 => ((a (n + 3) : ℤ) - a (n + 2) - a (n + 1)).natAbs

/-- The first 30 listed terms `a 1, …, a 30`. -/
example : (List.range 30).map (fun i => a (i + 1)) =
    [0,0,1,1,0,2,1,1,2,0,3,1,2,2,1,3,0,4,1,3,2,2,3,1,4,0,5,1,4,2] := by
  decide

/-- The defining recurrence, for `n > 3`, in shifted form. -/
theorem a_add_four (n : ℕ) :
    a (n + 4) = ((a (n + 3) : ℤ) - a (n + 2) - a (n + 1)).natAbs := by
  rw [a]

/-- The defining recurrence, stated at index `n + 3` for `1 ≤ n`. -/
theorem a_add_three (n : ℕ) (hn : 1 ≤ n) :
    a (n + 3) = ((a (n + 2) : ℤ) - a (n + 1) - a n).natAbs := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  exact a_add_four j

/-- Inside one block: if `1 ≤ N` and `a N = k - 1` (both when `1 ≤ k`),
`a (N+1) = 0` and `a (N+2) = k`, then `a (N + 2m + 1) = m` and
`a (N + 2m + 2) = k - m` for every `m ≤ k`. -/
theorem block (N k : ℕ) (h0 : 1 ≤ k → 1 ≤ N ∧ a N = k - 1)
    (h1 : a (N + 1) = 0) (h2 : a (N + 2) = k) :
    ∀ m, m ≤ k → a (N + 2 * m + 1) = m ∧ a (N + 2 * m + 2) = k - m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    match m, ih, hm with
    | 0, _, _ => exact ⟨by simpa using h1, by simpa using h2⟩
    | 1, _, hm =>
      obtain ⟨hN1, hN⟩ := h0 hm
      have e3 : a (N + 3) = 1 := by
        rw [a_add_three N hN1, h2, h1, hN]
        omega
      have e4 : a (N + 4) = k - 1 := by
        rw [show N + 4 = (N + 1) + 3 by ring, a_add_three (N + 1) (by omega),
          show N + 1 + 2 = N + 3 by ring, show N + 1 + 1 = N + 2 by ring, e3, h2, h1]
        omega
      exact ⟨by simpa using e3, by simpa using e4⟩
    | m + 2, ih, hm =>
      obtain ⟨p1, q1⟩ := ih (m + 1) (by omega) (by omega)
      obtain ⟨p0, q0⟩ := ih m (by omega) (by omega)
      have e5 : a (N + 2 * (m + 2) + 1) = m + 2 := by
        rw [show N + 2 * (m + 2) + 1 = (N + 2 * m + 2) + 3 by ring,
          a_add_three _ (by omega),
          show N + 2 * m + 2 + 2 = N + 2 * (m + 1) + 2 by ring,
          show N + 2 * m + 2 + 1 = N + 2 * (m + 1) + 1 by ring, q1, p1, q0]
        omega
      have e6 : a (N + 2 * (m + 2) + 2) = k - (m + 2) := by
        rw [show N + 2 * (m + 2) + 2 = (N + 2 * (m + 1) + 1) + 3 by ring,
          a_add_three _ (by omega),
          show N + 2 * (m + 1) + 1 + 2 = N + 2 * (m + 2) + 1 by ring,
          show N + 2 * (m + 1) + 1 + 1 = N + 2 * (m + 1) + 2 by ring, e5, q1, p1]
        omega
      exact ⟨e5, e6⟩

/-- **A088226 block formula** (the entry's `%F` line, the precise form of
Ralf Stephan's Sep 23 2013 conjecture "a(n) = m/2 where m is the smallest
even distance from n to a square", up to the index shift of his PARI
program).  For all `k` and all `m ≤ k`:
`a (k^2 + 2m + 1) = m` and `a (k^2 + 2m + 2) = k - m`.  Here `k - m` is
natural subtraction, which is exact since `m ≤ k`. -/
theorem block_formula (k m : ℕ) (hm : m ≤ k) :
    a (k ^ 2 + 2 * m + 1) = m ∧ a (k ^ 2 + 2 * m + 2) = k - m := by
  induction k generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hsq, hsq1⟩ := ih k le_rfl
    have hN : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    have h0 : 1 ≤ k + 1 → 1 ≤ (k + 1) ^ 2 ∧ a ((k + 1) ^ 2) = k + 1 - 1 := by
      intro _
      refine ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.succ_ne_zero k)), ?_⟩
      rw [hN, hsq]
      omega
    have h1 : a ((k + 1) ^ 2 + 1) = 0 := by
      rw [hN, show k ^ 2 + 2 * k + 1 + 1 = k ^ 2 + 2 * k + 2 by ring, hsq1]
      omega
    have h2 : a ((k + 1) ^ 2 + 2) = k + 1 := by
      rcases k with _ | j
      · rfl
      · obtain ⟨_, hprev⟩ := ih j (by omega)
        rw [show (j + 1 + 1) ^ 2 + 2 = ((j + 1) ^ 2 + 2 * j + 2) + 3 by ring,
          a_add_three _ (by omega),
          show (j + 1) ^ 2 + 2 * j + 2 + 2 = (j + 1) ^ 2 + 2 * (j + 1) + 2 by ring,
          show (j + 1) ^ 2 + 2 * j + 2 + 1 = (j + 1) ^ 2 + 2 * (j + 1) + 1 by ring,
          hsq1, hsq, hprev]
        omega
    exact block ((k + 1) ^ 2) (k + 1) h0 h1 h2 m hm

/-- **Stephan's comment, shifted form** (Ralf Stephan, Sep 23 2013, read
with the index shift of his PARI program `a(n) = f(n-1)`): `2 * a (n + 1)`
is the smallest even distance from `n` to a square, i.e. it is attained by
some square and bounds every even distance `|n - s^2|` from below. -/
theorem stephan_shifted (n : ℕ) :
    (∃ s : ℕ, ((n : ℤ) - (s : ℤ) ^ 2).natAbs = 2 * a (n + 1)) ∧
      ∀ s : ℕ, Even ((n : ℤ) - (s : ℤ) ^ 2) →
        2 * a (n + 1) ≤ ((n : ℤ) - (s : ℤ) ^ 2).natAbs := by
  set k := Nat.sqrt n with hk
  have hlo : k ^ 2 ≤ n := Nat.sqrt_le' n
  have hhi : n < (k + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hhi' : n ≤ k ^ 2 + 2 * k := by nlinarith
  obtain ⟨j, hj⟩ : ∃ j, n = k ^ 2 + j := ⟨n - k ^ 2, by omega⟩
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · -- `n = k^2 + 2m` with `m ≤ k`: `a (n+1) = m`, nearest even-distance square `k^2`.
    have hm : m ≤ k := by omega
    have ha : a (n + 1) = m := by rw [hj]; exact (block_formula k m hm).1
    rw [ha]
    refine ⟨⟨k, by rw [hj]; push_cast; omega⟩, fun s hs => ?_⟩
    rw [hj] at hs ⊢
    push_cast at hs ⊢
    rcases Nat.lt_or_ge k s with hks | hks
    · rcases Nat.eq_or_lt_of_le hks with hks | hks
      · -- `s = k + 1`: the distance `2k + 1 - 2m` is odd.
        subst hks
        obtain ⟨r, hr⟩ := hs
        have hr' : (2 * m : ℤ) - 2 * k - 1 = r + r := by rw [← hr]; push_cast; ring
        omega
      · have hs2 : (k : ℤ) ^ 2 + 4 * k + 4 ≤ (s : ℤ) ^ 2 := by
          have hks_int : (k : ℤ) + 2 ≤ s := by exact_mod_cast hks
          nlinarith
        omega
    · have hs2 : (s : ℤ) ^ 2 ≤ (k : ℤ) ^ 2 := by
        have hks_int : (s : ℤ) ≤ k := by exact_mod_cast hks
        have hs0 : (0 : ℤ) ≤ s := by positivity
        nlinarith
      omega
  · -- `n = k^2 + 2m + 1` with `m < k`: `a (n+1) = k - m`, nearest square `(k+1)^2`.
    have hm : m + 1 ≤ k := by omega
    have ha : a (n + 1) = k - m := by
      rw [hj, show k ^ 2 + (2 * m + 1) + 1 = k ^ 2 + 2 * m + 2 by ring]
      exact (block_formula k m (by omega)).2
    rw [ha]
    refine ⟨⟨k + 1, by rw [hj]; push_cast; ring_nf; omega⟩, fun s hs => ?_⟩
    rw [hj] at hs ⊢
    push_cast at hs ⊢
    rcases Nat.lt_or_ge s k with hks | hks
    · have hs2 : (s : ℤ) ^ 2 ≤ (k : ℤ) ^ 2 - 2 * k + 1 := by
        have hks_int : (s : ℤ) ≤ k - 1 := by omega
        have hs0 : (0 : ℤ) ≤ s := by positivity
        nlinarith
      omega
    · rcases Nat.eq_or_lt_of_le hks with hks | hks
      · -- `s = k`: the distance `2m + 1` is odd.
        subst hks
        obtain ⟨r, hr⟩ := hs
        have hr' : (2 * m : ℤ) + 1 = r + r := by rw [← hr]; ring
        omega
      · have hs2 : (k : ℤ) ^ 2 + 2 * k + 1 ≤ (s : ℤ) ^ 2 := by
          have hks_int : (k : ℤ) + 1 ≤ s := by exact_mod_cast hks
          nlinarith
        omega

/-- Stephan's comment read literally with the entry's offset 1 fails at
`n = 2`: `a 2 = 0`, but `2` is not a square, so `0` is not a distance from
`2` to a square (the smallest even distance is `2`, giving `1 ≠ 0`).  This is
why `stephan_shifted` carries the index shift. -/
theorem stephan_unshifted_fails :
    ¬ ∃ s : ℕ, ((2 : ℤ) - (s : ℤ) ^ 2).natAbs = 2 * a 2 := by
  rintro ⟨s, hs⟩
  have h0 : a 2 = 0 := rfl
  rw [h0, Int.natAbs_eq_zero] at hs
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · interval_cases s <;> norm_num at hs
  · have hs2_int : (2 : ℤ) ≤ s := by exact_mod_cast hs2
    nlinarith

end Candidates.A088226EquivalentlyStephanHalf
