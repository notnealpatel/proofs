/-
# A077653: a scaling counterexample to the running-maximum formula

OEIS A077653, Benoit Cloitre (Dec 02 2002), with A088226.
For the recurrence `z(n) = |z(n-1)-z(n-2)-z(n-3)|`, the nonnegative seed
`(0,0,2)` has an unbounded orbit and an even running maximum. It cannot
eventually equal `floor(sqrt(n+w))` for any integer `w`, since that expression
takes arbitrarily large odd values.
This refutes the unrestricted nonnegative-seed claim, not a version
restricted to primitive seeds. A positive-seed variant is not proved here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A077653Refutation

/-- The orbit of the seed `(x, y, z)`, 0-indexed: `orb x y z n = z(n+1)` with
`z(1) = x`, `z(2) = y`, `z(3) = z`, `z(n) = |z(n-1) - z(n-2) - z(n-3)|`. -/
def orb (x y z : ℕ) : ℕ → ℕ
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Int.natAbs ((orb x y z (n + 2) : ℤ) - orb x y z (n + 1) - orb x y z n)

/-- Running maximum `M(n) = max_{1 ≤ k ≤ n} z(k)` of a 0-indexed sequence `f`
(`f i = z(i+1)`); `runMax f 0 = 0` is the empty-maximum junk value. -/
def runMax (f : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range n).sup f

/-! ## Examples -/

/-- The first 40 terms of A077653 (seed `(1,2,2)`). -/
example : (List.range 40).map (orb 1 2 2) =
    [1,2,2,1,3,0,4,1,3,2,2,3,1,4,0,5,1,4,2,3,3,2,4,1,5,0,6,1,5,2,4,3,3,4,2,5,1,6,0,7] := by
  decide

/-- The first 40 terms of A088226 (seed `(0,0,1)`). -/
example : (List.range 40).map (orb 0 0 1) =
    [0,0,1,1,0,2,1,1,2,0,3,1,2,2,1,3,0,4,1,3,2,2,3,1,4,0,5,1,4,2,3,3,2,4,1,5,0,6,1,5] := by
  decide

/-- The entry's formula `M(n) = ⌊√(n+9)⌋` for `4 < n ≤ 40`, and `M(4) ≠ ⌊√13⌋`. -/
example : (List.range 36).map (fun i => runMax (orb 1 2 2) (i + 5)) =
    (List.range 36).map (fun i => Nat.sqrt (i + 5 + 9)) ∧
    runMax (orb 1 2 2) 4 ≠ Nat.sqrt (4 + 9) := by
  decide +kernel

/-! ## Orbit structure -/

/-- Unfolding equation of the recurrence. -/
theorem orb_add_three (x y z n : ℕ) :
    orb x y z (n + 3) =
      Int.natAbs ((orb x y z (n + 2) : ℤ) - orb x y z (n + 1) - orb x y z n) := rfl

/-- One recurrence step expressed through named values of the previous three terms. -/
theorem orb_next (x y z N a b c : ℕ) (ha : orb x y z N = a) (hb : orb x y z (N + 1) = b)
    (hc : orb x y z (N + 2) = c) : orb x y z (N + 3) = Int.natAbs ((c : ℤ) - b - a) := by
  rw [orb_add_three, ha, hb, hc]

/-- Closed form of the A088226 orbit (seed `(0,0,1)`): the block starting at the
square `(k+1)²` reads `0, k+1, 1, k, 2, …`; precisely, for `j ≤ k` the terms at
indices `(k+1)² + 1 + 2j`, `(k+1)² + 2 + 2j`, `(k+1)² + 3 + 2j` are
`k+1-j`, `j+1`, `k-j`. -/
theorem block (k : ℕ) : ∀ j ≤ k,
    orb 0 0 1 ((k + 1) ^ 2 + 1 + 2 * j) = k + 1 - j ∧
    orb 0 0 1 ((k + 1) ^ 2 + 2 + 2 * j) = j + 1 ∧
    orb 0 0 1 ((k + 1) ^ 2 + 3 + 2 * j) = k - j := by
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    decide
  | succ k ih =>
    intro j hj
    induction j with
    | zero =>
      obtain ⟨h1, h2, h3⟩ := ih k le_rfl
      set N := (k + 1) ^ 2 + 1 + 2 * k with hN
      have h2' : orb 0 0 1 (N + 1) = k + 1 := by
        rw [show N + 1 = (k + 1) ^ 2 + 2 + 2 * k by omega]; exact h2
      have h3' : orb 0 0 1 (N + 2) = 0 := by
        rw [show N + 2 = (k + 1) ^ 2 + 3 + 2 * k by omega, h3]; simp
      have h1' : orb 0 0 1 N = 1 := by rw [h1]; omega
      have h4 : orb 0 0 1 (N + 3) = k + 2 := by
        rw [orb_next 0 0 1 N 1 (k + 1) 0 h1' h2' h3']; omega
      have h5 : orb 0 0 1 (N + 3 + 1) = 1 := by
        rw [orb_next 0 0 1 (N + 1) (k + 1) 0 (k + 2) h2' h3' h4]; omega
      have h6 : orb 0 0 1 (N + 3 + 2) = k + 1 := by
        rw [show N + 3 + 2 = N + 2 + 3 by omega,
          orb_next 0 0 1 (N + 2) 0 (k + 2) 1 h3' h4 h5]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [show (k + 1 + 1) ^ 2 + 1 + 2 * 0 = N + 3 by rw [hN]; ring, h4]; omega
      · rw [show (k + 1 + 1) ^ 2 + 2 + 2 * 0 = N + 3 + 1 by rw [hN]; ring, h5]
      · rw [show (k + 1 + 1) ^ 2 + 3 + 2 * 0 = N + 3 + 2 by rw [hN]; ring, h6]; omega
    | succ j ihj =>
      obtain ⟨h1, h2, h3⟩ := ihj (by omega)
      set N := (k + 1 + 1) ^ 2 + 1 + 2 * j with hN
      have h2' : orb 0 0 1 (N + 1) = j + 1 := by
        rw [show N + 1 = (k + 1 + 1) ^ 2 + 2 + 2 * j by omega]; exact h2
      have h3' : orb 0 0 1 (N + 2) = k + 1 - j := by
        rw [show N + 2 = (k + 1 + 1) ^ 2 + 3 + 2 * j by omega]; exact h3
      have h4 : orb 0 0 1 (N + 3) = j + 2 := by
        rw [orb_next 0 0 1 N (k + 1 + 1 - j) (j + 1) (k + 1 - j) h1 h2' h3']; omega
      have h5 : orb 0 0 1 (N + 3 + 1) = k - j := by
        rw [orb_next 0 0 1 (N + 1) (j + 1) (k + 1 - j) (j + 2) h2' h3' h4]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [show (k + 1 + 1) ^ 2 + 1 + 2 * (j + 1) = N + 2 by rw [hN]; ring, h3']; omega
      · rw [show (k + 1 + 1) ^ 2 + 2 + 2 * (j + 1) = N + 3 by rw [hN]; ring, h4]
      · rw [show (k + 1 + 1) ^ 2 + 3 + 2 * (j + 1) = N + 3 + 1 by rw [hN]; ring, h5]; omega

/-- Homogeneity: the orbit of `(0,0,2)` is twice the orbit of `(0,0,1)`. -/
theorem orb_double : ∀ n, orb 0 0 2 n = 2 * orb 0 0 1 n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by
    rw [orb_add_three, orb_add_three, orb_double n, orb_double (n + 1), orb_double (n + 2)]
    push_cast
    rw [show (2 * (orb 0 0 1 (n + 2) : ℤ) - 2 * orb 0 0 1 (n + 1) - 2 * orb 0 0 1 n) =
      2 * ((orb 0 0 1 (n + 2) : ℤ) - orb 0 0 1 (n + 1) - orb 0 0 1 n) by ring,
      Int.natAbs_mul]
    rfl

/-- The A088226 orbit is unbounded: it takes the value `k+1` at index `(k+1)² + 1`. -/
theorem orb001_unbounded : ¬ BddAbove (Set.range (orb 0 0 1)) := by
  rintro ⟨B, hB⟩
  have h := hB ⟨(B + 1) ^ 2 + 1 + 2 * 0, rfl⟩
  rw [(block B 0 (Nat.zero_le B)).1] at h
  omega

/-- The orbit of `(0,0,2)` is unbounded, so it satisfies the conjecture's hypothesis. -/
theorem orb002_unbounded : ¬ BddAbove (Set.range (orb 0 0 2)) := by
  rintro ⟨B, hB⟩
  apply orb001_unbounded
  refine ⟨B, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h := hB ⟨n, rfl⟩
  simp only [orb_double] at h
  omega

/-- `M(n+1) = max(z(n+1), M(n))`. -/
theorem runMax_succ (f : ℕ → ℕ) (n : ℕ) : runMax f (n + 1) = max (f n) (runMax f n) := by
  rw [runMax, Finset.range_add_one, Finset.sup_insert]
  rfl

/-- Every running maximum of the doubled orbit is even. -/
theorem even_runMax_orb002 (n : ℕ) : Even (runMax (orb 0 0 2) n) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [runMax_succ]
    rcases le_total (orb 0 0 2 n) (runMax (orb 0 0 2) n) with h | h
    · rw [max_eq_right h]; exact ih
    · rw [max_eq_left h, orb_double]; exact even_two_mul _

/-! ## The conjecture and its refutation -/

/-- **Cloitre's conjecture (A077653, Dec 02 2002).**  For all nonnegative seeds
`x, y, z` whose orbit is unbounded, there are integers `n0`, `w` with
`M(n) = ⌊√(n + w)⌋` for every `n > n0`.  `M(n)` is only defined for `n ≥ 1`,
hence the guard `1 ≤ n`; `Real.sqrt` of a negative number is the junk value
`0`, which only enlarges the conclusion, so the refutation below is of a
formally weaker (more permissive) reading than the source. -/
def Conjecture : Prop :=
  ∀ x y z : ℕ, ¬ BddAbove (Set.range (orb x y z)) →
    ∃ n0 w : ℤ, ∀ n : ℕ, 1 ≤ n → n0 < n →
      (runMax (orb x y z) n : ℤ) = ⌊Real.sqrt ((n : ℝ) + w)⌋

/-- The seed `(0,0,2)` has an unbounded orbit with even running maxima,
whereas `floor(sqrt(n+w))` takes odd values at arbitrarily large shifted
odd-square indices. This does not refute a primitive-seed restriction. -/
theorem a077653_conjecture_false : ¬ Conjecture := by
  intro hC
  obtain ⟨n0, w, hw⟩ := hC 0 0 2 orb002_unbounded
  set t : ℕ := n0.natAbs + w.natAbs + 1 with ht
  set s : ℕ := (2 * t + 1) ^ 2 with hs
  have hsq : 2 * t + 1 ≤ s := Nat.le_self_pow two_ne_zero _
  set n : ℕ := ((s : ℤ) - w).toNat with hn
  have hnw : (n : ℤ) + w = s := by omega
  have hn1 : 1 ≤ n := by omega
  have hn0 : n0 < n := by omega
  have hval := hw n hn1 hn0
  have hreal : (n : ℝ) + w = ((2 * t + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← Nat.cast_pow, ← hs]
    exact_mod_cast hnw
  rw [hreal, Real.sqrt_sq (Nat.cast_nonneg _), Int.floor_natCast] at hval
  have hodd : runMax (orb 0 0 2) n = 2 * t + 1 := by exact_mod_cast hval
  obtain ⟨r, hr⟩ := even_runMax_orb002 n
  omega

end Candidates.A077653Refutation
