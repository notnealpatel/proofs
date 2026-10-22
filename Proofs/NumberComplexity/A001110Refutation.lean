/-
# A001110 — Ianakiev: no `a(2^k)` is a positive square plus a positive
# triangular number (refuted)

OEIS A001110, Ivan N. Ianakiev's conjecture; counterexample due to
Clément Garrot: `a(16) = 303363259914^2 + T(111868096760)`.
The refutation uses `k = 4`; minimality is not proved here.

`a` is defined exactly as in the NAME line, as the `n`-th number (from 0)
that is both a square and a triangular number.  The bridge `a_eq` identifies
it with the square of the Pell `y`-sequence for `x^2 - 8y^2 = 1`
(Mathlib's `Pell.yn` with `a = 3`), via `Pell.eq_pell`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A001110Refutation

/-! ## Definitions -/

/-- `m` is a square triangular number: a perfect square and a triangular
number `T(t) = t(t+1)/2` for some `t ≥ 0`.  The division is exact because
`t(t+1)` is even. -/
def IsSquareTriangular (m : ℕ) : Prop :=
  IsSquare m ∧ ∃ t : ℕ, m = t * (t + 1) / 2

/-- A001110 (offset 0): `a n` is the `n`-th square triangular number in
increasing order, `a 0 = 0`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsSquareTriangular n

/-- The Pell parameter `3 > 1`, giving `x^2 - 8y^2 = 1` in Mathlib's
`Pell.xn`/`Pell.yn` (there `d = 3*3 - 1`). -/
theorem one_lt_pellParam : 1 < 3 := by norm_num

/-- The Pell solutions `(xn n, yn n)` of `x^2 - 8y^2 = 1`. -/
theorem pell_eight (n : ℕ) :
    Pell.xn one_lt_pellParam n * Pell.xn one_lt_pellParam n
      - 8 * Pell.yn one_lt_pellParam n * Pell.yn one_lt_pellParam n = 1 := by
  have hd := Pell.pell_eq one_lt_pellParam 1
  rw [Pell.xn_one, Pell.yn_one] at hd
  have aux : ∀ D : ℕ, 3 * 3 - D * 1 * 1 = 1 →
      Pell.xn one_lt_pellParam n * Pell.xn one_lt_pellParam n
        - D * Pell.yn one_lt_pellParam n * Pell.yn one_lt_pellParam n = 1 →
      Pell.xn one_lt_pellParam n * Pell.xn one_lt_pellParam n
        - 8 * Pell.yn one_lt_pellParam n * Pell.yn one_lt_pellParam n = 1 := by
    intro D hD h
    have hD8 : D = 8 := by omega
    rw [hD8] at h
    exact h
  exact aux _ hd (Pell.pell_eq one_lt_pellParam n)

/-- Every natural solution of `x^2 - 8y^2 = 1` is a Pell solution
`(xn n, yn n)`. -/
theorem eq_pell_eight {x y : ℕ} (h : x * x - 8 * y * y = 1) :
    ∃ n, x = Pell.xn one_lt_pellParam n ∧ y = Pell.yn one_lt_pellParam n := by
  have hd := Pell.pell_eq one_lt_pellParam 1
  rw [Pell.xn_one, Pell.yn_one] at hd
  have aux : ∀ D : ℕ, 3 * 3 - D * 1 * 1 = 1 → x * x - D * y * y = 1 := by
    intro D hD
    have hD8 : D = 8 := by omega
    rw [hD8]
    exact h
  exact Pell.eq_pell one_lt_pellParam (aux _ hd)

/-- The square triangular numbers are exactly the squares of the Pell
`y`-sequence `0, 1, 6, 35, 204, …` (A001109). -/
theorem isSquareTriangular_iff (m : ℕ) :
    IsSquareTriangular m ↔ ∃ n, m = Pell.yn one_lt_pellParam n ^ 2 := by
  constructor
  · rintro ⟨⟨y, hy⟩, t, ht⟩
    have heven : 2 ∣ t * (t + 1) := (Nat.even_mul_succ_self t).two_dvd
    have h2m : 2 * m = t * (t + 1) := by
      rw [ht]
      exact Nat.mul_div_cancel' heven
    have hsq : (2 * t + 1) * (2 * t + 1) = 8 * y * y + 1 := by
      have hexp : (2 * t + 1) * (2 * t + 1) = 4 * (t * (t + 1)) + 1 := by ring
      rw [hexp, ← h2m, hy]
      ring
    have hpell : (2 * t + 1) * (2 * t + 1) - 8 * y * y = 1 := by
      rw [hsq]
      exact Nat.add_sub_cancel_left _ _
    obtain ⟨n, -, hyn⟩ := eq_pell_eight hpell
    exact ⟨n, by rw [hy, hyn, sq]⟩
  · rintro ⟨n, rfl⟩
    set X := Pell.xn one_lt_pellParam n with hX
    set Y := Pell.yn one_lt_pellParam n with hY
    have hpell : X * X - 8 * Y * Y = 1 := pell_eight n
    have hXX : X * X = 8 * Y * Y + 1 := by
      have hle : 8 * Y * Y ≤ X * X := by
        by_contra hlt
        rw [Nat.sub_eq_zero_of_le (le_of_not_ge hlt)] at hpell
        exact absurd hpell (by norm_num)
      omega
    have hodd : Odd (X * X) := ⟨4 * Y * Y, by rw [hXX]; ring⟩
    obtain ⟨t, ht⟩ : Odd X := (Nat.odd_mul.mp hodd).1
    refine ⟨⟨Y, sq Y⟩, t, ?_⟩
    have htt : t * (t + 1) = 2 * Y ^ 2 := by
      have h4 : 4 * (t * (t + 1)) = 4 * (2 * Y ^ 2) := by
        have hexp : X * X = 4 * (t * (t + 1)) + 1 := by rw [ht]; ring
        have h8 : 8 * Y * Y = 4 * (2 * Y ^ 2) := by ring
        omega
      omega
    rw [htt]
    omega

/-- **Bridge.** `a n = (yn n)^2`: the `n`-th square triangular number is the
square of the `n`-th Pell `y`-value for `x^2 - 8y^2 = 1`. -/
theorem a_eq (n : ℕ) : a n = Pell.yn one_lt_pellParam n ^ 2 := by
  let f : ℕ → ℕ := fun i => Pell.yn one_lt_pellParam i ^ 2
  have hf : StrictMono f := fun i j hij =>
    Nat.pow_lt_pow_left (Pell.strictMono_y one_lt_pellParam hij) two_ne_zero
  have hall : ∀ i, IsSquareTriangular (f i) := fun i =>
    (isSquareTriangular_iff (f i)).mpr ⟨i, rfl⟩
  have h0 : ∀ k, IsSquareTriangular k → k ∈ Set.range f := by
    intro k hk
    obtain ⟨i, hi⟩ := (isSquareTriangular_iff k).mp hk
    exact ⟨i, hi.symm⟩
  have hinf : (Set.ofPred IsSquareTriangular).Infinite :=
    (Set.infinite_range_of_injective hf.injective).mono (by
      rintro k ⟨i, rfl⟩
      exact hall i)
  have hcomp := Nat.nth_comp_of_strictMono (p := IsSquareTriangular) (n := n) hf h0
    (fun hfi => absurd hfi hinf)
  have htrue : (fun i => IsSquareTriangular (f i)) = fun _ => True :=
    funext fun i => eq_true (hall i)
  rw [htrue, Nat.nth_true] at hcomp
  exact hcomp.symm

/-! ## Examples -/

-- The Pell `y`-sequence is A001109 `0, 1, 6, 35, 204, 1189, …`.
example : (List.range 8).map (Pell.yn one_lt_pellParam) = [0, 1, 6, 35, 204, 1189, 6930, 40391] := by
  decide

-- A001110 against the first 17 terms of its DATA line (through `a(16)`).
example : (List.range 17).map a =
    [0, 1, 36, 1225, 41616, 1413721, 48024900, 1631432881, 55420693056,
      1882672131025, 63955431761796, 2172602007770041, 73804512832419600,
      2507180834294496361, 85170343853180456676, 2893284510173841030625,
      98286503002057414584576] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, a_eq]
  decide

/-! ## The conjecture and its refutation -/

/-- Ianakiev’s conjecture (A001110): no `a(2^k)`, `k ≥ 0`, is a positive
square plus a positive triangular number. A positive square is `s²`,
`0 < s`; a positive triangular number is `t(t+1)/2`, `0 < t`. The division
is exact since `t(t+1)` is even. -/
def Conjecture : Prop :=
  ∀ k : ℕ, ¬ ∃ s t : ℕ, 0 < s ∧ 0 < t ∧ a (2 ^ k) = s ^ 2 + t * (t + 1) / 2

/-- `a(16) = 98286503002057414584576`. -/
theorem a_sixteen : a 16 = 98286503002057414584576 := by
  rw [a_eq]
  decide

/-- Garrot’s counterexample to Ianakiev’s conjecture (OEIS A001110):
`a(16) = 98286503002057414584576 = 303363259914^2 + T(111868096760)`,
at `k = 4`. Minimality of this counterexample is not proved here. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  refine hconj 4 ⟨303363259914, 111868096760, by norm_num, by norm_num, ?_⟩
  rw [show (2 : ℕ) ^ 4 = 16 by norm_num, a_sixteen]
  norm_num

end Candidates.A001110Refutation
