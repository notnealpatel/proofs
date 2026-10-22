/-
Refutation of the bound for OEIS A077199 (Amarnath Murthy, Nov 01 2002).

The least k≥2 with k and k+n squarefree is 10 at n=1857:
the shifts by 2, 3, 5, 6 and 7 all have explicit square divisors.
Both the term bound and the five-shift version are refuted.
Harvey P. Dale records n=1857 among counterexamples (May 24 2014).
The convention k≥2 follows the listed terms and the five-shift statement;
allowing k=1 would instead give a(1)=1.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A077199Refutation

/-! ## A decidable bounded form of `Squarefree` on `ℕ`

Mathlib's `Nat.instDecidablePredSquarefree` goes through `Nat.minSqFac`, which
the kernel does not reduce under `decide`.  The bounded characterization below
is used only to evaluate the examples. -/

/-- A natural number is squarefree iff it is nonzero and no `d` with
`2 ≤ d ≤ m` has `d * d ∣ m`. -/
theorem squarefree_iff_bounded (m : ℕ) :
    Squarefree m ↔ m ≠ 0 ∧ ∀ d < m + 1, 2 ≤ d → ¬ d * d ∣ m := by
  constructor
  · intro hsq
    refine ⟨hsq.ne_zero, ?_⟩
    intro d _ hd hdvd
    have hd1 : d = 1 := Nat.isUnit_iff.mp (hsq d hdvd)
    omega
  · rintro ⟨hm, hb⟩ x hx
    rw [Nat.isUnit_iff]
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hm (zero_dvd_iff.mp (by simpa only [mul_zero] using hx))
    by_contra hx1
    have hle : x * x ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hx
    have hxle : x ≤ x * x := Nat.le_mul_of_pos_left x (Nat.pos_of_ne_zero hx0)
    exact hb x (by omega) (by omega) hx

/-- A witness `d ≥ 2` with `d * d ∣ m` shows that `m` is not squarefree. -/
theorem not_squarefree_of_mul_self_dvd {m d : ℕ} (hd : 2 ≤ d) (hdvd : d * d ∣ m) :
    ¬ Squarefree m := by
  intro hsq
  have hd1 : d = 1 := Nat.isUnit_iff.mp (hsq d hdvd)
  omega

/-! ## Definition layer -/

/-- `IsA077199 n k` says that `k` is the term `a(n)` of A077199: `k` is the
smallest integer `k ≥ 2` such that both `k` and `k + n` are squarefree.
(The lower bound `2` is forced by the listed data; see the module header.) -/
def IsA077199 (n k : ℕ) : Prop :=
  2 ≤ k ∧ Squarefree k ∧ Squarefree (k + n) ∧
    ∀ j, 2 ≤ j → j < k → ¬ (Squarefree j ∧ Squarefree (j + n))

/-! ### the first ten listed terms `2,3,2,2,2,5,3,2,2,3` -/

example : IsA077199 1 2 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 2 3 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 3 2 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 4 2 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 5 2 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 6 5 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 7 3 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 8 2 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 9 2 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
example : IsA077199 10 3 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
/-- The listed term `a(22) = 7`. -/
example : IsA077199 22 7 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
/-- The listed term `a(47) = 6`. -/
example : IsA077199 47 6 := by
  simp only [IsA077199, squarefree_iff_bounded]; decide
/-- The `k ≥ 2` convention matters: `1` would otherwise qualify for `n = 1`. -/
example : Squarefree (1 : ℕ) ∧ Squarefree (1 + 1 : ℕ) := by
  simp only [squarefree_iff_bounded]; decide

/-! ## The conjecture -/

/-- The source's term-bound claim: every A077199 term at index `n≥1` is less than `10`. -/
def Conjecture : Prop :=
  ∀ n, 1 ≤ n → ∀ k, IsA077199 n k → k < 10

/-- The "i.e." clause of the A077199 conjecture: for every `n ≥ 1`, at least
one of `n+2, n+3, n+5, n+6, n+7` is squarefree. -/
def ConjectureShifts : Prop :=
  ∀ n, 1 ≤ n → Squarefree (n + 2) ∨ Squarefree (n + 3) ∨ Squarefree (n + 5) ∨
    Squarefree (n + 6) ∨ Squarefree (n + 7)

/-- The "i.e." clause implies the first clause: if for every `n ≥ 1` one of
`n+2, n+3, n+5, n+6, n+7` is squarefree, then every term `a(n)` is `< 10`. -/
theorem conjecture_of_conjectureShifts (h : ConjectureShifts) : Conjecture := by
  intro n hn k hk
  obtain ⟨_, _, _, hmin⟩ := hk
  by_contra hk10
  have hsq : ∀ j, Squarefree (n + j) → j ∈ ({2, 3, 5, 6, 7} : Finset ℕ) → False := by
    intro j hj hjmem
    have hjsq : Squarefree j := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
      rcases hjmem with rfl | rfl | rfl | rfl | rfl <;>
        · simp only [squarefree_iff_bounded]; decide
    have hj2 : 2 ≤ j := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
      omega
    have hjk : j < k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
      omega
    exact hmin j hj2 hjk ⟨hjsq, by rwa [add_comm]⟩
  rcases h n hn with h' | h' | h' | h' | h'
  · exact hsq 2 h' (by decide)
  · exact hsq 3 h' (by decide)
  · exact hsq 5 h' (by decide)
  · exact hsq 6 h' (by decide)
  · exact hsq 7 h' (by decide)

/-! ## The counterexample `n = 1857` -/

/-- None of `1859, 1860, 1862, 1863, 1864` is squarefree. -/
theorem not_squarefree_shifts_1857 :
    ¬ Squarefree (1857 + 2) ∧ ¬ Squarefree (1857 + 3) ∧ ¬ Squarefree (1857 + 5) ∧
      ¬ Squarefree (1857 + 6) ∧ ¬ Squarefree (1857 + 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1859 = 11 * 13^2
    exact not_squarefree_of_mul_self_dvd (d := 13) (by norm_num) ⟨11, by norm_num⟩
  · -- 1860 = 2^2 * 465
    exact not_squarefree_of_mul_self_dvd (d := 2) (by norm_num) ⟨465, by norm_num⟩
  · -- 1862 = 7^2 * 38
    exact not_squarefree_of_mul_self_dvd (d := 7) (by norm_num) ⟨38, by norm_num⟩
  · -- 1863 = 3^2 * 207
    exact not_squarefree_of_mul_self_dvd (d := 3) (by norm_num) ⟨207, by norm_num⟩
  · -- 1864 = 2^2 * 466
    exact not_squarefree_of_mul_self_dvd (d := 2) (by norm_num) ⟨466, by norm_num⟩

/-- `a(1857) = 10`: the smallest `k ≥ 2` with `k` and `k + 1857` both squarefree
is `10` (`10 = 2 * 5` and `1867` is prime). -/
theorem isA077199_1857 : IsA077199 1857 10 := by
  obtain ⟨h2, h3, h5, h6, h7⟩ := not_squarefree_shifts_1857
  have hsq10 : Squarefree (10 : ℕ) := by
    simp only [squarefree_iff_bounded]; decide
  have hp1867 : Nat.Prime (10 + 1857) := by norm_num
  refine ⟨by norm_num, hsq10, hp1867.squarefree, ?_⟩
  intro j hj2 hj10 hj
  obtain ⟨hjsq, hjnsq⟩ := hj
  interval_cases j
  · exact h2 hjnsq
  · exact h3 hjnsq
  · exact not_squarefree_of_mul_self_dvd (d := 2) le_rfl ⟨1, by norm_num⟩ hjsq
  · exact h5 hjnsq
  · exact h6 hjnsq
  · exact h7 hjnsq
  · exact not_squarefree_of_mul_self_dvd (d := 2) le_rfl ⟨2, by norm_num⟩ hjsq
  · exact not_squarefree_of_mul_self_dvd (d := 3) (by norm_num) ⟨1, by norm_num⟩ hjsq

/-- The A077199 bound fails at `n=1857` (Harvey P. Dale, May 24 2014):
`a(1857)=10`, since none of `1859,1860,1862,1863,1864` is squarefree. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hlt : (10 : ℕ) < 10 := hconj 1857 (by norm_num) 10 isA077199_1857
  exact lt_irrefl 10 hlt

/-- **The "i.e." form of the A077199 conjecture is false.**  At `n = 1857`
none of `1859, 1860, 1862, 1863, 1864` is squarefree. -/
theorem conjectureShifts_false : ¬ ConjectureShifts := by
  intro hconj
  obtain ⟨h2, h3, h5, h6, h7⟩ := not_squarefree_shifts_1857
  rcases hconj 1857 (by norm_num) with h | h | h | h | h
  · exact h2 h
  · exact h3 h
  · exact h5 h
  · exact h6 h
  · exact h7 h

end Candidates.A077199Refutation
