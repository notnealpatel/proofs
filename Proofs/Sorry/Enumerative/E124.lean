/-
Erdős Problem #124 archive. The second question and the two research claims
below remain admitted. Their historical source descriptions and proof sketches
are not independently verified here, and no inherited source-fidelity verdict
is asserted by this file.

The exact shared definitions and the global partial-sum completeness criterion
are formalized in Enumerative.E124. The two elementary arithmetic sanity checks
below are proved; they do not establish the archived completeness or necessity
claims. In particular no density estimate or BEGL proof is certified here.
-/
import Enumerative.E124

set_option autoImplicit false

/-- Archive-only compatibility: a sorted list has every earlier element
related to every later element. For natural `<`, this means strictly increasing. -/
abbrev List.Sorted {α : Type*} (r : α → α → Prop) (l : List α) : Prop :=
  l.Pairwise r

example (l : List ℕ) : l.Sorted (· < ·) ↔ l.SortedLT := by
  exact List.sortedLT_iff_pairwise.symm

namespace ErdosCandidates.E124

/-- `12 = 3^1 + 3^2` uses distinct exponents at least one. Every such
sum is divisible by three, so `4` cannot be represented. -/
example : (12 : ℕ) ∈ PowSumSet 3 1 ∧ (4 : ℕ) ∉ PowSumSet 3 1 := by
  constructor
  · refine ⟨{1, 2}, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> norm_num
    · norm_num
  · rintro ⟨S, hS, heq⟩
    have hdiv : 3 ∣ ∑ i ∈ S, (3 : ℕ) ^ i := by
      apply Finset.dvd_sum
      intro i hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := i) (by
        intro hi0
        have hpos := hS i hi
        omega)
      rw [pow_succ]
      exact dvd_mul_left 3 (3 ^ j)
    rw [← heq] at hdiv
    norm_num at hdiv

/-- Archived second-question conjecture for sorted bases at least three,
with the rational reciprocal-sum and gcd conditions. This remains admitted. -/
theorem erdos_124_second (ds : List ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hsort : ds.Sorted (· < ·)) (h3 : ∀ d ∈ ds, 3 ≤ d)
    (hsum : 1 ≤ ∑ j ∈ Finset.range ds.length,
      (1 : ℚ) / ((ds.getD j 0 : ℚ) - 1))
    (hgcd : ds.foldr Nat.gcd 0 = 1) :
    CompleteFor ds k := by
  sorry

/-- Archived `{3,4,7}` completeness claim at every positive level.
The arithmetic checks below do not prove this claim; it remains admitted. -/
theorem begl_347 (k : ℕ) (hk : 1 ≤ k) : CompleteFor [3, 4, 7] k := by
  sorry

/-- The reciprocal sum and nested gcd for `{3,4,7}` have the required
arithmetic values; this does not certify a completeness theorem. -/
example : (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 ∧
    Nat.gcd 3 (Nat.gcd 4 7) = 1 := by
  norm_num

/-- Archived necessity claim for a reciprocal sum below one.
No density or counting argument is formalized here; this remains admitted. -/
theorem pomerance_necessity (ds : List ℕ) (hsort : ds.Sorted (· < ·))
    (h3 : ∀ d ∈ ds, 3 ≤ d)
    (hsum : ∑ j ∈ Finset.range ds.length,
      (1 : ℚ) / ((ds.getD j 0 : ℚ) - 1) < 1) :
    ¬ CompleteFor ds 0 := by
  sorry

end ErdosCandidates.E124
