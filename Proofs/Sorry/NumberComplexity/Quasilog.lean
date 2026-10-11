import NumberComplexity.Quasilog

/-!
# Archived Cloitre upper bound for A064097

The source asserts the strict bound with natural logarithm for `1 < n`.
This is the module's single admission. The old weak theorem is derived from it,
not separately admitted. The actual sequence and all proved results remain in
`NumberComplexity.Quasilog`; production does not import this module.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- Cloitre's strict upper bound (OEIS A064097, 2002-10-30), OPEN:
`quasilog n < 2.5 * ln n` for `1 < n`. `Real.log` is the natural logarithm.
The strict guard excludes `n = 1`, where the claimed strict inequality is false,
and the junk logarithm at `n = 0`. -/
theorem quasilog_lt_two_point_five_mul_log (n : ℕ) (hn : 1 < n) :
    (quasilog n : ℝ) < 2.5 * Real.log n := by
  -- intended sorry: the strict source conjecture (card A064097-quasilog-bounds).
  sorry

/-- The original weak Cloitre upper bound, with its original name and statement,
is a consequence of the strict archived conjecture, not an independent admission. -/
theorem quasilog_le_two_point_five_mul_log (n : ℕ) (hn : 1 < n) :
    (quasilog n : ℝ) ≤ 2.5 * Real.log n :=
  le_of_lt (quasilog_lt_two_point_five_mul_log n hn)

-- Joint satisfiability is proved independently of the admission at n = 2.
example : ∃ n : ℕ, 1 < n ∧ (quasilog n : ℝ) < 2.5 * Real.log n := by
  refine ⟨2, one_lt_two, ?_⟩
  have h2 : quasilog 2 = 1 := by norm_num [quasilog_of_prime]
  rw [h2]
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  push_cast
  linarith

example : ¬((quasilog 1 : ℝ) < 2.5 * Real.log 1) := by
  norm_num [quasilog]

end NumberComplexity
