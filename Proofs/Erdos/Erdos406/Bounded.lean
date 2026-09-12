/-
A bounded formal result related to Erdős problem 406.  The classification below
stops at exponent 200 and makes no assertion about the open finiteness
conjecture.
-/

import Erdos.Erdos406.Certificates

set_option autoImplicit false

namespace Erdos406

/-- For every exponent at most 200, a power of two has only zero and one as
ternary digits exactly for exponents `0`, `2`, and `8`.  This is the logical
interface to the bounded certificate in `Certificates.lean`. -/
theorem zeroOneBase3_pow_two_iff_of_le_200 {n : ℕ} (hn : n ≤ 200) :
    ZeroOneBase3 (2 ^ n) ↔ n = 0 ∨ n = 2 ∨ n = 8 := by
  have hmem :
      n ∈ (Finset.range 201).filter (fun k => ZeroOneBase3 (2 ^ k)) ↔
        n ∈ ({0, 2, 8} : Finset ℕ) := by
    rw [exponents_le_200_certificate]
  have hnrange : n < 201 := by omega
  simpa only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton, hnrange, true_and] using hmem

/-- Equivalent set-theoretic form of the bounded classification: restricting
the exceptional-exponent set to `[0, 200]` gives exactly `{0, 2, 8}`. -/
theorem exceptional_exponents_inter_Iic_200 :
    {n : ℕ | ZeroOneBase3 (2 ^ n)} ∩ Set.Iic 200 = ({0, 2, 8} : Set ℕ) := by
  ext n
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzeroOne, hn⟩
    exact (zeroOneBase3_pow_two_iff_of_le_200 hn).mp hzeroOne
  · intro hn
    have hnle : n ≤ 200 := by rcases hn with rfl | rfl | rfl <;> norm_num
    exact ⟨(zeroOneBase3_pow_two_iff_of_le_200 hnle).mpr hn, hnle⟩

/-- Satisfiability and boundary audit for the bounded theorem: its hypotheses
hold at the upper endpoint, where the predicate is false. -/
example : 200 ≤ 200 ∧ ¬ ZeroOneBase3 (2 ^ 200) := by decide

end Erdos406

#check @Erdos406.zeroOneBase3_pow_two_iff_of_le_200
#print axioms Erdos406.zeroOneBase3_pow_two_iff_of_le_200
#print axioms Erdos406.exceptional_exponents_inter_Iic_200
