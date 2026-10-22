import Sorry.Combinatorics.SelfridgeLacampagneFamilyArithmetic
import Combinatorics.SelfridgeLacampagnePrefixComputation

set_option autoImplicit false

namespace SelfridgeLacampagne

/-- Removing one ordinary ternary digit gives its exact quotient and remainder. -/
theorem ternary01_drop_step (L : List Bool) (i : ℕ) :
    ternary01 (L.drop i) = (if L.getD i false then 1 else 0) +
      3 * ternary01 (L.drop (i + 1)) := by
  induction i generalizing L with
  | zero => cases L <;> simp [ternary01]
  | succ i ih =>
    cases L with
    | nil => simp [ternary01]
    | cons b t => simpa using ih t

/-- Five successive exact digit decompositions expose the remainder modulo `3^5`. -/
theorem ternary01_first_five (L : List Bool) :
    ternary01 L = (if L.getD 0 false then 1 else 0) +
      3 * (if L.getD 1 false then 1 else 0) +
      9 * (if L.getD 2 false then 1 else 0) +
      27 * (if L.getD 3 false then 1 else 0) +
      81 * (if L.getD 4 false then 1 else 0) + 243 * ternary01 (L.drop 5) := by
  have h0 := ternary01_drop_step L 0
  have h1 := ternary01_drop_step L 1
  have h2 := ternary01_drop_step L 2
  have h3 := ternary01_drop_step L 3
  have h4 := ternary01_drop_step L 4
  simp only [List.drop_zero, Nat.reduceAdd] at h0 h1 h2 h3 h4
  omega

/-- Powers with exponent at least five are divisible by 243. -/
theorem three_pow_mod_243 (t : ℕ) (ht : 5 ≤ t) : (3 : ℤ) ^ t % 243 = 0 := by
  have hpow : (3 : ℤ) ^ t = 243 * 3 ^ (t - 5) := by
    rw [show t = 5 + (t - 5) by omega, pow_add]
    norm_num
  rw [hpow]
  omega

/-- The exact global encoding implies the first five local column congruences. -/
theorem sparse_encoding_mod_243 (L U : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5)) :
    (4 * ternary01 U + 16 * ternary01 (L.map Bool.not) + 5) % 243 = 0 := by
  have hlen := sparse_encoding_length_lower L U m hm heq
  have hmdiv := three_pow_mod_243 m hm
  have hndiv := three_pow_mod_243 L.length (by omega)
  have hmul : ((3 : ℤ) ^ m * ternary01 (L.map Bool.not)) % 243 = 0 := by
    rw [Int.mul_emod, hmdiv]
    simp
  have hlinear : 4 * ternary01 U + 16 * ternary01 (L.map Bool.not) +
      4 * ((3 : ℤ) ^ m * ternary01 (L.map Bool.not)) + (3 : ℤ) ^ m + 5 =
        4 * (3 : ℤ) ^ L.length := by nlinarith [heq]
  omega

set_option maxHeartbeats 2000000 in
/-- The actual first five negative-sign digits of the denominator are forced by arithmetic. -/
theorem sparse_encoding_first_five (L U : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (heq : 4 * ternary01 U + 4 * ((3 : ℤ) ^ m + 4) * ternary01 (L.map Bool.not) =
      4 * (3 : ℤ) ^ L.length - ((3 : ℤ) ^ m + 5)) :
    let s := fun i => (L.map Bool.not).getD i false
    s 1 = s 0 ∧ s 2 = !(s 0) ∧ s 3 = !(s 0) ∧ s 4 = s 0 := by
  dsimp only
  have hmod := sparse_encoding_mod_243 L U m hm heq
  have hS := ternary01_first_five (L.map Bool.not)
  have hT := ternary01_first_five U
  apply sparse_first_five_residue
    ((L.map Bool.not).getD 0 false) ((L.map Bool.not).getD 1 false)
    ((L.map Bool.not).getD 2 false) ((L.map Bool.not).getD 3 false)
    ((L.map Bool.not).getD 4 false)
    (U.getD 0 false) (U.getD 1 false) (U.getD 2 false) (U.getD 3 false) (U.getD 4 false)
  omega

end SelfridgeLacampagne
