/-
# A136510 — every positive integer occurs in binary inside one of its powers

OEIS A136510 (entry by Reinhard Zumkeller) asks whether its least exponent
`k > 1` exists for every positive `n`: the binary representation of `n`
must occur as a contiguous substring of that of `n^k`.

Write `n = 2^e m` with `m` odd and bit length `L`. Euler's theorem gives
`m^φ(2^L) ≡ 1 [MOD 2^L]`, so `k = φ(2^L)+1 > 1` makes the low `L` bits of
`m^k` equal those of `m`. Thus `n^k` ends with `bin(m)` followed by `ek ≥ e`
zeros and contains `bin(n) = bin(m) 0^e`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A136510ThereSomeBinary

/-! ## Definitions -/

/-- The binary representation of `n` as a most-significant-bit-first list of
bits (`Nat.digits 2` is least-significant-first, so it is reversed).  For
`n = 0` this is the empty list; the entry only concerns `n ≥ 1`. -/
def binaryRep (n : ℕ) : List ℕ := (Nat.digits 2 n).reverse

/-- `ContainsInPower n k`: the binary representation of `n` occurs as a
contiguous substring (`List.IsInfix`) of the binary representation of `n ^ k`. -/
def ContainsInPower (n k : ℕ) : Prop := binaryRep n <:+: binaryRep (n ^ k)

/-- `ContainsInPower n k` is decidable (infix on lists of naturals). -/
instance (n k : ℕ) : Decidable (ContainsInPower n k) := by
  unfold ContainsInPower; infer_instance

example : binaryRep 6 = [1, 1, 0] := by decide
example : binaryRep 27 = [1, 1, 0, 1, 1] := by decide
example : ContainsInPower 3 3 ∧ ¬ ContainsInPower 3 2 := by decide

/-! ## Little-endian bridge lemmas -/

/-- For odd `m` there is an exponent `k > 1` such that the little-endian
binary digits of `m ^ k` begin with the binary digits of `m`, i.e.
`m ^ k ≡ m` modulo `2 ^ (bit length of m)`. -/
theorem exists_digits_pow_eq_append_of_odd {m : ℕ} (hm : Odd m) :
    ∃ k, 1 < k ∧ ∃ q, Nat.digits 2 (m ^ k) = Nat.digits 2 m ++ Nat.digits 2 q := by
  set L := (Nat.digits 2 m).length with hL
  have hpos : 0 < Nat.totient (2 ^ L) := Nat.totient_pos.mpr (by positivity)
  refine ⟨Nat.totient (2 ^ L) + 1, by omega, m ^ (Nat.totient (2 ^ L) + 1) / 2 ^ L, ?_⟩
  have hcop : Nat.Coprime m (2 ^ L) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have hlt : m < 2 ^ L := Nat.lt_base_pow_length_digits (by norm_num)
  have heul : m ^ Nat.totient (2 ^ L) ≡ 1 [MOD 2 ^ L] := Nat.ModEq.pow_totient hcop
  have hmod : m ^ (Nat.totient (2 ^ L) + 1) % 2 ^ L = m := by
    have h1 : m ^ (Nat.totient (2 ^ L) + 1) ≡ 1 * m [MOD 2 ^ L] := by
      rw [pow_succ]; exact heul.mul_right m
    rw [one_mul] at h1
    rw [h1, Nat.mod_eq_of_lt hlt]
  rw [Nat.digits_append_digits (by norm_num), ← hL]
  congr 1
  conv_lhs => rw [← Nat.mod_add_div (m ^ (Nat.totient (2 ^ L) + 1)) (2 ^ L)]
  rw [hmod]

/-! ## The conjecture -/

/-- **A136510 conjecture ("a(n) is defined for all n"), proved.**
For every `n ≥ 1` there is some `k > 1` such that the binary representation of
`n` occurs as a contiguous substring of the binary representation of `n ^ k`. -/
theorem exists_containsInPower (n : ℕ) (hn : 0 < n) :
    ∃ k, 1 < k ∧ ContainsInPower n k := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hm0 : 0 < m := hm.pos
  obtain ⟨k, hk, q, hq⟩ := exists_digits_pow_eq_append_of_odd hm
  refine ⟨k, hk, ?_⟩
  unfold ContainsInPower binaryRep
  rw [List.reverse_infix, mul_pow, ← pow_mul,
    Nat.digits_base_pow_mul (by norm_num) (pow_pos hm0 k),
    Nat.digits_base_pow_mul (by norm_num) hm0, hq]
  refine ⟨List.replicate (e * k - e) 0, Nat.digits 2 q, ?_⟩
  have hek : e * k = (e * k - e) + e := by
    have hle : e ≤ e * k := Nat.le_mul_of_pos_right e (by omega)
    omega
  conv_rhs => rw [hek, List.replicate_add]
  simp only [List.append_assoc]

/-- `a(n)` of A136510: the smallest `k > 1` with `ContainsInPower n k`, for
`n ≥ 1`; well defined by `exists_containsInPower`. -/
noncomputable def a (n : ℕ) (hn : 0 < n) : ℕ := Nat.find (exists_containsInPower n hn)

/-- Characterisation of `a n` as the least admissible exponent. -/
theorem a_eq_iff (n : ℕ) (hn : 0 < n) (k : ℕ) :
    a n hn = k ↔ (1 < k ∧ ContainsInPower n k) ∧
      ∀ j < k, ¬ (1 < j ∧ ContainsInPower n j) := by
  unfold a
  exact Nat.find_eq_iff _

/-- `a 1 = 2`, `a 2 = 2`, `a 3 = 3` (first listed terms). -/
example : a 1 (by norm_num) = 2 ∧ a 2 (by norm_num) = 2 ∧ a 3 (by norm_num) = 3 := by
  refine ⟨(a_eq_iff _ _ _).mpr ?_, (a_eq_iff _ _ _).mpr ?_, (a_eq_iff _ _ _).mpr ?_⟩ <;> decide

/-- `a 11 = 5`, `a 13 = 4`, `a 19 = 6` (listed terms). -/
example : a 11 (by norm_num) = 5 ∧ a 13 (by norm_num) = 4 ∧ a 19 (by norm_num) = 6 := by
  refine ⟨(a_eq_iff _ _ _).mpr ?_, (a_eq_iff _ _ _).mpr ?_, (a_eq_iff _ _ _).mpr ?_⟩ <;> decide

/-- `a 42 = 9`, `a 71 = 10`, `a 74 = 11` (listed terms). -/
example : a 42 (by norm_num) = 9 ∧ a 71 (by norm_num) = 10 ∧ a 74 (by norm_num) = 11 := by
  refine ⟨(a_eq_iff _ _ _).mpr ?_, (a_eq_iff _ _ _).mpr ?_, (a_eq_iff _ _ _).mpr ?_⟩ <;> decide

end Candidates.A136510ThereSomeBinary
