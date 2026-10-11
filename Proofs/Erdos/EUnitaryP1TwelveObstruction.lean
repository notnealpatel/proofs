import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace EUnitaryP1

/-- Positive unitary divisors of an exponent: divisors `d` with coprime complementary divisor. -/
def exponentDivisors (a : ℕ) : Finset ℕ :=
  a.divisors.filter fun d => Nat.Coprime d (a / d)

/-- The normalized local exponential-unitary sum at base `p` and exponent `a`.
At exponent zero the sum is empty; uses of the local ratio require a positive exponent. -/
def localA (p a : ℕ) : ℕ :=
  ∑ d ∈ exponentDivisors a, p ^ (d - 1)

/-- Actual exponential-unitary divisor sum, multiplied over the actual prime factorization.
The explicit convention at zero is zero; exponent zero supplies no local term. -/
def sigmaEU (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, ∑ d ∈ exponentDivisors (n.factorization p), p ^ d

example : exponentDivisors 0 = ∅ := by simp [exponentDivisors]
example : exponentDivisors 1 = {1} := by simp [exponentDivisors]
example : localA 2 12 = 2061 := by decide
example : sigmaEU 0 = 0 := rfl
example : sigmaEU 1 = 1 := by simp [sigmaEU]

/-- A positive unitary exponent divisor is positive and divides its exponent. -/
theorem exponentDivisors_mem {a d : ℕ} (hd : d ∈ exponentDivisors a) :
    0 < d ∧ d ∣ a ∧ Nat.Coprime d (a / d) := by
  have hm := Finset.mem_filter.mp hd
  exact ⟨Nat.pos_of_mem_divisors hm.1, (Nat.mem_divisors.mp hm.1).1, hm.2⟩

/-- The local exponential-unitary sum is `p` times its normalized sum. -/
theorem local_sum_eq (p a : ℕ) :
    (∑ d ∈ exponentDivisors a, p ^ d) = p * localA p a := by
  rw [localA, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hpos := (exponentDivisors_mem hd).1
  rw [← pow_succ', Nat.sub_add_cancel hpos]

/-- On an actual prime power of positive exponent, the defined divisor sum equals
`p` times the normalized local sum. -/
theorem sigmaEU_prime_pow (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    sigmaEU (p ^ a) = p * localA p a := by
  have hn : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hf : (p ^ a).factorization p = a := by
    simp [Nat.factorization_pow, hp.factorization]
  rw [sigmaEU, if_neg hn, Nat.primeFactors_pow p (Nat.ne_of_gt ha), hp.primeFactors]
  simp only [Finset.prod_singleton, hf]
  exact local_sum_eq p a

/-- Exponent-one decoration has normalized local sum one. -/
theorem localA_one (p : ℕ) : localA p 1 = 1 := by
  have hd : exponentDivisors 1 = {1} := by decide
  simp [localA, hd]

/-- Exponent two has normalized local sum `p+1`. -/
theorem localA_two (p : ℕ) : localA p 2 = p + 1 := by
  have hd : exponentDivisors 2 = {1, 2} := by decide
  simp [localA, hd, Nat.add_comm]

example : sigmaEU 4 = 6 := by
  have h := sigmaEU_prime_pow 2 2 (by decide) (by decide)
  rw [localA_two] at h
  exact h

/-- The exact exceptional base-two local factor. -/
theorem localA_two_twelve : localA 2 12 = 2061 := by decide

/-- The two small base-three boundary factors from the reviewed proof. -/
theorem localA_three_five : localA 3 5 = 82 := by decide

/-- At exponent six the base-three factor consumes eight factors of two. -/
theorem localA_three_six : localA 3 6 = 256 := by decide

private theorem prime_dvd_prod_iff (p : ℕ) (hp : p.Prime) (S : Finset ℕ) :
    p ∣ ∏ q ∈ S, q ↔ ∃ q ∈ S, p ∣ q := by
  induction S using Finset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | @insert q S hq ih => simp [Finset.prod_insert hq, hp.dvd_mul, ih]

/-- A prime divisor of a product of distinct prime bases must be one of those bases. -/
theorem prime_mem_of_dvd_prod {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) (hd : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  obtain ⟨q, hq, hpq⟩ := (prime_dvd_prod_iff p hp S).mp hd
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hpq
  simpa only [heq] using hq

/-- The normalized perfectness identity forces any numerator prime other than two or three
into the square-exponent support. This does not assume a support size or exponent bound. -/
theorem normalized_force_prime (b : ℕ) (S : Finset ℕ) (_hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime) (p : ℕ) (hp : p.Prime)
    (h2 : p ≠ 2) (h3 : p ≠ 3)
    (hid : 2061 * localA 3 b * (∏ q ∈ S, (q + 1)) =
      2 ^ 12 * 3 ^ (b - 1) * (∏ q ∈ S, q))
    (hd : p ∣ 2061 * localA 3 b * (∏ q ∈ S, (q + 1))) : p ∈ S := by
  rw [hid] at hd
  have hn2 : ¬ p ∣ 2 ^ 12 := by
    intro h
    have hbase := hp.dvd_of_dvd_pow h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hbase)
  have hn3 : ¬ p ∣ 3 ^ (b - 1) := by
    intro h
    have hbase := hp.dvd_of_dvd_pow h
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hbase)
  have hprod : p ∣ ∏ q ∈ S, q := by
    rcases hp.dvd_mul.mp hd with hleft | hright
    · rcases hp.dvd_mul.mp hleft with htwo | hthree
      · exact False.elim (hn2 htwo)
      · exact False.elim (hn3 hthree)
    · exact hright
  exact prime_mem_of_dvd_prod hp S hS hprod

/-- All three forced bases in the reviewed argument follow from the unrestricted
normalized identity. -/
theorem normalized_forced_bases (b : ℕ) (S : Finset ℕ) (hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime)
    (hid : 2061 * localA 3 b * (∏ q ∈ S, (q + 1)) =
      2 ^ 12 * 3 ^ (b - 1) * (∏ q ∈ S, q)) :
    229 ∈ S ∧ 5 ∈ S ∧ 23 ∈ S := by
  have h229 : 229 ∈ S := normalized_force_prime b S hb hS 229 (by norm_num)
    (by decide) (by decide) hid
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 229 ∣ 2061) _) _)
  have hfactor : 230 ∣ ∏ q ∈ S, (q + 1) := by
    simpa using Finset.dvd_prod_of_mem (fun q : ℕ => q + 1) h229
  have h5 : 5 ∈ S := normalized_force_prime b S hb hS 5 (by decide)
    (by decide) (by decide) hid
    (dvd_mul_of_dvd_right ((by decide : 5 ∣ 230).trans hfactor) _)
  have h23 : 23 ∈ S := normalized_force_prime b S hb hS 23 (by decide)
    (by decide) (by decide) hid
    (dvd_mul_of_dvd_right ((by decide : 23 ∣ 230).trans hfactor) _)
  exact ⟨h229, h5, h23⟩

example : (∀ q ∈ ({5, 23, 229} : Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3) ∧
    0 < (5 : ℕ) := by norm_num

private theorem three_coprime_prod (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 3) : Nat.Coprime 3 (∏ q ∈ S, q) := by
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
  intro hd
  have hm := prime_mem_of_dvd_prod (by decide : Nat.Prime 3) S
    (fun q hq => (hS q hq).1) hd
  exact (hS 3 hm).2 rfl

/-- Exact removal of the three forced square-exponent bases from a prime support. -/
theorem forced_product_split (S : Finset ℕ) (hf : 229 ∈ S ∧ 5 ∈ S ∧ 23 ∈ S) :
    (∏ q ∈ S, (q + 1)) = 33120 * (∏ q ∈ S \ {229, 5, 23}, (q + 1)) ∧
    (∏ q ∈ S, q) = 26335 * (∏ q ∈ S \ {229, 5, 23}, q) := by
  have hsub : ({229, 5, 23} : Finset ℕ) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.1
    · exact hf.2.1
    · exact hf.2.2
  constructor
  · have heq := Finset.prod_sdiff (f := fun q : ℕ => q + 1) hsub
    norm_num [Finset.prod_insert, Finset.prod_singleton] at heq
    simpa only [Nat.mul_comm] using heq.symm
  · have heq := Finset.prod_sdiff (f := fun q : ℕ => q) hsub
    norm_num [Finset.prod_insert, Finset.prod_singleton] at heq
    simpa only [Nat.mul_comm] using heq.symm

/-- The normalized identity already forces `5 ≤ b`; no exponent cap is assumed. -/
theorem normalized_five_le (b : ℕ) (S : Finset ℕ) (hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 3)
    (hid : 2061 * localA 3 b * (∏ q ∈ S, (q + 1)) =
      2 ^ 12 * 3 ^ (b - 1) * (∏ q ∈ S, q)) : 5 ≤ b := by
  have hf := normalized_forced_bases b S hb (fun q hq => (hS q hq).1) hid
  have hsplit := forced_product_split S hf
  have h81 : 81 ∣ 2061 * localA 3 b * (∏ q ∈ S, (q + 1)) := by
    rw [hsplit.1]
    refine ⟨842720 * localA 3 b * (∏ q ∈ S \ {229, 5, 23}, (q + 1)), ?_⟩
    ring
  rw [hid] at h81
  have hco : Nat.Coprime 81 (2 ^ 12 * (∏ q ∈ S, q)) := by
    have h3 := (show Nat.Coprime 3 2 from by decide).pow_right 12
    have hp := three_coprime_prod S hS
    simpa using (h3.mul_right hp).pow_left 4
  have hpower : 81 ∣ 3 ^ (b - 1) := by
    apply hco.dvd_of_dvd_mul_right
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h81
  have hle : 4 ≤ b - 1 := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 3)).mp hpower
  omega

/-- The unrestricted normalized identity is impossible at every exponent below five. -/
theorem normalized_ne_of_lt_five (b : ℕ) (S : Finset ℕ) (hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 3) (hlt : b < 5) :
    2061 * localA 3 b * (∏ q ∈ S, (q + 1)) ≠
      2 ^ 12 * 3 ^ (b - 1) * (∏ q ∈ S, q) := by
  intro hid
  have hle := normalized_five_le b S hb hS hid
  omega

example : (∀ q ∈ (∅ : Finset ℕ), q.Prime ∧ q ≠ 2 ∧ q ≠ 3) ∧
    0 < (1 : ℕ) ∧ Squarefree (1 : ℕ) ∧ Nat.Coprime 1 (6 * ∏ q ∈ (∅ : Finset ℕ), q) := by
  simp

/-- Exact integer residual identity after cancelling the three forced bases.
The exponent lower bound is proved from the identity, not supplied as a premise. -/
theorem normalized_residual_identity (b : ℕ) (S : Finset ℕ) (hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 3)
    (hid : 2061 * localA 3 b * (∏ q ∈ S, (q + 1)) =
      2 ^ 12 * 3 ^ (b - 1) * (∏ q ∈ S, q)) :
    localA 3 b * (∏ q ∈ S \ {229, 5, 23}, (q + 1)) =
      128 * 3 ^ (b - 5) * (∏ q ∈ S \ {229, 5, 23}, q) := by
  have hfive := normalized_five_le b S hb hS hid
  have hf := normalized_forced_bases b S hb (fun q hq => (hS q hq).1) hid
  have hsplit := forced_product_split S hf
  have he : b - 1 = 4 + (b - 5) := by omega
  have hpow : 3 ^ (b - 1) = 81 * 3 ^ (b - 5) := by rw [he, pow_add]; norm_num
  rw [hsplit.1, hsplit.2, hpow] at hid
  ring_nf at hid ⊢
  omega

/-- The residual support is odd when the original prime support excludes two. -/
theorem residual_prod_odd (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2) :
    ¬ 2 ∣ ∏ q ∈ S \ {229, 5, 23}, q := by
  intro hd
  have hm := prime_mem_of_dvd_prod (by decide : Nat.Prime 2)
    (S \ {229, 5, 23}) (fun q hq => (hS q (Finset.mem_sdiff.mp hq).1).1) hd
  exact (hS 2 (Finset.mem_sdiff.mp hm).1).2 rfl

/-- The unrestricted normalized identity is impossible at exponent six:
its local factor has eight factors of two, but the residual right side has only seven. -/
theorem normalized_ne_six (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3) :
    2061 * localA 3 6 * (∏ q ∈ S, (q + 1)) ≠
      2 ^ 12 * 3 ^ (6 - 1) * (∏ q ∈ S, q) := by
  intro hid
  have hr := normalized_residual_identity 6 S (by decide) (fun q hq => ⟨(hS q hq).1, (hS q hq).2.2⟩) hid
  rw [localA_three_six] at hr
  norm_num at hr
  have hdiv : 256 ∣ 384 * (∏ q ∈ S \ {229, 5, 23}, q) := by
    rw [← hr]
    exact dvd_mul_right _ _
  have heven : 2 ∣ ∏ q ∈ S \ {229, 5, 23}, q := by
    have hm : 128 * 2 ∣ 128 * (3 * (∏ q ∈ S \ {229, 5, 23}, q)) := by
      norm_num only [← Nat.mul_assoc]
      exact hdiv
    have hd := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 128) hm
    exact (show Nat.Coprime 2 3 from by decide).dvd_of_dvd_mul_left hd
  exact residual_prod_odd S (fun q hq => ⟨(hS q hq).1, (hS q hq).2.1⟩) heven

/-- At exponent five, the local factor forces base 41. Its numerator 42 then
violates the residual three-budget. This closes the boundary without a support bound. -/
theorem normalized_ne_five (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3) :
    2061 * localA 3 5 * (∏ q ∈ S, (q + 1)) ≠
      2 ^ 12 * 3 ^ (5 - 1) * (∏ q ∈ S, q) := by
  intro hid
  have h41 : 41 ∈ S := by
    apply normalized_force_prime 5 S (by decide) (fun q hq => (hS q hq).1)
      41 (by norm_num) (by decide) (by decide) hid
    rw [localA_three_five]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by decide : 41 ∣ 82) _) _
  have h41U : 41 ∈ S \ {229, 5, 23} := by
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨h41, by decide⟩
  have hr := normalized_residual_identity 5 S (by decide)
    (fun q hq => ⟨(hS q hq).1, (hS q hq).2.2⟩) hid
  norm_num at hr
  have h42 : 42 ∣ ∏ q ∈ S \ {229, 5, 23}, (q + 1) := by
    simpa using Finset.dvd_prod_of_mem (fun q : ℕ => q + 1) h41U
  have h3 : 3 ∣ 128 * (∏ q ∈ S \ {229, 5, 23}, q) := by
    rw [← hr]
    exact dvd_mul_of_dvd_right ((by decide : 3 ∣ 42).trans h42) _
  have hnot : ¬ 3 ∣ ∏ q ∈ S \ {229, 5, 23}, q := by
    intro hd
    have hm := prime_mem_of_dvd_prod (by decide : Nat.Prime 3)
      (S \ {229, 5, 23}) (fun q hq => (hS q (Finset.mem_sdiff.mp hq).1).1) hd
    exact (hS 3 (Finset.mem_sdiff.mp hm).1).2.2 rfl
  exact hnot ((show Nat.Coprime 3 128 from by decide).dvd_of_dvd_mul_left h3)

/-- The local base-three sum is even at every exponent greater than one. -/
theorem localA_three_even (b : ℕ) (hb : 1 < b) : 2 ∣ localA 3 b := by
  have hz : b ≠ 0 := by omega
  have hm (d : ℕ) (hd : d ∈ exponentDivisors b) : b / d ∈ exponentDivisors b := by
    obtain ⟨hpos, hdiv, hcop⟩ := exponentDivisors_mem hd
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdiv, hz⟩, ?_⟩
    rw [Nat.div_div_self hdiv hz]
    exact hcop.symm
  have hnf (d : ℕ) (hd : d ∈ exponentDivisors b) : b / d ≠ d := by
    obtain ⟨hpos, hdiv, hcop⟩ := exponentDivisors_mem hd
    intro heq
    have hone : d = 1 := (Nat.coprime_self d).mp (by simpa only [heq] using hcop)
    have hmul := Nat.mul_div_cancel' hdiv
    rw [heq, hone] at hmul
    omega
  have hs : (∑ d ∈ exponentDivisors b, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun d _ => b / d)
    · intro d hd
      decide
    · intro d hd _
      exact hnf d hd
    · exact hm
    · intro d hd
      exact Nat.div_div_self (exponentDivisors_mem hd).2.1 hz
  apply (ZMod.natCast_eq_zero_iff (localA 3 b) 2).mp
  simpa only [localA, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat,
    show (3 : ZMod 2) = 1 by decide, one_pow] using hs

/-- The normalized identity internally bounds the residual support by six,
using one factor of two from the local sum and one from every residual prime. -/
theorem normalized_residual_card_le (b : ℕ) (S : Finset ℕ) (hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3)
    (hid : 2061 * localA 3 b * (∏ q ∈ S, (q+1)) =
      2^12 * 3^(b-1) * (∏ q ∈ S, q)) : (S \ {229,5,23}).card ≤ 6 := by
  let U := S \ {229,5,23}
  have hfive := normalized_five_le b S hb (fun q hq => ⟨(hS q hq).1,(hS q hq).2.2⟩) hid
  have hr := normalized_residual_identity b S hb (fun q hq => ⟨(hS q hq).1,(hS q hq).2.2⟩) hid
  have hp : 2 ^ U.card ∣ ∏ q ∈ U, (q+1) := by
    have hh := Finset.prod_dvd_prod_of_dvd (fun _ : ℕ => 2) (fun q => q+1) (s := U) ?_
    · simpa using hh
    · intro q hq
      have h := hS q (Finset.mem_sdiff.mp hq).1
      have ho := h.1.eq_two_or_odd.resolve_left h.2.1
      exact Nat.dvd_of_mod_eq_zero (by omega)
  have hd : 2 ^ (U.card+1) ∣ 128 * (3^(b-5) * ∏ q ∈ U, q) := by
    rw [pow_succ, Nat.mul_comm]
    have hh := Nat.mul_dvd_mul (localA_three_even b (by omega)) hp
    change localA 3 b * (∏ q ∈ U, (q+1)) = 128 * 3^(b-5) * (∏ q ∈ U, q) at hr
    rw [← Nat.mul_assoc, ← hr]
    exact hh
  have hc : Nat.Coprime 2 (3^(b-5) * ∏ q ∈ U, q) := by
    apply Nat.Coprime.mul_right
    · exact (show Nat.Coprime 2 3 from by decide).pow_right _
    · exact (show Nat.Prime 2 from by decide).coprime_iff_not_dvd.mpr
        (residual_prod_odd S (fun q hq => ⟨(hS q hq).1,(hS q hq).2.1⟩))
  have hd128 : 2 ^ (U.card+1) ∣ 2^7 := by
    have hh := (hc.pow_left (U.card+1)).dvd_of_dvd_mul_right hd
    exact hh
  have he := (Nat.pow_dvd_pow_iff_le_right (by decide : 1<2)).mp hd128
  change U.card ≤ 6
  omega

/-- A support of at most six allowed primes has ratio bounded by the exact
six-smallest-primes envelope; there is no bound on the individual prime bases. -/
theorem residual_ratio_le (U : Finset ℕ)
    (hU : ∀ q ∈ U, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 23)
    (hc : U.card ≤ 6) :
    (∏ q ∈ U, ((q : ℚ) + 1) / q) ≤ (2073600 / 1339481 : ℚ) := by
  let K : Finset ℕ := {7,11,13,17,19}
  let C : ℚ := 30/29
  let g : ℕ → ℚ := fun q => (((q : ℚ)+1)/q)/C
  have hpos (q : ℕ) (hq : q ∈ U) : 0 < g q := by
    have hh := (hU q hq).1.pos
    dsimp [g,C]
    positivity
  have hsmall (q : ℕ) (hq : q ∈ U) (hn : q ∉ K) : g q ≤ 1 := by
    have hp := (hU q hq).1
    have hn2 := (hU q hq).2.1
    have hn3 := (hU q hq).2.2.1
    have hn5 := (hU q hq).2.2.2.1
    have hn23 := (hU q hq).2.2.2.2
    have hge : 29 ≤ q := by
      have hh := hp.eq_two_or_odd.resolve_left hn2
      have hd := hp.not_dvd_one
      have hq2 := hp.two_le
      have hk : q ≠ 7 ∧ q ≠ 11 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 19 := by simpa [K] using hn
      have hn9 : q ≠ 9 := by rintro rfl; norm_num at hp
      have hn15 : q ≠ 15 := by rintro rfl; norm_num at hp
      have hn21 : q ≠ 21 := by rintro rfl; norm_num at hp
      have hn25 : q ≠ 25 := by rintro rfl; norm_num at hp
      have hn27 : q ≠ 27 := by rintro rfl; norm_num at hp
      omega
    have hqpos : (0 : ℚ) < q := by exact_mod_cast hp.pos
    have hqge : (29 : ℚ) ≤ q := by exact_mod_cast hge
    dsimp [g,C]
    apply (div_le_one (by norm_num : (0:ℚ)<30/29)).mpr
    apply (div_le_iff₀ hqpos).mpr
    linarith
  have hK (q : ℕ) (hq : q ∈ K) : 1 ≤ g q := by
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num [g,C]
  have hp1 : (∏ q ∈ U, g q) ≤ ∏ q ∈ U.filter (fun q => q ∈ K), g q := by
    rw [Finset.prod_filter]
    apply Finset.prod_le_prod
    · intro q hq
      exact (hpos q hq).le
    · intro q hq
      split_ifs with hk
      · exact le_rfl
      · exact hsmall q hq hk
  have hp2 : (∏ q ∈ U.filter (fun q => q ∈ K), g q) ≤ ∏ q ∈ K, g q := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
    · intro q hq
      exact (hpos q (Finset.mem_filter.mp hq).1).le
    · intro q hq _
      exact hK q hq
  have hpow : C ^ U.card ≤ C ^ 6 := by
    exact pow_le_pow_right₀ (by norm_num [C]) hc
  have heq : (∏ q ∈ U, ((q : ℚ)+1)/q) = C^U.card * ∏ q ∈ U, g q := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    dsimp [g,C]
    ring
  rw [heq]
  calc
    C ^ U.card * (∏ q ∈ U, g q) ≤ C ^ U.card * (∏ q ∈ K, g q) :=
      mul_le_mul_of_nonneg_left (hp1.trans hp2) (by positivity)
    _ ≤ C^6 * (∏ q ∈ K, g q) := mul_le_mul_of_nonneg_right hpow
      (Finset.prod_nonneg (fun q hq => (hK q hq).trans' (by norm_num)))
    _ = 2073600/1339481 := by norm_num [K,g,C]

private theorem geom_three (m : ℕ) : 2 * (∑ i ∈ Finset.range m, 3^i) + 1 = 3^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- For every exponent at least seven, the normalized base-three local factor
is strictly smaller than `55/54` times its leading term, in integer form. -/
theorem localA_three_tail_lt (b : ℕ) (hb : 7 ≤ b) : 54 * localA 3 b < 55 * 3^(b-1) := by
  let T := (exponentDivisors b).erase b
  let m := b/2
  have hbpos : 0 < b := by omega
  have hbmem : b ∈ exponentDivisors b := by
    simp [exponentDivisors, Nat.mem_divisors, Nat.ne_of_gt hbpos, Nat.div_self hbpos]
  have hdpos (d : ℕ) (hd : d ∈ T) : 0 < d :=
    (exponentDivisors_mem (Finset.mem_erase.mp hd).2).1
  have hdle (d : ℕ) (hd : d ∈ T) : d ≤ m := by
    have hne := (Finset.mem_erase.mp hd).1
    have hdiv := (exponentDivisors_mem (Finset.mem_erase.mp hd).2).2.1
    have hmul := Nat.mul_div_cancel' hdiv
    have hquotpos : 0 < b/d := Nat.div_pos (Nat.le_of_dvd hbpos hdiv) (hdpos d hd)
    have hquot : 2 ≤ b/d := by
      by_contra hn
      have hq : b/d = 1 := by omega
      rw [hq, Nat.mul_one] at hmul
      exact hne hmul
    exact (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
      ((Nat.mul_le_mul_left d hquot).trans_eq hmul)
  have himage : T.image (fun d => d-1) ⊆ Finset.range m := by
    intro i hi
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (by have hp := hdpos d hd; have hl := hdle d hd; omega)
  have hinj : Set.InjOn (fun d : ℕ => d-1) T := by
    intro d hd e he hde
    have hp := hdpos d hd
    have hq := hdpos e he
    dsimp only at hde
    omega
  have hsum : (∑ d ∈ T, 3^(d-1)) ≤ ∑ i ∈ Finset.range m, 3^i := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset himage
  have hsplit : localA 3 b = (∑ d ∈ T, 3^(d-1)) + 3^(b-1) := by
    exact (Finset.sum_erase_add (exponentDivisors b) (fun d => 3^(d-1)) hbmem).symm
  have hgeom := geom_three m
  have hbound : 2 * localA 3 b < 2 * 3^(b-1) + 3^m := by omega
  have hexp : m+3 ≤ b-1 := by dsimp [m]; omega
  have hpow : 27 * 3^m ≤ 3^(b-1) := by
    have hh := pow_le_pow_right₀ (by decide : 1 ≤ (3:ℕ)) hexp
    simpa only [pow_add, show (3:ℕ)^3=27 by decide, Nat.mul_comm] using hh
  omega

/-- The exact normalized identity is contradictory at every exponent at least seven:
the internally derived envelope is strictly below the local-factor lower bound. -/
theorem normalized_identity_false_of_seven_le (b : ℕ) (S : Finset ℕ) (hb : 7 ≤ b)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3)
    (hid : 2061 * localA 3 b * (∏ q ∈ S, (q+1)) =
      2^12 * 3^(b-1) * (∏ q ∈ S, q)) : False := by
  let U := S \ {229,5,23}
  let A := localA 3 b
  let P := ∏ q ∈ U, (q+1)
  let B := ∏ q ∈ U, q
  let Z := 3^(b-5)
  have hU : ∀ q ∈ U, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 23 := by
    intro q hq
    have hs := hS q (Finset.mem_sdiff.mp hq).1
    have hn := (Finset.mem_sdiff.mp hq).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    exact ⟨hs.1,hs.2.1,hs.2.2,hn.2.1,hn.2.2⟩
  have hcard := normalized_residual_card_le b S (by omega) hS hid
  have henv := residual_ratio_le U hU hcard
  have hB : 0 < B := Finset.prod_pos (fun q hq => (hU q hq).1.pos)
  have hrat : (∏ q ∈ U, ((q:ℚ)+1)/q) = (P:ℚ)/(B:ℚ) := by
    simp only [P,B,Finset.prod_div_distrib,Nat.cast_prod,Nat.cast_add,Nat.cast_one]
  rw [hrat] at henv
  have hBq : (0:ℚ) < B := by exact_mod_cast hB
  have heq : (1339481:ℚ)*P ≤ 2073600*B := by
    have hh := (div_le_iff₀ hBq).mp henv
    linarith
  have hen : 1339481 * P ≤ 2073600 * B := by exact_mod_cast heq
  have hr : A*P = 128*Z*B := normalized_residual_identity b S (by omega)
    (fun q hq => ⟨(hS q hq).1,(hS q hq).2.2⟩) hid
  have ht := localA_three_tail_lt b hb
  have he : b-1 = (b-5)+4 := by omega
  have hpow : 3^(b-1) = Z*81 := by rw [he,pow_add]; rfl
  rw [hpow] at ht
  change 54*A < 55*(Z*81) at ht
  have hmul := Nat.mul_le_mul_left A hen
  have hstrict := Nat.mul_lt_mul_of_pos_right ht hB
  nlinarith [hmul,hstrict,hr]

/-- For every positive exponent and every finite support of primes excluding two and
three, the exact exponent-twelve normalized perfectness identity is impossible.
No support-size, valuation, forced-base, or exponent-cap certificate is assumed. -/
theorem normalized_ne (b : ℕ) (S : Finset ℕ) (hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3) :
    2061 * localA 3 b * (∏ q ∈ S, (q + 1)) ≠
      2 ^ 12 * 3 ^ (b - 1) * (∏ q ∈ S, q) := by
  intro hid
  have hfive := normalized_five_le b S hb
    (fun q hq => ⟨(hS q hq).1, (hS q hq).2.2⟩) hid
  by_cases hseven : 7 ≤ b
  · exact normalized_identity_false_of_seven_le b S hseven hS hid
  · have hboundary : b = 5 ∨ b = 6 := by omega
    rcases hboundary with rfl | rfl
    · exact normalized_ne_five S hS hid
    · exact normalized_ne_six S hS hid

example : (1 < (2 : ℕ)) ∧ 2 ∣ localA 3 2 := by decide
example : (7 ≤ (7 : ℕ)) ∧ 54 * localA 3 7 < 55 * 3^(7-1) :=
  ⟨by decide, localA_three_tail_lt 7 (by decide)⟩
example : (∏ q ∈ (∅ : Finset ℕ), ((q : ℚ)+1)/q) ≤ (2073600/1339481 : ℚ) := by
  norm_num

example :
    2061 * localA 3 1 * (∏ q ∈ (∅ : Finset ℕ), (q + 1)) ≠
      2 ^ 12 * 3 ^ (1 - 1) * (∏ q ∈ (∅ : Finset ℕ), q) :=
  normalized_ne 1 ∅ (by decide) (by simp)

end EUnitaryP1
