/-
# A prime dividing no term of A377109

Source: the unsigned conjecture in OEIS A377109, entry by Clark Kimberling
(Oct 20 2024). Iterating integer coordinates in the radical basis computes
the coefficient of 1 in `(2+√2+√3)^n`; `coeffs_spec` proves the real expansion.
Linear independence of the radical basis is not formalized in this module.
Modulo 241 the state has period 240 and its first coordinate never vanishes.
Hence 241 divides no term, refuting the every-prime-infinitely-often clause
and the source conjunction. The eventual-gap-periodicity clause under
infinitude is not proved here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A377109Refutation

/-- Multiplication by `β = 2 + √2 + √3` on coordinates `(a, b, c, d)` in the
basis `{1, √2, √3, √6}`:
`(a + b√2 + c√3 + d√6)(2 + √2 + √3) =
 (2a+2b+3c) + (a+2b+3d)√2 + (a+2c+2d)√3 + (b+c+2d)√6`. -/
def step {R : Type*} [CommRing R] (x : R × R × R × R) : R × R × R × R :=
  (2 * x.1 + 2 * x.2.1 + 3 * x.2.2.1,
   x.1 + 2 * x.2.1 + 3 * x.2.2.2,
   x.1 + 2 * x.2.2.1 + 2 * x.2.2.2,
   x.2.1 + x.2.2.1 + 2 * x.2.2.2)

/-- The integer coordinates of `(2 + √2 + √3)^n` in the basis
`{1, √2, √3, √6}`. -/
def coeffs (n : ℕ) : ℤ × ℤ × ℤ × ℤ := step^[n] (1, 0, 0, 0)

/-- **A377109**: the coefficient of the term independent of `√2, √3, √6` in
`(2 + √2 + √3)^n`. -/
def A377109 (n : ℕ) : ℤ := (coeffs n).1

/-- The first ten listed terms. -/
example : (List.range 10).map A377109 =
    [1, 2, 9, 38, 185, 922, 4689, 23998, 123217, 633458] := by decide

/-- The last listed term `a(23)`. -/
example : A377109 23 = 5784397706237854 := by decide

/-- The coordinates `coeffs n` really are the coordinates of
`(2 + √2 + √3)^n` in the basis `{1, √2, √3, √6}`. -/
theorem coeffs_spec (n : ℕ) :
    ((2 : ℝ) + √2 + √3) ^ n =
      (coeffs n).1 + (coeffs n).2.1 * √2 + (coeffs n).2.2.1 * √3
        + (coeffs n).2.2.2 * √6 := by
  have hs : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have ht : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h6 : √6 = √2 * √3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  induction n with
  | zero => simp [coeffs]
  | succ n ih =>
    have hc : coeffs (n + 1) = step (coeffs n) :=
      Function.iterate_succ_apply' step n (1, 0, 0, 0)
    rw [pow_succ, ih, hc, h6]
    simp only [step, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    linear_combination ((coeffs n).2.1 + (coeffs n).2.2.2 * √3 : ℝ) * hs
      + ((coeffs n).2.2.1 + (coeffs n).2.2.2 * √2 : ℝ) * ht

/-- The difference sequence `k(i+1) - k(i)` of the increasing enumeration
`K(p) = (k(1), k(2), …)` of the indices `n` with `p ∣ a(n)` (cast to `ℤ`
before subtracting). -/
noncomputable def gapSeq (p : ℕ) (i : ℕ) : ℤ :=
  (Nat.nth (fun n => (p : ℤ) ∣ A377109 n) (i + 1) : ℤ)
    - (Nat.nth (fun n => (p : ℤ) ∣ A377109 n) i : ℤ)

/-- Kimberling's A377109 conjecture: every prime divides infinitely many
terms, and the gaps between successive divisible indices are eventually periodic. -/
def Conjecture : Prop :=
  ∀ p : ℕ, p.Prime →
    {n : ℕ | (p : ℤ) ∣ A377109 n}.Infinite ∧
      ∃ N T : ℕ, 0 < T ∧ ∀ i : ℕ, N ≤ i → gapSeq p (i + T) = gapSeq p i

/-- Reduction modulo `241` of the coordinate iteration. -/
def coeffsMod (n : ℕ) : ZMod 241 × ZMod 241 × ZMod 241 × ZMod 241 :=
  step^[n] (1, 0, 0, 0)

/-- Checks that the first coordinate stays nonzero along `k` steps. -/
def allNonzero : ℕ → ZMod 241 × ZMod 241 × ZMod 241 × ZMod 241 → Bool
  | 0, _ => true
  | k + 1, x => (x.1 != 0) && allNonzero k (step x)

/-- A successful `allNonzero` run certifies the first `k` iterates. -/
theorem fst_iterate_ne_zero_of_allNonzero (k : ℕ)
    (x : ZMod 241 × ZMod 241 × ZMod 241 × ZMod 241)
    (h : allNonzero k x = true) (j : ℕ) (hj : j < k) :
    (step^[j] x).1 ≠ 0 := by
  induction k generalizing x j with
  | zero => omega
  | succ k ih =>
    simp only [allNonzero, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      rw [Function.iterate_succ_apply]
      exact ih (step x) h.2 j (by omega)

set_option maxRecDepth 20000 in
/-- Kernel certificate: `β ^ 240 = 1` modulo `241`. -/
theorem coeffsMod_240 : coeffsMod 240 = (1, 0, 0, 0) := by decide

set_option maxRecDepth 20000 in
/-- Kernel certificate: no residue in one period vanishes. -/
theorem allNonzero_240 : allNonzero 240 (1, 0, 0, 0) = true := by decide

/-- The residues are `240`-periodic. -/
theorem coeffsMod_add_240 (n : ℕ) : coeffsMod (n + 240) = coeffsMod n := by
  unfold coeffsMod
  rw [Function.iterate_add_apply]
  exact congrArg (step^[n]) coeffsMod_240

/-- Residues repeat with period `240` in the iteration count. -/
theorem coeffsMod_add_mul_240 (r q : ℕ) : coeffsMod (r + 240 * q) = coeffsMod r := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show r + 240 * (q + 1) = r + 240 * q + 240 by ring, coeffsMod_add_240, ih]

/-- Applying a ring hom coordinatewise commutes with `step`. -/
theorem map_step {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : R × R × R × R) :
    step (f x.1, f x.2.1, f x.2.2.1, f x.2.2.2) =
      (f (step x).1, f (step x).2.1, f (step x).2.2.1, f (step x).2.2.2) := by
  simp [step, map_add, map_mul, map_ofNat]

/-- `coeffsMod` is the reduction of `coeffs` modulo `241`. -/
theorem coeffsMod_eq (n : ℕ) :
    coeffsMod n = (((coeffs n).1 : ZMod 241), ((coeffs n).2.1 : ZMod 241),
      ((coeffs n).2.2.1 : ZMod 241), ((coeffs n).2.2.2 : ZMod 241)) := by
  induction n with
  | zero => simp [coeffsMod, coeffs]
  | succ n ih =>
    have hc : coeffs (n + 1) = step (coeffs n) :=
      Function.iterate_succ_apply' step n (1, 0, 0, 0)
    have hm : coeffsMod (n + 1) = step (coeffsMod n) :=
      Function.iterate_succ_apply' step n (1, 0, 0, 0)
    rw [hm, ih, hc]
    exact map_step (Int.castRingHom (ZMod 241)) (coeffs n)

/-- **`241` divides no term of A377109.** -/
theorem not_dvd_A377109 (n : ℕ) : ¬ (241 : ℤ) ∣ A377109 n := by
  intro hdvd
  have hzero : ((A377109 n : ℤ) : ZMod 241) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (A377109 n) 241).2 hdvd
  have hfst : (coeffsMod n).1 = ((A377109 n : ℤ) : ZMod 241) := by
    rw [coeffsMod_eq]
    rfl
  have hper : coeffsMod n = coeffsMod (n % 240) := by
    conv_lhs => rw [← Nat.mod_add_div n 240]
    exact coeffsMod_add_mul_240 (n % 240) (n / 240)
  have hne : (coeffsMod (n % 240)).1 ≠ 0 :=
    fst_iterate_ne_zero_of_allNonzero 240 (1, 0, 0, 0) allNonzero_240 (n % 240)
      (Nat.mod_lt n (by norm_num))
  rw [← hper, hfst] at hne
  exact hne hzero

/-- Non-vacuity of the first clause at small primes: `2 ∣ a(1) = 2`, and
`3 ∣ a(2) = 9`. -/
example : (2 : ℤ) ∣ A377109 1 ∧ (3 : ℤ) ∣ A377109 2 := by decide

/-- The prime 241 divides no A377109 term, refuting Kimberling's conjunction.
The coordinate state modulo 241 returns after 240 steps with no zero
first coordinate. No claim about other primes is required. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hprime : Nat.Prime 241 := by norm_num
  have hempty : {n : ℕ | ((241 : ℕ) : ℤ) ∣ A377109 n} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact_mod_cast not_dvd_A377109 n
  have hinf := (hconj 241 hprime).1
  rw [hempty] at hinf
  exact hinf Set.finite_empty

end Candidates.A377109Refutation
