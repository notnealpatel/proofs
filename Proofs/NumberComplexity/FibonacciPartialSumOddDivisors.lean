/-
# Infinitely many odd `n` divide `F_1 + ⋯ + F_n` (Fatehizadeh–Yaqubi conjecture)

Oisín Flynn-Connolly, “On the divisibility of sums of Fibonacci
numbers”, arXiv:2504.09938, §3, Theorem `thm:main` and its corollary.
There are infinitely many odd `N` dividing `F₁+⋯+F_N`, resolving the
Fatehizadeh–Yaqubi conjecture (J. Integer Seq. 25 (2022)).
The module proves the `n = 2p` case for odd primes `p ≡ 2 (mod 3)`,
`p ≡ ±2 (mod 5)`; the paper's `n = 4p` case is not needed and is not
formalized. Witnesses are `N = F_{2p}` with `p ≡ 17 (mod 30)`.

The paper computes `F_{2p} mod 4p` through Wall's bound on the Pisano period
`π(p) ∣ 2(p+1)`.  Here the only input is the congruence
`F_p ≡ -1, F_{p+1} ≡ 0 (mod p)` for `p ≡ ±2 (mod 5)`, proved by a Frobenius
computation with the Fibonacci matrix `M = !![1,1;1,0]` over `ZMod p`:
`s = 2M - 1` satisfies `s² = 5`, Euler's criterion and quadratic reciprocity
give `5^((p-1)/2) = -1`, so `(2M)^p = (1 + s)^p = 1 + s^p = 1 - s`, i.e.
`M^p = 1 - M`.  Then `F_{2p} = F_{p-1} F_p + F_p F_{p+1} ≡ -1 (mod p)`, and
`F_{2p} ≡ F_4 = 3 (mod 4)` by the period `6` of `F mod 4`.  Proposition
`prop:pisano_period` is proved from Cassini (the determinant of `M^{n+1}`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FibonacciPartialSumOddDivisors

/-! ## The Fibonacci matrix -/

/-- The Fibonacci matrix `!![1, 1; 1, 0]` over a commutative ring `R`; its
`(n+1)`-st power is `!![F_{n+2}, F_{n+1}; F_{n+1}, F_n]`. -/
def fibMat (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, 0]

example : fibMat ℤ ^ 4 = !![5, 3; 3, 2] := by decide

/-- Powers of the Fibonacci matrix:
`M^(n+1) = !![F_{n+2}, F_{n+1}; F_{n+1}, F_n]`. -/
theorem fibMat_pow_succ (R : Type*) [CommRing R] (n : ℕ) :
    fibMat R ^ (n + 1) =
      !![(Nat.fib (n + 2) : R), (Nat.fib (n + 1) : R);
         (Nat.fib (n + 1) : R), (Nat.fib n : R)] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fibMat]
  | succ n ih =>
    rw [pow_succ, ih, fibMat, Matrix.mul_fin_two, Nat.fib_add_two (n := n + 1),
      Nat.fib_add_two (n := n)]
    push_cast
    ring_nf

/-- The matrix `s = 2M - 1` is a square root of `5`. -/
theorem sq_two_mul_fibMat_sub_one (R : Type*) [CommRing R] :
    (2 * fibMat R - 1) ^ 2 = (5 : Matrix (Fin 2) (Fin 2) R) := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fibMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply]

/-- **Cassini's identity** in any commutative ring, from `det M = -1`:
`F_{n+2} F_n - F_{n+1}² = (-1)^(n+1)`. -/
theorem fib_cassini (R : Type*) [CommRing R] (n : ℕ) :
    (Nat.fib (n + 2) : R) * Nat.fib n - (Nat.fib (n + 1) : R) ^ 2 = (-1) ^ (n + 1) := by
  have h := congrArg Matrix.det (fibMat_pow_succ R n)
  rw [Matrix.det_pow, Matrix.det_fin_two_of, fibMat, Matrix.det_fin_two_of] at h
  linear_combination -h

/-! ## Fibonacci numbers modulo a prime `p ≡ ±2 (mod 5)` -/

/-- **Frobenius step.** If `p` is an odd prime and `5^((p-1)/2) = -1` in
`ZMod p`, then `M^p = 1 - M` for the Fibonacci matrix `M` over `ZMod p`. -/
theorem fibMat_pow_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : (5 : ZMod p) ^ (p / 2) = -1) :
    fibMat (ZMod p) ^ p = 1 - fibMat (ZMod p) := by
  set M := fibMat (ZMod p) with hM
  set s : Matrix (Fin 2) (Fin 2) (ZMod p) := 2 * M - 1 with hs
  have hodd : p = 2 * (p / 2) + 1 := by
    have h2 := hp.out.eq_one_or_self_of_dvd 2
    omega
  have h5m : (5 : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (p / 2) = -1 := by
    have hsc : (5 : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.scalar (Fin 2) (5 : ZMod p) :=
      (map_ofNat (Matrix.scalar (Fin 2) : ZMod p →+* _) 5).symm
    rw [hsc, ← map_pow, h5, map_neg, map_one]
  have hsp : s ^ p = -s := by
    have hpow : s ^ p = s ^ (2 * (p / 2) + 1) := congrArg (s ^ ·) hodd
    rw [hpow, pow_succ, pow_mul, hs, sq_two_mul_fibMat_sub_one, h5m]
    simp
  have h2sc : (2 : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.scalar (Fin 2) (2 : ZMod p) :=
    (map_ofNat (Matrix.scalar (Fin 2) : ZMod p →+* _) 2).symm
  have h2p : (2 : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p = 2 := by
    rw [h2sc, ← map_pow, ZMod.pow_card]
  have hkey : (2 : Matrix (Fin 2) (Fin 2) (ZMod p)) * M ^ p = 2 * (1 - M) := by
    have h1 : 2 * M = 1 + s := by rw [hs]; abel
    calc (2 : Matrix (Fin 2) (Fin 2) (ZMod p)) * M ^ p = (2 * M) ^ p := by
          rw [(Commute.ofNat_left 2 M).mul_pow p, h2p]
      _ = 1 + s ^ p := by rw [h1, add_pow_char_of_commute p (Commute.one_left s), one_pow]
      _ = 2 * (1 - M) := by rw [hsp, hs]; noncomm_ring
  have h2u : IsUnit (2 : ZMod p) := by
    rw [isUnit_iff_ne_zero]
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hdvd)
  obtain ⟨u, hu⟩ := h2u
  have hinv : (Matrix.scalar (Fin 2) ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * 2 = 1 := by
    rw [h2sc, ← map_mul, ← hu, Units.inv_mul, map_one]
  calc M ^ p = (Matrix.scalar (Fin 2) ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * 2 * M ^ p := by
        rw [hinv, one_mul]
    _ = (Matrix.scalar (Fin 2) ((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * 2 * (1 - M) := by
        rw [mul_assoc, hkey, ← mul_assoc]
    _ = 1 - M := by rw [hinv, one_mul]

/-- If `p` is an odd prime with `5^((p-1)/2) ≡ -1 (mod p)`, then
`F_p ≡ -1` and `F_{p+1} ≡ 0 (mod p)`. -/
theorem fib_prime_eq_neg_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : (5 : ZMod p) ^ (p / 2) = -1) :
    (Nat.fib p : ZMod p) = -1 ∧ (Nat.fib (p + 1) : ZMod p) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  have hM := fibMat_pow_prime hp2 h5
  rw [fibMat_pow_succ] at hM
  have h01 := congrFun (congrFun hM 0) 1
  have h00 := congrFun (congrFun hM 0) 0
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, fibMat, Matrix.sub_apply, ne_eq, zero_ne_one,
    not_false_eq_true, Matrix.one_apply_ne, zero_sub, Matrix.one_apply_eq, sub_self] at h01 h00
  exact ⟨h01, by linear_combination h00⟩

/-- Neither `2` nor `3` is a square modulo `5`. -/
theorem zmod_five_mul_self_ne : ∀ r : ZMod 5, r * r ≠ 2 ∧ r * r ≠ 3 := by decide

/-- For an odd prime `p ≡ ±2 (mod 5)`, `5` is a quadratic non-residue mod `p`, so by
Euler's criterion `5^((p-1)/2) ≡ -1 (mod p)`. -/
theorem five_pow_div_two_eq_neg_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : p % 5 = 2 ∨ p % 5 = 3) : (5 : ZMod p) ^ (p / 2) = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hne : (5 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have hp5 := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1 h'
    omega
  have hns : ¬ IsSquare ((p : ℕ) : ZMod 5) := by
    have hp5 : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod p 5).symm
    rw [hp5]
    have hsq := zmod_five_mul_self_ne
    rintro ⟨r, hr⟩
    rcases h5 with h | h <;> rw [h] at hr <;> simp only [Nat.cast_ofNat] at hr
    · exact (hsq r).1 hr.symm
    · exact (hsq r).2 hr.symm
  have hrec := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
  have hns5 : ¬ IsSquare (5 : ZMod p) := by
    intro h
    apply hns
    rw [hrec]
    exact_mod_cast h
  rcases ZMod.pow_div_two_eq_neg_one_or_one p hne with h | h
  · exact absurd ((ZMod.euler_criterion p hne).2 h) hns5
  · exact h

/-- For an odd prime `p ≡ ±2 (mod 5)`, `F_{2p} ≡ -1 (mod p)`. -/
theorem fib_two_mul_prime_eq_neg_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : p % 5 = 2 ∨ p % 5 = 3) : (Nat.fib (2 * p) : ZMod p) = -1 := by
  obtain ⟨hFp, hFp1⟩ := fib_prime_eq_neg_one hp2 (five_pow_div_two_eq_neg_one hp2 h5)
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  have hk : (Nat.fib k : ZMod (k + 1)) = 1 := by
    have h' : (Nat.fib (k + 2) : ZMod (k + 1)) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [hFp1, hFp] at h'
    linear_combination -h'
  have hadd := Nat.fib_add k (k + 1)
  have e : 2 * (k + 1) = k + (k + 1) + 1 := by ring
  rw [e, hadd]
  push_cast
  rw [hk, hFp, hFp1]
  ring

/-! ## Fibonacci numbers modulo `4` -/

/-- The Fibonacci numbers modulo `4` have period `6`. -/
theorem fib_add_six_mod_four (k : ℕ) : (Nat.fib (k + 6) : ZMod 4) = Nat.fib k := by
  have e : k + 6 = k + 5 + 1 := rfl
  rw [e, Nat.fib_add k 5]
  push_cast
  have h5 : (Nat.fib 5 : ZMod 4) = 1 := by decide
  have h6 : (Nat.fib 6 : ZMod 4) = 0 := by decide
  rw [h5, h6]
  ring

/-- `F_{6j+4} ≡ F_4 = 3 ≡ -1 (mod 4)`. -/
theorem fib_six_mul_add_four_mod_four (j : ℕ) : (Nat.fib (6 * j + 4) : ZMod 4) = -1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e : 6 * (j + 1) + 4 = (6 * j + 4) + 6 := by ring
    rw [e, fib_add_six_mod_four, ih]

/-! ## Proposition `prop:pisano_period`: `π(F_n) ∣ 2n` for even `n` -/

/-- **Proposition `prop:pisano_period`** (arXiv:2504.09938): for even `n`,
`F_{m + 2n} ≡ F_m (mod F_n)` for every `m`, i.e. the Pisano period of `F_n`
divides `2n`.  (The paper assumes `n > 1`; the congruence also holds at
`n = 0`, where it is trivial.) -/
theorem fib_add_two_mul_cast {n : ℕ} (hn : Even n) (m : ℕ) :
    (Nat.fib (m + 2 * n) : ZMod (Nat.fib n)) = Nat.fib m := by
  have h0 : (Nat.fib n : ZMod (Nat.fib n)) = 0 := ZMod.natCast_self _
  have h2n : (Nat.fib (2 * n) : ZMod (Nat.fib n)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.fib_dvd _ _ (dvd_mul_left n 2)
  have h2n1 : (Nat.fib (2 * n + 1) : ZMod (Nat.fib n)) = 1 := by
    have hc := fib_cassini (ZMod (Nat.fib n)) n
    rw [h0, (hn.add_one).neg_one_pow] at hc
    rw [Nat.fib_two_mul_add_one]
    push_cast
    rw [h0]
    linear_combination -hc
  cases m with
  | zero => simpa using h2n
  | succ k =>
    have e : k + 1 + 2 * n = k + 2 * n + 1 := by ring
    rw [e, Nat.fib_add]
    push_cast
    rw [h2n, h2n1]
    ring

/-- Iterated form of Proposition `prop:pisano_period`: for even `n`,
`F_{m + c·2n} ≡ F_m (mod F_n)`. -/
theorem fib_add_mul_two_mul_cast {n : ℕ} (hn : Even n) (m c : ℕ) :
    (Nat.fib (m + c * (2 * n)) : ZMod (Nat.fib n)) = Nat.fib m := by
  induction c with
  | zero => simp
  | succ c ih =>
    have e : m + (c + 1) * (2 * n) = (m + c * (2 * n)) + 2 * n := by ring
    rw [e, fib_add_two_mul_cast hn, ih]

/-! ## Proposition `add`: `S_n = F_{n+2} - 1` -/

example : ∑ i ∈ Finset.Icc 1 10, Nat.fib i = 143 := by decide

/-- **Proposition `add`** (arXiv:2504.09938), stated without truncated
subtraction: `F_1 + ⋯ + F_n + 1 = F_{n+2}`. -/
theorem sum_Icc_fib_add_one (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, Nat.fib i + 1 = Nat.fib (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.fib_add_two (n := n + 1), ← ih]
    ring

/-! ## Theorem `thm:main`, case `n = 2p` -/

/-- The odd integer `n = 77` divides `F_1 + ⋯ + F_n`. -/
example : 77 ∣ ∑ i ∈ Finset.Icc 1 77, Nat.fib i := by decide

/-- Examples at `p = 17`: `F_{34} = 5702887 ≡ -1 (mod 68)`. -/
example : Nat.fib 34 = 5702887 ∧ Nat.fib 34 % 68 = 67 := by decide

/-- The hypotheses of `thm_main_two_mul` are jointly satisfiable (`p = 17`). -/
example : Nat.Prime 17 ∧ Odd 17 ∧ 17 % 3 = 2 ∧ (17 % 5 = 2 ∨ 17 % 5 = 3) :=
  ⟨by norm_num, by decide, by decide, by decide⟩

/-- Key congruence: for an odd prime `p ≡ 2 (mod 3)`, `p ≡ ±2 (mod 5)`,
`F_{2p} ≡ -1 (mod 4p)`. -/
theorem four_mul_dvd_fib_two_mul_add_one {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h3 : p % 3 = 2) (h5 : p % 5 = 2 ∨ p % 5 = 3) : 4 * p ∣ Nat.fib (2 * p) + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
  have hdp : p ∣ Nat.fib (2 * p) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [fib_two_mul_prime_eq_neg_one hp2 h5]
    ring
  have hd4 : 4 ∣ Nat.fib (2 * p) + 1 := by
    obtain ⟨i, hi⟩ : ∃ i, 2 * p = 6 * (2 * i + 1) + 4 := by
      obtain ⟨t, ht⟩ := hodd
      exact ⟨p / 6, by omega⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hi, fib_six_mul_add_four_mod_four]
    ring
  have hcop : Nat.Coprime 4 p := by
    have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    simpa using Nat.Coprime.pow_left 2 h2
  exact hcop.mul_dvd_of_dvd_of_dvd hd4 hdp

/-- **Theorem `thm:main`, case `n = 2p`** (Flynn-Connolly, arXiv:2504.09938),
sum form: if `p` is an odd prime with `p ≡ 2 (mod 3)` and `p ≡ ±2 (mod 5)`,
then `N = F_{2p}` is odd and `N ∣ F_1 + ⋯ + F_N`. -/
theorem thm_main_two_mul {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h3 : p % 3 = 2) (h5 : p % 5 = 2 ∨ p % 5 = 3) :
    Odd (Nat.fib (2 * p)) ∧
      Nat.fib (2 * p) ∣ ∑ i ∈ Finset.Icc 1 (Nat.fib (2 * p)), Nat.fib i := by
  obtain ⟨c, hc⟩ := four_mul_dvd_fib_two_mul_add_one hp hodd h3 h5
  set N := Nat.fib (2 * p)
  have hc' : N + 1 = 4 * (p * c) := by rw [hc]; ring
  refine ⟨Nat.odd_iff.2 (by omega), ?_⟩
  have hper := fib_add_mul_two_mul_cast (even_two_mul p) 1 c
  have e : 1 + c * (2 * (2 * p)) = N + 2 := by
    rw [show N + 2 = (N + 1) + 1 by ring, hc]; ring
  rw [e, ← sum_Icc_fib_add_one] at hper
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast at hper
  simpa using hper

/-- **Theorem `thm:main`, case `n = 2p`** (Flynn-Connolly, arXiv:2504.09938),
in the paper's form: if `p` is an odd prime with `p ≡ 2 (mod 3)` and
`p ≡ ±2 (mod 5)`, then `F_{2p}` is odd and `F_{2p} ∣ F_{F_{2p} + 2} - 1`
(subtraction in `ℤ`). -/
theorem thm_main_two_mul_int {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h3 : p % 3 = 2) (h5 : p % 5 = 2 ∨ p % 5 = 3) :
    Odd (Nat.fib (2 * p)) ∧
      (Nat.fib (2 * p) : ℤ) ∣ (Nat.fib (Nat.fib (2 * p) + 2) : ℤ) - 1 := by
  obtain ⟨hN, hdvd⟩ := thm_main_two_mul hp hodd h3 h5
  refine ⟨hN, ?_⟩
  rw [← sum_Icc_fib_add_one]
  push_cast
  rw [add_sub_cancel_right]
  exact_mod_cast hdvd

/-! ## The corollary: the Fatehizadeh–Yaqubi conjecture -/

/-- **Corollary (Fatehizadeh–Yaqubi conjecture, resolved by Flynn-Connolly,
arXiv:2504.09938).** There are infinitely many odd integers `n` that divide the
sum `F_1 + ⋯ + F_n` of the first `n` nonzero Fibonacci numbers.

Witnesses: `n = F_{2p}` for primes `p ≡ 17 (mod 30)` (Dirichlet's theorem,
`Nat.forall_exists_prime_gt_and_eq_mod`). -/
theorem fatehizadeh_yaqubi_conjecture :
    Set.Infinite {n : ℕ | Odd n ∧ n ∣ ∑ i ∈ Finset.Icc 1 n, Nat.fib i} := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  have hu : IsUnit (17 : ZMod 30) := IsUnit.of_mul_eq_one (b := 23) (by decide)
  obtain ⟨p, hpa, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (a + 17)
  have h30 : p % 30 = 17 := by
    have h' : ((p : ℕ) : ZMod 30) = ((17 : ℕ) : ZMod 30) := by rw [hpmod]; rfl
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    simpa using h'
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  obtain ⟨hNodd, hNdvd⟩ := thm_main_two_mul hp hodd (by omega) (Or.inl (by omega))
  refine ⟨Nat.fib (2 * p), ⟨hNodd, hNdvd⟩, ?_⟩
  have hle : 2 * p ≤ Nat.fib (2 * p) := Nat.le_fib_self (by omega)
  omega

end Candidates.FibonacciPartialSumOddDivisors
