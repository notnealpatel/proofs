/-
# Wolstenholme's theorem

## Source

J. Wolstenholme, "On certain properties of prime numbers",
Quart. J. Pure Appl. Math. 5 (1862) 35–39; also G. H. Hardy and
E. M. Wright, *An Introduction to the Theory of Numbers*, Theorems 115–116
and §7.8.

## Statement (verbatim from the target spec)

"For every prime p >= 5: (a) the numerator of H_{p-1} = 1 + 1/2 + ... +
1/(p-1) is divisible by p^2; (b) C(2p-1, p-1) ≡ 1 (mod p^3)."

The hypothesis `5 ≤ p` is necessary: at `p = 3`, `H_2 = 3/2` and
`C(5, 2) = 10 ≢ 1 (mod 27)` (checked below).

## Mathlib

No Wolstenholme/Babbage result in Mathlib (leandoc and grep re-checked
2026-10-21).  Mathlib's `harmonic : ℕ → ℚ` and `Nat.choose` are used
directly; no new definitions are introduced.

## Proof route

The single number-theoretic input is `∑_{k=1}^{p-1} k⁻² ≡ 0 (mod p)` for
`p ≥ 5` (`FiniteField.sum_pow_lt_card_sub_one`).  Part (a) pairs `k` with
`p - k`; part (b) uses Vandermonde `∑ C(p,k)² = C(2p,p)` and
`k · C(p,k) = p · C(p-1,k-1)` with `C(p-1,k-1) ≡ ±1 (mod p)`.

Date: 2026-10-21.
-/
import Mathlib

set_option autoImplicit false

namespace NumberComplexity.Wolstenholme

open Finset

/-- For a prime `p ≥ 5`, `∑_{k=1}^{p-1} k⁻² = 0` in `ZMod p`: inversion permutes
`ZMod p` and `∑_x x² = 0` because `p - 1 ∤ 2`. -/
theorem sum_inv_sq_zmod {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  haveI := Fact.mk hp
  have hall : ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    have hinv : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
      Fintype.sum_equiv (Equiv.inv (ZMod p)) _ _ (fun x => by simp)
    rw [hinv]
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  have hrange : ∑ k ∈ range p, ((k : ZMod p)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    apply Finset.sum_bij' (fun (i : ℕ) _ => (i : ZMod p)) (fun (x : ZMod p) _ => x.val)
    · intro i _; exact mem_univ _
    · intro x _; exact mem_range.mpr (ZMod.val_lt x)
    · intro i hi; exact ZMod.val_cast_of_lt (mem_range.mp hi)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro i _; rfl
  have hsplit : range p = insert 0 (Ico 1 p) := by
    ext k; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [← hall, ← hrange, hsplit, sum_insert (by simp)]
  simp

/-- If `k² · x k ≡ M (mod p)` for every `1 ≤ k < p` (with `p ≥ 5` prime), then
`p ∣ ∑_{k=1}^{p-1} x k`, since `x k ≡ M k⁻²` and `∑ k⁻² ≡ 0`. -/
theorem dvd_sum_of_sq_mul_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (x : ℕ → ℕ) (M : ZMod p)
    (hx : ∀ k ∈ Ico 1 p, (k : ZMod p) ^ 2 * (x k : ZMod p) = M) :
    p ∣ ∑ k ∈ Ico 1 p, x k := by
  haveI := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
  have hterm : ∀ k ∈ Ico 1 p, (x k : ZMod p) = M * ((k : ZMod p)⁻¹) ^ 2 := by
    intro k hk
    have hk0 : (k : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (mem_Ico.mp hk).1 hdvd
      have := (mem_Ico.mp hk).2
      omega
    rw [← hx k hk]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, sum_inv_sq_zmod hp h5, mul_zero]

/-- **Wolstenholme, integer form.**  For a prime `p ≥ 5`, `p²` divides
`∑_{k=1}^{p-1} (p-1)!/k`, the numerator of `H_{p-1}` over the common
denominator `(p-1)!`. -/
theorem sq_dvd_sum_factorial_div {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    p ^ 2 ∣ ∑ k ∈ Ico 1 p, (p - 1).factorial / k := by
  set N := (p - 1).factorial with hN
  have hdvd : ∀ k ∈ Ico 1 p, k ∣ N := fun k hk =>
    Nat.dvd_factorial (mem_Ico.mp hk).1 (by have := (mem_Ico.mp hk).2; omega)
  have hrefl : ∑ k ∈ Ico 1 p, N / (p - k) = ∑ k ∈ Ico 1 p, N / k := by
    apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
    · intro k hk; simp only [mem_Ico] at hk ⊢; omega
    · intro k hk; simp only [mem_Ico] at hk ⊢; omega
    · intro k hk; simp only [mem_Ico] at hk; omega
    · intro k hk; simp only [mem_Ico] at hk; omega
    · intro k _; rfl
  have hnotdvd : ∀ k ∈ Ico 1 p, ¬ p ∣ k := fun k hk hd => by
    have := Nat.le_of_dvd (mem_Ico.mp hk).1 hd
    have := (mem_Ico.mp hk).2
    omega
  have hrefl_mem : ∀ k ∈ Ico 1 p, p - k ∈ Ico 1 p := fun k hk => by
    simp only [mem_Ico] at hk ⊢; omega
  -- `b k = N / k + N / (p - k)` satisfies `k (p - k) b k = p N`.
  have hb : ∀ k ∈ Ico 1 p, k * (p - k) * (N / k + N / (p - k)) = p * N := by
    intro k hk
    have h1 := Nat.mul_div_cancel' (hdvd k hk)
    have h2 := Nat.mul_div_cancel' (hdvd (p - k) (hrefl_mem k hk))
    have hkp : k + (p - k) = p := by have := (mem_Ico.mp hk).2; omega
    calc k * (p - k) * (N / k + N / (p - k))
        = (p - k) * (k * (N / k)) + k * ((p - k) * (N / (p - k))) := by ring
      _ = (k + (p - k)) * N := by rw [h1, h2]; ring
      _ = p * N := by rw [hkp]
  have hpb : ∀ k ∈ Ico 1 p, p ∣ N / k + N / (p - k) := by
    intro k hk
    have hd : p ∣ k * (p - k) * (N / k + N / (p - k)) := by
      rw [hb k hk]; exact dvd_mul_right p N
    rcases (Nat.Prime.dvd_mul hp).mp hd with hd' | hd'
    · rcases (Nat.Prime.dvd_mul hp).mp hd' with hd'' | hd''
      · exact absurd hd'' (hnotdvd k hk)
      · exact absurd hd'' (hnotdvd (p - k) (hrefl_mem k hk))
    · exact hd'
  set c : ℕ → ℕ := fun k => (N / k + N / (p - k)) / p with hc
  have hcb : ∀ k ∈ Ico 1 p, p * c k = N / k + N / (p - k) := fun k hk =>
    Nat.mul_div_cancel' (hpb k hk)
  have hcN : ∀ k ∈ Ico 1 p, k * (p - k) * c k = N := by
    intro k hk
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc p * (k * (p - k) * c k) = k * (p - k) * (p * c k) := by ring
      _ = p * N := by rw [hcb k hk, hb k hk]
  have hcmod : ∀ k ∈ Ico 1 p, (k : ZMod p) ^ 2 * (c k : ZMod p) = -(N : ZMod p) := by
    intro k hk
    have hcast := congrArg (fun n : ℕ => (n : ZMod p)) (hcN k hk)
    simp only [Nat.cast_mul] at hcast
    rw [Nat.cast_sub (mem_Ico.mp hk).2.le, ZMod.natCast_self] at hcast
    rw [← hcast]; ring
  have hpc : p ∣ ∑ k ∈ Ico 1 p, c k := dvd_sum_of_sq_mul_eq hp h5 c _ hcmod
  have htwo : 2 * ∑ k ∈ Ico 1 p, N / k = p * ∑ k ∈ Ico 1 p, c k := by
    calc 2 * ∑ k ∈ Ico 1 p, N / k
        = ∑ k ∈ Ico 1 p, N / k + ∑ k ∈ Ico 1 p, N / (p - k) := by rw [hrefl]; ring
      _ = ∑ k ∈ Ico 1 p, p * c k := by
          rw [← sum_add_distrib]; exact sum_congr rfl fun k hk => (hcb k hk).symm
      _ = p * ∑ k ∈ Ico 1 p, c k := by rw [mul_sum]
  have hsq : p ^ 2 ∣ 2 * ∑ k ∈ Ico 1 p, N / k := by
    rw [htwo, pow_two]; exact Nat.mul_dvd_mul_left p hpc
  have hcop : Nat.Coprime (p ^ 2) 2 :=
    Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  exact hcop.dvd_of_dvd_mul_left hsq

/-- `H_{p-1} = (∑_{k=1}^{p-1} (p-1)!/k) / (p-1)!` for a prime `p` (each `k < p`
divides `(p-1)!`). -/
theorem harmonic_eq_sum_div_factorial {p : ℕ} (hp : p.Prime) :
    harmonic (p - 1) =
      ((∑ k ∈ Ico 1 p, (p - 1).factorial / k : ℕ) : ℚ) / ((p - 1).factorial : ℚ) := by
  have hIcc : Icc 1 (p - 1) = Ico 1 p := by
    ext k; simp only [mem_Icc, mem_Ico]; have := hp.pos; omega
  have hN0 : ((p - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [harmonic_eq_sum_Icc, hIcc, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Ico.mp hk).1)
  have hdvd : k ∣ (p - 1).factorial :=
    Nat.dvd_factorial (mem_Ico.mp hk).1 (by have := (mem_Ico.mp hk).2; omega)
  rw [Nat.cast_div hdvd hk0]
  field_simp

/-- **Wolstenholme's theorem (a).**  For every prime `p ≥ 5`, the numerator of
the harmonic number `H_{p-1} = 1 + 1/2 + ⋯ + 1/(p-1)` (in lowest terms) is
divisible by `p²`. -/
theorem sq_dvd_harmonic_num {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ (harmonic (p - 1)).num := by
  set N := (p - 1).factorial with hN
  set S := ∑ k ∈ Ico 1 p, N / k with hS
  set H := harmonic (p - 1) with hH
  have hHS : H = (S : ℚ) / (N : ℚ) := harmonic_eq_sum_div_factorial hp
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hden0 : (H.den : ℚ) ≠ 0 := by exact_mod_cast H.den_nz
  have hcross : H.num * (N : ℤ) = (S : ℤ) * (H.den : ℤ) := by
    have hq : (H.num : ℚ) / (H.den : ℚ) = (S : ℚ) / (N : ℚ) := by rw [Rat.num_div_den, hHS]
    rw [div_eq_div_iff hden0 hN0] at hq
    exact_mod_cast hq
  have hSdvd : (p : ℤ) ^ 2 ∣ (S : ℤ) := by exact_mod_cast sq_dvd_sum_factorial_div hp h5
  have hdvd : (p : ℤ) ^ 2 ∣ H.num * (N : ℤ) := by
    rw [hcross]; exact Dvd.dvd.mul_right hSdvd _
  have hcopN : Nat.Coprime (p ^ 2) N := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp, Nat.Prime.dvd_factorial hp]
    omega
  have hcopZ : IsCoprime ((p : ℤ) ^ 2) (N : ℤ) := by
    rw [← Nat.cast_pow]; exact Nat.isCoprime_iff_coprime.mpr hcopN
  exact hcopZ.dvd_of_dvd_mul_right hdvd

/-- For a prime `p` and `j < p`, `C(p-1, j) ≡ (-1)^j (mod p)`. -/
theorem choose_pred_cast_zmod {p : ℕ} (hp : p.Prime) :
    ∀ j < p, (((p - 1).choose j : ℕ) : ZMod p) = (-1) ^ j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hsucc : p.choose (j + 1) = (p - 1).choose j + (p - 1).choose (j + 1) := by
      have hp1 : p = (p - 1) + 1 := by have := hp.pos; omega
      conv_lhs => rw [hp1]
      exact Nat.choose_succ_succ (p - 1) j
    have hzero : ((p.choose (j + 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hp.dvd_choose_self (Nat.succ_ne_zero j) hj)
    rw [hsucc, Nat.cast_add, ih (by omega)] at hzero
    rw [pow_succ]
    linear_combination hzero

/-- `C(2p, p) = 2 · C(2p-1, p-1)` for `p ≥ 1`. -/
theorem central_choose_eq {p : ℕ} (hp1 : 1 ≤ p) :
    (2 * p).choose p = 2 * (2 * p - 1).choose (p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, Nat.add_sub_cancel,
    show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ, Nat.choose_symm_half]
  ring

/-- For a prime `p ≥ 5`, `p³ ∣ ∑_{k=1}^{p-1} C(p,k)²`: each
`C(p,k)² ≡ p² k⁻² (mod p³)` and `∑ k⁻² ≡ 0 (mod p)`. -/
theorem cube_dvd_sum_choose_sq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ ∑ k ∈ Ico 1 p, ((p.choose k : ℕ) : ℤ) ^ 2 := by
  haveI := Fact.mk hp
  set N := (p - 1).factorial with hN
  have hdvd : ∀ k ∈ Ico 1 p, k ∣ N := fun k hk =>
    Nat.dvd_factorial (mem_Ico.mp hk).1 (by have := (mem_Ico.mp hk).2; omega)
  -- `k · C(p, k) = p · C(p - 1, k - 1)`
  have hkchoose : ∀ k ∈ Ico 1 p, k * p.choose k = p * (p - 1).choose (k - 1) := by
    intro k hk
    have h := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
    have hp1 : p - 1 + 1 = p := by have := hp.pos; omega
    have hk1 : k - 1 + 1 = k := by have := (mem_Ico.mp hk).1; omega
    rw [hp1, hk1] at h
    rw [h, mul_comm]
  -- each term: `p ^ 3 ∣ N ^ 2 C(p,k) ^ 2 - p ^ 2 (N / k) ^ 2`
  have hterm : ∀ k ∈ Ico 1 p,
      (p : ℤ) ^ 3 ∣ (N : ℤ) ^ 2 * ((p.choose k : ℕ) : ℤ) ^ 2 - (p : ℤ) ^ 2 * ((N / k : ℕ) : ℤ) ^ 2 := by
    intro k hk
    have hNk : ((N / k : ℕ) : ℤ) * (k : ℤ) = (N : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel (hdvd k hk)
    have hkc : (k : ℤ) * ((p.choose k : ℕ) : ℤ) = (p : ℤ) * (((p - 1).choose (k - 1) : ℕ) : ℤ) := by
      exact_mod_cast hkchoose k hk
    have hmodp : (p : ℤ) ∣ (((p - 1).choose (k - 1) : ℕ) : ℤ) ^ 2 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [choose_pred_cast_zmod hp (k - 1) (by have := (mem_Ico.mp hk).2; omega)]
      rw [← pow_mul, mul_comm, pow_mul]; simp
    have hid : (N : ℤ) ^ 2 * ((p.choose k : ℕ) : ℤ) ^ 2 - (p : ℤ) ^ 2 * ((N / k : ℕ) : ℤ) ^ 2
        = (p : ℤ) ^ 2 * ((N / k : ℕ) : ℤ) ^ 2 * ((((p - 1).choose (k - 1) : ℕ) : ℤ) ^ 2 - 1) := by
      rw [← hNk]
      linear_combination (((N / k : ℕ) : ℤ)) ^ 2 * ((k : ℤ) * ((p.choose k : ℕ) : ℤ) + (p : ℤ) * (((p - 1).choose (k - 1) : ℕ) : ℤ)) * hkc
    rw [hid, show (p : ℤ) ^ 3 = (p : ℤ) ^ 2 * (p : ℤ) by ring]
    exact mul_dvd_mul (dvd_mul_right _ _) hmodp
  -- the sum of `(N / k) ^ 2` is divisible by `p`
  have hsumsq : p ∣ ∑ k ∈ Ico 1 p, (N / k) ^ 2 := by
    apply dvd_sum_of_sq_mul_eq hp h5 (fun k => (N / k) ^ 2) ((N : ZMod p) ^ 2)
    intro k hk
    have hNk : ((N / k : ℕ) : ZMod p) * (k : ZMod p) = (N : ZMod p) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvd k hk)]
    simp only [Nat.cast_pow]
    rw [← hNk]; ring
  have hsumsqZ : (p : ℤ) ∣ ∑ k ∈ Ico 1 p, ((N / k : ℕ) : ℤ) ^ 2 := by exact_mod_cast hsumsq
  have htot : (p : ℤ) ^ 3 ∣ (N : ℤ) ^ 2 * ∑ k ∈ Ico 1 p, ((p.choose k : ℕ) : ℤ) ^ 2 := by
    have hdiff := Finset.dvd_sum hterm
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum] at hdiff
    have hsecond : (p : ℤ) ^ 3 ∣ (p : ℤ) ^ 2 * ∑ k ∈ Ico 1 p, ((N / k : ℕ) : ℤ) ^ 2 := by
      rw [show (p : ℤ) ^ 3 = (p : ℤ) ^ 2 * (p : ℤ) by ring]
      exact mul_dvd_mul_left _ hsumsqZ
    have hsum := dvd_add hdiff hsecond
    rwa [sub_add_cancel] at hsum
  have hcopN : Nat.Coprime (p ^ 3) (N ^ 2) := by
    apply Nat.Coprime.pow
    rw [Nat.Prime.coprime_iff_not_dvd hp, Nat.Prime.dvd_factorial hp]
    omega
  have hcopZ : IsCoprime ((p : ℤ) ^ 3) ((N : ℤ) ^ 2) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow]; exact Nat.isCoprime_iff_coprime.mpr hcopN
  exact hcopZ.dvd_of_dvd_mul_left htot

/-- **Wolstenholme's theorem (b).**  For every prime `p ≥ 5`,
`C(2p-1, p-1) ≡ 1 (mod p³)`. -/
theorem wolstenholme_choose {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
  have hsplit : ∑ k ∈ range (p + 1), ((p.choose k : ℕ) : ℤ) ^ 2
      = 2 + ∑ k ∈ Ico 1 p, ((p.choose k : ℕ) : ℤ) ^ 2 := by
    rw [sum_range_succ, range_eq_Ico, sum_eq_sum_Ico_succ_bot hp.pos]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_pow]
    ring
  have hvdm : ∑ k ∈ range (p + 1), ((p.choose k : ℕ) : ℤ) ^ 2
      = 2 * (((2 * p - 1).choose (p - 1) : ℕ) : ℤ) := by
    have h := Nat.sum_range_choose_sq p
    rw [central_choose_eq hp.pos] at h
    exact_mod_cast h
  have hcube := cube_dvd_sum_choose_sq hp h5
  have hmid : (p : ℤ) ^ 3 ∣ 2 * ((((2 * p - 1).choose (p - 1) : ℕ) : ℤ) - 1) := by
    have h2 : 2 * ((((2 * p - 1).choose (p - 1) : ℕ) : ℤ) - 1)
        = ∑ k ∈ Ico 1 p, ((p.choose k : ℕ) : ℤ) ^ 2 := by linarith
    rw [h2]; exact hcube
  have hcop : IsCoprime ((p : ℤ) ^ 3) 2 := by
    rw [← Nat.cast_pow, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl]
    exact Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow_left 3 ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)))
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact dvd_sub_comm.mp (hcop.dvd_of_dvd_mul_left hmid)

/-! ## Ground truth and the boundary at `p = 3` -/

/-- `p = 5`: `C(9, 4) = 126 ≡ 1 (mod 125)`. -/
example : (2 * 5 - 1).choose (5 - 1) ≡ 1 [MOD 5 ^ 3] := by decide

/-- `p = 5`: `H_4 = 25/12`, whose numerator is `25 = 5²`. -/
example : (harmonic (5 - 1)).num = 25 := by
  rw [show harmonic (5 - 1) = ((25 : ℤ) : ℚ) / ((12 : ℤ) : ℚ) by norm_num [harmonic]]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

/-- `p = 3` fails (b): `C(5, 2) = 10 ≢ 1 (mod 27)`. -/
example : ¬ (2 * 3 - 1).choose (3 - 1) ≡ 1 [MOD 3 ^ 3] := by decide

/-- `p = 3` fails (a): `H_2 = 3/2`, numerator `3`, not divisible by `9`. -/
example : ¬ (3 : ℤ) ^ 2 ∣ (harmonic (3 - 1)).num := by
  rw [show harmonic (3 - 1) = ((3 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) by norm_num [harmonic],
    Rat.num_div_eq_of_coprime (by norm_num) (by decide)]
  decide

/-- The hypotheses are jointly satisfiable: the theorems apply at `p = 7`. -/
example : (7 : ℤ) ^ 2 ∣ (harmonic (7 - 1)).num ∧
    (2 * 7 - 1).choose (7 - 1) ≡ 1 [MOD 7 ^ 3] :=
  ⟨sq_dvd_harmonic_num (by norm_num) (by norm_num),
    wolstenholme_choose (by norm_num) (by norm_num)⟩

end NumberComplexity.Wolstenholme
