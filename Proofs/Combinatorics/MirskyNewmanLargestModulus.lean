/-
# Davenport–Rado / Mirsky–Newman: the largest covering modulus repeats

Fabienne Chouraqui, *About an extension of the Davenport-Rado result to the
Herzog-Schönheim conjecture for free groups*, arXiv:1901.09898, Introduction
after Theorem A, cites the classical theorem of Davenport–Rado and
Mirsky–Newman (c. 1950), with the strengthening of Newman and Znám.
This is the integer case of Erdős problem 274 (Herzog–Schönheim).

For an exact covering of `ℤ` by at least two residue classes, the largest
modulus repeats. The proof uses roots of unity:

* `sum_root_pow_residue_eq_zero`: for a maximal modulus bound `N ≥ 2` and a
  primitive `N`-th root `ζ`, the residues `r_i` of the classes of modulus
  exactly `N` satisfy `∑ ζ ^ r_i = 0`;
* `exists_ne_modulus_eq_of_max` (main theorem): the largest modulus occurs
  at least twice;
* `not_injective_modulus` (Erdős #274 for `ℤ`): the moduli are not distinct;
* `prime_dvd_card_max_modulus` (prime-power strengthening): if the largest
  modulus is `p ^ k` with `k > 0`, then `p` divides its multiplicity (via
  divisibility by the cyclotomic polynomial `Φ_{p^k}` and `Φ_{p^k}(1) = p`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.MirskyNewmanLargestModulus

open Finset

/-- A family of residue classes `a i mod d i` is an *exact covering* (a coset
partition of `ℤ`) when every integer lies in exactly one of the classes. -/
def IsExactCover {ι : Type*} (d : ι → ℕ) (a : ι → ℤ) : Prop :=
  ∀ x : ℤ, ∃! i, (d i : ℤ) ∣ x - a i

/-- `{0 mod 2, 1 mod 4, 3 mod 4}` is an exact covering. -/
theorem isExactCover_two_four_four : IsExactCover ![2, 4, 4] ![0, 1, 3] := by
  intro x
  have hcases : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  obtain ⟨i, hi⟩ : ∃ i : Fin 3,
      (((![2, 4, 4] : Fin 3 → ℕ) i : ℕ) : ℤ) ∣ x - (![0, 1, 3] : Fin 3 → ℤ) i := by
    rcases hcases with h | h | h | h
    · exact ⟨0, by simp; omega⟩
    · exact ⟨1, by simp; omega⟩
    · exact ⟨0, by simp; omega⟩
    · exact ⟨2, by simp; omega⟩
  refine ⟨i, hi, fun j hj => ?_⟩
  fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> omega

/-- `{0 mod 2, 0 mod 3}` is not an exact covering (`1` is missed). -/
example : ¬ IsExactCover ![2, 3] ![0, 0] := by
  intro h
  obtain ⟨i, hi, -⟩ := h 1
  fin_cases i <;> simp_all


/-- Splitting a sum over `[0, m d)` into `m` blocks of length `d`. -/
theorem sum_range_mul_eq_sum_sum {M : Type*} [AddCommMonoid M] (m d : ℕ) (f : ℕ → M) :
    ∑ x ∈ range (m * d), f x = ∑ j ∈ range m, ∑ s ∈ range d, f (j * d + s) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A geometric sum of a ratio `x ≠ 1` with `x ^ n = 1` vanishes. -/
theorem geom_sum_eq_zero_of_pow_eq_one (x : ℂ) (n : ℕ) (hx : x ≠ 1) (h : x ^ n = 1) :
    ∑ i ∈ range n, x ^ i = 0 := by
  rw [geom_sum_eq hx, h, sub_self, zero_div]

/-- For `0 ≤ s < d`, `s ≡ a (mod d)` holds exactly when `s` is the least
nonnegative residue of `a`. -/
theorem natCast_dvd_sub_iff_eq_toNat_emod (d s : ℕ) (a : ℤ) (hd : 0 < d) (hs : s < d) :
    (d : ℤ) ∣ (s : ℤ) - a ↔ s = (a % d).toNat := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have h0 : 0 ≤ a % d := Int.emod_nonneg _ hd'.ne'
  have h1 : a % d < d := Int.emod_lt_of_pos _ hd'
  rw [← Int.modEq_iff_dvd]
  constructor
  · intro h
    have : (s : ℤ) % d = s := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hs)
    unfold Int.ModEq at h
    omega
  · intro h
    unfold Int.ModEq
    have : (s : ℤ) = a % d := by omega
    rw [this, Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- The sum of `ζ ^ x` over `x ∈ [0, L)` in the class `a mod d` (with
`d ∣ L`) equals `ζ ^ r * ∑_{j < L/d} (ζ ^ d) ^ j`, `r` the residue of `a`. -/
theorem sum_range_ite_dvd_eq (ζ : ℂ) (d L : ℕ) (a : ℤ) (hd : 0 < d) (hdL : d ∣ L) :
    ∑ x ∈ range L, (if (d : ℤ) ∣ (x : ℤ) - a then ζ ^ x else 0) =
      ζ ^ (a % d).toNat * ∑ j ∈ range (L / d), (ζ ^ d) ^ j := by
  obtain ⟨m, rfl⟩ := hdL
  rw [Nat.mul_div_cancel_left _ hd, mul_comm d m, sum_range_mul_eq_sum_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcond : ∀ s ∈ range d, ((d : ℤ) ∣ ((j * d + s : ℕ) : ℤ) - a ↔ s = (a % d).toNat) := by
    intro s hs
    rw [← natCast_dvd_sub_iff_eq_toNat_emod d s a hd (Finset.mem_range.mp hs)]
    have : (((j * d + s : ℕ) : ℤ) - a) = ((s : ℤ) - a) + (d : ℤ) * j := by push_cast; ring
    rw [this, dvd_add_left (dvd_mul_right _ _)]
  rw [Finset.sum_congr rfl (fun s hs => if_congr (hcond s hs) rfl rfl)]
  have hr : (a % d).toNat ∈ range d := by
    have hd' : (0 : ℤ) < d := by exact_mod_cast hd
    have h0 : 0 ≤ a % d := Int.emod_nonneg _ hd'.ne'
    have h1 : a % d < d := Int.emod_lt_of_pos _ hd'
    rw [Finset.mem_range]; omega
  rw [Finset.sum_ite_eq' _ _ (fun s => ζ ^ (j * d + s)), if_pos hr]
  rw [pow_add, ← pow_mul, mul_comm, mul_comm j d]

/-- Roots-of-unity identity for an exact covering: if every modulus is at
most `N ≥ 2` and `ζ` is a primitive `N`-th root of unity, then the residues
of the classes of modulus exactly `N` satisfy `∑ ζ ^ r_i = 0`. -/
theorem sum_root_pow_residue_eq_zero {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : ∀ i, 0 < d i)
    (hexact : IsExactCover d a) (N : ℕ) (hN : 1 < N)
    (hmax : ∀ i, d i ≤ N) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N) :
    ∑ i ∈ univ.filter (fun i => d i = N), ζ ^ (a i % d i).toNat = 0 := by
  classical
  set L : ℕ := N * ∏ i, d i with hLdef
  have hdivL : ∀ i, d i ∣ L := fun i =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) N
  have hNL : N ∣ L := dvd_mul_right _ _
  have hL : 0 < L := Nat.mul_pos (by omega) (Finset.prod_pos fun i _ => hd i)
  have hζL : ζ ^ L = 1 := (hζ.pow_eq_one_iff_dvd L).mpr hNL
  -- the full geometric sum vanishes
  have hfull : ∑ x ∈ range L, ζ ^ x = 0 := geom_sum_eq_zero_of_pow_eq_one ζ L (hζ.ne_one hN) hζL
  -- exactness splits it along the classes
  have hsplit : ∑ x ∈ range L, ζ ^ x =
      ∑ i, ∑ x ∈ range L, (if (d i : ℤ) ∣ (x : ℤ) - a i then ζ ^ x else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨i, hi, huniq⟩ := hexact x
    rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (huniq j h))
      (fun h => absurd (Finset.mem_univ i) h), if_pos hi]
  -- each class contributes zero unless its modulus is `N`
  have hclass : ∀ i, ∑ x ∈ range L, (if (d i : ℤ) ∣ (x : ℤ) - a i then ζ ^ x else 0) =
      if d i = N then ζ ^ (a i % d i).toNat * ((L / N : ℕ) : ℂ) else 0 := by
    intro i
    rw [sum_range_ite_dvd_eq ζ (d i) L (a i) (hd i) (hdivL i)]
    split_ifs with hiN
    · rw [hiN, hζ.pow_eq_one]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · have hlt : d i < N := lt_of_le_of_ne (hmax i) hiN
      have hne : ζ ^ d i ≠ 1 := by
        rw [Ne, hζ.pow_eq_one_iff_dvd]
        exact fun h => absurd (Nat.le_of_dvd (hd i) h) (not_le.mpr hlt)
      have hpow : (ζ ^ d i) ^ (L / d i) = 1 := by
        rw [← pow_mul, Nat.mul_div_cancel' (hdivL i), hζL]
      rw [geom_sum_eq_zero_of_pow_eq_one _ _ hne hpow, mul_zero]
  have htot : (∑ i ∈ univ.filter (fun i => d i = N), ζ ^ (a i % d i).toNat) *
      ((L / N : ℕ) : ℂ) = 0 := by
    rw [Finset.sum_mul, Finset.sum_filter]
    calc ∑ i, (if d i = N then ζ ^ (a i % d i).toNat * ((L / N : ℕ) : ℂ) else 0)
        = ∑ i, ∑ x ∈ range L, (if (d i : ℤ) ∣ (x : ℤ) - a i then ζ ^ x else 0) :=
          Finset.sum_congr rfl fun i _ => (hclass i).symm
      _ = 0 := by rw [← hsplit, hfull]
  have hLN : ((L / N : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hL hNL) (by omega)).ne'
  exact (mul_eq_zero.mp htot).resolve_right hLN

/-- **Davenport-Rado / Mirsky-Newman.** If finitely many residue classes
`a i mod d i` (`d i > 0`), at least two of them, partition `ℤ`, then the
largest modulus `d i₀` is attained by some other class `j ≠ i₀`. -/
theorem exists_ne_modulus_eq_of_max {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : ∀ i, 0 < d i)
    (hexact : IsExactCover d a) (htwo : 1 < Fintype.card ι)
    (i₀ : ι) (hmax : ∀ i, d i ≤ d i₀) : ∃ j, j ≠ i₀ ∧ d j = d i₀ := by
  classical
  by_contra hne
  push Not at hne
  have hN : 1 < d i₀ := by
    by_contra h1
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card htwo i₀
    have := hd j
    have := hmax j
    exact hne j hj (by omega)
  have hζ := Complex.isPrimitiveRoot_exp (d i₀) (by omega)
  have hkey := sum_root_pow_residue_eq_zero d a hd hexact (d i₀) hN hmax _ hζ
  have hfilter : univ.filter (fun i => d i = d i₀) = {i₀} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => by_contra fun hi => hne i hi h, fun h => h ▸ rfl⟩
  rw [hfilter, Finset.sum_singleton] at hkey
  exact pow_ne_zero _ (hζ.ne_zero (by omega)) hkey

/-- **Prime-power strengthening (Newman, Znám).** If the residue classes
`a i mod d i` partition `ℤ` and the largest modulus is `p ^ k` with `p` prime
and `k > 0`, then `p` divides the number of classes of that modulus. -/
theorem prime_dvd_card_max_modulus {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : ∀ i, 0 < d i)
    (hexact : IsExactCover d a) (i₀ : ι) (hmax : ∀ i, d i ≤ d i₀)
    (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (hN : d i₀ = p ^ k) :
    p ∣ (univ.filter (fun i => d i = d i₀)).card := by
  classical
  have hN1 : 1 < d i₀ := hN ▸ Nat.one_lt_pow hk.ne' hp.one_lt
  have hζ := Complex.isPrimitiveRoot_exp (d i₀) (by omega)
  have hkey := sum_root_pow_residue_eq_zero d a hd hexact (d i₀) hN1 hmax _ hζ
  set S := univ.filter (fun i => d i = d i₀) with hS
  let f : Polynomial ℤ := ∑ i ∈ S, Polynomial.X ^ (a i % d i).toNat
  have hf : Polynomial.aeval (Complex.exp (2 * Real.pi * Complex.I / (d i₀ : ℂ))) f = 0 := by
    simp only [f, map_sum, map_pow, Polynomial.aeval_X]
    exact hkey
  have hdvd : Polynomial.cyclotomic (d i₀) ℤ ∣ f := by
    rw [Polynomial.cyclotomic_eq_minpoly hζ (by omega)]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral (by omega)) hf
  obtain ⟨g, hg⟩ := hdvd
  have heval : (S.card : ℤ) = p * g.eval 1 := by
    have h1 : f.eval 1 = S.card := by simp [f, Polynomial.eval_finsetSum]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← h1, hg, Polynomial.eval_mul, hN, Polynomial.eval_one_cyclotomic_prime_pow]
  exact Int.natCast_dvd_natCast.mp ⟨_, heval⟩

/-- **Erdős #274 for `ℤ`.** A partition of `ℤ` into at least two residue
classes never has pairwise distinct moduli. -/
theorem not_injective_modulus {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : ∀ i, 0 < d i) (hexact : IsExactCover d a) (htwo : 1 < Fintype.card ι) :
    ¬ Function.Injective d := by
  intro hinj
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i₀, hmax⟩ := Finite.exists_max d
  obtain ⟨j, hj, hdj⟩ := exists_ne_modulus_eq_of_max d a hd hexact htwo i₀ hmax
  exact hj (hinj hdj)

/-- Non-vacuity: the hypotheses of the main theorem hold jointly for
`{0 mod 2, 1 mod 4, 3 mod 4}`, whose largest modulus `4 = 2 ^ 2` repeats. -/
example : ∃ j : Fin 3, j ≠ 1 ∧ (![2, 4, 4] : Fin 3 → ℕ) j = (![2, 4, 4] : Fin 3 → ℕ) 1 := by
  exact exists_ne_modulus_eq_of_max ![2, 4, 4] ![0, 1, 3] (by decide)
    isExactCover_two_four_four (by decide) 1 (by decide)

/-- Non-vacuity of the prime-power strengthening on the same covering:
the largest modulus `4 = 2 ^ 2` occurs an even number of times. -/
example : 2 ∣ (univ.filter fun i : Fin 3 =>
    (![2, 4, 4] : Fin 3 → ℕ) i = (![2, 4, 4] : Fin 3 → ℕ) 1).card :=
  prime_dvd_card_max_modulus ![2, 4, 4] ![0, 1, 3] (by decide) isExactCover_two_four_four 1
    (by decide) 2 2 Nat.prime_two (by norm_num) (by decide)

end Candidates.MirskyNewmanLargestModulus
