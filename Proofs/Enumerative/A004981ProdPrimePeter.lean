/-
Bala's congruence for OEIS A004981 (Peter Bala, Dec 22 2019).

For a(n) = 2^n ∏_{k<n}(4k+1) / n!, the division is exact and
 a(pn) ≡ a(n) (mod p²) for every n ≥ 0 and prime p ≡ 1 (mod 4).
The proof uses the recurrence n a(n) = 2(4n-3)a(n-1)
(R. J. Mathar, Mar 14 2014), block products, and cancellation modulo p².
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Candidates.A004981ProdPrimePeter

/-- `P n = ∏_{k=0}^{n-1} (4k+1)`, the product in the OEIS definition. -/
def P (n : ℕ) : ℕ := ∏ k ∈ range n, (4 * k + 1)

/-- OEIS A004981: `a(n) = (2^n / n!) * ∏_{k=0}^{n-1} (4k+1)`, with the division in `ℕ`;
`factorial_dvd` shows it is exact. -/
def a (n : ℕ) : ℕ := 2 ^ n * P n / n.factorial

/-- Integrality: `n! ∣ 2ⁿ ∏_{k<n} (4k+1)`. The `2`-part of `n!` is below `2ⁿ`; the odd part
`m` divides `∏ (4k+1) ≡ 4ⁿ ∏ (c+k) (mod m)` with `4c ≡ 1`, an ascending factorial. -/
theorem factorial_dvd (n : ℕ) : n.factorial ∣ 2 ^ n * P n := by
  obtain ⟨e, m, hm, hfac⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.factorial_ne_zero n)
  rw [hfac]
  apply mul_dvd_mul
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h : 2 ^ e ∣ (0 : ℕ).factorial := Dvd.intro _ hfac.symm
      simpa using h
    · apply Nat.pow_dvd_pow
      have h1 : emultiplicity 2 n.factorial < n := Nat.emultiplicity_two_factorial_lt hn.ne'
      have h2 : (e : ℕ∞) ≤ emultiplicity 2 n.factorial :=
        le_emultiplicity_of_pow_dvd (hfac ▸ dvd_mul_right _ _)
      have := lt_of_le_of_lt h2 h1
      exact_mod_cast this.le
  · have hm0 : NeZero m := ⟨by rintro rfl; simp at hm⟩
    have hcop : Nat.Coprime 4 m := by
      have : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hm
      simpa using Nat.Coprime.pow_left 2 this
    set c : ℕ := ((4 : ZMod m)⁻¹).val with hc
    have hc4 : (4 : ZMod m) * (c : ZMod m) = 1 := by
      rw [hc, ZMod.natCast_zmod_val]
      exact_mod_cast ZMod.coe_mul_inv_eq_one 4 hcop
    have hdvd : m ∣ c.ascFactorial n :=
      (Dvd.intro_left _ hfac.symm).trans (Nat.factorial_dvd_ascFactorial c n)
    rw [← ZMod.natCast_eq_zero_iff] at hdvd ⊢
    have hP : (P n : ZMod m) = 4 ^ n * (c.ascFactorial n : ZMod m) := by
      rw [P, Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_prod,
        show (4 : ZMod m) ^ n = ∏ _i ∈ range n, (4 : ZMod m) by simp, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      push_cast
      linear_combination hc4.symm
    rw [hP, hdvd, mul_zero]


/-- First-order expansion: `∏ (c i + p x) ≡ ∏ c i + p x ∑_i ∏_{j ≠ i} c j (mod p²)`. -/
theorem prod_add_expand {ι : Type*} [DecidableEq ι] (p x : ℤ) (c : ι → ℤ) (S : Finset ι) :
    p ^ 2 ∣ ∏ i ∈ S, (c i + p * x) -
      (∏ i ∈ S, c i + p * x * ∑ i ∈ S, ∏ j ∈ S.erase i, c j) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S haS ih =>
    obtain ⟨t, ht⟩ := ih
    have hsum : ∑ i ∈ insert a S, ∏ j ∈ (insert a S).erase i, c j =
        ∏ j ∈ S, c j + c a * ∑ i ∈ S, ∏ j ∈ S.erase i, c j := by
      rw [Finset.sum_insert haS, Finset.erase_insert haS, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => haS (h ▸ hi)
      rw [Finset.erase_insert_of_ne (Ne.symm hia), Finset.prod_insert
        (fun h => haS (Finset.mem_of_mem_erase h))]
    rw [Finset.prod_insert haS, Finset.prod_insert haS, hsum]
    refine ⟨(c a + p * x) * t + x ^ 2 * ∑ i ∈ S, ∏ j ∈ S.erase i, c j, ?_⟩
    have ht' : ∏ i ∈ S, (c i + p * x) =
        ∏ i ∈ S, c i + p * x * ∑ i ∈ S, ∏ j ∈ S.erase i, c j + p ^ 2 * t := by
      linear_combination ht
    rw [ht']
    ring

/-- A family of `p - 1` pairwise incongruent nonzero residues hits every nonzero residue. -/
theorem image_eq_univ_erase {ι : Type*} (p : ℕ) [Fact p.Prime] (S : Finset ι) (c : ι → ℤ)
    (hinj : Set.InjOn (fun i => (c i : ZMod p)) S) (hne : ∀ i ∈ S, (c i : ZMod p) ≠ 0)
    (hcard : S.card = p - 1) :
    S.image (fun i => (c i : ZMod p)) = univ.erase 0 := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_erase.mpr ⟨hne i hi, Finset.mem_univ _⟩
  · rw [Finset.card_image_of_injOn hinj, hcard, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]

/-- For a complete system of nonzero residues modulo an odd prime `p`, the first-order
coefficient `∑_i ∏_{j ≠ i} c j` vanishes modulo `p` (it is `(∏ c) ∑ y⁻¹` and `∑ y = 0`). -/
theorem sum_prod_erase_dvd {ι : Type*} [DecidableEq ι] (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (S : Finset ι) (c : ι → ℤ)
    (hinj : Set.InjOn (fun i => (c i : ZMod p)) S) (hne : ∀ i ∈ S, (c i : ZMod p) ≠ 0)
    (hcard : S.card = p - 1) :
    (p : ℤ) ∣ ∑ i ∈ S, ∏ j ∈ S.erase i, c j := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have herase : ∀ i ∈ S, ∏ j ∈ S.erase i, (c j : ZMod p) =
      (∏ j ∈ S, (c j : ZMod p)) * (c i : ZMod p)⁻¹ := by
    intro i hi
    rw [← Finset.prod_erase_mul S _ hi, mul_assoc, mul_inv_cancel₀ (hne i hi), mul_one]
  rw [Finset.sum_congr rfl herase, ← Finset.mul_sum]
  have hsum : ∑ i ∈ S, (c i : ZMod p)⁻¹ = 0 := by
    have himg := image_eq_univ_erase p S c hinj hne hcard
    rw [← Finset.sum_image (f := fun y : ZMod p => y⁻¹) hinj, himg]
    have hinv : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
      Equiv.sum_comp (Equiv.inv (ZMod p)) (fun y => y)
    rw [Finset.sum_erase _ (by simp), hinv]
    have h := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 1 (by
      have := hp.out.two_le
      rw [ZMod.card]; omega)
    simpa using h
  rw [hsum, mul_zero]


/-- Generic block congruence: if the `c i` (`i ∈ S`) form a complete system of nonzero
residues modulo an odd prime `p`, then shifting every factor by the same multiple `p * x`
does not change the product modulo `p ^ 2`. -/
theorem prod_add_mul_dvd {ι : Type*} [DecidableEq ι] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (S : Finset ι) (c : ι → ℤ)
    (hinj : Set.InjOn (fun i => (c i : ZMod p)) S) (hne : ∀ i ∈ S, (c i : ZMod p) ≠ 0)
    (hcard : S.card = p - 1) (x : ℤ) :
    (p : ℤ) ^ 2 ∣ ∏ i ∈ S, (c i + p * x) - ∏ i ∈ S, c i := by
  obtain ⟨t, ht⟩ := sum_prod_erase_dvd p hp2 S c hinj hne hcard
  have hexp := prod_add_expand (p : ℤ) x c S
  rw [ht] at hexp
  have h2 : (p : ℤ) ^ 2 ∣ (p : ℤ) * x * ((p : ℤ) * t) := ⟨x * t, by ring⟩
  have heq : ∏ i ∈ S, (c i + p * x) - ∏ i ∈ S, c i =
      (∏ i ∈ S, (c i + p * x) - (∏ i ∈ S, c i + p * x * (p * t))) + p * x * (p * t) := by ring
  rw [heq]
  exact dvd_add hexp h2

/-- Two complete systems of nonzero residues modulo `p` have congruent products modulo `p`. -/
theorem prod_sub_prod_dvd {ι κ : Type*} (p : ℕ) [Fact p.Prime]
    (S : Finset ι) (c : ι → ℤ)
    (hinj : Set.InjOn (fun i => (c i : ZMod p)) S) (hne : ∀ i ∈ S, (c i : ZMod p) ≠ 0)
    (hcard : S.card = p - 1)
    (T : Finset κ) (d : κ → ℤ)
    (hinj' : Set.InjOn (fun i => (d i : ZMod p)) T) (hne' : ∀ i ∈ T, (d i : ZMod p) ≠ 0)
    (hcard' : T.card = p - 1) :
    (p : ℤ) ∣ ∏ i ∈ S, c i - ∏ i ∈ T, d i := by
  classical
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [← Finset.prod_image (f := fun y : ZMod p => y) hinj,
    ← Finset.prod_image (f := fun y : ZMod p => y) hinj', image_eq_univ_erase p S c hinj hne hcard,
    image_eq_univ_erase p T d hinj' hne' hcard', sub_self]

/-- Natural numbers below `p` that are congruent modulo `p` are equal. -/
theorem eq_of_dvd_sub_of_lt {p j j' : ℕ} (hj : j < p) (hj' : j' < p)
    (h : (p : ℤ) ∣ (j : ℤ) - j') : j = j' := by
  have hmod : j' ≡ j [MOD p] := Nat.modEq_iff_dvd.mpr h
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj', eq_comm] at hmod

/-- For a prime `p ≡ 1 (mod 4)`, the only `j < p` with `p ∣ 4 j + 1` is `j = p / 4`. -/
theorem eq_of_dvd_four_mul_add_one {p j : ℕ} (h4 : p % 4 = 1) (hj : j < p)
    (h : p ∣ 4 * j + 1) : j = p / 4 := by
  obtain ⟨t, ht⟩ := h
  have hp0 : 0 < p := by omega
  have ht4 : t < 4 := by
    by_contra hcon
    push Not at hcon
    have : p * 4 ≤ p * t := Nat.mul_le_mul_left p hcon
    omega
  interval_cases t <;> omega

/-- The residues `4 j + 1` (`j < p`, `j ≠ p / 4`) are pairwise incongruent modulo `p`. -/
theorem injOn_four_mul_add_one (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 1) (s : ℤ)
    (hs : s = 1 ∨ s = -1) :
    Set.InjOn (fun j : ℕ => ((s * (4 * (j : ℤ) + 1) : ℤ) : ZMod p)) ((range p).erase (p / 4)) := by
  intro j hj j' hj' hjj
  simp only [Finset.coe_erase, Finset.coe_range, Set.mem_sdiff, Set.mem_Iio,
    Set.mem_singleton_iff] at hj hj'
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hjj.symm
  have hfac : s * (4 * (j : ℤ) + 1) - s * (4 * (j' : ℤ) + 1) = (s * 4) * ((j : ℤ) - j') := by ring
  rw [hfac] at hdvd
  have hpr : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rcases hpr.dvd_or_dvd hdvd with h | h
  · exfalso
    have h' : (p : ℤ) ∣ 4 := by
      rcases hs with rfl | rfl
      · simpa using h
      · simpa using h
    have h'' : p ∣ 4 := by exact_mod_cast h'
    have := Nat.le_of_dvd (by norm_num) h''
    have := hp.out.two_le
    interval_cases p <;> simp_all
  · exact eq_of_dvd_sub_of_lt hj.1 hj'.1 h

/-- The residues `4 j + 1` (`j < p`, `j ≠ p / 4`) are nonzero modulo `p`. -/
theorem four_mul_add_one_ne_zero (p : ℕ) [Fact p.Prime] (h4 : p % 4 = 1) (s : ℤ)
    (hs : s = 1 ∨ s = -1) :
    ∀ j ∈ (range p).erase (p / 4), ((s * (4 * (j : ℤ) + 1) : ℤ) : ZMod p) ≠ 0 := by
  intro j hj hzero
  rw [Finset.mem_erase, Finset.mem_range] at hj
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  have h1 : (p : ℤ) ∣ ((4 * j + 1 : ℕ) : ℤ) := by
    rcases hs with rfl | rfl
    · simpa using hzero
    · rw [neg_one_mul, dvd_neg] at hzero
      push_cast
      exact hzero
  exact hj.1 (eq_of_dvd_four_mul_add_one h4 hj.2 (by exact_mod_cast h1))

/-- The residues `j + 1` (`j < p - 1`) are pairwise incongruent modulo `p`. -/
theorem injOn_add_one (p : ℕ) :
    Set.InjOn (fun j : ℕ => (((j : ℤ) + 1 : ℤ) : ZMod p)) (range (p - 1)) := by
  intro j hj j' hj' hjj
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hjj.symm
  have hfac : (j : ℤ) + 1 - ((j' : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) - ((j' + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hfac] at hdvd
  have := eq_of_dvd_sub_of_lt (by omega) (by omega) hdvd
  omega

/-- The residues `j + 1` (`j < p - 1`) are nonzero modulo `p`. -/
theorem add_one_ne_zero (p : ℕ) :
    ∀ j ∈ range (p - 1), (((j : ℤ) + 1 : ℤ) : ZMod p) ≠ 0 := by
  intro j hj hzero
  rw [Finset.mem_range] at hj
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  have h1 : p ∣ j + 1 := by exact_mod_cast hzero
  have := Nat.le_of_dvd (by omega) h1
  omega


/-- The `m`-th block of the factorial: `∏_{j=1}^{p-1} (m p + j)`. -/
def D (p m : ℕ) : ℕ := ∏ j ∈ range (p - 1), (m * p + j + 1)

/-- The `m`-th block of `∏ (4k+1)` with the multiple of `p` removed:
`∏_{j < p, j ≠ p/4} (4 p m + 4 j + 1)`. -/
def N (p m : ℕ) : ℕ := ∏ j ∈ (range p).erase (p / 4), (4 * p * m + 4 * j + 1)

/-- `D p m ≡ (p - 1)! (mod p²)` for every odd prime `p`. -/
theorem D_dvd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    (p : ℤ) ^ 2 ∣ (D p m : ℤ) - ((p - 1).factorial : ℕ) := by
  have h := prod_add_mul_dvd p hp2 (range (p - 1)) (fun j : ℕ => (j : ℤ) + 1)
    (injOn_add_one p) (add_one_ne_zero p) (Finset.card_range _) (m : ℤ)
  have hD : (D p m : ℤ) = ∏ j ∈ range (p - 1), ((j : ℤ) + 1 + p * m) := by
    rw [D, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast
    ring
  have hF : (((p - 1).factorial : ℕ) : ℤ) = ∏ j ∈ range (p - 1), ((j : ℤ) + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
    push_cast
    rfl
  rw [hD, hF]
  exact h

/-- `N p m ≡ N p 0 (mod p²)` for every prime `p ≡ 1 (mod 4)`. -/
theorem N_dvd (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 1) (m : ℕ) :
    (p : ℤ) ^ 2 ∣ (N p m : ℤ) - (N p 0 : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  have hcard : ((range p).erase (p / 4)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  have h := prod_add_mul_dvd p hp2 ((range p).erase (p / 4))
    (fun j : ℕ => 1 * (4 * (j : ℤ) + 1)) (injOn_four_mul_add_one p h4 1 (Or.inl rfl))
    (four_mul_add_one_ne_zero p h4 1 (Or.inl rfl)) hcard (4 * m : ℤ)
  have hN : ∀ m' : ℕ, (N p m' : ℤ) =
      ∏ j ∈ (range p).erase (p / 4), (1 * (4 * (j : ℤ) + 1) + p * (4 * m')) := by
    intro m'
    rw [N, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hN m, hN 0]
  simpa using h


/-- `4ⁿ (2n)! ∏_{k<n} (4k+1)(4k+3) = (4n)!`. -/
theorem four_pow_mul_factorial_mul_prod (n : ℕ) :
    4 ^ n * (2 * n).factorial * ∏ k ∈ range n, ((4 * k + 1) * (4 * k + 3)) =
      (4 * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ← ih]
    ring

/-- The exact identity `4^(p-1) · N p 0 · B₃ = D p 2 · D p 3`, where
`B₃ = ∏_{j < p, j ≠ p/4} (4p - (4j+1))` is the product of the residues `≡ 3 (mod 4)`
below `4p` other than `3p`. -/
theorem four_pow_mul_N_mul_B3 (p : ℕ) (hp : 0 < p) (h4 : p % 4 = 1) :
    (4 : ℤ) ^ (p - 1) * (N p 0 : ℤ) *
        ∏ j ∈ (range p).erase (p / 4), (-1 * (4 * (j : ℤ) + 1) + p * 4) =
      (D p 2 : ℤ) * (D p 3 : ℤ) := by
  have hj0 : p / 4 ∈ range p := Finset.mem_range.mpr (by omega)
  -- The class `1 (mod 4)`
  have hR1 : (∏ k ∈ range p, (4 * k + 1) : ℕ) = N p 0 * p := by
    rw [← Finset.prod_erase_mul _ _ hj0, N]
    congr 1
    · simp
    · omega
  -- The class `3 (mod 4)`, reflected
  have hR3 : ((∏ k ∈ range p, (4 * k + 3) : ℕ) : ℤ) =
      (∏ j ∈ (range p).erase (p / 4), (-1 * (4 * (j : ℤ) + 1) + p * 4)) * (3 * p) := by
    rw [← Finset.prod_range_reflect, Nat.cast_prod, ← Finset.prod_erase_mul _ _ hj0]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hjp : j < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
      have hsum : 4 * (p - 1 - j) + 3 + (4 * j + 1) = 4 * p := by omega
      have hsumZ : ((4 * (p - 1 - j) + 3 : ℕ) : ℤ) + (4 * (j : ℤ) + 1) = 4 * p := by
        exact_mod_cast hsum
      linear_combination hsumZ
    · have h3 : 4 * (p - 1 - p / 4) + 3 = 3 * p := by omega
      rw [h3]
      push_cast
      ring
  -- The factorial ratio `(4p)! / (2p)!`
  have hF : (4 * p).factorial = (2 * p).factorial * (D p 2 * (3 * p) * (D p 3 * (4 * p))) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_add_one_eq_factorial,
      show 4 * (q + 1) = 2 * (q + 1) + ((q + 1) + (q + 1)) by ring, Finset.prod_range_add,
      Finset.prod_range_add, Finset.prod_range_succ, Finset.prod_range_succ, D, D,
      show q + 1 - 1 = q by omega]
    simp only [show ∀ x, 2 * (q + 1) + ((q + 1) + x) + 1 = 3 * (q + 1) + x + 1 from
      fun x => by ring]
    ring
  have hmain := four_pow_mul_factorial_mul_prod p
  rw [Finset.prod_mul_distrib, hR1, hF] at hmain
  have hmainZ := congrArg (fun t : ℕ => (t : ℤ)) hmain
  push_cast at hmainZ hR3
  rw [hR3] at hmainZ
  have hne : ((2 * p).factorial : ℤ) * (12 * (p : ℤ) ^ 2) ≠ 0 := by
    have : ((2 * p).factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    positivity
  apply mul_left_cancel₀ hne
  have h4p : (4 : ℤ) ^ p = 4 * 4 ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h4p] at hmainZ
  linear_combination hmainZ


/-- **Core congruence** (equivalent to `a p ≡ 2 (mod p²)`): for a prime `p ≡ 1 (mod 4)`,
`2^(p-1) · ∏_{j < p, j ≠ p/4} (4j+1) ≡ (p-1)! (mod p²)`. -/
theorem two_pow_mul_N_zero_dvd (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 1) :
    (p : ℤ) ^ 2 ∣ (2 : ℤ) ^ (p - 1) * (N p 0 : ℤ) - ((p - 1).factorial : ℕ) := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : 0 < p := hp.out.pos
  have hcard : ((range p).erase (p / 4)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  set Y : ℤ := (((p - 1).factorial : ℕ) : ℤ) with hY
  set N0 : ℤ := (N p 0 : ℤ) with hN0
  set X : ℤ := (2 : ℤ) ^ (p - 1) * N0 with hX
  set B3 : ℤ := ∏ j ∈ (range p).erase (p / 4), (-1 * (4 * (j : ℤ) + 1) + p * 4) with hB3
  -- `B3 ≡ N0 (mod p²)`
  have hB3N0 : (p : ℤ) ^ 2 ∣ B3 - N0 := by
    have h := prod_add_mul_dvd p hp2 ((range p).erase (p / 4))
      (fun j : ℕ => -1 * (4 * (j : ℤ) + 1)) (injOn_four_mul_add_one p h4 (-1) (Or.inr rfl))
      (four_mul_add_one_ne_zero p h4 (-1) (Or.inr rfl)) hcard 4
    have hsign : ∏ j ∈ (range p).erase (p / 4), (-1 * (4 * (j : ℤ) + 1)) = N0 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, hN0, N, Nat.cast_prod]
      have hev : (-1 : ℤ) ^ (p - 1) = 1 := by
        rw [show p - 1 = 2 * (2 * (p / 4)) by omega, pow_mul]
        norm_num
      rw [hev, one_mul]
      refine Finset.prod_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [← hsign]
    exact h
  -- `X² ≡ Y² (mod p²)`
  have hsq : (p : ℤ) ^ 2 ∣ X ^ 2 - Y ^ 2 := by
    have hid := four_pow_mul_N_mul_B3 p hp0 h4
    rw [← hN0, ← hB3] at hid
    have hD2 := D_dvd p hp2 2
    have hD3 := D_dvd p hp2 3
    have heq : X ^ 2 - Y ^ 2 = (4 : ℤ) ^ (p - 1) * N0 * (N0 - B3) +
        ((D p 2 : ℤ) * ((D p 3 : ℤ) - Y) + Y * ((D p 2 : ℤ) - Y)) := by
      rw [hX]
      have h4' : (4 : ℤ) ^ (p - 1) = ((2 : ℤ) ^ (p - 1)) ^ 2 := by
        rw [← pow_mul, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
      linear_combination hid - N0 ^ 2 * h4'
    rw [heq]
    refine dvd_add (Dvd.dvd.mul_left ?_ _) (dvd_add (Dvd.dvd.mul_left hD3 _)
      (Dvd.dvd.mul_left hD2 _))
    rw [← neg_sub]
    exact (dvd_neg).mpr hB3N0
  -- `X ≡ Y (mod p)`
  have hlin : (p : ℤ) ∣ X - Y := by
    have hferm : (p : ℤ) ∣ (2 : ℤ) ^ (p - 1) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.pow_card_sub_one_eq_one (by
        intro h0
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
        rw [ZMod.natCast_eq_zero_iff] at this
        have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
        exact hp2 this), sub_self]
    have hmodp : (p : ℤ) ∣ N0 - Y := by
      have h := prod_sub_prod_dvd p ((range p).erase (p / 4))
        (fun j : ℕ => 1 * (4 * (j : ℤ) + 1)) (injOn_four_mul_add_one p h4 1 (Or.inl rfl))
        (four_mul_add_one_ne_zero p h4 1 (Or.inl rfl)) hcard
        (range (p - 1)) (fun j : ℕ => (j : ℤ) + 1) (injOn_add_one p) (add_one_ne_zero p)
        (Finset.card_range _)
      have hN0' : N0 = ∏ j ∈ (range p).erase (p / 4), (1 * (4 * (j : ℤ) + 1)) := by
        rw [hN0, N, Nat.cast_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        push_cast
        ring
      have hY' : Y = ∏ j ∈ range (p - 1), ((j : ℤ) + 1) := by
        rw [hY, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
        push_cast
        rfl
      rw [hN0', hY']
      exact h
    have heq : X - Y = ((2 : ℤ) ^ (p - 1) - 1) * N0 + (N0 - Y) := by rw [hX]; ring
    rw [heq]
    exact dvd_add (Dvd.dvd.mul_right hferm _) hmodp
  -- `p ∤ X + Y`, hence `p²` is coprime to `X + Y`
  have hpr : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hYp : ¬ (p : ℤ) ∣ Y := by
    intro h
    rw [hY] at h
    have h' : p ∣ (p - 1).factorial := by exact_mod_cast h
    rw [hp.out.dvd_factorial] at h'
    omega
  have hsum : ¬ (p : ℤ) ∣ X + Y := by
    intro h
    have h2Y : (p : ℤ) ∣ 2 * Y := by
      have : 2 * Y = (X + Y) - (X - Y) := by ring
      rw [this]
      exact dvd_sub h hlin
    rcases hpr.dvd_or_dvd h2Y with h2 | h2
    · have : p ∣ 2 := by exact_mod_cast h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    · exact hYp h2
  have hcop : IsCoprime ((p : ℤ) ^ 2) (X + Y) :=
    ((Prime.coprime_iff_not_dvd hpr).mpr hsum).pow_left
  have hfac : X ^ 2 - Y ^ 2 = (X + Y) * (X - Y) := by ring
  rw [hfac] at hsq
  exact hcop.dvd_of_dvd_mul_left hsq


/-- `a n · n! = 2ⁿ ∏_{k<n} (4k+1)`: the division defining `a` is exact. -/
theorem a_mul_factorial (n : ℕ) : a n * n.factorial = 2 ^ n * P n :=
  Nat.div_mul_cancel (factorial_dvd n)

/-- The recurrence `(n+1) a(n+1) = 2 (4n+1) a(n)` (R. J. Mathar's D-finite form). -/
theorem succ_mul_a_succ (n : ℕ) : (n + 1) * a (n + 1) = 2 * (4 * n + 1) * a n := by
  have h1 := a_mul_factorial (n + 1)
  have h0 := a_mul_factorial n
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n)
  calc (n + 1) * a (n + 1) * n.factorial = a (n + 1) * (n + 1).factorial := by
        rw [Nat.factorial_succ]; ring
    _ = 2 ^ (n + 1) * P (n + 1) := h1
    _ = 2 * (4 * n + 1) * (2 ^ n * P n) := by rw [P, P, Finset.prod_range_succ]; ring
    _ = 2 * (4 * n + 1) * a n * n.factorial := by rw [← h0]; ring

/-- Iterated recurrence: `a(m+k) ∏_{j<k} (m+j+1) = a(m) ∏_{j<k} 2(4(m+j)+1)`. -/
theorem a_add_mul_prod (m k : ℕ) :
    a (m + k) * ∏ j ∈ range k, (m + j + 1) = a m * ∏ j ∈ range k, (2 * (4 * (m + j) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hr := succ_mul_a_succ (m + k)
    calc a (m + (k + 1)) * ((∏ j ∈ range k, (m + j + 1)) * (m + k + 1))
        = ((m + k + 1) * a (m + k + 1)) * ∏ j ∈ range k, (m + j + 1) := by
          rw [← add_assoc]; ring
      _ = (a (m + k) * ∏ j ∈ range k, (m + j + 1)) * (2 * (4 * (m + k) + 1)) := by
          rw [hr]; ring
      _ = a m * ((∏ j ∈ range k, (2 * (4 * (m + j) + 1))) * (2 * (4 * (m + k) + 1))) := by
          rw [ih]; ring

/-- One block of length `p`: `a(p(n+1)) (n+1) D p n = a(pn) 2^p (4n+1) N p n`. -/
theorem a_block (p : ℕ) (hp : 0 < p) (h4 : p % 4 = 1) (n : ℕ) :
    a (p * (n + 1)) * (n + 1) * D p n = a (p * n) * 2 ^ p * (4 * n + 1) * N p n := by
  have h := a_add_mul_prod (p * n) p
  have hj0 : p / 4 ∈ range p := Finset.mem_range.mpr (by omega)
  have hprodD : ∏ j ∈ range p, (p * n + j + 1) = D p n * (p * (n + 1)) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Finset.prod_range_succ, D, show q + 1 - 1 = q by omega]
    simp only [show ∀ j, (q + 1) * n + j + 1 = n * (q + 1) + j + 1 from fun j => by ring]
    ring
  have hprodN : ∏ j ∈ range p, (2 * (4 * (p * n + j) + 1)) = 2 ^ p * (N p n * (p * (4 * n + 1))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Finset.prod_erase_mul _ _ hj0, N]
    congr 1
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      ring
    · have : 4 * (p / 4) + 1 = p := by omega
      calc 4 * (p * n + p / 4) + 1 = 4 * p * n + (4 * (p / 4) + 1) := by ring
        _ = p * (4 * n + 1) := by rw [this]; ring
  rw [show p * n + p = p * (n + 1) by ring, hprodD, hprodN] at h
  apply Nat.eq_of_mul_eq_mul_right hp
  calc a (p * (n + 1)) * (n + 1) * D p n * p = a (p * (n + 1)) * (D p n * (p * (n + 1))) := by ring
    _ = a (p * n) * (2 ^ p * (N p n * (p * (4 * n + 1)))) := h
    _ = a (p * n) * 2 ^ p * (4 * n + 1) * N p n * p := by ring

/-- Exact product identity:
`a(pn) ∏_{m<n} D p m = a(n) ∏_{m<n} 2^(p-1) N p m`. -/
theorem a_mul_prod_D (p : ℕ) (hp : 0 < p) (h4 : p % 4 = 1) (n : ℕ) :
    a (p * n) * ∏ m ∈ range n, D p m = a n * ∏ m ∈ range n, (2 ^ (p - 1) * N p m) := by
  induction n with
  | zero => simp [a, P]
  | succ n ih =>
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
    have hblk := a_block p hp h4 n
    have hrec := succ_mul_a_succ n
    have h2p : 2 ^ p = 2 * 2 ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    calc (n + 1) * (a (p * (n + 1)) * ((∏ m ∈ range n, D p m) * D p n))
        = (a (p * (n + 1)) * (n + 1) * D p n) * ∏ m ∈ range n, D p m := by ring
      _ = (a (p * n) * ∏ m ∈ range n, D p m) * 2 ^ p * (4 * n + 1) * N p n := by
          rw [hblk]; ring
      _ = ((n + 1) * a (n + 1)) * ((∏ m ∈ range n, (2 ^ (p - 1) * N p m)) *
            (2 ^ (p - 1) * N p n)) := by
          rw [ih, hrec, h2p]; ring
      _ = (n + 1) * (a (n + 1) * ((∏ m ∈ range n, (2 ^ (p - 1) * N p m)) *
            (2 ^ (p - 1) * N p n))) := by ring

/-- For every prime `p ≡ 1 (mod 4)` and every `n` (including `n = 0`),
`a(p n) ≡ a(n) (mod p²)`. -/
theorem a_prime_mul_modEq (p n : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) :
    a (p * n) ≡ a n [MOD p ^ 2] := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  set Y : ℤ := (((p - 1).factorial : ℕ) : ℤ) with hY
  have hDprod : (∏ m ∈ range n, (D p m : ℤ)) ≡ ∏ _m ∈ range n, Y [ZMOD (p : ℤ) ^ 2] :=
    Int.ModEq.prod fun m _ => ((Int.modEq_iff_dvd).mpr (D_dvd p hp2 m)).symm
  have hNprod : (∏ m ∈ range n, ((2 : ℤ) ^ (p - 1) * (N p m : ℤ))) ≡
      ∏ _m ∈ range n, Y [ZMOD (p : ℤ) ^ 2] := by
    refine Int.ModEq.prod fun m _ => ?_
    have h1 : (2 : ℤ) ^ (p - 1) * (N p m : ℤ) ≡ 2 ^ (p - 1) * (N p 0 : ℤ) [ZMOD (p : ℤ) ^ 2] :=
      ((Int.modEq_iff_dvd.mpr (N_dvd p h4 m)).symm).mul_left _
    have h2 : (2 : ℤ) ^ (p - 1) * (N p 0 : ℤ) ≡ Y [ZMOD (p : ℤ) ^ 2] :=
      (Int.modEq_iff_dvd.mpr (two_pow_mul_N_zero_dvd p h4)).symm
    exact h1.trans h2
  have hE := congrArg (fun t : ℕ => (t : ℤ)) (a_mul_prod_D p hp.pos h4 n)
  push_cast at hE
  have hmod : (a (p * n) : ℤ) * ∏ _m ∈ range n, Y ≡
      (a n : ℤ) * ∏ _m ∈ range n, Y [ZMOD (p : ℤ) ^ 2] :=
    calc (a (p * n) : ℤ) * ∏ _m ∈ range n, Y
        ≡ (a (p * n) : ℤ) * ∏ m ∈ range n, (D p m : ℤ) [ZMOD (p : ℤ) ^ 2] :=
          hDprod.symm.mul_left _
      _ = (a n : ℤ) * ∏ m ∈ range n, ((2 : ℤ) ^ (p - 1) * (N p m : ℤ)) := hE
      _ ≡ (a n : ℤ) * ∏ _m ∈ range n, Y [ZMOD (p : ℤ) ^ 2] := hNprod.mul_left _
  rw [Finset.prod_const, Finset.card_range] at hmod
  have hdvd := Int.modEq_iff_dvd.mp hmod
  rw [← sub_mul] at hdvd
  have hpr : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hYp : ¬ (p : ℤ) ∣ Y := by
    intro h
    rw [hY] at h
    have h' : p ∣ (p - 1).factorial := by exact_mod_cast h
    rw [hp.dvd_factorial] at h'
    have := hp.pos
    omega
  have hcop : IsCoprime ((p : ℤ) ^ 2) (Y ^ n) :=
    ((Prime.coprime_iff_not_dvd hpr).mpr hYp).pow
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact hcop.dvd_of_dvd_mul_right hdvd

/-! ## The conjecture -/

/-- Bala's congruence for positive `n` (OEIS A004981). The stronger theorem
`a_prime_mul_modEq` also covers `n=0`. -/
theorem bala_conjecture (p n : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) (_hn : 0 < n) :
    a (p * n) ≡ a n [MOD p ^ 2] :=
  a_prime_mul_modEq p n hp h4

/-! ## Sanity layer -/

-- The first eight terms of the OEIS DATA line.
example : (List.range 8).map a = [1, 2, 10, 60, 390, 2652, 18564, 132600] := by decide

-- The hypotheses hold jointly at `p = 5`, `n = 1`, where the conclusion
-- reads `a 5 = 2652 ≡ 2 = a 1 (mod 25)`.
example : Nat.Prime 5 ∧ 5 % 4 = 1 ∧ 0 < 1 ∧ a (5 * 1) ≡ a 1 [MOD 5 ^ 2] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide⟩

-- The hypothesis `p ≡ 1 (mod 4)` is key: at `p = 3`, `a 3 = 60 ≢ 2 (mod 9)`.
example : ¬ a (3 * 1) ≡ a 1 [MOD 3 ^ 2] := by decide

end Candidates.A004981ProdPrimePeter
