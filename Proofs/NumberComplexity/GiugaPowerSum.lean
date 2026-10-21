/-
# Giuga's 1950 theorem: the power-sum characterization

## Source

* G. Giuga, "Su una presumibile proprietà caratteristica dei numeri primi",
  Rend. Ist. Lombardo Sci. Lett. A 83 (1950) 511–528.
* D. Borwein, J. M. Borwein, P. B. Borwein, R. Girgensohn, "Giuga's conjecture
  on primality", Amer. Math. Monthly 103 (1996) 40–50 (restates Giuga's theorem).

## Informal statement (verbatim from the target card)

For composite n > 1: sum_{k=1}^{n-1} k^{n-1} ≡ -1 (mod n) if and only if, for
every prime p | n, p | (n/p - 1) and (p - 1) | (n/p - 1). Equivalently, n is both
a Giuga number and a Carmichael number.

## Formalization notes (2026-10-21)

* `-1 (mod n)` is spelled `S % n = n - 1`; with `1 < n` the subtraction `n - 1`
  is off its junk value.  For `p ∈ n.primeFactors`, `p ∣ n`, so `n / p` is the
  exact cofactor and `1 ≤ n / p`; `n / p - 1` is therefore genuine.
* The proof works for every `n > 1`; compositeness is not used.
  `sum_pow_mod_eq_sub_one_iff` is the general form and `giuga_1950` adds the
  source's hypothesis `¬ n.Prime` verbatim.
* Giuga's conjecture (open) asserts that no composite `n` satisfies either side.
* Route: modulo a prime `p ∣ n` with `n = p * m`, periodicity gives
  `∑_{k<n} k^(n-1) ≡ m · ∑_{x ∈ 𝔽_p} x^(n-1)`, and `FiniteField.sum_pow_units`
  evaluates the inner sum to `-1` or `0`.  The local conditions force `n`
  squarefree, and `Finset.prod_primes_dvd` glues the prime moduli.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.GiugaPowerSum

open Finset

/-- A sum over `ZMod p` (`p ≠ 0`) is the sum over the residues `0, 1, …, p - 1`. -/
theorem sum_zmod_eq_sum_range {p : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ x : ZMod p, f x = ∑ i ∈ range p, f (i : ZMod p) := by
  refine Finset.sum_nbij' (fun x : ZMod p => x.val) (fun i : ℕ => (i : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro i _
    exact Finset.mem_univ _
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro i hi
    exact ZMod.val_cast_of_lt (Finset.mem_range.1 hi)
  · intro x _
    rw [ZMod.natCast_zmod_val]

/-- Periodicity: summing `k ^ e` in `ZMod p` over `k < p * m` gives `m` copies of the
full residue sum `∑ x : ZMod p, x ^ e`. -/
theorem sum_range_mul_cast_pow (p m e : ℕ) [NeZero p] :
    ∑ k ∈ range (p * m), (k : ZMod p) ^ e = m * ∑ x : ZMod p, x ^ e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_zmod_eq_sum_range]
    simp [add_mul]

/-- Power sums over the prime field: for `e ≠ 0`,
`∑ x : ZMod p, x ^ e = -1` if `p - 1 ∣ e` and `0` otherwise. -/
theorem sum_zmod_pow {p : ℕ} [Fact p.Prime] {e : ℕ} (he : e ≠ 0) :
    ∑ x : ZMod p, x ^ e = if p - 1 ∣ e then -1 else 0 := by
  classical
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    ∑ x : ZMod p, x ^ e = ∑ x ∈ univ \ {(0 : ZMod p)}, x ^ e := by
      rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow he, add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ e) := by simp [φ, ← hmap, univ.sum_map φ]
    _ = if p - 1 ∣ e then -1 else 0 := by
      rw [FiniteField.sum_pow_units (ZMod p) e, ZMod.card]

/-- `S ≡ -1 (mod n)` in the residue form `S % n = n - 1` is the same as `n ∣ S + 1`. -/
theorem mod_eq_sub_one_iff_dvd_add_one {S n : ℕ} (hn : 0 < n) : S % n = n - 1 ↔ n ∣ S + 1 := by
  have hr : S % n < n := Nat.mod_lt S hn
  have hdecomp : S + 1 = n * (S / n) + (S % n + 1) := by
    have := Nat.div_add_mod S n
    omega
  rw [hdecomp, Nat.dvd_add_right (Nat.dvd_mul_right n _)]
  constructor
  · intro h
    rw [h, Nat.sub_add_cancel hn]
  · intro h
    have hle : n ≤ S % n + 1 := Nat.le_of_dvd (Nat.succ_pos _) h
    omega

/-- For `1 < n` the `k = 0` term `0 ^ (n - 1)` vanishes, so the Giuga sum over
`1 ≤ k < n` equals the sum over `k < n`. -/
theorem sum_Ico_one_eq_sum_range {n : ℕ} (hn : 1 < n) :
    ∑ k ∈ Ico 1 n, k ^ (n - 1) = ∑ k ∈ range n, k ^ (n - 1) := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < n), zero_pow (by omega), zero_add]

/-- Casting the power sum into `ZMod p` commutes with the sum and the powers. -/
theorem zmod_cast_sum {p n : ℕ} :
    ((∑ k ∈ range n, k ^ (n - 1) : ℕ) : ZMod p) = ∑ k ∈ range n, (k : ZMod p) ^ (n - 1) := by
  push_cast
  rfl

/-- Local criterion at a prime `p` (with `n = p * m`, `m ≥ 1`):
`∑_{k<n} k^(n-1) ≡ -1 (mod p)` iff `p - 1 ∣ n - 1` and `m ≡ 1 (mod p)`. -/
theorem prime_dvd_sum_add_one_iff {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hn : 1 < p * m) :
    p ∣ (∑ k ∈ range (p * m), k ^ (p * m - 1)) + 1 ↔ p - 1 ∣ p * m - 1 ∧ p ∣ m - 1 := by
  haveI := Fact.mk hp
  have he : p * m - 1 ≠ 0 := by omega
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff (m - 1) p,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hm.ne'), Nat.cast_add, zmod_cast_sum,
    sum_range_mul_cast_pow, sum_zmod_pow he, Nat.cast_one]
  split_ifs with hdvd
  · simp only [hdvd, true_and]
    constructor
    · intro h
      linear_combination -h
    · intro h
      linear_combination -h
  · simp only [mul_zero, zero_add, one_ne_zero, hdvd, false_and]

/-- Since `p * m - 1 = (p - 1) * m + (m - 1)`, `p - 1 ∣ p * m - 1 ↔ p - 1 ∣ m - 1`. -/
theorem sub_one_dvd_mul_sub_one_iff {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    p - 1 ∣ p * m - 1 ↔ p - 1 ∣ m - 1 := by
  have hid : p * m - 1 = (p - 1) * m + (m - 1) := by
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hid, Nat.dvd_add_right (Nat.dvd_mul_right _ _)]

/-- If `p ∣ n / p - 1` for every prime `p ∣ n` (and `n ≠ 0`), then `n` is squarefree:
a square factor `p * p ∣ n` would force `p ∣ n / p` and hence `p ∣ 1`. -/
theorem squarefree_of_forall_dvd_div_sub_one {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ∣ n / p - 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := (Nat.dvd_mul_right p p).trans hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩
  have hdiv : p ∣ n / p := by
    obtain ⟨c, hc⟩ := hpp
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact Nat.dvd_mul_right p c
  have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos
  have h1 : p ∣ n / p - (n / p - 1) := Nat.dvd_sub hdiv (h p hmem)
  rw [Nat.sub_sub_self hpos] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

/-- Giuga's power-sum characterization for every `n > 1` (prime or not):
`∑_{k=1}^{n-1} k^(n-1) ≡ -1 (mod n)` iff for every prime `p ∣ n`,
`p ∣ n/p - 1` and `(p - 1) ∣ n/p - 1`. -/
theorem sum_pow_mod_eq_sub_one_iff {n : ℕ} (hn : 1 < n) :
    (∑ k ∈ Ico 1 n, k ^ (n - 1)) % n = n - 1 ↔
      ∀ p ∈ n.primeFactors, p ∣ n / p - 1 ∧ p - 1 ∣ n / p - 1 := by
  rw [mod_eq_sub_one_iff_dvd_add_one (by omega), sum_Ico_one_eq_sum_range hn]
  have hloc : ∀ p ∈ n.primeFactors,
      (p ∣ (∑ k ∈ range n, k ^ (n - 1)) + 1 ↔ p ∣ n / p - 1 ∧ p - 1 ∣ n / p - 1) := by
    intro p hp
    obtain ⟨hpr, hpn, -⟩ := Nat.mem_primeFactors.1 hp
    have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hpr.pos
    have hnm : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
    have key := prime_dvd_sum_add_one_iff hpr hm (hnm ▸ hn)
    have hsub := sub_one_dvd_mul_sub_one_iff hpr.pos hm
    rw [← hnm] at key hsub
    rw [hsub] at key
    rw [key, and_comm]
  constructor
  · intro h p hp
    exact (hloc p hp).1 ((Nat.dvd_of_mem_primeFactors hp).trans h)
  · intro h
    have hsf : Squarefree n := squarefree_of_forall_dvd_div_sub_one (by omega) (fun p hp => (h p hp).1)
    have hprod := Finset.prod_primes_dvd ((∑ k ∈ range n, k ^ (n - 1)) + 1)
      (fun p hp => Nat.prime_iff.1 (Nat.prime_of_mem_primeFactors hp))
      (fun p hp => (hloc p hp).2 (h p hp))
    rwa [Nat.prod_primeFactors_of_squarefree hsf] at hprod

/-- **Giuga (1950).**  For composite `n > 1`,
`∑_{k=1}^{n-1} k^(n-1) ≡ -1 (mod n)` if and only if every prime `p ∣ n` satisfies
`p ∣ n/p - 1` and `(p - 1) ∣ n/p - 1` (i.e. `n` is both a Giuga number and a
Carmichael number). -/
theorem giuga_1950 {n : ℕ} (hn : 1 < n) (_hc : ¬ n.Prime) :
    (∑ k ∈ Ico 1 n, k ^ (n - 1)) % n = n - 1 ↔
      ∀ p ∈ n.primeFactors, p ∣ n / p - 1 ∧ (p - 1) ∣ n / p - 1 :=
  sum_pow_mod_eq_sub_one_iff hn

/-- The prime case of the same congruence: for a prime `p`,
`∑_{k=1}^{p-1} k^(p-1) ≡ -1 (mod p)`. -/
theorem sum_pow_mod_prime {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ Ico 1 p, k ^ (p - 1)) % p = p - 1 := by
  rw [sum_pow_mod_eq_sub_one_iff hp.one_lt, hp.primeFactors]
  intro q hq
  rw [Finset.mem_singleton.1 hq, Nat.div_self hp.pos]
  exact ⟨dvd_zero _, dvd_zero _⟩

/-! ## Ground truth and non-vacuity -/

/-- The hypotheses of `giuga_1950` are jointly satisfiable (`n = 4`). -/
example : 1 < 4 ∧ ¬ Nat.Prime 4 := by decide

/-- At `n = 4`: `1 + 8 + 27 = 36 ≡ 0 (mod 4)`, so the congruence side fails. -/
example : (∑ k ∈ Ico 1 4, k ^ (4 - 1)) % 4 = 0 := by decide

/-- At `n = 4` the theorem transports the failure: some prime factor violates
the local conditions. -/
example : ¬ ∀ p ∈ (4 : ℕ).primeFactors, p ∣ 4 / p - 1 ∧ (p - 1) ∣ 4 / p - 1 := by
  rw [← giuga_1950 (by norm_num) (by decide)]
  decide

/-- The prime case at `p = 5`: `1 + 16 + 81 + 256 = 354 ≡ 4 (mod 5)`. -/
example : (∑ k ∈ Ico 1 5, k ^ (5 - 1)) % 5 = 5 - 1 := by decide

end Candidates.GiugaPowerSum
