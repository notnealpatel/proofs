/-
# A106303 — Wu: periods of the Fibonacci 5-step sequence modulo prime powers

OEIS A106303, Chai Wah Wu: the pentanacci least period satisfies
`a(5^k) = 781·5^(k-1)` for `k ≥ 1`. For prime `p`, if `a(p) ≠ a(p²)`,
then `a(p^k) = p^(k-1)·a(p)` for `k ≥ 1`.
The sequence starts `0, 0, 0, 0, 1`, with each later term the sum of
the previous five (A001591).

Let `M` be the companion matrix of the recurrence, acting on the state
vectors `st n = (s n, …, s (n+4))`.  The Hankel matrix `K` with columns
`st 0, …, st 4` is unimodular, so `t` is a period mod `m` iff
`m ∣ M^t - 1` in `Matrix (Fin 5) (Fin 5) ℤ`.  If `M^t = 1 + p^e A` with
`p ∤ A` and (`p` odd or `e ≥ 2`), the binomial theorem gives
`M^(t p) = 1 + p^(e+1) (A + p B)`, so the exact power of `p` dividing
`M^(t p^j) - 1` is `p^(e+j)`; since periods mod `m` are the multiples of the
least one, the least period mod `p^(e+j)` is `t p^j`.  For `p = 2` the start
is `e = 2`, `t = 12` (finite checks `a(4) = 12`, `M^12 ≢ 1 mod 8`); for `p = 5`
the finite checks are `a(5) = 781` and `M^781 ≢ 1 mod 25`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A106303FibonacciStepLeast

open Matrix

/-! ## Definitions -/

/-- The Fibonacci 5-step (pentanacci) sequence A001591: `0, 0, 0, 0, 1`, then
each term is the sum of the previous five. -/
def pent : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | n + 5 => pent n + pent (n + 1) + pent (n + 2) + pent (n + 3) + pent (n + 4)

/-- `t` is a period of the pentanacci sequence modulo `m`: `t > 0` and
`s (n + t) ≡ s n (mod m)` for every `n`. -/
def IsPeriodMod (m t : ℕ) : Prop :=
  0 < t ∧ ∀ n, pent (n + t) ≡ pent n [MOD m]

/-- A106303: the least period of the pentanacci sequence modulo `m`
(`sInf` of the set of periods; the junk value `0` occurs only if there is no
period, which never happens for the moduli used below). -/
noncomputable def leastPeriod (m : ℕ) : ℕ :=
  sInf {t | IsPeriodMod m t}

/-! ## Examples for `pent` -/

/-- The first seventeen terms of A001591. -/
example : (List.range 17).map pent =
    [0, 0, 0, 0, 1, 1, 2, 4, 8, 16, 31, 61, 120, 236, 464, 912, 1793] := by
  decide

/-! ## A computable state iteration modulo `m` -/

/-- One step of the pentanacci recurrence on a state of five residues mod `m`. -/
def stepMod (m : ℕ) (s : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2,
    (s.1 + s.2.1 + s.2.2.1 + s.2.2.2.1 + s.2.2.2.2) % m)

/-- The state `(s n, …, s (n+4))` reduced mod `m`, computed by iteration. -/
def stMod (m n : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (stepMod m)^[n] (0, 0, 0, 0, 1 % m)

/-- The iterated state is the reduced pentanacci state. -/
theorem stMod_eq (m n : ℕ) : stMod m n =
    (pent n % m, pent (n + 1) % m, pent (n + 2) % m, pent (n + 3) % m,
      pent (n + 4) % m) := by
  induction n with
  | zero => simp [stMod, pent]
  | succ n ih =>
    rw [stMod, Function.iterate_succ_apply', ← stMod, ih]
    simp only [stepMod, Prod.mk.injEq, true_and]
    rw [show n + 1 + 4 = n + 5 from rfl, pent]
    exact ((((Nat.mod_modEq _ m).add (Nat.mod_modEq _ m)).add (Nat.mod_modEq _ m)).add
      (Nat.mod_modEq _ m)).add (Nat.mod_modEq _ m)

/-- Congruence of the first five shifted terms propagates to all terms. -/
theorem modEq_shift_of_initial (m t : ℕ)
    (h : ∀ i < 5, pent (i + t) ≡ pent i [MOD m]) (n : ℕ) :
    pent (n + t) ≡ pent n [MOD m] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 5 with hn | hn
    · exact h n hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have e : k + 5 + t = (k + t) + 5 := by ring
      rw [e, pent, pent]
      have h0 := ih k (by omega)
      have h1 := ih (k + 1) (by omega)
      have h2 := ih (k + 2) (by omega)
      have h3 := ih (k + 3) (by omega)
      have h4 := ih (k + 4) (by omega)
      rw [show k + 1 + t = k + t + 1 by ring] at h1
      rw [show k + 2 + t = k + t + 2 by ring] at h2
      rw [show k + 3 + t = k + t + 3 by ring] at h3
      rw [show k + 4 + t = k + t + 4 by ring] at h4
      exact (((h0.add h1).add h2).add h3).add h4

/-- Decidable form of the period predicate: compare the iterated states. -/
theorem isPeriodMod_iff_stMod (m t : ℕ) :
    IsPeriodMod m t ↔ 0 < t ∧ stMod m t = stMod m 0 := by
  rw [stMod_eq, stMod_eq]
  simp only [IsPeriodMod, Prod.mk.injEq, zero_add]
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Nat.ModEq, add_comm] using h 0
    · simpa [Nat.ModEq, add_comm, add_left_comm] using h 1
    · simpa [Nat.ModEq, add_comm, add_left_comm] using h 2
    · simpa [Nat.ModEq, add_comm, add_left_comm] using h 3
    · simpa [Nat.ModEq, add_comm, add_left_comm] using h 4
  · rintro ⟨ht, h0, h1, h2, h3, h4⟩
    refine ⟨ht, modEq_shift_of_initial m t ?_⟩
    intro i hi
    interval_cases i
    · simpa [Nat.ModEq] using h0
    · simpa [Nat.ModEq, add_comm] using h1
    · simpa [Nat.ModEq, add_comm] using h2
    · simpa [Nat.ModEq, add_comm] using h3
    · simpa [Nat.ModEq, add_comm] using h4

/-! ## Elementary facts about periods -/

/-- A congruence period mod `m` is a congruence period mod every divisor of `m`. -/
theorem IsPeriodMod.of_dvd {m d t : ℕ} (h : IsPeriodMod m t) (hd : d ∣ m) :
    IsPeriodMod d t :=
  ⟨h.1, fun n => (h.2 n).of_dvd hd⟩

/-- Shift invariance by `t` implies shift invariance by every multiple of `t`. -/
theorem modEq_shift_mul {m t : ℕ} (h : ∀ n, pent (n + t) ≡ pent n [MOD m]) (q n : ℕ) :
    pent (n + t * q) ≡ pent n [MOD m] := by
  induction q with
  | zero => simp [Nat.ModEq.refl]
  | succ q ih =>
    rw [show n + t * (q + 1) = (n + t * q) + t by ring]
    exact (h _).trans ih

/-- Shift invariance by `u ≤ v` and by `v` implies shift invariance by `v - u`. -/
theorem modEq_shift_sub {m u v : ℕ} (hu : ∀ n, pent (n + u) ≡ pent n [MOD m])
    (hv : ∀ n, pent (n + v) ≡ pent n [MOD m]) (huv : u ≤ v) (n : ℕ) :
    pent (n + (v - u)) ≡ pent n [MOD m] := by
  have e : n + (v - u) + u = n + v := by omega
  have h1 := hu (n + (v - u))
  rw [e] at h1
  exact h1.symm.trans (hv n)

/-- The least period divides every period. -/
theorem dvd_of_isLeast {m t₀ v : ℕ} (h : IsLeast {t | IsPeriodMod m t} t₀)
    (hv : IsPeriodMod m v) : t₀ ∣ v := by
  have ht₀ : IsPeriodMod m t₀ := h.1
  by_contra hndvd
  have hr : 0 < v % t₀ := Nat.pos_of_ne_zero (fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0))
  have hlt : v % t₀ < t₀ := Nat.mod_lt _ ht₀.1
  have hle : t₀ * (v / t₀) ≤ v := Nat.mul_div_le v t₀
  have hsub : v - t₀ * (v / t₀) = v % t₀ := by
    have := Nat.div_add_mod v t₀
    omega
  have hper : IsPeriodMod m (v % t₀) := by
    refine ⟨hr, fun n => ?_⟩
    rw [← hsub]
    exact modEq_shift_sub (modEq_shift_mul ht₀.2 (v / t₀)) hv.2 hle n
  exact absurd (h.2 hper) (not_le.mpr hlt)

/-- A period `t` mod `m` all of whose proper divisors fail to be periods is the
least period mod `m`. -/
theorem isLeast_of_dvd_check {m t : ℕ} (ht : IsPeriodMod m t)
    (h : ∀ d, d ∣ t → d < t → ¬ IsPeriodMod m d) :
    IsLeast {s | IsPeriodMod m s} t := by
  have hne : ({s | IsPeriodMod m s} : Set ℕ).Nonempty := ⟨t, ht⟩
  have hw : IsLeast {s | IsPeriodMod m s} (sInf {s | IsPeriodMod m s}) :=
    ⟨Nat.sInf_mem hne, fun v hv => Nat.sInf_le hv⟩
  have hdvd := dvd_of_isLeast hw ht
  have hle : sInf {s | IsPeriodMod m s} ≤ t := hw.2 ht
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hw.1 (h _ hdvd hlt)
  · rw [← heq]
    exact hw

/-! ## Matrix formulation -/

/-- Companion matrix of `x^5 - x^4 - x^3 - x^2 - x - 1`, acting on states. -/
def M : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 1, 1, 1, 1]

/-- The integer state vector `(s n, …, s (n+4))`. -/
def st (n : ℕ) : Fin 5 → ℤ := fun i => (pent (n + i) : ℤ)

/-- `M` advances the state by one step. -/
theorem M_mulVec_st (n : ℕ) : M *ᵥ st n = st (n + 1) := by
  ext i
  fin_cases i <;>
    simp only [mulVec, dotProduct, M, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      of_apply, cons_val', cons_val_fin_one, cons_val_zero, cons_val_one, cons_val, st,
      Fin.sum_univ_five, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, zero_mul, one_mul,
      zero_add, Nat.one_mod, Nat.reduceMod, Nat.mod_succ]
  rw [show n + 1 + 4 = n + 5 from rfl, pent]
  push_cast
  ring

/-- `M ^ t` advances the state by `t` steps. -/
theorem M_pow_mulVec_st (t n : ℕ) : (M ^ t) *ᵥ st n = st (n + t) := by
  induction t generalizing n with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← mulVec_mulVec, M_mulVec_st, ih]
    congr 1
    omega

/-- The Hankel (Krylov) matrix with columns `st 0, …, st 4`. -/
def K : Matrix (Fin 5) (Fin 5) ℤ := Matrix.of fun i j => st j i

/-- The integer inverse of `K` (`det K = 1`). -/
def Kinv : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-1, -1, -1, -1, 1; -1, -1, -1, 1, 0; -1, -1, 1, 0, 0; -1, 1, 0, 0, 0; 1, 0, 0, 0, 0]

/-- Explicit entries of `K`. -/
theorem K_eq : K = !![0, 0, 0, 0, 1; 0, 0, 0, 1, 1; 0, 0, 1, 1, 2; 0, 1, 1, 2, 4;
    1, 1, 2, 4, 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `Kinv` is a right inverse of `K`. -/
theorem K_mul_Kinv : K * Kinv = 1 := by
  rw [K_eq, Kinv]
  decide

/-- Entries of a natural-number scalar times a matrix. -/
theorem natCast_mul_apply (n : ℕ) (A : Matrix (Fin 5) (Fin 5) ℤ) (i j : Fin 5) :
    ((n : Matrix (Fin 5) (Fin 5) ℤ) * A) i j = n * A i j := by
  rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul]

/-- Divisibility of an integer matrix by a natural scalar is entrywise
divisibility. -/
theorem natCast_dvd_iff (n : ℕ) (A : Matrix (Fin 5) (Fin 5) ℤ) :
    (n : Matrix (Fin 5) (Fin 5) ℤ) ∣ A ↔ ∀ i j, (n : ℤ) ∣ A i j := by
  constructor
  · rintro ⟨C, rfl⟩ i j
    rw [natCast_mul_apply]
    exact dvd_mul_right _ _
  · intro h
    refine ⟨Matrix.of fun i j => A i j / n, ?_⟩
    ext i j
    rw [natCast_mul_apply, Matrix.of_apply, Int.mul_ediv_cancel' (h i j)]

/-- **Bridge.** `t` is a period mod `m` iff `t > 0` and `m ∣ M ^ t - 1`. -/
theorem isPeriodMod_iff_dvd (m t : ℕ) :
    IsPeriodMod m t ↔ 0 < t ∧ (m : Matrix (Fin 5) (Fin 5) ℤ) ∣ M ^ t - 1 := by
  have hcol : ∀ n, (M ^ t - 1) *ᵥ st n = st (n + t) - st n := by
    intro n
    rw [sub_mulVec, M_pow_mulVec_st, one_mulVec]
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    have hDK : (m : Matrix (Fin 5) (Fin 5) ℤ) ∣ (M ^ t - 1) * K := by
      rw [natCast_dvd_iff]
      intro i j
      have e : ((M ^ t - 1) * K) i j = ((M ^ t - 1) *ᵥ st j) i := rfl
      rw [e, hcol]
      simp only [Pi.sub_apply, st]
      rw [show j.val + t + i.val = (j.val + i.val) + t by ring]
      exact (Nat.modEq_iff_dvd.mp (h _).symm)
    have e : M ^ t - 1 = (M ^ t - 1) * K * Kinv := by
      rw [mul_assoc, K_mul_Kinv, mul_one]
    rw [e]
    exact hDK.mul_right _
  · rintro ⟨ht, h⟩
    refine ⟨ht, fun n => ?_⟩
    obtain ⟨C, hC⟩ := h
    have hv := congrFun (hcol n) 0
    rw [hC, ← mulVec_mulVec, natCast_mulVec] at hv
    simp only [Pi.smul_apply, Pi.sub_apply, st, Fin.val_zero, add_zero] at hv
    apply (Nat.modEq_iff_dvd.mpr _).symm
    rw [← hv]
    exact dvd_mul_right _ _

/-! ## The binomial lifting step -/

/-- Binomial step in a commutative ring: for `p` prime, `e ≥ 1`, and `p` odd
or `e ≥ 2`, `(1 + p^e y)^p = 1 + p^(e+1) (y + p z)` for some `z`. -/
theorem one_add_pow_prime_comm {S : Type*} [CommRing S] (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hpe : 3 ≤ p ∨ 2 ≤ e) (y : S) :
    ∃ z : S, (1 + (p : S) ^ e * y) ^ p = 1 + (p : S) ^ (e + 1) * (y + p * z) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hterm : ∀ i ∈ Finset.range (q + 1), ((q + 2 : ℕ) : S) ^ (e + 2) ∣
      (((q + 2 : ℕ) : S) ^ e * y) ^ (i + 1 + 1) * 1 ^ (q + 2 - (i + 1 + 1)) *
        ((q + 2).choose (i + 1 + 1) : S) := by
    intro i hi
    have hi' : i < q + 1 := Finset.mem_range.mp hi
    rcases (Nat.lt_succ_iff.mp hi').lt_or_eq with hlt | heq
    · obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := i + 1 + 1) (by omega) (by omega)
      have hle : e + 2 ≤ e * (i + 1 + 1) + 1 := by nlinarith
      have hrw : (((q + 2 : ℕ) : S) ^ e * y) ^ (i + 1 + 1) * 1 ^ (q + 2 - (i + 1 + 1)) *
          ((q + 2).choose (i + 1 + 1) : S) =
          ((q + 2 : ℕ) : S) ^ (e * (i + 1 + 1) + 1) * (y ^ (i + 1 + 1) * c) := by
        rw [hc, one_pow, mul_one, mul_pow, ← pow_mul, pow_succ]
        push_cast
        ring
      rw [hrw]
      exact (pow_dvd_pow _ hle).mul_right _
    · subst heq
      have hle : e + 2 ≤ e * (i + 1 + 1) := by
        rcases hpe with h3 | h2 <;> nlinarith
      have hrw : (((i + 2 : ℕ) : S) ^ e * y) ^ (i + 1 + 1) * 1 ^ (i + 2 - (i + 1 + 1)) *
          ((i + 2).choose (i + 1 + 1) : S) =
          ((i + 2 : ℕ) : S) ^ (e * (i + 1 + 1)) * y ^ (i + 1 + 1) := by
        rw [Nat.choose_self, one_pow, mul_one, mul_pow, ← pow_mul, Nat.cast_one, mul_one]
      rw [hrw]
      exact (pow_dvd_pow _ hle).mul_right _
  obtain ⟨z, hz⟩ := Finset.dvd_sum hterm
  refine ⟨z, ?_⟩
  rw [add_comm, add_pow, Finset.sum_range_succ', Finset.sum_range_succ', hz]
  simp only [zero_add, pow_one, one_pow, mul_one, pow_zero, Nat.choose_one_right,
    Nat.choose_zero_right, Nat.cast_one]
  ring

/-- The binomial step in an arbitrary ring, transported from `ℤ[X]` along
`Polynomial.aeval`. -/
theorem one_add_pow_prime {R : Type*} [Ring R] (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hpe : 3 ≤ p ∨ 2 ≤ e) (a : R) :
    ∃ b : R, (1 + (p : R) ^ e * a) ^ p = 1 + (p : R) ^ (e + 1) * (a + p * b) := by
  obtain ⟨z, hz⟩ := one_add_pow_prime_comm (S := Polynomial ℤ) p e hp he hpe Polynomial.X
  refine ⟨Polynomial.aeval a z, ?_⟩
  have h := congrArg (Polynomial.aeval a) hz
  simpa using h

/-- Iterated lifting: if `x - 1 = p^e a` with `p ∤ a`, then
`x^(p^j) - 1 = p^(e+j) b` with `p ∤ b`. -/
theorem pow_prime_pow_sub_one {R : Type*} [Ring R] (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hpe : 3 ≤ p ∨ 2 ≤ e) (x a : R) (hx : x - 1 = (p : R) ^ e * a) (ha : ¬ (p : R) ∣ a)
    (j : ℕ) : ∃ b : R, x ^ (p ^ j) - 1 = (p : R) ^ (e + j) * b ∧ ¬ (p : R) ∣ b := by
  induction j with
  | zero => exact ⟨a, by simpa using hx, ha⟩
  | succ j ih =>
    obtain ⟨b, hb, hnb⟩ := ih
    obtain ⟨c, hc⟩ := one_add_pow_prime p (e + j) hp (by omega) (by omega) b
    refine ⟨b + p * c, ?_, ?_⟩
    · rw [pow_succ, pow_mul, sub_eq_iff_eq_add'.mp hb, hc, add_sub_cancel_left, ← add_assoc]
    · intro h
      exact hnb ((dvd_add_left (dvd_mul_right _ _)).mp h)

/-- Cancellation: if `p^(f+1) ∣ p^f a` for an integer matrix `a` and `p ≠ 0`,
then `p ∣ a`. -/
theorem natCast_dvd_of_pow_succ_dvd (p f : ℕ) (hp : p ≠ 0) (a : Matrix (Fin 5) (Fin 5) ℤ)
    (h : (p : Matrix (Fin 5) (Fin 5) ℤ) ^ (f + 1) ∣ (p : Matrix (Fin 5) (Fin 5) ℤ) ^ f * a) :
    (p : Matrix (Fin 5) (Fin 5) ℤ) ∣ a := by
  obtain ⟨c, hc⟩ := h
  rw [natCast_dvd_iff]
  intro i j
  have hij := congrArg (fun A : Matrix (Fin 5) (Fin 5) ℤ => A i j) hc
  rw [← Nat.cast_pow, ← Nat.cast_pow, natCast_mul_apply, natCast_mul_apply] at hij
  refine ⟨c i j, ?_⟩
  have hpf : ((p ^ f : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero f hp
  apply mul_left_cancel₀ hpf
  rw [hij]
  push_cast
  ring

/-- **Lifting theorem.** Let `p` be prime, `e ≥ 1` with `p` odd or `e ≥ 2`.
If `t₀` is the least period mod `p^e` and is not a period mod `p^(e+1)`, then
`t₀ * p^j` is the least period mod `p^(e+j)` for every `j`. -/
theorem isLeast_lift (p e t₀ : ℕ) (hp : p.Prime) (he : 1 ≤ e) (hpe : 3 ≤ p ∨ 2 ≤ e)
    (ht₀ : IsLeast {t | IsPeriodMod (p ^ e) t} t₀)
    (hnot : ¬ IsPeriodMod (p ^ (e + 1)) t₀) (j : ℕ) :
    IsLeast {t | IsPeriodMod (p ^ (e + j)) t} (t₀ * p ^ j) := by
  have hpos : 0 < t₀ := ht₀.1.1
  obtain ⟨a, ha⟩ : ∃ a, M ^ t₀ - 1 = (p : Matrix (Fin 5) (Fin 5) ℤ) ^ e * a := by
    obtain ⟨-, a, ha⟩ := (isPeriodMod_iff_dvd _ _).mp ht₀.1
    exact ⟨a, by rw [ha, Nat.cast_pow]⟩
  have hna : ¬ (p : Matrix (Fin 5) (Fin 5) ℤ) ∣ a := by
    rintro ⟨c, rfl⟩
    apply hnot
    refine (isPeriodMod_iff_dvd _ _).mpr ⟨hpos, c, ?_⟩
    rw [ha, Nat.cast_pow, pow_succ, mul_assoc]
  have hlift := pow_prime_pow_sub_one p e hp he hpe (M ^ t₀) a ha hna
  have hper : ∀ j, IsPeriodMod (p ^ (e + j)) (t₀ * p ^ j) := by
    intro j
    obtain ⟨b, hb, -⟩ := hlift j
    refine (isPeriodMod_iff_dvd _ _).mpr ⟨Nat.mul_pos hpos (pow_pos hp.pos _), b, ?_⟩
    rw [pow_mul, hb, Nat.cast_pow]
  have hnper : ∀ j, ¬ IsPeriodMod (p ^ (e + j + 1)) (t₀ * p ^ j) := by
    intro j h
    obtain ⟨b, hb, hnb⟩ := hlift j
    obtain ⟨-, hd⟩ := (isPeriodMod_iff_dvd _ _).mp h
    rw [pow_mul, hb, Nat.cast_pow] at hd
    exact hnb (natCast_dvd_of_pow_succ_dvd p (e + j) hp.ne_zero b hd)
  induction j with
  | zero => simpa using ht₀
  | succ j ih =>
    have hmem : t₀ * p ^ (j + 1) ∈ {t | IsPeriodMod (p ^ (e + (j + 1))) t} := hper (j + 1)
    have hw : IsLeast {t | IsPeriodMod (p ^ (e + (j + 1))) t}
        (sInf {t | IsPeriodMod (p ^ (e + (j + 1))) t}) :=
      ⟨Nat.sInf_mem ⟨_, hmem⟩, fun v hv => Nat.sInf_le hv⟩
    have hw_dvd := dvd_of_isLeast hw hmem
    have hdvd_w : t₀ * p ^ j ∣ sInf {t | IsPeriodMod (p ^ (e + (j + 1))) t} :=
      dvd_of_isLeast ih (hw.1.of_dvd (pow_dvd_pow p (by omega)))
    obtain ⟨c, hc⟩ := hdvd_w
    have hpos' : 0 < t₀ * p ^ j := Nat.mul_pos hpos (pow_pos hp.pos _)
    have hcp : c ∣ p := by
      rw [hc, pow_succ, ← mul_assoc] at hw_dvd
      exact Nat.dvd_of_mul_dvd_mul_left hpos' hw_dvd
    rcases hp.eq_one_or_self_of_dvd c hcp with rfl | rfl
    · rw [mul_one] at hc
      have hmem' := hw.1
      rw [hc] at hmem'
      exact absurd hmem' (by simpa [add_assoc] using hnper j)
    · rw [pow_succ, ← mul_assoc, ← hc]
      exact hw

/-! ## Finite checks -/

/-- `t = 1` is a period mod `1`, the least one. -/
theorem isLeast_one : IsLeast {t | IsPeriodMod 1 t} 1 :=
  ⟨⟨Nat.one_pos, fun _ => Nat.modEq_one⟩, fun _ hv => hv.1⟩

/-- The least period mod `2` is `6`. -/
theorem isLeast_two : IsLeast {t | IsPeriodMod 2 t} 6 := by
  have key : ∀ d < 6, d = 0 ∨ stMod 2 d ≠ stMod 2 0 := by decide
  refine isLeast_of_dvd_check ((isPeriodMod_iff_stMod _ _).mpr ⟨by norm_num, by decide⟩) ?_
  intro d _ hd hper
  rw [isPeriodMod_iff_stMod] at hper
  rcases key d hd with h0 | hne
  · exact absurd h0 hper.1.ne'
  · exact hne hper.2

/-- The least period mod `3` is `104`. -/
theorem isLeast_three : IsLeast {t | IsPeriodMod 3 t} 104 := by
  have key : ∀ d < 104, d = 0 ∨ ¬ d ∣ 104 ∨ stMod 3 d ≠ stMod 3 0 := by decide
  refine isLeast_of_dvd_check ((isPeriodMod_iff_stMod _ _).mpr ⟨by norm_num, by decide⟩) ?_
  intro d hdvd hd hper
  rw [isPeriodMod_iff_stMod] at hper
  rcases key d hd with h0 | hndvd | hne
  · exact absurd h0 hper.1.ne'
  · exact hndvd hdvd
  · exact hne hper.2

/-- The least period mod `4` is `12`. -/
theorem isLeast_four : IsLeast {t | IsPeriodMod 4 t} 12 := by
  have key : ∀ d < 12, d = 0 ∨ stMod 4 d ≠ stMod 4 0 := by decide
  refine isLeast_of_dvd_check ((isPeriodMod_iff_stMod _ _).mpr ⟨by norm_num, by decide⟩) ?_
  intro d _ hd hper
  rw [isPeriodMod_iff_stMod] at hper
  rcases key d hd with h0 | hne
  · exact absurd h0 hper.1.ne'
  · exact hne hper.2

/-- The divisors of `781 = 11 * 71`. -/
theorem eq_of_dvd_781 (d : ℕ) (h : d ∣ 781) : d = 1 ∨ d = 11 ∨ d = 71 ∨ d = 781 := by
  rw [show (781 : ℕ) = 11 * 71 by norm_num] at h
  obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.mp h
  rcases (by norm_num : Nat.Prime 11).eq_one_or_self_of_dvd d₁ h₁ with rfl | rfl <;>
    rcases (by norm_num : Nat.Prime 71).eq_one_or_self_of_dvd d₂ h₂ with rfl | rfl <;>
    norm_num

set_option maxRecDepth 100000 in
/-- `781` is a period mod `5` (finite check of 781 recurrence steps). -/
theorem isPeriodMod_five : IsPeriodMod 5 781 :=
  (isPeriodMod_iff_stMod _ _).mpr ⟨by norm_num, by decide⟩

set_option maxRecDepth 20000 in
/-- The least period mod `5` is `781 = 11 * 71`. -/
theorem isLeast_five : IsLeast {t | IsPeriodMod 5 t} 781 := by
  have h1 : stMod 5 1 ≠ stMod 5 0 := by decide
  have h11 : stMod 5 11 ≠ stMod 5 0 := by decide
  have h71 : stMod 5 71 ≠ stMod 5 0 := by decide
  refine isLeast_of_dvd_check isPeriodMod_five ?_
  intro d hdvd hd hper
  rw [isPeriodMod_iff_stMod] at hper
  rcases eq_of_dvd_781 d hdvd with rfl | rfl | rfl | rfl
  · exact h1 hper.2
  · exact h11 hper.2
  · exact h71 hper.2
  · exact absurd hd (lt_irrefl _)

/-- `12` is not a period mod `8` (so `a(8) ≠ a(4)`). -/
theorem not_isPeriodMod_eight_twelve : ¬ IsPeriodMod 8 12 := by
  rw [isPeriodMod_iff_stMod]
  decide

set_option maxRecDepth 100000 in
/-- `781` is not a period mod `25` (so `a(25) ≠ a(5)`). -/
theorem not_isPeriodMod_twentyfive : ¬ IsPeriodMod 25 781 := by
  rw [isPeriodMod_iff_stMod]
  decide

/-- The least period mod `m` is the `IsLeast` element of the set of periods. -/
theorem leastPeriod_eq {m t : ℕ} (h : IsLeast {s | IsPeriodMod m s} t) : leastPeriod m = t :=
  h.csInf_eq

/-! ## Examples for `leastPeriod` against the listed terms `1, 6, 104, 12, 781` -/

example : leastPeriod 1 = 1 := leastPeriod_eq isLeast_one
example : leastPeriod 2 = 6 := leastPeriod_eq isLeast_two
example : leastPeriod 3 = 104 := leastPeriod_eq isLeast_three
example : leastPeriod 4 = 12 := leastPeriod_eq isLeast_four
example : leastPeriod 5 = 781 := leastPeriod_eq isLeast_five

/-! ## The conjecture -/

/-- **Wu's conjecture (i) (A106303, Chai Wah Wu, 2022).**
The least period of the pentanacci sequence A001591 modulo `5^k` is `781 * 5^(k-1)` for every `k ≥ 1`
(the guard `1 ≤ k` keeps `k - 1` off natural-number truncation). -/
theorem leastPeriod_five_pow (k : ℕ) (hk : 1 ≤ k) :
    leastPeriod (5 ^ k) = 781 * 5 ^ (k - 1) := by
  have h := isLeast_lift 5 1 781 (by norm_num) le_rfl (Or.inl (by norm_num))
    (by simpa using isLeast_five) (by simpa using not_isPeriodMod_twentyfive) (k - 1)
  rw [show 1 + (k - 1) = k by omega] at h
  exact leastPeriod_eq h

/-- **Wu's conjecture (ii) (A106303, Chai Wah Wu, 2022).**
For every prime `p` with `a(p^2) ≠ a(p)`, the least period of the
pentanacci sequence modulo `p^k` is `p^(k-1) * a(p)` for every `k ≥ 1`. -/
theorem leastPeriod_prime_pow (p : ℕ) (hp : p.Prime)
    (hne : leastPeriod (p ^ 2) ≠ leastPeriod p) (k : ℕ) (hk : 1 ≤ k) :
    leastPeriod (p ^ k) = p ^ (k - 1) * leastPeriod p := by
  have hp2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  by_cases hS : ({t | IsPeriodMod p t} : Set ℕ).Nonempty
  · have ht : IsLeast {t | IsPeriodMod p t} (leastPeriod p) :=
      ⟨Nat.sInf_mem hS, fun v hv => Nat.sInf_le hv⟩
    rcases Nat.lt_or_ge p 3 with hp3 | hp3
    · -- `p = 2`: start the lifting at `e = 2`, `t₀ = 12`.
      have hp2' : p = 2 := by
        have := hp.two_le
        omega
      subst hp2'
      have hl2 : leastPeriod 2 = 6 := leastPeriod_eq isLeast_two
      rw [hl2]
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain rfl : k = 1 := by omega
        simpa using hl2
      · have h := isLeast_lift 2 2 12 (by norm_num) (by norm_num) (Or.inr le_rfl)
          (by simpa using isLeast_four) (by simpa using not_isPeriodMod_eight_twelve) (k - 2)
        rw [show 2 + (k - 2) = k by omega] at h
        rw [leastPeriod_eq h]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
        rw [show j + 2 - 2 = j by omega, show j + 2 - 1 = j + 1 by omega, pow_succ]
        ring
    · -- odd `p`: start the lifting at `e = 1`, `t₀ = a(p)`.
      have hnot : ¬ IsPeriodMod (p ^ (1 + 1)) (leastPeriod p) := by
        intro h
        apply hne
        exact leastPeriod_eq ⟨h, fun v hv => ht.2 (hv.of_dvd hp2)⟩
      have h := isLeast_lift p 1 (leastPeriod p) hp le_rfl (Or.inl hp3)
        (by simpa using ht) hnot (k - 1)
      rw [show 1 + (k - 1) = k by omega] at h
      rw [leastPeriod_eq h, mul_comm]
  · exfalso
    apply hne
    have h1 : leastPeriod p = 0 :=
      Nat.sInf_eq_zero.mpr (Or.inr (Set.not_nonempty_iff_eq_empty.mp hS))
    have h2 : leastPeriod (p ^ 2) = 0 := by
      refine Nat.sInf_eq_zero.mpr (Or.inr ?_)
      refine Set.eq_empty_iff_forall_notMem.mpr fun t ht => hS ⟨t, ?_⟩
      exact IsPeriodMod.of_dvd ht hp2
    rw [h1, h2]

/-- Non-vacuity of (ii): the hypothesis `a(p^2) ≠ a(p)` holds at `p = 2` and
at `p = 5`. -/
example : leastPeriod (2 ^ 2) ≠ leastPeriod 2 ∧ leastPeriod (5 ^ 2) ≠ leastPeriod 5 := by
  constructor
  · rw [leastPeriod_eq isLeast_two, show (2 : ℕ) ^ 2 = 4 by norm_num, leastPeriod_eq isLeast_four]
    decide
  · rw [leastPeriod_five_pow 2 (by norm_num), leastPeriod_eq isLeast_five]
    norm_num

end Candidates.A106303FibonacciStepLeast
