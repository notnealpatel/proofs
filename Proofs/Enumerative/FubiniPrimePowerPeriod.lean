import Enumerative.FubiniPrimePeriod
import Mathlib.NumberTheory.Multiplicity

/-!
# Exact eventual Fubini periods modulo odd prime powers

For every odd prime `p` and `1 ≤ m`, this module proves that a natural
shift `T` is an eventual period of the actual sequence `A051293.fubini`
modulo `p ^ m` exactly when `p ^ (m - 1) * (p - 1)` divides `T`.
Zero shifts are included; periodicity from index zero is not asserted.

This is the odd-prime-power case of B. Poonen, *Periodicity of a
combinatorial sequence*, Fibonacci Quarterly 26 (1988), 70–76,
Theorem 3 (p. 73), with the upper bound furnished by Theorem 2 (p. 72).
Reference: https://www.fq.math.ca/Scanned/26-1/poonen.pdf.
No novelty is claimed.

The lower bound uses the polynomial projector `1 - (X - 1) ^ (p - 1)`
on Poonen's moment formula. An elementary odd-power lift evaluates the
surviving residue class. Its weighted geometric sum reduces to the
nonzero inverse of two modulo `p`. Cancellation is performed in natural
number divisibility, not in a ring with zero divisors. Finally, induction
and gcd closure exclude every smaller eventual period.
-/

set_option autoImplicit false
open Finset
namespace A000670
open A051293

private lemma lift_coefficient (p : ℕ) (hp : Odd p) (k : ℤ) (s : ℕ) :
    ∃ b : ℤ, (1 + (p : ℤ) * k) ^ (p ^ s) =
      1 + (p : ℤ) ^ (s + 1) * (k + p * b) := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
    obtain ⟨b, hb⟩ := ih
    let c : ℤ := (p : ℤ) ^ s * (k + p * b)
    have hc : (1 + (p : ℤ) * k) ^ (p ^ s) = 1 + p * c := by
      rw [hb]
      dsimp [c]
      ring
    obtain ⟨d, hd⟩ := odd_sq_dvd_geom_sum₂_sub (R := ℤ) 1 c hp
    simp only [one_pow, mul_one] at hd
    have hgeom := geom_sum₂_mul (1 + (p : ℤ) * c) 1 p
    simp only [one_pow, mul_one] at hgeom
    refine ⟨b + d * (k + p * b), ?_⟩
    rw [pow_succ, pow_mul, hc]
    dsimp [c] at hgeom hd
    dsimp [c]
    simp only [pow_succ] at *
    linear_combination -hgeom + ((p : ℤ) ^ s * p * (k + p * b)) * hd

private lemma one_add_pow_sq_zero {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 2 = 0) (n : ℕ) : (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one]
    linear_combination (n : R) * hx

private lemma sum_blocks {R : Type*} [AddCommMonoid R] (p k : ℕ) (f : ℕ → R) :
    ∑ j ∈ range (p * k), f j = ∑ a ∈ range k, ∑ r ∈ range p, f (p * a + r) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

private lemma weighted_geometric {R : Type*} [CommRing R] (x : R) (m : ℕ) :
    (1 - x) * (∑ k ∈ range m, (k : R) * x ^ k) =
      (∑ k ∈ range m, x ^ k) - 1 + (1 - (m : R)) * x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, pow_succ, Nat.cast_add, Nat.cast_one]
    linear_combination ih

private lemma period_polynomial_moment {K T N : ℕ}
    (h : ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD K])
    {n : ℕ} (hn : N ≤ n) (Q : Polynomial (ZMod K)) :
    ∑ j ∈ range K, (2 : ZMod K) ^ (K - 1 - j) * (j : ZMod K) ^ n *
      ((j : ZMod K) ^ T - 1) * Q.eval (j : ZMod K) = 0 := by
  have hmom (r : ℕ) :
      ∑ j ∈ range K, (2 : ZMod K) ^ (K - 1 - j) * (j : ZMod K) ^ n *
        ((j : ZMod K) ^ T - 1) * (j : ZMod K) ^ r = 0 := by
    have he : (fubini (n + r + T) : ZMod K) = (fubini (n + r) : ZMod K) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (h _ (by omega))
    have he' := congrArg (fun x : ZMod K => ((2 : ZMod K) ^ K - 1) * x) he
    rw [poonen_congr, poonen_congr, ← sub_eq_zero, ← sum_sub_distrib] at he'
    calc
      _ = ∑ j ∈ range K, ((2 : ZMod K) ^ (K - 1 - j) * (j : ZMod K) ^ (n + r + T) -
          (2 : ZMod K) ^ (K - 1 - j) * (j : ZMod K) ^ (n + r)) := by
        apply sum_congr rfl
        intro j _
        simp only [pow_add]
        ring
      _ = 0 := he'
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
    simp only [Polynomial.eval_add, mul_add, sum_add_distrib, hQ, hR, add_zero]
  | monomial r a =>
    simp only [Polynomial.eval_monomial]
    calc
      _ = a * ∑ j ∈ range K, (2 : ZMod K) ^ (K - 1 - j) * (j : ZMod K) ^ n *
          ((j : ZMod K) ^ T - 1) * (j : ZMod K) ^ r := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hmom, mul_zero]

private lemma eventual_eq_gcd {α : Type*} (f : ℕ → α) {a b : ℕ}
    (ha : ∃ N, ∀ n, N ≤ n → f (n + a) = f n)
    (hb : ∃ N, ∀ n, N ≤ n → f (n + b) = f n) :
    ∃ N, ∀ n, N ≤ n → f (n + a.gcd b) = f n := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  let N := max A B
  let shift : (ℕ → α) → (ℕ → α) := fun g n => g (n + 1)
  have hiter (k : ℕ) (g : ℕ → α) (n : ℕ) : shift^[k] g n = g (n + k) := by
    induction k generalizing n with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change shift^[k] g (n + 1) = g (n + (k + 1))
      rw [ih]
      congr 1
      omega
  let g : ℕ → α := fun n => f (N + n)
  have hpa : Function.IsPeriodicPt shift a g := by
    change shift^[a] g = g
    funext n
    rw [hiter]
    simpa only [g, Nat.add_assoc] using hA (N + n) (by dsimp [N]; omega)
  have hpb : Function.IsPeriodicPt shift b g := by
    change shift^[b] g = g
    funext n
    rw [hiter]
    simpa only [g, Nat.add_assoc] using hB (N + n) (by dsimp [N]; omega)
  have hg := hpa.gcd hpb
  refine ⟨N, fun n hn => ?_⟩
  have he := congrFun hg (n - N)
  rw [hiter] at he
  change f (N + (n - N + a.gcd b)) = f (N + (n - N)) at he
  have hn' : N + (n - N) = n := Nat.add_sub_of_le hn
  simpa only [← Nat.add_assoc, hn'] using he

private lemma kernel_factor {d K : ℕ} [NeZero K] (hd : d ∣ K) (a : ZMod K)
    (ha : ZMod.castHom hd (ZMod d) a = 0) : ∃ b : ZMod K, a = (d : ZMod K) * b := by
  have hv : (a.val : ZMod d) = 0 := by
    have h := congrArg (ZMod.castHom hd (ZMod d)) (ZMod.natCast_zmod_val a)
    simpa only [map_natCast, ha] using h
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff a.val d).mp hv
  exact ⟨k, by rw [← Nat.cast_mul, ← hk, ZMod.natCast_zmod_val]⟩

private lemma kernel_product (p s : ℕ) (hp : 0 < p) (a b : ZMod (p ^ (s + 2)))
    (ha : ZMod.castHom (pow_dvd_pow p (by omega : s + 1 ≤ s + 2))
      (ZMod (p ^ (s + 1))) a = 0)
    (hb : ZMod.castHom (dvd_pow_self p (by omega : s + 2 ≠ 0)) (ZMod p) b = 0) :
    a * b = 0 := by
  letI : NeZero (p ^ (s + 2)) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  obtain ⟨u, rfl⟩ := kernel_factor _ a ha
  obtain ⟨v, rfl⟩ := kernel_factor _ b hb
  have hz : (p : ZMod (p ^ (s + 2))) ^ (s + 1) * p = 0 := by
    rw [← pow_succ, ← Nat.cast_pow, ZMod.natCast_self]
  push_cast
  calc
    _ = ((p : ZMod (p ^ (s + 2))) ^ (s + 1) * p) * (u * v) := by ring
    _ = 0 := by rw [hz, zero_mul]

private lemma high_mul (p s : ℕ) (hp : 0 < p) (a b : ZMod (p ^ (s + 2)))
    (h : ZMod.castHom (dvd_pow_self p (by omega : s + 2 ≠ 0)) (ZMod p) a =
      ZMod.castHom (dvd_pow_self p (by omega : s + 2 ≠ 0)) (ZMod p) b) :
    (p : ZMod (p ^ (s + 2))) ^ (s + 1) * a = p ^ (s + 1) * b := by
  have hz := kernel_product p s hp ((p : ZMod (p ^ (s + 2))) ^ (s + 1)) (a - b)
    (by rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]) (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp (by simpa only [mul_sub] using hz)

private lemma lift_zmod {p : ℕ} (hp : Odd p) (s k : ℕ) :
    ((1 + p * k : ℕ) : ZMod (p ^ (s + 2))) ^ (p ^ s) =
      1 + (p : ZMod (p ^ (s + 2))) ^ (s + 1) * k := by
  obtain ⟨b, hb⟩ := lift_coefficient p hp (k : ℤ) s
  have h := congrArg (fun z : ℤ => (z : ZMod (p ^ (s + 2)))) hb
  push_cast at h
  have hz : (p : ZMod (p ^ (s + 2))) ^ (s + 1) * p = 0 := by
    rw [← pow_succ, ← Nat.cast_pow, ZMod.natCast_self]
  push_cast
  rw [h]
  linear_combination (b : ZMod (p ^ (s + 2))) * hz

private lemma projector_term {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (s : ℕ) (hn : s + 2 ≤ n) (k r : ℕ) (hr : r < p) :
    ((p * k + r : ℕ) : ZMod (p ^ (s + 2))) ^ n *
      (((p * k + r : ℕ) : ZMod (p ^ (s + 2))) ^ (p ^ s * (p - 1)) - 1) *
      (1 - (((p * k + r : ℕ) : ZMod (p ^ (s + 2))) - 1) ^ (p - 1)) =
      if r = 1 then -(p : ZMod (p ^ (s + 2))) ^ (s + 1) * k else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let π := ZMod.castHom (dvd_pow_self p (by omega : s + 2 ≠ 0)) (ZMod p)
  let ρ := ZMod.castHom (pow_dvd_pow p (by omega : s + 1 ≤ s + 2)) (ZMod (p ^ (s + 1)))
  have hred : π ((p * k + r : ℕ) : ZMod (p ^ (s + 2))) = (r : ZMod p) := by
    simp [π, Nat.cast_add, Nat.cast_mul]
  have hpz : (p : ZMod (p ^ (s + 2))) ^ (s + 2) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  by_cases hr0 : r = 0
  · subst r
    have hz : ((p * k + 0 : ℕ) : ZMod (p ^ (s + 2))) ^ n = 0 := by
      simp only [Nat.add_zero, Nat.cast_mul, mul_pow]
      rw [ZMod.natCast_pow_eq_zero_of_le p hn, zero_mul]
    rw [hz]
    simp
  by_cases hr1 : r = 1
  · subst r
    rw [if_pos rfl]
    let a : ZMod (p ^ (s + 2)) := ((p * k + 1 : ℕ) : ZMod (p ^ (s + 2)))
    have hpow : a ^ (p ^ s * (p - 1)) - 1 = -(p : ZMod (p ^ (s + 2))) ^ (s + 1) * k := by
      let x : ZMod (p ^ (s + 2)) := (p : ZMod (p ^ (s + 2))) ^ (s + 1) * k
      have hx : x ^ 2 = 0 := by
        dsimp [x]
        rw [mul_pow, ← pow_mul]
        exact mul_eq_zero_of_left (ZMod.natCast_pow_eq_zero_of_le p (by omega)) _
      have ha : a ^ (p ^ s) = 1 + x := by
        dsimp [a, x]
        rw [Nat.add_comm (p * k) 1]
        exact lift_zmod (hp.odd_of_ne_two hodd) s k
      rw [pow_mul, ha, one_add_pow_sq_zero x hx, add_sub_cancel_left]
      dsimp [x]
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      linear_combination (k : ZMod (p ^ (s + 2))) * hpz
    change a ^ n * (a ^ (p ^ s * (p - 1)) - 1) * (1 - (a - 1) ^ (p - 1)) = _
    rw [hpow]
    have hred' : π a = 1 := by simpa only [Nat.cast_one] using hred
    have he := high_mul p s hp.pos (a ^ n * (1 - (a - 1) ^ (p - 1))) 1 (by
      change π (a ^ n * (1 - (a - 1) ^ (p - 1))) = π 1
      rw [map_mul, map_pow, map_sub, map_one, map_pow, map_sub, map_one, hred']
      simp [Nat.sub_ne_zero_of_lt hp.one_lt])
    calc
      _ = -(k : ZMod (p ^ (s + 2))) *
        ((p : ZMod (p ^ (s + 2))) ^ (s + 1) * (a ^ n * (1 - (a - 1) ^ (p - 1)))) := by ring
      _ = _ := by rw [he]; ring
  · rw [if_neg hr1]
    have hrone : (r : ZMod p) - 1 ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val (sub_eq_zero.mp hz)
      rw [ZMod.val_natCast_of_lt hr] at hv
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt] at hv
      exact hr1 hv
    have hj : ¬p ∣ p * k + r := by
      intro hd
      have hdr : p ∣ r := (Nat.dvd_add_right (dvd_mul_right p k)).mp hd
      exact hr0 (Nat.eq_zero_of_dvd_of_lt hdr hr)
    have hcop : (p * k + r).Coprime (p ^ (s + 1)) :=
      ((hp.coprime_iff_not_dvd.mpr hj).symm).pow_right _
    have he := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime_pow_succ hp s] at he
    have ha : ρ ((((p * k + r : ℕ) : ZMod (p ^ (s + 2)))) ^ (p ^ s * (p - 1)) - 1) = 0 := by
      simp only [ρ, map_sub, map_pow, map_natCast, map_one]
      exact sub_eq_zero.mpr (by exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr he)
    have hb : π (1 - ((((p * k + r : ℕ) : ZMod (p ^ (s + 2)))) - 1) ^ (p - 1)) = 0 := by
      rw [map_sub, map_one, map_pow, map_sub, map_one, hred,
        ZMod.pow_card_sub_one_eq_one hrone, sub_self]
    have hz := kernel_product p s hp.pos _ _ ha hb
    calc
      _ = (((p * k + r : ℕ) : ZMod (p ^ (s + 2)))) ^ n *
        (((((p * k + r : ℕ) : ZMod (p ^ (s + 2)))) ^ (p ^ s * (p - 1)) - 1) *
        (1 - ((((p * k + r : ℕ) : ZMod (p ^ (s + 2)))) - 1) ^ (p - 1))) := by ring
      _ = 0 := by rw [hz, mul_zero]

private lemma weight_reduction {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (s : ℕ) :
    (∑ k ∈ range (p ^ (s + 1)), (k : ZMod p) *
      (2 : ZMod p) ^ (p ^ (s + 2) - 1 - (p * k + 1))) = (2 : ZMod p)⁻¹ := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hodd (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  have hpow (x : ZMod p) (a : ℕ) : x ^ (p ^ a) = x := by
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  let x : ZMod p := (2 : ZMod p)⁻¹
  have hx : 2 * x = 1 := mul_inv_cancel₀ htwo
  have hxne : x ≠ 1 := by
    intro he
    rw [he] at hx
    have hz : (1 : ZMod p) = 0 := by linear_combination hx
    exact one_ne_zero hz
  have hweight (k : ℕ) (hk : k < p ^ (s + 1)) :
      (2 : ZMod p) ^ (p ^ (s + 2) - 1 - (p * k + 1)) = x ^ (k + 1) := by
    have hbound : p * k + 2 ≤ p ^ (s + 2) := by
      have he : p ^ (s + 2) = p * p ^ (s + 1) := by rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]; ring
      rw [he]
      have := hp.two_le
      nlinarith
    have he : p ^ (s + 2) - 1 - (p * k + 1) + (p * k + 2) = p ^ (s + 2) := by omega
    have heq : (2 : ZMod p) ^ (p ^ (s + 2) - 1 - (p * k + 1)) * (2 : ZMod p) ^ (k + 1) = 1 := by
      have h := hpow (2 : ZMod p) (s + 2)
      rw [← he, pow_add] at h
      have hpk : (2 : ZMod p) ^ (p * k + 2) = (2 : ZMod p) ^ (k + 1) * 2 := by
        rw [pow_add, pow_mul, ZMod.pow_card]
        ring
      rw [hpk] at h
      exact (mul_right_cancel₀ htwo) (by simpa only [mul_assoc, one_mul] using h)
    apply (mul_left_injective₀ (pow_ne_zero (k + 1) htwo))
    change (2 : ZMod p) ^ (p ^ (s + 2) - 1 - (p * k + 1)) * (2 : ZMod p) ^ (k + 1) =
      x ^ (k + 1) * (2 : ZMod p) ^ (k + 1)
    rw [heq]
    dsimp [x]
    rw [← mul_pow, inv_mul_cancel₀ htwo, one_pow]
  have hG : ∑ k ∈ range (p ^ (s + 1)), x ^ k = 1 := by
    have hg := geom_sum_mul x (p ^ (s + 1))
    rw [hpow] at hg
    apply (mul_left_injective₀ (sub_ne_zero.mpr hxne))
    simpa using hg
  have hS : ∑ k ∈ range (p ^ (s + 1)), (k : ZMod p) * x ^ k = 1 := by
    have hs := weighted_geometric x (p ^ (s + 1))
    have hz : ((p ^ (s + 1) : ℕ) : ZMod p) = 0 := by simp [pow_succ]
    rw [hG, hz, hpow] at hs
    have hx' : 1 - x = x := by linear_combination -hx
    rw [hx'] at hs
    apply (mul_left_injective₀ (inv_ne_zero htwo))
    linear_combination hs
  calc
    _ = ∑ k ∈ range (p ^ (s + 1)), (k : ZMod p) * x ^ (k + 1) := by
      apply sum_congr rfl
      intro k hk
      rw [hweight k (mem_range.mp hk)]
    _ = (∑ k ∈ range (p ^ (s + 1)), (k : ZMod p) * x ^ k) * x := by
      rw [sum_mul]
      apply sum_congr rfl
      intro k _
      rw [pow_succ, mul_assoc]
    _ = x := by rw [hS, one_mul]

private lemma high_cancel {p : ℕ} (hp : 0 < p) (s : ℕ) (a : ZMod (p ^ (s + 2)))
    (ha : (p : ZMod (p ^ (s + 2))) ^ (s + 1) * a = 0) :
    ZMod.castHom (dvd_pow_self p (by omega : s + 2 ≠ 0)) (ZMod p) a = 0 := by
  letI : NeZero (p ^ (s + 2)) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  have hz : ((p ^ (s + 1) * a.val : ℕ) : ZMod (p ^ (s + 2))) = 0 := by
    rw [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val, ha]
  have hd' := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hd'' : p ^ (s + 1) * p ∣ p ^ (s + 1) * a.val := by
    simpa only [← pow_succ] using hd'
  have hd : p ∣ a.val := (Nat.mul_dvd_mul_iff_left (pow_pos hp _)).mp hd''
  rw [← ZMod.natCast_zmod_val a, map_natCast]
  exact (ZMod.natCast_eq_zero_iff a.val p).mpr hd

private lemma not_lower_period {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (s : ℕ) :
    ¬ (∃ N, ∀ n, N ≤ n →
      A051293.fubini (n + (p ^ s * (p - 1))) ≡ A051293.fubini n [MOD p ^ (s + 2)]) := by
  intro h
  obtain ⟨N, hN⟩ := h
  let n := max N (s + 2)
  have hn : s + 2 ≤ n ∧ N ≤ n := ⟨le_max_right _ _, le_max_left _ _⟩
  let W : ZMod (p ^ (s + 2)) := ∑ k ∈ range (p ^ (s + 1)),
    (k : ZMod (p ^ (s + 2))) * (2 : ZMod (p ^ (s + 2))) ^ (p ^ (s + 2) - 1 - (p * k + 1))
  let Q : Polynomial (ZMod (p ^ (s + 2))) := 1 - (Polynomial.X - 1) ^ (p - 1)
  have hm := period_polynomial_moment hN hn.2 Q
  simp only [Q, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X] at hm
  have heval : (∑ j ∈ range (p ^ (s + 2)), (2 : ZMod (p ^ (s + 2))) ^ (p ^ (s + 2) - 1 - j) *
      (j : ZMod (p ^ (s + 2))) ^ n * ((j : ZMod (p ^ (s + 2))) ^ (p ^ s * (p - 1)) - 1) *
      (1 - ((j : ZMod (p ^ (s + 2))) - 1) ^ (p - 1))) = -(p : ZMod (p ^ (s + 2))) ^ (s + 1) * W := by
    conv_lhs => arg 1; rw [show p ^ (s + 2) = p * p ^ (s + 1) by rw [show s + 2 = 1 + (s + 1) by omega, pow_add, pow_one]]
    rw [sum_blocks]
    change (∑ k ∈ range (p ^ (s + 1)), ∑ r ∈ range p,
      (2 : ZMod (p ^ (s + 2))) ^ (p ^ (s + 2) - 1 - (p * k + r)) *
      ((p * k + r : ℕ) : ZMod (p ^ (s + 2))) ^ n *
      (((p * k + r : ℕ) : ZMod (p ^ (s + 2))) ^ (p ^ s * (p - 1)) - 1) *
      (1 - (((p * k + r : ℕ) : ZMod (p ^ (s + 2))) - 1) ^ (p - 1))) = _
    have hinner (k : ℕ) : (∑ r ∈ range p,
      (2 : ZMod (p ^ (s + 2))) ^ (p ^ (s + 2) - 1 - (p * k + r)) *
      ((p * k + r : ℕ) : ZMod (p ^ (s + 2))) ^ n *
      (((p * k + r : ℕ) : ZMod (p ^ (s + 2))) ^ (p ^ s * (p - 1)) - 1) *
      (1 - (((p * k + r : ℕ) : ZMod (p ^ (s + 2))) - 1) ^ (p - 1))) =
      -(p : ZMod (p ^ (s + 2))) ^ (s + 1) * ((k : ZMod (p ^ (s + 2))) *
        (2 : ZMod (p ^ (s + 2))) ^ (p ^ (s + 2) - 1 - (p * k + 1))) := by
      calc
        _ = ∑ r ∈ range p, (2 : ZMod (p ^ (s + 2))) ^ (p ^ (s + 2) - 1 - (p * k + r)) *
            (if r = 1 then -(p : ZMod (p ^ (s + 2))) ^ (s + 1) * k else 0) := by
          apply sum_congr rfl
          intro r hr
          rw [← projector_term hp hodd s hn.1 k r (mem_range.mp hr)]
          ring
        _ = _ := by
          simp only [mul_ite, mul_zero, sum_ite_eq', mem_range, hp.one_lt, if_true]
          ring
    simp_rw [hinner]
    exact (mul_sum _ _ _).symm
  have hpW : (p : ZMod (p ^ (s + 2))) ^ (s + 1) * W = 0 := by
    rw [heval, neg_mul] at hm
    exact neg_eq_zero.mp hm
  let π := ZMod.castHom (show p ∣ p ^ (s + 2) by exact dvd_pow_self p (by omega : s + 2 ≠ 0)) (ZMod p)
  have hπW : π W = 0 := high_cancel hp.pos s W hpW
  have hW : π W = (2 : ZMod p)⁻¹ := by
    dsimp [W]
    simp only [map_sum, map_mul, map_pow, map_natCast, map_ofNat]
    exact weight_reduction hp hodd s
  haveI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hodd (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  exact (inv_ne_zero htwo) (hW.symm.trans hπW)

private lemma power_period_upper {p T : ℕ} (s : ℕ) (hp : p.Prime)
    (hT : p ^ s * (p - 1) ∣ T) :
    ∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p ^ (s + 1)] := by
  obtain ⟨N, P, hP, _, hN⟩ :=
    fubini_mod_eventuallyPeriodic_conjecture (p ^ (s + 1)) (by exact (one_lt_pow₀ hp.one_lt (by omega)).le)
  have hphi : Nat.totient (p ^ (s + 1)) = p ^ s * (p - 1) := by
    simpa using Nat.totient_prime_pow_succ hp s
  rw [hphi] at hP
  obtain ⟨k, hk⟩ := hP.trans hT
  refine ⟨N, fun n hn => ?_⟩
  rw [hk]
  clear hk
  induction k with
  | zero => exact Nat.ModEq.refl _
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact (hN (n + P * k) (by omega)).trans ih

private lemma power_period_iff {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (s T : ℕ) :
    (∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p ^ (s + 1)]) ↔
      p ^ s * (p - 1) ∣ T := by
  induction s generalizing T with
  | zero => simpa using fubini_prime_eventual_period_iff (T := T) hp hodd
  | succ s ih =>
    constructor
    · intro hT
      have hprev : ∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p ^ (s + 1)] := by
        obtain ⟨N, hN⟩ := hT
        exact ⟨N, fun n hn => (hN n hn).of_dvd (pow_dvd_pow p (by omega))⟩
      obtain ⟨t, ht⟩ := (ih T).mp hprev
      let A := p ^ s * (p - 1)
      have hU := power_period_upper (s + 1) hp (dvd_refl (p ^ (s + 1) * (p - 1)))
      have hcast (a : ℕ)
          (ha : ∃ N, ∀ n, N ≤ n → fubini (n + a) ≡ fubini n [MOD p ^ (s + 2)]) :
          ∃ N, ∀ n, N ≤ n → (fubini (n + a) : ZMod (p ^ (s + 2))) = (fubini n : ZMod (p ^ (s + 2))) := by
        obtain ⟨N, hN⟩ := ha
        exact ⟨N, fun n hn => (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hN n hn)⟩
      have hg := eventual_eq_gcd (fun n => (fubini n : ZMod (p ^ (s + 2))))
        (hcast T hT) (hcast (p ^ (s + 1) * (p - 1)) hU)
      have hgcd : Nat.gcd T (p ^ (s + 1) * (p - 1)) = A * Nat.gcd t p := by
        rw [ht, show p ^ (s + 1) * (p - 1) = (p ^ s * (p - 1)) * p by rw [pow_succ]; ring,
          Nat.gcd_mul_left]
      rcases hp.eq_one_or_self_of_dvd (Nat.gcd t p) (Nat.gcd_dvd_right t p) with h1 | hself
      · rw [hgcd, h1, Nat.mul_one] at hg
        apply False.elim
        apply not_lower_period hp hodd s
        obtain ⟨N, hN⟩ := hg
        exact ⟨N, fun n hn => (ZMod.natCast_eq_natCast_iff _ _ _).mp (hN n hn)⟩
      · have hd := Nat.gcd_dvd_left T (p ^ (s + 1) * (p - 1))
        rw [hgcd, hself] at hd
        simpa only [A, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd
    · exact power_period_upper (s + 1) hp

/-- For an odd prime `p` and positive exponent `m`, the eventual periods of
`A051293.fubini` modulo `p ^ m` are exactly the multiples of
`p ^ (m - 1) * (p - 1)`. Natural shifts include zero. -/
theorem fubini_prime_power_eventual_period_iff {p m T : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hm : 1 ≤ m) :
    (∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p ^ m]) ↔
      p ^ (m - 1) * (p - 1) ∣ T := by
  have h := power_period_iff hp hodd (m - 1) T
  simpa only [Nat.sub_add_cancel hm] using h

example : ∃ N, ∀ n, N ≤ n → fubini (n + 2) ≡ fubini n [MOD 3 ^ 1] := by
  exact (fubini_prime_power_eventual_period_iff (by decide) (by decide) (by decide)).mpr (by decide)

example : ∃ N, ∀ n, N ≤ n → fubini (n + 6) ≡ fubini n [MOD 3 ^ 2] := by
  exact (fubini_prime_power_eventual_period_iff (by decide) (by decide) (by decide)).mpr (by decide)

example : ∃ N, ∀ n, N ≤ n → fubini (n + 18) ≡ fubini n [MOD 3 ^ 3] := by
  exact (fubini_prime_power_eventual_period_iff (by decide) (by decide) (by decide)).mpr (by decide)

example : ∃ N, ∀ n, N ≤ n → fubini (n + 0) ≡ fubini n [MOD 3 ^ 3] := by
  exact (fubini_prime_power_eventual_period_iff (by decide) (by decide) (by decide)).mpr (dvd_zero _)

example : ¬ (∃ N, ∀ n, N ≤ n → fubini (n + 6) ≡ fubini n [MOD 3 ^ 3]) := by
  rw [fubini_prime_power_eventual_period_iff (by decide) (by decide) (by decide)]
  decide

end A000670
