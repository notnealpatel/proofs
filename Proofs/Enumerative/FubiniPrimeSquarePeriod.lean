import Enumerative.FubiniPrimePeriod

/-!
# Exact eventual Fubini periods modulo odd prime squares

This is the prime-square case of the known period theorem in B. Poonen,
*Periodicity of a combinatorial sequence*, Fibonacci Quarterly 26 (1988),
70–76, Theorem 3 (p. 73); the upper bound comes from Theorem 2 (p. 72).
Reference: https://www.fq.math.ca/Scanned/26-1/poonen.pdf.
No novelty is claimed.

The sequence is exactly `A051293.fubini`. For a prime `p ≠ 2`, a natural
shift `T` is an eventual period modulo `p ^ 2` if and only if
`p * (p - 1) ∣ T`. This includes `T = 0`; it does not assert periodicity
from index zero. The lower bound uses polynomial-weighted Poonen differences
and the projector `1 - (X - 1) ^ (p - 1)`. A common-tail shift gives gcd
closure of eventual periods, which combines the lower bound with the
existing prime-period theorem and totient upper bound.
-/

set_option autoImplicit false
open Finset
namespace A000670
open A051293

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

private lemma square_kernel {p : ℕ} (hp : 0 < p) (a : ZMod (p ^ 2))
    (ha : ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by decide)) (ZMod p) a = 0) :
    ∃ b : ZMod (p ^ 2), a = (p : ZMod (p ^ 2)) * b := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  let π := ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by decide)) (ZMod p)
  change π a = 0 at ha
  have hv : (a.val : ZMod p) = 0 := by
    have h := congrArg π (ZMod.natCast_zmod_val a)
    simpa only [map_natCast, ha] using h
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff a.val p).mp hv
  refine ⟨(k : ZMod (p ^ 2)), ?_⟩
  rw [← Nat.cast_mul, ← hk, ZMod.natCast_zmod_val]

private lemma square_kernel_mul {p : ℕ} (hp : 0 < p) (a b : ZMod (p ^ 2))
    (ha : ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by decide)) (ZMod p) a = 0)
    (hb : ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by decide)) (ZMod p) b = 0) :
    a * b = 0 := by
  obtain ⟨u, rfl⟩ := square_kernel hp a ha
  obtain ⟨v, rfl⟩ := square_kernel hp b hb
  have hz : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  calc
    _ = (p : ZMod (p ^ 2)) ^ 2 * (u * v) := by ring
    _ = 0 := by rw [hz, zero_mul]

private lemma square_projector_term {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hn : 2 ≤ n) (hpn : p ∣ n) (k r : ℕ) (hr : r < p) :
    ((p * k + r : ℕ) : ZMod (p ^ 2)) ^ n *
        (((p * k + r : ℕ) : ZMod (p ^ 2)) ^ (p - 1) - 1) *
        (1 - (((p * k + r : ℕ) : ZMod (p ^ 2)) - 1) ^ (p - 1)) =
      if r = 1 then -(p : ZMod (p ^ 2)) * k else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let π := ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by decide)) (ZMod p)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpz : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  by_cases hr0 : r = 0
  · subst r
    have hz : ((p * k + 0 : ℕ) : ZMod (p ^ 2)) ^ n = 0 := by
      simp only [Nat.add_zero, Nat.cast_mul, mul_pow]
      rw [ZMod.natCast_pow_eq_zero_of_le p hn, zero_mul]
    rw [hz]
    simp
  by_cases hr1 : r = 1
  · subst r
    rw [if_pos rfl]
    let x : ZMod (p ^ 2) := (p : ZMod (p ^ 2)) * k
    have hx : x ^ 2 = 0 := by dsimp [x]; rw [mul_pow, hpz, zero_mul]
    have ha : ((p * k + 1 : ℕ) : ZMod (p ^ 2)) = 1 + x := by dsimp [x]; push_cast; ring
    have hnx : (n : ZMod (p ^ 2)) * x = 0 := by
      obtain ⟨t, rfl⟩ := hpn
      dsimp [x]
      push_cast
      calc
        _ = (p : ZMod (p ^ 2)) ^ 2 * (t * k) := by ring
        _ = 0 := by rw [hpz, zero_mul]
    have hqx : ((p - 1 : ℕ) : ZMod (p ^ 2)) * x = -(p : ZMod (p ^ 2)) * k := by
      dsimp [x]
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      linear_combination (k : ZMod (p ^ 2)) * hpz
    have hxq : x ^ (p - 1) = 0 := by
      obtain ⟨t, ht⟩ : ∃ t, p - 1 = 2 + t := ⟨p - 1 - 2, by omega⟩
      rw [ht, pow_add, hx, zero_mul]
    rw [ha, one_add_pow_sq_zero x hx n, hnx, add_zero,
      one_add_pow_sq_zero x hx (p - 1), add_sub_cancel_left,
      hqx, add_sub_cancel_left, hxq]
    ring
  · rw [if_neg hr1]
    have hred : π (((p * k + r : ℕ) : ZMod (p ^ 2))) = (r : ZMod p) := by
      simp [π, Nat.cast_add, Nat.cast_mul]
    have hrz : (r : ZMod p) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hr] at hv
      exact hr0 (by simpa using hv)
    have hrone : (r : ZMod p) - 1 ≠ 0 := by
      intro hz
      have he : (r : ZMod p) = (1 : ℕ) := by simpa using (sub_eq_zero.mp hz)
      have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt hr, ZMod.val_natCast_of_lt hp.one_lt] at hv
      exact hr1 hv
    have hfirst : π ((((p * k + r : ℕ) : ZMod (p ^ 2))) ^ (p - 1) - 1) = 0 := by
      rw [map_sub, map_pow, map_one, hred, ZMod.pow_card_sub_one_eq_one hrz, sub_self]
    have hsecond : π (1 - ((((p * k + r : ℕ) : ZMod (p ^ 2))) - 1) ^ (p - 1)) = 0 := by
      rw [map_sub, map_one, map_pow, map_sub, map_one, hred,
        ZMod.pow_card_sub_one_eq_one hrone, sub_self]
    have hz := square_kernel_mul hp.pos _ _ hfirst hsecond
    calc
      _ = (((p * k + r : ℕ) : ZMod (p ^ 2))) ^ n *
          (((((p * k + r : ℕ) : ZMod (p ^ 2))) ^ (p - 1) - 1) *
          (1 - ((((p * k + r : ℕ) : ZMod (p ^ 2))) - 1) ^ (p - 1))) := by ring
      _ = 0 := by rw [hz, mul_zero]

private lemma weighted_geometric {R : Type*} [CommRing R] (x : R) (m : ℕ) :
    (1 - x) * (∑ k ∈ range m, (k : R) * x ^ k) =
      (∑ k ∈ range m, x ^ k) - 1 + (1 - (m : R)) * x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, pow_succ, Nat.cast_add, Nat.cast_one]
    linear_combination ih

private lemma square_weight_reduction {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (∑ k ∈ range p, (k : ZMod p) * (2 : ZMod p) ^ (p ^ 2 - 1 - (p * k + 1))) =
      (2 : ZMod p)⁻¹ := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hodd (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  let x : ZMod p := (2 : ZMod p)⁻¹
  have hx : 2 * x = 1 := mul_inv_cancel₀ htwo
  have hxne : x ≠ 1 := by
    intro he
    rw [he] at hx
    have hz : (1 : ZMod p) = 0 := by linear_combination hx
    exact one_ne_zero hz
  have hweight (k : ℕ) (hk : k < p) :
      (2 : ZMod p) ^ (p ^ 2 - 1 - (p * k + 1)) = x ^ (k + 1) := by
    have he : p ^ 2 - 1 - (p * k + 1) + (k + 1) = (p - 1) * (p + 1 - k) := by
      have hpk : p * k + 2 ≤ p ^ 2 := by nlinarith
      have hk' : k ≤ p + 1 := by omega
      have hp1 : p - 1 + 1 = p := by omega
      have hk1 : p + 1 - k + k = p + 1 := by omega
      have he' : p ^ 2 - 1 - (p * k + 1) + (p * k + 2) = p ^ 2 := by omega
      have hm := congrArg (fun z => (p - 1) * z) hk1
      have hm' := congrArg (fun z => z * k) hp1
      have hm'' := congrArg (fun z => z * (p + 1)) hp1
      nlinarith
    have heq : (2 : ZMod p) ^ (p ^ 2 - 1 - (p * k + 1)) * (2 : ZMod p) ^ (k + 1) = 1 := by
      rw [← pow_add, he, pow_mul, ZMod.pow_card_sub_one_eq_one htwo, one_pow]
    apply (mul_left_injective₀ (pow_ne_zero (k + 1) htwo))
    change (2 : ZMod p) ^ (p ^ 2 - 1 - (p * k + 1)) * (2 : ZMod p) ^ (k + 1) =
      x ^ (k + 1) * (2 : ZMod p) ^ (k + 1)
    rw [heq]
    dsimp [x]
    rw [← mul_pow, inv_mul_cancel₀ htwo, one_pow]
  have hG : ∑ k ∈ range p, x ^ k = 1 := by
    have hg := geom_sum_mul x p
    rw [ZMod.pow_card] at hg
    apply (mul_left_injective₀ (sub_ne_zero.mpr hxne))
    simpa using hg
  have hS : ∑ k ∈ range p, (k : ZMod p) * x ^ k = 1 := by
    have hs := weighted_geometric x p
    rw [hG, ZMod.natCast_self, ZMod.pow_card] at hs
    have hx' : 1 - x = x := by linear_combination -hx
    rw [hx'] at hs
    have hx0 : x ≠ 0 := inv_ne_zero htwo
    apply (mul_left_injective₀ hx0)
    linear_combination hs
  calc
    _ = ∑ k ∈ range p, (k : ZMod p) * x ^ (k + 1) := by
      apply sum_congr rfl
      intro k hk
      rw [hweight k (mem_range.mp hk)]
    _ = (∑ k ∈ range p, (k : ZMod p) * x ^ k) * x := by
      rw [sum_mul]
      apply sum_congr rfl
      intro k _
      rw [pow_succ, mul_assoc]
    _ = x := by rw [hS, one_mul]

private lemma square_mul_prime_eq_zero {p : ℕ} (hp : 0 < p) (a : ZMod (p ^ 2))
    (ha : (p : ZMod (p ^ 2)) * a = 0) :
    ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by decide)) (ZMod p) a = 0 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  have hz : ((p * a.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ha]
  have hd : p ∣ a.val := by
    have hd' := (ZMod.natCast_eq_zero_iff (p * a.val) (p ^ 2)).mp hz
    have hd'' : p * p ∣ p * a.val := by simpa only [pow_two] using hd'
    exact (Nat.mul_dvd_mul_iff_left hp).mp hd''
  rw [← ZMod.natCast_zmod_val a, map_natCast]
  exact (ZMod.natCast_eq_zero_iff a.val p).mpr hd

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


private lemma not_square_sub_one_period {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    ¬ (∃ N, ∀ n, N ≤ n →
      A051293.fubini (n + (p - 1)) ≡ A051293.fubini n [MOD p ^ 2]) := by
  intro h
  obtain ⟨N, hN⟩ := h
  let n := p * (N + 2)
  have hn : 2 ≤ n ∧ N ≤ n := by dsimp [n]; have := hp.two_le; constructor <;> nlinarith
  let W : ZMod (p ^ 2) := ∑ k ∈ range p,
    (k : ZMod (p ^ 2)) * (2 : ZMod (p ^ 2)) ^ (p ^ 2 - 1 - (p * k + 1))
  let Q : Polynomial (ZMod (p ^ 2)) := 1 - (Polynomial.X - 1) ^ (p - 1)
  have hm := period_polynomial_moment hN hn.2 Q
  simp only [Q, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X] at hm
  have heval : (∑ j ∈ range (p ^ 2), (2 : ZMod (p ^ 2)) ^ (p ^ 2 - 1 - j) *
      (j : ZMod (p ^ 2)) ^ n * ((j : ZMod (p ^ 2)) ^ (p - 1) - 1) *
      (1 - ((j : ZMod (p ^ 2)) - 1) ^ (p - 1))) = -(p : ZMod (p ^ 2)) * W := by
    conv_lhs => arg 1; rw [pow_two]
    rw [sum_blocks]
    change (∑ k ∈ range p, ∑ r ∈ range p,
      (2 : ZMod (p ^ 2)) ^ (p ^ 2 - 1 - (p * k + r)) *
      ((p * k + r : ℕ) : ZMod (p ^ 2)) ^ n *
      (((p * k + r : ℕ) : ZMod (p ^ 2)) ^ (p - 1) - 1) *
      (1 - (((p * k + r : ℕ) : ZMod (p ^ 2)) - 1) ^ (p - 1))) = _
    have hinner (k : ℕ) : (∑ r ∈ range p,
      (2 : ZMod (p ^ 2)) ^ (p ^ 2 - 1 - (p * k + r)) *
      ((p * k + r : ℕ) : ZMod (p ^ 2)) ^ n *
      (((p * k + r : ℕ) : ZMod (p ^ 2)) ^ (p - 1) - 1) *
      (1 - (((p * k + r : ℕ) : ZMod (p ^ 2)) - 1) ^ (p - 1))) =
      -(p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2)) *
        (2 : ZMod (p ^ 2)) ^ (p ^ 2 - 1 - (p * k + 1))) := by
      calc
        _ = ∑ r ∈ range p, (2 : ZMod (p ^ 2)) ^ (p ^ 2 - 1 - (p * k + r)) *
            (if r = 1 then -(p : ZMod (p ^ 2)) * k else 0) := by
          apply sum_congr rfl
          intro r hr
          rw [← square_projector_term hp hodd hn.1 (dvd_mul_right p (N + 2)) k r (mem_range.mp hr)]
          ring
        _ = _ := by simp [hp.one_lt]; ring
    simp_rw [hinner]
    exact (mul_sum _ _ _).symm
  have hpW : (p : ZMod (p ^ 2)) * W = 0 := by
    rw [heval, neg_mul] at hm
    exact neg_eq_zero.mp hm
  let π := ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by decide)) (ZMod p)
  have hπW : π W = 0 := square_mul_prime_eq_zero hp.pos W hpW
  have hW : π W = (2 : ZMod p)⁻¹ := by
    dsimp [W]
    simp only [map_sum, map_mul, map_pow, map_natCast, map_ofNat]
    exact square_weight_reduction hp hodd
  haveI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hodd (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  exact (inv_ne_zero htwo) (hW.symm.trans hπW)

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


private lemma square_period_upper {p T : ℕ} (hp : p.Prime)
    (hT : p * (p - 1) ∣ T) :
    ∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p ^ 2] := by
  obtain ⟨N, P, hP, _, hN⟩ :=
    fubini_mod_eventuallyPeriodic_conjecture (p ^ 2) (by have := hp.one_lt; nlinarith)
  have hphi : Nat.totient (p ^ 2) = p * (p - 1) := by
    simpa using Nat.totient_prime_pow_succ hp 1
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

/-- For an odd prime `p`, the eventual Fubini periods modulo `p²` are exactly
multiples of `p * (p - 1)`. The zero shift is included, and no claim of
periodicity from index zero is made. -/
theorem fubini_prime_square_eventual_period_iff {p T : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) :
    (∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p ^ 2]) ↔
      p * (p - 1) ∣ T := by
  constructor
  · intro hT
    have hprime : ∃ N, ∀ n, N ≤ n → fubini (n + T) ≡ fubini n [MOD p] := by
      obtain ⟨N, hN⟩ := hT
      exact ⟨N, fun n hn => (hN n hn).of_dvd (dvd_pow_self p (by decide))⟩
    obtain ⟨t, ht⟩ := prime_sub_one_dvd_fubini_eventual_period hp hodd hprime
    have hU := square_period_upper hp (dvd_refl (p * (p - 1)))
    have hcast (a : ℕ)
        (ha : ∃ N, ∀ n, N ≤ n → fubini (n + a) ≡ fubini n [MOD p ^ 2]) :
        ∃ N, ∀ n, N ≤ n → (fubini (n + a) : ZMod (p ^ 2)) = (fubini n : ZMod (p ^ 2)) := by
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, fun n hn => (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hN n hn)⟩
    have hg := eventual_eq_gcd (fun n => (fubini n : ZMod (p ^ 2)))
      (hcast T hT) (hcast (p * (p - 1)) hU)
    have hgcd : Nat.gcd T (p * (p - 1)) = (p - 1) * Nat.gcd t p := by
      rw [ht, Nat.mul_comm p (p - 1), Nat.gcd_mul_left]
    rcases hp.eq_one_or_self_of_dvd (Nat.gcd t p) (Nat.gcd_dvd_right t p) with h1 | hp'
    · rw [hgcd, h1, Nat.mul_one] at hg
      apply False.elim
      apply not_square_sub_one_period hp hodd
      obtain ⟨N, hN⟩ := hg
      exact ⟨N, fun n hn => (ZMod.natCast_eq_natCast_iff _ _ _).mp (hN n hn)⟩
    · have hd := Nat.gcd_dvd_left T (p * (p - 1))
      rw [hgcd, hp', Nat.mul_comm (p - 1) p] at hd
      exact hd
  · exact square_period_upper hp

example : ∃ N, ∀ n, N ≤ n → fubini (n + 6) ≡ fubini n [MOD 3 ^ 2] := by
  exact (fubini_prime_square_eventual_period_iff (by decide) (by decide)).mpr (by decide)

example : ∃ N, ∀ n, N ≤ n → fubini (n + 0) ≡ fubini n [MOD 3 ^ 2] := by
  exact (fubini_prime_square_eventual_period_iff (by decide) (by decide)).mpr (dvd_zero _)

example : ¬ (∃ N, ∀ n, N ≤ n → fubini (n + 2) ≡ fubini n [MOD 3 ^ 2]) := by
  rw [fubini_prime_square_eventual_period_iff (by decide) (by decide)]
  decide

end A000670
