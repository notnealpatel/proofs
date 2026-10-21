/-
# A226898 — Greathouse: Hooley's `Δ(n) ≤ τ(n)/2` for `n > 4`

## OEIS source (retrieved with `oeis show A226898`, 2026-10-21)

```
NAME:     Hooley's Delta function: maximum number of divisors of n in [u, e*u]
          for all u. (Here e is Euler's number 2.718... = A001113.)
TERMS:    1,2,1,2,1,2,1,2,1,2,1,3,1,2,2,2,1,2,1,3,2,2,1,4,1,2,1,2,1,3,1,2,1,2,
          2,3,1,2,1,4,1,3,1,2,2,2,1,4,1,2,1,2,1,2,2,3,1,2,1,4,1,2,2,2,2,2,1,2,
          1,3,1,4,1,2,2,2,2,2,1,4,1,2,1,4,1,2,1,2,1,4,2,2
COMMENT (equivalent definition):
  Equivalent definition: Let D be the set of divisors of n, then
  Delta(n) = Max_{d in D} #([d, e*d] INTERSECT D).
COMMENT (the conjecture):
  Conjecture: For n > 4, a(n) <= d(n)/2 where d(n) is A000005.
  - _Charles R Greathouse IV_, Jan 24 2026
```

## Status

Triage status: open (no proof in the entry or in the literature found by the
triage).  Computation: `2·Δ(n) ≤ τ(n)` holds for every `n ≤ 400000` except
`n = 1, 2, 4`, which the hypothesis `n > 4` excludes.  This module proves the
conjecture (`greathouse_conjecture`), sorry-free.

## Formalization

* `hooleyWindow n u` is `D ∩ [u, e·u]`; `hooleyDelta n` is the entry's
  equivalent form `max_{d ∈ D} #([d, e·d] ∩ D)` (`0` for `n = 0`, outside the
  offset).  `isGreatest_hooleyDelta` proves it is the maximum over all real
  `u > 0`, matching the NAME.
* `d(n)/2` is read over the rationals, so `a(n) ≤ d(n)/2` is stated as
  `2 * hooleyDelta n ≤ n.divisors.card`.

## Proof

If an odd prime `p` divides `n`, two distinct divisors with the same `p`-free
part differ by a factor `≥ p ≥ 3 > e`, so `d ↦ d / p^{v_p(d)}` is injective on
any window and `Δ(n) ≤ τ(n / p^{v_p(n)}) = τ(n)/(v_p(n)+1) ≤ τ(n)/2`.
Otherwise `n = 2^k` with `k ≥ 3`; a window holds at most two powers of `2`
since `e < 4`, and `τ(2^k) = k + 1 ≥ 4`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A226898HooleyDelta

/-- The divisors of `n` in the window `[u, e·u]`, where `e = Real.exp 1`. -/
noncomputable def hooleyWindow (n : ℕ) (u : ℝ) : Finset ℕ :=
  n.divisors.filter (fun d => u ≤ d ∧ (d : ℝ) ≤ Real.exp 1 * u)

/-- Hooley's `Δ(n)` (A226898), in the entry's equivalent form
`Δ(n) = max_{d ∈ D} #([d, e·d] ∩ D)` with `D` the divisors of `n`. -/
noncomputable def hooleyDelta (n : ℕ) : ℕ :=
  n.divisors.sup (fun d => (hooleyWindow n d).card)

/-- Membership in the window, unfolded. -/
theorem mem_hooleyWindow {n d : ℕ} {u : ℝ} :
    d ∈ hooleyWindow n u ↔ (d ∣ n ∧ n ≠ 0) ∧ u ≤ d ∧ (d : ℝ) ≤ Real.exp 1 * u := by
  simp only [hooleyWindow, Finset.mem_filter, Nat.mem_divisors]

/-- Two members of one window have ratio below `3` (because `e < 3`). -/
theorem lt_three_mul_of_mem_hooleyWindow {n x y : ℕ} {u : ℝ} (hx : x ∈ hooleyWindow n u)
    (hy : y ∈ hooleyWindow n u) : y < 3 * x := by
  rw [mem_hooleyWindow] at hx hy
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hxu : u ≤ (x : ℝ) := hx.2.1
  have hyle : (y : ℝ) ≤ Real.exp 1 * u := hy.2.2
  have hx0 : (0 : ℝ) < x := by
    have : 0 < x := Nat.pos_of_dvd_of_pos hx.1.1 (Nat.pos_of_ne_zero hx.1.2)
    exact_mod_cast this
  have hreal : (y : ℝ) < 3 * x := by
    calc (y : ℝ) ≤ Real.exp 1 * u := hyle
      _ ≤ Real.exp 1 * x := by gcongr
      _ < 3 * x := by gcongr
  exact_mod_cast hreal

/-- If two nonzero numbers share their `p`-free part and the first has smaller `p`-adic
valuation, the second is at least `p` times the first. -/
theorem mul_le_of_ordCompl_eq {p x y : ℕ} (hp : p.Prime)
    (hc : ordCompl[p] x = ordCompl[p] y) (hlt : x.factorization p < y.factorization p) :
    p * x ≤ y := by
  have hx' := Nat.ordProj_mul_ordCompl_eq_self x p
  have hy' := Nat.ordProj_mul_ordCompl_eq_self y p
  have hpow : p * p ^ x.factorization p ≤ p ^ y.factorization p := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right hp.pos hlt
  calc p * x = p * p ^ x.factorization p * ordCompl[p] x := by rw [mul_assoc, hx']
    _ ≤ p ^ y.factorization p * ordCompl[p] y := by rw [hc]; gcongr
    _ = y := hy'

/-- Every window `[u, e·u]` holds at most `Δ(n)` divisors: the supremum over divisor
windows dominates the supremum over all real `u` (shift `u` up to the least divisor in
the window). -/
theorem card_hooleyWindow_le_hooleyDelta (n : ℕ) (u : ℝ) :
    (hooleyWindow n u).card ≤ hooleyDelta n := by
  set W := hooleyWindow n u with hW
  rcases W.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]; exact Nat.zero_le _
  set d := W.min' hne with hddef
  have hdW : d ∈ W := W.min'_mem hne
  have hd := mem_hooleyWindow.mp hdW
  have hsub : W ⊆ hooleyWindow n d := by
    intro y hy
    have hy' := mem_hooleyWindow.mp hy
    have hdy : d ≤ y := W.min'_le y hy
    have hdyR : (d : ℝ) ≤ y := by exact_mod_cast hdy
    have hud : u ≤ (d : ℝ) := hd.2.1
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    refine mem_hooleyWindow.mpr ⟨hy'.1, hdyR, ?_⟩
    calc (y : ℝ) ≤ Real.exp 1 * u := hy'.2.2
      _ ≤ Real.exp 1 * d := by gcongr
  calc W.card ≤ (hooleyWindow n d).card := Finset.card_le_card hsub
    _ ≤ hooleyDelta n := by
      rw [hooleyDelta]
      exact Finset.le_sup (f := fun m : ℕ => (hooleyWindow n m).card) (Nat.mem_divisors.mpr hd.1)

/-- Fidelity with the entry's NAME: `Δ(n)` is the maximum over all real `u > 0` of the
number of divisors of `n` in `[u, e·u]`. -/
theorem isGreatest_hooleyDelta (n : ℕ) :
    IsGreatest {k | ∃ u : ℝ, 0 < u ∧ (hooleyWindow n u).card = k} (hooleyDelta n) := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · refine ⟨1, one_pos, ?_⟩
      simp [hooleyWindow, hooleyDelta]
    obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup _ (Nat.nonempty_divisors.mpr hn)
      (fun d => (hooleyWindow n d).card)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    exact ⟨d, by exact_mod_cast hdpos, hdeq.symm⟩
  · rintro k ⟨u, -, rfl⟩
    exact card_hooleyWindow_le_hooleyDelta n u

/-- For `b ≤ 100`, the test `a ≤ e·b` agrees with the rational test `a ≤ 2.718·b`
(no integer lies in `(2.718·b, e·b]` for these `b`). -/
theorem natCast_le_exp_one_mul_iff {a b : ℕ} (hb : b ≤ 100) :
    (a : ℝ) ≤ Real.exp 1 * b ↔ 1000 * a ≤ 2718 * b := by
  have hlo : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hhi : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  constructor
  · intro h
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hreal : (10000 : ℝ) * a < 27183 * b ∨ b = 0 := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · exact Or.inr h0
      · left
        have hbpos : (0 : ℝ) < b := by exact_mod_cast h0
        nlinarith
    rcases hreal with hreal | h0
    · have hnat : 10000 * a < 27183 * b := by exact_mod_cast hreal
      interval_cases b <;> omega
    · subst h0
      have : (a : ℝ) ≤ 0 := by simpa using h
      have ha : a = 0 := by exact_mod_cast le_antisymm this (Nat.cast_nonneg a)
      omega
  · intro h
    have hreal : (1000 : ℝ) * a ≤ 2718 * b := by exact_mod_cast h
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    nlinarith

/-- A computable stand-in for `Δ(n)` using the rational test `d' ≤ 2.718·d` in place of
`d' ≤ e·d`; it agrees with `hooleyDelta` for `n ≤ 100` (`hooleyDelta_eq_hooleyDeltaRat`). -/
def hooleyDeltaRat (n : ℕ) : ℕ :=
  n.divisors.sup (fun d => (n.divisors.filter (fun d' => d ≤ d' ∧ 1000 * d' ≤ 2718 * d)).card)

/-- For `n ≤ 100`, `Δ(n)` equals its computable rational stand-in. -/
theorem hooleyDelta_eq_hooleyDeltaRat {n : ℕ} (hn : n ≤ 100) :
    hooleyDelta n = hooleyDeltaRat n := by
  rw [hooleyDelta, hooleyDeltaRat]
  refine Finset.sup_congr rfl (fun d hd => congrArg Finset.card ?_)
  have hdn : d ≤ 100 := (Nat.divisor_le hd).trans hn
  refine Finset.filter_congr (fun d' _ => ?_)
  rw [Nat.cast_le, natCast_le_exp_one_mul_iff hdn]

/-- Ground truth: `Δ(1), …, Δ(92)` agree with the 92 terms listed in A226898. -/
example : (List.range 92).map (fun i => hooleyDeltaRat (i + 1)) =
    [1,2,1,2,1,2,1,2,1,2,1,3,1,2,2,2,1,2,1,3,2,2,1,4,1,2,1,2,1,3,1,2,1,2,2,3,1,2,1,4,1,3,1,2,
      2,2,1,4,1,2,1,2,1,2,2,3,1,2,1,4,1,2,2,2,2,2,1,2,1,3,1,4,1,2,2,2,2,2,1,4,1,2,1,4,1,2,1,2,
      1,4,2,2] := by
  decide

/-- Ground truth for the real-valued definition: `Δ(12) = 3` (window `[2, 2e]` holds `2, 3, 4`). -/
example : hooleyDelta 12 = 3 := by
  rw [hooleyDelta_eq_hooleyDeltaRat (by norm_num)]; decide

/-- Ground truth: `Δ(24) = 4` (window `[3, 3e]` holds `3, 4, 6, 8`). -/
example : hooleyDelta 24 = 4 := by
  rw [hooleyDelta_eq_hooleyDeltaRat (by norm_num)]; decide

/-- Odd-prime case: the window injects into the divisors of the `p`-free part. -/
theorem card_hooleyWindow_le_of_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hp3 : 3 ≤ p) (u : ℝ) :
    (hooleyWindow n u).card ≤ (ordCompl[p] n).divisors.card := by
  apply Finset.card_le_card_of_injOn (fun d => ordCompl[p] d)
  · intro d hd
    rw [Finset.mem_coe, mem_hooleyWindow] at hd
    rw [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨Nat.ordCompl_dvd_ordCompl_of_dvd hd.1.1 p, (Nat.ordCompl_pos p hn).ne'⟩
  · intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    have hxy' : ordCompl[p] x = ordCompl[p] y := hxy
    rcases lt_trichotomy (x.factorization p) (y.factorization p) with h | h | h
    · have h1 := mul_le_of_ordCompl_eq hp hxy' h
      have h2 := lt_three_mul_of_mem_hooleyWindow hx hy
      nlinarith
    · rw [← Nat.ordProj_mul_ordCompl_eq_self x p, ← Nat.ordProj_mul_ordCompl_eq_self y p, hxy', h]
    · have h1 := mul_le_of_ordCompl_eq hp hxy'.symm h
      have h2 := lt_three_mul_of_mem_hooleyWindow hy hx
      nlinarith

/-- The number of divisors factors as `(v_p(n) + 1) · τ(n / p^{v_p(n)})`. -/
theorem card_divisors_eq_mul_ordCompl {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    n.divisors.card = (n.factorization p + 1) * (ordCompl[p] n).divisors.card := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [Nat.Coprime.card_divisors_mul ((Nat.coprime_ordCompl hp hn).pow_left _),
    Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- Power-of-two case: a window contains at most two divisors of `2 ^ k`. -/
theorem card_hooleyWindow_two_pow_le (k : ℕ) (u : ℝ) : (hooleyWindow (2 ^ k) u).card ≤ 2 := by
  set W := hooleyWindow (2 ^ k) u with hW
  rcases W.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]; omega
  set x := W.min' hne with hxdef
  have hxW : x ∈ W := W.min'_mem hne
  have hpow : ∀ z ∈ W, ∃ j, z = 2 ^ j := by
    intro z hz
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (mem_hooleyWindow.mp hz).1.1
    exact ⟨j, hj⟩
  have hsub : W ⊆ {x, 2 * x} := by
    intro y hy
    have hxy : x ≤ y := W.min'_le y hy
    have hy3 : y < 3 * x := lt_three_mul_of_mem_hooleyWindow hxW hy
    obtain ⟨i, hi⟩ := hpow x hxW
    obtain ⟨j, hj⟩ := hpow y hy
    rw [hi, hj] at hxy hy3
    have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hxy
    have hji : j ≤ i + 1 := by
      by_contra hcon
      have h4 : 2 ^ (i + 2) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_add] at h4
      omega
    rw [Finset.mem_insert, Finset.mem_singleton, hi, hj]
    rcases Nat.eq_or_lt_of_le hij with h | h
    · left; rw [h]
    · right; rw [show j = i + 1 by omega, pow_succ]; ring
  calc W.card ≤ ({x, 2 * x} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- Every window `[u, e·u]` of a number `n > 4` holds at most half of its divisors. -/
theorem two_mul_card_hooleyWindow_le {n : ℕ} (hn : 4 < n) (u : ℝ) :
    2 * (hooleyWindow n u).card ≤ n.divisors.card := by
  have hn0 : n ≠ 0 := by omega
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨k, rfl⟩ | ⟨p, hp, hpn, hodd⟩
  · have hk : 3 ≤ k := by
      by_contra hcon
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hcard : (2 ^ k).divisors.card = k + 1 := by
      rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
    have h2 := card_hooleyWindow_two_pow_le k u
    omega
  · have hp3 : 3 ≤ p := by
      obtain ⟨m, hm⟩ := hodd
      have h2 := hp.two_le
      omega
    have hv : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn0).mp hpn
    have hW := card_hooleyWindow_le_of_prime hn0 hp hp3 u
    rw [card_divisors_eq_mul_ordCompl hn0 hp]
    calc 2 * (hooleyWindow n u).card ≤ 2 * (ordCompl[p] n).divisors.card := by gcongr
      _ ≤ (n.factorization p + 1) * (ordCompl[p] n).divisors.card := by gcongr; omega

/-- **Greathouse's conjecture (A226898, Charles R Greathouse IV, Jan 24 2026).**

Verbatim: "Conjecture: For n > 4, a(n) <= d(n)/2 where d(n) is A000005."
Here `a(n) = Δ(n)` is Hooley's Delta function and `d(n) = τ(n)` the number of
divisors; the inequality is stated without division as `2 Δ(n) ≤ τ(n)`.  The
hypothesis `4 < n` is sharp: the bound fails at `n = 1, 2, 4`. -/
theorem greathouse_conjecture {n : ℕ} (hn : 4 < n) : 2 * hooleyDelta n ≤ n.divisors.card := by
  rw [hooleyDelta]
  have hne : n.divisors.Nonempty := Nat.nonempty_divisors.mpr (by omega)
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_sup _ hne (fun d => (hooleyWindow n d).card)
  rw [hd]
  exact two_mul_card_hooleyWindow_le hn d

/-- The hypothesis `4 < n` is sharp: the bound fails at `n = 4` (`Δ(4) = 2`, `τ(4) = 3`). -/
example : ¬ 2 * hooleyDelta 4 ≤ (4 : ℕ).divisors.card := by
  rw [hooleyDelta_eq_hooleyDeltaRat (by norm_num)]; decide

/-- The bound also fails at `n = 2` (`Δ(2) = τ(2) = 2`). -/
example : ¬ 2 * hooleyDelta 2 ≤ (2 : ℕ).divisors.card := by
  rw [hooleyDelta_eq_hooleyDeltaRat (by norm_num)]; decide

/-- The bound also fails at `n = 1` (`Δ(1) = τ(1) = 1`). -/
example : ¬ 2 * hooleyDelta 1 ≤ (1 : ℕ).divisors.card := by
  rw [hooleyDelta_eq_hooleyDeltaRat (by norm_num)]; decide

/-- At `n = 3` the bound holds although `n ≤ 4` (`Δ(3) = 1`, `τ(3) = 2`). -/
example : 2 * hooleyDelta 3 ≤ (3 : ℕ).divisors.card := by
  rw [hooleyDelta_eq_hooleyDeltaRat (by norm_num)]; decide

end Candidates.A226898HooleyDelta
