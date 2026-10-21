/-
# A072995 — Wilson: `a(n) = 0` iff `n/2` is an odd non-prime-power (refuted)

## OEIS source (retrieved 2026-10-21 with `oeis show A072995`)

```
NAME:     Least k > 0 such that the number of solutions to x^k == 1 (mod k)
          1 <= x <= k is equal to n, or 0 if no such k exists.
TERMS:    1,4,9,8,25,18,49,16,27,50,121,36,169,98,225,32,289,54,361,110,
          147,242,529,72,125,338,81,196,841,0,961,64,1089,578,1225,108,...
COMMENT:  a(30) doesn't exist: If N is even, and divisible by D different
          odd primes, but not divisible by 2^D, then a(N) doesn't exist.
          - _Don Reble_, Feb 23 2014
COMMENT:  Conjecture: a(n)=0 iff n/2 is in A061346.
          - _Robert G. Wilson v_, Feb 23 2014
COMMENT:  [n=420 seems to be a counterexample to the above conjecture.
          - _M. F. Hasler_, Feb 24 2014]
COMMENT:  (Wilson, Mar 05 2014) If n (an odd number) is {273, 399, 651,
          741, 777, 903, ...}, then a(n) = 0;
FORMULA:  First occurrence of n in A072994.
```

A061346 is "Odd numbers that are neither primes nor prime powers"
(`15, 21, 33, 35, 39, 45, ...`; `1` is not a term).

The conjecture line is not withdrawn by any later comment; Hasler's
bracketed comment only flags `n = 420` as a probable counterexample, and
Wilson's later observations implicitly contradict it as well.

## Status

This module **refutes** the conjecture (`conjecture_false`): `a(420) = 0`
(`a_four_hundred_twenty`) although `420 / 2 = 210` is even, hence not in
A061346.  The proof follows Reble's criterion with `N = 420 = 4 * 3 * 5 * 7`,
`D = 3`, `8 ∤ 420`: the solution set is the group `rootsOfUnity k (ZMod k)`;
Cauchy's theorem forces `2, 3, 5, 7 ∣ k`; the Chinese remainder theorem
splits off the `3`-, `5`- and `7`-primary components, each of which
contains the element `-1` of order `2`, so `8` divides the count.

The reverse implication of the conjecture is true and is proved here as
`a_eq_zero_of_A061346` (Reble's criterion with `D ≥ 2`, `4 ∤ n`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A072995Refutation

/-! ## Definition layer -/

/-- A072994(k): the number of `x` with `1 ≤ x ≤ k` and `x ^ k ≡ 1 (mod k)`. -/
def numSol (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun x => x ^ k ≡ 1 [MOD k])).card

/-- A072995: the least `k > 0` with exactly `n` solutions of `x ^ k ≡ 1 (mod k)`,
`1 ≤ x ≤ k`, or `0` if there is no such `k` (`sInf ∅ = 0` on `ℕ` realises the
OEIS convention). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | 0 < k ∧ numSol k = n}

/-- A061346: odd numbers that are neither primes nor prime powers.  Mathlib's
`IsPrimePow` covers primes, and `1 < m` excludes `1`, which is not a term. -/
def A061346 (m : ℕ) : Prop := Odd m ∧ 1 < m ∧ ¬ IsPrimePow m

/-- A finite criterion for `a n = k`: `k > 0` has `n` solutions and no smaller
positive `j` does. -/
theorem a_eq_of_forall {n k : ℕ} (hk : 0 < k) (hsol : numSol k = n)
    (hmin : ∀ j < k, 0 < j → numSol j ≠ n) : a n = k := by
  refine IsLeast.csInf_eq ⟨⟨hk, hsol⟩, fun j hj => ?_⟩
  by_contra hlt
  exact hmin j (Nat.lt_of_not_le hlt) hj.1 hj.2

/-! ## Ground truth -/

example : (List.range 12).map (fun k => numSol (k + 1)) = [1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4] := by
  decide

example : a 1 = 1 := a_eq_of_forall (by norm_num) (by decide) (by decide)
example : a 2 = 4 := a_eq_of_forall (by norm_num) (by decide) (by decide)
example : a 3 = 9 := a_eq_of_forall (by norm_num) (by decide) (by decide)
example : a 4 = 8 := a_eq_of_forall (by norm_num) (by decide) (by decide)
example : a 6 = 18 := a_eq_of_forall (by norm_num) (by decide) (by decide)

example : A061346 15 ∧ A061346 21 ∧ ¬ A061346 1 ∧ ¬ A061346 9 ∧ ¬ A061346 7 ∧
    ¬ A061346 30 := by
  unfold A061346
  decide +kernel

/-! ## Bridge to roots of unity -/

/-- Roots of unity as units correspond to elements with `x ^ j = 1`. -/
def rootsOfUnityEquivPowEqOne (M : Type*) [CommMonoid M] {j : ℕ} (hj : j ≠ 0) :
    rootsOfUnity j M ≃ {x : M // x ^ j = 1} where
  toFun u := ⟨((u : Mˣ) : M), by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity j _).mp u.2, Units.val_one]⟩
  invFun x := ⟨Units.ofPowEqOne x.1 j x.2 hj, (mem_rootsOfUnity j _).mpr (Units.pow_ofPowEqOne _ _)⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv x := rfl

/-- For `k ≥ 2`, A072994(k) counts the `x : ZMod k` with `x ^ k = 1`. -/
theorem numSol_eq_card {k : ℕ} (hk : 1 < k) :
    numSol k = Nat.card {x : ZMod k // x ^ k = 1} := by
  have : NeZero k := ⟨by omega⟩
  have : Fact (1 < k) := ⟨hk⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, numSol]
  refine Finset.card_bij (fun x _ => (x : ZMod k)) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hx.2
    push_cast at h
    exact h
  · intro x hx y hy hxy
    rw [Finset.mem_filter, Finset.mem_Icc] at hx hy
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mp hxy
    unfold Nat.ModEq at h
    rcases (show x < k ∨ x = k by omega) with hxk | hxk <;>
      rcases (show y < k ∨ y = k by omega) with hyk | hyk
    · rwa [Nat.mod_eq_of_lt hxk, Nat.mod_eq_of_lt hyk] at h
    · rw [Nat.mod_eq_of_lt hxk, hyk, Nat.mod_self] at h
      omega
    · rw [Nat.mod_eq_of_lt hyk, hxk, Nat.mod_self] at h
      omega
    · omega
  · intro z hz
    rw [Finset.mem_filter] at hz
    have hz0 : z.val ≠ 0 := by
      intro h0
      rw [ZMod.val_eq_zero] at h0
      rw [h0, zero_pow (by omega)] at hz
      exact zero_ne_one hz.2
    refine ⟨z.val, ?_, ZMod.natCast_zmod_val z⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hz0, (ZMod.val_lt z).le⟩, ?_⟩
    refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz.2

/-! ## Group-theoretic core -/

/-- The roots of unity of a product monoid are the product of the roots of unity. -/
theorem card_rootsOfUnity_prod (M N : Type*) [CommMonoid M] [CommMonoid N] (j : ℕ) :
    Nat.card (rootsOfUnity j (M × N)) =
      Nat.card (rootsOfUnity j M) * Nat.card (rootsOfUnity j N) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ?_
  refine (MulEquiv.prodUnits.toEquiv.subtypeEquiv (p := fun u => u ∈ rootsOfUnity j (M × N))
    (q := fun v : Mˣ × Nˣ => v.1 ∈ rootsOfUnity j M ∧ v.2 ∈ rootsOfUnity j N) ?_).trans
    Equiv.subtypeProdEquivProd
  intro u
  simp only [mem_rootsOfUnity, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← MulEquiv.map_eq_one_iff MulEquiv.prodUnits, map_pow, Prod.ext_iff, Prod.pow_fst,
    Prod.pow_snd, Prod.fst_one, Prod.snd_one]

/-- Chinese remainder theorem: the number of `j`-th roots of unity modulo `m * n`,
for coprime `m` and `n`, is the product of the counts modulo `m` and modulo `n`. -/
theorem card_rootsOfUnity_zmod_mul {m n : ℕ} (h : m.Coprime n) (j : ℕ) :
    Nat.card (rootsOfUnity j (ZMod (m * n))) =
      Nat.card (rootsOfUnity j (ZMod m)) * Nat.card (rootsOfUnity j (ZMod n)) := by
  rw [← card_rootsOfUnity_prod]
  exact Nat.card_congr
    (MulEquiv.restrictRootsOfUnity (ZMod.chineseRemainder h).toMulEquiv j).toEquiv

/-- For `n > 2` and even `j`, the element `-1` of order `2` is a `j`-th root of unity
modulo `n`, so the number of `j`-th roots of unity modulo `n` is even. -/
theorem two_dvd_card_rootsOfUnity_zmod {n j : ℕ} (hn : 2 < n) (hj : Even j) :
    2 ∣ Nat.card (rootsOfUnity j (ZMod n)) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hmem : (-1 : (ZMod n)ˣ) ∈ rootsOfUnity j (ZMod n) := by
    rw [mem_rootsOfUnity]
    exact hj.neg_one_pow
  have hord : orderOf (-1 : (ZMod n)ˣ) = 2 := by
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ZMod.ringChar_zmod_n,
      if_neg (by omega)]
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard _ hmem

/-- Cauchy's theorem: every prime dividing the number of `j`-th roots of unity of a
monoid with finitely many units divides `j`. -/
theorem prime_dvd_of_dvd_card_rootsOfUnity (M : Type*) [CommMonoid M] [Finite Mˣ] {j q : ℕ}
    (hq : q.Prime) (hdvd : q ∣ Nat.card (rootsOfUnity j M)) : q ∣ j := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity j M) q hdvd
  rw [← hx, ← Subgroup.orderOf_coe]
  exact orderOf_dvd_of_pow_eq_one ((mem_rootsOfUnity j _).mp x.2)

/-- Splitting off an odd prime: if `p` is an odd prime dividing `m ≠ 0` and `j` is
even, then twice the count modulo the `p`-free part of `m` divides the count
modulo `m`. -/
theorem two_mul_card_dvd_card_rootsOfUnity {p m j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : m ≠ 0) (hpm : p ∣ m) (hj : Even j) :
    2 * Nat.card (rootsOfUnity j (ZMod (m / p ^ m.factorization p))) ∣
      Nat.card (rootsOfUnity j (ZMod m)) := by
  have hcop : (p ^ m.factorization p).Coprime (m / p ^ m.factorization p) :=
    (Nat.coprime_ordCompl hp hm).pow_left _
  have hpos : 0 < m.factorization p := hp.factorization_pos_of_dvd hm hpm
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpow : 2 < p ^ m.factorization p :=
    lt_of_lt_of_le (by omega) (Nat.le_self_pow hpos.ne' p |>.trans' hp3)
  conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
  rw [card_rootsOfUnity_zmod_mul hcop]
  exact mul_dvd_mul (two_dvd_card_rootsOfUnity_zmod hpow hj) dvd_rfl

/-- For `k ≥ 2`, A072994(k) is the number of `k`-th roots of unity in `(ZMod k)ˣ`. -/
theorem numSol_eq_card_rootsOfUnity {k : ℕ} (hk : 1 < k) :
    numSol k = Nat.card (rootsOfUnity k (ZMod k)) := by
  rw [numSol_eq_card hk]
  exact (Nat.card_congr (rootsOfUnityEquivPowEqOne (ZMod k) (by omega))).symm

/-- No `k > 0` has exactly `420` solutions of `x ^ k ≡ 1 (mod k)`, `1 ≤ x ≤ k`. -/
theorem numSol_ne_four_hundred_twenty {k : ℕ} (hk : 0 < k) : numSol k ≠ 420 := by
  rcases (show k = 1 ∨ 1 < k by omega) with rfl | hk1
  · decide
  intro h420
  have : NeZero k := ⟨by omega⟩
  rw [numSol_eq_card_rootsOfUnity hk1] at h420
  have hdvd : ∀ q, q.Prime → q ∣ 420 → q ∣ k := fun q hq hq420 =>
    prime_dvd_of_dvd_card_rootsOfUnity (ZMod k) hq (h420 ▸ hq420)
  have h2 : 2 ∣ k := hdvd 2 Nat.prime_two (by norm_num)
  have h3 : 3 ∣ k := hdvd 3 Nat.prime_three (by norm_num)
  have h5 : 5 ∣ k := hdvd 5 Nat.prime_five (by norm_num)
  have h7 : 7 ∣ k := hdvd 7 (by norm_num) (by norm_num)
  have hk0 : k ≠ 0 := by omega
  have hev : Even k := even_iff_two_dvd.mpr h2
  have hm₁0 : k / 3 ^ k.factorization 3 ≠ 0 := (Nat.ordCompl_pos 3 hk0).ne'
  have h5m₁ : 5 ∣ k / 3 ^ k.factorization 3 := Nat.dvd_ordCompl_of_dvd_not_dvd h5 (by norm_num)
  have h7m₁ : 7 ∣ k / 3 ^ k.factorization 3 := Nat.dvd_ordCompl_of_dvd_not_dvd h7 (by norm_num)
  have hs₁ := two_mul_card_dvd_card_rootsOfUnity Nat.prime_three (by norm_num) hk0 h3 hev
  have hs₂ := two_mul_card_dvd_card_rootsOfUnity Nat.prime_five (by norm_num) hm₁0 h5m₁ hev
  have hs₃ := two_mul_card_dvd_card_rootsOfUnity (p := 7) (by norm_num) (by norm_num)
    (Nat.ordCompl_pos 5 hm₁0).ne' (Nat.dvd_ordCompl_of_dvd_not_dvd h7m₁ (by norm_num)) hev
  have h8 : 8 ∣ Nat.card (rootsOfUnity k (ZMod k)) :=
    (Dvd.intro _ (by ring)).trans
      ((mul_dvd_mul_left 2 ((mul_dvd_mul_left 2 hs₃).trans hs₂)).trans hs₁)
  rw [h420] at h8
  norm_num at h8

/-- If no `k > 0` has `n` solutions, then `a n = 0`. -/
theorem a_eq_zero_of_forall {n : ℕ} (h : ∀ k, 0 < k → numSol k ≠ n) : a n = 0 := by
  rw [a, Nat.sInf_eq_zero]
  right
  exact Set.eq_empty_iff_forall_notMem.mpr fun k hk => h k hk.1 hk.2

/-- **The counterexample.** `a(420) = 0`: no `k > 0` has exactly `420` solutions of
`x ^ k ≡ 1 (mod k)` with `1 ≤ x ≤ k`. -/
theorem a_four_hundred_twenty : a 420 = 0 :=
  a_eq_zero_of_forall fun _ hk => numSol_ne_four_hundred_twenty hk

/-! ## The conjecture -/

/-- **Wilson's conjecture (A072995, Robert G. Wilson v, Feb 23 2014).**

Verbatim: "Conjecture: a(n)=0 iff n/2 is in A061346."

"`n/2` is in A061346" is read as `n = 2 * m` with `m ∈ A061346`; for odd `n` the
quotient `n/2` is not an integer and so not a term.  The counterexample `n = 420`
is even, so it does not depend on this reading.  The range `1 ≤ n` is the entry's
offset. -/
def Conjecture : Prop :=
  ∀ n, 1 ≤ n → (a n = 0 ↔ ∃ m, n = 2 * m ∧ A061346 m)

/-- **Wilson's conjecture is false.**  Counterexample `n = 420` (flagged by
M. F. Hasler, Feb 24 2014): `a(420) = 0` by Reble's criterion (`420` is even,
divisible by the three odd primes `3, 5, 7`, and not by `2^3`), yet
`420 / 2 = 210` is even, hence not in A061346.  The author presumably intended
the zeros to be exactly the cases of Reble's criterion with `n ≡ 2 (mod 4)`;
the criterion also produces zeros with `4 ∣ n`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨m, hm, hodd, -, -⟩ := (hconj 420 (by norm_num)).mp a_four_hundred_twenty
  have hm210 : m = 210 := by omega
  rw [hm210] at hodd
  exact absurd hodd (by decide)

/-! ## The true half of the conjecture -/

/-- **The reverse implication holds.**  If `m` is an odd number that is neither
`1`, a prime, nor a prime power (A061346), then `a(2m) = 0` (Reble's criterion
with two odd primes and `4 ∤ 2m`). -/
theorem a_eq_zero_of_A061346 {m : ℕ} (hm : A061346 m) : a (2 * m) = 0 := by
  obtain ⟨hodd, h1m, hpp⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have hcard : 1 < m.primeFactors.card := by
    have hne : m.primeFactors.card ≠ 1 := fun h =>
      hpp (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
    have hpos : 0 < m.primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h1m)
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  have hpp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqp' : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpm)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqm)
  refine a_eq_zero_of_forall fun k hk hsol => ?_
  rcases (show k = 1 ∨ 1 < k by omega) with rfl | hk1
  · have h1 : numSol 1 = 1 := by decide
    omega
  have : NeZero k := ⟨by omega⟩
  rw [numSol_eq_card_rootsOfUnity hk1] at hsol
  have hdvd : ∀ r, r.Prime → r ∣ 2 * m → r ∣ k := fun r hr hrm =>
    prime_dvd_of_dvd_card_rootsOfUnity (ZMod k) hr (hsol ▸ hrm)
  have hk0 : k ≠ 0 := by omega
  have hev : Even k := even_iff_two_dvd.mpr (hdvd 2 Nat.prime_two (dvd_mul_right 2 m))
  have hpk : p ∣ k := hdvd p hpp' (hpm.mul_left 2)
  have hqk : q ∣ k := hdvd q hqp' (hqm.mul_left 2)
  have hs₁ := two_mul_card_dvd_card_rootsOfUnity hpp' hp2 hk0 hpk hev
  have hs₂ := two_mul_card_dvd_card_rootsOfUnity hqp' hq2 (Nat.ordCompl_pos p hk0).ne'
    (Nat.dvd_ordCompl_of_dvd_not_dvd hqk
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hpp' hqp').mp h))) hev
  have h4 : 4 ∣ Nat.card (rootsOfUnity k (ZMod k)) :=
    (Dvd.intro _ (by ring)).trans ((mul_dvd_mul_left 2 hs₂).trans hs₁)
  rw [hsol] at h4
  obtain ⟨r, hr⟩ := hodd
  omega

end Candidates.A072995Refutation
