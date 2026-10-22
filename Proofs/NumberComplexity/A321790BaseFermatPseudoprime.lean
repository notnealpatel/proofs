/-
# A321790 — Ordowski: least non-liar of a semiprime base-2 pseudoprime lies below its least prime factor

Thomas Ordowski's conjecture in OEIS A321790 says that the least base
`a > 2` which is not a Fermat liar for a semiprime base-2 pseudoprime lies
below its least prime factor. The stronger statement below gives such a
non-liar in `[2,p-1]` for all primes `3 ≤ p ≤ q`, modulo `pq`.

* `p < q`: if every `a ∈ [1, p-1]` were a liar mod `pq`, then in `ZMod q` the
  `p - 1` residues `1, …, p-1` and also `-1 = q - 1` (as `p - 1` is even) would
  be `p` distinct roots of `X^(p-1) - 1`, since `pq - 1 = (q-1)p + (p-1)`.
* `p = q`: `(p-1)^(p^2-1) ≡ 1 + p (mod p^2)`.

Since `2` is a liar for a base-2 pseudoprime, the non-liar is at least `3`.
-/
import Mathlib.NumberTheory.FermatPsp
import Mathlib.Data.Nat.Nth
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace Candidates.A321790BaseFermatPseudoprime

/-! ## Definitions

* Membership in A001567 ("Fermat pseudoprimes to base 2") is Mathlib's
  `Nat.FermatPsp k 2`, unfolding to `k ∣ 2 ^ (k - 1) - 1 ∧ ¬ k.Prime ∧ 1 < k`.
* `A001567 n` is the `n`-th such number, 1-indexed as in the OEIS.
* `leastNonLiar k` is the least `a > 2` with `a ^ (k - 1) ≢ 1 (mod k)`, and
  `a321790 n = leastNonLiar (A001567 n)`. -/

/-- The `n`-th Fermat pseudoprime to base 2 (OEIS A001567, offset 1:
`A001567 1 = 341`). -/
noncomputable def A001567 (n : ℕ) : ℕ :=
  Nat.nth (fun k => Nat.FermatPsp k 2) (n - 1)

/-- The smallest base `a > 2` with `a ^ (k - 1) ≢ 1 (mod k)` (`0` if there is
none; for every `k ≥ 3` the base `a = k` qualifies, so the junk value never
occurs on A001567). -/
noncomputable def leastNonLiar (k : ℕ) : ℕ :=
  sInf {a : ℕ | 2 < a ∧ ¬ a ^ (k - 1) ≡ 1 [MOD k]}

/-- OEIS A321790: `a(n) = leastNonLiar (A001567 n)`. -/
noncomputable def a321790 (n : ℕ) : ℕ :=
  leastNonLiar (A001567 n)

/-- `leastNonLiar k` is at most any base `a > 2` that is a non-liar mod `k`. -/
theorem leastNonLiar_le {k a : ℕ} (ha : 2 < a) (hna : ¬ a ^ (k - 1) ≡ 1 [MOD k]) :
    leastNonLiar k ≤ a :=
  Nat.sInf_le ⟨ha, hna⟩

/-- Characterisation used for the examples: if `a > 2` is a non-liar
mod `k` and every `b` with `2 < b < a` is a liar, then `leastNonLiar k = a`. -/
theorem leastNonLiar_eq_of {k a : ℕ} (ha : 2 < a) (hna : ¬ a ^ (k - 1) ≡ 1 [MOD k])
    (hb : ∀ b, 2 < b → b < a → b ^ (k - 1) ≡ 1 [MOD k]) : leastNonLiar k = a := by
  refine le_antisymm (leastNonLiar_le ha hna) ?_
  unfold leastNonLiar
  refine le_csInf ⟨a, ha, hna⟩ ?_
  rintro b ⟨hb2, hnb⟩
  by_contra hlt
  exact hnb (hb b hb2 (Nat.lt_of_not_le hlt))

/-! ## Examples against the first terms

`A001567` begins `341, 561, 645, 1105, 1387, 1729`, and A321790 begins
`3, 3, 3, 5, 3, 7`. -/

/-- `341` is the first Fermat pseudoprime to base 2, so `A001567 1 = 341`. -/
theorem A001567_one : A001567 1 = 341 := by
  have h341 : Nat.FermatPsp 341 2 := by
    refine ⟨?_, by norm_num, by norm_num⟩
    unfold Nat.ProbablePrime
    decide +kernel
  have hbelow : ∀ k < 341, ¬ Nat.FermatPsp k 2 := by
    unfold Nat.FermatPsp Nat.ProbablePrime
    decide +kernel
  unfold A001567
  rw [Nat.sub_self, Nat.nth_zero]
  refine le_antisymm (Nat.sInf_le h341) (le_csInf ⟨341, h341⟩ ?_)
  intro k hk
  by_contra hlt
  exact hbelow k (Nat.lt_of_not_le hlt) hk

example : leastNonLiar 341 = 3 :=
  leastNonLiar_eq_of (by norm_num) (by decide +kernel) (by intro b hb hb'; omega)

example : leastNonLiar 561 = 3 :=
  leastNonLiar_eq_of (by norm_num) (by decide +kernel) (by intro b hb hb'; omega)

example : leastNonLiar 645 = 3 :=
  leastNonLiar_eq_of (by norm_num) (by decide +kernel) (by intro b hb hb'; omega)

example : leastNonLiar 1105 = 5 :=
  leastNonLiar_eq_of (by norm_num) (by decide +kernel)
    (by intro b hb hb'; interval_cases b <;> decide +kernel)

example : leastNonLiar 1387 = 3 :=
  leastNonLiar_eq_of (by norm_num) (by decide +kernel) (by intro b hb hb'; omega)

example : leastNonLiar 1729 = 7 :=
  leastNonLiar_eq_of (by norm_num) (by decide +kernel)
    (by intro b hb hb'; interval_cases b <;> decide +kernel)

example : a321790 1 = 3 := by
  rw [a321790, A001567_one]
  exact leastNonLiar_eq_of (by norm_num) (by decide +kernel) (by intro b hb hb'; omega)

/-! ## The mathematics -/

/-- In a commutative ring, if `x * x = 0` then `(x - 1) ^ n = (-1) ^ n * (1 - n x)`. -/
theorem sub_one_pow_of_mul_self_eq_zero {R : Type*} [CommRing R] (x : R) (hx : x * x = 0)
    (n : ℕ) : (x - 1) ^ n = (-1) ^ n * (1 - n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    push_cast
    linear_combination (-(-1) ^ n * (n : R)) * hx

/-- Square case: for a prime `p ≥ 3`, `p - 1` is not a Fermat liar mod `p ^ 2`,
since `(p - 1) ^ (p ^ 2 - 1) ≡ 1 + p (mod p ^ 2)`. -/
theorem not_sub_one_pow_modEq_one_of_sq {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ¬ (p - 1) ^ (p * p - 1) ≡ 1 [MOD p * p] := by
  intro h
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  set x : ZMod (p * p) := (p : ZMod (p * p)) with hxdef
  have hxx : x * x = 0 := by rw [hxdef, ← Nat.cast_mul, ZMod.natCast_self]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : Even (p * p - 1) := Nat.Odd.sub_odd (hodd.mul hodd) odd_one
  have hpp : 1 ≤ p * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcast : (((p * p - 1 : ℕ)) : ZMod (p * p)) = -1 := by
    rw [Nat.cast_sub hpp, ZMod.natCast_self]
    simp
  rw [Nat.cast_pow, Nat.cast_sub (by omega), Nat.cast_one, ← hxdef,
    sub_one_pow_of_mul_self_eq_zero x hxx, heven.neg_one_pow, one_mul, hcast] at hz
  have hx0 : x = 0 := by linear_combination hz
  rw [hxdef, ZMod.natCast_eq_zero_iff] at hx0
  have hle := Nat.le_of_dvd hp.pos hx0
  nlinarith

open Polynomial in
/-- Distinct-primes case: for primes `3 ≤ p < q`, some `a ∈ [2, p - 1]` satisfies
`a ^ (p q - 1) ≢ 1 (mod p q)`.  Otherwise `1, …, p - 1` and `q - 1 = -1` would be
`p` distinct roots of `X ^ (p - 1) - 1` in `ZMod q`. -/
theorem exists_nonliar_lt_of_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p)
    (hpq : p < q) : ∃ a, 2 ≤ a ∧ a < p ∧ ¬ a ^ (p * q - 1) ≡ 1 [MOD p * q] := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hall
  push Not at hall
  -- every element of `S = [1, p) ∪ {q - 1}` is a `(p-1)`-th root of unity mod `q`
  have hroot : ∀ a ∈ Finset.Ico 1 p ∪ {q - 1}, ((a : ℕ) : ZMod q) ^ (p - 1) = 1 := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨ha1, hap⟩ := Finset.mem_Ico.mp ha
      have hne : ((a : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have hqa := Nat.le_of_dvd (by omega) hdvd
        omega
      have hmodq : ((a : ℕ) : ZMod q) ^ (p * q - 1) = 1 := by
        rcases Nat.lt_or_ge a 2 with h | h
        · have ha1' : a = 1 := by omega
          subst ha1'
          simp
        · have hm : a ^ (p * q - 1) ≡ 1 [MOD q] := (hall a h hap).of_mul_left p
          simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
      have hsplit : p * q - 1 = (q - 1) * p + (p - 1) := by
        have hq1 : 1 ≤ q := hq.one_lt.le
        have hp1 : 1 ≤ p := by omega
        zify [hq1, hp1,
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega) : p * q ≠ 0)]
        ring
      rw [hsplit, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hne, one_pow, one_mul]
        at hmodq
      exact hmodq
    · rw [Finset.mem_singleton.mp ha]
      have hcast : ((q - 1 : ℕ) : ZMod q) = -1 := by
        rw [Nat.cast_sub hq.one_lt.le, ZMod.natCast_self]
        simp
      have heven : Even (p - 1) := Nat.Odd.sub_odd (hp.odd_of_ne_two (by omega)) odd_one
      rw [hcast, heven.neg_one_pow]
  have hsub : (Finset.Ico 1 p ∪ {q - 1}).image (fun a : ℕ => (a : ZMod q)) ⊆
      nthRootsFinset (p - 1) (1 : ZMod q) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_nthRootsFinset (by omega)]
    exact hroot a ha
  -- the residues of `S` are pairwise distinct, all elements being `< q`
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod q)) (Finset.Ico 1 p ∪ {q - 1} : Finset ℕ) := by
    intro a ha b hb hab
    have hlt : ∀ c ∈ (Finset.Ico 1 p ∪ {q - 1} : Finset ℕ), c < q := by
      intro c hc
      rcases Finset.mem_union.mp hc with hc | hc
      · have hcp := (Finset.mem_Ico.mp hc).2
        omega
      · rw [Finset.mem_singleton.mp hc]
        have hq1 := hq.one_lt
        omega
    have hmod := (ZMod.natCast_eq_natCast_iff' a b q).mp hab
    rwa [Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb)] at hmod
  have hcard : (Finset.Ico 1 p ∪ {q - 1}).card = p := by
    rw [Finset.card_union_of_disjoint]
    · rw [Nat.card_Ico, Finset.card_singleton]
      omega
    · rw [Finset.disjoint_singleton_right, Finset.mem_Ico]
      omega
  have hle : p ≤ p - 1 := by
    calc p = ((Finset.Ico 1 p ∪ {q - 1}).image (fun a : ℕ => (a : ZMod q))).card := by
          rw [Finset.card_image_of_injOn hinj, hcard]
      _ ≤ (nthRootsFinset (p - 1) (1 : ZMod q)).card := Finset.card_le_card hsub
      _ ≤ (nthRoots (p - 1) (1 : ZMod q)).card := by
          rw [nthRootsFinset_def]
          exact Multiset.toFinset_card_le _
      _ ≤ p - 1 := card_nthRoots _ _
  omega

/-- **Stronger statement.** For primes `3 ≤ p ≤ q`, some base `a` with
`2 ≤ a < p` is not a Fermat liar mod `p q`. -/
theorem exists_nonliar_lt_of_prime_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p)
    (hpq : p ≤ q) : ∃ a, 2 ≤ a ∧ a < p ∧ ¬ a ^ (p * q - 1) ≡ 1 [MOD p * q] := by
  rcases hpq.lt_or_eq with hlt | heq
  · exact exists_nonliar_lt_of_prime_lt hp hq hp3 hlt
  · subst heq
    exact ⟨p - 1, by omega, by omega, not_sub_one_pow_modEq_one_of_sq hp hp3⟩

/-- A base-2 Fermat pseudoprime `k` makes `2` a Fermat liar: `2 ^ (k - 1) ≡ 1 (mod k)`. -/
theorem two_pow_modEq_one_of_fermatPsp {k : ℕ} (hk : Nat.FermatPsp k 2) :
    2 ^ (k - 1) ≡ 1 [MOD k] :=
  ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr hk.1).symm

/-! ## The conjecture -/

/-- **Ordowski's conjecture (A321790, Thomas Ordowski), in the
pseudoprime form.**

If `k` is a Fermat pseudoprime to base 2 and `k = p * q` with `p`, `q` prime,
then the least base `a > 2` with `a ^ (k - 1) ≢ 1 (mod k)` is smaller than the
least prime factor `k.minFac` of `k`.  The square case `p = q` is included
(e.g. the Wieferich squares `1093 ^ 2`, `3511 ^ 2`). -/
theorem leastNonLiar_lt_minFac {k p q : ℕ} (hk : Nat.FermatPsp k 2) (hp : p.Prime)
    (hq : q.Prime) (hkpq : k = p * q) : leastNonLiar k < k.minFac := by
  wlog hpq : p ≤ q generalizing p q
  · exact this hq hp (by rw [hkpq, Nat.mul_comm]) (by omega)
  have h2 := two_pow_modEq_one_of_fermatPsp hk
  have hk1 : 1 < k := hk.2.2
  -- `p ≠ 2`: an even `k > 1` cannot satisfy `2 ^ (k - 1) ≡ 1 (mod k)`
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hdvd : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
    have hmod := (Nat.ModEq.of_mul_right q (hkpq ▸ h2) : 2 ^ (k - 1) ≡ 1 [MOD 2])
    have h0 : 2 ^ (k - 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    unfold Nat.ModEq at hmod
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨a, ha2, hap, hna⟩ := exists_nonliar_lt_of_prime_le hp hq hp3 hpq
  rw [← hkpq] at hna
  have ha3 : 2 < a := by
    rcases ha2.lt_or_eq with h | h
    · exact h
    · subst h
      exact absurd h2 hna
  have hmin : k.minFac = p := by
    have hfac : k.minFac.Prime := Nat.minFac_prime (by omega)
    have hle : k.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le (hkpq ▸ dvd_mul_right p q)
    have hdvd : k.minFac ∣ p * q := hkpq ▸ Nat.minFac_dvd k
    rcases (Nat.Prime.dvd_mul hfac).mp hdvd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hfac hp).mp h
    · have hfq := (Nat.prime_dvd_prime_iff_eq hfac hq).mp h
      omega
  rw [hmin]
  exact lt_of_le_of_lt (leastNonLiar_le ha3 hna) hap

/-- Every `A001567 n` is a Fermat pseudoprime to base 2 (the base-2 pseudoprimes
are infinite, so `Nat.nth` never takes its junk value). -/
theorem fermatPsp_A001567 (n : ℕ) : Nat.FermatPsp (A001567 n) 2 := by
  have hinf : (Set.ofPred fun k => Nat.FermatPsp k 2).Infinite :=
    Nat.frequently_atTop_iff_infinite.mp (Nat.frequently_atTop_fermatPsp (by norm_num))
  exact Nat.nth_mem_of_infinite hinf (n - 1)

/-- **Ordowski's conjecture (A321790, Thomas Ordowski), OEIS-indexed.**

If the `n`-th base-2 Fermat pseudoprime `k = A001567 n` is a product of two
primes, then `a(n) = a321790 n < lpf(k) = k.minFac`.  (`n = 0` merely aliases
`n = 1` through the truncated offset shift `n - 1`.) -/
theorem a321790_lt_minFac (n : ℕ)
    (hsemi : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ A001567 n = p * q) :
    a321790 n < (A001567 n).minFac := by
  obtain ⟨p, q, hp, hq, hkpq⟩ := hsemi
  exact leastNonLiar_lt_minFac (fermatPsp_A001567 n) hp hq hkpq

/-- Non-vacuity: `341 = 11 * 31 = A001567 1` is a semiprime base-2 pseudoprime,
so the hypothesis of `a321790_lt_minFac` is satisfied at `n = 1`
(and there `a(1) = 3 < 11`). -/
example : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ A001567 1 = p * q :=
  ⟨11, 31, by norm_num, by norm_num, by rw [A001567_one]⟩

end Candidates.A321790BaseFermatPseudoprime
