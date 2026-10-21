/-
# A257743 — Shevelev: the odd-part `3x+1` stopping index is unbounded

## OEIS source (`oeis show A257743`, live entry checked 2026-10-21)

```
NAME:     Let n'= odd part of n. If n' is 1 or prime, then a(n)=1; otherwise
          a(n) is 1+ the number of times the map x -> (3*x+1)' must be applied
          to n' in order to reach 1 or a prime.
TERMS:    1,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,2,1,1,1,2,1,2,1,1,2,1,1,3,1,
          2,2,1,1,2,1,1,2,1,1,2,1,1,1,2,2,3,1,1,2,2,1,2,1,1,2,1,1,8,1,3,3,1,1,
          2,2,1,2,1,1,2,1,2,2,1,1,2,1,1,2,2,1,2
KEYWORDS: nonn
OFFSET:   1
AUTHOR:   Vladimir Shevelev, May 07 2015
          (more terms from Peter J. C. Moses, May 07 2015)
COMMENT (the conjecture; unsigned, hence the author's, May 07 2015):
  Conjecture: for every N>0 there exists n=n(N) such that a(n)>N.
```

Retrieved 2026-10-21.

## Status

Triage: open (no proof in the entry; only a b-file).  This module proves the
conjecture in the strong form "for every `N` there is `n > 0` such that none
of the iterates `T^j(n')`, `0 ≤ j ≤ N`, is `1` or prime", which does not
presuppose that any orbit ever reaches `1` or a prime.

## Proof idea

`1` is a fixed point of `T x = (3x+1)'`.  If `2j < E` then
`T^j(1 + 2^E t) = 1 + 3^j 2^(E-2j) t`, because
`3 (1 + 3^j 2^(e+2) t) + 1 = 4 (1 + 3^(j+1) 2^e t)` with the bracket odd when
`e ≥ 1`.  For `E = 2N+1`, a Chinese-remainder construction (by induction,
adding one fresh prime `p ≥ 5` per step) yields a residue class of `t` such
that each `1 + 3^j 2^(E-2j) t` is a proper multiple of a prime.

## Definitional fidelity

`oddPart n = n / 2 ^ padicValNat 2 n` mirrors Mathematica's
`#/2^IntegerExponent[#,2]&` in the entry's program.  The value `a n` is in
`ℕ∞`: it is `1 + (least k with T^k(n') ∈ {1} ∪ primes)`, and `⊤` when no such
`k` exists (the entry's programs do not halt in that case).  The bridge
`natCast_lt_a_iff` shows `N < a n` is exactly "no iterate `T^j(n')`, `j < N`,
is `1` or prime", so the `⊤` convention never affects the claim.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A257743OddPartThere

/-! ## Definitions -/

/-- The odd part `n'` of `n`: `n` divided by the largest power of `2` dividing
it (`oddPart 0 = 0`). -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ padicValNat 2 n

/-- The map `x ↦ (3x+1)'` of A257743. -/
def T (x : ℕ) : ℕ := oddPart (3 * x + 1)

/-- The stopping condition of A257743: `x` is `1` or prime. -/
def Stops (x : ℕ) : Prop := x = 1 ∨ x.Prime

/-- A257743 as an `ℕ∞`-valued function: `a n = k + 1` for the least `k` such that
`T^k(n')` is `1` or prime, and `a n = ⊤` if there is no such `k`. -/
noncomputable def a (n : ℕ) : ℕ∞ :=
  ⨅ k : {k : ℕ // Stops (T^[k] (oddPart n))}, ((k : ℕ) : ℕ∞) + 1

/-! ## Basic lemmas -/

/-- The odd part of `2^k * m` is `m` when `m` is odd. -/
theorem oddPart_two_pow_mul {k m : ℕ} (hm : Odd m) : oddPart (2 ^ k * m) = m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hm)
  have hv : padicValNat 2 (2 ^ k * m) = k := by
    rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm.not_two_dvd_nat, add_zero]
  unfold oddPart
  rw [hv, Nat.mul_div_cancel_left _ (by positivity)]

/-- An odd number is its own odd part. -/
theorem oddPart_of_odd {m : ℕ} (hm : Odd m) : oddPart m = m := by
  simpa using oddPart_two_pow_mul (k := 0) hm

/-- Evaluation helper: if `3x+1 = 2^k * m` with `m` odd then `T x = m`. -/
theorem T_eq {x k m : ℕ} (h : 3 * x + 1 = 2 ^ k * m) (hm : Odd m) : T x = m := by
  unfold T
  rw [h, oddPart_two_pow_mul hm]

/-- Closed form of the iterates on `1 + 2^E t`: for `2j < E`,
`T^j(1 + 2^E t) = 1 + 3^j 2^(E-2j) t`. -/
theorem T_iterate_one_add {E t : ℕ} :
    ∀ j : ℕ, 2 * j < E → T^[j] (1 + 2 ^ E * t) = 1 + 3 ^ j * 2 ^ (E - 2 * j) * t
  | 0, _ => by simp
  | j + 1, hj => by
    rw [Function.iterate_succ_apply', T_iterate_one_add j (by omega)]
    set e := E - 2 * (j + 1) with he
    have hE : E - 2 * j = e + 2 := by omega
    have he1 : e ≠ 0 := by omega
    have hodd : Odd (1 + 3 ^ (j + 1) * 2 ^ e * t) := by
      have h2e : Even (2 ^ e) := Nat.even_pow.mpr ⟨even_two, he1⟩
      exact ((h2e.mul_left (3 ^ (j + 1))).mul_right t).one_add
    apply T_eq (k := 2) _ hodd
    rw [hE]
    ring

/-- Solving a linear congruence modulo a prime: if `p ∤ c` there is `s` with
`p ∣ b + c * s`. -/
theorem exists_dvd_add_mul {p : ℕ} (hp : p.Prime) {c : ℕ} (hc : ¬ p ∣ c) (b : ℕ) :
    ∃ s : ℕ, p ∣ b + c * s := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc0 : (c : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  refine ⟨(-(b : ZMod p) * (c : ZMod p)⁻¹).val, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

/-- Chinese-remainder step, iterated: given multipliers `c j` with no prime
factor `≥ 5`, there is a residue class `t + M s` (`M > 0`) such that for every
`s` and every `j < K`, `1 + c j * (t + M s)` has a prime divisor `p ≤ M`. -/
theorem exists_residue_class (c : ℕ → ℕ)
    (hc : ∀ j p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ c j) :
    ∀ K : ℕ, ∃ M t : ℕ, 0 < M ∧ ∀ s j : ℕ, j < K →
      ∃ p : ℕ, p.Prime ∧ p ≤ M ∧ p ∣ 1 + c j * (t + M * s)
  | 0 => ⟨1, 0, one_pos, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | K + 1 => by
    obtain ⟨M, t, hM, hcls⟩ := exists_residue_class c hc K
    obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 5)
    have hpc : ¬ p ∣ c K * M := by
      rw [hp.dvd_mul]
      rintro (h | h)
      · exact hc K p hp (by omega) h
      · exact absurd (Nat.le_of_dvd hM h) (by omega)
    obtain ⟨s₀, hs₀⟩ := exists_dvd_add_mul hp hpc (1 + c K * t)
    refine ⟨M * p, t + M * s₀, Nat.mul_pos hM hp.pos, fun s j hj => ?_⟩
    have hshift : t + M * s₀ + M * p * s = t + M * (s₀ + p * s) := by ring
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjK | rfl
    · obtain ⟨q, hq, hqM, hqd⟩ := hcls (s₀ + p * s) j hjK
      refine ⟨q, hq, hqM.trans (Nat.le_mul_of_pos_right M hp.pos), ?_⟩
      rwa [hshift]
    · refine ⟨p, hp, Nat.le_mul_of_pos_left p hM, ?_⟩
      have hsplit : 1 + c j * (t + M * s₀ + M * p * s)
          = (1 + c j * t + c j * M * s₀) + p * (c j * M * s) := by ring
      rw [hsplit]
      refine dvd_add ?_ (dvd_mul_right p _)
      simpa [mul_assoc] using hs₀

/-! ## The conjecture -/

/-- **A257743, strong form.**  For every `N` there is `n > 0` such that none of
the iterates `T^j(n')`, `0 ≤ j ≤ N`, of `T x = (3x+1)'` on the odd part `n'`
of `n` is `1` or prime.  (Triage formulation of Shevelev's conjecture, which
does not presuppose that orbits reach `1` or a prime.) -/
theorem exists_iterates_not_one_not_prime (N : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ j ≤ N, T^[j] (oddPart n) ≠ 1 ∧ ¬ (T^[j] (oddPart n)).Prime := by
  set E := 2 * N + 1 with hE
  let c : ℕ → ℕ := fun j => 3 ^ j * 2 ^ (E - 2 * j)
  have hc : ∀ j p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ c j := by
    intro j p hp hp5 hdvd
    rcases hp.dvd_mul.mp hdvd with h3 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)) (by omega)
  have hcpos : ∀ j, 0 < c j := fun j => by positivity
  obtain ⟨M, t, hM, hcls⟩ := exists_residue_class c hc (N + 1)
  have hodd : Odd (1 + 2 ^ E * (t + M * 1)) := by
    have h2E : Even (2 ^ E) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact (h2E.mul_right _).one_add
  refine ⟨1 + 2 ^ E * (t + M * 1), by omega, fun j hj => ?_⟩
  have hval : T^[j] (oddPart (1 + 2 ^ E * (t + M * 1))) = 1 + c j * (t + M * 1) := by
    rw [oddPart_of_odd hodd, T_iterate_one_add j (by omega)]
  obtain ⟨p, hp, hpM, hpd⟩ := hcls 1 j (by omega)
  have hbig : p < 1 + c j * (t + M * 1) := by
    have hge : M ≤ c j * (t + M * 1) :=
      calc M ≤ t + M * 1 := by omega
        _ ≤ c j * (t + M * 1) := Nat.le_mul_of_pos_left _ (hcpos j)
    omega
  rw [hval]
  refine ⟨by have := hp.two_le; omega, fun hprime => ?_⟩
  rcases hprime.eq_one_or_self_of_dvd p hpd with h1 | hself
  · exact hp.one_lt.ne' h1
  · exact hbig.ne hself

/-- Bridge: `N < a n` holds exactly when no iterate `T^j(n')` with `j < N` is
`1` or prime. -/
theorem natCast_lt_a_iff (N n : ℕ) :
    (N : ℕ∞) < a n ↔ ∀ j < N, ¬ Stops (T^[j] (oddPart n)) := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top N), a, le_iInf_iff]
  constructor
  · intro h j hj hstop
    have hle : N + 1 ≤ j + 1 := by exact_mod_cast h ⟨j, hstop⟩
    omega
  · rintro h ⟨k, hk⟩
    have hNk : N ≤ k := by
      by_contra hlt
      exact h k (by omega) hk
    exact_mod_cast Nat.add_le_add_right hNk 1

/-- Evaluation of `a`: if `T^k(n')` is the first iterate that is `1` or prime,
then `a n = k + 1`. -/
theorem a_eq_of_stops {n k : ℕ} (hk : Stops (T^[k] (oddPart n)))
    (hmin : ∀ j < k, ¬ Stops (T^[j] (oddPart n))) : a n = (k : ℕ∞) + 1 := by
  rw [a]
  refine le_antisymm
    (iInf_le (fun k' : {k : ℕ // Stops (T^[k] (oddPart n))} => ((k' : ℕ) : ℕ∞) + 1)
      ⟨k, hk⟩) ?_
  rw [le_iInf_iff]
  rintro ⟨k', hk'⟩
  have hkk : k ≤ k' := by
    by_contra hlt
    exact hmin k' (by omega) hk'
  exact_mod_cast Nat.add_le_add_right hkk 1

/-- **A257743 conjecture (Vladimir Shevelev, May 07 2015).**  Verbatim:
"Conjecture: for every N>0 there exists n=n(N) such that a(n)>N."
Here `a n : ℕ∞` is A257743 (with value `⊤` if the orbit never reaches `1` or a
prime); the witness `n` is positive, matching the entry's offset 1. -/
theorem conjecture (N : ℕ) (_hN : 0 < N) : ∃ n : ℕ, 0 < n ∧ (N : ℕ∞) < a n := by
  obtain ⟨n, hn, hit⟩ := exists_iterates_not_one_not_prime N
  refine ⟨n, hn, (natCast_lt_a_iff N n).mpr fun j hj hstop => ?_⟩
  obtain ⟨hne1, hnp⟩ := hit j hj.le
  rcases hstop with h1 | hpr
  · exact hne1 h1
  · exact hnp hpr

/-! ## Ground truth against the listed terms -/

/-- `a 1 = 1` (first listed term). -/
example : a 1 = 1 := by
  have h : a 1 = ((0 : ℕ) : ℕ∞) + 1 :=
    a_eq_of_stops (by left; simp [oddPart_of_odd (m := 1) odd_one]) (fun j hj => absurd hj (by omega))
  simpa using h

/-- `a 8 = 1` (eighth listed term; `8' = 1`). -/
example : a 8 = 1 := by
  have h8 : oddPart 8 = 1 := oddPart_two_pow_mul (k := 3) odd_one
  have h : a 8 = ((0 : ℕ) : ℕ∞) + 1 :=
    a_eq_of_stops (by left; simp [h8]) (fun j hj => absurd hj (by omega))
  simpa using h

/-- `a 9 = 2` (ninth listed term: `9 → 7`). -/
example : a 9 = 2 := by
  have h0 : oddPart 9 = 9 := oddPart_of_odd (by decide)
  have h1 : T 9 = 7 := T_eq (k := 2) (by norm_num) (by decide)
  have h : a 9 = ((1 : ℕ) : ℕ∞) + 1 := by
    refine a_eq_of_stops ?_ fun j hj => ?_
    · right; simp only [Function.iterate_one, h0, h1]; norm_num
    · obtain rfl : j = 0 := by omega
      simp only [Function.iterate_zero_apply, h0, Stops]; norm_num
  rw [h]; rfl

/-- `a 63 = 8` (63rd listed term: `63 → 95 → 143 → 215 → 323 → 485 → 91 → 137`). -/
example : a 63 = 8 := by
  have h0 : oddPart 63 = 63 := oddPart_of_odd (by decide)
  have h1 : T 63 = 95 := T_eq (k := 1) (by norm_num) (by decide)
  have h2 : T 95 = 143 := T_eq (k := 1) (by norm_num) (by decide)
  have h3 : T 143 = 215 := T_eq (k := 1) (by norm_num) (by decide)
  have h4 : T 215 = 323 := T_eq (k := 1) (by norm_num) (by decide)
  have h5 : T 323 = 485 := T_eq (k := 1) (by norm_num) (by decide)
  have h6 : T 485 = 91 := T_eq (k := 4) (by norm_num) (by decide)
  have h7 : T 91 = 137 := T_eq (k := 1) (by norm_num) (by decide)
  have h : a 63 = ((7 : ℕ) : ℕ∞) + 1 := by
    refine a_eq_of_stops ?_ fun j hj => ?_
    · right
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
        h0, h1, h2, h3, h4, h5, h6, h7]
      norm_num
    · interval_cases j <;>
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
          h0, h1, h2, h3, h4, h5, h6, Stops] <;> norm_num
  rw [h]; rfl

/-- Non-vacuity of the iterate formula: `T^2(1 + 2^5) = T^2(33) = 1 + 9 * 2 = 19`. -/
example : T^[2] (1 + 2 ^ 5 * 1) = 19 := by
  rw [T_iterate_one_add 2 (by norm_num)]
  norm_num

end Candidates.A257743OddPartThere
