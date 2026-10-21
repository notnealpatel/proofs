/-
# A166102 — Karttunen: the odd Jacobi-symbol conjecture

## OEIS source (pulled with `oeis show A166102` and the live `/internal` page, 2026-10-21)

```
A166102  NAME:     Odd numbers k such that A166100((k-1)/2)/k is not an integer.
         TERMS:    3,27,75,243,363,675,867,1587,1875,2187,2523,3267,5043,6075,
                   6627,7803,8427,9075,10443,14283,15123,16875,19683,...
         AUTHOR:   _Antti Karttunen_, Oct 13 2009
         COMMENT:  Conjecture: a(n) = 3*A166103(n). (Checked for terms a(1)-a(92).)
         KEYWORDS: nonn
A166100  NAME:     Sum of those positive i <= 2n+1, for which J(i,2n+1)=+1.
                   Here J(i,k) is the Jacobi symbol.
         TERMS:    1,1,5,7,27,22,39,15,68,76,63,92,250,...
A166103  NAME:     Squares of A166104.
         TERMS:    1,9,25,81,121,225,289,529,625,729,841,1089,...
         COMMENT:  Conjecture: a(n)=A166102(n)/3. (Checked for terms a(1)-a(92).)
A166104  NAME:     Natural numbers whose prime factors are all congruent to 3 or 5
                   mod 6 (i.e., are in the sequence A045410).
         TERMS:    1,3,5,9,11,15,17,23,25,27,29,33,41,45,...
         COMMENT:  1 is included, as it has no prime factors at all.
```

The conjecture line carries no separate signature; it is part of Karttunen's
original Oct 13 2009 submission.

## Status

Triage: open (no proof in the entry or the literature found by the triage;
the entry checked 92 terms, the triage checked every odd `k ≤ 40001`).  This
module re-validated the characterisation for the 400 odd `k` in
`[40003, 40801]` and for `k = 3m²`, `m` odd in `[117, 259]` (up to `201243`),
with no mismatch, and then **proves it in full** (`a166102_conjecture`,
`a166102_eq_three_mul_a166103`).

## Proof outline

Write `χ(i) = J(i,k)` for odd `k`, `S = ∑_{i<k} χ(i) i` and `S⁺ = A166100((k-1)/2)`.

1. `2 S⁺ = ∑ χ(i)² i + ∑ χ(i) i` and reflecting `i ↦ k - i` shows `k ∣ ∑ χ(i)² i`,
   so `k ∣ S⁺ ↔ k ∣ S` (`Splus_dvd_iff`).
2. For `c` coprime to `k`, `x ↦ c x` permutes `ZMod k`, so `k ∣ S (1 - χ(c) c)`
   (`dvd_Ssum_mul`).
3. For each prime `p ∣ k` a Chinese-remainder multiplier `c` with
   `p ∤ 1 - χ(c) c` exists unless `p = 3`, `v₃(k)` is odd and `k / 3^{v₃(k)}`
   is a square; hence `k ∣ S` unless `k = 3 m²` (`dvd_Ssum_of_not_three_mul_sq`).
4. For `k = 3 m²`, `χ(i) = J(i,3) [gcd(i,m) = 1]`, and induction over the prime
   factors of `m` gives `S = -m² ∏_{p ∣ m} (1 - J(p,3))` (`Ssum_three_mul_sq`).
   So `k ∣ S` iff `3` divides that product iff some `p ∣ m` has `p ≡ 1 (mod 3)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A166102OddJacobiSymbol

open Finset

/-! ## Definition layer (mirrors the OEIS entries) -/

/-- **A166100.** `A166100 n` is the sum of those positive `i ≤ 2n+1` with
Jacobi symbol `J(i, 2n+1) = +1`. -/
def A166100 (n : ℕ) : ℕ :=
  ∑ i ∈ (Icc 1 (2 * n + 1)).filter (fun i : ℕ => jacobiSym (i : ℤ) (2 * n + 1) = 1), i

/-- **A166102** (membership). The odd numbers `k` such that `A166100((k-1)/2)/k` is not an
integer, i.e. `k` does not divide `A166100((k-1)/2)`.  The `Odd k` conjunct keeps the
natural-number subtraction and halving on their intended values (`(k-1)/2 = n` for
`k = 2n+1`). -/
def IsA166102 (k : ℕ) : Prop := Odd k ∧ ¬ k ∣ A166100 ((k - 1) / 2)

/-- **A166104** (membership). Natural numbers (positive integers) all of whose prime factors
are congruent to `3` or `5` modulo `6`; `1` is included. -/
def IsA166104 (n : ℕ) : Prop := 0 < n ∧ ∀ p ∈ n.primeFactors, p % 6 = 3 ∨ p % 6 = 5

/-- **A166103** (membership). The squares of the members of A166104. -/
def IsA166103 (x : ℕ) : Prop := ∃ n : ℕ, IsA166104 n ∧ x = n ^ 2

/-! ### Ground truth against the DATA lines -/

-- A166100: 1, 1, 5, 7, 27, 22, ...
example : A166100 0 = 1 := by
  rw [A166100, show Icc 1 (2 * 0 + 1) = {1} by decide]
  simp only [filter_singleton]
  norm_num

example : A166100 1 = 1 := by
  rw [A166100, show Icc 1 (2 * 1 + 1) = {1, 2, 3} by decide]
  simp only [filter_insert, filter_singleton]
  norm_num

example : A166100 2 = 5 := by
  rw [A166100, show Icc 1 (2 * 2 + 1) = {1, 2, 3, 4, 5} by decide]
  simp only [filter_insert, filter_singleton]
  norm_num

example : A166100 3 = 7 := by
  rw [A166100, show Icc 1 (2 * 3 + 1) = {1, 2, 3, 4, 5, 6, 7} by decide]
  simp only [filter_insert, filter_singleton]
  norm_num

example : A166100 4 = 27 := by
  rw [A166100, show Icc 1 (2 * 4 + 1) = {1, 2, 3, 4, 5, 6, 7, 8, 9} by decide]
  simp only [filter_insert, filter_singleton]
  norm_num

example : A166100 5 = 22 := by
  rw [A166100, show Icc 1 (2 * 5 + 1) = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} by decide]
  simp only [filter_insert, filter_singleton]
  norm_num

-- A166102 starts with 3 (A166100(1) = 1 is not a multiple of 3), and 1, 5 are not members
-- (A166100(0) = 1 and A166100(2) = 5).
example : IsA166102 3 := by
  refine ⟨⟨1, rfl⟩, ?_⟩
  rw [show (3 - 1) / 2 = 1 by rfl, A166100, show Icc 1 (2 * 1 + 1) = {1, 2, 3} by decide]
  simp only [filter_insert, filter_singleton]
  norm_num

example : ¬ IsA166102 5 := by
  rintro ⟨-, h⟩
  apply h
  rw [show (5 - 1) / 2 = 2 by rfl, A166100, show Icc 1 (2 * 2 + 1) = {1, 2, 3, 4, 5} by decide]
  simp only [filter_insert, filter_singleton]
  norm_num

-- A166104: 1, 3, 5 are members, 7 is not.
example : IsA166104 1 := ⟨by norm_num, by simp⟩

example : IsA166104 3 := ⟨by norm_num, by simp [Nat.prime_three.primeFactors]⟩

example : IsA166104 5 := ⟨by norm_num, by simp [Nat.prime_five.primeFactors]⟩

example : ¬ IsA166104 7 := by
  rintro ⟨-, h⟩
  have h7 := h 7 (by simp [(by norm_num : Nat.Prime 7).primeFactors])
  omega

-- A166103: 9 = 3^2 is a member.
example : IsA166103 9 := ⟨3, ⟨by norm_num, by simp [Nat.prime_three.primeFactors]⟩, rfl⟩


/-! ## Proof layer -/

/-- The internal sum `S⁺(k) = ∑_{1 ≤ i ≤ k, J(i,k) = 1} i`; `A166100 n = Splus (2n+1)`. -/
def Splus (k : ℕ) : ℕ := ∑ i ∈ (Icc 1 k).filter (fun i : ℕ => jacobiSym (i : ℤ) k = 1), i

/-- The twisted sum `S(k) = ∑_{0 ≤ i < k} J(i,k) i`. -/
def Ssum (k : ℕ) : ℤ := ∑ i ∈ range k, jacobiSym (i : ℤ) k * (i : ℤ)

/-- `A166100 n` is `S⁺(2n+1)` by definition. -/
theorem A166100_eq_Splus (n : ℕ) : A166100 n = Splus (2 * n + 1) := rfl

/-! ### Step 4: the conductor-3 sum -/


/-- `J(3j+1, 3) = 1`. -/
theorem jac3_three_mul_add_one (j : ℕ) : jacobiSym ((3 * j + 1 : ℕ) : ℤ) 3 = 1 := by
  rw [jacobiSym.mod_left]; push_cast
  rw [show ((3 * (j:ℤ) + 1) % (3:ℤ)) = 1 by omega]; norm_num

/-- `J(3j+2, 3) = -1`. -/
theorem jac3_three_mul_add_two (j : ℕ) : jacobiSym ((3 * j + 2 : ℕ) : ℤ) 3 = -1 := by
  rw [jacobiSym.mod_left]; push_cast
  rw [show ((3 * (j:ℤ) + 2) % (3:ℤ)) = 2 by omega]; norm_num

/-- `J(3j, 3) = 0`. -/
theorem jac3_three_mul (j : ℕ) : jacobiSym ((3 * j : ℕ) : ℤ) 3 = 0 := by
  rw [jacobiSym.mod_left]; push_cast
  rw [show ((3 * (j:ℤ)) % (3:ℤ)) = 0 by omega]; norm_num

/-- Block sum: `∑_{i < 3N} J(i,3) i = -N`. -/
theorem block_sum (N : ℕ) :
    ∑ i ∈ range (3 * N), jacobiSym (i : ℤ) 3 * (i : ℤ) = -(N : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 2 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, ih, jac3_three_mul, jac3_three_mul_add_one, jac3_three_mul_add_two]
    push_cast; ring

/-- Summing over the multiples of `p` below `p N`: `∑_{i < pN, p ∣ i} f i = ∑_{j < N} f (p j)`. -/
theorem sum_range_mul_filter_dvd {M : Type*} [AddCommMonoid M] (p N : ℕ) (hp : 0 < p)
    (f : ℕ → M) :
    ∑ i ∈ range (p * N), (if p ∣ i then f i else 0) = ∑ j ∈ range N, f (p * j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [mul_add, mul_one, sum_range_add, ih, sum_range_succ]
    congr 1
    rw [sum_eq_single 0]
    · simp
    · intro b hb hb0
      have hb' : b < p := mem_range.mp hb
      rw [if_neg]
      intro hd
      have : p ∣ b := (Nat.dvd_add_right (dvd_mul_right p N)).mp hd
      exact hb0 (Nat.eq_zero_of_dvd_of_lt this hb')
    · intro h; exact absurd (mem_range.mpr hp) h

/-- The coprimality indicator `[gcd(i, m) = 1]` as an integer. -/
def cop (m i : ℕ) : ℤ := if Nat.Coprime i m then 1 else 0

/-- `F(m, L) = ∑_{i < 3L} J(i,3) [gcd(i,m) = 1] i`. -/
def Fsum (m L : ℕ) : ℤ := ∑ i ∈ range (3 * L), jacobiSym (i : ℤ) 3 * cop m i * (i : ℤ)

/-- `g(m) = ∏_{p ∣ m prime} (1 - J(p,3))`. -/
def gfac (m : ℕ) : ℤ := ∏ p ∈ m.primeFactors, (1 - jacobiSym (p : ℤ) 3)

/-- Closed form of the conductor-3 sum: if `m ∣ L` then `F(m, L) = -L · g(m)` (induction over
the prime factors of `m`). -/
theorem Fsum_eq (m : ℕ) : ∀ L : ℕ, m ∣ L → Fsum m L = -(L : ℤ) * gfac m := by
  induction m using induction_on_primes with
  | zero =>
    intro L hL
    rw [zero_dvd_iff] at hL; subst hL; simp [Fsum]
  | one =>
    intro L _
    simp [Fsum, gfac, cop, block_sum]
  | prime_mul p a hp ih =>
    intro L hL
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · subst hL0; simp [Fsum]
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [mul_zero, zero_dvd_iff] at hL; omega
    by_cases hpa : p ∣ a
    · have hcop : ∀ i, cop (p * a) i = cop a i := by
        intro i
        unfold cop
        congr 1
        apply propext
        rw [Nat.coprime_mul_iff_right]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨Nat.Coprime.coprime_dvd_right hpa h, h⟩
      have hpf : (p * a).primeFactors = a.primeFactors := by
        rw [Nat.primeFactors_mul hp.ne_zero ha0, hp.primeFactors]
        have : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpa, ha0⟩
        simpa using this
      have hFa := ih L (dvd_trans (dvd_mul_left a p) hL)
      simp only [Fsum, hcop] at hFa ⊢
      rw [hFa, gfac, gfac, hpf]
    · obtain ⟨L', rfl⟩ : p ∣ L := dvd_trans (dvd_mul_right p a) hL
      have haL' : a ∣ L' := Nat.dvd_of_mul_dvd_mul_left hp.pos hL
      have hcop : ∀ i, cop (p * a) i = cop a i - (if p ∣ i then cop a i else 0) := by
        intro i
        unfold cop
        have hc : Nat.Coprime i (p * a) ↔ ¬ p ∣ i ∧ Nat.Coprime i a := by
          rw [Nat.coprime_mul_iff_right, Nat.coprime_comm, hp.coprime_iff_not_dvd]
        simp only [hc]
        by_cases h1 : p ∣ i <;> by_cases h2 : Nat.Coprime i a <;> simp [h1, h2]
      have hcopmul : ∀ j, cop a (p * j) = cop a j := by
        intro j
        unfold cop
        have hc : Nat.Coprime (p * j) a ↔ Nat.Coprime j a := by
          rw [Nat.coprime_mul_iff_left, hp.coprime_iff_not_dvd]
          simp [hpa]
        simp only [hc]
      have hpf : (p * a).primeFactors = insert p a.primeFactors := by
        rw [Nat.primeFactors_mul hp.ne_zero ha0, hp.primeFactors]
        rfl
      have hpnot : p ∉ a.primeFactors := fun h => hpa (Nat.dvd_of_mem_primeFactors h)
      have hsplit : Fsum (p * a) (p * L') = Fsum a (p * L') -
          ∑ i ∈ range (p * (3 * L')),
            (if p ∣ i then jacobiSym (i : ℤ) 3 * cop a i * (i : ℤ) else 0) := by
        simp only [Fsum, hcop]
        rw [show 3 * (p * L') = p * (3 * L') by ring, ← sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        split_ifs <;> ring
      have hmult : ∑ i ∈ range (p * (3 * L')),
            (if p ∣ i then jacobiSym (i : ℤ) 3 * cop a i * (i : ℤ) else 0)
          = jacobiSym (p : ℤ) 3 * (p : ℤ) * Fsum a L' := by
        rw [sum_range_mul_filter_dvd p (3 * L') hp.pos, Fsum, mul_sum]
        apply sum_congr rfl
        intro j _
        rw [hcopmul]
        push_cast
        rw [jacobiSym.mul_left]
        ring
      rw [hsplit, hmult, ih _ (dvd_trans haL' (dvd_mul_left L' p)), ih _ haL', gfac, gfac, hpf,
        prod_insert hpnot]
      push_cast
      ring

/-! ### Step 2: the multiplier identity -/

/-- A sum over `range k` is a sum over `ZMod k` through `ZMod.val`. -/
theorem sum_range_eq_sum_zmod {R : Type*} [AddCommMonoid R] (k : ℕ) [NeZero k] (g : ℕ → R) :
    ∑ i ∈ range k, g i = ∑ x : ZMod k, g x.val := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  exact (Fin.sum_univ_eq_sum_range g (n + 1)).symm

/-- `J(n mod k, k) = J(n, k)` for natural `n`. -/
theorem jac_natCast_mod (n k : ℕ) : jacobiSym ((n % k : ℕ) : ℤ) k = jacobiSym (n : ℤ) k := by
  rw [Int.natCast_mod, ← jacobiSym.mod_left]


/-- `S(k)` reduced modulo `k` is `∑_{x : ZMod k} J(x,k) x`. -/
theorem Ssum_cast (k : ℕ) [NeZero k] :
    ((Ssum k : ℤ) : ZMod k) = ∑ x : ZMod k, ((jacobiSym (x.val : ℤ) k : ℤ) : ZMod k) * x := by
  rw [Ssum]; push_cast
  rw [sum_range_eq_sum_zmod k (fun i => ((jacobiSym (i : ℤ) k : ℤ) : ZMod k) * (i : ZMod k))]
  simp only [ZMod.natCast_zmod_val]

/-- Multiplier identity: for `c` coprime to `k ≠ 0`, `k ∣ S(k) · (1 - J(c,k) c)`, because `x ↦ c
x` permutes `ZMod k`. -/
theorem dvd_Ssum_mul (k c : ℕ) (hk : k ≠ 0) (hc : Nat.Coprime c k) :
    (k : ℤ) ∣ Ssum k * (1 - jacobiSym (c : ℤ) k * (c : ℤ)) := by
  haveI : NeZero k := ⟨hk⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set u := ZMod.unitOfCoprime c hc
  have hu : (u : ZMod k) = (c : ZMod k) := ZMod.coe_unitOfCoprime c hc
  set F : ZMod k → ZMod k := fun x => ((jacobiSym (x.val : ℤ) k : ℤ) : ZMod k) * x with hF
  have hperm : ∑ x : ZMod k, F x = ∑ x : ZMod k, F ((u : ZMod k) * x) :=
    (Equiv.sum_comp (Units.mulLeft u) F).symm
  have hFu : ∀ x : ZMod k, F ((u : ZMod k) * x)
      = ((jacobiSym (c : ℤ) k : ℤ) : ZMod k) * (c : ZMod k) * F x := by
    intro x
    simp only [hF, hu, ZMod.val_mul, ZMod.val_natCast]
    rw [jac_natCast_mod]
    push_cast
    rw [jacobiSym.mul_left, ← jacobiSym.mod_left]
    push_cast
    ring
  have hT : ((Ssum k : ℤ) : ZMod k) =
      ((jacobiSym (c : ℤ) k : ℤ) : ZMod k) * (c : ZMod k) * ((Ssum k : ℤ) : ZMod k) := by
    have hSF : ((Ssum k : ℤ) : ZMod k) = ∑ x : ZMod k, F x := Ssum_cast k
    rw [hSF, mul_sum]
    conv_lhs => rw [hperm]
    exact sum_congr rfl (fun x _ => hFu x)
  push_cast
  linear_combination hT

/-! ### Step 3: local multipliers -/

/-- Local-to-global: if for every prime `p ∣ k` some `u` with `p ∤ u` has `k ∣ S u`, then `k ∣
S`. -/
theorem dvd_of_local (k : ℕ) (S : ℤ)
    (h : ∀ p : ℕ, p.Prime → p ∣ k → ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (k : ℤ) ∣ S * u) :
    (k : ℤ) ∣ S := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p e hp hpe
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp
  have hp' : p.Prime := hp
  have hpk : p ∣ k := dvd_trans (dvd_pow_self p he.ne') hpe
  obtain ⟨u, hpu, hku⟩ := h p hp' hpk
  have hcop : IsCoprime ((p : ℤ) ^ e) u :=
    ((Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp').irreducible).mpr
      hpu).pow_left
  have hpeS : ((p : ℤ) ^ e) ∣ S * u :=
    dvd_trans (by exact_mod_cast Int.natCast_dvd_natCast.mpr hpe) hku
  have := hcop.dvd_of_dvd_mul_right hpeS
  rw [← Int.natCast_dvd]
  exact_mod_cast this

/-- Chinese remainder multiplier: for coprime `d, M` and `a` coprime to `d` there is `c` coprime
to `d M` with `c ≡ a (mod d)`, `c ≡ 1 (mod M)` and `J(c, d M) = J(a, d)`. -/
theorem exists_crt_jac (d M a : ℕ) (hd : d ≠ 0) (hM : M ≠ 0) (hdM : Nat.Coprime d M)
    (ha : Nat.Coprime a d) :
    ∃ c : ℕ, Nat.Coprime c (d * M) ∧ c ≡ a [MOD d] ∧ c ≡ 1 [MOD M] ∧
      jacobiSym (c : ℤ) (d * M) = jacobiSym (a : ℤ) d := by
  haveI : NeZero d := ⟨hd⟩
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨c, hcd, hcM⟩ := Nat.chineseRemainder hdM a 1
  refine ⟨c, ?_, hcd, hcM, ?_⟩
  · apply Nat.Coprime.mul_right
    · unfold Nat.Coprime; rw [hcd.gcd_eq]; exact ha
    · unfold Nat.Coprime; rw [hcM.gcd_eq]; exact Nat.gcd_one_left M
  · rw [jacobiSym.mul_right]
    have h1 : jacobiSym (c : ℤ) d = jacobiSym (a : ℤ) d := by
      apply jacobiSym.mod_left'
      exact_mod_cast hcd
    have h2 : jacobiSym (c : ℤ) M = 1 := by
      rw [jacobiSym.mod_left' (a₂ := ((1 : ℕ) : ℤ)) (by exact_mod_cast hcM)]
      simp
    rw [h1, h2, mul_one]

/-- A prime divisor of an odd number is not `2`. -/
theorem odd_prime_of_dvd_odd {k p : ℕ} (hk : Odd k) (hp : p.Prime) (hpk : p ∣ k) : p ≠ 2 := by
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr hpk)

/-- Local multiplier at a prime `p ∣ k` (odd `k`) unless `p = 3` with odd exponent: some `c`
coprime to `k` has `p ∤ 1 - J(c,k) c` (take `c ≡ 2` on the `p`-part and `c ≡ 1` elsewhere). -/
theorem witness_two (k p : ℕ) (hk : Odd k) (hp : p.Prime) (hpk : p ∣ k)
    (h : ¬ (p = 3 ∧ Odd (k.factorization p))) :
    ∃ c : ℕ, Nat.Coprime c k ∧ ¬ (p : ℤ) ∣ 1 - jacobiSym (c : ℤ) k * (c : ℤ) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hk) ⟨0, rfl⟩
  have hp2 : p ≠ 2 := odd_prime_of_dvd_odd hk hp hpk
  set e := k.factorization p with he_def
  have he : 0 < e := hp.factorization_pos_of_dvd hk0 hpk
  set M := ordCompl[p] k with hM_def
  have hkdM : p ^ e * M = k := Nat.ordProj_mul_ordCompl_eq_self k p
  have hM0 : M ≠ 0 := by intro h0; rw [h0, mul_zero] at hkdM; exact hk0 hkdM.symm
  have hdM : Nat.Coprime (p ^ e) M := (Nat.coprime_ordCompl hp hk0).pow_left e
  have ha : Nat.Coprime 2 (p ^ e) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_right e
  obtain ⟨c, hck, hcd, -, hJ⟩ :=
    exists_crt_jac (p ^ e) M 2 (pow_ne_zero e hp.ne_zero) hM0 hdM ha
  rw [hkdM] at hck hJ
  refine ⟨c, hck, ?_⟩
  rw [hJ, jacobiSym.pow_right]
  intro hdiv
  have hcp : (p : ℤ) ∣ (c : ℤ) - 2 := by
    have h1 : c ≡ 2 [MOD p] := Nat.ModEq.of_dvd (dvd_pow_self p he.ne') hcd
    have h2 := Nat.modEq_iff_dvd.mp h1.symm
    exact_mod_cast h2
  have hε : jacobiSym ((2 : ℕ) : ℤ) p = 1 ∨ jacobiSym ((2 : ℕ) : ℤ) p = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hkey : (p : ℤ) ∣ 1 - jacobiSym ((2 : ℕ) : ℤ) p ^ e * 2 := by
    have hsum := dvd_add hdiv (dvd_mul_of_dvd_right hcp (jacobiSym ((2 : ℕ) : ℤ) p ^ e))
    have heq : 1 - jacobiSym ((2 : ℕ) : ℤ) p ^ e * 2 = 1 - jacobiSym ((2 : ℕ) : ℤ) p ^ e * c
        + jacobiSym ((2 : ℕ) : ℤ) p ^ e * (c - 2) := by ring
    rw [heq]; exact hsum
  rcases hε with hε | hε
  · rw [hε, one_pow] at hkey
    have : (p : ℤ) ∣ 1 := by
      have h' : (1 : ℤ) = -(1 - 1 * 2) := by norm_num
      rw [h']; exact dvd_neg.mpr hkey
    have := Int.natCast_dvd_natCast.mp (by exact_mod_cast this)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · rcases Nat.even_or_odd e with hev | hodd
    · rw [hε, hev.neg_one_pow] at hkey
      have : (p : ℤ) ∣ 1 := by
        have h' : (1 : ℤ) = -(1 - 1 * 2) := by norm_num
        rw [h']; exact dvd_neg.mpr hkey
      have := Int.natCast_dvd_natCast.mp (by exact_mod_cast this)
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · rw [hε, hodd.neg_one_pow] at hkey
      have h3 : p ∣ 3 := Int.natCast_dvd_natCast.mp (by norm_num at hkey; exact_mod_cast hkey)
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      exact h ⟨hp3, hodd⟩

/-- Every odd prime `q` has a quadratic nonresidue `g`, i.e. `J(g, q) = -1`. -/
theorem exists_nonresidue (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    ∃ g : ℕ, Nat.Coprime g q ∧ jacobiSym (g : ℤ) q = -1 := by
  haveI := Fact.mk hq
  obtain ⟨z, hz⟩ := FiniteField.exists_nonsquare (F := ZMod q)
    (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  have hJ : jacobiSym ((z.val : ℕ) : ℤ) q = -1 := by
    rw [ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
    simpa using hz
  refine ⟨z.val, ?_, hJ⟩
  by_contra hcop
  have h0 : jacobiSym ((z.val : ℕ) : ℤ) q = 0 := by
    rw [jacobiSym.eq_zero_iff, Int.gcd_natCast_natCast]
    exact ⟨hq.ne_zero, hcop⟩
  rw [h0] at hJ
  norm_num at hJ

/-- Local multiplier at `p = 3` with odd exponent when `k` is not of the form `3 m²`: some `c`
coprime to `k` has `3 ∤ 1 - J(c,k) c` (a nonresidue at a prime of odd exponent in `k /
3^{v₃(k)}`, and `c ≡ 1` elsewhere). -/
theorem witness_three (k : ℕ) (hk : Odd k) (h3 : 3 ∣ k) (hsq : ¬ ∃ m : ℕ, k = 3 * m ^ 2)
    (he : Odd (k.factorization 3)) :
    ∃ c : ℕ, Nat.Coprime c k ∧ ¬ (3 : ℤ) ∣ 1 - jacobiSym (c : ℤ) k * (c : ℤ) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hk) ⟨0, rfl⟩
  set e := k.factorization 3 with he_def
  set M := ordCompl[3] k with hM_def
  have hkM : 3 ^ e * M = k := Nat.ordProj_mul_ordCompl_eq_self k 3
  have hM0 : M ≠ 0 := by intro h0; rw [h0, mul_zero] at hkM; exact hk0 hkM.symm
  obtain ⟨a, b, ha0, hb0, hab, hsqf⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hM0)
  have ha1 : a ≠ 1 := by
    rintro rfl
    obtain ⟨t, ht⟩ := he
    apply hsq
    refine ⟨3 ^ t * b, ?_⟩
    rw [← hkM, ← hab, ht]
    ring
  obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd ha1
  have hqM : q ∣ M := dvd_trans hqa (hab ▸ dvd_mul_left a (b ^ 2))
  have hqk : q ∣ k := dvd_trans hqM (Nat.ordCompl_dvd k 3)
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact Nat.not_dvd_ordCompl Nat.prime_three hk0 hqM
  have hq2 : q ≠ 2 := odd_prime_of_dvd_odd hk hq hqk
  set f := k.factorization q with hf_def
  have hf : Odd f := by
    have h1 : f = M.factorization q := by
      rw [hM_def, Nat.factorization_ordCompl, Finsupp.erase_ne hq3]
    have h2 : M.factorization q = 2 * b.factorization q + a.factorization q := by
      rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0.ne') ha0.ne', Nat.factorization_pow]
      simp
    have h3' : a.factorization q = 1 := Nat.factorization_eq_one_of_squarefree hsqf hq hqa
    rw [h1, h2, h3']
    exact ⟨b.factorization q, rfl⟩
  obtain ⟨g, hgq, hgJ⟩ := exists_nonresidue q hq hq2
  set N := ordCompl[q] k with hN_def
  have hkN : q ^ f * N = k := Nat.ordProj_mul_ordCompl_eq_self k q
  have hN0 : N ≠ 0 := by intro h0; rw [h0, mul_zero] at hkN; exact hk0 hkN.symm
  have hdN : Nat.Coprime (q ^ f) N := (Nat.coprime_ordCompl hq hk0).pow_left f
  obtain ⟨c, hck, -, hcN, hJ⟩ :=
    exists_crt_jac (q ^ f) N g (pow_ne_zero f hq.ne_zero) hN0 hdN (hgq.pow_right f)
  rw [hkN] at hck hJ
  refine ⟨c, hck, ?_⟩
  rw [hJ, jacobiSym.pow_right, hgJ, hf.neg_one_pow]
  have h3N : 3 ∣ N := Nat.dvd_ordCompl_of_dvd_not_dvd h3
    (fun hq3' => hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hq3'))
  have hc3 : c % 3 = 1 := Nat.ModEq.of_dvd h3N hcN
  omega

/-! ### Step 1: reduction from `S⁺` to `S` -/



/-- `2 S⁺(k) = ∑_{i ≤ k} J(i,k)² i + ∑_{i ≤ k} J(i,k) i`. -/
theorem two_mul_Splus (k : ℕ) :
    2 * (Splus k : ℤ) = ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k ^ 2 * (i : ℤ)
      + ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k * (i : ℤ) := by
  have h1 : (Splus k : ℤ) = ∑ i ∈ range (k + 1),
      (if jacobiSym (i : ℤ) k = 1 then (i : ℤ) else 0) := by
    rw [Splus, Nat.cast_sum, sum_filter]
    apply sum_subset
    · intro i hi
      rw [mem_Icc] at hi; rw [mem_range]; omega
    · intro i hi hni
      rw [mem_range] at hi
      rw [mem_Icc] at hni
      have hi0 : i = 0 := by omega
      subst hi0; simp
  rw [h1, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rcases jacobiSym.trichotomy (i : ℤ) k with h | h | h <;> rw [h] <;> norm_num
  ring

/-- `J(k - j, k)² = J(j, k)²` for `j ≤ k`. -/
theorem jac_sq_reflect (k j : ℕ) (hj : j ≤ k) :
    jacobiSym ((k - j : ℕ) : ℤ) k ^ 2 = jacobiSym (j : ℤ) k ^ 2 := by
  have hmod : jacobiSym ((k - j : ℕ) : ℤ) k = jacobiSym (-1 * (j : ℤ)) k := by
    apply jacobiSym.mod_left'
    rw [Nat.cast_sub hj, show (k : ℤ) - j = -1 * j + k * 1 by ring, Int.add_mul_emod_self_left]
  have hneg : jacobiSym (-1 : ℤ) k ^ 2 = 1 := by
    apply jacobiSym.sq_one
    simp
  rw [hmod, jacobiSym.mul_left, mul_pow, hneg, one_mul]

/-- For odd `k`, `k ∣ ∑_{i ≤ k} J(i,k)² i` (reflection `i ↦ k - i`). -/
theorem dvd_Usum (k : ℕ) (hk : Odd k) :
    (k : ℤ) ∣ ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k ^ 2 * (i : ℤ) := by
  have hrefl : ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k ^ 2 * (i : ℤ)
      = ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k ^ 2 * ((k : ℤ) - i) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    have hle : i ≤ k := by omega
    rw [show k + 1 - 1 - i = k - i by omega, jac_sq_reflect k i hle, Nat.cast_sub hle]
  have h2U : 2 * ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k ^ 2 * (i : ℤ)
      = (k : ℤ) * ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k ^ 2 := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hk2 : IsCoprime (k : ℤ) 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨t, rfl⟩ := hk
    push_cast
    have : Int.gcd (2 * (t : ℤ) + 1) 2 = Int.gcd 1 2 := by
      rw [show (2 * (t : ℤ) + 1) = 1 + 2 * t by ring, Int.gcd_add_mul_left_left]
    rw [this]; rfl
  exact hk2.dvd_of_dvd_mul_left (h2U ▸ dvd_mul_right _ _)

/-- For odd `k`, `k ∣ S⁺(k)` iff `k ∣ S(k)`. -/
theorem Splus_dvd_iff (k : ℕ) (hk : Odd k) :
    (k : ℤ) ∣ (Splus k : ℤ) ↔ (k : ℤ) ∣ Ssum k := by
  have hk2 : IsCoprime (k : ℤ) 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨t, rfl⟩ := hk
    push_cast
    have : Int.gcd (2 * (t : ℤ) + 1) 2 = Int.gcd 1 2 := by
      rw [show (2 * (t : ℤ) + 1) = 1 + 2 * t by ring, Int.gcd_add_mul_left_left]
    rw [this]; rfl
  have hS' : ∑ i ∈ range (k + 1), jacobiSym (i : ℤ) k * (i : ℤ)
      = Ssum k + jacobiSym (k : ℤ) k * k := by
    rw [sum_range_succ, Ssum]
  have hiff2 : (k : ℤ) ∣ (Splus k : ℤ) ↔ (k : ℤ) ∣ 2 * (Splus k : ℤ) :=
    ⟨fun h => dvd_mul_of_dvd_right h 2, fun h => hk2.dvd_of_dvd_mul_left h⟩
  rw [hiff2, two_mul_Splus, hS', ← add_assoc, dvd_add_left (dvd_mul_left _ _),
    dvd_add_right (dvd_Usum k hk)]

/-! ### Assembly -/

/-- For odd `k` not of the form `3 m²`, `k ∣ S(k)`. -/
theorem dvd_Ssum_of_not_three_mul_sq (k : ℕ) (hk : Odd k) (hsq : ¬ ∃ m : ℕ, k = 3 * m ^ 2) :
    (k : ℤ) ∣ Ssum k := by
  have hk0 : k ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hk) ⟨0, rfl⟩
  apply dvd_of_local k (Ssum k)
  intro p hp hpk
  by_cases h : p = 3 ∧ Odd (k.factorization p)
  · obtain ⟨rfl, hodd⟩ := h
    obtain ⟨c, hck, hc⟩ := witness_three k hk hpk hsq hodd
    exact ⟨_, by exact_mod_cast hc, dvd_Ssum_mul k c hk0 hck⟩
  · obtain ⟨c, hck, hc⟩ := witness_two k p hk hp hpk h
    exact ⟨_, hc, dvd_Ssum_mul k c hk0 hck⟩

/-- `J(i, 3 m²) = J(i, 3) [gcd(i, m) = 1]` for `m ≠ 0`. -/
theorem jac_three_mul_sq (i m : ℕ) (hm : m ≠ 0) :
    jacobiSym (i : ℤ) (3 * m ^ 2) = jacobiSym (i : ℤ) 3 * cop m i := by
  haveI : NeZero m := ⟨hm⟩
  rw [jacobiSym.mul_right, jacobiSym.pow_right, cop]
  split_ifs with h
  · rw [jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact h)]
  · have h0 : jacobiSym (i : ℤ) m = 0 := by
      rw [jacobiSym.eq_zero_iff, Int.gcd_natCast_natCast]
      exact ⟨hm, h⟩
    rw [h0]; ring

/-- `S(3 m²) = -m² g(m)` for `m ≠ 0`. -/
theorem Ssum_three_mul_sq (m : ℕ) (hm : m ≠ 0) :
    Ssum (3 * m ^ 2) = -((m : ℤ) ^ 2) * gfac m := by
  have h := Fsum_eq m (m ^ 2) (dvd_pow_self m two_ne_zero)
  rw [Fsum] at h
  rw [Ssum, show -((m : ℤ) ^ 2) * gfac m = -((m ^ 2 : ℕ) : ℤ) * gfac m by push_cast; ring, ← h]
  apply sum_congr rfl
  intro i _
  rw [jac_three_mul_sq i m hm]

/-- `J(n, 3)` by residue: `0`, `1`, `-1` for `n ≡ 0, 1, 2 (mod 3)`. -/
theorem jac3_eq (n : ℕ) : jacobiSym (n : ℤ) 3 =
    if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1 := by
  have hn : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 3
  · rw [hn, add_zero, jac3_three_mul]; rfl
  · rw [hn, jac3_three_mul_add_one]; rfl
  · rw [hn, jac3_three_mul_add_two]; rfl

/-- `g(m) = 0` when some prime factor of `m` is `≡ 1 (mod 3)`. -/
theorem gfac_eq_zero (m p : ℕ) (hp : p ∈ m.primeFactors) (hp3 : p % 3 = 1) : gfac m = 0 := by
  apply prod_eq_zero hp
  rw [jac3_eq, if_neg (by omega), if_pos hp3]
  ring

/-- `3 ∤ g(m)` when no prime factor of `m` is `≡ 1 (mod 3)` (every factor is `1` or `2`). -/
theorem not_three_dvd_gfac (m : ℕ) (h : ∀ p ∈ m.primeFactors, p % 3 ≠ 1) :
    ¬ (3 : ℤ) ∣ gfac m := by
  rw [gfac, Prime.dvd_finsetProd_iff Int.prime_three]
  rintro ⟨p, hp, hdvd⟩
  have hp3 := h p hp
  rw [jac3_eq] at hdvd
  by_cases h0 : p % 3 = 0
  · rw [if_pos h0] at hdvd; norm_num at hdvd
  · rw [if_neg h0, if_neg hp3] at hdvd; norm_num at hdvd


/-- **Core characterisation.** For odd `k`, `k ∤ S⁺(k)` iff `k = 3 m²` with no prime factor
of `m` congruent to `1` modulo `3`. -/
theorem not_dvd_Splus_iff (k : ℕ) (hk : Odd k) :
    ¬ k ∣ Splus k ↔ ∃ m : ℕ, k = 3 * m ^ 2 ∧ ∀ p ∈ m.primeFactors, p % 3 ≠ 1 := by
  have hk0 : k ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hk) ⟨0, rfl⟩
  rw [← Int.natCast_dvd_natCast, Splus_dvd_iff k hk]
  constructor
  · intro hnd
    by_contra hcon
    apply hnd
    by_cases hsq : ∃ m : ℕ, k = 3 * m ^ 2
    · obtain ⟨m, rfl⟩ := hsq
      have hm : m ≠ 0 := by rintro rfl; exact hk0 (by norm_num)
      push Not at hcon
      obtain ⟨p, hp, hp1⟩ := hcon m rfl
      rw [Ssum_three_mul_sq m hm, gfac_eq_zero m p hp hp1, mul_zero]
      exact dvd_zero _
    · exact dvd_Ssum_of_not_three_mul_sq k hk hsq
  · rintro ⟨m, rfl, hm⟩ hdvd
    have hm0 : m ≠ 0 := by rintro rfl; exact hk0 (by norm_num)
    rw [Ssum_three_mul_sq m hm0] at hdvd
    have h3 : (3 : ℤ) ∣ gfac m := by
      push_cast at hdvd
      rw [neg_mul, dvd_neg, mul_comm ((m : ℤ) ^ 2) (gfac m)] at hdvd
      exact (mul_dvd_mul_iff_right (by positivity)).mp hdvd
    exact not_three_dvd_gfac m hm h3

/-- **Karttunen's conjecture (A166102, Antti Karttunen, Oct 13 2009), set form.**

Verbatim: "Conjecture: a(n) = 3*A166103(n). (Checked for terms a(1)-a(92).)"

An odd `k` fails to divide `A166100((k-1)/2)` exactly when `k = 3 x` with `x` a square of a
number all of whose prime factors are `≡ 3` or `5 (mod 6)`.  Since A166102 and A166103 are
the increasing enumerations of these two sets, this set equality is equivalent to the
termwise statement, which is derived as `a166102_eq_three_mul_a166103`. -/
theorem a166102_conjecture (k : ℕ) : IsA166102 k ↔ ∃ x : ℕ, IsA166103 x ∧ k = 3 * x := by
  constructor
  · rintro ⟨hk, hnd⟩
    have hkn : 2 * ((k - 1) / 2) + 1 = k := by
      obtain ⟨t, rfl⟩ := hk; omega
    rw [A166100_eq_Splus, hkn] at hnd
    obtain ⟨m, rfl, hm⟩ := (not_dvd_Splus_iff _ hk).mp hnd
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; exact absurd hk (by decide)
      · exact h
    refine ⟨m ^ 2, ⟨m, ⟨hm0, ?_⟩, rfl⟩, rfl⟩
    intro p hp
    have hpk : p ∣ 3 * m ^ 2 := dvd_trans (Nat.dvd_of_mem_primeFactors hp)
      (dvd_trans (dvd_pow_self m two_ne_zero) (dvd_mul_left _ 3))
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Odd.of_dvd_nat hk hpk)
    have hp3 := hm p hp
    omega
  · rintro ⟨x, ⟨n, ⟨hn0, hn⟩, rfl⟩, rfl⟩
    have hn2 : ¬ 2 ∣ n := by
      intro h2
      have := hn 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn0.ne'⟩)
      omega
    have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
    have hk : Odd (3 * n ^ 2) := (by decide : Odd 3).mul (hnodd.pow)
    refine ⟨hk, ?_⟩
    have hkn : 2 * ((3 * n ^ 2 - 1) / 2) + 1 = 3 * n ^ 2 := by
      obtain ⟨t, ht⟩ := hk; omega
    rw [A166100_eq_Splus, hkn]
    refine (not_dvd_Splus_iff _ hk).mpr ⟨n, rfl, fun p hp => ?_⟩
    have := hn p hp
    omega

/-- A166102 is infinite: `3 · (3^j)²` is a member for every `j`. -/
theorem infinite_A166102 : {k : ℕ | IsA166102 k}.Infinite := by
  have hinj : Function.Injective (fun j : ℕ => 3 * (3 ^ j) ^ 2) := by
    intro a b hab
    have h1 : (3 ^ a) ^ 2 = (3 ^ b) ^ 2 := by simpa using hab
    have h2 : 3 ^ a = 3 ^ b := Nat.pow_left_injective two_ne_zero h1
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h2)
  refine Set.infinite_of_injective_forall_mem hinj (fun j => ?_)
  refine (a166102_conjecture _).mpr ⟨(3 ^ j) ^ 2, ⟨3 ^ j, ⟨by positivity, ?_⟩, rfl⟩, rfl⟩
  intro p hp
  have hp3 : p ∣ 3 := (Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow
    (Nat.dvd_of_mem_primeFactors hp)
  have : p = 3 := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hp)
    Nat.prime_three).mp hp3
  omega

/-- **Karttunen's conjecture (A166102), termwise form.** `a(n) = 3 * A166103(n)` for every
index, with both sequences enumerated from offset `0` by `Nat.nth`. -/
theorem a166102_eq_three_mul_a166103 (n : ℕ) :
    Nat.nth IsA166102 n = 3 * Nat.nth IsA166103 n := by
  have hfun : (fun i => IsA166102 (3 * i)) = IsA166103 := by
    funext i
    apply propext
    rw [a166102_conjecture]
    constructor
    · rintro ⟨x, hx, hix⟩
      have : i = x := by omega
      exact this ▸ hx
    · intro hi
      exact ⟨i, hi, rfl⟩
  have hmono : StrictMono (fun i : ℕ => 3 * i) := fun a b hab => by
    show 3 * a < 3 * b
    omega
  have h := Nat.nth_comp_of_strictMono (p := IsA166102) (n := n) hmono
    (fun k hk => by
      obtain ⟨x, -, rfl⟩ := (a166102_conjecture k).mp hk
      exact ⟨x, rfl⟩)
    (fun hfi => absurd hfi infinite_A166102)
  rw [hfun] at h
  exact h.symm

end Candidates.A166102OddJacobiSymbol
