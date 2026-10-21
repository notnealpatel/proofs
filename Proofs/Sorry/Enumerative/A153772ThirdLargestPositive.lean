/-
# A153772 — Sigg: `a(n)` is the third largest member of a Collatz level

## OEIS source (retrieved with `oeis show A153772`, 2026-10-21)

```
NAME:     a(n) = (2^n + 2*(-1)^n - 6)/3.
TERMS:    -1,-2,0,0,4,8,20,40,84,168,340,680,1364,2728,5460,10920,21844,...
KEYWORDS: easy,sign
FORMULA:  a(n) = 4*A000975(n-3) for n >= 3. - _Markus Sigg_, Sep 14 2020
COMMENT (the conjecture):
  Conjecture: For n >= 6, a(n) is the third largest natural number whose
  Collatz orbit has length n+2. - _Markus Sigg_, Sep 14 2020
```

## Status

Triage: open (no proof in the entry; a web and OEIS name search found no
published proof, which does not establish novelty).  The companion statement
(A000975, Sigg, Sep 14 2020: `A000975(n)` is the second largest element of the
level `n + 2`) is stated without proof in A127824 and is not formalized here.

## Conventions

The Collatz map is `x ↦ x/2` for even `x` and `x ↦ 3x+1` for odd `x`.  The
orbit of `m` is `(m, T m, …, 1)`, stopped at the first `1`; it has `n + 2`
elements exactly when the trajectory first reaches `1` at step `n + 1`
(`FirstHitsOne (n + 1) m`).  `0` never reaches `1`, so every level consists of
positive integers.

## Proof outline (kernel-checked below)

* `level_trichotomy`: an `m` first reaching `1` at step `k` is `2^k`, or has a
  single `3x+1` step (`3m + 2^e = 2^(e+j)`, `j` even, `4 ≤ j`, `k = e + j + 1`),
  or satisfies `36 m ≤ 2^k`.  Forward induction on `k`.
* `level_top`: the level elements above `2^(e₁+2) c₀` are exactly `2^k` and
  `2^e₁ c₁` (one-up elements with the two largest admissible `j`).
* `a153772_third_largest`: the conjecture, for every `n ≥ 6`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A153772ThirdLargestPositive

/-- The OEIS `A153772` term formula `a(n) = (2^n + 2(-1)^n - 6)/3`, over `ℤ`. -/
def a (n : ℕ) : ℤ := (2 ^ n + 2 * (-1) ^ n - 6) / 3

example : a 0 = -1 := by decide
example : a 6 = 20 := by decide
example : a 9 = 168 := by decide
example : (List.range 12).map a = [-1, -2, 0, 0, 4, 8, 20, 40, 84, 168, 340, 680] := by decide

/-- The standard Collatz map. -/
def collatzStep (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- `FirstHitsOne k m`: the Collatz trajectory of `m` first reaches `1` at step `k`. -/
def FirstHitsOne (k m : ℕ) : Prop :=
  collatzStep^[k] m = 1 ∧ ∀ i < k, collatzStep^[i] m ≠ 1

/-- `FirstHitsOne k m` is decidable (finitely many iterates are inspected). -/
instance (k m : ℕ) : Decidable (FirstHitsOne k m) := by
  unfold FirstHitsOne; infer_instance

-- The orbit `20, 10, 5, 16, 8, 4, 2, 1` has `8 = 6 + 2` elements.
example : FirstHitsOne 7 20 := by decide
example : ¬ FirstHitsOne 7 40 := by decide
-- Level `7` is `{128, 21, 20, 3}` (checked on `x ≤ 130`), so `a 6 = 20` is third largest.
example : (List.range 131).filter (fun x => decide (FirstHitsOne 7 x)) = [3, 20, 21, 128] := by
  decide
-- Level `6` is `{64, 10}`: the hypothesis `6 ≤ n` is sharp.
example : (List.range 66).filter (fun x => decide (FirstHitsOne 6 x)) = [10, 64] := by
  decide

/-- Peeling one step off a first-hitting trajectory. -/
lemma firstHitsOne_succ {k m : ℕ} (h : FirstHitsOne (k + 1) m) :
    m ≠ 1 ∧ FirstHitsOne k (collatzStep m) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hm => h2 0 (Nat.succ_pos k) (by simpa using hm), ?_, ?_⟩
  · rwa [Function.iterate_succ_apply] at h1
  · intro i hi
    have hne := h2 (i + 1) (by omega)
    rwa [Function.iterate_succ_apply] at hne

/-- `2^k ≡ 1 (mod 3)` forces `k` even. -/
lemma even_of_two_pow_mod_three {k : ℕ} (h : 2 ^ k % 3 = 1) : Even k := by
  rcases Nat.even_or_odd k with hk | ⟨q, rfl⟩
  · exact hk
  · exfalso
    have h4 : 4 ^ q % 3 = 1 := by rw [Nat.pow_mod]; simp
    rw [pow_succ, pow_mul] at h
    norm_num at h
    omega

/-- Trichotomy for a Collatz level: an `m` first reaching `1` at step `k` is `2^k`,
or has exactly one `3x+1` step (`3m + 2^a = 2^(a+j)` with `j` even, `4 ≤ j`,
`k = a + j + 1`), or satisfies `36 m ≤ 2^k`. -/
theorem level_trichotomy (k : ℕ) : ∀ m : ℕ, FirstHitsOne k m →
    m = 2 ^ k ∨
    (∃ e j : ℕ, Even j ∧ 4 ≤ j ∧ k = e + j + 1 ∧ 3 * m + 2 ^ e = 2 ^ (e + j)) ∨
    36 * m ≤ 2 ^ k := by
  induction k with
  | zero =>
    intro m hm
    left
    simpa [FirstHitsOne] using hm.1
  | succ k ih =>
    intro m hm
    obtain ⟨hm1, hstep⟩ := firstHitsOne_succ hm
    rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have hT : collatzStep (t + t) = t := by
        unfold collatzStep; split_ifs <;> omega
      rw [hT] at hstep
      rcases ih t hstep with h | ⟨e, j, hj, hj4, hk, he⟩ | h
      · left; rw [h, pow_succ]; ring
      · right; left
        refine ⟨e + 1, j, hj, hj4, by omega, ?_⟩
        rw [show e + 1 + j = (e + j) + 1 by ring, pow_succ, pow_succ, ← he]; ring
      · right; right; rw [pow_succ]; omega
    · have hT : collatzStep (2 * t + 1) = 3 * (2 * t + 1) + 1 := by
        unfold collatzStep; split_ifs <;> omega
      rw [hT] at hstep
      have ht : 1 ≤ t := by omega
      rcases ih _ hstep with h | ⟨e, j, hj, hj4, hk, he⟩ | h
      · right; left
        have hmod : 2 ^ k % 3 = 1 := by omega
        have hk4 : 4 ≤ k := by
          by_contra hlt
          interval_cases k <;> omega
        exact ⟨0, k, even_of_two_pow_mod_three hmod, hk4, by omega, by simp [h]⟩
      · right; right
        have h4 : 2 ^ (k + 1) = 4 * 2 ^ (e + j) := by
          rw [hk, show e + j + 1 + 1 = (e + j) + 2 by ring, pow_add]; ring
        have hpos : 0 < 2 ^ e := by positivity
        omega
      · right; right; rw [pow_succ]; omega

/-- Even exponents give `2^j ≡ 1 (mod 3)`. -/
lemma two_pow_mod_three_of_even {j : ℕ} (hj : Even j) : 2 ^ j % 3 = 1 := by
  obtain ⟨q, rfl⟩ := hj
  rw [← two_mul, pow_mul, Nat.pow_mod]; simp

/-- Halving `i` times: `T^[i] (2^(i+d) c) = 2^d c`. -/
lemma iterate_two_pow_mul (d c : ℕ) : ∀ i : ℕ, collatzStep^[i] (2 ^ (i + d) * c) = 2 ^ d * c := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    have hT : collatzStep (2 ^ (i + 1 + d) * c) = 2 ^ (i + d) * c := by
      have h2 : 2 ^ (i + 1 + d) * c = 2 * (2 ^ (i + d) * c) := by
        rw [show i + 1 + d = (i + d) + 1 by ring, pow_succ]; ring
      rw [h2]; unfold collatzStep; simp
    rw [hT, ih]

/-- Powers of two reach `1` first at their exponent. -/
lemma firstHitsOne_two_pow (k : ℕ) : FirstHitsOne k (2 ^ k) := by
  refine ⟨by simpa using iterate_two_pow_mul 0 1 k, fun i hi => ?_⟩
  have h := iterate_two_pow_mul (k - i) 1 i
  rw [show i + (k - i) = k by omega, mul_one, mul_one] at h
  rw [h]
  have : 2 ≤ 2 ^ (k - i) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The one-`3x+1` elements: `2^e c` with `3c + 1 = 2^j`, `2 ≤ c`, reaches `1` first
at step `e + j + 1`. -/
lemma firstHitsOne_of_one_up (e j c : ℕ) (hc : 3 * c + 1 = 2 ^ j) (hc2 : 2 ≤ c) :
    FirstHitsOne (e + j + 1) (2 ^ e * c) := by
  have hodd : collatzStep c = 2 ^ j := by
    unfold collatzStep
    have : c % 2 = 1 := by
      rcases Nat.even_or_odd c with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · have hj : j ≠ 0 := by rintro rfl; omega
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        rw [pow_succ] at hc
        omega
      · omega
    simp [this, hc]
  have hhalf : collatzStep^[e] (2 ^ e * c) = c := by
    simpa using iterate_two_pow_mul 0 c e
  have hup : ∀ l, collatzStep^[l + 1 + e] (2 ^ e * c) = collatzStep^[l] (2 ^ j) := by
    intro l
    rw [Function.iterate_add_apply, hhalf, Function.iterate_succ_apply, hodd]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [show e + j + 1 = j + 1 + e by ring, hup]
    exact (firstHitsOne_two_pow j).1
  · by_cases hie : i ≤ e
    · have h := iterate_two_pow_mul (e - i) c i
      rw [show i + (e - i) = e by omega] at h
      rw [h]
      have : 1 ≤ 2 ^ (e - i) := Nat.one_le_two_pow
      nlinarith
    · obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 + e := ⟨i - 1 - e, by omega⟩
      rw [hup]
      exact (firstHitsOne_two_pow j).2 l (by omega)


/-- The top of a Collatz level.  Let `e₁ ∈ {0, 1}`, `j` even with `4 ≤ j`,
`k = e₁ + j + 3`, `3 c₀ + 1 = 2^j` and `3 c₁ + 1 = 2^(j+2)`.  Then
`m = 2^(e₁+2) c₀` reaches `1` first at step `k`, and the elements of that level
exceeding `m` are exactly `2^k` and `2^e₁ c₁`. -/
theorem level_top (e₁ j c₀ c₁ : ℕ) (he₁ : e₁ ≤ 1) (hj : Even j) (hj4 : 4 ≤ j)
    (hc₀ : 3 * c₀ + 1 = 2 ^ j) (hc₁ : 3 * c₁ + 1 = 2 ^ (j + 2)) :
    FirstHitsOne (e₁ + j + 3) (2 ^ (e₁ + 2) * c₀) ∧
    {x : ℕ | FirstHitsOne (e₁ + j + 3) x ∧ 2 ^ (e₁ + 2) * c₀ < x} =
      {2 ^ (e₁ + j + 3), 2 ^ e₁ * c₁} := by
  have h16 : 16 ≤ 2 ^ j := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj4
  have hc₀2 : 2 ≤ c₀ := by omega
  have hpj : 2 ^ (j + 2) = 4 * 2 ^ j := by rw [pow_add]; ring
  have hc₁2 : 2 ≤ c₁ := by omega
  have hpe : 2 ^ (e₁ + 2) = 4 * 2 ^ e₁ := by rw [pow_add]; ring
  have hk1 : 2 ^ (e₁ + j + 3) = 2 * 2 ^ (e₁ + (j + 2)) := by
    rw [show e₁ + j + 3 = (e₁ + (j + 2)) + 1 by ring, pow_succ]; ring
  have hm : 3 * (2 ^ (e₁ + 2) * c₀) + 2 ^ (e₁ + 2) = 2 ^ (e₁ + (j + 2)) := by
    rw [show e₁ + (j + 2) = (e₁ + 2) + j by ring, pow_add (2 : ℕ) (e₁ + 2) j, ← hc₀]; ring
  have hb : 3 * (2 ^ e₁ * c₁) + 2 ^ e₁ = 2 ^ (e₁ + (j + 2)) := by
    rw [pow_add (2 : ℕ) e₁ (j + 2), ← hc₁]; ring
  have he₁pos : 1 ≤ 2 ^ e₁ := Nat.one_le_two_pow
  have he₁le : 2 ^ e₁ ≤ 2 := by
    calc 2 ^ e₁ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) he₁
      _ = 2 := by norm_num
  refine ⟨?_, ?_⟩
  · have := firstHitsOne_of_one_up (e₁ + 2) j c₀ hc₀ hc₀2
    rwa [show e₁ + 2 + j + 1 = e₁ + j + 3 by ring] at this
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hmx⟩
      rcases level_trichotomy _ x hx with h | ⟨e, j', hj', hj'4, hk, he⟩ | h
      · left; exact h
      · right
        have hsum : e + j' = e₁ + (j + 2) := by omega
        rw [hsum] at he
        have hlt : 2 ^ e < 2 ^ (e₁ + 2) := by omega
        have hlt' : e < e₁ + 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
        have hee : e = e₁ := by
          obtain ⟨u, hu⟩ := hj
          obtain ⟨u', hu'⟩ := hj'
          omega
        subst hee
        omega
      · exfalso
        rw [hk1] at h
        omega
    · rintro (rfl | rfl)
      · exact ⟨firstHitsOne_two_pow _, by omega⟩
      · refine ⟨?_, by omega⟩
        have := firstHitsOne_of_one_up e₁ (j + 2) c₁ hc₁ hc₁2
        rwa [show e₁ + (j + 2) + 1 = e₁ + j + 3 by ring] at this


/-- **Sigg's conjecture (A153772, Markus Sigg, Sep 14 2020).** For `n ≥ 6`,
`a(n) = (2^n + 2(-1)^n - 6)/3` is the third largest positive integer whose Collatz
orbit has `n + 2` elements, i.e. whose trajectory first reaches `1` after exactly
`n + 1` steps: `a(n)` is a natural number `m` in that level and exactly two
elements of the level exceed it. -/
theorem a153772_third_largest (n : ℕ) (hn : 6 ≤ n) :
    ∃ m : ℕ, (m : ℤ) = a n ∧ FirstHitsOne (n + 1) m ∧
      {x : ℕ | FirstHitsOne (n + 1) x ∧ m < x}.ncard = 2 := by
  obtain ⟨e₁, j, he₁, hj, hj4, hnj⟩ :
      ∃ e₁ j : ℕ, e₁ ≤ 1 ∧ Even j ∧ 4 ≤ j ∧ n = e₁ + j + 2 := by
    rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact ⟨0, n - 2, le_refl _ |>.trans (by norm_num), ⟨q - 1, by omega⟩, by omega, by omega⟩
    · exact ⟨1, n - 3, le_refl _, ⟨q - 1, by omega⟩, by omega, by omega⟩
  have hj2 : Even (j + 2) := hj.add even_two
  have hmod₀ := two_pow_mod_three_of_even hj
  have hmod₁ := two_pow_mod_three_of_even hj2
  have hpos₀ : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hpos₁ : 1 ≤ 2 ^ (j + 2) := Nat.one_le_two_pow
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, 3 * c₀ + 1 = 2 ^ j := ⟨(2 ^ j - 1) / 3, by omega⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℕ, 3 * c₁ + 1 = 2 ^ (j + 2) := ⟨(2 ^ (j + 2) - 1) / 3, by omega⟩
  obtain ⟨hmem, hset⟩ := level_top e₁ j c₀ c₁ he₁ hj hj4 hc₀ hc₁
  have hk : n + 1 = e₁ + j + 3 := by omega
  refine ⟨2 ^ (e₁ + 2) * c₀, ?_, hk ▸ hmem, ?_⟩
  · -- `2^n = 2^(e₁+2) (3 c₀ + 1)` and `(-1)^n = (-1)^e₁`
    have hpow : (2 : ℤ) ^ n = 2 ^ (e₁ + 2) * (3 * c₀ + 1) := by
      rw [hnj, show e₁ + j + 2 = (e₁ + 2) + j by ring, pow_add]
      exact_mod_cast congrArg (fun t : ℕ => (2 : ℤ) ^ (e₁ + 2) * t) hc₀.symm
    have hsign : (-1 : ℤ) ^ n = (-1) ^ e₁ := by
      rw [hnj, add_assoc, pow_add, hj2.neg_one_pow, mul_one]
    have hnum : (2 : ℤ) ^ n + 2 * (-1) ^ n - 6 = 3 * ((2 ^ (e₁ + 2) * c₀ : ℕ) : ℤ) := by
      rw [hpow, hsign]
      push_cast
      interval_cases e₁ <;> ring
    unfold a
    rw [hnum, Int.mul_ediv_cancel_left _ (by norm_num)]
  · rw [hk, hset, Set.ncard_pair]
    have hc₁lt : c₁ < 2 ^ (j + 2) := by omega
    have hlt : 2 ^ e₁ * c₁ < 2 ^ (e₁ + j + 3) :=
      calc 2 ^ e₁ * c₁ < 2 ^ e₁ * 2 ^ (j + 2) :=
            Nat.mul_lt_mul_of_pos_left hc₁lt (by positivity)
        _ = 2 ^ (e₁ + j + 2) := by rw [← pow_add, add_assoc]
        _ < 2 ^ (e₁ + j + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Candidates.A153772ThirdLargestPositive
