/-
# A248667 — Kurkov: every composite term is a product of two terms > 1

Mikhail Kurkov's conjecture in OEIS A248667 says that every composite term
is a product of two terms greater than one. Membership means that the
coefficients of the numerator polynomial `p(n,x)` are relatively prime.
Peter J. Taylor characterizes this as `gcd(n,A000522(n-1)) = 1`.
His stated top coefficient `n^n` is a slip: it is `n^(n-1)`; the bridge
below does not use that coefficient.

The polynomial is the numerator of
`1 + 1/(nx+1) + … + 1/((nx+1)⋯(nx+n-1))` over the denominator
`(nx+1)⋯(nx+n-1)`, equivalently
`p(n,x) = Σ_{j=0}^{n-1} ∏_{i=1}^{j} (nx+n-i)`.

## Proof

1. (`inA248667_iff_coprime`, Taylor's comment, proved.)  Modulo a prime `q`,
   `p(k,x)` is the constant `A000522(k-1)` when `q ∣ k`; when `q ∤ k`, its
   reduction takes the value `1` at the root `x = (1-k)/k` of the factor
   `k x + k - 1` (every product with `j ≥ 1` contains this factor), so it is
   nonzero.  Hence the content of `p(k,x)` is `1` iff `gcd(k, A000522(k-1)) = 1`.
2. (`a000522_mul_add`.)  `A000522(m) = m A000522(m-1) + 1` resets to `1`
   modulo `q` at every multiple of `q`, so `A000522(q t + r) ≡ A000522(r)`.
3. (`inA248667_iff_forall_prime`.)  So `k` is a term iff no prime `q ∣ k`
   divides `A000522(q - 1)`; in particular the terms are closed under divisors
   (`InA248667.of_dvd`).
4. (`kurkov_conjecture`.)  A composite term `k` is `q * (k / q)` with
   `q = minFac k`, and both factors are terms greater than `1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A248667CoefficientsCoprimeTaylor

open Polynomial

/-! ## Definitions -/

/-- OEIS A000522 (total number of arrangements of an `m`-set,
`a(m) = ∑_{j=0}^{m} m!/j!`), defined by its recurrence `a(0) = 1`,
`a(m+1) = (m+1) a(m) + 1`; `a000522_eq_sum_descFactorial` proves agreement
with the defining sum. -/
def a000522 : ℕ → ℕ
  | 0 => 1
  | m + 1 => (m + 1) * a000522 m + 1

/-- the first terms of A000522 are `1, 2, 5, 16, 65, 326, 1957, 13700`. -/
example : (List.range 8).map a000522 = [1, 2, 5, 16, 65, 326, 1957, 13700] := by decide

/-- The recurrence agrees with the A000522 definition
`a(m) = ∑_{j=0}^{m} m!/j! = ∑_{j=0}^{m} m!/(m-j)!`, written with descending
factorials `m!/(m-j)! = m.descFactorial j`. -/
theorem a000522_eq_sum_descFactorial (m : ℕ) :
    a000522 m = ∑ j ∈ Finset.range (m + 1), m.descFactorial j := by
  induction m with
  | zero => simp [a000522]
  | succ m ih =>
    rw [Finset.sum_range_succ', a000522, ih, Finset.mul_sum]
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero]

/-- The polynomial `p(n,x)` of A248664/A248667, exactly as in the entry's
Mathematica program: `p(n,x) = ∑_{j=0}^{n-1} ∏_{i=1}^{j} (n x + n - i)`, with
integer coefficients.  This is the numerator of
`1 + 1/(nx+1) + … + 1/((nx+1)⋯(nx+n-1))` over the denominator
`(nx+1)⋯(nx+n-1)`. -/
noncomputable def p (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range n, ∏ i ∈ Finset.Icc 1 j, (C (n : ℤ) * X + C ((n : ℤ) - i))

/-- `p(2,x) = 2x + 2` (coefficient gcd `2`, so `2 ∉ A248667`). -/
example : p 2 = C 2 * X + C 2 := by
  simp only [p, Nat.cast_ofNat, eq_intCast, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Order.lt_one_iff,
    Finset.Icc_eq_empty_of_lt, Finset.prod_empty, Finset.Icc_self, Finset.prod_singleton,
    Nat.cast_one]
  ring

/-- `p(3,x) = 9x^2 + 12x + 5` (coefficient gcd `1`). -/
example : p 3 = C 9 * X ^ 2 + C 12 * X + C 5 := by
  simp only [p, Nat.cast_ofNat, eq_intCast, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Order.lt_one_iff,
    Finset.Icc_eq_empty_of_lt, Finset.prod_empty, Finset.Icc_self, Finset.prod_singleton,
    Nat.cast_one, Nat.reduceAdd, Nat.one_le_ofNat, Finset.prod_Icc_succ_top]
  ring

/-! ## Constant coefficient and periodicity of A000522 -/

/-- `∏_{i=1}^{j} ((n+1) - i) = n (n-1) ⋯ (n-j+1) = n.descFactorial j` in `ℤ`
(both sides vanish once `j > n`). -/
theorem prod_Icc_sub_eq_descFactorial (n j : ℕ) :
    ∏ i ∈ Finset.Icc 1 j, (((n + 1 : ℕ) : ℤ) - i) = (n.descFactorial j : ℤ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.descFactorial_succ]
    rcases lt_or_ge n j with h | h
    · rw [(Nat.descFactorial_eq_zero_iff_lt).2 h]
      simp
    · push_cast [h]
      ring

/-- Periodicity of A000522: `A000522(q t + r) ≡ A000522(r) (mod q)`, because
the recurrence `a(m) = m a(m-1) + 1` resets to `1` at each multiple of `q`. -/
theorem a000522_mul_add (q t r : ℕ) :
    (a000522 (q * t + r) : ZMod q) = a000522 r := by
  induction r with
  | zero =>
    rcases Nat.eq_zero_or_pos (q * t) with h | h
    · simp [h]
    · obtain ⟨m, hm⟩ : ∃ m, q * t = m + 1 := ⟨q * t - 1, by omega⟩
      have hcast : ((m + 1 : ℕ) : ZMod q) = 0 := by
        rw [← hm, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      rw [Nat.add_zero, hm]
      simp only [a000522]
      push_cast at hcast ⊢
      rw [hcast]
      ring
  | succ r ih =>
    rw [← Nat.add_assoc, a000522, a000522]
    push_cast
    rw [ih, ZMod.natCast_self]
    ring


/-- The value of `p(n+1, x)` at `x = 0` (its constant coefficient) is
`A000522(n)`: `∑_{j=0}^{n} ∏_{i=1}^{j} ((n+1) - i) = A000522(n)`. -/
theorem sum_prod_eq_a000522 (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ∏ i ∈ Finset.Icc 1 j, (((n + 1 : ℕ) : ℤ) - i) =
      (a000522 n : ℤ) := by
  simp only [prod_Icc_sub_eq_descFactorial, a000522_eq_sum_descFactorial]
  push_cast
  rfl

/-! ## Reduction of `p(k,x)` modulo a prime -/

/-- If `q ∣ k` (with `k ≥ 1`), then `p(k,x)` reduced modulo `q` is the constant
`A000522(k-1)`: the terms `k x` all vanish. -/
theorem map_p_of_dvd (q k : ℕ) (hk : 1 ≤ k) (hqk : q ∣ k) :
    (p k).map (Int.castRingHom (ZMod q)) = C ((a000522 (k - 1) : ℕ) : ZMod q) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hk0 : (Int.castRingHom (ZMod q)) ((n + 1 : ℕ) : ℤ) = 0 := by
    rw [eq_intCast, Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hqk
  calc (p (n + 1)).map (Int.castRingHom (ZMod q))
      = ∑ j ∈ Finset.range (n + 1), ∏ i ∈ Finset.Icc 1 j,
          C ((Int.castRingHom (ZMod q)) (((n + 1 : ℕ) : ℤ) - i)) := by
        simp only [p, Polynomial.map_sum, Polynomial.map_prod]
        refine Finset.sum_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
          Polynomial.map_X, hk0, C_0, zero_mul, zero_add]
    _ = C ((Int.castRingHom (ZMod q))
          (∑ j ∈ Finset.range (n + 1), ∏ i ∈ Finset.Icc 1 j, (((n + 1 : ℕ) : ℤ) - i))) := by
        simp only [map_sum, map_prod]
    _ = C ((a000522 (n + 1 - 1) : ℕ) : ZMod q) := by
        rw [sum_prod_eq_a000522, Nat.add_sub_cancel, eq_intCast, Int.cast_natCast]

/-- If `q` is a prime not dividing `k ≥ 1`, then `p(k,x)` reduced modulo `q`
is nonzero: at `x = (1-k)/k` every product with `j ≥ 1` contains the vanishing
factor `k x + k - 1`, so the value is the `j = 0` term `1`. -/
theorem map_p_ne_zero_of_not_dvd (q k : ℕ) [hq : Fact q.Prime] (hk : 1 ≤ k) (hqk : ¬ q ∣ k) :
    (p k).map (Int.castRingHom (ZMod q)) ≠ 0 := by
  have hk0 : ((k : ℕ) : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set x : ZMod q := (1 - (k : ZMod q)) * (k : ZMod q)⁻¹ with hx
  have hroot : (k : ZMod q) * x + ((k : ZMod q) - 1) = 0 := by
    rw [hx, mul_comm, mul_assoc, inv_mul_cancel₀ hk0]
    ring
  intro h
  have heval := congrArg (Polynomial.eval x) h
  rw [eval_zero] at heval
  simp only [p, Polynomial.map_sum, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_X, eq_intCast, Int.cast_natCast, eval_finsetSum,
    eval_prod, eval_add, eval_mul, eval_X, Int.cast_sub] at heval
  rw [Finset.sum_eq_single 0] at heval
  · simp at heval
  · intro j _ hj
    apply Finset.prod_eq_zero (i := 1)
    · simp only [Finset.mem_Icc, Std.le_refl, true_and]
      omega
    · simpa using hroot
  · intro h0
    simp only [Finset.mem_range, not_lt, nonpos_iff_eq_zero] at h0
    omega


/-- An integer polynomial reduces to `0` modulo `q` iff `q` divides all its
coefficients. -/
theorem map_eq_zero_iff_C_dvd (f : ℤ[X]) (q : ℕ) :
    f.map (Int.castRingHom (ZMod q)) = 0 ↔ C (q : ℤ) ∣ f := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  simp only [coeff_map, eq_intCast, coeff_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The coefficients of an integer polynomial have gcd `1` iff its reduction
modulo every prime is nonzero. -/
theorem content_eq_one_iff (f : ℤ[X]) :
    f.content = 1 ↔ ∀ q : ℕ, q.Prime → f.map (Int.castRingHom (ZMod q)) ≠ 0 := by
  constructor
  · intro h q hq hmap
    rw [map_eq_zero_iff_C_dvd, ← dvd_content_iff_C_dvd, h] at hmap
    have h1 : q ∣ 1 := by exact_mod_cast hmap
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)
  · intro h
    rw [← isPrimitive_iff_content_eq_one]
    intro r hr
    by_contra hu
    rw [Int.isUnit_iff_natAbs_eq] at hu
    obtain ⟨q, hq, hqr⟩ := Nat.exists_prime_and_dvd hu
    apply h q hq
    rw [map_eq_zero_iff_C_dvd]
    exact (C_dvd_iff_dvd_coeff _ _).2 fun i =>
      (Int.natCast_dvd.2 hqr).trans ((C_dvd_iff_dvd_coeff _ _).1 hr i)


/-! ## The sequence and Taylor's characterization -/

/-- `k` is a term of A248667: `k ≥ 1` and the coefficients of `p(k,x)` are
relatively prime (their gcd, `Polynomial.content`, is `1`; this gcd is
A248666). -/
def InA248667 (k : ℕ) : Prop := 1 ≤ k ∧ (p k).content = 1

/-- **Taylor's comment (Apr 08 2022), proved.**  `k` is a term iff
`k ≥ 1` and `gcd(k, A000522(k-1)) = 1`. -/
theorem inA248667_iff_coprime (k : ℕ) :
    InA248667 k ↔ 1 ≤ k ∧ Nat.Coprime k (a000522 (k - 1)) := by
  refine and_congr_right fun hk => ?_
  rw [content_eq_one_iff]
  constructor
  · intro h
    refine Nat.coprime_of_dvd fun q hq hqk hqa => h q hq ?_
    rw [map_p_of_dvd q k hk hqk, C_eq_zero, ZMod.natCast_eq_zero_iff]
    exact hqa
  · intro hcop q hq
    haveI : Fact q.Prime := ⟨hq⟩
    by_cases hqk : q ∣ k
    · rw [map_p_of_dvd q k hk hqk, Ne, C_eq_zero, ZMod.natCast_eq_zero_iff]
      intro hqa
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqk hcop) hqa)
    · exact map_p_ne_zero_of_not_dvd q k hk hqk

/-- For a prime `q ∣ k` with `k ≥ 1`, `A000522(k-1) ≡ A000522(q-1) (mod q)`. -/
theorem a000522_pred_cast_of_dvd (q k : ℕ) (hq : q.Prime) (hk : 1 ≤ k) (hqk : q ∣ k) :
    (a000522 (k - 1) : ZMod q) = a000522 (q - 1) := by
  obtain ⟨t, rfl⟩ := hqk
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; omega
    · exact h
  have hsplit : q * t - 1 = q * (t - 1) + (q - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have := hq.one_lt
    rw [Nat.add_sub_cancel, Nat.mul_succ]
    omega
  rw [hsplit, a000522_mul_add]

/-- `k` is a term iff `k ≥ 1` and no prime factor `q` of `k` divides
`A000522(q-1)`. -/
theorem inA248667_iff_forall_prime (k : ℕ) :
    InA248667 k ↔ 1 ≤ k ∧ ∀ q : ℕ, q.Prime → q ∣ k → ¬ q ∣ a000522 (q - 1) := by
  rw [inA248667_iff_coprime]
  refine and_congr_right fun hk => ?_
  have key : ∀ q : ℕ, q.Prime → q ∣ k → (q ∣ a000522 (k - 1) ↔ q ∣ a000522 (q - 1)) := by
    intro q hq hqk
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff,
      a000522_pred_cast_of_dvd q k hq hk hqk]
  constructor
  · intro hcop q hq hqk hqa
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqk hcop)
      ((key q hq hqk).2 hqa))
  · intro h
    exact Nat.coprime_of_dvd fun q hq hqk hqa => h q hq hqk ((key q hq hqk).1 hqa)

/-- The terms of A248667 are closed under taking divisors. -/
theorem InA248667.of_dvd {k d : ℕ} (hk : InA248667 k) (hd : d ∣ k) : InA248667 d := by
  rw [inA248667_iff_forall_prime] at hk ⊢
  obtain ⟨hk1, hkq⟩ := hk
  refine ⟨Nat.pos_of_dvd_of_pos hd hk1, fun q hq hqd => hkq q hq (hqd.trans hd)⟩

/-! ## The conjecture -/

/-- **Kurkov's conjecture (A248667, Mikhail Kurkov), proved.**

Since `a(1) = 1` and the sequence is strictly increasing, the terms `a(i)` with
`i > 1` are exactly the terms greater than `1`; so the claim is: every
composite term `k` (`1 < k`, not prime) is `a * b` with `a`, `b` terms of
A248667 and `1 < a`, `1 < b`.  Here the terms are the polynomial-coefficient
definition `InA248667` of the entry's name. -/
theorem kurkov_conjecture (k : ℕ) (hk : InA248667 k) (h1 : 1 < k) (hnp : ¬ k.Prime) :
    ∃ a b : ℕ, InA248667 a ∧ InA248667 b ∧ 1 < a ∧ 1 < b ∧ a * b = k := by
  have hq : k.minFac.Prime := Nat.minFac_prime h1.ne'
  have hdvd : k.minFac ∣ k := Nat.minFac_dvd k
  have hmul : k.minFac * (k / k.minFac) = k := Nat.mul_div_cancel' hdvd
  have hcof : 1 < k / k.minFac := by
    rcases Nat.lt_or_ge 1 (k / k.minFac) with h | h
    · exact h
    · exfalso
      interval_cases hc : k / k.minFac
      · rw [Nat.mul_zero] at hmul; omega
      · rw [Nat.mul_one] at hmul; exact hnp (hmul ▸ hq)
  exact ⟨k.minFac, k / k.minFac, hk.of_dvd hdvd, hk.of_dvd (Nat.div_dvd_of_dvd hdvd),
    hq.one_lt, hcof, hmul⟩


/-! ## Examples -/

/-- The 60 terms listed in the OEIS DATA line of A248667 (all terms `< 168`). -/
def listedTerms : List ℕ :=
  [1, 3, 7, 9, 11, 17, 19, 21, 23, 27, 29, 31, 33, 41, 43, 47, 49, 51, 53, 57, 59, 61, 63, 67, 69,
    71, 73, 77, 79, 81, 83, 87, 89, 93, 97, 99, 101, 103, 107, 109, 113, 119, 121, 123, 127, 129,
    131, 133, 137, 139, 141, 147, 149, 151, 153, 157, 159, 161, 163, 167]

/-- The coprimality form selects exactly the listed terms below `168`. -/
theorem coprime_filter_eq_listedTerms :
    (List.range 168).filter (fun k => decide (1 ≤ k ∧ Nat.Coprime k (a000522 (k - 1)))) =
      listedTerms := by
  decide


/-- below `168`, the terms of A248667 (polynomial definition)
are exactly the 60 terms of the OEIS DATA line. -/
theorem inA248667_iff_mem_listedTerms (k : ℕ) (hk : k < 168) :
    InA248667 k ↔ k ∈ listedTerms := by
  rw [inA248667_iff_coprime, ← coprime_filter_eq_listedTerms, List.mem_filter,
    List.mem_range, decide_eq_true_iff]
  exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩

/-- `2` is not a term (`p(2,x) = 2x + 2`). -/
example : ¬ InA248667 2 := by
  rw [inA248667_iff_mem_listedTerms 2 (by norm_num)]
  decide

/-- Non-vacuity: `9` satisfies every hypothesis of `kurkov_conjecture`. -/
example : InA248667 9 ∧ 1 < 9 ∧ ¬ Nat.Prime 9 :=
  ⟨(inA248667_iff_mem_listedTerms 9 (by norm_num)).2 (by decide), by norm_num, by norm_num⟩

end Candidates.A248667CoefficientsCoprimeTaylor
