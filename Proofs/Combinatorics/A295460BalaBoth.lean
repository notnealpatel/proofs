/-
# A295460 — Bala: half- and quarter-integer values of a(n) are integers

## OEIS source (pulled with `oeis show A295460`, retrieved 2026-10-21)

```
NAME:     a(n) = (30*n)!*(3*n)!*(2*n)!/((15*n)!*(10*n)!*(6*n)!*(4*n)!).
TERMS:    1,38818159380,11536562100925275834420,
          3989159479106945583885404912116080, ...
FORMULA:  a(n) = binomial(30*n,15*n)*binomial(15*n,5*n)*binomial(2*n,n)/
          (binomial(6*n,n)*binomial(4*n,n)). - _Chai Wah Wu_, Feb 16 2026
COMMENT (the conjecture, verbatim):
  Conjecture: for n >= 0, both a(n/2) = (15*n)!*(3*n/2)!*(n)! /
  ((15*n/2)!*(5*n)!*(3*n)!*(2*n)!) and a(n/4) = (15*n/2)!*(3*n/4)!*(n/2)! /
  ((15*n/4)!*(5*n/2)!*(3*n/2)!*n!) are integers, where fractional factorials
  are defined using the Gamma function - for example, (3*n/2)! :=
  Gamma(3*n/2 + 1). - _Peter Bala_, Jul 29 2026
```

## Status

Triage status: open (no proof in the entry or in the literature as far as the
triage could tell; both expressions checked integral for `n ≤ 300`).  This
module re-checked integrality of the quadruple-factorial form for `n ≤ 1200`
and gives a complete kernel-checked proof of the conjecture (`conjecture`).

## Proof outline

* `x! := Γ(x + 1)` (`fact`).  Writing `q!!!! = ∏ {t ∈ [1, q] : t ≡ q (mod 4)} t`
  (`quadFact`), one has `Γ(q/4 + 1) = ρ(q mod 4) · q!!!! / 4^⌊q/4⌋` with a
  constant `ρ` depending only on `q mod 4`.  For the seven arguments of
  `a(n/4)` the residue constants and the powers of `4` cancel, so
  `a(n/4) = (30n)!!!!(3n)!!!!(2n)!!!! / ((15n)!!!!(10n)!!!!(6n)!!!!(4n)!!!!)`
  (`quarterExpr_eq`); and `a(n/2)` is `a(2n/4)` (`halfExpr_eq`).
* Odd primes `p`: `v_p(q!!!!) = ∑_i #{t ≡ q (mod 4), t ≤ q, p^i ∣ t}`, and for
  odd `m` this count is `⌊(q + e m)/(4m)⌋` with `e = (-q m) mod 4`.  With
  `j = ⌊60 n / m⌋` and `w = n m mod 4` every count becomes `⌊(c j + 60 e)/240⌋`,
  and a shifted Landau inequality (`key_floor`, four residues `w`) closes it.
* The prime `2`: explicit valuations `v_2((4k)!!!!) = 2k + v_2(k!)`,
  `v_2((4k+2)!!!!) = k + 1`, `v_2(odd!!!!) = 0`, by cases on `n mod 4`, with
  Legendre's formula and Landau's inequality for `n ≡ 0 (mod 4)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A295460BalaBoth

open Finset

/-! ## Definition layer -/

/-- The entry's sequence `a(n) = (30n)!(3n)!(2n)!/((15n)!(10n)!(6n)!(4n)!)` (natural-number
division; the quotient is exact, see `quarterExpr_four_mul` and `quarterExpr_int`). -/
def a (n : ℕ) : ℕ :=
  (30 * n).factorial * (3 * n).factorial * (2 * n).factorial /
    ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial * (4 * n).factorial)

example : a 0 = 1 := by decide
example : a 1 = 38818159380 := by decide

/-- The fractional factorial of the comment: `x! := Γ(x + 1)`. -/
noncomputable def fact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Bala's first expression `a(n/2) = (15n)!(3n/2)!n!/((15n/2)!(5n)!(3n)!(2n)!)`, with fractional
factorials given by the Gamma function. -/
noncomputable def halfExpr (n : ℕ) : ℝ :=
  fact (15 * n) * fact (3 * n / 2) * fact n /
    (fact (15 * n / 2) * fact (5 * n) * fact (3 * n) * fact (2 * n))

/-- Bala's second expression `a(n/4) = (15n/2)!(3n/4)!(n/2)!/((15n/4)!(5n/2)!(3n/2)!n!)`, with
fractional factorials given by the Gamma function. -/
noncomputable def quarterExpr (n : ℕ) : ℝ :=
  fact (15 * n / 2) * fact (3 * n / 4) * fact (n / 2) /
    (fact (15 * n / 4) * fact (5 * n / 2) * fact (3 * n / 2) * fact n)

/-- `fact` agrees with the factorial on natural numbers. -/
lemma fact_natCast (k : ℕ) : fact k = k.factorial := Real.Gamma_nat_eq_factorial k

/-- `fact` is positive on `[0, ∞)`; in particular every denominator in `halfExpr` and
`quarterExpr` is positive, so the real divisions there are never the junk value. -/
lemma fact_pos {x : ℝ} (hx : 0 ≤ x) : 0 < fact x :=
  Real.Gamma_pos_of_pos (by linarith)

/-- At `n = 4m` the second expression is the entry's `a(m)`, computed in `ℝ`. -/
lemma quarterExpr_four_mul (m : ℕ) : quarterExpr (4 * m) =
    ((30 * m).factorial * (3 * m).factorial * (2 * m).factorial : ℝ) /
      ((15 * m).factorial * (10 * m).factorial * (6 * m).factorial * (4 * m).factorial) := by
  have e : ∀ (c : ℕ) (x : ℝ), x = ((c * m : ℕ) : ℝ) → fact x = (c * m).factorial := by
    intro c x hx
    rw [hx, fact_natCast]
  unfold quarterExpr
  rw [e 30 _ (by push_cast; ring), e 3 _ (by push_cast; ring), e 2 _ (by push_cast; ring),
    e 15 _ (by push_cast; ring), e 10 _ (by push_cast; ring), e 6 _ (by push_cast; ring),
    e 4 _ (by push_cast; ring)]

/-- At `n = 2m` the first expression is the entry's `a(m)`, computed in `ℝ`. -/
lemma halfExpr_two_mul (m : ℕ) : halfExpr (2 * m) =
    ((30 * m).factorial * (3 * m).factorial * (2 * m).factorial : ℝ) /
      ((15 * m).factorial * (10 * m).factorial * (6 * m).factorial * (4 * m).factorial) := by
  have e : ∀ (c : ℕ) (x : ℝ), x = ((c * m : ℕ) : ℝ) → fact x = (c * m).factorial := by
    intro c x hx
    rw [hx, fact_natCast]
  unfold halfExpr
  rw [e 30 _ (by push_cast; ring), e 3 _ (by push_cast; ring), e 2 _ (by push_cast; ring),
    e 15 _ (by push_cast; ring), e 10 _ (by push_cast; ring), e 6 _ (by push_cast; ring),
    e 4 _ (by push_cast; ring)]

example : quarterExpr 4 = 38818159380 := by
  rw [show (4 : ℕ) = 4 * 1 from rfl, quarterExpr_four_mul]
  norm_num [Nat.factorial]

example : halfExpr 2 = 38818159380 := by
  rw [show (2 : ℕ) = 2 * 1 from rfl, halfExpr_two_mul]
  norm_num [Nat.factorial]

/-! ## Quadruple factorials and the Gamma bridge -/

/-- The index set `{t ∈ [1, q] : t ≡ q (mod 4)}` of the quadruple factorial of `q`. -/
def supp (q : ℕ) : Finset ℕ := (Icc 1 q).filter (fun t => t % 4 = q % 4)

/-- Quadruple factorial `q!!!! = ∏ {t ∈ [1, q] : t ≡ q (mod 4)} t`; empty product `1` at `q = 0`. -/
def quadFact (q : ℕ) : ℕ := ∏ t ∈ supp q, t


/-- Recursion `(q + 4)!!!! = (q + 4) · q!!!!`. -/
lemma quadFact_add_four (q : ℕ) : quadFact (q + 4) = (q + 4) * quadFact q := by
  have hset : (Icc 1 (q + 4)).filter (fun t => t % 4 = (q + 4) % 4) =
      insert (q + 4) ((Icc 1 q).filter (fun t => t % 4 = q % 4)) := by
    ext t
    simp only [mem_filter, mem_Icc, mem_insert]
    omega
  have hnot : q + 4 ∉ (Icc 1 q).filter (fun t => t % 4 = q % 4) := by
    simp only [mem_filter, mem_Icc]
    omega
  unfold quadFact supp
  rw [hset, prod_insert hnot]

/-- Quadruple factorials are positive. -/
lemma quadFact_pos (q : ℕ) : 0 < quadFact q :=
  prod_pos fun t ht => by
    simp only [supp, mem_filter, mem_Icc] at ht
    omega

/-- Base values: `r!!!! = max r 1` for `r < 4`. -/
lemma quadFact_lt_four (r : ℕ) (hr : r < 4) : quadFact r = max r 1 := by
  interval_cases r <;> decide

/-- Quarter-integer Gamma recursion: `Γ((4k+r)/4 + 1) · 4^k · r!!!! = Γ(r/4 + 1) · (4k+r)!!!!`. -/
lemma gamma_quarter_aux (k r : ℕ) :
    Real.Gamma (((4 * k + r : ℕ) : ℝ) / 4 + 1) * (4 : ℝ) ^ k * quadFact r =
      Real.Gamma ((r : ℝ) / 4 + 1) * quadFact (4 * k + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hq : 4 * (k + 1) + r = (4 * k + r) + 4 := by ring
    have hpos : (((4 * k + r : ℕ) : ℝ) / 4 + 1) ≠ 0 := by positivity
    rw [hq, quadFact_add_four]
    have hG : Real.Gamma ((((4 * k + r) + 4 : ℕ) : ℝ) / 4 + 1) =
        (((4 * k + r : ℕ) : ℝ) / 4 + 1) * Real.Gamma (((4 * k + r : ℕ) : ℝ) / 4 + 1) := by
      rw [← Real.Gamma_add_one hpos]
      congr 1
      push_cast
      ring
    rw [hG]
    push_cast at ih ⊢
    rw [pow_succ]
    linear_combination (((4 * k + r : ℝ)) + 4) * ih

/-- The residue constant `Γ((q mod 4)/4 + 1) / (q mod 4)!!!!`, depending only on `q mod 4`. -/
noncomputable def rho (q : ℕ) : ℝ := Real.Gamma (((q % 4 : ℕ) : ℝ) / 4 + 1) / quadFact (q % 4)

/-- `rho q` depends only on `q mod 4`. -/
lemma rho_congr {q q' : ℕ} (h : q % 4 = q' % 4) : rho q = rho q' := by
  unfold rho; rw [h]

/-- `rho q = 1` when `4 ∣ q`. -/
lemma rho_zero_mod {q : ℕ} (h : q % 4 = 0) : rho q = 1 := by
  unfold rho; rw [h]; simp [quadFact, supp]

/-- `Γ(q/4 + 1) = rho q · q!!!! / 4^⌊q/4⌋` for every natural `q`. -/
lemma gamma_quarter (q : ℕ) :
    Real.Gamma ((q : ℝ) / 4 + 1) = rho q * quadFact q / (4 : ℝ) ^ (q / 4) := by
  have h := gamma_quarter_aux (q / 4) (q % 4)
  rw [Nat.div_add_mod] at h
  have h1 : (0 : ℝ) < quadFact (q % 4) := by exact_mod_cast quadFact_pos _
  have h2 : (0 : ℝ) < (4 : ℝ) ^ (q / 4) := by positivity
  unfold rho
  rw [div_mul_eq_mul_div, div_div, eq_div_iff (by positivity)]
  linear_combination h



/-- Gamma bridge: the second expression of the conjecture equals the rational number
`(30n)!!!!(3n)!!!!(2n)!!!! / ((15n)!!!!(10n)!!!!(6n)!!!!(4n)!!!!)`; the residue constants and
powers of `4` cancel for every `n`. -/
lemma quarterExpr_eq (n : ℕ) : quarterExpr n =
    ((quadFact (30 * n) * quadFact (3 * n) * quadFact (2 * n) : ℕ) : ℝ) /
      ((quadFact (15 * n) * quadFact (10 * n) * quadFact (6 * n) * quadFact (4 * n) : ℕ) : ℝ) := by
  have e : ∀ (c : ℕ) (x : ℝ), x = ((c * n : ℕ) : ℝ) / 4 →
      fact x = rho (c * n) * quadFact (c * n) / (4 : ℝ) ^ (c * n / 4) := by
    intro c x hx
    rw [fact, hx, gamma_quarter]
  unfold quarterExpr
  rw [e 30 _ (by push_cast; ring), e 3 _ (by push_cast; ring), e 2 _ (by push_cast; ring),
    e 15 _ (by push_cast; ring), e 10 _ (by push_cast; ring), e 6 _ (by push_cast; ring),
    e 4 _ (by push_cast; ring)]
  rw [rho_congr (q := 30 * n) (q' := 2 * n) (by omega), rho_congr (q := 15 * n) (q' := 3 * n) (by omega),
    rho_congr (q := 10 * n) (q' := 2 * n) (by omega), rho_congr (q := 6 * n) (q' := 2 * n) (by omega),
    rho_zero_mod (q := 4 * n) (by omega)]
  have hexp : 30 * n / 4 + 3 * n / 4 + 2 * n / 4 = 15 * n / 4 + 10 * n / 4 + 6 * n / 4 + 4 * n / 4 := by
    obtain ⟨s, rfl | rfl | rfl | rfl⟩ : ∃ s, n = 4 * s ∨ n = 4 * s + 1 ∨ n = 4 * s + 2 ∨ n = 4 * s + 3 :=
      ⟨n / 4, by omega⟩ <;> omega
  have hr2 : 0 < rho (2 * n) := by
    unfold rho
    have hG := Real.Gamma_pos_of_pos (s := (((2 * n) % 4 : ℕ) : ℝ) / 4 + 1) (by positivity)
    have hQ := quadFact_pos ((2 * n) % 4)
    positivity
  have hr3 : 0 < rho (3 * n) := by
    unfold rho
    have hG := Real.Gamma_pos_of_pos (s := (((3 * n) % 4 : ℕ) : ℝ) / 4 + 1) (by positivity)
    have hQ := quadFact_pos ((3 * n) % 4)
    positivity
  have h4 : (4 : ℝ) ^ (30 * n / 4) * 4 ^ (3 * n / 4) * 4 ^ (2 * n / 4) =
      4 ^ (15 * n / 4) * 4 ^ (10 * n / 4) * 4 ^ (6 * n / 4) * 4 ^ (4 * n / 4) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, hexp]
  have hq := fun q => (Nat.cast_pos (α := ℝ)).2 (quadFact_pos q)
  have hq15 := hq (15 * n); have hq10 := hq (10 * n); have hq6 := hq (6 * n); have hq4 := hq (4 * n)
  push_cast
  field_simp
  linear_combination (-((quadFact (30 * n) : ℝ) * quadFact (3 * n) * quadFact (2 * n))) * h4

/-- `v_p(t) = #{i ∈ [1, K) : p^i ∣ t}` for `0 < t ≤ K`. -/
lemma factorization_eq_card_Ico {p t K : ℕ} (pp : p.Prime) (ht : 0 < t) (htK : t ≤ K) :
    t.factorization p = #{i ∈ Ico 1 K | p ^ i ∣ t} := by
  rw [Nat.factorization_eq_card_pow_dvd t pp]
  congr 1
  ext i
  simp only [mem_filter, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by omega⟩, h3⟩
  · rintro ⟨⟨h1, _⟩, h3⟩
    have hle : p ^ i ≤ t := Nat.le_of_dvd ht h3
    have hlt : i < p ^ i := Nat.lt_pow_self pp.one_lt
    exact ⟨⟨h1, by omega⟩, h3⟩

/-- Legendre-type formula: `v_p(q!!!!) = ∑_{1 ≤ i < K} #{t ∈ supp q : p^i ∣ t}` for `q ≤ K`. -/
lemma quadFact_factorization {p q K : ℕ} (pp : p.Prime) (hqK : q ≤ K) :
    (quadFact q).factorization p = ∑ i ∈ Ico 1 K, #{t ∈ supp q | p ^ i ∣ t} := by
  have hne : ∀ t ∈ supp q, t ≠ 0 := by
    intro t ht
    simp only [supp, mem_filter, mem_Icc] at ht
    omega
  have h1 : (quadFact q).factorization p = ∑ t ∈ supp q, t.factorization p := by
    unfold quadFact
    rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  rw [h1]
  have h2 : ∀ t ∈ supp q, t.factorization p = ∑ i ∈ Ico 1 K, if p ^ i ∣ t then 1 else 0 := by
    intro t ht
    simp only [supp, mem_filter, mem_Icc] at ht
    rw [factorization_eq_card_Ico (K := K) pp (by omega) (by omega), card_filter]
  rw [sum_congr rfl h2, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [card_filter]

/-- `#{u ∈ [1, U] : u ≡ a (mod 4)} = ⌊(U + (4 - a) mod 4)/4⌋` for `a < 4`. -/
lemma card_mod_four (U a : ℕ) (ha : a < 4) :
    #{u ∈ Icc 1 U | u % 4 = a} = (U + (4 - a) % 4) / 4 := by
  induction U with
  | zero =>
    have : (Icc 1 0 : Finset ℕ) = ∅ := by decide
    rw [this, filter_empty, card_empty]
    omega
  | succ U ih =>
    have hset : Icc 1 (U + 1) = insert (U + 1) (Icc 1 U) := by
      ext t; simp only [mem_Icc, mem_insert]; omega
    have hnot : U + 1 ∉ Icc 1 U := by simp
    rw [hset, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (fun hm => hnot (mem_filter.1 hm).1), ih]
      omega
    · rw [ih]
      omega

/-- For odd `m`, `m u ≡ r (mod 4)` iff `u ≡ r m (mod 4)` (as `m² ≡ 1 (mod 4)`). -/
lemma mul_mod_four_iff {m u r : ℕ} (hm : m % 2 = 1) (hr : r < 4) :
    (m * u) % 4 = r ↔ u % 4 = (r * m) % 4 := by
  rw [Nat.mul_mod, Nat.mul_mod r]
  have hr' : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hr']
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  have hu : u % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases hm4 with h | h <;> rw [h] <;> interval_cases (u % 4) <;> interval_cases r <;> simp

/-- For odd `m`, the number of multiples of `m` in `supp q` is
`⌊(q + e m)/(4m)⌋` with `e = (-q m) mod 4`. -/
lemma card_dvd_supp {q m : ℕ} (hm : m % 2 = 1) :
    #{t ∈ supp q | m ∣ t} = (q + (4 - (q * m) % 4) % 4 * m) / (4 * m) := by
  have hm0 : 0 < m := by omega
  have hset : (supp q).filter (fun t => m ∣ t) =
      ((Icc 1 (q / m)).filter (fun u => (m * u) % 4 = q % 4)).map
        ⟨(m * ·), mul_right_injective₀ hm0.ne'⟩ := by
    ext t
    simp only [supp, mem_filter, mem_Icc, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨u, rfl⟩⟩
      refine ⟨u, ⟨⟨?_, ?_⟩, h3⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos u with hu | hu
        · subst hu; simp at h1
        · exact hu
      · exact (Nat.le_div_iff_mul_le hm0).2 (by rw [mul_comm]; exact h2)
    · rintro ⟨u, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      refine ⟨⟨⟨?_, ?_⟩, h3⟩, dvd_mul_right m u⟩
      · exact Nat.mul_pos hm0 h1
      · have hmu := (Nat.le_div_iff_mul_le hm0).1 h2
        rw [mul_comm]; exact hmu
  rw [hset, card_map]
  have hfilt : (Icc 1 (q / m)).filter (fun u => (m * u) % 4 = q % 4) =
      (Icc 1 (q / m)).filter (fun u => u % 4 = ((q % 4) * m) % 4) := by
    ext u
    simp only [mem_filter]
    rw [mul_mod_four_iff hm (Nat.mod_lt _ (by norm_num))]
  rw [hfilt, card_mod_four _ _ (Nat.mod_lt _ (by norm_num))]
  have hqm : (q % 4 * m) % 4 = (q * m) % 4 := by rw [Nat.mod_mul_mod]
  rw [hqm, ← Nat.add_mul_div_right _ _ hm0, Nat.div_div_eq_div_mul, mul_comm m 4]

/-- Floor reduction: with `j = ⌊A n / m⌋`, `⌊(c n + e m)/(B m)⌋ = ⌊(c j + A e)/(A B)⌋`
whenever `c ∣ A B` and `c ∣ A e`. This turns the count into a function of `j` alone. -/
lemma floor_reduce {A B c e n m : ℕ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) (hm : 0 < m)
    (hcAB : c ∣ A * B) (hcAe : c ∣ A * e) :
    (c * n + e * m) / (B * m) = (c * (A * n / m) + A * e) / (A * B) := by
  set j := A * n / m with hj
  set s := A * n % m with hs
  have hdiv : m * j + s = A * n := Nat.div_add_mod _ _
  have hslt : s < m := Nat.mod_lt _ hm
  set X := c * j + A * e with hX
  have hXdvd : c ∣ X % (A * B) := by
    have hcX : c ∣ X := dvd_add (dvd_mul_right c j) hcAe
    exact (Nat.dvd_mod_iff hcAB).2 hcX
  have hβ : X % (A * B) + c ≤ A * B := by
    obtain ⟨b, hb⟩ := hXdvd
    obtain ⟨g, hg⟩ := hcAB
    have hlt : X % (A * B) < A * B := Nat.mod_lt _ (Nat.mul_pos hA hB)
    rw [hb, hg] at hlt ⊢
    have hbg : b < g := lt_of_mul_lt_mul_left hlt (Nat.zero_le c)
    nlinarith
  have hnum : A * (c * n + e * m) = (A * B * m) * (X / (A * B)) + (X % (A * B) * m + c * s) := by
    have h1 : X = A * B * (X / (A * B)) + X % (A * B) := (Nat.div_add_mod _ _).symm
    have h2 : A * (c * n + e * m) = X * m + c * s := by
      rw [hX]
      nlinarith [hdiv]
    rw [h2]
    conv_lhs => rw [h1]
    ring
  have hlt : X % (A * B) * m + c * s < A * B * m := by
    have hcs : c * s < c * m := Nat.mul_lt_mul_of_pos_left hslt hc
    nlinarith
  rw [← Nat.mul_div_mul_left (c * n + e * m) (B * m) hA, hnum,
    show A * (B * m) = A * B * m by ring, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hlt, add_zero]

/-- The shifted Landau inequality behind the odd-prime case, for each residue `w = n m mod 4`,
checked over all `j` by `omega`. -/
lemma key_floor (w j : ℕ) (hw : w < 4) :
    (15 * j + 60 * ((4 - 15 * w % 4) % 4)) / 240 + (10 * j + 60 * ((4 - 10 * w % 4) % 4)) / 240 +
      (6 * j + 60 * ((4 - 6 * w % 4) % 4)) / 240 + (4 * j + 60 * ((4 - 4 * w % 4) % 4)) / 240 ≤
    (30 * j + 60 * ((4 - 30 * w % 4) % 4)) / 240 + (3 * j + 60 * ((4 - 3 * w % 4) % 4)) / 240 +
      (2 * j + 60 * ((4 - 2 * w % 4) % 4)) / 240 := by
  interval_cases w <;>
    simp only [Nat.reduceMul, Nat.reduceMod, Nat.reduceSub, Nat.mul_zero, Nat.add_zero] <;> omega

/-- The multiple count of an odd `m` in `supp (c n)`, written as a function of
`j = ⌊60 n / m⌋` and `w = n m mod 4`. -/
lemma cnt_eq (c n m : ℕ) (hm : m % 2 = 1) (hc0 : 0 < c) (hc : c ∣ 240)
    (hce : c ∣ 60 * ((4 - (c * ((n * m) % 4)) % 4) % 4)) :
    #{t ∈ supp (c * n) | m ∣ t} = (c * (60 * n / m) + 60 * ((4 - (c * ((n * m) % 4)) % 4) % 4)) / 240 := by
  rw [card_dvd_supp hm]
  have hmod : (c * n * m) % 4 = (c * ((n * m) % 4)) % 4 := by
    rw [mul_assoc, Nat.mul_mod_mod]
  rw [hmod, floor_reduce (A := 60) (B := 4) (by norm_num) (by norm_num) hc0 (by omega)
    (by norm_num; exact hc) hce]

/-- Odd primes: `v_p` of the denominator is at most `v_p` of the numerator. -/
lemma odd_prime_le (n p : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) :
    (quadFact (15 * n)).factorization p + (quadFact (10 * n)).factorization p +
        (quadFact (6 * n)).factorization p + (quadFact (4 * n)).factorization p ≤
      (quadFact (30 * n)).factorization p + (quadFact (3 * n)).factorization p +
        (quadFact (2 * n)).factorization p := by
  have hK : ∀ c, c ≤ 30 → c * n ≤ 30 * n + 1 := fun c hc => by nlinarith
  rw [quadFact_factorization pp (hK 15 (by norm_num)), quadFact_factorization pp (hK 10 (by norm_num)),
    quadFact_factorization pp (hK 6 (by norm_num)), quadFact_factorization pp (hK 4 (by norm_num)),
    quadFact_factorization pp (hK 30 (by norm_num)), quadFact_factorization pp (hK 3 (by norm_num)),
    quadFact_factorization pp (hK 2 (by norm_num))]
  simp only [← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have hm : p ^ i % 2 = 1 := Nat.odd_iff.1 ((pp.odd_of_ne_two hp2).pow)
  have hw : (n * p ^ i) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [cnt_eq 15 n _ hm (by norm_num) (by norm_num) (by omega),
    cnt_eq 10 n _ hm (by norm_num) (by norm_num) (by omega),
    cnt_eq 6 n _ hm (by norm_num) (by norm_num) (by omega),
    cnt_eq 4 n _ hm (by norm_num) (by norm_num) (by omega),
    cnt_eq 30 n _ hm (by norm_num) (by norm_num) (by interval_cases (n * p ^ i % 4) <;> omega),
    cnt_eq 3 n _ hm (by norm_num) (by norm_num) (by omega),
    cnt_eq 2 n _ hm (by norm_num) (by norm_num) (by omega)]
  exact key_floor _ _ hw

/-- `(4k)!!!! = 4^k · k!`. -/
lemma quadFact_four_mul (k : ℕ) : quadFact (4 * k) = 4 ^ k * k.factorial := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 * k + 4 by ring, quadFact_add_four, ih, Nat.factorial_succ, pow_succ]
    ring

/-- `v_2((4k)!!!!) = 2k + v_2(k!)`. -/
lemma v2_four_mul (k : ℕ) :
    (quadFact (4 * k)).factorization 2 = 2 * k + k.factorial.factorization 2 := by
  rw [quadFact_four_mul, Nat.factorization_mul (by positivity) (Nat.factorial_ne_zero k),
    Finsupp.add_apply, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.prime_two.factorization_self, smul_eq_mul, mul_one]

/-- `v_2(q!!!!) = 0` for odd `q`. -/
lemma v2_odd {q : ℕ} (hq : q % 2 = 1) : (quadFact q).factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  unfold quadFact
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  rintro ⟨t, ht, h2⟩
  simp only [supp, mem_filter, mem_Icc] at ht
  omega

/-- `v_2((4k+2)!!!!) = k + 1`. -/
lemma v2_four_mul_add_two (k : ℕ) : (quadFact (4 * k + 2)).factorization 2 = k + 1 := by
  induction k with
  | zero =>
    rw [show 4 * 0 + 2 = 2 by rfl, quadFact_lt_four 2 (by norm_num)]
    exact Nat.prime_two.factorization_self
  | succ k ih =>
    rw [show 4 * (k + 1) + 2 = (4 * k + 2) + 4 by ring, quadFact_add_four,
      Nat.factorization_mul (by omega) (quadFact_pos _).ne', Finsupp.add_apply, ih,
      show 4 * k + 2 + 4 = 2 * (2 * k + 3) by ring,
      Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
      Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by omega)]
    ring

/-- Landau's floor inequality for `a(n)`:
`⌊15s/m⌋ + ⌊10s/m⌋ + ⌊6s/m⌋ + ⌊4s/m⌋ ≤ ⌊30s/m⌋ + ⌊3s/m⌋ + ⌊2s/m⌋`. -/
lemma legendre_floor (s m : ℕ) (hm : 0 < m) :
    15 * s / m + 10 * s / m + 6 * s / m + 4 * s / m ≤ 30 * s / m + 3 * s / m + 2 * s / m := by
  have h : ∀ c, 0 < c → c ∣ 240 → c * s / m = c * (240 * s / m) / 240 := fun c hc hd => by
    have hfr := floor_reduce (A := 240) (B := 1) (c := c) (e := 0) (n := s) (m := m) (by norm_num)
      (by norm_num) hc hm (by simpa using hd) (by simp)
    simpa using hfr
  rw [h 15 (by norm_num) (by norm_num), h 10 (by norm_num) (by norm_num), h 6 (by norm_num) (by norm_num),
    h 4 (by norm_num) (by norm_num), h 30 (by norm_num) (by norm_num), h 3 (by norm_num) (by norm_num),
    h 2 (by norm_num) (by norm_num)]
  omega

/-- Legendre consequence: `v_p((15s)!(10s)!(6s)!(4s)!) ≤ v_p((30s)!(3s)!(2s)!)`. -/
lemma factorial_factorization_le (s p : ℕ) (pp : p.Prime) :
    (15 * s).factorial.factorization p + (10 * s).factorial.factorization p +
        (6 * s).factorial.factorization p + (4 * s).factorial.factorization p ≤
      (30 * s).factorial.factorization p + (3 * s).factorial.factorization p +
        (2 * s).factorial.factorization p := by
  have hb : ∀ c, c ≤ 30 → Nat.log p (c * s) < 30 * s + 1 := fun c hc =>
    lt_of_le_of_lt (Nat.log_le_self _ _) (by nlinarith)
  rw [Nat.factorization_factorial pp (hb 15 (by norm_num)), Nat.factorization_factorial pp (hb 10 (by norm_num)),
    Nat.factorization_factorial pp (hb 6 (by norm_num)), Nat.factorization_factorial pp (hb 4 (by norm_num)),
    Nat.factorization_factorial pp (hb 30 (by norm_num)), Nat.factorization_factorial pp (hb 3 (by norm_num)),
    Nat.factorization_factorial pp (hb 2 (by norm_num))]
  simp only [← sum_add_distrib]
  exact sum_le_sum fun i _ => legendre_floor s _ (pow_pos pp.pos i)

/-- The prime `2`, odd `n`. -/
lemma two_le_odd (n t : ℕ) (hn : n = 2 * t + 1) :
    (quadFact (15 * n)).factorization 2 + (quadFact (10 * n)).factorization 2 +
        (quadFact (6 * n)).factorization 2 + (quadFact (4 * n)).factorization 2 ≤
      (quadFact (30 * n)).factorization 2 + (quadFact (3 * n)).factorization 2 +
        (quadFact (2 * n)).factorization 2 := by
  rw [v2_odd (q := 15 * n) (by omega), v2_odd (q := 3 * n) (by omega),
    show 30 * n = 4 * (15 * t + 7) + 2 by omega, v2_four_mul_add_two (15 * t + 7),
    show 2 * n = 4 * t + 2 by omega, v2_four_mul_add_two t,
    show 10 * n = 4 * (5 * t + 2) + 2 by omega, v2_four_mul_add_two (5 * t + 2),
    show 6 * n = 4 * (3 * t + 1) + 2 by omega, v2_four_mul_add_two (3 * t + 1),
    show 4 * n = 4 * (2 * t + 1) by omega, v2_four_mul (2 * t + 1)]
  have h := Nat.factorization_factorial_le_div_pred Nat.prime_two (2 * t + 1)
  norm_num at h
  omega

/-- The prime `2`, `n ≡ 2 (mod 4)`. -/
lemma two_le_two_mod_four (n s : ℕ) (hn : n = 4 * s + 2) :
    (quadFact (15 * n)).factorization 2 + (quadFact (10 * n)).factorization 2 +
        (quadFact (6 * n)).factorization 2 + (quadFact (4 * n)).factorization 2 ≤
      (quadFact (30 * n)).factorization 2 + (quadFact (3 * n)).factorization 2 +
        (quadFact (2 * n)).factorization 2 := by
  rw [show 15 * n = 4 * (15 * s + 7) + 2 by omega, v2_four_mul_add_two (15 * s + 7),
    show 3 * n = 4 * (3 * s + 1) + 2 by omega, v2_four_mul_add_two (3 * s + 1),
    show 30 * n = 4 * (30 * s + 15) by omega, v2_four_mul (30 * s + 15),
    show 2 * n = 4 * (2 * s + 1) by omega, v2_four_mul (2 * s + 1),
    show 10 * n = 4 * (10 * s + 5) by omega, v2_four_mul (10 * s + 5),
    show 6 * n = 4 * (6 * s + 3) by omega, v2_four_mul (6 * s + 3),
    show 4 * n = 4 * (4 * s + 2) by omega, v2_four_mul (4 * s + 2)]
  have h1 := Nat.factorization_factorial_le_div_pred Nat.prime_two (4 * s + 2)
  norm_num at h1
  have hd : (10 * s + 5).factorial * (6 * s + 3).factorial ∣ (30 * s + 15).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial (by omega))
  have h2 := (Nat.factorization_le_iff_dvd (by positivity) (Nat.factorial_ne_zero _)).2 hd 2
  rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _), Finsupp.add_apply] at h2
  omega

/-- The prime `2`, `n ≡ 0 (mod 4)`. -/
lemma two_le_zero_mod_four (n s : ℕ) (hn : n = 4 * s) :
    (quadFact (15 * n)).factorization 2 + (quadFact (10 * n)).factorization 2 +
        (quadFact (6 * n)).factorization 2 + (quadFact (4 * n)).factorization 2 ≤
      (quadFact (30 * n)).factorization 2 + (quadFact (3 * n)).factorization 2 +
        (quadFact (2 * n)).factorization 2 := by
  rw [show 15 * n = 4 * (15 * s) by omega, v2_four_mul (15 * s),
    show 3 * n = 4 * (3 * s) by omega, v2_four_mul (3 * s),
    show 30 * n = 4 * (30 * s) by omega, v2_four_mul (30 * s),
    show 2 * n = 4 * (2 * s) by omega, v2_four_mul (2 * s),
    show 10 * n = 4 * (10 * s) by omega, v2_four_mul (10 * s),
    show 6 * n = 4 * (6 * s) by omega, v2_four_mul (6 * s),
    show 4 * n = 4 * (4 * s) by omega, v2_four_mul (4 * s)]
  have h := factorial_factorization_le s 2 Nat.prime_two
  omega

/-! ## Integrality -/

/-- Integrality of the quadruple-factorial ratio:
`(15n)!!!!(10n)!!!!(6n)!!!!(4n)!!!! ∣ (30n)!!!!(3n)!!!!(2n)!!!!` for every `n`. -/
theorem quadFact_ratio_dvd (n : ℕ) :
    quadFact (15 * n) * quadFact (10 * n) * quadFact (6 * n) * quadFact (4 * n) ∣
      quadFact (30 * n) * quadFact (3 * n) * quadFact (2 * n) := by
  have h : ∀ q, quadFact q ≠ 0 := fun q => (quadFact_pos q).ne'
  refine (Nat.factorization_prime_le_iff_dvd (mul_ne_zero (mul_ne_zero (mul_ne_zero (h _) (h _)) (h _)) (h _))
    (mul_ne_zero (mul_ne_zero (h _) (h _)) (h _))).1 fun p pp => ?_
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (h _) (h _)) (h _)) (h _),
    Nat.factorization_mul (mul_ne_zero (h _) (h _)) (h _), Nat.factorization_mul (h _) (h _),
    Nat.factorization_mul (mul_ne_zero (h _) (h _)) (h _), Nat.factorization_mul (h _) (h _)]
  simp only [Finsupp.add_apply]
  by_cases hp2 : p = 2
  · subst hp2
    rcases (by omega : n % 4 = 0 ∨ n % 2 = 1 ∨ n % 4 = 2) with h0 | h1 | h2
    · exact two_le_zero_mod_four n (n / 4) (by omega)
    · exact two_le_odd n (n / 2) (by omega)
    · exact two_le_two_mod_four n (n / 4) (by omega)
  · exact odd_prime_le n p pp hp2


/-- The first expression at `n` is the second expression at `2n`. -/
lemma halfExpr_eq (n : ℕ) : halfExpr n = quarterExpr (2 * n) := by
  unfold halfExpr quarterExpr
  push_cast
  ring_nf

/-- The second expression of the conjecture is an integer for every `n`. -/
theorem quarterExpr_int (n : ℕ) : ∃ k : ℤ, quarterExpr n = k := by
  refine ⟨((quadFact (30 * n) * quadFact (3 * n) * quadFact (2 * n)) /
    (quadFact (15 * n) * quadFact (10 * n) * quadFact (6 * n) * quadFact (4 * n)) : ℕ), ?_⟩
  rw [quarterExpr_eq, Int.cast_natCast, Nat.cast_div (quadFact_ratio_dvd n)]
  have h : ∀ q, quadFact q ≠ 0 := fun q => (quadFact_pos q).ne'
  exact_mod_cast mul_ne_zero (mul_ne_zero (mul_ne_zero (h _) (h _)) (h _)) (h _)

/-! ## Ground truth at genuinely fractional arguments -/

/-- `a(1/4) = Γ(17/2)Γ(7/4)Γ(3/2)/(Γ(19/4)Γ(7/2)Γ(5/2)Γ(2)) = 156`. -/
example : quarterExpr 1 = 156 := by
  have hnum : quadFact (30 * 1) * quadFact (3 * 1) * quadFact (2 * 1) = 3113510400 := by decide
  have hden : quadFact (15 * 1) * quadFact (10 * 1) * quadFact (6 * 1) * quadFact (4 * 1) =
      19958400 := by decide
  rw [quarterExpr_eq, hnum, hden]
  norm_num

/-- `a(1/2) = 15! Γ(5/2) 1! / (Γ(17/2) 5! 3! 2!) = 86016`. -/
example : halfExpr 1 = 86016 := by
  have hnum : quadFact (30 * 2) * quadFact (3 * 2) * quadFact (2 * 2) = 67397023732529627136000 := by
    decide
  have hden : quadFact (15 * 2) * quadFact (10 * 2) * quadFact (6 * 2) * quadFact (4 * 2) =
      783540547485696000 := by decide
  rw [halfExpr_eq, quarterExpr_eq, hnum, hden]
  norm_num

/-! ## The conjecture -/

/-- **Bala's conjecture (A295460, Peter Bala, Jul 29 2026), proved.**

Verbatim: "Conjecture: for n >= 0, both a(n/2) = (15*n)!*(3*n/2)!*(n)! /
((15*n/2)!*(5*n)!*(3*n)!*(2*n)!) and a(n/4) = (15*n/2)!*(3*n/4)!*(n/2)! /
((15*n/4)!*(5*n/2)!*(3*n/2)!*n!) are integers, where fractional factorials are defined
using the Gamma function."

Here `x! = fact x = Γ(x + 1)` and both quotients are real numbers with positive denominators
(`fact_pos`). -/
theorem conjecture : ∀ n : ℕ, (∃ k : ℤ, halfExpr n = k) ∧ (∃ k : ℤ, quarterExpr n = k) := fun n =>
  ⟨by rw [halfExpr_eq]; exact quarterExpr_int _, quarterExpr_int n⟩

end Candidates.A295460BalaBoth
