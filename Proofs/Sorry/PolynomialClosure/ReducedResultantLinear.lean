/-
# Reduced resultant of two linear integer polynomials: closed form

## Source

arXiv:2506.10838 — Zhiqian Liu, Xiaoting Li, Wenheng Liu, Min Sha,
"Three integers arising from Bézout's identity and resultants of integer
polynomials".  Section 6 ("Numerical data"): Conjecture 6.1 (the frequency of
`B(f,g) = r(f,g)` is at least `9/10`) and the closing remark of the section,
which records `B(ax+b, cx+d) = |ad - bc| / gcd(a,c)`.

The paper defines the *reduced resultant* `r(f,g)` as the smallest positive
integer in `f(x)ℤ[x] + g(x)ℤ[x]`, so that
`(f(x)ℤ[x] + g(x)ℤ[x]) ∩ ℤ = r(f,g)ℤ`.  It computes `r` by Gröbner bases and
gives no closed form for `r` in the linear case.

## Claim formalized here (bridge lemma for the `(m,n) = (1,1)` case, 2026-10-21)

For `a, b, c, d ∈ ℤ` with `a, c ≠ 0`, `ad - bc ≠ 0` and `gcd(a,b,c,d) = 1`,
let `g = gcd(a,c)`, `Δ = |ad - bc|` and `B = Δ/g`.  Then
`(ax+b, cx+d)ℤ[x] ∩ ℤ = B₁·ℤ`, where `B₁ = B / gcd(B, g^B)` is the largest
divisor of `B` coprime to `g`.

## Status

Not stated or proved in the paper (the paper only computes `r(f,g)`
numerically); the closed form was proposed by the triage of this campaign
and checked against Sage Gröbner bases over `ℤ` (all pairs with height `≤ 4`,
several thousand random primitive pairs, and 353 further random and
structured pairs on 2026-10-21).  Proved below.

The hypotheses `a ≠ 0` and `c ≠ 0` are not used by the proof; the general
form `comap_C_linIdeal_eq_span` assumes only `ad - bc ≠ 0` and primitivity,
and the faithful statement `reducedResultant_linear` is its specialization.
-/
import Mathlib

set_option autoImplicit false

namespace ReducedResultantLinear

open Polynomial

/-- The ideal `(ax + b, cx + d)` of `ℤ[x]`, i.e. `f(x)ℤ[x] + g(x)ℤ[x]` for
`f = ax + b`, `g = cx + d`. -/
noncomputable def linIdeal (a b c d : ℤ) : Ideal ℤ[X] :=
  Ideal.span {C a * X + C b, C c * X + C d}

/-- `B = |ad - bc| / gcd(a, c)`, the Bézout denominator `B(ax+b, cx+d)` of
arXiv:2506.10838, end of Section 6. -/
def reducedB (a b c d : ℤ) : ℕ :=
  (a * d - b * c).natAbs / Int.gcd a c

/-- `B₁ = B / gcd(B, g^B)` with `g = gcd(a, c)`: the largest divisor of `B`
coprime to `g`. -/
def reducedB1 (a b c d : ℤ) : ℕ :=
  reducedB a b c d / Nat.gcd (reducedB a b c d) (Int.gcd a c ^ reducedB a b c d)

/-! ### Ground truth on small instances -/

/-- `f = 2x + 1`, `g = 2x + 7`: `Δ = 12`, `g = 2`, `B = 6`, `B₁ = 3`. -/
example : reducedB 2 1 2 7 = 6 ∧ reducedB1 2 1 2 7 = 3 := by decide

/-- `f = 8x + 1`, `g = 4x + 3`: `Δ = 20`, `g = 4`, `B = 5`, `B₁ = 5`. -/
example : reducedB 8 1 4 3 = 5 ∧ reducedB1 8 1 4 3 = 5 := by decide

/-- `f = 9x + 2`, `g = 27x + 1`: `Δ = 45`, `g = 9`, `B = 5`, `B₁ = 5`. -/
example : reducedB 9 2 27 1 = 5 ∧ reducedB1 9 2 27 1 = 5 := by decide

/-- `f = 16x + 3`, `g = 48x + 5`: `Δ = 64`, `g = 16`, `B = 4`, `B₁ = 1`. -/
example : reducedB 16 3 48 5 = 4 ∧ reducedB1 16 3 48 5 = 1 := by decide

/-- When `gcd(a,c) = 1`, `B₁ = B = |ad - bc|`: `f = 2x + 1`, `g = 3x + 5`. -/
example : reducedB1 2 1 3 5 = 7 := by decide

/-! ### Arithmetic of `B₁` -/

/-- For `B ≠ 0`, the quotient `B / gcd(B, g^B)` is coprime to `g`. -/
theorem coprime_div_gcd_pow (B g : ℕ) (hB : B ≠ 0) :
    Nat.Coprime (B / Nat.gcd B (g ^ B)) g := by
  set B2 := Nat.gcd B (g ^ B) with hB2
  have hB2B : B2 ∣ B := Nat.gcd_dvd_left B (g ^ B)
  have hB2ne : B2 ≠ 0 := Nat.gcd_ne_zero_left hB
  have hsplit : B / B2 * B2 = B := Nat.div_mul_cancel hB2B
  refine Nat.coprime_of_dvd fun p hp hp1 hpg => ?_
  set j := B2.factorization p
  have hpj : p ^ j ∣ B2 := Nat.ordProj_dvd B2 p
  have hpjB : p ^ (j + 1) ∣ B := by
    rw [← hsplit, pow_succ, mul_comm (B / B2)]
    exact mul_dvd_mul hpj hp1
  have hle : p ^ (j + 1) ≤ B := Nat.le_of_dvd (Nat.pos_of_ne_zero hB) hpjB
  have hjB : j + 1 ≤ B := (Nat.lt_pow_self hp.one_lt).le.trans hle
  have hpjg : p ^ (j + 1) ∣ g ^ B :=
    (pow_dvd_pow p hjB).trans (pow_dvd_pow_of_dvd hpg B)
  exact Nat.pow_succ_factorization_not_dvd hB2ne hp (Nat.dvd_gcd hpjB hpjg)

/-- `gcd(a,c)` divides `|ad - bc|`, so `|ad - bc| = gcd(a,c) · B`. -/
theorem natAbs_eq_gcd_mul_reducedB (a b c d : ℤ) :
    (a * d - b * c).natAbs = Int.gcd a c * reducedB a b c d := by
  have hdvd : ((Int.gcd a c : ℕ) : ℤ) ∣ a * d - b * c :=
    dvd_sub (dvd_mul_of_dvd_left (Int.gcd_dvd_left a c) d)
      (Dvd.dvd.mul_left (Int.gcd_dvd_right a c) b)
  exact (Nat.mul_div_cancel' (Int.natCast_dvd.mp hdvd)).symm

/-- If `ad - bc ≠ 0` then `gcd(a,c) ≠ 0` and `B ≠ 0`. -/
theorem gcd_ne_zero_and_reducedB_ne_zero (a b c d : ℤ) (hΔ : a * d - b * c ≠ 0) :
    Int.gcd a c ≠ 0 ∧ reducedB a b c d ≠ 0 := by
  have h := natAbs_eq_gcd_mul_reducedB a b c d
  have hne : (a * d - b * c).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hΔ
  rw [h] at hne
  exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/-- `B · ℤ ⊆ (ax+b, cx+d)`: with `a = g a'`, `c = g c'` one has
`c'(ax+b) - a'(cx+d) = c'b - a'd = ±B`. -/
theorem C_mem_linIdeal_of_reducedB_dvd (a b c d : ℤ) (hΔ : a * d - b * c ≠ 0)
    (n : ℤ) (hn : (reducedB a b c d : ℤ) ∣ n) : C n ∈ linIdeal a b c d := by
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a c
  obtain ⟨c', hc'⟩ := Int.gcd_dvd_right a c
  set g := Int.gcd a c with hg
  have hg0 : g ≠ 0 := (gcd_ne_zero_and_reducedB_ne_zero a b c d hΔ).1
  -- the integer `e = c'b - a'd` with `|e| = B`
  set e : ℤ := c' * b - a' * d with he
  have hge : (g : ℤ) * e = -(a * d - b * c) := by
    rw [he, ha', hc']; ring
  have habs : e.natAbs = reducedB a b c d := by
    have h1 := natAbs_eq_gcd_mul_reducedB a b c d
    have h2 : (a * d - b * c).natAbs = g * e.natAbs := by
      rw [← Int.natAbs_neg, ← hge, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) (h2.symm.trans h1)
  have hen : e ∣ n := by
    rw [← habs] at hn
    exact Int.natAbs_dvd.mp hn
  obtain ⟨k, hk⟩ := hen
  have hCe : C e ∈ linIdeal a b c d := by
    refine Ideal.mem_span_pair.mpr ⟨C c', -C a', ?_⟩
    rw [he, ha', hc']
    simp only [map_mul, map_sub, map_natCast]
    ring
  rw [hk, map_mul]
  exact Ideal.mul_mem_right _ _ hCe

/-- Primitivity `gcd(a,b,c,d) = 1` gives an integer relation
`αa + βb + γc + δd = 1`. -/
theorem exists_lin_comb_eq_one (a b c d : ℤ)
    (hprim : Int.gcd (Int.gcd a b : ℤ) (Int.gcd c d : ℤ) = 1) :
    ∃ α β γ δ : ℤ, α * a + β * b + γ * c + δ * d = 1 := by
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hprim
  rw [Int.gcd_eq_gcd_ab a b, Int.gcd_eq_gcd_ab c d] at huv
  exact ⟨u * a.gcdA b, u * a.gcdB b, v * c.gcdA d, v * c.gcdB d, by linear_combination huv⟩

/-- `B₁ ∈ (ax+b, cx+d)`.  Modulo the ideal, `g = gcd(a,c)` is a unit (by
primitivity, `1 = a(α - βx) + c(γ - δx)` there), hence so is
`gcd(B, g^B) ∣ g^B`; since `B = B₁ · gcd(B, g^B)` vanishes, `B₁` vanishes. -/
theorem C_reducedB1_mem_linIdeal (a b c d : ℤ) (hΔ : a * d - b * c ≠ 0)
    (hprim : Int.gcd (Int.gcd a b : ℤ) (Int.gcd c d : ℤ) = 1) :
    C (reducedB1 a b c d : ℤ) ∈ linIdeal a b c d := by
  obtain ⟨α, β, γ, δ, hcomb⟩ := exists_lin_comb_eq_one a b c d hprim
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a c
  obtain ⟨c', hc'⟩ := Int.gcd_dvd_right a c
  set g := Int.gcd a c with hg
  set B := reducedB a b c d with hBdef
  set B2 := Nat.gcd B (g ^ B) with hB2
  set I := linIdeal a b c d with hI
  let π := Ideal.Quotient.mk I
  -- `g` is a unit modulo `I`
  set h : ℤ[X] := C (α * a' + γ * c') - C (β * a' + δ * c') * X with hh
  have hrel : 1 - C (g : ℤ) * h = C β * (C a * X + C b) + C δ * (C c * X + C d) := by
    have hcomb' : C α * C a + C β * C b + C γ * C c + C δ * C d = (1 : ℤ[X]) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, ← map_add,
        hcomb, map_one]
    have hCa : C a = C (g : ℤ) * C a' := by rw [← map_mul, ← ha']
    have hCc : C c = C (g : ℤ) * C c' := by rw [← map_mul, ← hc']
    rw [hh]
    simp only [map_add, map_mul]
    linear_combination (-1 : ℤ[X]) * hcomb' + (C α - C β * X) * hCa + (C γ - C δ * X) * hCc
  have hrelI : 1 - C (g : ℤ) * h ∈ I := by
    rw [hrel]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  have hgunit : IsUnit (π (C (g : ℤ))) := by
    refine IsUnit.of_mul_eq_one (π h) ?_
    have h0 : π (1 - C (g : ℤ) * h) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrelI
    rw [map_sub, map_one, map_mul, sub_eq_zero] at h0
    exact h0.symm
  -- hence `gcd(B, g^B)` is a unit modulo `I`
  have hB2unit : IsUnit (π (C (B2 : ℤ))) := by
    refine isUnit_of_dvd_unit ?_ (hgunit.pow B)
    rw [← map_pow, ← map_pow]
    refine map_dvd π (map_dvd C ?_)
    exact_mod_cast Nat.gcd_dvd_right B (g ^ B)
  -- `B` vanishes modulo `I`
  have hB0 : π (C (B : ℤ)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (C_mem_linIdeal_of_reducedB_dvd a b c d hΔ _ dvd_rfl)
  have hsplit : (reducedB1 a b c d : ℤ) * (B2 : ℤ) = (B : ℤ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left B (g ^ B))
  have hprod : π (C (reducedB1 a b c d : ℤ)) * π (C (B2 : ℤ)) = 0 := by
    rw [← map_mul, ← map_mul, hsplit, hB0]
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((hB2unit.mul_left_eq_zero).mp hprod)

/-- `B₁` divides every integer of `(ax+b, cx+d)`.  Since `B₁` is coprime to
`g = gcd(a,c)`, there are `s, t, μ` with `sa + tc + μB₁ = 1`; then
`x₀ = -(sb + td)` is a common root of `ax+b` and `cx+d` modulo `B₁`
(because `B₁ ∣ ad - bc`), and evaluating at `x₀` gives the claim. -/
theorem reducedB1_dvd_of_C_mem_linIdeal (a b c d : ℤ) (hΔ : a * d - b * c ≠ 0)
    (n : ℤ) (hn : C n ∈ linIdeal a b c d) : (reducedB1 a b c d : ℤ) ∣ n := by
  set g := Int.gcd a c with hg
  set B := reducedB a b c d with hBdef
  set B1 := reducedB1 a b c d with hB1def
  have hBne : B ≠ 0 := (gcd_ne_zero_and_reducedB_ne_zero a b c d hΔ).2
  have hcop : Nat.Coprime B1 g := coprime_div_gcd_pow B g hBne
  obtain ⟨μ, ν, hμν⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hgab : (g : ℤ) = a * a.gcdA c + c * a.gcdB c := Int.gcd_eq_gcd_ab a c
  set s : ℤ := ν * a.gcdA c with hs
  set t : ℤ := ν * a.gcdB c with ht
  have hst : s * a + t * c + μ * (B1 : ℤ) = 1 := by
    rw [hs, ht]; linear_combination hμν - ν * hgab
  -- `B₁ ∣ ad - bc`
  have hB1Δ : (B1 : ℤ) ∣ a * d - b * c := by
    refine Int.natCast_dvd.mpr ?_
    rw [natAbs_eq_gcd_mul_reducedB a b c d]
    refine Dvd.dvd.mul_left ?_ g
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left B (g ^ B))
  obtain ⟨k, hk⟩ := hB1Δ
  set x₀ : ℤ := -(s * b + t * d) with hx₀
  have h1 : a * x₀ + b = (B1 : ℤ) * (-t * k + μ * b) := by
    rw [hx₀]; linear_combination (-b) * hst - t * hk
  have h2 : c * x₀ + d = (B1 : ℤ) * (s * k + μ * d) := by
    rw [hx₀]; linear_combination (-d) * hst + s * hk
  obtain ⟨P, Q, hPQ⟩ := Ideal.mem_span_pair.mp hn
  have heval := congrArg (Polynomial.eval x₀) hPQ
  simp only [eval_add, eval_mul, eval_C, eval_X] at heval
  rw [← heval, h1, h2]
  exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)

/-! ### Main results -/

/-- **Closed form of the reduced resultant of two linear polynomials**
(general form).  If `ad - bc ≠ 0` and `gcd(a,b,c,d) = 1`, then
`(ax+b, cx+d)ℤ[x] ∩ ℤ = B₁ℤ` with `g = gcd(a,c)`, `B = |ad-bc|/g` and
`B₁ = B / gcd(B, g^B)`.  Here `∩ ℤ` is the preimage under `C : ℤ → ℤ[x]`. -/
theorem comap_C_linIdeal_eq_span (a b c d : ℤ) (hΔ : a * d - b * c ≠ 0)
    (hprim : Int.gcd (Int.gcd a b : ℤ) (Int.gcd c d : ℤ) = 1) :
    Ideal.comap (C : ℤ →+* ℤ[X]) (linIdeal a b c d) =
      Ideal.span {(reducedB1 a b c d : ℤ)} := by
  ext n
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  constructor
  · exact reducedB1_dvd_of_C_mem_linIdeal a b c d hΔ n
  · rintro ⟨k, rfl⟩
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (C_reducedB1_mem_linIdeal a b c d hΔ hprim)

/-- **Reduced resultant of `ax+b` and `cx+d`** (bridge lemma for the `(1,1)`
case of Conjecture 6.1 of Liu–Li–Liu–Sha, arXiv:2506.10838).  For integers
`a, b, c, d` with `a, c ≠ 0`, `ad - bc ≠ 0` and `gcd(a,b,c,d) = 1`, let
`g = gcd(a,c)`, `B = |ad - bc| / g` and `B₁ = B / gcd(B, g^B)`.  Then
`(ax+b, cx+d)ℤ[x] ∩ ℤ = B₁·ℤ`, i.e. the reduced resultant `r(ax+b, cx+d)`
equals `B₁`. -/
theorem reducedResultant_linear (a b c d : ℤ) (_ha : a ≠ 0) (_hc : c ≠ 0)
    (hΔ : a * d - b * c ≠ 0)
    (hprim : Int.gcd (Int.gcd a b : ℤ) (Int.gcd c d : ℤ) = 1) :
    Ideal.comap (C : ℤ →+* ℤ[X]) (Ideal.span {C a * X + C b, C c * X + C d}) =
      Ideal.span {(reducedB1 a b c d : ℤ)} :=
  comap_C_linIdeal_eq_span a b c d hΔ hprim

/-- Membership form of `reducedResultant_linear`: under the same hypotheses,
the constant `n` lies in `(ax+b, cx+d)` iff `B₁ ∣ n`. -/
theorem C_mem_linIdeal_iff (a b c d : ℤ) (hΔ : a * d - b * c ≠ 0)
    (hprim : Int.gcd (Int.gcd a b : ℤ) (Int.gcd c d : ℤ) = 1) (n : ℤ) :
    C n ∈ linIdeal a b c d ↔ (reducedB1 a b c d : ℤ) ∣ n := by
  rw [← Ideal.mem_comap, comap_C_linIdeal_eq_span a b c d hΔ hprim,
    Ideal.mem_span_singleton]

/-- Corollary (the triage's criterion for `B(f,g) = r(f,g)` in degree
`(1,1)`): when `ad - bc ≠ 0`, `B₁ = B` iff `gcd(g, B) = 1`, where
`g = gcd(a,c)` and `B = |ad - bc| / g`. -/
theorem reducedB1_eq_reducedB_iff (a b c d : ℤ) (hΔ : a * d - b * c ≠ 0) :
    reducedB1 a b c d = reducedB a b c d ↔ Nat.Coprime (reducedB a b c d) (Int.gcd a c) := by
  have hBne : reducedB a b c d ≠ 0 := (gcd_ne_zero_and_reducedB_ne_zero a b c d hΔ).2
  rw [reducedB1, Nat.div_eq_self, ← Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hBne)]
  simp only [hBne, false_or]

/-- Non-vacuity and ground truth: `f = 2x + 1`, `g = 2x + 7` satisfy all
hypotheses, and `(2x+1, 2x+7) ∩ ℤ = 3ℤ` (matching a Sage Gröbner basis). -/
example : Ideal.comap (C : ℤ →+* ℤ[X]) (Ideal.span {C 2 * X + C 1, C 2 * X + C 7}) =
    Ideal.span {(3 : ℤ)} := by
  have h := reducedResultant_linear 2 1 2 7 (by decide) (by decide) (by decide) (by decide)
  rw [h]
  congr

end ReducedResultantLinear
