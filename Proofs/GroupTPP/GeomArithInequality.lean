import Mathlib

/-!
# CKSU Lemma `geom->arith`: the geometric-to-arithmetic-mean bound

This file formalizes the elementary limit lemma of Cohn–Kleinberg–Szegedy–Umans
[math/0511460, `lemma:geom->arith`, FOCS05-10page.tex:266–286]:

> Let `s 0, …, s (k-1)` be nonnegative reals, and suppose that for every `N`
> and every vector `μ` of nonnegative integers with `∑ i, μ i = N` we have
> `(N choose μ) * ∏ i, s i ^ μ i ≤ C ^ N`. Then `∑ i, s i ≤ C`.

It is the geometric-to-arithmetic-mean limit step in the proof of the STPP
capacity inequality (CKSU `theorem:asi`, `GroupTPP.STPPWreath.stpp_capacity_le`).

## Proof route

CKSU's own (`\remove{}`d) proof takes `μ/N → p` along a probability vector `p`
and extracts `-∑ pᵢ log pᵢ + ∑ pᵢ log sᵢ ≤ log C` via Stirling asymptotics.
We avoid entropy and Stirling entirely (per the Ga1 pricing memo) using the
**multinomial expansion** route:

* the multinomial theorem (`Finset.sum_pow_eq_sum_piAntidiag`, Mathlib) gives
  `(∑ i, s i) ^ N = ∑_{μ ∈ piAntidiag univ N} (N choose μ) * ∏ i, s i ^ μ i`;
* every summand is `≤ C ^ N` by hypothesis, and there are at most `(N + 1) ^ k`
  summands (each `μ i` lies in `{0, …, N}`), so
  `(∑ i, s i) ^ N ≤ (N + 1) ^ k * C ^ N` for every `N`;
* the polynomial prefactor `(N + 1) ^ k` dies as `N → ∞`
  (`le_of_pow_le_poly_mul_pow` below).

Note the multinomial-expansion proof never uses the sign of `s i`: the core
statement `sum_le_of_multinomial_prod_pow_le` drops CKSU's nonnegativity
hypothesis (a strict strengthening). The paper-literal form (with `0 ≤ s i`,
over `Fin k`) is provided as `geom_arith_inequality`.

## Main results

* `GroupTPP.GeomArithInequality.le_of_pow_le_poly_mul_pow` — the **polynomial
  prefactor absorption** limit engine: `x ^ N ≤ K * (N+1)^k * y ^ N` for all
  `N ≥ 1` forces `x ≤ y`. Generalizes
  `GroupTPP.CUCapacity.le_of_pow_le_const_mul_pow` (the `k = 0` case).
* `GroupTPP.GeomArithInequality.sum_le_of_multinomial_prod_pow_le` — CKSU
  `lemma:geom->arith` over any finite index type, without the (unneeded)
  nonnegativity of `s`.
* `GroupTPP.GeomArithInequality.geom_arith_inequality` — the paper-literal
  statement (CKSU Lemma 2.1) over `Fin k` with `0 ≤ s i`.

## References

* [Cohn–Kleinberg–Szegedy–Umans, *Group-theoretic algorithms for matrix
  multiplication*][math/0511460], Lemma `geom->arith` (FOCS 2005, Lemma 2.1).
-/

open Filter

namespace GroupTPP.GeomArithInequality

/-- **Polynomial-prefactor absorption** (the `N → ∞` limit engine): if
`x ^ N ≤ K * (N + 1) ^ k * y ^ N` for all `N ≥ 1` with `y ≥ 0`, then `x ≤ y`.

This generalizes `GroupTPP.CUCapacity.le_of_pow_le_const_mul_pow` (which is the
constant-prefactor case `k = 0`) from a constant `K` to a polynomial prefactor
`K * (N + 1) ^ k`; any real-polynomial prefactor of degree `≤ k` is dominated
by such a term. The proof pits the geometric decay `(y/x) ^ N` against the
polynomial growth (`tendsto_pow_const_mul_const_pow_of_abs_lt_one`).

Intended consumers: `sum_le_of_multinomial_prod_pow_le` below (where
`(N + 1) ^ k` counts the compositions of `N` into `k` parts), and any future
"kill a polynomial factor by powering" limit in the `STPPWreath` campaign
(Pl19). -/
theorem le_of_pow_le_poly_mul_pow {x y K : ℝ} (k : ℕ) (hy : 0 ≤ y)
    (h : ∀ N : ℕ, 1 ≤ N → x ^ N ≤ K * ((N : ℝ) + 1) ^ k * y ^ N) : x ≤ y := by
  by_contra hcon
  rw [not_le] at hcon
  have hx : 0 < x := hy.trans_lt hcon
  rcases eq_or_lt_of_le hy with hy0 | hy0
  · -- `y = 0`: already `x = x ^ 1 ≤ K * 2 ^ k * 0 = 0` contradicts `0 < x`.
    have h1 := h 1 le_rfl
    rw [← hy0] at h1
    simp at h1
    exact absurd h1 (not_le.mpr hx)
  · -- `0 < y < x`: the ratio `r = y / x` satisfies `0 < r < 1`, so
    -- `K * (N + 1) ^ k * r ^ N → 0`; but the hypothesis forces it `≥ 1`.
    set r := y / x with hr
    have hr0 : 0 < r := div_pos hy0 hx
    have hr1 : r < 1 := (div_lt_one hx).mpr hcon
    have habs : |r| < 1 := by rw [abs_of_pos hr0]; exact hr1
    have hshift := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k habs).comp
      (Filter.tendsto_add_atTop_nat 1)
    have hmul := hshift.const_mul (K / r)
    rw [mul_zero] at hmul
    have h2 : Tendsto (fun N : ℕ => K * ((N : ℝ) + 1) ^ k * r ^ N)
        atTop (nhds 0) := by
      refine hmul.congr fun N => ?_
      simp only [Function.comp_apply]
      push_cast
      rw [pow_succ]
      field_simp
    have hone : (1 : ℝ) ≤ 0 := by
      refine ge_of_tendsto h2 ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hxN : (0 : ℝ) < x ^ N := pow_pos hx N
      have hle' : 1 * x ^ N ≤ (K * ((N : ℝ) + 1) ^ k * r ^ N) * x ^ N := by
        rw [one_mul]
        calc x ^ N ≤ K * ((N : ℝ) + 1) ^ k * y ^ N := h N hN
          _ = (K * ((N : ℝ) + 1) ^ k * r ^ N) * x ^ N := by
              rw [hr, div_pow]
              field_simp
      exact le_of_mul_le_mul_right hle' hxN
    linarith

/-- **CKSU Lemma `geom->arith`** [math/0511460, FOCS05-10page.tex:266–286],
core form: if `(N choose μ) * ∏ i, s i ^ μ i ≤ C ^ N` for every `N` and every
`μ : ι → ℕ` with `∑ i, μ i = N`, then `∑ i, s i ≤ C`.

Stated over an arbitrary finite index type and **without** CKSU's
nonnegativity hypothesis on `s` (the multinomial-expansion proof never uses
it); `geom_arith_inequality` below restores the paper-literal shape.

Proof: expand `(∑ i, s i) ^ N` by the multinomial theorem, bound each of the
at most `(N + 1) ^ |ι|` summands by `C ^ N`, and absorb the polynomial
prefactor via `le_of_pow_le_poly_mul_pow`. -/
theorem sum_le_of_multinomial_prod_pow_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (μ : ι → ℕ), ∑ i, μ i = N →
      (Nat.multinomial Finset.univ μ : ℝ) * ∏ i, s i ^ μ i ≤ C ^ N) :
    ∑ i, s i ≤ C := by
  refine le_of_pow_le_poly_mul_pow (K := 1) (Fintype.card ι) hC fun N _hN => ?_
  rw [one_mul, Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset ι) s N]
  -- Each composition contributes at most `C ^ N` …
  have hterm : ∀ μ ∈ Finset.univ.piAntidiag N,
      (Nat.multinomial Finset.univ μ : ℝ) * ∏ i, s i ^ μ i ≤ C ^ N := by
    intro μ hμ
    exact h N μ ((Finset.mem_piAntidiag.mp hμ).1)
  -- … and there are at most `(N + 1) ^ |ι|` compositions.
  have hcard : ((Finset.univ.piAntidiag N : Finset (ι → ℕ)).card : ℝ)
      ≤ ((N : ℝ) + 1) ^ Fintype.card ι := by
    have hsub : (Finset.univ.piAntidiag N : Finset (ι → ℕ))
        ⊆ Fintype.piFinset fun _ : ι => Finset.range (N + 1) := by
      intro μ hμ
      obtain ⟨hsum, -⟩ := Finset.mem_piAntidiag.mp hμ
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range, Nat.lt_succ_iff]
      calc μ i ≤ Finset.univ.sum μ :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = N := hsum
    have hle := Finset.card_le_card hsub
    have hpf : (Fintype.piFinset fun _ : ι => Finset.range (N + 1)).card
        = (N + 1) ^ Fintype.card ι := by
      simp
    rw [hpf] at hle
    calc ((Finset.univ.piAntidiag N : Finset (ι → ℕ)).card : ℝ)
        ≤ (((N + 1) ^ Fintype.card ι : ℕ) : ℝ) := by exact_mod_cast hle
      _ = ((N : ℝ) + 1) ^ Fintype.card ι := by push_cast; ring
  calc ∑ μ ∈ Finset.univ.piAntidiag N,
        (Nat.multinomial Finset.univ μ : ℝ) * ∏ i, s i ^ μ i
      ≤ (Finset.univ.piAntidiag N : Finset (ι → ℕ)).card • C ^ N :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Finset.univ.piAntidiag N : Finset (ι → ℕ)).card : ℝ) * C ^ N :=
        nsmul_eq_mul _ _
    _ ≤ ((N : ℝ) + 1) ^ Fintype.card ι * C ^ N :=
        mul_le_mul_of_nonneg_right hcard (pow_nonneg hC N)

/-- **CKSU Lemma 2.1 (`lemma:geom->arith`), paper-literal form**
[math/0511460, FOCS05-10page.tex:266–286]: for nonnegative reals
`s 0, …, s (k-1)` and `C ≥ 0`, if `(N choose μ) * ∏ i, s i ^ μ i ≤ C ^ N`
for every `N` and every composition `μ` of `N` into `k` parts, then
`∑ i, s i ≤ C`.

The nonnegativity hypothesis `_hs` is part of CKSU's statement but is not
needed by the multinomial-expansion proof; see
`sum_le_of_multinomial_prod_pow_le` for the stronger form. -/
theorem geom_arith_inequality {k : ℕ} {s : Fin k → ℝ} {C : ℝ}
    (_hs : ∀ i, 0 ≤ s i) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (μ : Fin k → ℕ), ∑ i, μ i = N →
      (Nat.multinomial Finset.univ μ : ℝ) * ∏ i, s i ^ μ i ≤ C ^ N) :
    ∑ i, s i ≤ C :=
  sum_le_of_multinomial_prod_pow_le hC h

end GroupTPP.GeomArithInequality
