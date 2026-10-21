/-
# Casas-Alvero conjecture in prime-power degree (characteristic zero)

## Source

arXiv:math/0605090, H.-Chr. Graf von Bothmer, O. Labs, J. Schicho and
C. van de Woestijne, "The Casas-Alvero conjecture for infinitely many
degrees", J. Algebra 316 (2007).  Main Theorem (stated in the Introduction
and proved at the end of Section 2, "Mixing characteristics, or There and
Back Again"), case `d = p ^ k`; the characteristic-`p` input is the
Proposition `prop:prime` of Section 2 (Prop 2.4).  Retrieved and re-read
2026-10-21.

Verbatim (Introduction):

> **Conjecture (Casas-Alvero).** Let $P$ be a monic univariate polynomial of
> degree $d$ over a field $\KK$.  Then $\gcd(P,P_i)$ is nontrivial for
> $i=1,\ldots,d-1$ if and only if $P=(X-\alpha)^d$ for some $\alpha\in\KK$.
>
> **Theorem.** Let $d$ be of the form $p^k$ or $2p^k$ for some prime number
> $p$.  Then the Casas-Alvero Conjecture holds in characteristic $0$ for
> polynomials of degree $d$.

> **Proposition (prop:prime).** Let $d\ge 1$ be an integer.  If $d$ is a power
> of some prime number $p$, then $X_d(\barF_p)$ is empty.

## Status

Proved in the paper (the case `d = p ^ k` formalized here; the case
`d = 2 p ^ k` is not formalized).  The conjecture is open in general.

## Formalization

The hypothesis `gcd(f, f^(i)) ≠ 1` is the repo predicate
`Candidates.CasasAlveroDegreeFour.SharesFactorWithDerivatives`
(`¬ IsCoprime f (derivative^[i] f)` for `1 ≤ i < natDegree f`).  In
characteristic `0` the ordinary and Hasse derivatives differ by the unit
`i !`, so the paper's `P_i` and `P^(i)` give the same condition.

Instead of the paper's transfer through the proper scheme `X_d` over `ℤ`
(Prop `prop:frompto0`), the proof uses the elementary valuation form of the
same idea (Draisma-de Jong, EMS Newsletter 2011):

* `eq_X_pow_of_hasseDeriv_roots` (Prop `prop:prime`): over a commutative
  ring with `p = 0`, a monic `g` of degree `p ^ k` with `g(0) = 0` whose
  Hasse derivatives `D_i g` (`1 ≤ i < p ^ k`) all have a root is `X ^ (p ^ k)`.
* `exists_valuationSubring_natCast_mem_maximalIdeal`: a characteristic-zero
  field has a valuation subring in which `p` is not a unit.
* `eq_of_mem_of_taylor_coeff_eq_zero`: over a characteristic-zero field, the
  roots of a Casas-Alvero polynomial of degree `p ^ k` are all equal (rescale
  the roots into the valuation ring, so that one becomes `0` and another `1`,
  and reduce to the residue field).
* `casasAlvero_natDegree_eq_prime_pow`: the main theorem, by passing to the
  algebraic closure and descending the root `α = -a_{d-1} / d`.
-/
import NumberComplexity.CasasAlveroDegreeFour

set_option autoImplicit false

namespace Candidates.CasasAlveroPrimePower

open Polynomial

/-! ## Characteristic `p`: Proposition `prop:prime` -/

/-- If `p` is prime and `p = 0` in `R`, then `C(p ^ k, j) = 0` in `R` for
`j ≠ 0` and `j ≠ p ^ k`. -/
theorem choose_prime_pow_cast_eq_zero {R : Type*} [CommRing R] {p k j : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) (hj0 : j ≠ 0) (hjd : j ≠ p ^ k) : ((p ^ k).choose j : R) = 0 := by
  obtain ⟨m, hm⟩ := hp.dvd_choose_pow hj0 hjd
  rw [hm, Nat.cast_mul, hpR, zero_mul]

/-- Over a ring with `p = 0`, if `g` has `natDegree = p ^ k` and the coefficients of `g`
strictly between `j` and `p ^ k` vanish (`0 < j < p ^ k`), then the `j`-th Hasse derivative of
`g` is the constant `g.coeff j`. -/
theorem hasseDeriv_eq_C_coeff {R : Type*} [CommRing R] {p k : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) (g : R[X]) (hd : g.natDegree = p ^ k) (j : ℕ) (hj0 : 0 < j)
    (hjd : j < p ^ k) (hz : ∀ n, j < n → n < p ^ k → g.coeff n = 0) :
    hasseDeriv j g = C (g.coeff j) := by
  ext n
  rw [hasseDeriv_coeff, coeff_C]
  split_ifs with hn
  · subst hn
    simp
  · rcases lt_trichotomy (n + j) (p ^ k) with h | h | h
    · rw [hz (n + j) (by omega) h, mul_zero]
    · rw [h, choose_prime_pow_cast_eq_zero hp hpR (by omega) (by omega), zero_mul]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

/-- **Proposition `prop:prime`** (arXiv:math/0605090, Section 2, char-`p` core): over a
commutative ring `R` with `p = 0` (`p` prime), a monic `g` of degree `p ^ k` with `g(0) = 0`
such that for each `1 ≤ i < p ^ k` the Hasse derivative `D_i g` has a root, is `X ^ (p ^ k)`.
(The paper assumes a common root of `g` and `D_i g`; only a root of `D_i g` is used.) -/
theorem eq_X_pow_of_hasseDeriv_roots {R : Type*} [CommRing R] {p k : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) (g : R[X]) (hm : g.Monic) (hd : g.natDegree = p ^ k)
    (h0 : g.eval 0 = 0) (h : ∀ i, 1 ≤ i → i < p ^ k → ∃ r, (hasseDeriv i g).eval r = 0) :
    g = X ^ (p ^ k) := by
  have key : ∀ m j, p ^ k - j = m → 0 < j → j < p ^ k → g.coeff j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hjm hj0 hjd
      have hz : ∀ n, j < n → n < p ^ k → g.coeff n = 0 := fun n hjn hnd =>
        ih (p ^ k - n) (by omega) n rfl (by omega) hnd
      obtain ⟨r, hr⟩ := h j hj0 hjd
      rw [hasseDeriv_eq_C_coeff hp hpR g hd j hj0 hjd hz, eval_C] at hr
      exact hr
  ext n
  rw [coeff_X_pow]
  split_ifs with hn
  · subst hn
    rw [← hd]
    exact hm.coeff_natDegree
  · rcases Nat.lt_or_gt_of_ne hn with h1 | h1
    · rcases Nat.eq_zero_or_pos n with h2 | h2
      · subst h2
        rw [coeff_zero_eq_eval_zero]
        exact h0
      · exact key _ n rfl h2 h1
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-! ## A valuation ring in which `p` is not a unit -/

/-- In a field of characteristic zero, a prime `p` is not a unit of the prime subring `⊥`. -/
theorem natCast_prime_not_isUnit_bot {L : Type*} [Field L] [CharZero L] {p : ℕ}
    (hp : p.Prime) : ¬ IsUnit (p : (⊥ : Subring L)) := by
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨n, hn⟩ := Subring.mem_bot.mp y.2
  have hL : ((p : ℤ) * n : ℤ) = ((1 : ℤ) : L) := by
    have := congrArg (Subtype.val) hy
    push_cast at this ⊢
    rw [hn]
    exact this
  have hZ : (p : ℤ) * n = 1 := Int.cast_injective hL
  have h1 : (p : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) hZ
  exact hp.one_lt.ne' (by exact_mod_cast h1)

/-- A field of characteristic zero has a valuation subring `B` whose maximal ideal contains
the prime `p`, i.e. whose residue field has characteristic `p`. -/
theorem exists_valuationSubring_natCast_mem_maximalIdeal {L : Type*} [Field L] [CharZero L]
    {p : ℕ} (hp : p.Prime) :
    ∃ B : ValuationSubring L, (p : B) ∈ IsLocalRing.maximalIdeal B := by
  let A0 : Subring L := ⊥
  have hI : Ideal.span {(p : A0)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact natCast_prime_not_isUnit_bot hp
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
  haveI : M.IsPrime := hM.isPrime
  let A1 : LocalSubring L := LocalSubring.ofPrime A0 M
  obtain ⟨B, hB⟩ := A1.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hB
  refine ⟨B, ?_⟩
  have hpM : (p : A0) ∈ M := hIM (Ideal.subset_span rfl)
  have hA1 : (p : A1.toSubring) ∈ IsLocalRing.maximalIdeal A1.toSubring := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff A1.toSubring M (p : A0)).mpr hpM
    rwa [map_natCast] at this
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hA1 ⊢
  intro hu
  apply hA1
  apply isUnit_of_map_unit (Subring.inclusion hle)
  rw [map_natCast]
  exact hu

/-- For a valuation subring `B` of `L` and a multiset `D` with a nonzero element, some
nonzero `δ ∈ D` has maximal valuation: `y / δ ∈ B` for every `y ∈ D`. -/
theorem exists_mem_ne_zero_forall_div_mem {L : Type*} [Field L] (B : ValuationSubring L)
    (D : Multiset L) (hD : ∃ x ∈ D, x ≠ 0) : ∃ δ ∈ D, δ ≠ 0 ∧ ∀ y ∈ D, y / δ ∈ B := by
  obtain ⟨x, hx, hx0⟩ := hD
  obtain ⟨δ, hδ, hmax⟩ := Multiset.exists_max_image B.valuation (s := D) (by rintro rfl; simp at hx)
  have hδ0 : δ ≠ 0 := by
    intro h
    have hle := hmax x hx
    rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at hle
    exact hx0 hle
  refine ⟨δ, hδ, hδ0, fun y hy => ?_⟩
  rw [← B.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hmax y hy) zero_le

/-! ## Rescaling and translating roots -/

/-- Coefficient `i ≤ |u|` of `∏_{y ∈ u} (X - δ y)` is `δ ^ (|u| - i)` times coefficient `i` of
`∏_{y ∈ u} (X - y)`. -/
theorem coeff_prod_X_sub_C_mul {R : Type*} [CommRing R] (u : Multiset R) (δ : R) {i : ℕ}
    (hi : i ≤ Multiset.card u) :
    ((u.map fun y => X - C (δ * y)).prod).coeff i
      = δ ^ (Multiset.card u - i) * ((u.map fun y => X - C y).prod).coeff i := by
  have hc := Multiset.prod_X_sub_C_coeff (u.map (δ • ·)) (k := i) (by simpa using hi)
  rw [Multiset.map_map, Multiset.card_map, ← Multiset.pow_smul_esymm] at hc
  rw [Multiset.prod_X_sub_C_coeff u hi]
  simp only [Function.comp_def, smul_eq_mul] at hc
  rw [hc]
  ring

/-- The Taylor shift `P(X) ↦ P(X + a)` of `∏ (X - f x)` is `∏ (X - (f x - a))`. -/
theorem taylor_prod_X_sub_C {R S : Type*} [CommRing R] (s : Multiset S) (f : S → R) (a : R) :
    taylor a ((s.map fun x => X - C (f x)).prod) = (s.map fun x => X - C (f x - a)).prod := by
  change taylorAlgHom a _ = _
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply, map_sub]
  change taylor a X - taylor a (C (f x)) = _
  rw [taylor_X, taylor_C]
  ring

/-- If coefficient `i` of `∏_{x ∈ s} (X - (x - a))` vanishes and `δ ≠ 0`, then so does
coefficient `i` of `∏_{x ∈ s} (X - δ⁻¹ (x - a))`. -/
theorem scaled_coeff_eq_zero {L : Type*} [Field L] (s : Multiset L) (a δ : L) (hδ : δ ≠ 0)
    {i : ℕ} (hi : i ≤ Multiset.card s)
    (h : ((s.map fun x => X - C (x - a)).prod).coeff i = 0) :
    ((s.map fun x => X - C (δ⁻¹ * (x - a))).prod).coeff i = 0 := by
  have hsc := coeff_prod_X_sub_C_mul (s.map fun x => δ⁻¹ * (x - a)) δ (i := i)
    (by simpa using hi)
  rw [Multiset.map_map, Multiset.map_map] at hsc
  simp only [Function.comp_def, mul_inv_cancel_left₀ hδ, Multiset.card_map] at hsc
  rw [h] at hsc
  exact (mul_eq_zero.mp hsc.symm).resolve_left (pow_ne_zero _ hδ)

/-! ## Root form in characteristic zero -/

/-- **Root form of the main theorem**: over a field `L` of characteristic zero, let `s`
be a multiset of `p ^ k` elements (`p` prime) such that for each `1 ≤ i < p ^ k` some `a ∈ s`
is a root of the `i`-th Hasse derivative of `∏_{x ∈ s} (X - x)` (stated via the Taylor
coefficient `(taylor a P).coeff i = (hasseDeriv i P).eval a`).  Then all elements of `s` are
equal. -/
theorem eq_of_mem_of_taylor_coeff_eq_zero {L : Type*} [Field L] [CharZero L] {p k : ℕ}
    (hp : p.Prime) (s : Multiset L) (hs : Multiset.card s = p ^ k)
    (h : ∀ i, 1 ≤ i → i < p ^ k →
      ∃ a ∈ s, (taylor a (s.map fun x => X - C x).prod).coeff i = 0) :
    ∀ x ∈ s, ∀ y ∈ s, x = y := by
  by_contra hne
  push Not at hne
  obtain ⟨x0, hx0, y0, hy0, hxy⟩ := hne
  obtain ⟨B, hB⟩ := exists_valuationSubring_natCast_mem_maximalIdeal (L := L) hp
  obtain ⟨δ, hδD, hδ0, hdiv⟩ := exists_mem_ne_zero_forall_div_mem B (s.map (· - x0))
    ⟨y0 - x0, Multiset.mem_map_of_mem _ hy0, sub_ne_zero.mpr (Ne.symm hxy)⟩
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hδD
  have hγmem : ∀ x ∈ s, (x - x0) / (b - x0) ∈ B := fun x hx =>
    hdiv _ (Multiset.mem_map_of_mem _ hx)
  classical
  let γ : L → B := fun x => if hx : (x - x0) / (b - x0) ∈ B then ⟨_, hx⟩ else 0
  have hγ : ∀ x ∈ s, ((γ x : B) : L) = (x - x0) / (b - x0) := by
    intro x hx
    simp only [γ, dif_pos (hγmem x hx)]
  have hγ0 : γ x0 = 0 := by
    apply Subtype.ext
    rw [hγ x0 hx0, sub_self, zero_div]
    rfl
  have hγ1 : γ b = 1 := by
    apply Subtype.ext
    rw [hγ b hb, div_self hδ0]
    rfl
  let π := IsLocalRing.residue B
  let g : (IsLocalRing.ResidueField B)[X] := (s.map fun x => X - C (π (γ x))).prod
  have hpk : (p : IsLocalRing.ResidueField B) = 0 := by
    rw [← map_natCast π]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hB
  have hgm : g.Monic := monic_multiset_prod_of_monic _ _ fun c _ => monic_X_sub_C _
  have hgd : g.natDegree = p ^ k := by
    rw [← hs, ← Multiset.card_map (fun x => π (γ x)) s]
    have := natDegree_multiset_prod_X_sub_C_eq_card (s.map fun x => π (γ x))
    rw [Multiset.map_map] at this
    exact this
  have hg0 : g.eval 0 = 0 := by
    rw [eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.mpr ⟨x0, hx0, ?_⟩
    simp [hγ0]
  have hg1 : g.eval 1 = 0 := by
    rw [eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.mpr ⟨b, hb, ?_⟩
    simp [hγ1]
  have hder : ∀ i, 1 ≤ i → i < p ^ k → ∃ r, (hasseDeriv i g).eval r = 0 := by
    intro i hi1 hik
    obtain ⟨a, ha, hta⟩ := h i hi1 hik
    refine ⟨π (γ a), ?_⟩
    let gA : B[X] := (s.map fun x => X - C (γ x)).prod
    have hggA : g = gA.map π := by
      simp only [g, gA, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
        Polynomial.map_sub, map_X, map_C]
    have hgAL : gA.map B.subtype = (s.map fun x => X - C ((x - x0) / (b - x0))).prod := by
      simp only [gA, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
        Polynomial.map_sub, map_X, map_C]
      congr 1
      refine Multiset.map_congr rfl fun x hx => ?_
      rw [← hγ x hx]
      rfl
    have hA : (taylor (γ a) gA).coeff i = 0 := by
      apply Subtype.val_injective
      change B.subtype ((taylor (γ a) gA).coeff i) = B.subtype 0
      rw [map_zero, ← coeff_map, map_taylor, hgAL, taylor_prod_X_sub_C]
      have hcongr : (s.map fun x => X - C ((x - x0) / (b - x0) - B.subtype (γ a))).prod
          = (s.map fun x => X - C ((b - x0)⁻¹ * (x - a))).prod := by
        congr 1
        refine Multiset.map_congr rfl fun x _ => ?_
        change X - C ((x - x0) / (b - x0) - ((γ a : B) : L)) = _
        rw [hγ a ha, div_sub_div_same, div_eq_inv_mul, sub_sub_sub_cancel_right]
      rw [hcongr]
      refine scaled_coeff_eq_zero s a (b - x0) (sub_ne_zero.mpr ?_) (by omega) ?_
      · rintro rfl
        simp at hδ0
      · have hta' := hta
        rw [show (s.map fun x => X - C x) = (s.map fun x => X - C (id x)) from rfl,
          taylor_prod_X_sub_C] at hta'
        exact hta'
    rw [← taylor_coeff, hggA, ← map_taylor, coeff_map, hA, map_zero]
  have hX := eq_X_pow_of_hasseDeriv_roots hp hpk g hgm hgd hg0 hder
  rw [hX, eval_pow, eval_X, one_pow] at hg1
  exact one_ne_zero hg1

/-! ## Main theorem -/

/-- **Casas-Alvero conjecture in degree `p ^ k`** (arXiv:math/0605090, main Theorem,
case `d = p ^ k`): over a field `K` of characteristic zero, if `f ∈ K[X]` is monic of degree
`p ^ k` (`p` prime) and `gcd(f, f^(i)) ≠ 1` for `i = 1, …, p ^ k - 1`, then `f = (X - a) ^ d`
for some `a ∈ K`. -/
theorem casasAlvero_natDegree_eq_prime_pow {K : Type*} [Field K] [CharZero K] (f : K[X])
    (hm : f.Monic) {p k : ℕ} (hp : p.Prime) (hd : f.natDegree = p ^ k)
    (h : Candidates.CasasAlveroDegreeFour.SharesFactorWithDerivatives f) :
    ∃ a : K, f = (X - C a) ^ f.natDegree := by
  set φ := algebraMap K (AlgebraicClosure K)
  set F := f.map φ with hFdef
  have hFm : F.Monic := hm.map φ
  have hFd : F.natDegree = p ^ k := by rw [natDegree_map_eq_of_injective φ.injective, hd]
  have hsplit : F = (F.roots.map fun x => X - C x).prod :=
    (IsAlgClosed.splits F).eq_prod_roots_of_monic hFm
  have hcard : Multiset.card F.roots = p ^ k :=
    IsAlgClosed.card_roots_eq_natDegree.trans hFd
  have hroot : ∀ i, 1 ≤ i → i < p ^ k →
      ∃ a ∈ F.roots, (taylor a (F.roots.map fun x => X - C x).prod).coeff i = 0 := by
    intro i hi1 hik
    obtain ⟨a, ha, hda⟩ :=
      Candidates.CasasAlveroDegreeFour.common_roots_of_sharesFactorWithDerivatives f h i hi1
        (by omega)
    refine ⟨a, (mem_roots hFm.ne_zero).mpr ha, ?_⟩
    rw [← hsplit, taylor_coeff]
    rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul, nsmul_eq_mul] at hda
    exact (mul_eq_zero.mp hda).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i))
  have hall := eq_of_mem_of_taylor_coeff_eq_zero hp F.roots hcard hroot
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp (hcard ▸ hpk)
  have hrep : F.roots = Multiset.replicate (p ^ k) α :=
    Multiset.eq_replicate.mpr ⟨hcard, fun y hy => hall y hy α hα⟩
  have hFα : F = (X - C α) ^ (p ^ k) := by
    rw [hsplit, hrep, Multiset.map_replicate, Multiset.prod_replicate]
  have hcoeff : φ (f.coeff (p ^ k - 1)) = -α * (p ^ k : AlgebraicClosure K) := by
    rw [← coeff_map, ← hFdef, hFα, sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow,
      Nat.sub_sub_self (by omega), pow_one, Nat.choose_symm (by omega), Nat.choose_one_right]
    push_cast
    ring
  have hN : (p ^ k : AlgebraicClosure K) ≠ 0 := by exact_mod_cast hpk.ne'
  refine ⟨-f.coeff (p ^ k - 1) / (p ^ k : K), map_injective φ φ.injective ?_⟩
  have hβ : φ (-f.coeff (p ^ k - 1) / (p ^ k : K)) = α := by
    rw [map_div₀, map_neg, hcoeff, map_pow, map_natCast]
    field_simp
  rw [← hFdef, hFα, hd, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, hβ]

/-! ## Ground truth and non-vacuity -/

/-- Non-vacuity: `X ^ 4 ∈ ℚ[X]` (degree `2 ^ 2`) satisfies every hypothesis of
`casasAlvero_natDegree_eq_prime_pow` jointly; the theorem then yields `X ^ 4 = (X - C a) ^ 4`. -/
example : ∃ a : ℚ, (X ^ 4 : ℚ[X]) = (X - C a) ^ (X ^ 4 : ℚ[X]).natDegree := by
  have hshare : Candidates.CasasAlveroDegreeFour.SharesFactorWithDerivatives (X ^ 4 : ℚ[X]) := by
    intro i hi1 hi
    rw [natDegree_X_pow] at hi
    intro hcop
    have hXf : (X : ℚ[X]) ∣ X ^ 4 := dvd_pow_self X (by norm_num)
    have hXd : (X : ℚ[X]) ∣ derivative^[i] (X ^ 4) := by
      rw [iterate_derivative_X_pow_eq_C_mul]
      exact dvd_mul_of_dvd_right (dvd_pow_self X (by omega)) _
    exact not_isUnit_X (hcop.isUnit_of_dvd' hXf hXd)
  exact casasAlvero_natDegree_eq_prime_pow (X ^ 4 : ℚ[X]) (monic_X_pow 4) (k := 2)
    Nat.prime_two (by rw [natDegree_X_pow]; norm_num) hshare

/-- Ground truth for the char-`p` core: in `ZMod 2`, `C(4, j) = 0` for `j = 1, 2, 3`. -/
example : ((Nat.choose (2 ^ 2) 1 : ZMod 2) = 0) ∧ ((Nat.choose (2 ^ 2) 2 : ZMod 2) = 0) ∧
    ((Nat.choose (2 ^ 2) 3 : ZMod 2) = 0) := by decide

/-- Ground truth for the char-`p` core: `X ^ 2 + X` over `ZMod 2` has `g(0) = 0` but its first
Hasse derivative `2 X + 1 = 1` has no root, so the hypothesis of
`eq_X_pow_of_hasseDeriv_roots` correctly excludes it. -/
example : ∀ r : ZMod 2, (hasseDeriv 1 (X ^ 2 + X : (ZMod 2)[X])).eval r ≠ 0 := by
  intro r
  rw [hasseDeriv_one, derivative_add, derivative_X_pow, derivative_X]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one]
  fin_cases r <;> decide

end Candidates.CasasAlveroPrimePower
