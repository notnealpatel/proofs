/-
# Casas-Alvero conjecture in degree `2 p ^ k` (characteristic zero)

## Source

arXiv:math/0605090, Hans-Christian Graf von Bothmer, Oliver Labs, Josef Schicho,
Christiaan van de Woestijne, "The Casas-Alvero conjecture for infinitely many
degrees", J. Algebra 316 (2007).  Section 2 ("Mixing characteristics, or There
and Back Again"): Proposition `prop:case12` (degrees 1 and 2 over any field),
the Kummer Lemma, Proposition `prop:induc` (induction `d = n p ^ k`), and the
main Theorem (second family `d = 2 p ^ k`).  Recorded 2026-10-21.

Verbatim statements:

> **Conjecture (Casas-Alvero).** Let $P$ be a monic univariate polynomial of
> degree $d$ over a field $\KK$.  Then $\gcd(P,P_i)$ is nontrivial for
> $i=1,\ldots,d-1$ if and only if $P=(X-\alpha)^d$ for some $\alpha\in\KK$.

> **Theorem.** Let $d$ be of the form $p^k$ or $2p^k$ for some prime number
> $p$.  Then the Casas-Alvero Conjecture holds in characteristic $0$ for
> polynomials of degree $d$.

## Status

Proved in the paper (the case `d = 2 p ^ k` formalized here).  The conjecture
itself is open in general.

## Formalization

The hypothesis `gcd(f, f^(i)) ≠ 1` for `1 ≤ i < d` is the repository predicate
`SharesFactorWithDerivatives` of `NumberComplexity.CasasAlveroDegreeFour`
(non-coprimality of `f` and its `i`-th ordinary derivative; in characteristic
zero this is equivalent to the paper's Hasse-derivative condition).

The paper's transfer from characteristic `p` to characteristic `0`
(Proposition `prop:frompto0`, properness of a weighted projective scheme over
`Spec ℤ`) is replaced by the elementary valuation argument of Draisma and
de Jong (EMS Newsletter 2011): over `L = AlgebraicClosure K` choose a valuation
subring `B` with `p` in its maximal ideal, translate one root to `0` and rescale
by the root difference of largest valuation, so that the rescaled polynomial
has coefficients in `B`, roots `0` and `1`, and reduces to a polynomial over the
residue field (characteristic `p`) that still shares a root with each of its
Hasse derivatives.  The characteristic-`p` core (`charP_core`) is the paper's
`prop:induc` with `n = 2` combined with `prop:case12`, carried out without
taking `p ^ k`-th roots: all coefficients outside degrees `0, p ^ k, 2 p ^ k`
vanish, and the Hasse derivative of order `p ^ k` then forces
`g = (X ^ (p ^ k) - s) ^ 2`, incompatible with `g(0) = g(1) = 0`.

The reduction `casasAlvero_of_charP_core` is stated for an arbitrary degree `d`
and prime `p`; it reduces Casas-Alvero in degree `d` (characteristic zero) to
the non-existence of characteristic-`p` examples with roots `0` and `1`.
-/
import Mathlib
import NumberComplexity.CasasAlveroDegreeFour

set_option autoImplicit false

namespace Candidates.CasasAlveroTwoPrimePower

open Polynomial
open Candidates.CasasAlveroDegreeFour (SharesFactorWithDerivatives
  common_roots_of_sharesFactorWithDerivatives)

universe u

/-! ## Characteristic `p`: binomial coefficients and the core lemma -/

/-- Lucas-type congruence (the paper's Kummer Lemma in the form needed here): in a
commutative ring of characteristic `p`, with `q = p ^ k`, the binomial coefficient
`(q t).choose j` vanishes unless `q ∣ j`, in which case it equals `t.choose (j / q)`.
Proof: `(X + 1) ^ (q t) = (X ^ q + 1) ^ t` by the Frobenius. -/
theorem choose_mul_eq {F : Type*} [CommRing F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (k t j : ℕ) :
    (((p ^ k) * t).choose j : F) = if p ^ k ∣ j then (t.choose (j / p ^ k) : F) else 0 := by
  have hq : 0 < p ^ k := pow_pos hp.out.pos k
  have hX : ((X + 1 : F[X]) ^ (p ^ k * t)) = expand F (p ^ k) ((X + 1) ^ t) := by
    rw [pow_mul, add_pow_char_pow, one_pow, map_pow, map_add, expand_X, map_one]
  have h := congrArg (fun g => coeff g j) hX
  simp only [coeff_X_add_one_pow, coeff_expand hq] at h
  rw [h]

/-- Paper, Proposition `prop:induc` (first half) for `d = 2 p ^ k`: over a field of
characteristic `p`, if every Hasse derivative `D_i g` (`1 ≤ i < 2 p ^ k`) of `g` of
degree `2 p ^ k` has a root, then every coefficient `a_j` with `0 < j < 2 p ^ k` and
`p ^ k ∤ j` vanishes (descending induction: `D_j g` is the constant `a_j`). -/
theorem coeff_eq_zero_of_not_dvd {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (k : ℕ) (g : F[X]) (hd : g.natDegree = 2 * p ^ k)
    (h : ∀ i, 1 ≤ i → i < 2 * p ^ k → ∃ r, (hasseDeriv i g).eval r = 0) :
    ∀ j, 0 < j → j < 2 * p ^ k → ¬ p ^ k ∣ j → g.coeff j = 0 := by
  set q := p ^ k with hqdef
  have key : ∀ m j, 2 * q - j = m → 0 < j → j < 2 * q → ¬ q ∣ j → g.coeff j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hjm hj0 hjd hqj
      have hC : hasseDeriv j g = C (g.coeff j) := by
        ext n
        rw [hasseDeriv_coeff, coeff_C]
        split_ifs with hn
        · subst hn
          simp
        · by_cases hqn : q ∣ n + j
          · obtain ⟨t, ht⟩ := hqn
            rw [ht, hqdef, choose_mul_eq k t j, if_neg hqj, zero_mul]
          · rcases lt_or_ge (n + j) (2 * q) with hlt | hge
            · rw [ih (2 * q - (n + j)) (by omega) (n + j) rfl (by omega) hlt hqn, mul_zero]
            · have hne : n + j ≠ 2 * q := fun he => hqn (he ▸ dvd_mul_left q 2)
              rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      obtain ⟨r, hr⟩ := h j hj0 hjd
      rw [hC, eval_C] at hr
      exact hr
  intro j hj0 hjd hqj
  exact key _ j rfl hj0 hjd hqj

/-- Consequence of `coeff_eq_zero_of_not_dvd`: a monic `g` of degree `2 p ^ k` as there
is the trinomial `X ^ (2 p ^ k) + a_{p^k} X ^ (p ^ k) + a_0`. -/
theorem eq_trinomial {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (k : ℕ) (g : F[X]) (hm : g.Monic) (hd : g.natDegree = 2 * p ^ k)
    (h : ∀ i, 1 ≤ i → i < 2 * p ^ k → ∃ r, (hasseDeriv i g).eval r = 0) :
    g = X ^ (2 * p ^ k) + C (g.coeff (p ^ k)) * X ^ (p ^ k) + C (g.coeff 0) := by
  have hq : 0 < p ^ k := pow_pos hp.out.pos k
  have hz := coeff_eq_zero_of_not_dvd k g hd h
  ext n
  simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C]
  by_cases h2 : n = 2 * p ^ k
  · subst h2
    rw [if_pos rfl, if_neg (by omega), if_neg (by omega), ← hd, hm.coeff_natDegree]
    ring
  by_cases h1 : n = p ^ k
  · subst h1
    rw [if_neg (by omega), if_pos rfl, if_neg (by omega)]
    ring
  by_cases h0 : n = 0
  · subst h0
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    ring
  rw [if_neg h2, if_neg h1, if_neg h0]
  rcases lt_or_ge n (2 * p ^ k) with hlt | hge
  · have hnd : ¬ p ^ k ∣ n := by
      rintro ⟨t, rfl⟩
      rcases t with _ | _ | t
      · omega
      · omega
      · nlinarith
    rw [hz n (by omega) hlt hnd]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    ring

/-- **Characteristic-`p` core** (paper, Propositions `prop:induc` with `n = 2` and
`prop:case12`): over a field of characteristic `p` there is no monic `g` of degree
`2 p ^ k` with `g(0) = g(1) = 0` that shares a root with each of its Hasse
derivatives `D_i g`, `1 ≤ i < 2 p ^ k`. -/
theorem charP_core {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (k : ℕ) (g : F[X]) (hm : g.Monic) (hd : g.natDegree = 2 * p ^ k)
    (h0 : g.eval 0 = 0) (h1 : g.eval 1 = 0)
    (h : ∀ i, 1 ≤ i → i < 2 * p ^ k → ∃ r, g.eval r = 0 ∧ (hasseDeriv i g).eval r = 0) :
    False := by
  have hq : 0 < p ^ k := pow_pos hp.out.pos k
  have hg := eq_trinomial k g hm hd (fun i hi1 hi => (h i hi1 hi).imp fun _ hr => hr.2)
  set b := g.coeff (p ^ k)
  set c := g.coeff 0
  obtain ⟨r, hr0, hr1⟩ := h (p ^ k) hq (by omega)
  have hD : hasseDeriv (p ^ k) g = C 2 * X ^ (p ^ k) + C b := by
    have hch : ((2 * p ^ k).choose (p ^ k) : F) = 2 := by
      rw [mul_comm, choose_mul_eq k 2 (p ^ k), if_pos dvd_rfl, Nat.div_self hq]
      norm_num
    rw [hg, map_add, map_add, X_pow_eq_monomial, C_mul_X_pow_eq_monomial, hasseDeriv_monomial,
      hasseDeriv_monomial, hasseDeriv_C _ _ hq, hch, Nat.choose_self, Nat.sub_self,
      show 2 * p ^ k - p ^ k = p ^ k by omega, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    simp
  rw [hD] at hr1
  rw [hg] at hr0 h0 h1
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hr0 hr1 h0 h1
  set s := r ^ p ^ k with hs
  have hb : b = -2 * s := by linear_combination hr1
  have hc : c = s ^ 2 := by
    have hr2 : r ^ (2 * p ^ k) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
    linear_combination hr0 - hr2 - s * hr1
  have hq0 : (0 : F) ^ (2 * p ^ k) = 0 := zero_pow (by omega)
  have hq0' : (0 : F) ^ (p ^ k) = 0 := zero_pow (by omega)
  rw [hq0, hq0', hc] at h0
  have hs0 : s = 0 := by simpa using h0
  rw [one_pow, one_pow, hb, hc, hs0] at h1
  norm_num at h1

/-! ## Characteristic zero: valuation, rescaling and reduction -/

/-- In a field of characteristic zero, some valuation subring has the prime `p` in
its maximal ideal (`p` is a nonunit of the prime subring; Chevalley extension). -/
theorem exists_valuationSubring_prime_nonunit {L : Type*} [Field L] [CharZero L] {p : ℕ}
    (hp : p.Prime) : ∃ B : ValuationSubring L, (p : L) ∈ B.nonunits := by
  let A : Subring L := ⊥
  let I : Ideal A := Ideal.span {(p : A)}
  have hI : I ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp htop
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp w.2
    have hL : ((p * n : ℤ) : L) = ((1 : ℤ) : L) := by
      have hw' := congrArg Subtype.val hw
      push_cast at hw' ⊢
      rw [hn]
      exact hw'
    have hZ : (p : ℤ) * n = 1 := Int.cast_injective hL
    have hdvd : (p : ℤ) ∣ 1 := ⟨n, hZ.symm⟩
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hdvd)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨B, hB ⟨(p : A), Ideal.subset_span rfl, by simp⟩⟩

/-- If `p` is a nonunit of the valuation subring `B`, then `p = 0` in the residue
field of `B`. -/
theorem residue_prime_eq_zero {L : Type*} [Field L] {p : ℕ} (B : ValuationSubring L)
    (hB : (p : L) ∈ B.nonunits) : (p : IsLocalRing.ResidueField B) = 0 := by
  rw [← map_natCast (IsLocalRing.residue B), IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
  simpa using hB

/-- Chain rule for an affine substitution:
`(F ∘ (δ X + a))^(i) = δ ^ i · F^(i) ∘ (δ X + a)`. -/
theorem iterate_derivative_comp_affine {R : Type*} [CommRing R] (F : R[X]) (δ a : R) (i : ℕ) :
    derivative^[i] (F.comp (C δ * X + C a)) =
      C (δ ^ i) * (derivative^[i] F).comp (C δ * X + C a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp,
      Function.iterate_succ_apply']
    simp only [derivative_add, derivative_C_mul, derivative_X, derivative_C, mul_one, add_zero]
    rw [pow_succ, C_mul]
    ring

/-- Hasse derivatives commute with base change along a ring homomorphism. -/
theorem hasseDeriv_map {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) (g : R[X]) (i : ℕ) :
    hasseDeriv i (g.map ψ) = (hasseDeriv i g).map ψ := by
  ext n
  simp only [hasseDeriv_coeff, coeff_map, map_mul, map_natCast]

/-- In characteristic zero, a root of the ordinary derivative `g^(i)` is a root of
the Hasse derivative `D_i g = g^(i) / i!`. -/
theorem eval_hasseDeriv_eq_zero {L : Type*} [Field L] [CharZero L] (g : L[X]) (i : ℕ) (x : L)
    (h : (derivative^[i] g).eval x = 0) : (hasseDeriv i g).eval x = 0 := by
  have hfac := congrFun (factorial_smul_hasseDeriv (R := L) (k := i)) g
  rw [← hfac] at h
  rw [LinearMap.smul_apply, eval_smul, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i))


/-- **Mixed-characteristic transfer, root form** (replacing the paper's Proposition
`prop:frompto0` by the Draisma-de Jong valuation argument): let `L` be an
algebraically closed field of characteristic zero and `p` a prime.  If no field of
characteristic `p` carries a monic `g` of degree `d` with `g(0) = g(1) = 0` sharing
a root with every Hasse derivative `D_i g`, `1 ≤ i < d`, then every monic `F ∈ L[X]`
of degree `d` sharing a root with every `F^(i)`, `1 ≤ i < d`, is `(X - a) ^ d`. -/
theorem eq_X_sub_C_pow_of_charP_core {L : Type u} [Field L] [IsAlgClosed L] [CharZero L]
    {p d : ℕ} (hp : p.Prime)
    (hcore : ∀ (F : Type u) [Field F] [CharP F p] (g : F[X]), g.Monic → g.natDegree = d →
      g.eval 0 = 0 → g.eval 1 = 0 →
      (∀ i, 1 ≤ i → i < d → ∃ r, g.eval r = 0 ∧ (hasseDeriv i g).eval r = 0) → False)
    (F : L[X]) (hm : F.Monic) (hd : F.natDegree = d)
    (hroot : ∀ i, 1 ≤ i → i < d → ∃ α, F.eval α = 0 ∧ (derivative^[i] F).eval α = 0) :
    ∃ a, F = (X - C a) ^ d := by
  classical
  have hcard : Multiset.card F.roots = d := by rw [IsAlgClosed.card_roots_eq_natDegree, hd]
  have hsplit : (F.roots.map fun a => X - C a).prod = F :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hcard, hd])
  by_cases hconst : ∃ a, ∀ α ∈ F.roots, α = a
  · obtain ⟨a, ha⟩ := hconst
    refine ⟨a, ?_⟩
    rw [← hsplit, Multiset.eq_replicate.mpr ⟨hcard, ha⟩, Multiset.map_replicate,
      Multiset.prod_replicate]
  exfalso
  push Not at hconst
  obtain ⟨a0, ha0, -⟩ := hconst 0
  obtain ⟨β, hβ, hβa0⟩ := hconst a0
  obtain ⟨B, hB⟩ := exists_valuationSubring_prime_nonunit (L := L) hp
  let S : Finset L := (F.roots.toFinset.image (· - a0)).filter (· ≠ 0)
  have hβS : β - a0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_image, Multiset.mem_toFinset]
    exact ⟨⟨β, hβ, rfl⟩, sub_ne_zero.mpr hβa0⟩
  obtain ⟨δ, hδS, hδmax⟩ := S.exists_max_image B.valuation ⟨_, hβS⟩
  have hδ0 : δ ≠ 0 := (Finset.mem_filter.mp hδS).2
  have hmem : ∀ α ∈ F.roots, (α - a0) / δ ∈ B := by
    intro α hα
    by_cases hα0 : α - a0 = 0
    · rw [hα0, zero_div]
      exact B.zero_mem
    · apply B.mem_of_valuation_le_one
      have hαS : α - a0 ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_image, Multiset.mem_toFinset]
        exact ⟨⟨α, hα, rfl⟩, hα0⟩
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).mpr hδ0)]
      exact hδmax _ hαS
  let lift : L → B := fun x => if hx : x ∈ B then ⟨x, hx⟩ else 0
  have hlift : ∀ x ∈ B, ((lift x : B) : L) = x := by
    intro x hx
    simp only [lift, dif_pos hx]
  let ι : B →+* L := B.subtype
  have hι : Function.Injective ι := Subtype.val_injective
  let γ : L → L := fun α => (α - a0) / δ
  let Γ : Multiset B := F.roots.map fun α => lift (γ α)
  let g0 : B[X] := (Γ.map fun c => X - C c).prod
  have hg0m : g0.Monic := monic_multiset_prod_of_monic _ _ (fun c _ => monic_X_sub_C c)
  have hg0d : g0.natDegree = d := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, hcard]
  have hcomp : F.comp (C δ * X + C a0) = C (δ ^ d) * g0.map ι := by
    have hfac : ∀ α ∈ F.roots,
        (X - C α).comp (C δ * X + C a0) = C δ * (X - C (ι (lift (γ α)))) := by
      intro α hα
      rw [show ι (lift (γ α)) = γ α from hlift _ (hmem α hα)]
      simp only [sub_comp, X_comp, C_comp, γ, mul_sub, ← C_mul]
      rw [mul_div_cancel₀ _ hδ0, C_sub]
      ring
    conv_lhs => rw [← hsplit]
    rw [multiset_prod_comp, Multiset.map_map, Polynomial.map_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    rw [show F.roots.map ((fun p => p.comp (C δ * X + C a0)) ∘ fun a => X - C a) =
        F.roots.map (fun α => C δ * (X - C (ι (lift (γ α))))) from Multiset.map_congr rfl hfac,
      Multiset.prod_map_mul, Multiset.map_const',
      Multiset.prod_replicate, hcard, ← C_pow]
    congr 2
    apply Multiset.map_congr rfl
    intro α _
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
  have hkey : ∀ α ∈ F.roots, ∀ i, (derivative^[i] F).eval α = 0 →
      (hasseDeriv i g0).eval (lift (γ α)) = 0 := by
    intro α hα i hi
    have hγ : ι (lift (γ α)) = γ α := hlift _ (hmem α hα)
    have hD := congrArg (fun P => (derivative^[i] P).eval (γ α)) hcomp
    rw [iterate_derivative_comp_affine, iterate_derivative_C_mul, eval_mul, eval_mul, eval_C,
      eval_C, eval_comp] at hD
    have hq : (C δ * X + C a0).eval (γ α) = α := by
      simp only [eval_add, eval_mul, eval_C, eval_X, γ]
      rw [mul_div_cancel₀ _ hδ0]
      ring
    rw [hq, hi, mul_zero] at hD
    have h1 : (derivative^[i] (g0.map ι)).eval (γ α) = 0 :=
      (mul_eq_zero.mp hD.symm).resolve_left (pow_ne_zero _ hδ0)
    have h2 := eval_hasseDeriv_eq_zero _ i _ h1
    rw [hasseDeriv_map, ← hγ, eval_map, eval₂_at_apply] at h2
    exact (map_eq_zero_iff ι hι).mp h2
  let π := IsLocalRing.residue B
  haveI : CharP (IsLocalRing.ResidueField B) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr (residue_prime_eq_zero B hB)
  have hev : ∀ α ∈ F.roots, ∀ i, (derivative^[i] F).eval α = 0 →
      (hasseDeriv i (g0.map π)).eval (π (lift (γ α))) = 0 := by
    intro α hα i hi
    rw [hasseDeriv_map, eval_map, eval₂_at_apply, hkey α hα i hi, map_zero]
  have hev0 : ∀ α ∈ F.roots, (g0.map π).eval (π (lift (γ α))) = 0 := by
    intro α hα
    have h0 := hev α hα 0 (by
      rw [Function.iterate_zero, id]
      exact (mem_roots hm.ne_zero).mp hα)
    rwa [hasseDeriv_zero, LinearMap.id_apply] at h0
  obtain ⟨α1, hα1, hα1δ⟩ : ∃ α1 ∈ F.roots, α1 - a0 = δ := by
    have h := (Finset.mem_filter.mp hδS).1
    simp only [Finset.mem_image, Multiset.mem_toFinset] at h
    exact h
  have hl0 : π (lift (γ a0)) = 0 := by
    have hz : lift (γ a0) = 0 := Subtype.ext (by
      rw [hlift _ (hmem a0 ha0)]
      simp)
    rw [hz, map_zero]
  have hl1 : π (lift (γ α1)) = 1 := by
    have hz : lift (γ α1) = 1 := Subtype.ext (by
      rw [hlift _ (hmem α1 hα1)]
      simp [hα1δ, hδ0])
    rw [hz, map_one]
  refine hcore _ (g0.map π) (hg0m.map π) (by rw [hg0m.natDegree_map, hg0d])
    (hl0 ▸ hev0 a0 ha0) (hl1 ▸ hev0 α1 hα1) ?_
  intro i hi1 hi
  obtain ⟨α, hα0, hαi⟩ := hroot i hi1 hi
  have hα : α ∈ F.roots := (mem_roots hm.ne_zero).mpr hα0
  exact ⟨_, hev0 α hα, hev α hα i hαi⟩

/-- Descent: if `f ∈ K[X]` (characteristic zero) becomes `(X - a) ^ d` with `d > 0`
after an embedding `K → L`, then `f = (X - b) ^ d` already over `K`, with
`b = -a_{d-1} / d`. -/
theorem exists_eq_X_sub_C_pow_of_map {K L : Type*} [Field K] [CharZero K] [Field L]
    (φ : K →+* L) (f : K[X]) (d : ℕ) (hd : 0 < d) (a : L) (hf : f.map φ = (X - C a) ^ d) :
    ∃ b : K, f = (X - C b) ^ d := by
  have hcoeff : φ (f.coeff (d - 1)) = -a * d := by
    rw [← coeff_map, hf, sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow,
      Nat.sub_sub_self hd, pow_one, Nat.choose_symm (by omega : 1 ≤ d), Nat.choose_one_right]
  refine ⟨-(f.coeff (d - 1)) / d, map_injective φ φ.injective ?_⟩
  have hd0 : (d : L) ≠ 0 := by
    rw [← map_natCast φ]
    exact (map_ne_zero φ).mpr (Nat.cast_ne_zero.mpr hd.ne')
  have hb : φ (-(f.coeff (d - 1)) / d) = a := by
    rw [map_div₀, map_neg, hcoeff, map_natCast]
    field_simp
  rw [hf, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, hb]

/-! ## Main theorems -/

/-- **Reduction of Casas-Alvero to characteristic `p`** (the paper's mixing of
characteristics, Proposition `prop:frompto0`, in valuation form): let `K` be a field
of characteristic zero, `p` a prime and `d` a degree such that no field of
characteristic `p` carries a monic `g` of degree `d` with `g(0) = g(1) = 0` sharing a
root with each Hasse derivative `D_i g`, `1 ≤ i < d`.  Then every monic `f ∈ K[X]` of
degree `d` with `gcd(f, f^(i)) ≠ 1` for `1 ≤ i < d` equals `(X - a) ^ d` for some
`a ∈ K`. -/
theorem casasAlvero_of_charP_core {K : Type u} [Field K] [CharZero K] {p d : ℕ}
    (hp : p.Prime)
    (hcore : ∀ (F : Type u) [Field F] [CharP F p] (g : F[X]), g.Monic → g.natDegree = d →
      g.eval 0 = 0 → g.eval 1 = 0 →
      (∀ i, 1 ≤ i → i < d → ∃ r, g.eval r = 0 ∧ (hasseDeriv i g).eval r = 0) → False)
    (f : K[X]) (hm : f.Monic) (hd : f.natDegree = d) (h : SharesFactorWithDerivatives f) :
    ∃ a : K, f = (X - C a) ^ f.natDegree := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · refine ⟨0, ?_⟩
    rw [hd, hd0, pow_zero]
    exact Candidates.CasasAlveroDegreeFour.eq_one_of_natDegree_eq_zero f hm (hd.trans hd0)
  set φ := algebraMap K (AlgebraicClosure K)
  have hdL : (f.map φ).natDegree = d := by rw [natDegree_map_eq_of_injective φ.injective, hd]
  obtain ⟨a, ha⟩ := eq_X_sub_C_pow_of_charP_core hp hcore (f.map φ) (hm.map φ) hdL
    (fun i hi1 hi => common_roots_of_sharesFactorWithDerivatives f h i hi1 (by omega))
  rw [hd]
  exact exists_eq_X_sub_C_pow_of_map φ f d hdpos a ha

/-- **Casas-Alvero conjecture in degree `2 p ^ k`** (arXiv:math/0605090, main Theorem,
second family; proved in the paper): let `K` be a field of characteristic zero, `p` a
prime and `k ≥ 0`.  If `f ∈ K[X]` is monic of degree `2 p ^ k` and
`gcd(f, f^(i)) ≠ 1` for `i = 1, …, 2 p ^ k - 1`, then `f = (X - a) ^ (2 p ^ k)` for
some `a ∈ K`. -/
theorem casasAlvero_two_mul_prime_pow {K : Type u} [Field K] [CharZero K] (f : K[X])
    (hm : f.Monic) {p k : ℕ} (hp : p.Prime) (hd : f.natDegree = 2 * p ^ k)
    (h : SharesFactorWithDerivatives f) : ∃ a : K, f = (X - C a) ^ f.natDegree := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact casasAlvero_of_charP_core hp
    (fun F _ _ g hgm hgd hg0 hg1 hgi => charP_core k g hgm hgd hg0 hg1 hgi) f hm hd h

/-! ## Non-vacuity -/

/-- Ground truth / satisfiability: `X ^ 6 = X ^ (2 · 3 ^ 1)` over `ℚ` satisfies every
hypothesis of `casasAlvero_two_mul_prime_pow` (with `p = 3`, `k = 1`), and the
theorem returns the expected form. -/
example : ∃ a : ℚ, (X ^ 6 : ℚ[X]) = (X - C a) ^ (X ^ 6 : ℚ[X]).natDegree := by
  have hsh : SharesFactorWithDerivatives (X ^ 6 : ℚ[X]) := by
    intro i hi1 hi
    rw [natDegree_X_pow] at hi
    intro hcop
    have hXf : (X : ℚ[X]) ∣ X ^ 6 := dvd_pow_self X (by norm_num)
    have hXd : (X : ℚ[X]) ∣ derivative^[i] (X ^ 6) := by
      rw [iterate_derivative_X_pow_eq_C_mul]
      exact dvd_mul_of_dvd_right (dvd_pow_self X (by omega)) _
    exact not_isUnit_X (hcop.isUnit_of_dvd' hXf hXd)
  exact casasAlvero_two_mul_prime_pow (X ^ 6) (monic_X_pow 6) (k := 1) Nat.prime_three
    (by rw [natDegree_X_pow]; norm_num) hsh

/-- Ground truth for `choose_mul_eq`: in characteristic `3`, `(2 · 3).choose 3 = 2`
and `(2 · 3).choose 2 = 0`. -/
example : (((2 * 3).choose 3 : ℕ) : ZMod 3) = 2 ∧ (((2 * 3).choose 2 : ℕ) : ZMod 3) = 0 := by
  decide

end Candidates.CasasAlveroTwoPrimePower
