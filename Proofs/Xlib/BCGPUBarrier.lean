import Xlib.TPP
import Xlib.CharDegrees
import Xlib.FourierBarrier

/-!
# The BCGPU `n(G)` barrier and the normalizer barrier

This file states the two structural barriers of Blasiak–Church–Cohn–Grochow–Umans,
*Matrix multiplication via matrix groups* [arXiv:2204.03826], for the Cohn–Umans
group-theoretic approach to fast matrix multiplication.

The first barrier (BCGPU **Theorem 3.2**, `bcgpu_thm_3_2` below) is a
representation-theoretic bound on any Triple Product Property triple `(S, T, U)`
in terms of the *second-smallest irreducible representation dimension* `n(G)`:
\[ |S|\,|T|\,|U| \le \frac{|G|^{3/2}}{n(G)^{1/2}} + |G|. \]
It is the engine of the **Lie-type barrier** (BCGPU Corollary 3.4): since groups
of Lie type satisfy `n(G) ≥ Ω(|G|^δ)`, the right-hand side falls short of the
`|G|^{3/2}` packing bound by a polynomial factor, so no family of groups of Lie
type can prove `ω = 2` via the TPP. We state the finite, per-group inequality
kernel of that corollary (`bcgpu_cor_3_4_kernel`); the asymptotic `ω`-statement
itself is not faithfully formalizable (it quantifies over families of groups and
references the matrix-multiplication exponent, neither of which is available
here).

The second barrier (BCGPU **Theorem 3.6**, `bcgpu_thm_3_6` below) applies to TPP
triples of *subgroups* `H₁, H₂, H₃`. Writing `sᵢ = |N(Hᵢ)| / |Hᵢ|` for the
normalizer index, it gives
\[ |H_1|\,|H_2|\,|H_3| \le \frac{|G|^{3/2}}{(s_1 s_2 s_3)^{1/4}}, \]
so subgroups should be taken as close to **self-normalizing** (`sᵢ = 1`) as
possible. The companion **center barrier** (BCGPU Corollary 3.8,
`bcgpu_cor_3_8`) specializes this via `Z(G) ⊆ N(Hᵢ)`.

## Proof status

The normalizer barrier (Theorem 3.6, `bcgpu_thm_3_6`) and the center barrier
(Corollary 3.8, `bcgpu_cor_3_8`) are fully proved here. Theorem 3.2 and its
corollaries (3.3, 3.4, 3.5) remain `sorry`-skeletons. The barrier of Theorem 3.2
is a nonabelian Fourier / second-moment estimate (a Cauchy–Schwarz argument over
the character degrees, following Gowers' mixing theorem for quasirandom groups).
It needs the *indexed* representation-theory layer — Fourier inversion, Parseval,
and the per-irrep operator-norm bound — which sits on top of the
character-degree foundation `Xlib.CharDegrees` (itself carrying the single
Wedderburn `sorry`). Theorem 3.6 is an injectivity argument on
`H₁ × (N(H₁) ∩ H₂) × H₃`; it and Corollary 3.8 are proved by elementary
counting, so they do not depend on the deferred representation-theory layer.

## Main statements

* `Xlib.BCGPUBarrier.bcgpu_thm_3_2` — **(`sorry`)** the `n(G)` barrier.
* `Xlib.BCGPUBarrier.bcgpu_cor_3_3` — **(`sorry`)** the `n(G) ≥ |G|^δ` kernel of
  the "cannot meet the packing bound" corollary.
* `Xlib.BCGPUBarrier.bcgpu_cor_3_4_kernel` — **(`sorry`)** the Lie-type barrier,
  as a per-group inequality `|S||T||U| ≤ |G|^{(3-δ)/2} + |G|`.
* `Xlib.BCGPUBarrier.bcgpu_cor_3_5` — **(`sorry`)** the `√2` corollary,
  `|S||T||U| ≤ |G|^{3/2}/√2 + |G|`, for *any* finite group.
* `Xlib.BCGPUBarrier.bcgpu_thm_3_6` — the normalizer barrier.
* `Xlib.BCGPUBarrier.bcgpu_cor_3_8` — the center barrier.

## References

* J. Blasiak, T. Church, H. Cohn, J. Grochow, C. Umans, *Matrix multiplication
  via matrix groups*, [arXiv:2204.03826]. Theorem 3.2 = `thm:gowerstrick`,
  Corollary 3.3 = `cor:bigreps`, Corollary 3.4 = `cor:liebarrier`,
  Corollary 3.5 (the `√2` corollary), Theorem 3.6 = `thm:normbarrier`,
  Corollary 3.8 = `cor:centerbarrier`.
* H. Cohn, C. Umans, *A group-theoretic approach to fast matrix multiplication*,
  [arXiv:math/0307321] (Lemma 3.1: the abelian bound; Theorem 4.1: the capacity
  bound).
-/

open scoped BigOperators

namespace Xlib.BCGPUBarrier

open Xlib.TPP Xlib.CharDegrees

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- `n(G)`, the second-smallest irreducible representation dimension, as a real
number. This is `Xlib.CharDegrees.minNontrivIrrepDim G` cast to `ℝ`; it equals
`0` for abelian `G` and is `≥ 2` for nonabelian `G`. -/
noncomputable def nG (G : Type*) [Group G] [Fintype G] : ℝ :=
  (minNontrivIrrepDim G : ℝ)

/-! ### BCGPU Theorem 3.2: the representation-theoretic barrier -/

/-- **The `n(G)` bridge for nonabelian groups**: a nonabelian finite group has
an irreducible representation of dimension `> 1`, and therefore
`n(G) = minNontrivIrrepDim G ≥ 2`.  Extract any Wedderburn decomposition; were
all blocks of dimension `≤ 1`, the group algebra — hence the group — would be
commutative (`Xlib.FourierBarrier.exists_one_lt_dim_of_nonabelian`), so some
block dimension exceeds `1`, and through the bridge lemma
`charDegrees_eq_of_algEquiv` the filtered minimum defining `minNontrivIrrepDim`
is attained at a degree `> 1`. -/
theorem two_le_minNontrivIrrepDim (hG : ∃ a b : G, a * b ≠ b * a) :
    2 ≤ minNontrivIrrepDim G := by
  classical
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨k, d, hd, ⟨e₀⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hd
  have hbridge := charDegrees_eq_of_algEquiv G e₀
  obtain ⟨i₁, hi₁⟩ := Xlib.FourierBarrier.exists_one_lt_dim_of_nonabelian e₀ hG
  have hmem : d i₁ ∈ ((charDegrees G).filter (fun m => m > 1)).toFinset := by
    rw [Multiset.mem_toFinset, Multiset.mem_filter, hbridge]
    exact ⟨Multiset.mem_map.mpr ⟨i₁, Finset.mem_val.mpr (Finset.mem_univ i₁), rfl⟩, hi₁⟩
  have hne : ((charDegrees G).filter (fun m => m > 1)).toFinset.min ≠ ⊤ := by
    intro htop
    exact Finset.ne_empty_of_mem hmem (Finset.min_eq_top.mp htop)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
  have hmm := Finset.mem_of_min hm.symm
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hmm
  have h1 : 1 < m := hmm.2
  unfold minNontrivIrrepDim
  rw [← hm, WithTop.untopD_coe]
  omega

/-- **BCGPU Theorem 3.2** (`thm:gowerstrick`, arXiv:2204.03826).

If subsets `S`, `T`, `U` satisfy the Triple Product Property in a finite
*nonabelian* group `G`, then
\[ |S|\,|T|\,|U| \le \frac{|G|^{3/2}}{n(G)^{1/2}} + |G|, \]
where `n(G) = minNontrivIrrepDim G` is the smallest dimension `> 1` of an
irreducible complex representation of `G`.

Nonabelianness (`hG`) guarantees `n(G) ≥ 2 > 0`, so the right-hand side is finite
and the bound is meaningful. This is the fundamental barrier of the paper: a
family of groups with `n(G)` growing as a power of `|G|` cannot meet the
`|G|^{3/2}` packing bound.

**Proof.** Extract an indexed Wedderburn decomposition
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`), make it unitary
by the unitarian trick (`Xlib.FourierBarrier.exists_isUnitary`), and identify
its block dimensions with `charDegrees G` via `charDegrees_eq_of_algEquiv`.
The analytic core — Fourier inversion of the six-fold Gowers convolution at the
identity, isolation of the trivial-representation term `(|S||T||U|)²`, and the
Cauchy–Schwarz/Parseval estimate of the blocks of dimension `> 1` — is
`Xlib.FourierBarrier.master_bound`, applied with `n := minNontrivIrrepDim G`
(which lower-bounds every block dimension `> 1` by minimality, and is `≥ 2` by
`two_le_minNontrivIrrepDim`). -/
theorem bcgpu_thm_3_2 {S T U : Finset G} (hG : ∃ a b : G, a * b ≠ b * a)
    (h : TripleProductProperty S T U) :
    (S.card * T.card * U.card : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (nG G)
        + (Fintype.card G : ℝ) := by
  classical
  -- degenerate cases: an empty set makes the left side zero
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have h0 : ((Finset.card (∅ : Finset G) : ℝ)) * T.card * U.card = 0 := by simp
    rw [h0]
    positivity
  rcases T.eq_empty_or_nonempty with rfl | hT
  · have h0 : (S.card : ℝ) * (Finset.card (∅ : Finset G) : ℝ) * U.card = 0 := by simp
    rw [h0]
    positivity
  rcases U.eq_empty_or_nonempty with rfl | hU
  · have h0 : (S.card : ℝ) * T.card * (Finset.card (∅ : Finset G) : ℝ) = 0 := by simp
    rw [h0]
    positivity
  -- extract a unitary Wedderburn decomposition
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨k, d, hd, ⟨e₀⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hd
  obtain ⟨e, he⟩ := Xlib.FourierBarrier.exists_isUnitary e₀
  -- identify the block dimensions with the character degrees
  have hbridge := charDegrees_eq_of_algEquiv G e
  have hmem : ∀ i, 1 < d i →
      d i ∈ ((charDegrees G).filter (fun m => m > 1)).toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, Multiset.mem_filter, hbridge]
    exact ⟨Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), rfl⟩, hi⟩
  -- `n(G)` lower-bounds every block dimension exceeding `1`
  have hnd : ∀ i, 1 < d i → minNontrivIrrepDim G ≤ d i := by
    intro i hi
    have hminle := Finset.min_le (hmem i hi)
    have hne : ((charDegrees G).filter (fun m => m > 1)).toFinset.min ≠ ⊤ := by
      intro htop
      rw [htop] at hminle
      exact WithTop.not_top_le_coe _ hminle
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hm] at hminle
    unfold minNontrivIrrepDim
    rw [← hm, WithTop.untopD_coe]
    exact WithTop.coe_le_coe.mp hminle
  exact Xlib.FourierBarrier.master_bound he (two_le_minNontrivIrrepDim hG) hnd
    h hS hT hU

/-! ### BCGPU Corollary 3.3: groups with large `n(G)` miss the packing bound -/

/-- **BCGPU Corollary 3.3** (`cor:bigreps`, arXiv:2204.03826), finite kernel.

If `n(G) ≥ |G|^δ` for some `δ > 0` (the growth condition satisfied by groups of
Lie type of bounded rank), then any TPP triple `(S, T, U)` in the nonabelian
group `G` obeys
\[ |S|\,|T|\,|U| \le |G|^{(3-δ)/2} + |G|. \]
This is the per-group inequality underlying the asymptotic statement that no
family with `n(Gᵢ) ≥ Ω(|Gᵢ|^δ)` can meet the packing bound `|G|^{3/2 - o(1)}`:
the leading term `|G|^{(3-δ)/2}` is a *polynomial factor* `|G|^{δ/2}` below the
packing target `|G|^{3/2}`.

**Proof.** Substitute `n(G)^{1/2} ≥ |G|^{δ/2}` into
`bcgpu_thm_3_2`, so `|G|^{3/2}/n(G)^{1/2} ≤ |G|^{3/2}/|G|^{δ/2} = |G|^{(3-δ)/2}`. -/
theorem bcgpu_cor_3_3 {S T U : Finset G} {δ : ℝ} (hδ : 0 < δ)
    (hG : ∃ a b : G, a * b ≠ b * a)
    (hn : (Fintype.card G : ℝ) ^ δ ≤ nG G) (h : TripleProductProperty S T U) :
    (S.card * T.card * U.card : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 - δ) / 2) + (Fintype.card G : ℝ) := by
  have hNpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h32 := bcgpu_thm_3_2 hG h
  -- `√(n(G)) ≥ |G|^{δ/2} > 0`
  have hs1 : (Fintype.card G : ℝ) ^ (δ / 2) ≤ Real.sqrt (nG G) := by
    have hsq : Real.sqrt ((Fintype.card G : ℝ) ^ δ) ≤ Real.sqrt (nG G) :=
      Real.sqrt_le_sqrt hn
    rwa [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le,
      show δ * (1 / 2) = δ / 2 by ring] at hsq
  have hpos : (0 : ℝ) < (Fintype.card G : ℝ) ^ (δ / 2) :=
    Real.rpow_pos_of_pos hNpos _
  have hdiv : (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (nG G)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / (Fintype.card G : ℝ) ^ (δ / 2) :=
    div_le_div_of_nonneg_left (by positivity) hpos hs1
  have heq : (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / (Fintype.card G : ℝ) ^ (δ / 2)
      = (Fintype.card G : ℝ) ^ ((3 - δ) / 2) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  calc (S.card * T.card * U.card : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (nG G)
          + (Fintype.card G : ℝ) := h32
    _ ≤ (Fintype.card G : ℝ) ^ ((3 - δ) / 2) + (Fintype.card G : ℝ) := by
        rw [← heq]
        linarith

/-! ### BCGPU Corollary 3.4: the Lie-type barrier -/

/-- **BCGPU Corollary 3.4** (`cor:liebarrier`, arXiv:2204.03826), finite kernel.

The full corollary states that there is an absolute `ε > 0` such that no TPP
construction in a *group of Lie type* can prove a bound on the
matrix-multiplication exponent `ω` better than `2 + ε`. That statement quantifies
over infinite families of groups and references `ω`; neither "group of Lie type"
nor `ω` has a Mathlib definition, so it is **not faithfully formalizable here**.

We state instead its finite, per-group kernel — the form of the bound after the
Lie-type lower bound `n(G) ≥ |G|^δ` is substituted, expressed as the *ratio to
the packing target* `|G|^{3/2}`:
\[ \frac{|S|\,|T|\,|U|}{|G|^{3/2}} \le |G|^{-δ/2} + |G|^{-1/2}. \]
Both terms on the right tend to `0` as `|G| → ∞`, so the TPP product is bounded
*strictly below* the packing bound by a polynomial factor — exactly the obstruction
to `ω = 2`. (The further passage to an `ω`-bound in the paper uses convexity of
`x ↦ x^{ω/2}` and the conjugacy-class count `m = |ConjClasses G|`; see
`Xlib.CharDegrees.card_charDegrees`.)

**Proof.** Divide `bcgpu_cor_3_3` through by `|G|^{3/2}`. -/
theorem bcgpu_cor_3_4_kernel {S T U : Finset G} {δ : ℝ} (hδ : 0 < δ)
    (hG : ∃ a b : G, a * b ≠ b * a)
    (hn : (Fintype.card G : ℝ) ^ δ ≤ nG G) (h : TripleProductProperty S T U) :
    (S.card * T.card * U.card : ℝ) / (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2)
      ≤ (Fintype.card G : ℝ) ^ (-δ / 2) + (Fintype.card G : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hNpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hN32 : (0 : ℝ) < (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hNpos _
  rw [div_le_iff₀ hN32]
  calc (S.card * T.card * U.card : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 - δ) / 2) + (Fintype.card G : ℝ) :=
        bcgpu_cor_3_3 hδ hG hn h
    _ = ((Fintype.card G : ℝ) ^ (-δ / 2) + (Fintype.card G : ℝ) ^ (-(1 : ℝ) / 2))
          * (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) := by
        rw [add_mul, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos,
          show -δ / 2 + (3 : ℝ) / 2 = (3 - δ) / 2 by ring,
          show -(1 : ℝ) / 2 + (3 : ℝ) / 2 = 1 by ring, Real.rpow_one]

/-! ### BCGPU Corollary 3.5: the `√2` corollary (any finite group) -/

/-- **BCGPU Corollary 3.5** (the `√2` corollary, arXiv:2204.03826).

For *any* finite group `G` (abelian or not), every TPP triple `(S, T, U)`
satisfies
\[ |S|\,|T|\,|U| \le \frac{|G|^{3/2}}{\sqrt 2} + |G|. \]
This sharpens the elementary `|S||T||U| < |G|^{3/2}` bound: the three sets cannot
all be as large as `⌊|G|^{1/2} - 1⌋` once `|G|` is large.

**Proof.** If `G` is abelian then `|S||T||U| ≤ |G|`
(`Xlib.TPP.card_mul_card_mul_card_le`). Otherwise `n(G) ≥ 2`
(`two_le_minNontrivIrrepDim`), so `bcgpu_thm_3_2` gives
`|G|^{3/2}/n(G)^{1/2} ≤ |G|^{3/2}/√2`. -/
theorem bcgpu_cor_3_5 {S T U : Finset G} (h : TripleProductProperty S T U) :
    (S.card * T.card * U.card : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt 2
        + (Fintype.card G : ℝ) := by
  classical
  by_cases hab : ∃ a b : G, a * b ≠ b * a
  · -- nonabelian: `n(G) ≥ 2` and Theorem 3.2
    have h32 := bcgpu_thm_3_2 hab h
    have hn2 : 2 ≤ minNontrivIrrepDim G := two_le_minNontrivIrrepDim hab
    have hsqrt : Real.sqrt 2 ≤ Real.sqrt (nG G) := by
      apply Real.sqrt_le_sqrt
      unfold nG
      exact_mod_cast hn2
    have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hdiv : (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (nG G)
        ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt 2 :=
      div_le_div_of_nonneg_left (by positivity) hs2 hsqrt
    linarith
  · -- abelian: the abelian barrier `|S||T||U| ≤ |G|`
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      by_contra hne
      exact hab ⟨a, b, hne⟩
    letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
    have habel := card_mul_card_mul_card_le h
    have h1 : (S.card * T.card * U.card : ℝ) ≤ Fintype.card G := by
      exact_mod_cast habel
    have h2 : (0 : ℝ) ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt 2 := by
      positivity
    linarith

/-! ### BCGPU Theorem 3.6: the normalizer barrier for subgroups -/

/-- The **normalizer index** `s(H) = |N(H)| / |H|` of a subgroup `H ≤ G`, as a
real number. Here `N(H) = Subgroup.normalizer H` is the normalizer of `H` in `G`.
Since `H ≤ N(H)`, this ratio is the subgroup index `[N(H) : H] ≥ 1`, equal to `1`
exactly when `H` is self-normalizing. -/
noncomputable def normIndex (H : Subgroup G) : ℝ :=
  (Nat.card (Subgroup.normalizer (H : Set G)) : ℝ) / (Nat.card H : ℝ)

/-! Supporting lemmas for the proof of Theorem 3.6. -/

omit [Fintype G] [DecidableEq G] in
/-- **Cyclic invariance of the TPP.** If `(S, T, U)` has the Triple Product
Property then so does `(T, U, S)`. The cyclic hypothesis
`t'⁻¹t · u'⁻¹u · s'⁻¹s = 1` is conjugated by `s'⁻¹s` into the original
left-quotient form `s'⁻¹s · t'⁻¹t · u'⁻¹u = 1`. -/
private theorem tpp_cyclic {S T U : Finset G} (h : TripleProductProperty S T U) :
    TripleProductProperty T U S := by
  intro t ht t' ht' u hu u' hu' s hs s' hs' heq
  have heq' : s'⁻¹ * s * (t'⁻¹ * t) * (u'⁻¹ * u) = 1 := by
    have hconj : s'⁻¹ * s * (t'⁻¹ * t) * (u'⁻¹ * u)
        = (s'⁻¹ * s) * (t'⁻¹ * t * (u'⁻¹ * u) * (s'⁻¹ * s)) * (s'⁻¹ * s)⁻¹ := by group
    rw [hconj]
    have hz : t'⁻¹ * t * (u'⁻¹ * u) * (s'⁻¹ * s) = 1 := by
      have := heq; group at this ⊢; rw [this]
    rw [hz]; group
  have hstu : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1 := by rw [← heq']; group
  obtain ⟨h1, h2, h3⟩ := h s hs s' hs' t ht t' ht' u hu u' hu' hstu
  exact ⟨h2, h3, h1⟩

/-- **The injectivity bound** (the main observation of BCGPU Thm 3.6). For a
subgroup TPP triple, `|H₁| · |N(H₁) ∩ H₂| · |H₃| ≤ |G|`, because
`(h₁, h₂, h₃) ↦ h₁ h₂ h₃` is injective on `H₁ × (N(H₁) ∩ H₂) × H₃`: a collision
yields `h₁'' · (h₂'⁻¹h₂) · (h₃h₃'⁻¹) = 1` with `h₁'' = h₂'⁻¹(h₁'⁻¹h₁)h₂' ∈ H₁`
(since `h₂' ∈ N(H₁)`), and the TPP forces all three factors trivial. -/
private theorem injBound {H₁ H₂ H₃ : Subgroup G}
    [DecidablePred (· ∈ H₁)] [DecidablePred (· ∈ H₂)] [DecidablePred (· ∈ H₃)]
    (h : SubgroupTripleProductProperty H₁ H₂ H₃) :
    Nat.card H₁ * Nat.card ↥(Subgroup.normalizer (H₁ : Set G) ⊓ H₂)
      * Nat.card H₃ ≤ Fintype.card G := by
  classical
  haveI : Fintype ↥((Subgroup.normalizer (H₁ : Set G) ⊓ H₂ : Subgroup G) : Set G) :=
    Fintype.ofFinite _
  set A₁ : Finset G := (H₁ : Set G).toFinset with hA₁
  set M : Finset G :=
    ((Subgroup.normalizer (H₁ : Set G) ⊓ H₂ : Subgroup G) : Set G).toFinset with hM
  set A₃ : Finset G := (H₃ : Set G).toFinset with hA₃
  rw [show Nat.card H₁ = A₁.card from Nat.card_eq_card_toFinset (H₁ : Set G),
      show Nat.card ↥(Subgroup.normalizer (H₁ : Set G) ⊓ H₂) = M.card from
        Nat.card_eq_card_toFinset _,
      show Nat.card H₃ = A₃.card from Nat.card_eq_card_toFinset (H₃ : Set G)]
  have hinj : Set.InjOn (fun p : G × G × G => p.1 * p.2.1 * p.2.2)
      ((A₁ ×ˢ M ×ˢ A₃ : Finset (G × G × G)) : Set (G × G × G)) := by
    intro p hp q hq heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
    obtain ⟨hp1, hp2, hp3⟩ := hp
    obtain ⟨hq1, hq2, hq3⟩ := hq
    simp only at heq
    rw [hA₁, Set.mem_toFinset, SetLike.mem_coe] at hp1 hq1
    rw [hA₃, Set.mem_toFinset, SetLike.mem_coe] at hp3 hq3
    rw [hM, Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_inf] at hp2 hq2
    obtain ⟨hp2N, hp2H⟩ := hp2
    obtain ⟨hq2N, hq2H⟩ := hq2
    have hconj : q.2.1⁻¹ * (q.1⁻¹ * p.1) * q.2.1 ∈ H₁ := by
      rw [Subgroup.mem_normalizer_iff''] at hq2N
      rw [← hq2N]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hq1) hp1
    have htpp : (1 : G)⁻¹ * (q.2.1⁻¹ * (q.1⁻¹ * p.1) * q.2.1)
        * q.2.1⁻¹ * p.2.1 * (1 : G)⁻¹ * (p.2.2 * q.2.2⁻¹) = 1 := by
      have hrw : (1 : G)⁻¹ * (q.2.1⁻¹ * (q.1⁻¹ * p.1) * q.2.1)
          * q.2.1⁻¹ * p.2.1 * (1 : G)⁻¹ * (p.2.2 * q.2.2⁻¹)
          = q.2.1⁻¹ * q.1⁻¹ * (p.1 * p.2.1 * p.2.2) * q.2.2⁻¹ := by group
      rw [hrw, heq]; group
    have hmem1 : (q.2.1⁻¹ * (q.1⁻¹ * p.1) * q.2.1) ∈ (H₁ : Set G).toFinset := by
      rw [Set.mem_toFinset]; exact hconj
    have hmem1' : (1 : G) ∈ (H₁ : Set G).toFinset := by
      rw [Set.mem_toFinset]; exact H₁.one_mem
    have hmemt : p.2.1 ∈ (H₂ : Set G).toFinset := by
      rw [Set.mem_toFinset]; exact hp2H
    have hmemt' : q.2.1 ∈ (H₂ : Set G).toFinset := by
      rw [Set.mem_toFinset]; exact hq2H
    have hmemu : (p.2.2 * q.2.2⁻¹) ∈ (H₃ : Set G).toFinset := by
      rw [Set.mem_toFinset]; exact Subgroup.mul_mem _ hp3 (Subgroup.inv_mem _ hq3)
    have hmemu' : (1 : G) ∈ (H₃ : Set G).toFinset := by
      rw [Set.mem_toFinset]; exact H₃.one_mem
    obtain ⟨hs, ht, hu⟩ := h _ hmem1 _ hmem1' _ hmemt _ hmemt' _ hmemu _ hmemu' htpp
    have h1eq : p.1 = q.1 := by
      have hx : q.1⁻¹ * p.1 = 1 := by
        have hconjid : q.1⁻¹ * p.1
            = q.2.1 * (q.2.1⁻¹ * (q.1⁻¹ * p.1) * q.2.1) * q.2.1⁻¹ := by group
        rw [hconjid, hs]; group
      rw [inv_mul_eq_one] at hx
      exact hx.symm
    have h3eq : p.2.2 = q.2.2 := by
      rw [mul_inv_eq_one] at hu; exact hu
    exact Prod.ext h1eq (Prod.ext ht h3eq)
  have hcard :
      (A₁ ×ˢ M ×ˢ A₃ : Finset (G × G × G)).card ≤ (Finset.univ : Finset G).card :=
    Finset.card_le_card_of_injOn (fun p => p.1 * p.2.1 * p.2.2)
      (fun _ _ => Finset.mem_univ _) hinj
  rw [Finset.card_product, Finset.card_product, ← mul_assoc] at hcard
  simpa [hA₁, hM, hA₃] using hcard

omit [Fintype G] [DecidableEq G] in
/-- **The master cardinality inequality** `|A| · |K| ≤ |A ∩ K| · |G|` for two
subgroups of a finite group. It is the inequality `|AK| ≤ |G|` repackaged:
`|A| · |K| = |A ∩ K| · |AK|` and `|AK| ≤ |G|`. We prove it via the relative
index, using `[K : A ∩ K] ≤ [G : A]` (cosets of `A ∩ K` in `K` inject into
cosets of `A` in `G`). -/
private theorem cardMul_le {A K : Subgroup G} [Finite G] :
    Nat.card A * Nat.card K ≤ Nat.card ↥(A ⊓ K) * Nat.card G := by
  have hdecomp : A.relIndex K * Nat.card ↥(A ⊓ K) = Nat.card K := by
    have h1 : (A.subgroupOf K).index * Nat.card (A.subgroupOf K) = Nat.card K :=
      Subgroup.index_mul_card (A.subgroupOf K)
    have h2 : Nat.card (A.subgroupOf K) = Nat.card ↥(A ⊓ K) := by
      rw [← Subgroup.subgroupOf_map_subtype A K, Subgroup.card_subtype]
    rw [Subgroup.relIndex, ← h2]; exact h1
  have hrel : A.relIndex K ≤ A.index := by
    have h0 : A.relIndex ⊤ ≠ 0 := by
      rw [Subgroup.relIndex_top_right A]; exact Subgroup.index_ne_zero_of_finite
    calc A.relIndex K ≤ A.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top h0
      _ = A.index := Subgroup.relIndex_top_right A
  have hAidx : Nat.card A * A.index = Nat.card G := Subgroup.card_mul_index A
  calc Nat.card A * Nat.card K
      = Nat.card A * (A.relIndex K * Nat.card ↥(A ⊓ K)) := by rw [hdecomp]
    _ = (Nat.card A * A.relIndex K) * Nat.card ↥(A ⊓ K) := by ring
    _ ≤ (Nat.card A * A.index) * Nat.card ↥(A ⊓ K) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrel)
    _ = Nat.card G * Nat.card ↥(A ⊓ K) := by rw [hAidx]
    _ = Nat.card ↥(A ⊓ K) * Nat.card G := by ring

/-- **The per-pair quadratic bound** `|H₁| · |N(H₁)| · |H₂| · |H₃| ≤ |G|²`,
obtained by feeding the master inequality `|N(H₁)| · |H₂| ≤ |N(H₁) ∩ H₂| · |G|`
into the injectivity bound `|H₁| · |N(H₁) ∩ H₂| · |H₃| ≤ |G|`. -/
private theorem pairBound {H₁ H₂ H₃ : Subgroup G}
    [DecidablePred (· ∈ H₁)] [DecidablePred (· ∈ H₂)] [DecidablePred (· ∈ H₃)]
    (h : SubgroupTripleProductProperty H₁ H₂ H₃) :
    Nat.card H₁ * Nat.card ↥(Subgroup.normalizer (H₁ : Set G)) * Nat.card H₂
        * Nat.card H₃
      ≤ Fintype.card G * Fintype.card G := by
  have hinj := injBound h
  have hmaster :
      Nat.card ↥(Subgroup.normalizer (H₁ : Set G)) * Nat.card H₂
        ≤ Nat.card ↥(Subgroup.normalizer (H₁ : Set G) ⊓ H₂) * Fintype.card G := by
    have := cardMul_le (A := Subgroup.normalizer (H₁ : Set G)) (K := H₂)
    rwa [Nat.card_eq_fintype_card (α := G)] at this
  calc Nat.card H₁ * Nat.card ↥(Subgroup.normalizer (H₁ : Set G)) * Nat.card H₂
          * Nat.card H₃
      = (Nat.card H₁ * Nat.card H₃) *
          (Nat.card ↥(Subgroup.normalizer (H₁ : Set G)) * Nat.card H₂) := by ring
    _ ≤ (Nat.card H₁ * Nat.card H₃) *
          (Nat.card ↥(Subgroup.normalizer (H₁ : Set G) ⊓ H₂) * Fintype.card G) :=
        Nat.mul_le_mul_left _ hmaster
    _ = (Nat.card H₁ * Nat.card ↥(Subgroup.normalizer (H₁ : Set G) ⊓ H₂)
          * Nat.card H₃) * Fintype.card G := by ring
    _ ≤ Fintype.card G * Fintype.card G := Nat.mul_le_mul_right _ hinj

omit [DecidableEq G] in
/-- Each subgroup of a finite group has positive order. -/
private theorem natCard_subgroup_pos (H : Subgroup G) : 0 < Nat.card H :=
  Nat.card_pos

/-- **BCGPU Theorem 3.6** (`thm:normbarrier`, arXiv:2204.03826).

If subgroups `H₁, H₂, H₃` satisfy the Triple Product Property in a finite group
`G`, and `sᵢ = |N(Hᵢ)| / |Hᵢ|` is the normalizer index of each, then
\[ |H_1|\,|H_2|\,|H_3| \le \frac{|G|^{3/2}}{(s_1 s_2 s_3)^{1/4}}. \]
Subgroups far from self-normalizing (large `sᵢ`) shrink the right-hand side, so a
construction aiming for the packing bound should use subgroups as close to
self-normalizing (`sᵢ = 1`) as possible.

**Proof.** The key step is `|H₁| · |N(H₁) ∩ H₂| · |H₃| ≤ |G|` (`injBound`),
proved by showing `(h₁, h₂, h₃) ↦ h₁ h₂ h₃` is injective on
`H₁ × (N(H₁) ∩ H₂) × H₃`: a collision conjugates an `H₁`-element by an
`N(H₁)`-element, contradicting the TPP. The master inequality `cardMul_le`,
`|N(H₁)| · |H₂| ≤ |N(H₁) ∩ H₂| · |G|` (a repackaging of `|N(H₁)H₂| ≤ |G|`),
upgrades this to `|H₁| |N(H₁)| |H₂| |H₃| ≤ |G|²` (`pairBound`); cycling over the
three pairs (using `tpp_cyclic`) and multiplying yields
`(|H₁||H₂||H₃|)⁴ (s₁s₂s₃) ≤ |G|⁶`, and a fourth root gives the bound. -/
theorem bcgpu_thm_3_6 {H₁ H₂ H₃ : Subgroup G}
    [DecidablePred (· ∈ H₁)] [DecidablePred (· ∈ H₂)] [DecidablePred (· ∈ H₃)]
    (h : SubgroupTripleProductProperty H₁ H₂ H₃) :
    (Nat.card H₁ * Nat.card H₂ * Nat.card H₃ : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2)
        / (normIndex H₁ * normIndex H₂ * normIndex H₃) ^ ((1 : ℝ) / 4) := by
  classical
  -- the three cyclic per-pair bounds
  have b1 := pairBound h
  have b2 := pairBound (tpp_cyclic h)
  have b3 := pairBound (tpp_cyclic (tpp_cyclic h))
  -- abbreviations
  set h1 := Nat.card H₁
  set h2 := Nat.card H₂
  set h3 := Nat.card H₃
  set N1 := Nat.card ↥(Subgroup.normalizer (H₁ : Set G))
  set N2 := Nat.card ↥(Subgroup.normalizer (H₂ : Set G))
  set N3 := Nat.card ↥(Subgroup.normalizer (H₃ : Set G))
  set cardG := Fintype.card G
  -- multiply the three quadratic bounds into a degree-six Nat inequality
  have hnat : (h1 * h2 * h3) ^ 3 * (N1 * N2 * N3) ≤ cardG ^ 6 := by
    have hmul : (h1 * N1 * h2 * h3) * (h2 * N2 * h3 * h1) * (h3 * N3 * h1 * h2)
        ≤ (cardG * cardG) * (cardG * cardG) * (cardG * cardG) :=
      Nat.mul_le_mul (Nat.mul_le_mul b1 b2) b3
    calc (h1 * h2 * h3) ^ 3 * (N1 * N2 * N3)
        = (h1 * N1 * h2 * h3) * (h2 * N2 * h3 * h1) * (h3 * N3 * h1 * h2) := by ring
      _ ≤ (cardG * cardG) * (cardG * cardG) * (cardG * cardG) := hmul
      _ = cardG ^ 6 := by ring
  -- positivity of subgroup orders
  have hp1 : 0 < h1 := natCard_subgroup_pos H₁
  have hp2 : 0 < h2 := natCard_subgroup_pos H₂
  have hp3 : 0 < h3 := natCard_subgroup_pos H₃
  -- cast to ℝ and rearrange into P⁴ * (s₁s₂s₃) ≤ Q⁶
  have hP1' : (h1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp1.ne'
  have hP2' : (h2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp2.ne'
  have hP3' : (h3 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp3.ne'
  have hnat' : ((h1 : ℝ) * h2 * h3) ^ 3 * ((N1 : ℝ) * N2 * N3) ≤ (cardG : ℝ) ^ 6 := by
    exact_mod_cast hnat
  have hbound : ((h1 : ℝ) * h2 * h3) ^ 4
      * (normIndex H₁ * normIndex H₂ * normIndex H₃) ≤ (cardG : ℝ) ^ 6 := by
    have hexpand : (normIndex H₁ * normIndex H₂ * normIndex H₃ : ℝ)
        = ((N1 : ℝ) / h1) * ((N2 : ℝ) / h2) * ((N3 : ℝ) / h3) := rfl
    rw [hexpand]
    calc ((h1 : ℝ) * h2 * h3) ^ 4
          * (((N1 : ℝ) / h1) * ((N2 : ℝ) / h2) * ((N3 : ℝ) / h3))
        = ((h1 : ℝ) * h2 * h3) ^ 3 * ((N1 : ℝ) * N2 * N3) := by field_simp
      _ ≤ (cardG : ℝ) ^ 6 := hnat'
  -- extract the fourth root
  set P : ℝ := (h1 : ℝ) * h2 * h3
  set s : ℝ := normIndex H₁ * normIndex H₂ * normIndex H₃ with hsdef
  have hQpos : 0 < (cardG : ℝ) := by
    have : 0 < cardG := Fintype.card_pos
    exact_mod_cast this
  have hspos : 0 < s := by
    have hN1 : 0 < N1 := natCard_subgroup_pos _
    have hN2 : 0 < N2 := natCard_subgroup_pos _
    have hN3 : 0 < N3 := natCard_subgroup_pos _
    rw [hsdef]
    have e1 : (0 : ℝ) < normIndex H₁ := by
      rw [normIndex]; positivity
    have e2 : (0 : ℝ) < normIndex H₂ := by
      rw [normIndex]; positivity
    have e3 : (0 : ℝ) < normIndex H₃ := by
      rw [normIndex]; positivity
    positivity
  -- final root extraction: P⁴ * s ≤ Q⁶ ⟹ P ≤ Q^(3/2) / s^(1/4)
  have hs14 : 0 < s ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hspos _
  have hQ32 : 0 ≤ (cardG : ℝ) ^ ((3 : ℝ) / 2) := le_of_lt (Real.rpow_pos_of_pos hQpos _)
  rw [le_div_iff₀ hs14]
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hQ32
  have e1 : (P * s ^ ((1 : ℝ) / 4)) ^ 4 = P ^ 4 * s := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (s ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (le_of_lt hspos)]
    norm_num
  have e2 : ((cardG : ℝ) ^ ((3 : ℝ) / 2)) ^ 4 = (cardG : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast ((cardG : ℝ) ^ ((3 : ℝ) / 2)) 4,
      ← Real.rpow_mul (le_of_lt hQpos)]
    norm_num
  rw [e1, e2]
  exact hbound

/-! ### BCGPU Corollary 3.8: the center barrier -/

omit [Fintype G] [DecidableEq G] in
/-- **Second isomorphism cardinality** (normal case): `|H ⊔ N| · |H ⊓ N| = |H| · |N|`
when `N` is normal, via `QuotientGroup.quotientInfEquivProdNormalQuotient`. -/
private theorem card_sup_mul_card_inf_normal (H N : Subgroup G) [N.Normal] :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card H * Nat.card N := by
  have hQ : Nat.card (H ⧸ N.subgroupOf H)
      = Nat.card ((H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N)) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H N).toEquiv
  have cH : Nat.card H = Nat.card (H ⧸ N.subgroupOf H) * Nat.card ↥(H ⊓ N) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)]
    congr 1
    rw [← Subgroup.card_subtype H (N.subgroupOf H), Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have cHN : Nat.card ↥(H ⊔ N)
      = Nat.card ((H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N)) * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))]
    congr 1
    rw [← Subgroup.card_subtype (H ⊔ N) (N.subgroupOf (H ⊔ N)),
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right)]
  rw [cHN, cH, ← hQ]; ring

omit [DecidableEq G] in
/-- **Per-subgroup center bound:** `|H| · |Z(G)| ≤ |N(H)| · |H ∩ Z(G)|`. From
`|H ⊔ Z| · |H ∩ Z| = |H| · |Z|` and `H ⊔ Z ≤ N(H)` (both factors normalize `H`). -/
private theorem center_per_subgroup (H : Subgroup G) :
    Nat.card H * Nat.card ↥(Subgroup.center G)
      ≤ Nat.card ↥(Subgroup.normalizer (H : Set G))
        * Nat.card ↥(H ⊓ Subgroup.center G) := by
  set Z := Subgroup.center G
  have hsupinf : Nat.card ↥(H ⊔ Z) * Nat.card ↥(H ⊓ Z) = Nat.card H * Nat.card Z :=
    card_sup_mul_card_inf_normal H Z
  have hle : H ⊔ Z ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
  have hcard : Nat.card ↥(H ⊔ Z) ≤ Nat.card ↥(Subgroup.normalizer (H : Set G)) :=
    Subgroup.card_le_of_le hle
  calc Nat.card H * Nat.card Z
      = Nat.card ↥(H ⊔ Z) * Nat.card ↥(H ⊓ Z) := hsupinf.symm
    _ ≤ Nat.card ↥(Subgroup.normalizer (H : Set G)) * Nat.card ↥(H ⊓ Z) :=
        Nat.mul_le_mul_right _ hcard

open scoped IsMulCommutative in
/-- **The abelian barrier applied to the center.** The intersections
`Hᵢ ∩ Z(G)` form a TPP triple inside the commutative group `Z(G)` (the property
descends along the injective subgroup inclusion `Z(G) ↪ G`), so by the abelian
barrier `Xlib.TPP.card_mul_card_mul_card_le`,
`∏ᵢ |Hᵢ ∩ Z(G)| ≤ |Z(G)|`. -/
private theorem abelianBarrier_center {H₁ H₂ H₃ : Subgroup G}
    [DecidablePred (· ∈ H₁)] [DecidablePred (· ∈ H₂)] [DecidablePred (· ∈ H₃)]
    (h : SubgroupTripleProductProperty H₁ H₂ H₃) :
    Nat.card ↥(H₁ ⊓ Subgroup.center G) * Nat.card ↥(H₂ ⊓ Subgroup.center G)
        * Nat.card ↥(H₃ ⊓ Subgroup.center G)
      ≤ Nat.card ↥(Subgroup.center G) := by
  classical
  set Z := Subgroup.center G
  set S₁ : Finset ↥Z := ((H₁ ⊓ Z).subgroupOf Z : Set ↥Z).toFinset with hS₁
  set S₂ : Finset ↥Z := ((H₂ ⊓ Z).subgroupOf Z : Set ↥Z).toFinset with hS₂
  set S₃ : Finset ↥Z := ((H₃ ⊓ Z).subgroupOf Z : Set ↥Z).toFinset with hS₃
  have hZtpp : TripleProductProperty S₁ S₂ S₃ := by
    intro s hs s' hs' t ht t' ht' u hu u' hu' heq
    rw [hS₁, Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf] at hs hs'
    rw [hS₂, Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf] at ht ht'
    rw [hS₃, Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf] at hu hu'
    have heqG : (s' : G)⁻¹ * (s : G) * (t' : G)⁻¹ * (t : G) * (u' : G)⁻¹ * (u : G) = 1 := by
      have := congrArg (Z.subtype) heq
      push_cast at this
      simpa using this
    have hmems : (s : G) ∈ (H₁ : Set G).toFinset := by rw [Set.mem_toFinset]; exact hs.1
    have hmems' : (s' : G) ∈ (H₁ : Set G).toFinset := by rw [Set.mem_toFinset]; exact hs'.1
    have hmemt : (t : G) ∈ (H₂ : Set G).toFinset := by rw [Set.mem_toFinset]; exact ht.1
    have hmemt' : (t' : G) ∈ (H₂ : Set G).toFinset := by rw [Set.mem_toFinset]; exact ht'.1
    have hmemu : (u : G) ∈ (H₃ : Set G).toFinset := by rw [Set.mem_toFinset]; exact hu.1
    have hmemu' : (u' : G) ∈ (H₃ : Set G).toFinset := by rw [Set.mem_toFinset]; exact hu'.1
    obtain ⟨e1, e2, e3⟩ :=
      h _ hmems _ hmems' _ hmemt _ hmemt' _ hmemu _ hmemu' heqG
    exact ⟨Subtype.ext e1, Subtype.ext e2, Subtype.ext e3⟩
  have hbar := card_mul_card_mul_card_le hZtpp
  have key : ∀ K : Subgroup G, Nat.card ↥((K ⊓ Z).subgroupOf Z) = Nat.card ↥(K ⊓ Z) := by
    intro K
    rw [← Subgroup.card_subtype Z ((K ⊓ Z).subgroupOf Z),
      Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have c1 : S₁.card = Nat.card ↥(H₁ ⊓ Z) :=
    (calc S₁.card = Nat.card ↥((H₁ ⊓ Z).subgroupOf Z) := by
            rw [hS₁]; exact (Nat.card_eq_card_toFinset _).symm
      _ = Nat.card ↥(H₁ ⊓ Z) := key H₁)
  have c2 : S₂.card = Nat.card ↥(H₂ ⊓ Z) :=
    (calc S₂.card = Nat.card ↥((H₂ ⊓ Z).subgroupOf Z) := by
            rw [hS₂]; exact (Nat.card_eq_card_toFinset _).symm
      _ = Nat.card ↥(H₂ ⊓ Z) := key H₂)
  have c3 : S₃.card = Nat.card ↥(H₃ ⊓ Z) :=
    (calc S₃.card = Nat.card ↥((H₃ ⊓ Z).subgroupOf Z) := by
            rw [hS₃]; exact (Nat.card_eq_card_toFinset _).symm
      _ = Nat.card ↥(H₃ ⊓ Z) := key H₃)
  rw [c1, c2, c3, ← Nat.card_eq_fintype_card (α := ↥Z)] at hbar
  exact hbar

/-- **BCGPU Corollary 3.8** (`cor:centerbarrier`, arXiv:2204.03826).

If subgroups `H₁, H₂, H₃` satisfy the Triple Product Property in a finite group
`G`, then
\[ |H_1|\,|H_2|\,|H_3| \le \frac{|G|^{3/2}}{|Z(G)|^{1/2}}, \]
where `Z(G) = Subgroup.center G` is the center. Groups with a large center
(`|Z(G)| = Ω(|G|^δ)`, e.g. `GL(n, q)` for fixed `n` as `q → ∞`) cannot meet the
packing bound with subgroup triples.

**Proof.** The triple `Hᵢ ∩ Z(G)` satisfies the TPP in the abelian group `Z(G)`,
so `|Z(G)| ≥ ∏ᵢ |Hᵢ ∩ Z(G)|` (`abelianBarrier_center`). The per-subgroup bound
`|Hᵢ| |Z(G)| ≤ |N(Hᵢ)| |Hᵢ ∩ Z(G)|` (`center_per_subgroup`, using `Z(G) ⊆ N(Hᵢ)`)
multiplied over the three subgroups and combined with the abelian barrier yields
`(∏ᵢ |Hᵢ|) |Z(G)|² ≤ ∏ᵢ |N(Hᵢ)|`, i.e. `s₁ s₂ s₃ ≥ |Z(G)|²`. Hence
`(s₁ s₂ s₃)^{1/4} ≥ |Z(G)|^{1/2} = √|Z(G)|`, and substituting into `bcgpu_thm_3_6`
gives the bound. -/
theorem bcgpu_cor_3_8 {H₁ H₂ H₃ : Subgroup G}
    [DecidablePred (· ∈ H₁)] [DecidablePred (· ∈ H₂)] [DecidablePred (· ∈ H₃)]
    (h : SubgroupTripleProductProperty H₁ H₂ H₃) :
    (Nat.card H₁ * Nat.card H₂ * Nat.card H₃ : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2)
        / Real.sqrt (Nat.card (Subgroup.center G)) := by
  set Z := Subgroup.center G
  -- abbreviations (Nat)
  set P1 := Nat.card H₁; set P2 := Nat.card H₂; set P3 := Nat.card H₃
  set N1 := Nat.card ↥(Subgroup.normalizer (H₁ : Set G))
  set N2 := Nat.card ↥(Subgroup.normalizer (H₂ : Set G))
  set N3 := Nat.card ↥(Subgroup.normalizer (H₃ : Set G))
  set I1 := Nat.card ↥(H₁ ⊓ Z); set I2 := Nat.card ↥(H₂ ⊓ Z); set I3 := Nat.card ↥(H₃ ⊓ Z)
  set z := Nat.card ↥Z
  have hz : 0 < z := Nat.card_pos
  -- per-subgroup bounds and abelian barrier
  have per1 : P1 * z ≤ N1 * I1 := center_per_subgroup H₁
  have per2 : P2 * z ≤ N2 * I2 := center_per_subgroup H₂
  have per3 : P3 * z ≤ N3 * I3 := center_per_subgroup H₃
  have hab : I1 * I2 * I3 ≤ z := abelianBarrier_center h
  -- Nat combination: (P1 P2 P3) z² ≤ N1 N2 N3
  have hnat : (P1 * P2 * P3) * (z * z) ≤ N1 * N2 * N3 := by
    have hprod : (P1 * z) * (P2 * z) * (P3 * z) ≤ (N1 * I1) * (N2 * I2) * (N3 * I3) :=
      Nat.mul_le_mul (Nat.mul_le_mul per1 per2) per3
    have hstep : (P1 * P2 * P3) * (z * z * z) ≤ (N1 * N2 * N3) * z := by
      calc (P1 * P2 * P3) * (z * z * z)
          = (P1 * z) * (P2 * z) * (P3 * z) := by ring
        _ ≤ (N1 * I1) * (N2 * I2) * (N3 * I3) := hprod
        _ = (N1 * N2 * N3) * (I1 * I2 * I3) := by ring
        _ ≤ (N1 * N2 * N3) * z := Nat.mul_le_mul_left _ hab
    have hz3 : (P1 * P2 * P3) * (z * z) * z ≤ (N1 * N2 * N3) * z := by
      calc (P1 * P2 * P3) * (z * z) * z = (P1 * P2 * P3) * (z * z * z) := by ring
        _ ≤ (N1 * N2 * N3) * z := hstep
    exact Nat.le_of_mul_le_mul_right hz3 hz
  -- cast to ℝ: s₁s₂s₃ ≥ z²
  have hP1 : 0 < P1 := Nat.card_pos
  have hP2 : 0 < P2 := Nat.card_pos
  have hP3 : 0 < P3 := Nat.card_pos
  have hP1' : (P1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP1.ne'
  have hP2' : (P2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP2.ne'
  have hP3' : (P3 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP3.ne'
  have hsge : ((z : ℝ)) ^ 2 ≤ normIndex H₁ * normIndex H₂ * normIndex H₃ := by
    have hnat' : ((P1 : ℝ) * P2 * P3) * ((z : ℝ) * z) ≤ (N1 : ℝ) * N2 * N3 := by
      exact_mod_cast hnat
    have hexpand : (normIndex H₁ * normIndex H₂ * normIndex H₃ : ℝ)
        = ((N1 : ℝ) / P1) * ((N2 : ℝ) / P2) * ((N3 : ℝ) / P3) := rfl
    rw [hexpand, div_mul_div_comm, div_mul_div_comm, le_div_iff₀ (by positivity)]
    calc ((z : ℝ)) ^ 2 * ((P1 : ℝ) * P2 * P3)
        = ((P1 : ℝ) * P2 * P3) * ((z : ℝ) * z) := by ring
      _ ≤ (N1 : ℝ) * N2 * N3 := hnat'
  -- apply Theorem 3.6 and the division/exponent step
  have hthm := bcgpu_thm_3_6 h
  have hQ32 : 0 ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) :=
    le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos) _)
  have hsqrtz : 0 < Real.sqrt z := Real.sqrt_pos.mpr (by exact_mod_cast hz)
  have hsqrt_le :
      Real.sqrt z ≤ (normIndex H₁ * normIndex H₂ * normIndex H₃) ^ ((1 : ℝ) / 4) := by
    have hz2 : Real.sqrt z = ((z : ℝ) ^ 2) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (z : ℝ) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hz2]
    exact Real.rpow_le_rpow (by positivity) hsge (by norm_num)
  calc (Nat.card H₁ * Nat.card H₂ * Nat.card H₃ : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2)
          / (normIndex H₁ * normIndex H₂ * normIndex H₃) ^ ((1 : ℝ) / 4) := hthm
    _ ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt z :=
        div_le_div_of_nonneg_left hQ32 hsqrtz hsqrt_le

end Xlib.BCGPUBarrier
