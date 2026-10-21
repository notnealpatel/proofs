/-
# Irreducible complex character degrees divide the group order (Frobenius)

## Classical source (recorded 2026-10-21)

* G. Frobenius, *Über die Primfactoren der Gruppendeterminante*,
  Sitzungsber. Preuss. Akad. Wiss. Berlin (1896).
* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press (1976),
  Theorem 3.11 (degree divides `|G|`); Theorem 6.15 (Itô's refinement).

## Informal statement (verbatim from the target specification)

```
For a finite group G, every irreducible complex representation degree χ(1)
divides |G| (Frobenius); refinement (Itô): χ(1) divides [G:A] for every
abelian normal subgroup A.
```

## Scope of this module

This module formalizes and proves the **Frobenius part**: every element of the
repository's canonical character-degree multiset
`GroupTPP.CharDegrees.charDegrees G` divides `Fintype.card G`
(`charDegree_dvd_card`).  Itô's refinement (`χ(1) ∣ [G : A]` for abelian normal
`A`) is **not** formalized here; it remains a separate target.

## Mathlib absence check (2026-10-21)

`leandoc` searches "character degree divides order group", "dimension
irreducible representation divides card", "finrank simple module divides card
group", "central character algebraic integer", "class sum integral group
algebra" returned no divisibility theorem; `Mathlib/RepresentationTheory` has
no `dvd` or `IsIntegral` statement about character degrees.

## Proof route (character-free matrix form of the classical argument)

Fix a surjective `ℂ`-algebra map `ρ : ℂ[G] →ₐ Mat_d(ℂ)` (one Wedderburn block)
and write `R g = ρ (of g)`.

1. *Averaging.* For every matrix `A`, `Σ_g R(g⁻¹) A R(g)` commutes with every
   `R h`, hence (surjectivity) with every matrix, hence is scalar; comparing
   traces it equals `(|G| · tr A / d) · 1`.
2. *Schur relation.* Summing (1) over `A = E_{ac}` gives
   `Σ_g tr R(g⁻¹) • R(g) = (|G| / d) · 1`.
3. *Integrality.* Each `tr R(g)` is a sum of roots of unity, hence lies in the
   integral closure `O` of `ℤ` in `ℂ`.  The left side of (2) lies in the
   `O`-algebra spanned by the finitely many `R g`, so `|G| / d` is integral
   over `O`, hence over `ℤ`.
4. *Rationality.* `|G| / d` is rational and `ℤ` is integrally closed, so it is
   an integer.
-/
import Mathlib
import GroupTPP.CharDegrees

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.CharacterDegreeDividesOrder

/-! ## The matrix representation attached to a block map -/

/-- The matrix of the group element `g` under a `ℂ`-algebra map
`ρ : ℂ[G] →ₐ[ℂ] Mat_d(ℂ)`, i.e. `ρ` applied to the basis element `g ∈ ℂ[G]`. -/
noncomputable def repMat {G : Type*} [Group G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) (g : G) :
    Matrix (Fin d) (Fin d) ℂ :=
  ρ (MonoidAlgebra.of ℂ G g)

/-- `repMat` is multiplicative: `R (g h) = R g * R h`. -/
theorem repMat_mul {G : Type*} [Group G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) (g h : G) :
    repMat ρ (g * h) = repMat ρ g * repMat ρ h := by
  simp only [repMat, map_mul]

/-- `repMat` sends the identity to the identity matrix. -/
theorem repMat_one {G : Type*} [Group G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    repMat ρ 1 = 1 := by
  simp only [repMat, map_one]

/-- `R g * R g⁻¹ = 1`. -/
theorem repMat_mul_inv {G : Type*} [Group G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) (g : G) :
    repMat ρ g * repMat ρ g⁻¹ = 1 := by
  rw [← repMat_mul, mul_inv_cancel, repMat_one]

/-- Ground truth: for the trivial one-dimensional representation (the lift of the
constant monoid map `G → Mat₁(ℂ)`), every group element acts as the identity. -/
example {G : Type*} [Group G] (g : G) :
    repMat (MonoidAlgebra.lift ℂ (Matrix (Fin 1) (Fin 1) ℂ) G 1) g = 1 := by
  simp [repMat]

/-- Ground truth / satisfiability: the trivial one-dimensional representation
`ℂ[G] → Mat₁(ℂ)` is surjective, so the hypotheses of `dvd_card_of_surjective`
are jointly satisfiable (with `d = 1`). -/
example {G : Type*} [Group G] :
    Function.Surjective (MonoidAlgebra.lift ℂ (Matrix (Fin 1) (Fin 1) ℂ) G 1) := by
  intro M
  refine ⟨MonoidAlgebra.single 1 (M 0 0), ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  simp [MonoidAlgebra.lift_single]

/-! ## Step 1: averaging over the group gives a scalar -/

/-- The group average `Σ_g R(g⁻¹) A R(g)` commutes with every `R h`. -/
theorem average_commute {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (h : G) :
    repMat ρ h * (∑ g, repMat ρ g⁻¹ * A * repMat ρ g) =
      (∑ g, repMat ρ g⁻¹ * A * repMat ρ g) * repMat ρ h := by
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [← Equiv.sum_comp (Equiv.mulRight h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.coe_mulRight, mul_inv_rev, repMat_mul, ← mul_assoc, repMat_mul_inv, one_mul]

/-- If `ρ` is surjective, a matrix commuting with every `R h` commutes with
every matrix. -/
theorem commute_of_surjective {G : Type*} [Group G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : Function.Surjective ρ) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ h : G, repMat ρ h * X = X * repMat ρ h) (M : Matrix (Fin d) (Fin d) ℂ) :
    M * X = X * M := by
  obtain ⟨x, rfl⟩ := hρ M
  induction x using MonoidAlgebra.induction_on with
  | of g => exact hX g
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | smul r x hx => rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]

/-- If `ρ` is surjective, the group average `Σ_g R(g⁻¹) A R(g)` is a scalar matrix. -/
theorem average_eq_scalar {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : Function.Surjective ρ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∃ c : ℂ, (∑ g, repMat ρ g⁻¹ * A * repMat ρ g) = Matrix.scalar (Fin d) c := by
  have hmem : (∑ g, repMat ρ g⁻¹ * A * repMat ρ g) ∈
      Set.center (Matrix (Fin d) (Fin d) ℂ) := by
    rw [Semigroup.mem_center_iff]
    exact commute_of_surjective ρ hρ _ (average_commute ρ A)
  rw [Matrix.center_eq_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

/-- The trace of the group average is `|G| · tr A`. -/
theorem trace_average {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ g, repMat ρ g⁻¹ * A * repMat ρ g).trace = Fintype.card G * A.trace := by
  rw [Matrix.trace_sum]
  have h : ∀ g : G, (repMat ρ g⁻¹ * A * repMat ρ g).trace = A.trace := by
    intro g
    rw [Matrix.trace_mul_cycle, repMat_mul_inv, one_mul]
  simp [h]

/-- **Averaging identity.** For surjective `ρ` onto `d × d` matrices with
`0 < d`, `Σ_g R(g⁻¹) A R(g) = (|G| · tr A / d) · 1`. -/
theorem average_eq {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : Function.Surjective ρ) (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ g, repMat ρ g⁻¹ * A * repMat ρ g) =
      Matrix.scalar (Fin d) ((Fintype.card G : ℂ) * A.trace / d) := by
  obtain ⟨c, hc⟩ := average_eq_scalar ρ hρ A
  have htr := trace_average ρ A
  rw [hc, Matrix.scalar_apply, Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at htr
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hc, ← htr, mul_div_cancel_left₀ _ hd']

/-! ## Step 2: the Schur relation -/

/-- **Schur relation.** For surjective `ρ` onto `d × d` matrices with `0 < d`,
`Σ_g tr R(g⁻¹) • R(g) = (|G| / d) · 1`. -/
theorem sum_trace_smul {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : Function.Surjective ρ) (hd : 0 < d) :
    ∑ g, (repMat ρ g⁻¹).trace • repMat ρ g =
      Matrix.scalar (Fin d) ((Fintype.card G : ℂ) / d) := by
  ext c y
  have key : ∀ a : Fin d, ∑ g, (repMat ρ g⁻¹) a a * (repMat ρ g) c y =
      (Matrix.scalar (Fin d)
        ((Fintype.card G : ℂ) * (Matrix.single a c (1 : ℂ)).trace / d)) a y := by
    intro a
    rw [← average_eq ρ hρ hd, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [key]
  by_cases h : c = y
  · subst h
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.trace, Matrix.single_apply,
      Finset.filter_eq]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.trace, Matrix.single_apply, h]

/-! ## Step 3: integrality -/

/-- `R g ^ |G| = 1`. -/
theorem repMat_pow_card {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) (g : G) :
    repMat ρ g ^ Fintype.card G = 1 := by
  simp only [repMat, ← map_pow, pow_card_eq_one, map_one]

/-- Character values are algebraic integers: `tr R(g)` is integral over `ℤ`
(it is a sum of eigenvalues, each a `|G|`-th root of unity). -/
theorem isIntegral_trace_repMat {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (g : G) :
    IsIntegral ℤ (repMat ρ g).trace := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun r hr => ?_
  have hroot : (repMat ρ g).charpoly.IsRoot r := (Polynomial.mem_roots'.mp hr).2
  have hspec : r ∈ spectrum ℂ (repMat ρ g) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  have hpow : r ^ Fintype.card G ∈ spectrum ℂ (repMat ρ g ^ Fintype.card G) := by
    have hsub := spectrum.subset_polynomial_aeval (repMat ρ g) (Polynomial.X ^ Fintype.card G)
      ⟨r, hspec, rfl⟩
    simpa using hsub
  rw [repMat_pow_card, spectrum.one_eq, Set.mem_singleton_iff] at hpow
  refine IsIntegral.of_pow (Fintype.card_pos (α := G)) ?_
  rw [hpow]
  exact isIntegral_one

/-- **Integrality of `|G| / d`.** For a surjective `ℂ`-algebra map
`ρ : ℂ[G] →ₐ Mat_d(ℂ)` with `0 < d`, the complex number `|G| / d` is an
algebraic integer. -/
theorem isIntegral_card_div {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : Function.Surjective ρ) (hd : 0 < d) :
    IsIntegral ℤ ((Fintype.card G : ℂ) / d) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let O : Subalgebra ℤ ℂ := integralClosure ℤ ℂ
  let S : Subalgebra O (Matrix (Fin d) (Fin d) ℂ) := Algebra.adjoin O (Set.range (repMat ρ))
  have hclosure : (Submonoid.closure (Set.range (repMat ρ)) :
      Set (Matrix (Fin d) (Fin d) ℂ)) = Set.range (repMat ρ) := by
    have hrange : Set.range (repMat ρ) =
        Set.range ((ρ : MonoidAlgebra ℂ G →* Matrix (Fin d) (Fin d) ℂ).comp
          (MonoidAlgebra.of ℂ G)) := rfl
    rw [hrange, MonoidHom.mclosure_range]
    rfl
  have hS : (Subalgebra.toSubmodule S).FG := by
    rw [Algebra.adjoin_eq_span, hclosure]
    exact Submodule.fg_span (Set.finite_range _)
  let χ : G → O := fun g => ⟨(repMat ρ g⁻¹).trace, isIntegral_trace_repMat ρ hd g⁻¹⟩
  have hmem : (∑ g, χ g • repMat ρ g) ∈ S :=
    Subalgebra.sum_mem _ fun g _ =>
      Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self g)) _
  have hsum : (∑ g, χ g • repMat ρ g) =
      algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) ((Fintype.card G : ℂ) / d) := by
    refine (show _ = ∑ g, (repMat ρ g⁻¹).trace • repMat ρ g from rfl).trans ?_
    rw [sum_trace_smul ρ hρ hd]
    rfl
  have hint : IsIntegral O
      (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) ((Fintype.card G : ℂ) / d)) :=
    hsum ▸ IsIntegral.of_mem_of_fg S hS _ hmem
  have hinj : Function.Injective
      ((Algebra.ofId ℂ (Matrix (Fin d) (Fin d) ℂ)).restrictScalars O) :=
    (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)).injective
  have hintO : IsIntegral O ((Fintype.card G : ℂ) / d) :=
    (isIntegral_algHom_iff _ hinj).mp hint
  exact isIntegral_trans _ hintO

/-! ## Step 4: rationality -/

/-- If `n / d` (computed in `ℂ`) is an algebraic integer and `0 < d`, then
`d ∣ n`. -/
theorem dvd_of_isIntegral_div {n d : ℕ} (hd : 0 < d)
    (h : IsIntegral ℤ ((n : ℂ) / d)) : d ∣ n := by
  let q : ℚ := (n : ℚ) / d
  have hq : ((n : ℂ) / d) = algebraMap ℚ ℂ q := by simp [q]
  have hinj : Function.Injective ((Algebra.ofId ℚ ℂ).restrictScalars ℤ) :=
    (algebraMap ℚ ℂ).injective
  have hqint : IsIntegral ℤ q := (isIntegral_algHom_iff _ hinj).mp (hq ▸ h)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnq : (n : ℚ) = y * d := by
    rw [eq_div_iff hd'] at hy
    simpa using hy.symm
  have hnz : (n : ℤ) = y * d := by exact_mod_cast hnq
  exact Int.natCast_dvd_natCast.mp ⟨y, by rw [hnz, mul_comm]⟩

/-! ## Main theorems -/

/-- **Degree divides order, block form.** If `ρ : ℂ[G] →ₐ[ℂ] Mat_d(ℂ)` is a
surjective `ℂ`-algebra map (equivalently, an irreducible complex representation
of `G` of degree `d`) with `0 < d`, then `d ∣ |G|`. -/
theorem dvd_card_of_surjective {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : Function.Surjective ρ) (hd : 0 < d) : d ∣ Fintype.card G :=
  dvd_of_isIntegral_div hd (isIntegral_card_div ρ hρ hd)

/-- **Frobenius (1896); Isaacs, Theorem 3.11.** For a finite group `G`, every
irreducible complex character degree `χ(1)` — i.e. every element `d` of the
character-degree multiset `GroupTPP.CharDegrees.charDegrees G` — divides `|G|`. -/
theorem charDegree_dvd_card {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (hd : d ∈ GroupTPP.CharDegrees.charDegrees G) : d ∣ Fintype.card G := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨n, dims, hdims, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hdims
  rw [GroupTPP.CharDegrees.charDegrees_eq_of_algEquiv G e] at hd
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hd
  let ρ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin (dims i)) (Fin (dims i)) ℂ :=
    (Pi.evalAlgHom ℂ (fun j => Matrix (Fin (dims j)) (Fin (dims j)) ℂ) i).comp e.toAlgHom
  have hρ : Function.Surjective ρ :=
    (Function.surjective_eval i).comp e.surjective
  exact dvd_card_of_surjective ρ hρ (Nat.pos_of_ne_zero (NeZero.ne (dims i)))

/-- Non-vacuity: the character-degree multiset of any finite group is nonempty
(its cardinality is the number of conjugacy classes), so the hypothesis of
`charDegree_dvd_card` is satisfiable for every `G`. -/
example {G : Type*} [Group G] [Fintype G] :
    ∃ d, d ∈ GroupTPP.CharDegrees.charDegrees G := by
  have hcard := GroupTPP.CharDegrees.card_charDegrees G
  have hpos : 0 < Multiset.card (GroupTPP.CharDegrees.charDegrees G) := by
    rw [hcard]
    exact Nat.card_pos
  exact Multiset.card_pos_iff_exists_mem.mp hpos

end GroupTPP.CharacterDegreeDividesOrder
