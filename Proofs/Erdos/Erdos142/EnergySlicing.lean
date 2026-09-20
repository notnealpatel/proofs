/-
  Erdős Problem #142 — finite half-open energy slicing and pigeonhole.

  The finite torus transfer of the EHPS construction slices a finite point
  set `P` by the value of a nonnegative energy function `E : P → ℝ` and keeps
  the half-open bin that carries the largest number of points.  The energy of
  every point is bounded above by a constant `M`, so the number of nonempty
  bins is `⌊M / Δ⌋ + 1` for a slice width `Δ > 0`.  Pigeonhole then gives a
  bin whose cardinality pays for the total count `|P|`.

  This module isolates that argument as a reusable finite statement and then
  specializes it to the exact arithmetic used by the handoff: with the audited
  single-block energy constant `2921/144` and the slice width
  `Δ = R² / (2 q²)`, the bin count `⌊M / Δ⌋ + 1` satisfies

    `(⌊M / Δ⌋ + 1) * R² ≤ 41 * k * e² * q² + R²`,

  where `M = (2921 / 144) * k * e²`.  The coefficient `41` is the handoff
  target; the audited arithmetic gives the stronger `(2921 / 72) * k * e² * q²
  + R²` since `2921 / 72 = 40.569… < 41`.

  The consumer produces one half-open bin `energyBin E Δ j` and the bound

    `|P| * R² ≤ (41 * k * e² * q² + R²) * |energyBin E Δ j|`.

  No claim of mathematical novelty is made; the module only records the finite
  slicing algebra and its certified arithmetic specialisation.
-/

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos142

variable {P : Type*} [Fintype P]

/-- The half-open energy bin of index `j`: the points whose energy lies in the
interval `[j * Δ, j * Δ + Δ)`. -/
noncomputable def energyBin (E : P → ℝ) (Δ : ℝ) (j : ℕ) : Finset P := by
  classical
  exact Finset.univ.filter fun X => (j : ℝ) * Δ ≤ E X ∧ E X < (j : ℝ) * Δ + Δ

/-- Membership in an energy bin is exactly membership in the half-open interval
`[j * Δ, j * Δ + Δ)`. -/
@[simp]
theorem mem_energyBin {E : P → ℝ} {Δ : ℝ} {j : ℕ} {X : P} :
    X ∈ energyBin E Δ j ↔ (j : ℝ) * Δ ≤ E X ∧ E X < (j : ℝ) * Δ + Δ := by
  classical
  simp [energyBin]

/-- Ground truth: on the three-point type `Fin 3` with energy `E i = i` and
unit width, the bin of index `0` is the singleton `{0}`. -/
example : energyBin (fun i : Fin 3 => (i : ℝ)) 1 0 = {0} := by
  ext i
  fin_cases i <;> simp [mem_energyBin]

/-- Ground truth: on `Fin 3` with energy `E i = i` and unit width, the bin of
index `1` is the singleton `{1}`. -/
example : energyBin (fun i : Fin 3 => (i : ℝ)) 1 1 = {1} := by
  ext i
  fin_cases i
  · simp [mem_energyBin]
  · simp [mem_energyBin]
  · simp [mem_energyBin]
    norm_num

/-- Ground truth: with the audited energy bound, the bin-count coefficient
`2921 / 72` is at most the handoff coefficient `41`. -/
example : (2921 / 72 : ℝ) ≤ 41 := by norm_num

/-- **Floor characterisation of the energy bin.** For positive width `Δ` and
nonnegative energy, the half-open bin of index `j` is exactly the set of points
whose energy-to-width ratio has natural floor `j`.  This is the bridge that
turns the half-open slicing statement into a pigeonhole over `Fin J`. -/
theorem energyBin_eq_filter_floor {E : P → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hE_nonneg : ∀ X, 0 ≤ E X) (j : ℕ) :
    energyBin E Δ j = Finset.univ.filter (fun X => Nat.floor (E X / Δ) = j) := by
  classical
  ext X
  simp only [mem_energyBin, Finset.mem_filter, Finset.mem_univ, true_and]
  have hx : 0 ≤ E X / Δ := div_nonneg (hE_nonneg X) hΔ.le
  rw [Nat.floor_eq_iff hx, le_div_iff₀ hΔ, div_lt_iff₀ hΔ]
  have hstep : ((j : ℝ) + 1) * Δ = (j : ℝ) * Δ + Δ := by ring
  rw [hstep]

/-- **Finite half-open energy slicing (pigeonhole).** Let `P` be finite,
`E : P → ℝ` nonnegative and bounded above by `M`, and `Δ > 0`.  Then some
half-open bin `energyBin E Δ j` with `j < ⌊M / Δ⌋ + 1` satisfies

  `|P| ≤ (⌊M / Δ⌋ + 1) * |energyBin E Δ j|`.

In the intended regime `M` is a nonnegative energy bound; the identity of the
bin count `⌊M / Δ⌋ + 1` matches the handoff's `J = floor(M/Δ) + 1`. -/
theorem exists_energyBin_card_le {E : P → ℝ} {M Δ : ℝ} (hΔ : 0 < Δ)
    (hE_nonneg : ∀ X, 0 ≤ E X) (hE_le : ∀ X, E X ≤ M) :
    ∃ j : ℕ, j < Nat.floor (M / Δ) + 1 ∧
      (Fintype.card P : ℝ) ≤
        ((Nat.floor (M / Δ) + 1 : ℕ) : ℝ) * ((energyBin E Δ j).card : ℝ) := by
  classical
  set J : ℕ := Nat.floor (M / Δ) + 1 with hJ
  have hJpos : 0 < J := Nat.succ_pos _
  haveI : Nonempty (Fin J) := ⟨⟨0, hJpos⟩⟩
  let f : P → Fin J := fun X =>
    ⟨Nat.floor (E X / Δ), by
      have hle : E X / Δ ≤ M / Δ := div_le_div_of_nonneg_right (hE_le X) hΔ.le
      exact Nat.lt_succ_of_le (Nat.floor_mono hle)⟩
  have hb : Fintype.card (Fin J) • ((Fintype.card P : ℝ) / (J : ℝ)) ≤
      (Fintype.card P : ℝ) := by
    have hJne : (J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hJpos.ne'
    have hval : (J : ℝ) * ((Fintype.card P : ℝ) / (J : ℝ)) = (Fintype.card P : ℝ) := by
      rw [mul_comm, div_mul_cancel₀ _ hJne]
    rw [Fintype.card_fin, nsmul_eq_mul, hval]
  obtain ⟨j, hj⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card (M := ℝ) f hb
  refine ⟨j, j.isLt, ?_⟩
  have hfiber : (Finset.univ.filter (fun X => f X = j)) = energyBin E Δ j := by
    rw [energyBin_eq_filter_floor hΔ hE_nonneg j]
    apply Finset.filter_congr
    intro X _
    simp only [f]
    exact Fin.ext_iff
  rw [hfiber] at hj
  have hJne : (J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hJpos.ne'
  have hmul := mul_le_mul_of_nonneg_right hj (le_of_lt (Nat.cast_pos.mpr hJpos) :
    (0 : ℝ) ≤ (J : ℝ))
  rw [div_mul_cancel₀ _ hJne] at hmul
  exact hmul.trans_eq (mul_comm _ _)

/-- **Bin-count arithmetic at the audited constant.** With `M = (2921/144) k e²`
and `Δ = R² / (2 q²)`, the bin count `⌊M / Δ⌋ + 1` satisfies

  `(⌊M / Δ⌋ + 1) * R² ≤ (2921 / 72) * k * e² * q² + R²`.

The stronger coefficient `2921 / 72` is recorded here; the handoff's `41`
follows by monotonicity. -/
theorem binCount_mul_sq_le_2921 {k : ℕ} {e q R : ℝ} (hq : 0 < q) (hR : 0 < R) :
    ((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) / (R ^ 2 / (2 * q ^ 2)))
          + 1 : ℕ) : ℝ) * R ^ 2 ≤
      (2921 / 72 : ℝ) * (k : ℝ) * e ^ 2 * q ^ 2 + R ^ 2 := by
  have hMnonneg : 0 ≤ (2921 / 144 : ℝ) * (k : ℝ) * e ^ 2 := by positivity
  have hΔpos : 0 < R ^ 2 / (2 * q ^ 2) := by positivity
  have hR2ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hdiv : ((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) / (R ^ 2 / (2 * q ^ 2)) =
      (2921 / 72 : ℝ) * (k : ℝ) * e ^ 2 * q ^ 2 / R ^ 2 := by
    field_simp
    ring
  have hfloor : ((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
      (R ^ 2 / (2 * q ^ 2))) : ℕ) : ℝ) ≤
      (2921 / 72 : ℝ) * (k : ℝ) * e ^ 2 * q ^ 2 / R ^ 2 := by
    calc ((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
          (R ^ 2 / (2 * q ^ 2))) : ℕ) : ℝ)
        ≤ ((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) / (R ^ 2 / (2 * q ^ 2)) :=
          Nat.floor_le (by positivity)
      _ = (2921 / 72 : ℝ) * (k : ℝ) * e ^ 2 * q ^ 2 / R ^ 2 := hdiv
  have hkey : ((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
      (R ^ 2 / (2 * q ^ 2))) : ℕ) : ℝ) * R ^ 2 ≤
      (2921 / 72 : ℝ) * (k : ℝ) * e ^ 2 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hfloor (by positivity : (0 : ℝ) ≤ R ^ 2)
    rwa [div_mul_cancel₀ _ hR2ne] at h
  have hcast : (((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
          (R ^ 2 / (2 * q ^ 2))) + 1 : ℕ) : ℝ)) =
      ((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
          (R ^ 2 / (2 * q ^ 2))) : ℕ) : ℝ) + 1 := by
    push_cast
    rfl
  rw [hcast]
  nlinarith [hkey]

/-- **Bin-count arithmetic at the handoff coefficient `41`.** With
`M = (2921/144) k e²` and `Δ = R² / (2 q²)`,

  `(⌊M / Δ⌋ + 1) * R² ≤ 41 * k * e² * q² + R²`. -/
theorem binCount_mul_sq_le_41 {k : ℕ} {e q R : ℝ} (hq : 0 < q) (hR : 0 < R) :
    ((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) / (R ^ 2 / (2 * q ^ 2)))
          + 1 : ℕ) : ℝ) * R ^ 2 ≤
      41 * (k : ℝ) * e ^ 2 * q ^ 2 + R ^ 2 := by
  have h := binCount_mul_sq_le_2921 (k := k) (e := e) hq hR
  have hcoef : (2921 / 72 : ℝ) ≤ 41 := by norm_num
  have hnn : 0 ≤ (k : ℝ) * e ^ 2 * q ^ 2 := by positivity
  nlinarith [h, hcoef, hnn]

/-- Ground truth at the handoff parameters: the bin-count inequality holds at
`k = 3`, `e = 6`, `q = 11`, `R = 7`. -/
example : ((Nat.floor (((2921 / 144 : ℝ) * 3 * (6 : ℝ) ^ 2) /
        ((7 : ℝ) ^ 2 / (2 * (11 : ℝ) ^ 2))) + 1 : ℕ) : ℝ) * (7 : ℝ) ^ 2 ≤
      41 * 3 * (6 : ℝ) ^ 2 * (11 : ℝ) ^ 2 + (7 : ℝ) ^ 2 :=
  binCount_mul_sq_le_41 (k := 3) (e := 6) (q := 11) (R := 7)
    (by norm_num) (by norm_num)

/-- **Handoff consumer: one half-open energy bin pays for `|P| * R²`.** Let
`P` be finite and `E : P → ℝ` nonnegative with `E X ≤ (2921 / 144) k e²`.
For positive `q` and `R`, set the slice width `Δ = R² / (2 q²)`.  Then there
is a bin index `j < ⌊M / Δ⌋ + 1` whose bin satisfies

  `|P| * R² ≤ (41 * k * e² * q² + R²) * |energyBin E Δ j|`. -/
theorem exists_energyBin_card_mul_le_41 {E : P → ℝ} {k : ℕ} {e q R : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hE_nonneg : ∀ X, 0 ≤ E X)
    (hE_le : ∀ X, E X ≤ (2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) :
    ∃ j : ℕ,
      j < Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) / (R ^ 2 / (2 * q ^ 2)))
          + 1 ∧
        (Fintype.card P : ℝ) * R ^ 2 ≤
          (41 * (k : ℝ) * e ^ 2 * q ^ 2 + R ^ 2) *
            ((energyBin E (R ^ 2 / (2 * q ^ 2)) j).card : ℝ) := by
  have hΔ : 0 < R ^ 2 / (2 * q ^ 2) := by positivity
  obtain ⟨j, hjlt, hjcard⟩ :=
    exists_energyBin_card_le (E := E) (M := (2921 / 144 : ℝ) * (k : ℝ) * e ^ 2)
      hΔ hE_nonneg hE_le
  refine ⟨j, hjlt, ?_⟩
  have hJle := binCount_mul_sq_le_41 (k := k) (e := e) (q := q) (R := R) hq hR
  have hcardR := mul_le_mul_of_nonneg_right hjcard (by positivity : (0 : ℝ) ≤ R ^ 2)
  have hstep : (((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
        (R ^ 2 / (2 * q ^ 2))) + 1 : ℕ) : ℝ) *
        ((energyBin E (R ^ 2 / (2 * q ^ 2)) j).card : ℝ)) * R ^ 2 =
      (((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
        (R ^ 2 / (2 * q ^ 2))) + 1 : ℕ) : ℝ) * R ^ 2) *
        ((energyBin E (R ^ 2 / (2 * q ^ 2)) j).card : ℝ) := by ring
  calc (Fintype.card P : ℝ) * R ^ 2
      ≤ (((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
            (R ^ 2 / (2 * q ^ 2))) + 1 : ℕ) : ℝ) *
            ((energyBin E (R ^ 2 / (2 * q ^ 2)) j).card : ℝ)) * R ^ 2 := hcardR
    _ = ((((Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
            (R ^ 2 / (2 * q ^ 2))) + 1 : ℕ) : ℝ) * R ^ 2) *
            ((energyBin E (R ^ 2 / (2 * q ^ 2)) j).card : ℝ)) := hstep
    _ ≤ (41 * (k : ℝ) * e ^ 2 * q ^ 2 + R ^ 2) *
          ((energyBin E (R ^ 2 / (2 * q ^ 2)) j).card : ℝ) :=
        mul_le_mul_of_nonneg_right hJle (Nat.cast_nonneg _)

/-- **Half-open bin form of the handoff consumer.** The bin of the previous
theorem is exposed as a `Finset` `S` that is exactly `energyBin E Δ j` for some
index `j`. -/
theorem exists_energyBin_41 {E : P → ℝ} {k : ℕ} {e q R : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hE_nonneg : ∀ X, 0 ≤ E X)
    (hE_le : ∀ X, E X ≤ (2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) :
    ∃ S : Finset P, (∃ j, S = energyBin E (R ^ 2 / (2 * q ^ 2)) j) ∧
      (Fintype.card P : ℝ) * R ^ 2 ≤
        (41 * (k : ℝ) * e ^ 2 * q ^ 2 + R ^ 2) * (S.card : ℝ) := by
  obtain ⟨j, _, hj⟩ := exists_energyBin_card_mul_le_41 (E := E) hq hR hE_nonneg hE_le
  exact ⟨energyBin E (R ^ 2 / (2 * q ^ 2)) j, ⟨j, rfl⟩, hj⟩

/-- Joint satisfiability of the handoff consumer: on `Fin 4` with the zero
energy, every hypothesis holds and a sliced bin attains the conclusion. -/
example : ∃ S : Finset (Fin 4),
    (∃ j, S = energyBin (fun _ : Fin 4 => (0 : ℝ)) ((7 : ℝ) ^ 2 / (2 * (11 : ℝ) ^ 2)) j) ∧
      (Fintype.card (Fin 4) : ℝ) * (7 : ℝ) ^ 2 ≤
        (41 * 3 * (6 : ℝ) ^ 2 * (11 : ℝ) ^ 2 + (7 : ℝ) ^ 2) * (S.card : ℝ) :=
  exists_energyBin_41 (E := fun _ : Fin 4 => (0 : ℝ)) (k := 3) (e := 6) (q := 11) (R := 7)
    (by norm_num) (by norm_num) (fun _ => le_refl 0) (fun _ => by norm_num)

#check @energyBin
#check @mem_energyBin
#check @energyBin_eq_filter_floor
#check @exists_energyBin_card_le
#check @binCount_mul_sq_le_2921
#check @binCount_mul_sq_le_41
#check @exists_energyBin_card_mul_le_41
#check @exists_energyBin_41

#print axioms energyBin_eq_filter_floor
#print axioms exists_energyBin_card_le
#print axioms binCount_mul_sq_le_2921
#print axioms binCount_mul_sq_le_41
#print axioms exists_energyBin_card_mul_le_41
#print axioms exists_energyBin_41

end Erdos142