import Xlib.CharDegreesMul
import Xlib.CUCapacity

/-!
# Character degrees of abelian groups: the collapse to all-ones

This file proves that every irreducible complex representation of a finite
abelian group is one-dimensional, and derives the collapse of the
character-degree multiset and power sum:

  `charDegrees H = Multiset.replicate (Fintype.card H) 1`
  `charDegreeSumReal H x = Fintype.card H`

## Main results

* `matrix_comm_imp_dim_le_one` — if `Matrix (Fin d) (Fin d) ℂ` is a
  commutative ring (via a `Mul.mul` commutativity hypothesis), then `d ≤ 1`.
  Proof: for `d ≥ 2`, two single-entry matrices `Matrix.single 0 1 1` and
  `Matrix.single 1 0 1` fail to commute.
* `charDegrees_of_commGroup` — for a finite abelian group `H`, every character
  degree is `1` and there are `|H|` of them.
* `charDegreeSumReal_of_commGroup` — the real-exponent power sum collapses:
  `D_x(H) = |H|` for every `x`.

## Design for downstream consumers

The statement `charDegrees_of_commGroup` takes `[CommGroup H]` so that Ab2
can instantiate it at a subgroup `A : Subgroup G` with `IsMulCommutative A`:
open the `IsMulCommutative` scope to get the scoped `CommGroup` instance from
`[Group A] [IsMulCommutative A]`.

## References

Standard representation theory of abelian groups; ring-side proof via
Wedderburn–Artin (no character theory, no Schur's lemma).
-/

open scoped BigOperators
open Xlib.CharDegrees Xlib.CharDegreesMul

namespace Xlib.CharDegreesComm

/-! ### Commutative matrix rings have dimension at most 1 -/

/-- If `Matrix (Fin d) (Fin d) ℂ` is a commutative ring, then `d ≤ 1`.

Proof: for `d ≥ 2`, the single-entry matrices `E₀₁ = Matrix.single 0 1 1` and
`E₁₀ = Matrix.single 1 0 1` satisfy `(E₀₁ * E₁₀) 0 0 = 1` but
`(E₁₀ * E₀₁) 0 0 = 0`, contradicting commutativity. -/
theorem matrix_comm_imp_dim_le_one {d : ℕ}
    (hcomm : ∀ A B : Matrix (Fin d) (Fin d) ℂ, A * B = B * A) :
    d ≤ 1 := by
  by_contra h
  push_neg at h
  -- d ≥ 2, so 0 ≠ 1 in Fin d
  have h0 : (0 : Fin d) ≠ 1 := Fin.zero_ne_one_of_le (by omega)
  -- E₀₁ = Matrix.single 0 1 1, E₁₀ = Matrix.single 1 0 1
  let E₀₁ : Matrix (Fin d) (Fin d) ℂ := Matrix.single 0 1 1
  let E₁₀ : Matrix (Fin d) (Fin d) ℂ := Matrix.single 1 0 1
  have hab : (E₀₁ * E₁₀) 0 0 = 1 := by
    simp [E₀₁, E₁₀, Matrix.mul_apply, Matrix.single, Matrix.of_apply]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hba : (E₁₀ * E₀₁) 0 0 = 0 := by
    simp [E₁₀, E₀₁, Matrix.mul_apply, Matrix.single, Matrix.of_apply]
    apply Finset.sum_eq_zero
    intro b _
    simp only [ite_mul, one_mul, zero_mul]
    split_ifs with h1 h2
    · obtain ⟨_, h1b⟩ := h1; obtain ⟨h2a, _⟩ := h2
      exact absurd (h1b ▸ h2a) h0.symm
    · simp
    · simp
    · simp
  have := hcomm E₀₁ E₁₀
  have : (E₀₁ * E₁₀) 0 0 = (E₁₀ * E₀₁) 0 0 := congrFun (congrFun this 0) 0
  rw [hab, hba] at this
  exact one_ne_zero this

/-! ### Character degrees of abelian groups -/

/-- **Character degrees of an abelian group are all ones.** For a finite
abelian group `H`, `charDegrees H = Multiset.replicate (Fintype.card H) 1`.

Ring-side proof (no character theory): `ℂ[H]` is a `CommSemiring`
(`MonoidAlgebra.commSemiring`, needing `[CommMonoid H]` from `[CommGroup H]`).
Extract a Wedderburn decomposition; transport commutativity through the
`AlgEquiv` to each matrix block; apply `matrix_comm_imp_dim_le_one` to force
`d i ≤ 1`; the `NeZero (d i)` witnesses from the decomposition give `d i = 1`.
The count `n = Fintype.card H` follows from `charDegreeSum_two`. -/
theorem charDegrees_of_commGroup (H : Type*) [CommGroup H] [Fintype H] :
    charDegrees H = Multiset.replicate (Fintype.card H) 1 := by
  haveI : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨n, d, hne, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ H)
  haveI := hne
  -- ℂ[H] is a CommSemiring because H is a CommGroup
  haveI : CommSemiring (MonoidAlgebra ℂ H) := MonoidAlgebra.commSemiring
  -- Each matrix block is commutative (transported from ℂ[H] through the AlgEquiv)
  have block_comm : ∀ i, ∀ A B : Matrix (Fin (d i)) (Fin (d i)) ℂ, A * B = B * A := by
    intro i A B
    -- The evaluation AlgHom projects to block i
    let ev := Pi.evalAlgHom ℂ (fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ) i
    -- e is surjective, so ev ∘ e is surjective
    have hsurj : Function.Surjective (fun x => ev (e x)) :=
      ev.toRingHom.surjective_comp e.surjective
    obtain ⟨a, ha⟩ := hsurj A
    obtain ⟨b, hb⟩ := hsurj B
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  -- Each block size d i ≤ 1
  have hle : ∀ i, d i ≤ 1 := fun i => matrix_comm_imp_dim_le_one (block_comm i)
  -- Combined with NeZero (d i), we get d i = 1
  have heq : ∀ i, d i = 1 := fun i => by
    have := (NeZero.ne (d i))
    omega
  -- The multiset is all ones
  have hmultiset : charDegrees H = Finset.univ.val.map d := charDegrees_eq_of_algEquiv H e
  rw [hmultiset]
  -- Finset.univ.val.map d = Multiset.replicate n 1
  have hmap : Finset.univ.val.map d = Multiset.replicate n 1 := by
    conv_lhs => rw [show d = fun _ => 1 from funext heq]
    rw [Multiset.map_const', Finset.card_fin]
  rw [hmap]
  -- n = Fintype.card H from charDegreeSum_two
  congr 1
  have h2 := charDegreeSum_two H
  unfold charDegreeSum at h2
  rw [hmultiset, hmap, Multiset.map_replicate, Multiset.sum_replicate] at h2
  simp at h2
  exact h2

/-- **The real-exponent power sum of an abelian group.** For a finite abelian
group `H`, `charDegreeSumReal H x = Fintype.card H` for every `x : ℝ`.

Proof: from `charDegrees_of_commGroup`, every entry is `1`, so each term is
`(1 : ℝ) ^ x = 1` (`Real.one_rpow`), and the sum of `|H|` ones is `|H|`. -/
theorem charDegreeSumReal_of_commGroup (H : Type*) [CommGroup H] [Fintype H]
    (x : ℝ) : charDegreeSumReal H x = Fintype.card H := by
  rw [charDegreeSumReal_eq_map_sum]
  rw [charDegrees_of_commGroup]
  rw [Multiset.map_replicate, Multiset.sum_replicate]
  simp [Real.one_rpow]

end Xlib.CharDegreesComm
