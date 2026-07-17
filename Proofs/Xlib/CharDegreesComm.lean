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
  Proof: for `d ≥ 2`, two single-entry matrices fail to commute.
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
Wedderburn-Artin (no character theory, no Schur's lemma).
-/

open scoped BigOperators
open Xlib.CharDegrees Xlib.CharDegreesMul Xlib.CUCapacity

namespace Xlib.CharDegreesComm

/-! ### Commutative matrix rings have dimension at most 1 -/

/-- If `Matrix (Fin d) (Fin d) ℂ` is a commutative ring, then `d ≤ 1`.

Proof: for `d ≥ 2`, the single-entry matrices `E₀₁ = Matrix.single i0 i1 1`
and `E₁₀ = Matrix.single i1 i0 1` (where `i0 = ⟨0, _⟩`, `i1 = ⟨1, _⟩`)
satisfy `(E₀₁ * E₁₀) i0 i0 = 1` but `(E₁₀ * E₀₁) i0 i0 = 0`, contradicting
commutativity. -/
theorem matrix_comm_imp_dim_le_one {d : ℕ}
    (hcomm : ∀ A B : Matrix (Fin d) (Fin d) ℂ, A * B = B * A) :
    d ≤ 1 := by
  by_contra h
  rw [not_le] at h
  -- d ≥ 2, so we have distinct elements i0, i1 : Fin d
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, h⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h10 : i1 ≠ i0 := h01.symm
  -- E₀₁ = Matrix.single i0 i1 1, E₁₀ = Matrix.single i1 i0 1
  let E₀₁ : Matrix (Fin d) (Fin d) ℂ := Matrix.single i0 i1 1
  let E₁₀ : Matrix (Fin d) (Fin d) ℂ := Matrix.single i1 i0 1
  -- (E₀₁ * E₁₀) i0 i0 = 1
  -- The sum ∑_b (single i0 i1 1)(i0, b) * (single i1 i0 1)(b, i0) has unique
  -- nonzero term at b = i1: conditions i0 = i0 ∧ i1 = b (needs b = i1)
  -- and i1 = b ∧ i0 = i0 (needs b = i1).
  have hab : (E₀₁ * E₁₀) i0 i0 = 1 := by
    simp only [Matrix.mul_apply, E₀₁, E₁₀, Matrix.single, Matrix.of_apply]
    rw [Finset.sum_eq_single i1]
    · simp [i1]
    · intro b _ hb
      simp only [ite_mul, one_mul, zero_mul]
      split_ifs <;> simp_all
    · intro habs; exact absurd (Finset.mem_univ i1) habs
  -- (E₁₀ * E₀₁) i0 i0 = 0
  -- The sum ∑_b (single i1 i0 1)(i0, b) * (single i0 i1 1)(b, i0) is zero
  -- because the first factor (single i1 i0 1)(i0, b) requires i1 = i0 ∧ i0 = b,
  -- and i1 = i0 fails.
  have hba : (E₁₀ * E₀₁) i0 i0 = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b _
    simp only [E₁₀, Matrix.single, Matrix.of_apply]
    simp only [ite_mul, one_mul, zero_mul]
    split_ifs with h1
    · exact absurd h1.1 h10
    · rfl
  have hc := hcomm E₀₁ E₁₀
  have hc' : (E₀₁ * E₁₀) i0 i0 = (E₁₀ * E₀₁) i0 i0 := congrFun (congrFun hc i0) i0
  rw [hab, hba] at hc'
  exact one_ne_zero hc'

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
    -- Lift A and B to ℂ[H] via e.symm and Pi.single
    obtain ⟨a, ha⟩ : ∃ a, (e a) i = A := ⟨e.symm (Pi.single i A), by simp⟩
    obtain ⟨b, hb⟩ : ∃ b, (e b) i = B := ⟨e.symm (Pi.single i B), by simp⟩
    -- e preserves multiplication, and the source is commutative
    calc A * B = (e a) i * (e b) i := by rw [ha, hb]
      _ = (e a * e b) i := (Pi.mul_apply (e a) (e b) i).symm
      _ = (e (a * b)) i := by rw [map_mul]
      _ = (e (b * a)) i := by rw [mul_comm a b]
      _ = (e b * e a) i := by rw [map_mul]
      _ = (e b) i * (e a) i := Pi.mul_apply (e b) (e a) i
      _ = B * A := by rw [ha, hb]
  -- Each block size d i ≤ 1
  have hle : ∀ i, d i ≤ 1 := fun i => matrix_comm_imp_dim_le_one (block_comm i)
  -- Combined with NeZero (d i), we get d i = 1
  have heq : ∀ i, d i = 1 := fun i =>
    le_antisymm (hle i) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (d i)))
  -- The multiset is all ones
  have hmultiset : charDegrees H = Finset.univ.val.map d := charDegrees_eq_of_algEquiv H e
  -- Finset.univ.val.map d = Multiset.replicate n 1 (since all d i = 1)
  have hmap : Finset.univ.val.map d = Multiset.replicate n 1 := by
    conv_lhs => rw [show d = fun _ => 1 from funext heq]
    simp [Multiset.map_const']
  -- n = Fintype.card H from charDegreeSum_two
  have hn : n = Fintype.card H := by
    have h2 := charDegreeSum_two H
    unfold charDegreeSum at h2
    rw [hmultiset, hmap, Multiset.map_replicate, Multiset.sum_replicate] at h2
    simp at h2
    exact h2
  rw [hmultiset, hmap, hn]

/-- **The real-exponent power sum of an abelian group.** For a finite abelian
group `H`, `charDegreeSumReal H x = Fintype.card H` for every `x : ℝ`.

Proof: from `charDegrees_of_commGroup`, every entry is `1`, so each term is
`(1 : ℝ) ^ x = 1` (`Real.one_rpow`), and the sum of `|H|` ones is `|H|`. -/
theorem charDegreeSumReal_of_commGroup (H : Type*) [CommGroup H] [Fintype H]
    (x : ℝ) : charDegreeSumReal H x = Fintype.card H := by
  rw [charDegreeSumReal_eq_map_sum, charDegrees_of_commGroup]
  simp [Multiset.map_replicate, Multiset.sum_replicate, Real.one_rpow]

end Xlib.CharDegreesComm
