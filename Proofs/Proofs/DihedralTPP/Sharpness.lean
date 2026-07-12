import Proofs.DihedralTPP.Basic

/-!
# Sharpness of the dihedral TPP bound

The classical triple `(⟨r³, f⟩, ⟨fr⟩, ⟨fr²⟩)` in `D₁₂` (here `n = 6`),
written in the `DihedralGroup` normal form, witnesses equality
`3 * (|S| * |T| * |U|) = 8 * n` in `DihedralTPP.card_mul_le_of_isTPP`.
This also confirms the `IsTPP` predicate is satisfiable by nontrivial
triples (the definition is not vacuous).
-/

namespace DihedralTPP

open DihedralGroup

/-- `S = ⟨r³, f⟩ = {1, r³, f, fr³}`, in `sr`-coordinates `{r 0, r 3, sr 0, sr 3}`. -/
private def S6 : Finset (DihedralGroup 6) := {r 0, r 3, sr 0, sr 3}

/-- `T = ⟨fr⟩ = {1, fr}`, in `sr`-coordinates `{r 0, sr 1}` (up to labeling). -/
private def T6 : Finset (DihedralGroup 6) := {r 0, sr 1}

/-- `U = ⟨fr²⟩ = {1, fr²}`, in `sr`-coordinates `{r 0, sr 2}`. -/
private def U6 : Finset (DihedralGroup 6) := {r 0, sr 2}

private lemma isTPP_S6_T6_U6 : IsTPP S6 T6 U6 := by
  unfold IsTPP
  decide

/-- The bound `3 |S| |T| |U| ≤ 8 n` is attained in `D₁₂`: the theorem is sharp. -/
theorem exists_isTPP_bound_eq :
    ∃ S T U : Finset (DihedralGroup 6),
      IsTPP S T U ∧ 3 * (S.card * T.card * U.card) = 8 * 6 :=
  ⟨S6, T6, U6, isTPP_S6_T6_U6, by decide⟩

end DihedralTPP
