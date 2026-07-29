import GroupTPP.DihedralTPP.Basic

/-!
# Sharpness of the dihedral TPP bound

The classical triple `(⟨r³, f⟩, ⟨fr⟩, ⟨fr²⟩)` in `D₁₂` (here `n = 6`),
written in the `DihedralGroup` normal form, witnesses equality
`3 * (|S| * |T| * |U|) = 8 * n` in `DihedralTPP.card_mul_le_of_isTPP`.
This also confirms the `IsTPP` predicate is satisfiable by nontrivial
triples (the definition is not vacuous).

All three sets consist of involutions, hence are inversion-stable, so the
same triple also witnesses sharpness for the canonical left-quotient
`GroupTPP.TPP.TripleProductProperty`.  Combining the witness with the capacity
bound `DihedralTPP.three_mul_tppCapacity_le` pins down the exact TPP
capacity `β(D₁₂) = GroupTPP.TPP.tppCapacity (DihedralGroup 6) = 16`: the first
exact nonabelian `tppCapacity` value in this development, and since
`|D₁₂| = 12 < 16` it exhibits `ρ(D₁₂) = 4/3 > 1`, beating the abelian
barrier `GroupTPP.TPP.tppCapacity_eq_card`.
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

/-- The witness triple also satisfies the canonical left-quotient TPP:
`S6, T6, U6` are involution-sets, hence inversion-stable, and the two TPP
conventions agree on inversion-stable triples. -/
private lemma tripleProductProperty_S6_T6_U6 :
    GroupTPP.TPP.TripleProductProperty S6 T6 U6 := by
  decide

/-- The bound `3 |S| |T| |U| ≤ 8 n` of `card_mul_le_of_tripleProductProperty`
is attained in `D₁₂`: the re-homed theorem is sharp on the canonical
left-quotient TPP as well. -/
theorem exists_tripleProductProperty_bound_eq :
    ∃ S T U : Finset (DihedralGroup 6),
      GroupTPP.TPP.TripleProductProperty S T U ∧
        3 * (S.card * T.card * U.card) = 8 * 6 :=
  ⟨S6, T6, U6, tripleProductProperty_S6_T6_U6, by decide⟩

/-- **Exact nonabelian TPP capacity:** `β(D₁₂) = 16`.  Lower bound: the
sharp triple `(S6, T6, U6)` with `|S6| · |T6| · |U6| = 16`.  Upper bound:
the capacity form of the 4/3 theorem at `n = 6`, `3 · β ≤ 48`.  Since
`|D₁₂| = 12 < 16 = β(D₁₂)`, the subset-TPP ratio is `ρ(D₁₂) = 4/3 > 1`,
strictly beating the abelian barrier `GroupTPP.TPP.tppCapacity_eq_card`. -/
theorem tppCapacity_dihedralGroup_six :
    GroupTPP.TPP.tppCapacity (DihedralGroup 6) = 16 := by
  have hlow : 16 ≤ GroupTPP.TPP.tppCapacity (DihedralGroup 6) := by
    have h := GroupTPP.TPP.le_tppCapacity tripleProductProperty_S6_T6_U6
    have hc : S6.card * T6.card * U6.card = 16 := by decide
    rwa [hc] at h
  have hhigh : 3 * GroupTPP.TPP.tppCapacity (DihedralGroup 6) ≤ 8 * 6 :=
    three_mul_tppCapacity_le
  omega

end DihedralTPP
