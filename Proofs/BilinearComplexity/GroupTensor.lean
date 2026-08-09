/-
  BilinearComplexity/GroupTensor — the group-algebra multiplication tensor
  and the Cohn–Umans / Murthy 4.13 bridge.

  This file connects the two finished pillars of the Om campaign:
  Pl7 tensor rank (`BilinearComplexity/`) and Pl9 TPP
  (`DihedralTPP/Basic.lean`). It formalizes Murthy thesis
  (arXiv:0709.1223) Theorem 4.13, the group-algebra embedding of matrix
  multiplication via the triple product property.

    · `mulTensor k G` — the structure tensor of the group algebra `k[G]` in
      the trilinear "trace form" convention that mirrors `matMulTensor`
      (structure tensor of `trace (X * Y * Z)`): the entry at `(x, y, z)` is
      `1` iff `eG x * eG y * eG z = 1`, where `eG = (Fintype.equivFin G).symm`
      is a fixed enumeration `Fin (card G) ≃ G`. (Both `Finset.equivFin` and
      `Fintype.equivFin` are noncomputable, so `mulTensor` is noncomputable.)

    · `rank_matMulTensor_le_of_isTPP` — Murthy 4.13(2): if `(S, T, U)` is a
      TPP triple in `G` (right-quotient convention `Q(X) = X * X⁻¹`, matching
      `DihedralTPP.IsTPP`), then `R⟨|S|,|T|,|U|⟩ ≤ R(mulTensor k G)`. This is
      the honest form: the campaign-brief paraphrase "≤ |G|" is Murthy's
      Corollary 4.14(3) (the abelian special case over ℂ) and is WRONG in
      general.

    · `rank_mulTensor_le` — the trivial sanity anchor
      `R(mulTensor k G) ≤ |G| * |G|` via `rank_le_mul`.

  Proof shape (a pure sub-tensor statement — no group algebra object is
  built). Enumerate `S, T, U` by `finsetEnum` (injective, lands in the
  finset). Build three index maps `quotIndex` on the row-major-packed modes:
  a packed `x = (i, j)` maps to `eG⁻¹(sᵢ⁻¹ tⱼ)` (resp. `tⱼ'⁻¹ uₗ`,
  `uₗ'⁻¹ sᵢ'`). Pulling `mulTensor` back along these three maps reproduces
  `matMulTensor` exactly:

    (sᵢ⁻¹ tⱼ)(tⱼ'⁻¹ uₗ)(uₗ'⁻¹ sᵢ') = 1  ⟺  j = j' ∧ l = l' ∧ i' = i.

  The `⇐` direction is telescoping (`group`); the `⇒` direction is exactly
  TPP: conjugating by `sᵢ'` turns the left side into a product of
  right-quotient elements `(sᵢ' sᵢ⁻¹)(tⱼ tⱼ'⁻¹)(uₗ uₗ'⁻¹) = 1`, whose three
  factors lie in `S*S⁻¹`, `T*T⁻¹`, `U*U⁻¹`; the enumerations are injective,
  so TPP forces the three index equalities. The rank bound then follows from
  Om3's injectivity-free sub-tensor lemma `rank_comp_le`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import BilinearComplexity.MatMulMono
import GroupTPP.DihedralTPP.Basic

namespace BilinearComplexity

open scoped Pointwise

/-! ## 1. Finset enumeration -/

section Enum

variable {G : Type*}

/-- A fixed enumeration `Fin S.card → G` of a finset `S`: the underlying
element of `S.equivFin.symm i`. It is injective and lands in `S`. -/
noncomputable def finsetEnum (S : Finset G) (i : Fin S.card) : G :=
  (S.equivFin.symm i : G)

/-- The enumeration lands inside the finset. -/
lemma finsetEnum_mem (S : Finset G) (i : Fin S.card) : finsetEnum S i ∈ S :=
  Finset.coe_mem (S.equivFin.symm i)

/-- The enumeration is injective (`Subtype.val ∘ S.equivFin.symm`). -/
lemma finsetEnum_injective (S : Finset G) : Function.Injective (finsetEnum S) := by
  intro a b hab
  exact S.equivFin.symm.injective (Subtype.ext hab)

end Enum

/-! ## 2. The group-algebra multiplication tensor -/

/-- The structure tensor of the group algebra `k[G]` in trilinear "trace
form" convention (mirroring `matMulTensor` = structure tensor of
`trace (X * Y * Z)`): the entry at `(x, y, z)` is `1` iff
`eG x * eG y * eG z = 1`, where `eG = (Fintype.equivFin G).symm` is a fixed
enumeration `Fin (card G) ≃ G`. Noncomputable because `Fintype.equivFin` is. -/
noncomputable def mulTensor (k : Type*) [CommSemiring k] (G : Type*) [Group G]
    [Fintype G] [DecidableEq G] :
    Tensor k (Fintype.card G) (Fintype.card G) (Fintype.card G) := fun x y z =>
  if (Fintype.equivFin G).symm x * (Fintype.equivFin G).symm y
      * (Fintype.equivFin G).symm z = 1 then 1 else 0

/-- Entry formula for `mulTensor`, as a `rfl`-lemma for rewriting. -/
theorem mulTensor_apply (k : Type*) [CommSemiring k] (G : Type*) [Group G]
    [Fintype G] [DecidableEq G] (x y z : Fin (Fintype.card G)) :
    mulTensor k G x y z =
      if (Fintype.equivFin G).symm x * (Fintype.equivFin G).symm y
          * (Fintype.equivFin G).symm z = 1 then 1 else 0 :=
  rfl

/-! ## 3. The Murthy 4.13 index maps and bridge -/

section Bridge

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The Cohn–Umans monomial index map on the mode `Fin (A.card * B.card)`:
unpack the packed index `x` to `(i, j)` via `finProdFinEquiv.symm`, form the
"right quotient in the algebra" `(finsetEnum A i)⁻¹ * finsetEnum B j`, and
re-index into `Fin (card G)` via `Fintype.equivFin G`. -/
noncomputable def quotIndex (A B : Finset G) (x : Fin (A.card * B.card)) :
    Fin (Fintype.card G) :=
  Fintype.equivFin G
    ((finsetEnum A (finProdFinEquiv.symm x).1)⁻¹ * finsetEnum B (finProdFinEquiv.symm x).2)

omit [DecidableEq G] in
/-- The enumeration equiv cancels the re-indexing in `quotIndex`. -/
lemma symm_equivFin_quotIndex (A B : Finset G) (x : Fin (A.card * B.card)) :
    (Fintype.equivFin G).symm (quotIndex A B x)
      = (finsetEnum A (finProdFinEquiv.symm x).1)⁻¹ * finsetEnum B (finProdFinEquiv.symm x).2 := by
  simp only [quotIndex, Equiv.symm_apply_apply]

/-- **Murthy Thm 4.13 / Cohn–Umans embedding (honest form, part (2)).**
If `(S, T, U)` is a TPP triple in `G` (right-quotient convention, matching
`DihedralTPP.IsTPP`), then the matrix multiplication tensor `⟨|S|,|T|,|U|⟩`
restricts the group-algebra tensor `mulTensor k G`, so
`R⟨|S|,|T|,|U|⟩ ≤ R(mulTensor k G)`. NOT `≤ |G|` (that is Corollary 4.14(3),
the abelian case over ℂ). -/
theorem rank_matMulTensor_le_of_isTPP {k : Type*} [CommSemiring k]
    {S T U : Finset G} (h : DihedralTPP.IsTPP S T U) :
    rank (matMulTensor k S.card T.card U.card) ≤ rank (mulTensor k G) := by
  have hEq : (fun x y z => mulTensor k G (quotIndex S T x) (quotIndex T U y) (quotIndex U S z))
      = matMulTensor k S.card T.card U.card := by
    funext x y z
    rw [mulTensor_apply, matMulTensor_apply]
    simp only [symm_equivFin_quotIndex]
    set i := (finProdFinEquiv.symm x).1
    set j := (finProdFinEquiv.symm x).2
    set j' := (finProdFinEquiv.symm y).1
    set l := (finProdFinEquiv.symm y).2
    set l' := (finProdFinEquiv.symm z).1
    set i' := (finProdFinEquiv.symm z).2
    refine if_congr ?_ rfl rfl
    constructor
    · -- ⇒ direction: exactly TPP after cyclic conjugation.
      intro hone
      have hq₁ : finsetEnum S i' * (finsetEnum S i)⁻¹ ∈ S * S⁻¹ :=
        Finset.mul_mem_mul (finsetEnum_mem S i') (Finset.inv_mem_inv (finsetEnum_mem S i))
      have hq₂ : finsetEnum T j * (finsetEnum T j')⁻¹ ∈ T * T⁻¹ :=
        Finset.mul_mem_mul (finsetEnum_mem T j) (Finset.inv_mem_inv (finsetEnum_mem T j'))
      have hq₃ : finsetEnum U l * (finsetEnum U l')⁻¹ ∈ U * U⁻¹ :=
        Finset.mul_mem_mul (finsetEnum_mem U l) (Finset.inv_mem_inv (finsetEnum_mem U l'))
      have hprod : finsetEnum S i' * (finsetEnum S i)⁻¹ * (finsetEnum T j * (finsetEnum T j')⁻¹)
          * (finsetEnum U l * (finsetEnum U l')⁻¹) = 1 := by
        rw [show finsetEnum S i' * (finsetEnum S i)⁻¹ * (finsetEnum T j * (finsetEnum T j')⁻¹)
                * (finsetEnum U l * (finsetEnum U l')⁻¹)
              = finsetEnum S i' * ((finsetEnum S i)⁻¹ * finsetEnum T j
                  * ((finsetEnum T j')⁻¹ * finsetEnum U l) * ((finsetEnum U l')⁻¹ * finsetEnum S i'))
                * (finsetEnum S i')⁻¹ from by group, hone]
        group
      obtain ⟨e1, e2, e3⟩ := h _ hq₁ _ hq₂ _ hq₃ hprod
      exact ⟨finsetEnum_injective T (mul_inv_eq_one.mp e2),
             finsetEnum_injective U (mul_inv_eq_one.mp e3),
             finsetEnum_injective S (mul_inv_eq_one.mp e1)⟩
    · -- ⇐ direction: telescoping.
      rintro ⟨hj, hl, hi⟩
      rw [← congrArg (finsetEnum T) hj, ← congrArg (finsetEnum U) hl,
        congrArg (finsetEnum S) hi]
      group
  rw [← hEq]
  exact rank_comp_le (mulTensor k G) (quotIndex S T) (quotIndex T U) (quotIndex U S)

/-- Sanity anchor: the group-algebra tensor has rank at most `|G|²` (the
generic `a * b` bound; the honest Murthy statement bounds `R⟨|S|,|T|,|U|⟩`,
not `R(mulTensor k G)`, from above). -/
theorem rank_mulTensor_le (k : Type*) [CommSemiring k] (G : Type*) [Group G]
    [Fintype G] [DecidableEq G] :
    rank (mulTensor k G) ≤ Fintype.card G * Fintype.card G :=
  rank_le_mul (mulTensor k G)

end Bridge

end BilinearComplexity
