/- One general-Group STPP capacity admission remains. The CommGroup capacity
assembly is proved in production by all-powers multinomial amplification. -/
import GroupTPP.STPPCapacityComm

/-!
# Retired implementation card: CKSU STPP and wreath inequalities

These are published results from Cohn–Kleinberg–Szegedy–Umans,
arXiv:math/0511460, not open mathematical conjectures. Only the central
simultaneous-TPP capacity and wreath-specialization portions belong to this
archive. The chart-USP construction and `ω < 2.41` derivation remain separate
in `Formalize/GroupTPP-Barriers-Lie-ChartUSP.md`.

Production retains the right-quotient, cyclic `SimultaneousTPP` convention,
direct-product closure, wreath embeddings, character-degree bounds and
asymptotic witness families. The hypothesis-factored wreath theorem and its
CommGroup specialization are proved in `GroupTPP.STPPCapacityComm` by exact
prescribed-type counting and all-powers multinomial amplification. Their
original names and signatures remain exposed here through the import.

One admission remains below: the general capacity theorem with `[Group G]`.
Its general wreath character-degree bound or direct-sum tensor/Schönhage
asymptotic sum inequality remains unpaid. The proved commutative specialization
does not discharge this general theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.STPPWreath

open GroupTPP.TPP GroupTPP.CUCapacity GroupTPP.CharDegrees

variable {G : Type*} [Group G]

/-! ### The STPP capacity inequality (CKSU `theorem:asi`, `sorry`)

The multi-triple analogue of `GroupTPP.CUCapacity.capacity_rpow_le_charDegreeSumReal`
(CU Theorem 4.1). Whereas the single-triple bound reads
`(|S|·|T|·|U|)^{ω/3} ≤ D_ω(G)`, the STPP packs `n` independent triples into one
group-algebra multiplication, giving a *sum* on the left. -/

/-- **CKSU Theorem `theorem:asi`** [math/0511460]: the **STPP capacity
inequality**. If the `n` triples `(A i, B i, C i)` of a finite group `G` satisfy
the STPP, then

  `∑ᵢ (|A i| · |B i| · |C i|)^{ω/3} ≤ D_ω(G) = ∑ₖ dₖ^ω`.

This is the multi-triple version of CU Theorem 4.1
(`GroupTPP.CUCapacity.capacity_rpow_le_charDegreeSumReal`). For abelian `G` the
right-hand side collapses to `|G|` (`GroupTPP.CharDegrees.charDegreeSum_two`), the
form used in the `ω < 2.93` example.

**Proof route**: the general-`G` form still requires a general wreath
character-degree bound or a direct-sum tensor/Schönhage asymptotic sum
inequality. The hypothesis-factored `stpp_capacity_le_of_wreath` and the
commutative `stpp_capacity_le_comm` are now proved in production by
all-powers multinomial amplification; this declaration alone remains admitted. -/
theorem stpp_capacity_le {n : ℕ} [Fintype G] [DecidableEq G]
    (A B C : Fin n → Finset G) (h : SimultaneousTPP A B C) :
    ∑ i, ((A i).card * (B i).card * (C i).card : ℝ) ^ (ω / 3)
      ≤ charDegreeSumReal G ω :=
  sorry

end GroupTPP.STPPWreath
