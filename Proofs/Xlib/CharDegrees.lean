import Xlib.TPP

/-!
# Character degrees: the indexed representation-theory foundation

This file builds the **character-degree foundation** for the Cohn–Umans
group-theoretic matrix-multiplication program. Its centerpiece is the multiset
of dimensions of the irreducible complex representations of a finite group `G`,

  `charDegrees G : Multiset ℕ`,

and the two power-sum invariants built on it,

  `charDegreeSum G r = Σᵢ dᵢʳ`   (`ℕ`-exponent, Hedtke–Murthy `Dᵣ(G)`),
  `charDegreeSumReal G x = Σᵢ dᵢˣ` (`ℝ`-exponent, the form CU Thm 4.1 uses),

together with the minimal nontrivial irrep dimension `minNontrivIrrepDim G`
(the `n(G)` of the Blasiak–Church–Cohn–Grochow–Umans barrier).

## The foundation debt is a single `sorry`

The *only* `sorry` in the definitional layer is in `charDegrees` itself. At the
present Mathlib coverage there is no canonical **enumeration** of the
irreducible complex representations of `G`. Mathlib has the *unindexed*
Wedderburn–Artin decomposition
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
(`ℂ[G] ≃ₐ[ℂ] Π i : Fin n, Matrix (Fin (dᵢ)) (Fin (dᵢ)) ℂ` with `dᵢ ≠ 0`), and the
semisimplicity / finite-dimensionality of `ℂ[G]` (Maschke,
`Mathlib.RepresentationTheory.Maschke`), but it does **not** package the
decomposition as an indexed family tied to the isomorphism classes of simple
`ℂ[G]`-modules, nor does it record either of the two classical identities

  `Σᵢ dᵢ² = |G|`   and   `#{irreps} = #{conjugacy classes}`.

Both are confirmed **absent** from Mathlib (`leandoc` finds `FDRep.character`,
`FDRep.Simple`, `char_orthonormal`, but no irrep-indexing / `Σ dᵢ² = |G|` /
irrep-count declaration).

The single `sorry` in `charDegrees` isolates this entire debt: every other
declaration below is a **total, `sorry`-free** function of the abstract multiset,
so a future task landing the indexed Wedderburn layer replaces that one `sorry`
and the whole file becomes `sorry`-free. The two classical identities are stated
as named theorems (`charDegreeSum_two` and `card_charDegrees`), each a `sorry`
with the standard-proof citation, so downstream files (CU Thm 4.1, the `n(G)`
barrier) import them by name rather than re-deriving them.

## Main definitions

* `Xlib.CharDegrees.charDegrees` — the multiset of irreducible complex character
  degrees of `G`. **The single foundation `sorry`.**
* `Xlib.CharDegrees.charDegreeSum` — `Dᵣ(G) = Σᵢ dᵢʳ`, the `ℕ`-exponent power sum.
* `Xlib.CharDegrees.charDegreeSumReal` — `D_x(G) = Σᵢ dᵢˣ`, the `ℝ`-exponent power
  sum (via `Real.rpow`), the form CU Thm 4.1 compares the TPP capacity against.
* `Xlib.CharDegrees.minNontrivIrrepDim` — `n(G)`, the smallest degree `> 1` (or
  `0` if none, i.e. for abelian `G`).

## Main results

* `Xlib.CharDegrees.charDegreeSum_two` — **(`sorry`)** `D₂(G) = |G|`, i.e.
  `Σᵢ dᵢ² = |G|`. The fundamental identity (Wedderburn + `dim ℂ[G] = |G|`).
* `Xlib.CharDegrees.card_charDegrees` — **(`sorry`)** the number of irreducible
  representations equals the number of conjugacy classes of `G`.
* `Xlib.CharDegrees.charDegreeSumReal_natCast` — the `ℕ`↔`ℝ` exponent bridge
  `D_(r)(G) = (Dᵣ(G) : ℝ)` for natural `r` (`sorry`-free).
* `Xlib.CharDegrees.charDegreeSum_zero`, `charDegreeSum_one` — `D₀(G) = #{irreps}`
  and `D₁(G) = Σᵢ dᵢ` (`sorry`-free unfoldings).

## References

* H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, [arXiv:math/0307321] (Thm 4.1: `|G|^{ω/α} ≤ Σᵢ dᵢ^ω`).
* J. Hedtke, A. R. Murthy, *Search and test algorithms for triple product
  property triples* / the `Dᵣ` capacity-sum bound, [arXiv:1305.0448].
* J. Blasiak, T. Church, H. Cohn, J. Grochow, C. Umans, *On cap sets and the
  group-theoretic approach to matrix multiplication* (`n(G)`, the minimal
  nontrivial irrep dimension barrier).
-/

open scoped BigOperators

namespace Xlib.CharDegrees

/-! ### The character-degree multiset (the single foundation `sorry`) -/

/-- **The character-degree multiset.** `charDegrees G` is the multiset of
dimensions `d₁, …, d_r` of the irreducible complex representations of the finite
group `G`, *with multiplicity* (distinct irreps can share a degree — e.g. `S₃`
has degrees `1, 1, 2` — and the power sums below count each irrep, so a
`Multiset` rather than a `Finset` is the faithful container; a `Finset` would
collapse `1, 1, 2 ↦ {1, 2}` and break `Σ dᵢ² = |G|`).

**This is the single `sorry` of the entire foundation.** Constructing it requires
the *indexed* Wedderburn–Artin decomposition of `ℂ[G]` — i.e. extracting the
family `d : Fin n → ℕ` of matrix-block sizes from
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` (applied to the
finite-dimensional semisimple ℂ-algebra `ℂ[G]`; finite-dimensionality from
`Fintype G`, semisimplicity from Maschke since `char ℂ = 0`) and identifying the
blocks with the isomorphism classes of simple `ℂ[G]`-modules. That indexing is
not yet in Mathlib, so the body is `sorry`.

A future task landing the indexed Wedderburn layer replaces this `sorry` with
`(Finset.univ : Finset (Fin n)).val.map d` (equivalently, the multiset of
`Module.finrank ℂ Vᵢ` over isomorphism classes of simple `FDRep ℂ G`); every
declaration below then becomes `sorry`-free. -/
noncomputable def charDegrees (G : Type*) [Group G] [Fintype G] : Multiset ℕ :=
  sorry

/-! ### The character-degree power sums `Dᵣ` (`sorry`-free over `charDegrees`) -/

/-- The **character-degree power sum** `Dᵣ(G) = Σᵢ dᵢʳ` (Hedtke–Murthy,
[arXiv:1305.0448]), summing the `r`-th powers of the irreducible character
degrees. The Cohn–Umans capacity bound (CU Thm 4.1) is the case `r = ω`. -/
noncomputable def charDegreeSum (G : Type*) [Group G] [Fintype G] (r : ℕ) : ℕ :=
  ((charDegrees G).map (fun d => d ^ r)).sum

/-- The **real-exponent character-degree power sum** `D_x(G) = Σᵢ dᵢˣ` for
`x : ℝ`, using `Real.rpow`. This is the form CU Thm 4.1 compares the TPP capacity
against: `(tppCapacity G : ℝ) ^ (ω / 3) ≤ charDegreeSumReal G ω`. -/
noncomputable def charDegreeSumReal (G : Type*) [Group G] [Fintype G] (x : ℝ) : ℝ :=
  ((charDegrees G).map (fun d => (d : ℝ) ^ x)).sum

/-! ### The minimal nontrivial irrep dimension `n(G)` (`sorry`-free) -/

/-- **The minimal nontrivial irrep dimension** `n(G)` (Blasiak–Church–Cohn–
Grochow–Umans): the smallest character degree strictly greater than `1`, or `0`
if no such degree exists (i.e. for abelian `G`, where every `dᵢ = 1`).

Total `ℕ`-valued: `charDegrees G` is filtered to the degrees `> 1`, deduplicated
to a `Finset`, and `Finset.min : Finset ℕ → WithTop ℕ` (which returns `⊤` on the
empty finset) is collapsed to `ℕ` with default `0` via `WithTop.untopD`.
Deduplication is harmless here — the *minimum* of a multiset is unaffected by
multiplicity. -/
noncomputable def minNontrivIrrepDim (G : Type*) [Group G] [Fintype G] : ℕ :=
  ((charDegrees G).filter (fun d => d > 1)).toFinset.min.untopD 0

/-! ### Unfoldings and the `ℕ`↔`ℝ` exponent bridge (`sorry`-free) -/

/-- `D₀(G) = #{irreps}`: the zeroth power sum is the number of irreducible
representations (the multiset cardinality), since `dᵢ⁰ = 1`. -/
@[simp] theorem charDegreeSum_zero (G : Type*) [Group G] [Fintype G] :
    charDegreeSum G 0 = Multiset.card (charDegrees G) := by
  simp only [charDegreeSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]

/-- `D₁(G) = Σᵢ dᵢ`: the first power sum is the plain sum of the degrees. -/
@[simp] theorem charDegreeSum_one (G : Type*) [Group G] [Fintype G] :
    charDegreeSum G 1 = (charDegrees G).sum := by
  simp only [charDegreeSum, pow_one, Multiset.map_id']

/-- The **`ℕ`↔`ℝ` exponent bridge**: for a *natural* exponent `r`, the
real-exponent power sum agrees with the cast of the natural-exponent power sum,
`D_(r)(G) = (Dᵣ(G) : ℝ)`. This lets CU Thm 4.1 (stated with `Real.rpow`) consume
the `ℕ`-valued `Dᵣ` for integer exponents with no coercion friction. -/
theorem charDegreeSumReal_natCast (G : Type*) [Group G] [Fintype G] (r : ℕ) :
    charDegreeSumReal G (r : ℝ) = (charDegreeSum G r : ℝ) := by
  unfold charDegreeSumReal charDegreeSum
  induction charDegrees G using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [Real.rpow_natCast]

/-! ### The two classical identities (the foundation theorems, `sorry`)

These are the two standard representation-theory facts that justify the whole
program but are **absent from Mathlib**. They are stated here as named theorems
so downstream files import them by name. Each is a `sorry` with its standard
proof cited; landing the indexed Wedderburn layer (the same layer that discharges
the `charDegrees` `sorry`) discharges both. -/

/-- **Sum of squared degrees equals the group order:** `D₂(G) = |G|`, i.e.
`Σᵢ dᵢ² = |G|`.

This is the fundamental identity of complex representation theory. Standard
proof: the indexed Wedderburn decomposition gives
`ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin dᵢ) (Fin dᵢ) ℂ`; taking `ℂ`-dimensions of both sides,
`dim ℂ[G] = Σᵢ dᵢ²`, and `dim ℂ[G] = |G|` (the group elements are a basis).
Absent from Mathlib (no `Σ dᵢ² = |G|` declaration). `sorry`. -/
theorem charDegreeSum_two (G : Type*) [Group G] [Fintype G] :
    charDegreeSum G 2 = Fintype.card G :=
  sorry

/-- **Number of irreps equals number of conjugacy classes:** the cardinality of
the character-degree multiset equals `|ConjClasses G|`.

This is the second classical count. Standard proof: the dimension of the center
of `ℂ[G]` equals both the number of simple factors (one per irrep, from the
Wedderburn decomposition) and the number of conjugacy classes (the class sums are
a basis of the center). Absent from Mathlib. `sorry`. -/
theorem card_charDegrees (G : Type*) [Group G] [Fintype G] :
    Multiset.card (charDegrees G) = Nat.card (ConjClasses G) :=
  sorry

/-! ### Immediate consequences of the foundation theorems (`sorry`-free) -/

/-- The number of irreducible representations, expressed via `D₀`, equals the
number of conjugacy classes. Combines `charDegreeSum_zero` and
`card_charDegrees`; `sorry`-free *given* those. -/
theorem charDegreeSum_zero_eq_card_conjClasses (G : Type*) [Group G] [Fintype G] :
    charDegreeSum G 0 = Nat.card (ConjClasses G) := by
  rw [charDegreeSum_zero, card_charDegrees]

end Xlib.CharDegrees
