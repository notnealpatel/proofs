import GroupTPP.TPP
import GroupTPP.Wedderburn
import GroupTPP.GroupAlgebraCenter

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

## The canonical definition and the bridge lemma

`charDegrees G` is defined **canonically and choice-free** as the multiset of
`(Module.length ℂ[G] c).toNat` over the isotypic components
`c ∈ isotypicComponents ℂ[G] ℂ[G]` of the group algebra as a module over itself
(via `GroupTPP.Wedderburn.isotypicLengthMultiset`).  Maschke
(`Mathlib.RepresentationTheory.Maschke`, `char ℂ = 0`) makes `ℂ[G]` semisimple,
so the components are finitely many, one per isomorphism class of simple
`ℂ[G]`-modules (= irreducible complex representations), and the length of a
component counts the multiplicity of its simple in `ℂ[G]` — which equals the
dimension of the corresponding irrep.  That this multiset agrees with the
matrix-block sizes of **any** Wedderburn–Artin decomposition is the content of
the bridge lemma

  `charDegrees_eq_of_algEquiv :
    (e : ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →
    charDegrees G = Finset.univ.val.map d`,

i.e. **Wedderburn uniqueness** over an algebraically closed field
(`GroupTPP.Wedderburn.isotypicLengthMultiset_eq_of_algEquiv`; the existence half is
Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`, and the
uniqueness half is an explicit Mathlib TODO).

The two classical identities

  `Σᵢ dᵢ² = |G|`   and   `#{irreps} = #{conjugacy classes}`

are both **absent** from Mathlib and both now **proved** here (`sorry`-free).
The first (`charDegreeSum_two`): extract a decomposition with
`exists_algEquiv_pi_matrix_of_isAlgClosed`, rewrite with
`charDegrees_eq_of_algEquiv`, and count `ℂ`-dimensions.  The second
(`card_charDegrees`): the same extraction, then match the dimension of the
center of `ℂ[G]` computed on both sides — it is the number `n` of matrix blocks
(each matrix algebra is central, `GroupTPP.Wedderburn.finrank_center_pi` transported
along `GroupTPP.Wedderburn.centerCongr`), and it is `#ConjClasses G` by the
class-sum basis (`GroupTPP.GroupAlgebraCenter.classSumBasis`).  Both are stated as
named theorems so downstream files (CU Thm 4.1, the `n(G)` barrier) import them
by name rather than re-deriving them.

## Main definitions

* `GroupTPP.CharDegrees.charDegrees` — the multiset of irreducible complex character
  degrees of `G`, defined canonically via the isotypic components of `ℂ[G]`
  (**`sorry`-free**).
* `GroupTPP.CharDegrees.charDegreeSum` — `Dᵣ(G) = Σᵢ dᵢʳ`, the `ℕ`-exponent power sum.
* `GroupTPP.CharDegrees.charDegreeSumReal` — `D_x(G) = Σᵢ dᵢˣ`, the `ℝ`-exponent power
  sum (via `Real.rpow`), the form CU Thm 4.1 compares the TPP capacity against.
* `GroupTPP.CharDegrees.minNontrivIrrepDim` — `n(G)`, the smallest degree `> 1` (or
  `0` if none, i.e. for abelian `G`).

## Main results

* `GroupTPP.CharDegrees.charDegrees_eq_of_algEquiv` — **the bridge lemma**
  (`sorry`-free): `charDegrees G` equals the block-size multiset `{d i}` of
  *any* Wedderburn decomposition `ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`.
* `GroupTPP.CharDegrees.charDegreeSum_two` — (**`sorry`-free**) `D₂(G) = |G|`, i.e.
  `Σᵢ dᵢ² = |G|`. The fundamental identity (Wedderburn + `dim ℂ[G] = |G|`).
* `GroupTPP.CharDegrees.card_charDegrees` — (**`sorry`-free**) the number of
  irreducible representations equals the number of conjugacy classes of `G`
  (via the class-sum basis of the center, `GroupTPP.GroupAlgebraCenter`).
* `GroupTPP.CharDegrees.charDegreeSumReal_natCast` — the `ℕ`↔`ℝ` exponent bridge
  `D_(r)(G) = (Dᵣ(G) : ℝ)` for natural `r` (`sorry`-free).
* `GroupTPP.CharDegrees.charDegreeSum_zero`, `charDegreeSum_one` — `D₀(G) = #{irreps}`
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

namespace GroupTPP.CharDegrees

/-! ### The character-degree multiset (canonical, choice-free) -/

/-- **The character-degree multiset.** `charDegrees G` is the multiset of
dimensions `d₁, …, d_r` of the irreducible complex representations of the finite
group `G`, *with multiplicity* (distinct irreps can share a degree — e.g. `S₃`
has degrees `1, 1, 2` — and the power sums below count each irrep, so a
`Multiset` rather than a `Finset` is the faithful container; a `Finset` would
collapse `1, 1, 2 ↦ {1, 2}` and break `Σ dᵢ² = |G|`).

**Canonical, choice-free definition**: the multiset of
`(Module.length ℂ[G] c).toNat` over the isotypic components
`c ∈ isotypicComponents ℂ[G] ℂ[G]` of the group algebra as a module over itself.
Maschke (`char ℂ = 0`, `Mathlib.RepresentationTheory.Maschke`) makes `ℂ[G]`
semisimple, so there are finitely many components, one per isomorphism class of
simple `ℂ[G]`-modules (= irreducible representations); the component of a simple
`S` is isomorphic to `S ^ (dim S)`, so its length is exactly the degree of the
corresponding character.  The identification with the block sizes of any
Wedderburn decomposition is `charDegrees_eq_of_algEquiv` below. -/
noncomputable def charDegrees (G : Type*) [Group G] [Fintype G] : Multiset ℕ :=
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : Fintype ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
    Fintype.ofFinite _
  Wedderburn.isotypicLengthMultiset (MonoidAlgebra ℂ G)

/-- **The bridge lemma (Wedderburn uniqueness for `ℂ[G]`).**  The canonical
character-degree multiset equals the block-size multiset `{d i}` of **any**
pi-matrix Wedderburn decomposition of the group algebra.  This is the
well-definedness statement that lets downstream results extract an arbitrary
decomposition from `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
and transport its block data to `charDegrees`. -/
theorem charDegrees_eq_of_algEquiv (G : Type*) [Group G] [Fintype G] {n : ℕ}
    {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    charDegrees G = Finset.univ.val.map d := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : Fintype ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
    Fintype.ofFinite _
  exact Wedderburn.isotypicLengthMultiset_eq_of_algEquiv e

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

/-! ### The two classical identities (the foundation theorems)

These are the two standard representation-theory facts that justify the whole
program but are **absent from Mathlib**. They are stated here as named theorems
so downstream files import them by name. Both follow from the bridge lemma
`charDegrees_eq_of_algEquiv` (extract a decomposition from
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`, transport, and
count `ℂ`-dimensions resp. match centers), and both are proved `sorry`-free:
the dimension count is `charDegreeSum_two`, the center match is
`card_charDegrees`. -/

/-- **Sum of squared degrees equals the group order:** `D₂(G) = |G|`, i.e.
`Σᵢ dᵢ² = |G|`.

This is the fundamental identity of complex representation theory, absent from
Mathlib (no `Σ dᵢ² = |G|` declaration) — **upstream candidate**.

Proof: Maschke (`NeZero (|G| : ℂ)`) makes `ℂ[G]` semisimple, so
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` yields an indexed
Wedderburn decomposition `e : ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin dᵢ) (Fin dᵢ) ℂ`; the
bridge lemma `charDegrees_eq_of_algEquiv` identifies `charDegrees G` with
`{dᵢ}`, and taking `ℂ`-dimensions along `e` gives
`|G| = dim ℂ[G] = Σᵢ dim (Matrix (Fin dᵢ) (Fin dᵢ) ℂ) = Σᵢ dᵢ²` (the group
elements are a basis of `ℂ[G]`; each matrix block contributes `dᵢ²`). -/
theorem charDegreeSum_two (G : Type*) [Group G] [Fintype G] :
    charDegreeSum G 2 = Fintype.card G := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hd
  have hsum : charDegreeSum G 2 = ∑ i, d i ^ 2 := by
    unfold charDegreeSum
    rw [charDegrees_eq_of_algEquiv G e, Multiset.map_map]
    rfl
  have hR : Module.finrank ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) = ∑ i, d i ^ 2 := by
    rw [Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, pow_two]
  calc charDegreeSum G 2 = ∑ i, d i ^ 2 := hsum
    _ = Module.finrank ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := hR.symm
    _ = Module.finrank ℂ (MonoidAlgebra ℂ G) := e.toLinearEquiv.finrank_eq.symm
    _ = Fintype.card G := Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ)

/-- **Number of irreps equals number of conjugacy classes:** the cardinality of
the character-degree multiset equals `|ConjClasses G|`.

This is the second classical count, absent from Mathlib — **upstream
candidate**. Proof: the dimension of the center of `ℂ[G]` equals both the
number of simple factors of a Wedderburn decomposition (one per irrep: each
matrix block is a central algebra, so contributes exactly the scalars to the
center — `GroupTPP.Wedderburn.finrank_center_pi`, transported along
`GroupTPP.Wedderburn.centerCongr e`) and the number of conjugacy classes (the class
sums are a basis of the center — `GroupTPP.GroupAlgebraCenter.classSumBasis`,
consumed via `GroupTPP.GroupAlgebraCenter.finrank_center`). -/
theorem card_charDegrees (G : Type*) [Group G] [Fintype G] :
    Multiset.card (charDegrees G) = Nat.card (ConjClasses G) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hd
  haveI : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  -- the number of irreps is the number of matrix blocks
  have h1 : Multiset.card (charDegrees G) = n := by
    rw [charDegrees_eq_of_algEquiv G e, Multiset.card_map]
    exact Finset.card_fin n
  -- the dimension of the center, computed on the matrix side, is also `n`
  have h2 : Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) = n := by
    rw [LinearEquiv.finrank_eq (Wedderburn.centerCongr e).toLinearEquiv,
      Wedderburn.finrank_center_pi, Fintype.card_fin]
  -- the dimension of the center, computed via class sums, is `#ConjClasses G`
  have h3 := GroupAlgebraCenter.finrank_center ℂ G
  omega

/-! ### Immediate consequences of the foundation theorems (`sorry`-free) -/

/-- The number of irreducible representations, expressed via `D₀`, equals the
number of conjugacy classes. Combines `charDegreeSum_zero` and
`card_charDegrees`. -/
theorem charDegreeSum_zero_eq_card_conjClasses (G : Type*) [Group G] [Fintype G] :
    charDegreeSum G 0 = Nat.card (ConjClasses G) := by
  rw [charDegreeSum_zero, card_charDegrees]

end GroupTPP.CharDegrees
