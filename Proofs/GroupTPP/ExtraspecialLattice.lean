import Mathlib

/-!
# The upper subgroup lattice of an extraspecial 2-group is type-independent

This file formalizes the following fact about **extraspecial 2-groups**
`G = 2^{1+2n}` (groups of order `2^{1+2n}` with cyclic center `Z(G)` of order `2`
equal to the commutator and Frattini subgroups, so that `V := G/Z(G)` is an
elementary abelian `2`-group, i.e. a `GF(2)`-vector space of dimension `2n`):

> **Theorem (upper-lattice type-invariance).** For each `k` with `n+1 ≤ k ≤ 2n+1`,
> the number of subgroups of order `2^k` is the same for the `+`-type group
> `2^{1+2n}_+` and the `-`-type group `2^{1+2n}_-`.

There are exactly two extraspecial groups of each order `2^{1+2n}`, distinguished
by the **Arf invariant** of the quadratic form `q(xZ) = x²` on `V` (the `+` type has
Arf invariant `0`, the `-` type Arf invariant `1`). The remarkable feature is that
although the two groups differ in their *lower* subgroup lattice (e.g. their counts
of involutions, hence of order-`2` subgroups, are `2^{2n} ± 2^n - 1`), their *upper*
subgroup lattices — subgroups of order `≥ 2^{n+1}` — are counted identically.
This was verified computationally (GAP/Sage) for `n = 1, 2, 3`:

| order | `+` count | `-` count |
| ----- | --------- | --------- |
| `n=2`: `2^3 = 8`  | `35`  | `35`  |
| `n=2`: `2^4 = 16` | `15`  | `15`  |
| `n=3`: `2^4 = 16` | `1395`| `1395`|
| `n=3`: `2^5 = 32` | `651` | `651` |
| `n=3`: `2^6 = 64` | `63`  | `63`  |

## The mathematics (and a corrected reduction)

The phenomenon reduces to two facts.

1. **(Group → form)** *Every subgroup `H` with `|H| ≥ 2^{n+1}` contains `Z(G)`.*
   If `Z(G) ⊄ H` then, as `|Z(G)| = 2`, necessarily `H ∩ Z(G) = 1`; the image `W`
   of `H` in `V = G/Z(G)` then has `|W| = |H|`, and for `x, y ∈ H` the commutator
   `⁅x,y⁆ ∈ H ∩ G' = H ∩ Z(G) = 1`, so `W` is **totally isotropic** for the
   commutator symplectic form `B` on `V`. A totally isotropic subspace of a
   non-degenerate symplectic space of dimension `2n` has dimension `≤ n` (Lagrangian
   bound, `ExtraspecialLattice.isotropic_two_finrank_le`), whence `|H| = |W| ≤ 2^n`,
   contradiction. This is the genuine content; it is folklore / a standard exercise
   (Aschbacher, *Finite Group Theory* 2nd ed., §23; Winter, *Rocky Mountain J. Math.*
   2 (1972) 159–168; the isotropic bound is Artin, *Geometric Algebra*).

2. **(Form → count)** *Once `H ⊇ Z(G)`, `H` corresponds to the subspace `H/Z(G)` of
   `V`, and the number of `m`-dimensional subspaces of `V` does not depend on any
   quadratic refinement of `B` — the subspace lattice does not see `q`.* Hence the
   count of subgroups of order `2^k` (`k ≥ n+1`) equals the number of `(k-1)`-
   dimensional subspaces of `GF(2)^{2n}`, the Gaussian binomial `[2n; k-1]_2`, which
   is manifestly independent of the type. The abstract content is
   `ExtraspecialLattice.card_fixedDimSubspaces_eq_of_finrank_eq`: two `GF(2)`-spaces
   of equal dimension have equinumerous Grassmannians.

**Caveat on the naive reduction.** One might hope to phrase fact 1 as "for `k ≥ n`
every `k`-dimensional `B`-isotropic subspace is totally singular for `q`" — but this
is **false**: for the `-` type *no* maximal (`n`-dimensional) `B`-isotropic subspace
is `q`-singular (its Witt index is `n-1`), and even for the `+` type only some are
(`2`, `6`, `30` of the `3`, `15`, `135` Lagrangians for `n = 1, 2, 3`). The correct
reduction does **not** use the quadratic form at all beyond fact 1: subgroups
containing `Z` biject with *all* subspaces, with no isotropy condition, which is
exactly why the count is type-independent.

## Formalization strategy

Extraspecial groups, and the commutator-induced `GF(2)`-symplectic form, are not in
Mathlib. We therefore package the standard structure of an extraspecial 2-group into
`ExtraspecialLattice.ExtraspecialData`, whose fields are precisely the textbook facts
(Aschbacher §23): the center of order `2`, the `GF(2)`-space `V = G/Z` of dimension
`2n` with its non-degenerate form `B`, the isotropy of `Z`-disjoint subgroups
(packaging the class-`2` commutator identity), and the subgroup-correspondence
`{H | Z ≤ H} ≃ {subspaces of V}` with its order bookkeeping `|H| = 2·|H/Z|`.

Everything *derived* from these fields is a complete proof with no `sorry`:

* `isotropic_two_finrank_le` — the Lagrangian/isotropic dimension bound (pure linear
  algebra, via `BilinForm.finrank_orthogonal`);
* `card_le_of_disjoint_center`, `center_le_of_card_ge` — fact 1;
* `card_fixedDimSubspaces_eq_of_finrank_eq` — fact 2 (pure linear algebra, via
  `Submodule.orderIsoMapComap` and `LinearEquiv.finrank_map_eq`);
* `upperSubgroupEquiv`, `subgroupCount_eq_fixedDim` — the reduction;
* `subgroupCount_eq_of_same_rank` — the main theorem.

The packaging is *not* an unwitnessed hypothesis bundle: the section
`A concrete model: D₄ = 2^{1+2}_+, the rank-1 witness` at the end of this file
constructs `extraspecialD4 : ExtraspecialData (DihedralGroup 4)` (order `8`,
`n = 1`), jointly satisfying every field, so all five conditional results above
are statements about a nonempty class.

## References

* M. Aschbacher, *Finite Group Theory*, 2nd ed., Cambridge Univ. Press, §23.
* D. L. Winter, *The automorphism group of an extraspecial p-group*,
  Rocky Mountain J. Math. **2** (1972) 159–168.
* E. Artin, *Geometric Algebra*, Interscience, 1957 (symplectic isotropic bound).
* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2*,
  J. Reine Angew. Math. **183** (1941) 148–167 (Arf invariant, Witt index).
-/

open Module LinearMap LinearMap.BilinForm Subgroup

namespace ExtraspecialLattice

/-- Abstract data describing an extraspecial-type 2-group `G` of rank `n`, i.e. of order
`2^{1+2n}` and type `±`. The fields bundle the standard structure theory of extraspecial
2-groups (Aschbacher, *Finite Group Theory*, §23):

* the center `Z` of order `2` (`= G' = Φ(G)`);
* the elementary abelian quotient `V = G/Z`, a `GF(2)`-vector space of dimension `2n`;
* the non-degenerate commutator symplectic form `B` on `V`;
* `isotropicImage`: a subgroup disjoint from `Z` maps to a `B`-isotropic subspace of the
  same cardinality (this packages the class-`2` commutator identity
  `⁅x,y⁆ ∈ H ⊓ G' = H ⊓ Z`);
* `corr`/`corr_card`: the subgroup-correspondence `{H | Z ≤ H} ≃ {subspaces of V}` with the
  order bookkeeping `|H| = |Z|·|H/Z| = 2·|H/Z|`.

The two extraspecial groups `2^{1+2n}_±` of a given rank differ only in the Arf invariant
of the *quadratic* refinement `q(xZ) = x²` of `B`; the data recorded here is exactly the
type-independent part, which is why it suffices to prove the upper-lattice invariance.

Scope note (audit D1, `.tasks/f5exp/docs/vacuity-ad1-recheck.md`): the fields do not
*force* the bindings named above — `Z` need not be the full center, `B` need not be the
commutator form, and abelian instances exist at `n = 0`. Every theorem below is a theorem
about this data-class; genuinely extraspecial content enters only through concrete
witnesses such as `extraspecialD4`. -/
structure ExtraspecialData (G : Type*) [Group G] where
  /-- The rank: `G` has order `2^{1+2n}`. -/
  n : ℕ
  /-- The center `Z(G) = G' = Φ(G)`. -/
  Z : Subgroup G
  /-- The center has order `2`. -/
  hZcard : Nat.card Z = 2
  /-- The `GF(2)`-vector space `V = G/Z`. -/
  V : Type*
  instAddCommGroup : AddCommGroup V
  instModule : Module (ZMod 2) V
  instFinite : FiniteDimensional (ZMod 2) V
  /-- `V` has dimension `2n`. -/
  hdimV : finrank (ZMod 2) V = 2 * n
  /-- The non-degenerate commutator symplectic form on `V`. -/
  B : LinearMap.BilinForm (ZMod 2) V
  hBnondeg : B.Nondegenerate
  /-- A subgroup disjoint from the center maps to a totally isotropic subspace of the same
  size. This packages the class-`2` commutator identity: for `x, y ∈ H` with `H ⊓ Z = ⊥`,
  the commutator `⁅x,y⁆ ∈ H ⊓ G' = H ⊓ Z = ⊥`, so the images are `B`-orthogonal, i.e. the
  image submodule `W` satisfies `W ≤ Wᗮ`. -/
  isotropicImage : ∀ H : Subgroup G, Disjoint H Z →
    ∃ W : Submodule (ZMod 2) V, W ≤ B.orthogonal W ∧ Nat.card H = Nat.card W
  /-- The subgroup-correspondence theorem: subgroups containing the center biject with
  subspaces of `V = G/Z`, via `H ↦ H/Z`. -/
  corr : { H : Subgroup G // Z ≤ H } ≃ Submodule (ZMod 2) V
  /-- Order bookkeeping for the correspondence: `|H| = |Z| · |H/Z| = 2 · |corr H|`. -/
  corr_card : ∀ H : { H : Subgroup G // Z ≤ H },
    Nat.card (H : Subgroup G) = 2 * Nat.card (corr H)

attribute [instance] ExtraspecialData.instAddCommGroup ExtraspecialData.instModule
  ExtraspecialData.instFinite

variable {G : Type*} [Group G]

/-! ### The Lagrangian / isotropic dimension bound -/

/-- **Lagrangian bound.** A totally isotropic subspace `W ≤ Wᗮ` of a non-degenerate
bilinear form on a finite-dimensional space has `2 · finrank W ≤ finrank V`; in particular a
totally isotropic subspace of a `2n`-dimensional symplectic space has dimension `≤ n`.

The proof is the standard one: `finrank W ≤ finrank Wᗮ = finrank V - finrank W`. -/
theorem isotropic_two_finrank_le
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    {U : Submodule K W} (hU : U ≤ B.orthogonal U) :
    2 * finrank K U ≤ finrank K W := by
  have h1 : finrank K U ≤ finrank K (B.orthogonal U) := Submodule.finrank_mono hU
  have h2 : finrank K (B.orthogonal U) = finrank K W - finrank K U :=
    LinearMap.BilinForm.finrank_orthogonal hB U
  have h3 : finrank K U ≤ finrank K W := Submodule.finrank_le U
  lia

/-! ### Fact 1: large subgroups contain the center -/

/-- In an extraspecial-type 2-group of rank `n`, every subgroup `H` disjoint from the center
has order at most `2^n`. This is the Lagrangian bound transported through the commutator form:
`H ↪ V` with isotropic image `W`, so `|H| = |W| = 2^{dim W} ≤ 2^n`. -/
theorem card_le_of_disjoint_center (E : ExtraspecialData G)
    {H : Subgroup G} (hH : Disjoint H E.Z) :
    Nat.card H ≤ 2 ^ E.n := by
  obtain ⟨W, hWiso, hcard⟩ := E.isotropicImage H hH
  have hbound : 2 * finrank (ZMod 2) W ≤ 2 * E.n := by
    have := isotropic_two_finrank_le E.B E.hBnondeg hWiso
    rwa [E.hdimV] at this
  have hfr : finrank (ZMod 2) W ≤ E.n := by lia
  have hWcard : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite E.V := Module.finite_of_finite (ZMod 2)
    have : Finite ↥W := Subtype.finite
    exact (FiniteField.pow_finrank_eq_natCard 2 W).symm
  rw [hcard, hWcard]
  exact Nat.pow_le_pow_right (by norm_num) hfr

/-- **Large subgroups contain the center.** Every subgroup of order `≥ 2^{n+1}` contains the
center `Z(G)`. This is the cutoff at order `2^n` that makes the upper subgroup lattice
type-independent: above it, every subgroup is a full preimage from `G/Z`.

The argument: if `Z ⊄ H`, then since `|Z| = 2` is prime, the subgroup `(H ⊓ Z).subgroupOf Z`
of `Z` is `⊥` or `⊤`; the `⊤` case gives `Z ≤ H` (contradiction), so it is `⊥`, i.e.
`H ⊓ Z = ⊥`, i.e. `Disjoint H Z`, whence `|H| ≤ 2^n < 2^{n+1}` by `card_le_of_disjoint_center`,
contradicting the hypothesis. -/
theorem center_le_of_card_ge (E : ExtraspecialData G)
    {H : Subgroup G} (hH : 2 ^ (E.n + 1) ≤ Nat.card H) :
    E.Z ≤ H := by
  by_contra hnle
  have hprime : Fact (Nat.card E.Z).Prime := by rw [E.hZcard]; exact ⟨Nat.prime_two⟩
  have hdisj : Disjoint H E.Z := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((H ⊓ E.Z).subgroupOf E.Z) with hbot | htop
    · -- `(H ⊓ Z).subgroupOf Z = ⊥` ⇒ `Disjoint (H ⊓ Z) Z` ⇒ `H ⊓ Z = ⊥`.
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      rw [disjoint_iff]
      exact le_antisymm (le_trans (le_inf le_rfl inf_le_right) hbot.le_bot) bot_le
    · -- `(H ⊓ Z).subgroupOf Z = ⊤` ⇒ `Z ≤ H ⊓ Z` ⇒ `Z ≤ H`, contradicting `hnle`.
      rw [Subgroup.subgroupOf_eq_top] at htop
      exact absurd (le_trans htop inf_le_left) hnle
  have hle := card_le_of_disjoint_center E hdisj
  have hlt : (2 : ℕ) ^ E.n < 2 ^ (E.n + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self E.n)
  omega

/-! ### Fact 2: subspace counts ignore the quadratic refinement -/

/-- The type of `m`-dimensional subspaces of a vector space `W`. -/
def fixedDimSubspaces (K W : Type*) [Field K] [AddCommGroup W] [Module K W] (m : ℕ) :
    Type _ := { U : Submodule K W // finrank K U = m }

/-- A linear equivalence `e : V ≃ₗ V'` transports `m`-dimensional subspaces bijectively,
since `Submodule.map e` preserves dimension. -/
noncomputable def fixedDimSubspacesEquiv {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (e : V ≃ₗ[K] V') (m : ℕ) :
    fixedDimSubspaces K V m ≃ fixedDimSubspaces K V' m :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun p => by
    rw [OrderIso.coe_toEquiv, Submodule.orderIsoMapComap_apply',
      ← Submodule.map_equiv_eq_comap_symm, e.finrank_map_eq])

/-- **Type-invariance core.** Two finite-dimensional `K`-spaces of equal dimension have the
same number of `m`-dimensional subspaces, for every `m`. This is the abstract reason the
upper-lattice counts do not depend on the extraspecial type: a quadratic refinement is extra
structure invisible to the subspace lattice. (Over `K = GF(2)` of dimension `2n`, this count
is the Gaussian binomial `[2n; m]_2`.) -/
theorem card_fixedDimSubspaces_eq_of_finrank_eq {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (h : finrank K V = finrank K V') (m : ℕ) :
    Nat.card (fixedDimSubspaces K V m) = Nat.card (fixedDimSubspaces K V' m) :=
  Nat.card_congr (fixedDimSubspacesEquiv (LinearEquiv.ofFinrankEq V V' h) m)

/-! ### The reduction and the main theorem -/

/-- The number of subgroups of `G` of order `2^k`. -/
noncomputable def subgroupCount (G : Type*) [Group G] (k : ℕ) : ℕ :=
  Nat.card { H : Subgroup G // Nat.card H = 2 ^ k }

/-- **Reduction to subspace counting.** For `k ≥ n+1`, subgroups of `G` of order `2^k` biject
with `(k-1)`-dimensional subspaces of `V = G/Z`: by `center_le_of_card_ge` every such subgroup
contains `Z`, and the correspondence `corr` sends it to a subspace `W` with
`2·|W| = |H| = 2^k`, i.e. `finrank W = k-1`. -/
noncomputable def upperSubgroupEquiv (E : ExtraspecialData G) {k : ℕ} (hk : E.n + 1 ≤ k) :
    { H : Subgroup G // Nat.card H = 2 ^ k } ≃ fixedDimSubspaces (ZMod 2) E.V (k - 1) := by
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 E.n) hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVfin : Finite E.V := Module.finite_of_finite (ZMod 2)
  -- Step 1: collapse the nested subtype using that order-`2^k` subgroups contain `Z`.
  refine (Equiv.subtypeSubtypeEquivSubtype (p := fun H : Subgroup G => E.Z ≤ H)
    (q := fun H : Subgroup G => Nat.card H = 2 ^ k)
    (fun {H} hcard => center_le_of_card_ge E
      (by rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hk))).symm.trans ?_
  -- Step 2: transport through the correspondence, matching predicates.
  refine E.corr.subtypeEquiv (fun H => ?_)
  -- `Nat.card H = 2^k ↔ finrank (corr H) = k - 1`.
  rw [E.corr_card H]
  have hWcard : Nat.card (E.corr H) = 2 ^ finrank (ZMod 2) (E.corr H) :=
    (FiniteField.pow_finrank_eq_natCard 2 (E.corr H)).symm
  rw [hWcard]
  constructor
  · intro h
    have hk' : (2 : ℕ) ^ (1 + finrank (ZMod 2) (E.corr H)) = 2 ^ k := by
      rw [pow_add, pow_one]; exact h
    have := Nat.pow_right_injective (le_refl 2) hk'
    omega
  · intro h
    rw [h]
    conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring

/-- For `k ≥ n+1`, the number of subgroups of order `2^k` equals the number of `(k-1)`-
dimensional subspaces of `V = G/Z`. -/
theorem subgroupCount_eq_fixedDim (E : ExtraspecialData G) {k : ℕ} (hk : E.n + 1 ≤ k) :
    subgroupCount G k = Nat.card (fixedDimSubspaces (ZMod 2) E.V (k - 1)) :=
  Nat.card_congr (upperSubgroupEquiv E hk)

/-- **Main theorem: upper-lattice type-invariance.** If two extraspecial-type 2-groups have
the same rank `n`, then for every `k ≥ n+1` they have the same number of subgroups of order
`2^k`. Equivalently, the upper half (orders `2^{n+1}` through `2^{2n+1}`) of the subgroup
lattice is counted identically for the `+` and `-` types: the count is the Gaussian binomial
`[2n; k-1]_2`, depending only on `n` and `k`, never on the Arf invariant. -/
theorem subgroupCount_eq_of_same_rank {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (E₁ : ExtraspecialData G₁) (E₂ : ExtraspecialData G₂) (hn : E₁.n = E₂.n)
    {k : ℕ} (hk : E₁.n + 1 ≤ k) :
    subgroupCount G₁ k = subgroupCount G₂ k := by
  rw [subgroupCount_eq_fixedDim E₁ hk, subgroupCount_eq_fixedDim E₂ (hn ▸ hk)]
  apply card_fixedDimSubspaces_eq_of_finrank_eq
  rw [E₁.hdimV, E₂.hdimV, hn]

/-! ## A concrete model: `D₄ = 2^{1+2}_+`, the rank-`1` witness

Everything above is conditional on a term of `ExtraspecialData G`. This section
discharges the satisfiability obligation (STYLE.md: "exhibit satisfiability
before committing a theorem: instantiate every hypothesis jointly at one
concrete model") by constructing `extraspecialD4 : ExtraspecialData (DihedralGroup 4)`,
the `+`-type extraspecial group of order `8 = 2^{1+2·1}`, i.e. rank `n = 1`.

The four substantive fields are discharged as follows.

* `hZcard` — `Z(D₄) = {1, r²}` has order `2`; kernel `decide`.
* `isotropicImage` — this is *fact 1* at `n = 1`: a subgroup `H` with
  `H ⊓ Z = 1` cannot contain `r² = (r¹)²`, so `H` has index neither `1`
  (that is `H = ⊤`) nor `2` (index-`2` subgroups contain all squares,
  `Subgroup.mul_self_mem_of_index_two`); with `|H| · [D₄ : H] = 8` this forces
  `|H| ≤ 2`, and a subspace of the required order (`1` or `2`) that is
  isotropic exists because every subspace of dimension `≤ 1` is isotropic for
  an alternating form.
* `corr` — the correspondence theorem `QuotientGroup.comapMk'OrderIso`,
  composed with `Subgroup.toAddSubgroup` and `AddSubgroup.toZModSubmodule`
  (over `ZMod 2` every additive subgroup is a submodule).
* `corr_card` — the first isomorphism theorem for `H → D₄/Z` plus Lagrange:
  the kernel is `Z` (as `Z ≤ H`), of order `2`.

**On the choice of `B`.** The structure's intended `B` is the commutator form
`B(xZ, yZ) = ⁅x,y⁆ ∈ Z ≅ 𝔽₂`; the field only constrains `B` through
`hBnondeg` and `isotropicImage`. Here `B` is taken to be the coordinate
symplectic form of a basis of the plane `V = D₄/Z`. This is no loss: on a
`2`-dimensional `𝔽₂`-space the alternating bilinear forms are a
`1`-dimensional space and the only nonzero scalar is `1`, so the nondegenerate
alternating form is unique — the form built here *is* the commutator form read
in these coordinates. Both properties actually used downstream are proved:
`D4B_self` (alternating) and `D4B_nondeg`. -/

section D4

open DihedralGroup QuotientGroup

/-- `D₄`, the dihedral group of order `8`: the `+`-type extraspecial 2-group
`2^{1+2}_+` of rank `n = 1`. -/
abbrev D4 : Type := DihedralGroup 4

/-- The centre `Z(D₄) = {1, r²}`, of order `2`; it is also `D₄'` and `Φ(D₄)`. -/
abbrev D4Z : Subgroup D4 := Subgroup.center D4

/-- `|D₄| = 8`. -/
lemma card_D4 : Nat.card D4 = 8 := by rw [Nat.card_eq_fintype_card, DihedralGroup.card]

/-- `|Z(D₄)| = 2` — the `hZcard` field of `ExtraspecialData`, kernel-decided. -/
lemma card_D4Z : Nat.card D4Z = 2 := by rw [Nat.card_eq_fintype_card]; decide

/-- `D₄/Z(D₄)` is commutative (`D₄` has nilpotency class `2`), so the quotient
is an elementary abelian `2`-group; kernel-decided on the `64` pairs. -/
instance instD4QuotCommGroup : CommGroup (D4 ⧸ D4Z) :=
  { (inferInstance : Group (D4 ⧸ D4Z)) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have h : ∀ x y : D4, (x * y)⁻¹ * (y * x) ∈ D4Z := by decide
          exact h a b }

/-- The plane `V = D₄/Z(D₄)`, written additively. -/
abbrev D4V : Type := Additive (D4 ⧸ D4Z)

/-- Every element of `V = D₄/Z` has order dividing `2`: squares of `D₄` lie in
the centre. This is what makes `V` an `𝔽₂`-vector space. -/
lemma two_nsmul_D4V (x : D4V) : (2 : ℕ) • x = 0 := by
  apply Additive.toMul.injective
  show (Additive.toMul x) ^ (2 : ℕ) = 1
  induction (Additive.toMul x) using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have h : ∀ y : D4, y ^ 2 ∈ D4Z := by decide
    exact h a

/-- The `𝔽₂`-module structure on `V = D₄/Z`. -/
noncomputable instance instD4VModule : Module (ZMod 2) D4V :=
  AddCommGroup.zmodModule two_nsmul_D4V

instance instD4VFinite : _root_.Finite D4V := by
  show _root_.Finite (Additive (D4 ⧸ D4Z))
  infer_instance

noncomputable instance instD4VFiniteDimensional : FiniteDimensional (ZMod 2) D4V :=
  Module.Finite.of_finite

/-- `|V| = |D₄| / |Z(D₄)| = 4`. -/
lemma card_D4V : Nat.card D4V = 4 := by
  have hlag := D4Z.card_eq_card_quotient_mul_card_subgroup
  rw [card_D4, card_D4Z] at hlag
  have hV : Nat.card D4V = Nat.card (D4 ⧸ D4Z) := Nat.card_congr (Additive.ofMul.symm)
  omega

/-- `dim_{𝔽₂} V = 2 = 2n` at `n = 1` — the `hdimV` field. -/
lemma finrank_D4V : finrank (ZMod 2) D4V = 2 * 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := FiniteField.pow_finrank_eq_natCard 2 D4V
  rw [card_D4V] at hp
  have h : (2 : ℕ) ^ finrank (ZMod 2) D4V = 2 ^ 2 := by rw [hp]; norm_num
  have := Nat.pow_right_injective (le_refl 2) h
  omega

/-- A basis of the plane `V = D₄/Z`. -/
noncomputable def D4basis : Basis (Fin 2) (ZMod 2) D4V :=
  Module.finBasisOfFinrankEq (ZMod 2) D4V (by rw [finrank_D4V])

/-- The symplectic form on `V`, in the coordinates of `D4basis`:
`B(x, y) = x₀y₁ + x₁y₀`. On a `2`-dimensional `𝔽₂`-space this is the unique
nondegenerate alternating form, hence the commutator form of `D₄` read in
these coordinates. -/
noncomputable def D4B : LinearMap.BilinForm (ZMod 2) D4V :=
  (LinearMap.mul (ZMod 2) (ZMod 2)).compl₁₂ (D4basis.coord 0) (D4basis.coord 1)
    + (LinearMap.mul (ZMod 2) (ZMod 2)).compl₁₂ (D4basis.coord 1) (D4basis.coord 0)

/-- Coordinate formula for `D4B`. -/
lemma D4B_apply (x y : D4V) :
    D4B x y = D4basis.coord 0 x * D4basis.coord 1 y
      + D4basis.coord 1 x * D4basis.coord 0 y := rfl

/-- `D4B` is alternating: `B(x, x) = 0`. Hence every subspace of dimension
`≤ 1` is totally isotropic. -/
lemma D4B_self (x : D4V) : D4B x x = 0 := by
  rw [D4B_apply]
  have h : ∀ a b : ZMod 2, a * b + b * a = 0 := by decide
  exact h _ _

/-- `D4B` is symmetric (in characteristic `2`, alternating implies symmetric). -/
lemma D4B_symm (x y : D4V) : D4B x y = D4B y x := by
  rw [D4B_apply, D4B_apply]; ring

/-- Left-separation for `D4B`: probing at the two basis vectors reads off both
coordinates. -/
lemma D4B_separatingLeft : ∀ x : D4V, (∀ y, D4B x y = 0) → x = 0 := by
  intro x hx
  have h0 := hx (D4basis 1)
  have h1 := hx (D4basis 0)
  rw [D4B_apply] at h0 h1
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply] at h0 h1
  norm_num at h0 h1
  refine D4basis.ext_elem fun i => ?_
  rw [map_zero]
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- `D4B` is nondegenerate — the `hBnondeg` field. -/
lemma D4B_nondeg : D4B.Nondegenerate :=
  ⟨D4B_separatingLeft,
    fun y hy => D4B_separatingLeft y fun x => (D4B_symm y x).trans (hy x)⟩

/-- **Fact 1 at `D₄`.** A subgroup meeting the centre trivially has order at
most `2 = 2^n`. Proof: such an `H` misses `r² = (r¹)²`, so it is neither the
whole group (index `1`) nor of index `2` (index-`2` subgroups contain every
square); with `|H| · [D₄ : H] = 8` this forces `|H| ≤ 2`. -/
lemma card_le_two_of_disjoint_D4Z {H : Subgroup D4} (hH : Disjoint H D4Z) :
    Nat.card H ≤ 2 := by
  have hr2 : (r 2 : D4) ∈ D4Z := by decide
  have hr2ne : (r 2 : D4) ≠ 1 := by decide
  have hnot : (r 2 : D4) ∉ H := fun hm => hr2ne (Subgroup.disjoint_def.mp hH hm hr2)
  have hidx1 : H.index ≠ 1 := fun h =>
    hnot (Subgroup.index_eq_one.mp h ▸ Subgroup.mem_top (r 2))
  have hidx2 : H.index ≠ 2 := by
    intro h
    have hsq : (r 1 : D4) * r 1 ∈ H := Subgroup.mul_self_mem_of_index_two h (r 1)
    have hval : (r 1 : D4) * r 1 = r 2 := by decide
    exact hnot (hval ▸ hsq)
  have hcard := H.card_mul_index
  rw [card_D4] at hcard
  by_contra hc
  have hgt : 3 ≤ Nat.card ↥H := by omega
  have hi : H.index ≤ 2 := by
    by_contra hi'
    have hi3 : 3 ≤ H.index := by omega
    have h9 : 3 * 3 ≤ Nat.card ↥H * H.index := Nat.mul_le_mul hgt hi3
    omega
  rcases (show H.index = 0 ∨ H.index = 1 ∨ H.index = 2 by omega) with h | h | h
  · rw [h] at hcard; omega
  · exact hidx1 h
  · exact hidx2 h

/-- The `isotropicImage` field at `D₄`: a subgroup disjoint from the centre has
order `1` or `2` (`card_le_two_of_disjoint_D4Z`), matched by `⊥` resp. a line,
both totally isotropic because `D4B` is alternating. -/
lemma exists_isotropic_of_disjoint_D4Z {H : Subgroup D4} (hH : Disjoint H D4Z) :
    ∃ W : Submodule (ZMod 2) D4V, W ≤ D4B.orthogonal W ∧ Nat.card H = Nat.card W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := card_le_two_of_disjoint_D4Z hH
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  rcases (show Nat.card ↥H = 1 ∨ Nat.card ↥H = 2 by omega) with h1 | h2
  · exact ⟨⊥, bot_le, by rw [h1]; exact Nat.card_unique.symm⟩
  · refine ⟨Submodule.span (ZMod 2) {D4basis 0}, ?_, ?_⟩
    · intro m hm
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hm
      simp only [map_smul, LinearMap.smul_apply, D4B_self, smul_zero]
    · have hne : D4basis 0 ≠ 0 := D4basis.ne_zero 0
      have hfr : finrank (ZMod 2) (Submodule.span (ZMod 2) {D4basis 0}) = 1 :=
        finrank_span_singleton hne
      have hc := FiniteField.pow_finrank_eq_natCard 2
        (Submodule.span (ZMod 2) {D4basis 0})
      rw [hfr] at hc
      rw [h2, ← hc]
      norm_num

/-- The `corr` field at `D₄`: the correspondence theorem
(`QuotientGroup.comapMk'OrderIso`) followed by the two type-level
identifications `Subgroup (D₄/Z) ≃o AddSubgroup V ≃o Submodule 𝔽₂ V`. -/
noncomputable def D4corr : { H : Subgroup D4 // D4Z ≤ H } ≃ Submodule (ZMod 2) D4V :=
  (QuotientGroup.comapMk'OrderIso D4Z).symm.toEquiv.trans
    ((Subgroup.toAddSubgroup : Subgroup (D4 ⧸ D4Z) ≃o AddSubgroup D4V).toEquiv.trans
      (AddSubgroup.toZModSubmodule 2).toEquiv)

/-- Order bookkeeping for the correspondence: for `Z ≤ H` the projection
`H → D₄/Z` has image `H/Z` and kernel `Z` of order `2`, so `|H| = 2·|H/Z|`. -/
lemma card_eq_two_mul_card_map_mk' {H : Subgroup D4} (hH : D4Z ≤ H) :
    Nat.card ↥H = 2 * Nat.card ↥(Subgroup.map (QuotientGroup.mk' D4Z) H) := by
  let f : H →* D4 ⧸ D4Z := (QuotientGroup.mk' D4Z).comp H.subtype
  have hker : f.ker = D4Z.subgroupOf H := by
    show ((QuotientGroup.mk' D4Z).comp H.subtype).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : f.range = Subgroup.map (QuotientGroup.mk' D4Z) H := by
    show ((QuotientGroup.mk' D4Z).comp H.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hlag := (f.ker).card_eq_card_quotient_mul_card_subgroup
  have hq : Nat.card (↥H ⧸ f.ker) = Nat.card ↥(f.range) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hk : Nat.card ↥(f.ker) = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv]
    exact card_D4Z
  rw [hlag, hq, hk, hrange, Nat.mul_comm]

/-- The `corr_card` field at `D₄`. -/
lemma D4corr_card (H : { H : Subgroup D4 // D4Z ≤ H }) :
    Nat.card (H : Subgroup D4) = 2 * Nat.card (D4corr H) :=
  card_eq_two_mul_card_map_mk' H.2

/-- **The rank-`1` witness.** `D₄ = DihedralGroup 4`, of order `8 = 2^{1+2·1}`,
carries `ExtraspecialData` with `n = 1`, `Z = Z(D₄)` of order `2`, and
`V = D₄/Z` the `𝔽₂`-plane. Every consequence proved above —
`card_le_of_disjoint_center`, `center_le_of_card_ge`, `upperSubgroupEquiv`,
`subgroupCount_eq_fixedDim`, `subgroupCount_eq_of_same_rank` — is therefore a
statement about a nonempty hypothesis class, not a conditional with no known
model. -/
noncomputable def extraspecialD4 : ExtraspecialData D4 where
  n := 1
  Z := D4Z
  hZcard := card_D4Z
  V := D4V
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFinite := inferInstance
  hdimV := finrank_D4V
  B := D4B
  hBnondeg := D4B_nondeg
  isotropicImage := fun _ hH => exists_isotropic_of_disjoint_D4Z hH
  corr := D4corr
  corr_card := D4corr_card

/-- The witness has rank `1`, as intended (not the degenerate `n = 0`). -/
lemma extraspecialD4_n : extraspecialD4.n = 1 := rfl

/-- Instantiation of the main theorem at the witness: for `k ≥ 2` the count of
order-`2^k` subgroups of `D₄` is the number of `(k-1)`-dimensional subspaces of
the `𝔽₂`-plane — `3` lines at `k = 2` (the three subgroups of order `4`) and
`1` at `k = 3`. -/
lemma subgroupCount_D4_eq_fixedDim {k : ℕ} (hk : 2 ≤ k) :
    subgroupCount D4 k = Nat.card (fixedDimSubspaces (ZMod 2) D4V (k - 1)) :=
  subgroupCount_eq_fixedDim extraspecialD4 hk

end D4

end ExtraspecialLattice
