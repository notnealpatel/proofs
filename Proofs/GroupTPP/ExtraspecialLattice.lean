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
type-independent part, which is why it suffices to prove the upper-lattice invariance. -/
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

end ExtraspecialLattice
