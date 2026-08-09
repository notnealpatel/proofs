import GroupTPP.MonomialRealization

/-!
# P1 conjecture sweep: monomial realizations beyond no-cancellation

Conjecture candidates extending `GroupTPP.MonomialRealization`. Every statement is
`sorry`-stubbed; a later stage elaborates and attacks them. None restates an
existing lemma in `Xlib/`: the module proves semantic ⟹ coefficient,
no-cancellation, diagonal identities, and Kronecker closure — the statements
below are converses, rigidity/classification results, closure under a
different operation (cyclic rotation), and quantitative bounds, all absent
from the module.

All pattern checks here are coefficient-level hand derivations from
`coeff_identity` / `diagonal_coeff` / `no_cancellation`; the one Sage
spot-check performed (small-group TPP-to-realization roundtrip) is noted at
`p1_c8`.
-/

namespace GroupTPP.MonomialRealization

open GroupTPP.TPP Finset

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}
variable {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
variable {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}

/-- (a) The deliberately-unformalized converse: the coefficient-level identity
already implies the full semantic trilinear identity, by multilinear expansion
of `Phi` over the sextuple index sum — the summand coefficient
`α·β·γ·[abc=1]` is exactly the Kronecker delta by `coeff_identity`.
(b) [theory]
(c) Self-contained; no unproved dependencies. -/
theorem p1_c1 (h : IsMonomialRealization a b c α β γ) :
    IsSemanticMonomialRealization a b c α β γ := sorry

/-- (a) Closure under an operation other than Kronecker product: cyclic
rotation. `bca = 1 ↔ abc = 1` by cyclicity, and `F` is commutative, so the
rotated data realize `⟨m, p, n⟩` matmul over the same group.
(b) [theory]
(c) Self-contained. -/
theorem p1_c2 (h : IsMonomialRealization a b c α β γ) :
    IsMonomialRealization b c a β γ α := sorry

/-- (a) Hidden injectivity: the index maps are injective as maps on index
pairs — a collision `a i j = a i' j'` propagates through a diagonal identity
into an off-diagonal group collision, killed by no-cancellation. Not stated
anywhere in the module.
(b) [theory]
(c) Self-contained. -/
theorem p1_c3 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    Function.Injective (fun q : Fin n × Fin m => a q.1 q.2) ∧
    Function.Injective (fun q : Fin m × Fin p => b q.1 q.2) ∧
    Function.Injective (fun q : Fin p × Fin n => c q.1 q.2) := sorry

/-- (a) Quantitative consequence of `p1_c3`: a monomial realization of
`⟨n, m, p⟩` needs a group of size at least `max(nm, mp, pn)`.
(b) [theory]
(c) Follows from `p1_c3` (conjectural but hand-derived); stated separately so
it survives even if only one injectivity conjunct holds. -/
theorem p1_c4 [Fintype G] (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    n * m ≤ Fintype.card G ∧ m * p ≤ Fintype.card G ∧ p * n ≤ Fintype.card G :=
  sorry

/-- (a) Scalar rigidity: the coefficient matrices are multiplicatively rank
one — every 2×2 "minor" is balanced. Derivation: `diagonal_coeff` gives
`α i j = (β j k · γ k i)⁻¹` for every `k`, and the cross-ratio cancels.
A quantitative refinement absent from the module (which only proves the
diagonal product identity).
(b) [theory]
(c) Self-contained. -/
theorem p1_c5 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    (∀ i i' j j', α i j * α i' j' = α i j' * α i' j) ∧
    (∀ j j' k k', β j k * β j' k' = β j k' * β j' k) ∧
    (∀ k k' i i', γ k i * γ k' i' = γ k i' * γ k' i) := sorry

/-- (a) Structural classification (gauge normal form): the index maps of any
monomial realization factor through three one-variable maps,
`a = s·t⁻¹`, `b = t·u⁻¹`, `c = u·s⁻¹`. This is the group-valued rank-one
analogue of `p1_c5`, extracted from the diagonal identities; it is the exact
shape of the Cohn–Umans TPP construction, recovered here as forced rather
than chosen.
(b) [theory]
(c) Self-contained. -/
theorem p1_c6 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    ∃ (s : Fin n → G) (t : Fin m → G) (u : Fin p → G),
      (∀ i j, a i j = s i * (t j)⁻¹) ∧
      (∀ j k, b j k = t j * (u k)⁻¹) ∧
      (∀ k i, c k i = u k * (s i)⁻¹) := sorry

/-- (a) Bridge to the honest `TripleProductProperty` (not the false subgroup
bridge flagged in the module docstring): given the normal form of `p1_c6`,
the three one-variable images form a genuine TPP triple in the left-quotient
sense — the TPP hypothesis rearranges cyclically into exactly one
`no_cancellation` instance. Works over any group, no commutativity.
(b) [theory]
(c) Self-contained given the factorization hypotheses (which `p1_c6`
conjectures always exist). -/
theorem p1_c7 [Fintype G] (h : IsMonomialRealization a b c α β γ)
    (s : Fin n → G) (t : Fin m → G) (u : Fin p → G)
    (ha : ∀ i j, a i j = s i * (t j)⁻¹)
    (hb : ∀ j k, b j k = t j * (u k)⁻¹)
    (hc : ∀ k i, c k i = u k * (s i)⁻¹) :
    TripleProductProperty (Finset.image s Finset.univ)
      (Finset.image t Finset.univ) (Finset.image u Finset.univ) := sorry

/-- (a) Full converse (Cohn–Umans direction, unformalized in the module):
any TPP triple with injective enumerations yields a monomial realization with
unit scalars. Together with `p1_c6`/`p1_c7` this would make monomial
realizability of `⟨n,m,p⟩` *equivalent* to the existence of a TPP triple of
sizes `n, m, p`.
(b) [theory]
(c) Self-contained. Sage spot-check (S₃, GF(5), TPP triple of sizes 2·2·1,
gauge-twisted scalars): coefficient identity, no-cancellation, and TPP on
images all verified. Exhaustive small-group sweep skipped for time per sweep
constraint. -/
theorem p1_c8 [Fintype G] {S T U : Finset G} (hTPP : TripleProductProperty S T U)
    (s : Fin n → G) (t : Fin m → G) (u : Fin p → G)
    (hs : Function.Injective s) (ht : Function.Injective t)
    (hu : Function.Injective u)
    (hsS : ∀ i, s i ∈ S) (htT : ∀ j, t j ∈ T) (huU : ∀ k, u k ∈ U) :
    IsMonomialRealization (F := F)
      (fun i j => s i * (t j)⁻¹)
      (fun j k => t j * (u k)⁻¹)
      (fun k i => u k * (s i)⁻¹)
      (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) := sorry

/-- (a) Capacity bound: chaining `p1_c3` (sizes), `p1_c6` (normal form), and
`p1_c7` (TPP on images) through `le_tppCapacity` bounds the realizable matmul
volume by the TPP capacity `β(G)`. For commutative `G` this specializes via
`tppCapacity_eq_card` to `n·m·p ≤ |G|` — a strictly stronger abelian bound
than `p1_c4`.
(b) [theory]
(c) Leans on the conjectural chain `p1_c3` → `p1_c6` → `p1_c7`; all three are
hand-derived but unproved. -/
theorem p1_c9 [Fintype G] (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (h : IsMonomialRealization a b c α β γ) :
    n * m * p ≤ tppCapacity G := sorry

/-- (a) Gauge classification of scalars (basis-dependence): two monomial
realizations sharing the same index maps differ exactly by a diagonal gauge
`(u, v, w)` telescoping around the triangle — the scalar data is unique up to
this action. The forward closure (gauging preserves realization) is easy;
the content is that the gauge orbit is the *whole* fiber over the index maps.
(b) [theory]
(c) Uses the rank-one mechanism of `p1_c5` in its derivation, but the
statement is independent. -/
theorem p1_c10 (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    {α' : Fin n → Fin m → F} {β' : Fin m → Fin p → F} {γ' : Fin p → Fin n → F}
    (h : IsMonomialRealization a b c α β γ)
    (h' : IsMonomialRealization a b c α' β' γ') :
    ∃ (u : Fin n → F) (v : Fin m → F) (w : Fin p → F),
      (∀ i j, α' i j = α i j * u i * v j) ∧
      (∀ j k, β' j k = β j k * (v j)⁻¹ * w k) ∧
      (∀ k i, γ' k i = γ k i * (w k)⁻¹ * (u i)⁻¹) := sorry

end GroupTPP.MonomialRealization
