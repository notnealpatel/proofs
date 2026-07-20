import Xlib.IsoclinismInvariants
import Xlib.CharDegrees
import Xlib.CharDegreesMul
import Xlib.STPPWreath

/-!
# P3 conjecture sweep: isoclinism invariants × character-degree data

Calibration sweep (pair P3, theory track). NEW conjecture statements connecting
`Xlib.IsoclinismInvariants` (Hall isoclinism, `k(G)`, `n_c(G)`) with
`Xlib.CharDegrees` (`charDegrees`, `Dᵣ`, `n(G)`) and the wreath/STPP lane.

## Sorry census (2026-07-19, this sweep)

* `Xlib/IsoclinismInvariants.lean` — **0 code sorries** (all grep hits are
  doc-comment mentions). PROVED foundation.
* `Xlib/CharDegrees.lean` — **0 code sorries**; its imports `Xlib.TPP`,
  `Xlib.Wedderburn`, `Xlib.GroupAlgebraCenter` — **0 code sorries**. PROVED
  foundation. (The `WreathNg` docstring's claim of a "single foundational
  `sorry` of `Xlib.CharDegrees`" is STALE: the indexed Wedderburn layer is now
  sorry-free.)
* `Xlib/CharDegreesMul.lean` — 0 code sorries.
* `Xlib/STPPWreath.lean` — exactly 2 code sorries: `stpp_capacity_le` (l.389)
  and `stpp_capacity_le_of_wreath` (l.939, hence also `stpp_capacity_le_comm`
  which invokes it). The *definitions* used below (`ImprimitiveWreathProduct`,
  `permArrowHom`) are sorry-free.

The dispatch premise "BOTH modules contain sorries" is FALSE per this census;
every statement below therefore sits on **proved** definitions unless noted.

## Computational evidence

GAP/Sage runs recorded in the sweep scratchpad (`p3_checks.sage`, each phase
< 60 s):

* `|(H ≀ S_n)'| = |H|^(n-1) · |H'| · (n!/2)` for
  `H ∈ {C₂,S₃,C₄,D₈,Q₈,C₆} (n=2)`, `{C₂,S₃} (n=3)`, `{C₂} (n=4)`; and
  `|Z(H ≀ S₂)| = |Z(H)|` on all six.
* `D_x(H ≀ S_m) ≤ (m!)^(x-1) · D_x(H)^m` for nonabelian
  `H ∈ {S₃, D₈, Q₈, A₄}`, `m ∈ {2,3}`, `x ∈ {2, 2.372, 2.5, 3}`
  (equality at `x = 2`); the inequality REVERSES for `x ∈ {0.5, 1, 1.5}`.
* All 51 groups of order 32, bucketed by the coarse isoclinism signature
  `(G/Z ≅, G' ≅)`: no bucket contains two distinct degree multisets.
* `n(G × C_k) = n(G)` for `G ∈ {S₃, SL(2,3)}`, `k ∈ {2,3}`.
-/

open Xlib.CharDegrees Xlib.CharDegreesMul Xlib.TPP Xlib.STPPWreath
open IsoclinismInvariants

namespace Scratch.Sweep.P3

universe u v w

/- ────────────────────────────────────────────────────────────────────────────
### Block I: character-degree data across a general isoclinism
──────────────────────────────────────────────────────────────────────────── -/

/-- (a) Isoclinic groups have PROPORTIONAL character-degree multiplicities: the
multiplicity of each degree `d`, normalized by group order, is an isoclinism
invariant. Generalizes the canonical case (`charDegrees (G × A)` = `|A|` copies
of `charDegrees G`, via `CharDegreesMul.charDegrees_prod`) to arbitrary Hall
isoclinisms; consistent with all order-32 coarse families and all same-order
isoclinic classics (`D₈ ~ Q₈`; `D₁₆ ~ QD₁₆ ~ Q₁₆`; extraspecial `p³`) checked
in GAP.
(b) [theory]
(c) FOUNDATION: proved (`IsoclinismInvariants.Isoclinic`, `charDegrees` both
sorry-free).
GAP-checkable: needs an isoclinism tester (compare across P. Hall families,
e.g. all orders ≤ 64 crossed with `G × C_k` paddings). -/
theorem p3_c1 {G : Type u} {H : Type v} [Group G] [Group H]
    [Fintype G] [Fintype H] (h : Isoclinic G H) (d : ℕ) :
    (charDegrees G).count d * Fintype.card H
      = (charDegrees H).count d * Fintype.card G := sorry

/-- (a) The BCCGU barrier quantity `n(G)` (minimal nontrivial irrep degree) is a
full isoclinism invariant — so the `n(G) ≥ 2`-type barriers to `ω = 2` via any
group transfer across its entire isoclinism family. Weaker than `p3_c1` (which
implies it) but independently attackable. Verified on `D₈ ~ Q₈` (both `n = 2`),
`D₁₆ ~ QD₁₆ ~ Q₁₆` (all `n = 2`), extraspecial `p³` pairs (`n = p`), and
`G ~ G × C_k` paddings.
(b) [theory]
(c) FOUNDATION: proved.
GAP-checkable (same harness as `p3_c1`). -/
theorem p3_c2 {G : Type u} {H : Type v} [Group G] [Group H]
    [Fintype G] [Fintype H] (h : Isoclinic G H) :
    minNontrivIrrepDim G = minNontrivIrrepDim H := sorry

/-- (a) The γ-relevant power sums transfer across an isoclinism with the exact
order ratio: `D_x(G)/|G|` is an isoclinism invariant for EVERY real exponent
`x`. This is the character-degree analogue of the file's own
`ratio_isoclinism_invariant_prod` (`k/|Z|` invariance): at `x = 0` it recovers
`k(G)/|G|` invariance via `charDegreeSum_zero_eq_card_conjClasses`, at `x = 2`
it is trivial (`D₂ = |G|`), and at `x = ω` it says isoclinism padding moves the
CU right-hand side `D_ω` exactly linearly in the order.
(b) [theory]
(c) FOUNDATION: proved.
GAP-checkable at rational sample exponents. -/
theorem p3_c3 {G : Type u} {H : Type v} [Group G] [Group H]
    [Fintype G] [Fintype H] (h : Isoclinic G H) (x : ℝ) :
    charDegreeSumReal G x * (Fintype.card H : ℝ)
      = charDegreeSumReal H x * (Fintype.card G : ℝ) := sorry

/-- (a) Canonical-isoclinism instance of `p3_c2`, isolated because it has a
concrete proof route inside the repo: `CharDegreesMul.charDegrees_prod` +
`charDegrees` of abelian `A` being all-ones should give
`charDegrees (G × A) = |A| • charDegrees G` up to `bind` bookkeeping, and the
`> 1` filter then has the same `toFinset.min`. A sanity anchor for the block:
if THIS fails, `p3_c1`/`p3_c2` die with it.
(b) [theory]
(c) FOUNDATION: proved.
Checked in GAP: `G ∈ {S₃, SL(2,3)}`, `A ∈ {C₂, C₃}`. -/
theorem p3_c4 {G : Type u} [Group G] [Fintype G]
    {A : Type w} [CommGroup A] [Fintype A] :
    minNontrivIrrepDim (G × A) = minNontrivIrrepDim G := sorry

/-- (a) The multiplicity of degree `1` in `charDegrees` is the order of the
abelianization: linear characters = characters of `G/G'`. This is the plank
that ties `charDegrees` directly to the commutator subgroup — one half of the
isoclinism datum `(G/Z, G', cmap)` — and the normalization that makes `p3_c1`
consistent (`|(G × A)ᵃᵇ| = |A| · |Gᵃᵇ|` matches the count scaling). Absent from
`Xlib` and Mathlib per grep.
(b) [theory]
(c) FOUNDATION: proved.
GAP-checkable trivially (`LinearCharacters` vs `G/DerivedSubgroup`). -/
theorem p3_c5 {G : Type u} [Group G] [Fintype G] :
    (charDegrees G).count 1 = Nat.card (G ⧸ commutator G) := sorry

/-- (a) Cross-module zero-locus bridge: the barrier quantity `n(G)` vanishes iff
the non-central class count `n_c(G)` vanishes (both detect abelianness, but
neither module states either equivalence, and the statement mentions
commutativity nowhere). Nontrivial witnesses on both sides: any abelian `G`
(both `0`) and any nonabelian `G` (both positive, via
`nc_pos_of_not_commutative` and `BCGPUBarrier.two_le_minNontrivIrrepDim`).
(b) [theory]
(c) FOUNDATION: proved.
GAP-checkable trivially. -/
theorem p3_c6 {G : Type u} [Group G] [Fintype G] :
    minNontrivIrrepDim G = 0 ↔ nc G = 0 := sorry

/- ────────────────────────────────────────────────────────────────────────────
### Block II: isoclinism data of the wreath construction (the live lane)
──────────────────────────────────────────────────────────────────────────── -/

/-- (a) The commutator-subgroup order of the imprimitive wreath product:
`|(D ≀ Sₙ)'| = |D|^(n-1) · |D'| · (n!/2)` for `n ≥ 2` — the base part is the
"product-in-`D'`" subgroup of `Dⁿ` (order `|D|^(n-1)·|D'|`), the top part is
`Aₙ`. This is one half of the isoclinism datum of the CU wreath family and the
quantitative engine behind `p3_c8`. Verified in GAP for six base groups at
`n = 2`, two at `n = 3`, one at `n = 4` (exact match in all nine cases).
(b) [theory]
(c) FOUNDATION: proved (`ImprimitiveWreathProduct` and its `card` are
sorry-free; unrelated to the two `STPPWreath` capacity sorries).
GAP-checkable for many more `(D, n)`. -/
theorem p3_c7 {D : Type u} [Group D] [Fintype D] [DecidableEq D]
    {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (commutator (ImprimitiveWreathProduct D n))
      = Nat.card D ^ (n - 1) * Nat.card (commutator D) * (n.factorial / 2) :=
  sorry

/-- (a) Isoclinism padding does NOT commute with the wreath construction: `G` is
isoclinic to `G × A` (`isoclinic_prod_abelian`), yet `G ≀ S₂` is NOT isoclinic
to `(G × A) ≀ S₂` for any nontrivial finite abelian `A` — by `p3_c7` the
commutator subgroups have orders `|G|·|G'|` vs `|G|·|A|·|G'|`, so no
`ψ : W₁' ≃* W₂'` can exist. Consequence for the STPP lane: the wreath capacity
chain is sensitive to the isoclinism representative of the base, so
α/γ-optimization over an isoclinism family must happen BEFORE wreathing.
(b) [theory]
(c) FOUNDATION: proved.
GAP-checkable via commutator orders (no isoclinism tester needed). -/
theorem p3_c8 {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {A : Type w} [CommGroup A] [Fintype A] [DecidableEq A]
    (hA : 1 < Nat.card A) :
    ¬ Isoclinic (ImprimitiveWreathProduct G 2)
        (ImprimitiveWreathProduct (G × A) 2) := sorry

/-- (a) The nonabelian wreath `D_x` bound — the general-`H` form of the
`hbound` hypothesis that `stpp_capacity_le_of_wreath` (one of the two live
sorries) consumes, currently proved in `STPPWreath` only for `CommGroup H`
(`wreath_charDegree_bound`). Verified in GAP for nonabelian
`H ∈ {S₃, D₈, Q₈, A₄}`, `m ∈ {2,3}`, `x ∈ {2, 2.372, 2.5, 3}`, with equality at
`x = 2` (both sides `= |H ≀ Sₘ|`). The hypothesis `2 ≤ x` is SHARP: the
inequality reverses at `x ∈ {0.5, 1, 1.5}` in every tested case. Extrapolation
flag: only `m ≤ 3` and `x ≤ 3` were computed.
(b) [theory]
(c) FOUNDATION: proved definitions; NOTE this statement is the missing plank
for the sorried `stpp_capacity_le_of_wreath`/`stpp_capacity_le`, so proving it
would discharge part of a sorried foundation rather than sit on one.
GAP-checkable for larger `m` (cost grows fast; keep runs < 60 s). -/
theorem p3_c9 {H : Type u} [Group H] [Fintype H] [DecidableEq H]
    {m : ℕ} {x : ℝ} (hx : 2 ≤ x) :
    charDegreeSumReal (ImprimitiveWreathProduct H m) x
      ≤ (Nat.factorial m : ℝ) ^ (x - 1) * (charDegreeSumReal H x) ^ m := sorry

/- ────────────────────────────────────────────────────────────────────────────
### Block III: TPP capacity across the canonical isoclinism
──────────────────────────────────────────────────────────────────────────── -/

/-- (a) TPP capacity transfer across the canonical isoclinism `G ~ G × A`:
padding by an abelian factor multiplies the capacity by AT LEAST `|A|`
(pad one TPP slot: `(S, T, U) ↦ (S ×ˢ univ, T × {1}, U × {1})`; the `A`-strand
of the quotient equation collapses on its own). Paired with `p3_c3` at `x = ω`
(where `D_ω` scales EXACTLY by `|A|`) this says the CU inequality's slack
`D_ω(G) - β(G)^(ω/3)`-side strictly reorganizes across an isoclinism family —
the family is not α-flat even though it is `k/|Z|`-flat. Nontrivial witness:
`G = S₃`, `A = C₂` (`β(S₃) ≥ 6·|A|` beats the trivial `card` bound on
`S₃ × C₂` only via the padding argument... verified consistent with
`tppCapacity_eq_card` on abelian instances).
(b) [theory]
(c) FOUNDATION: proved (`Xlib.TPP` is sorry-free).
Computationally checkable for tiny `G` only (`tppCapacity` is a sup over all
triple powersets; keep runs < 60 s — full check skipped for time). -/
theorem p3_c10 {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {A : Type w} [CommGroup A] [Fintype A] [DecidableEq A] :
    tppCapacity G * Fintype.card A ≤ tppCapacity (G × A) := sorry

end Scratch.Sweep.P3
