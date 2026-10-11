# Same-side axial ellipse theorem

## Scope, original geometry, and status

`Erdos132.AxialEllipse.same_side_axial_ellipse` is the full universal consumer for the **same-side axial** case. It quantifies over every natural `n` with `8 ≤ n`, every finite set `H` of `n - 2` actual points in `Plane = EuclideanSpace ℝ (Fin 2)`, and real parameters `a,b,c₁,c₂`. The joint hypotheses are:

* `0 < b < a`;
* every `p ∈ H` satisfies the ordinary Cartesian ellipse equation `p₀²/a² + p₁²/b² = 1`;
* `(c₁,0)` and `(c₂,0)` belong to the **ambient interior** of `convexHull ℝ H`;
* `c₁ ≠ c₂` and `0 < c₁*c₂`;
* `(a²-b²)/a ≤ |c₁|` and `(a²-b²)/a ≤ |c₂|` (inclusive).

For `X = insert (c₁,0) (insert (c₂,0) H)`, it proves `X.card = n` and

```text
∃ d : ℝ, 0 < d ∧ d < Metric.diam X ∧ 1 ≤ multiplicity X d ∧ multiplicity X d ≤ n.
```

The diameter uses the canonical Euclidean metric, and multiplicity counts actual loop-free unordered pairs. `TwoInteriorCircle.pairs X` is `X.offDiag.image Sym2.mk.uncurry`; `pairDist` descends ordinary distance to `Sym2`, and `multiplicity X d` filters these pairs at distance `d`. It counts each unordered distinct-endpoint pair once, not each orientation and not each coordinate or distance-support value. A finset enforces distinct hull points. Interior is ambient, not relative interior. Natural subtraction in `H.card = n - 2` is guarded by `8 ≤ n`. All ellipse denominators in geometric theorems are nonzero because `0 < b < a`.

No proposed-distance, radial-saturation, common-support, unique-diameter, reflection, symmetry, or affine-metric hypothesis was added to the consumer. There is no affine transformation of ordinary distances to a circle. Extreme-point assumptions are unnecessary here: the proved ellipse supporting-functional lemma excludes every ellipse point from the ambient hull interior. This is the original Euclidean conditional implication within the assigned canonical-axis same-side scope.

The full module and simultaneous fixture have compiled. A fresh imported **local** signature/axiom audit covered all 16 public declarations and reported only `propext`, `Classical.choice`, and `Quot.sound`. The parent's independent statement/semantic review and fresh axiom gate remain separate; these results are not a claim that the parent gates or campaign adoption are complete.

## Proof and exact bridge to the consumer

Write

```text
F_c(x) = (1-b²/a²)x² - 2cx + b² + c².
```

1. `coordinate_mem_Icc` proves `-a ≤ p₀ ≤ a` on the actual ellipse. `dist_sq_eq_radialSquare` proves `dist p (c,0)² = F_c(p₀)` using the Euclidean norm-square formula and the ellipse equation.
2. The factorization
   `F_c(y)-F_c(x) = (y-x)((1-b²/a²)(x+y)-2c)`
   proves strict decrease on `[-a,a]` when `(a²-b²)/a ≤ c`, and strict increase when `c ≤ -(a²-b²)/a`. Equality at the threshold is included: for distinct `x < y`, the sum is strictly below `2a` (or strictly above `-2a`), even though an endpoint derivative can vanish.
3. `vertical_card_le_two` proves that a fixed first coordinate yields at most two actual ellipse points, since the second coordinates have equal squares. Combining injectivity of `F_c` on the interval with this vertical bound gives `radial_card_le_two` for **ordinary distance fibers**.
4. `ellipse_not_mem_interior` uses the supporting functional `L(q)=p₀q₀/a²+p₁q₁/b²`. The ellipse equation and positivity of weighted squares show `L(q) ≤ 1` throughout the hull and `L(p)=1`. A sufficiently small dilation `(1+t)p` in an assumed interior ball has `L((1+t)p)>1`, a contradiction. Thus both interior points are new vertices, and distinctness gives `X.card=n`.
5. Under negation of the conclusion every occurring nondiameter class has at least `n+1` actual pairs. Both radial families map into the actual nondiameter set `T`, by the predecessor's strict interior-to-hull distance and unchanged-diameter lemmas. If `q=T.card`, the new radial fiber bound gives `n-2 ≤ 2q`; actual all-pair counting, reserving a diameter pair, gives `q(n+1)+1 ≤ n.choose 2`. The predecessor's checked arithmetic lemma forces `n=2(q+1)`, hence `H.card=2q` and `q≥3`.
6. The checked finite fiber-saturation lemma now forces both radial images to equal `T`. This certificate is **derived**, not assumed. Applying the square map to the equality and the ordinary-distance identity yields equal `F_c` images on the actual coordinate set `A = H.image (fun p => p₀)`.
7. `eq_on_of_strictMonoOn_image_eq` proves the finite ordered-image lemma. Choosing `T:A→A` with `f(x)=g(T(x))` makes `T` strictly increasing, so `StrictMono.eq_id` on the finite linear order gives pointwise equality. For two decreasing maps, negate both. The same-side product hypothesis ensures both radial quadratics have the same monotonic direction. Their pointwise equality factors as `(c₁-c₂)(c₁+c₂-2x)=0`; distinctness forces every first coordinate to equal `(c₁+c₂)/2`. The actual vertical-line bound gives `H.card≤2`, contradicting `H.card≥6`.

`common_support_card_le_two` is the resulting explicit intermediate implication. The named consumer discharges its equal-support premise using contrary-case counting and saturation; that premise is not unpaid upstream work. There is no remaining bridge needed for the assigned same-side axial consumer.

## Joint exact non-vacuity fixture

`fixtureHull` is exactly

```text
{ (√3, 1/2), (√3,-1/2), (-√3,1/2), (-√3,-1/2), (0,1), (0,-1) }.
```

`ellipse_fixture` jointly proves cardinality six, every ellipse equation with `a=2,b=1`, both ambient-interior memberships with `c₁=8/5,c₂=17/10`, and every arithmetic/sign/distinctness/threshold premise at `n=8`. It does not certify these at unrelated models. Positivity of `√3` proves distinctness; `√3²=3` proves the ellipse equations. The closed rectangle `[-√3,√3] × [-1/2,1/2]` lies in the hull, proved by two explicit stages of convex combination of its four actual corner points. Its open rectangle is an ambient open subset of the hull; both chosen points lie there because `17/10 < √3`. `interior_maximal` then proves the required ambient interior, not merely membership in the hull or a line segment.

An anonymous final example applies `same_side_axial_ellipse` to this **same** fixture, including `H.card=8-2`, and obtains the actual eight-point multiplicity conclusion. This also checks the consumer/fixture interface. The intended domains are not empty: `Fin 2` has two coordinates, the fixture has six actual hull points, and its interior contains an open rectangle. The fixture is exact symbolic arithmetic, not a floating-point or `native_decide` calculation. Definition checks also identify Cartesian coordinates of `point`, an actual `OnEllipse 2 1 (point 0 1)` witness, and `radialSquare 2 1 (8/5) 0 = 89/25`.

## Rational four-fiber warning — not a target counterexample

The source's warning concerns the unrestricted ellipse/circle-reuse step. Take `a=2,b=1`,

```text
H = {(0,±1), (6/5,±4/5), (2,0), (-2,0)},
z = (9/20,0), w = (0,0).
```

Here the augmented diameter is `4`, and

```text
F_(9/20)(x) = (3/4)x² - (9/10)x + 481/400.
```

The level `481/400` occurs at `x=0` and `x=6/5`, giving **four actual hull points** at one radial distance. The radial fiber sizes are `4,1,1`; although `N=6=2q_z`, this does not saturate them at two. This refutes the unrestricted two-fiber premise and the consequent naive saturation inference. The positive threshold for this ellipse is `3/2`, which `9/20` fails; also `z*w=0`, not a positive same-side product.

For completeness, the source's squared-distance multiplicities among the 28 actual augmented pairs are:

```text
1:2, 117/25:2, 16:1, 2401/400:1, 272/25:2, 32/25:2,
37/25:2, 4:3, 481/400:4, 5:4, 52/25:2, 64/25:1,
81/400:1, 961/400:1.
```

These warning values are retained from the supplied mathematical source, not represented as a new Lean-certified enumeration. Squaring preserves equality of nonnegative ordinary distances. In particular this is **not** a counterexample to the same-side theorem and **not** a full contrary model in which every global nondiameter class is large: the listed classes are already small. No inference about the target's failure is drawn from this warning.

## Boundaries and remaining scope

* Threshold equality is allowed by the strict endpoint factor argument; thresholds were not strengthened to strict inequalities.
* Either positive-positive or negative-negative axial coordinates are covered. Opposite signs give opposite monotonic directions and invalidate the order-preserving-image step; that case remains outside this theorem.
* Odd `n` is handled automatically: the contrary counting inequalities force an even size, so odd sizes already contradict that case.
* Endpoint singleton radial fibers are initially allowed. Contrary-case saturation excludes them only after the exact all-pair budget is established; no two-points-per-fiber premise was smuggled into the statement.
* Circles (`a=b`), general nonaxial points, and general ellipses without these inclusive thresholds are not claimed. A translated/rotated isometric corollary could preserve distances, but is not implemented. General affine maps do not preserve the multiplicity problem.

## Dependency provenance and public interface inventory

The mathematical input was read in full from source revision `5535c641e7af248edaf817fa2255d4492f653930`, `/tmp/Ellipse-5535c641e7af248edaf817fa2255d4492f653930.md`, SHA256
`84ec05d61ae86b740e89f472ba6cf97b1684a92b72b60715e27617f91aa4266a`.

The unchanged `Erdos.Erdos132.TwoInteriorCircle` dependency is present at assigned base `9b803530d2472c7742b66d64a1b34e440c4c60f4`. Both the base contents and the current file hash to
`d36fdcc81b8e99f149e9ca53a8d57106563e46bbf93d70ef70b395db5faaab17`.
No predecessor copy or modification was necessary. The explicit second import is `Mathlib.Order.Preorder.Finite`, for the finite strict-order endomorphism identity. The new proof uses the predecessor's genuine pair and metric infrastructure (`Plane`, `multiplicity`, `nonDiameterDistances`, `mem_nonDiameterDistances`, `mk_mem_pairs`, `diam_insert_interiors`, `dist_lt_diam_hull`, `nonDiameter_pair_budget`, `even_size_of_pair_budget`, `saturated_fibers`). It does **not** use its circle-specific `radial_card_le_two`, circle intersections, reflection certificates, or final circle theorem.

There are four new public definitions and twelve public theorems, all in `Erdos132.AxialEllipse`. The exact elaborated signatures and individual axiom lists are recorded in the appendix. The private helpers are `radial_mem_actual`, `image_eq_of_saturated`, `rectangle_subset_hull`, and `axial_mem_interior_rectangle`; their dependencies are included transitively in the public audits. No public instances are added and there are no variable sections or silently generalized parameters.

## Checks and handoff

Observed start/source-consumption time: `2026-10-11 17:47:09 UTC`. The first successful geometric consumer check returned at `17:55:09 UTC`; the exact fixture and final production consumer call subsequently compiled. The exact final source passed both direct elaboration and the production build at `18:02:05 UTC`. At `17:58:56 UTC`, the complete production-module check and imported audit had both returned successfully. This records wall-clock observations, not invented token/CPU effort.

Checks performed, all with managed positive task deadlines:

```text
timeout 180s lake -q build +Erdos.Erdos132.TwoInteriorCircle
timeout 60s lake -q build +Erdos.Erdos132.AxialEllipse
timeout 60s lake env lean -j 1 -M 4000 Proofs/Erdos/Erdos132/AxialEllipse.lean
timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/AxialAudit.lean
```

The production build and complete direct check succeeded. Only existing predecessor linter warnings were replayed by the build; the final new Lean module has no warnings or errors. The imported temporary audit used `#check @...` and `#print axioms ...` for **every** public declaration, with the exact successful output below. Audit/probe modules were disposable leaves and are removed from the final changes; nothing imports them. The local transcript is also preserved at `/tmp/axial-ellipse-audit.log`. No production `#check`, `#print`, `#eval`, `sorry`, declared axioms, `native_decide`, implementation overrides, or `partial def` are present.

The only final production additions are this Markdown file and its sibling Lean file. References, Ledger, and shared helpers remain untouched. No revision was created/described/moved and no upload/adoption occurred. External progress-file writes were not made because the runtime restricts writes to the assigned workspace; this section is the handoff record. The parent should independently inspect the full pair and run its fresh semantic/signature/axiom gates. No mathematical obligation remains open within the assigned same-side axial contract; broader cases listed above remain outside scope.

## Exact imported signature and axiom audit

```text
Erdos132.AxialEllipse.eq_on_of_strictMonoOn_image_eq : ∀ (A : Finset ℝ) (f g : ℝ → ℝ),
  StrictMonoOn f ↑A → StrictMonoOn g ↑A → Finset.image f A = Finset.image g A → ∀ x ∈ A, f x = g x
'Erdos132.AxialEllipse.eq_on_of_strictMonoOn_image_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.radialSquare : ℝ → ℝ → ℝ → ℝ → ℝ
'Erdos132.AxialEllipse.radialSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.radialSquare_strictAntiOn : ∀ (a b c : ℝ),
  0 < b → b < a → (a ^ 2 - b ^ 2) / a ≤ c → StrictAntiOn (Erdos132.AxialEllipse.radialSquare a b c) (Set.Icc (-a) a)
'Erdos132.AxialEllipse.radialSquare_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.radialSquare_strictMonoOn : ∀ (a b c : ℝ),
  0 < b → b < a → c ≤ -((a ^ 2 - b ^ 2) / a) → StrictMonoOn (Erdos132.AxialEllipse.radialSquare a b c) (Set.Icc (-a) a)
'Erdos132.AxialEllipse.radialSquare_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.point : ℝ → ℝ → Erdos132.TwoInteriorCircle.Plane
'Erdos132.AxialEllipse.point' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.OnEllipse : ℝ → ℝ → Erdos132.TwoInteriorCircle.Plane → Prop
'Erdos132.AxialEllipse.OnEllipse' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.coordinate_mem_Icc : ∀ (a b : ℝ),
  0 < b →
    b < a → ∀ {p : Erdos132.TwoInteriorCircle.Plane}, Erdos132.AxialEllipse.OnEllipse a b p → p.ofLp 0 ∈ Set.Icc (-a) a
'Erdos132.AxialEllipse.coordinate_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.dist_sq_eq_radialSquare : ∀ (a b c : ℝ),
  0 < b →
    b < a →
      ∀ {p : Erdos132.TwoInteriorCircle.Plane},
        Erdos132.AxialEllipse.OnEllipse a b p →
          dist p (Erdos132.AxialEllipse.point c 0) ^ 2 = Erdos132.AxialEllipse.radialSquare a b c (p.ofLp 0)
'Erdos132.AxialEllipse.dist_sq_eq_radialSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.vertical_card_le_two : ∀ (H : Finset Erdos132.TwoInteriorCircle.Plane) (a b x : ℝ),
  0 < b → b < a → (∀ p ∈ H, Erdos132.AxialEllipse.OnEllipse a b p) → {p ∈ H | p.ofLp 0 = x}.card ≤ 2
'Erdos132.AxialEllipse.vertical_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.ellipse_not_mem_interior : ∀ (H : Finset Erdos132.TwoInteriorCircle.Plane) (a b : ℝ),
  0 < b →
    b < a →
      (∀ p ∈ H, Erdos132.AxialEllipse.OnEllipse a b p) →
        ∀ {p : Erdos132.TwoInteriorCircle.Plane},
          Erdos132.AxialEllipse.OnEllipse a b p → p ∉ interior ((convexHull ℝ) ↑H)
'Erdos132.AxialEllipse.ellipse_not_mem_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.radialSquare_injOn : ∀ (a b c : ℝ),
  0 < b → b < a → (a ^ 2 - b ^ 2) / a ≤ |c| → Set.InjOn (Erdos132.AxialEllipse.radialSquare a b c) (Set.Icc (-a) a)
'Erdos132.AxialEllipse.radialSquare_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.radial_card_le_two : ∀ (H : Finset Erdos132.TwoInteriorCircle.Plane) (a b c d : ℝ),
  0 < b →
    b < a →
      (∀ p ∈ H, Erdos132.AxialEllipse.OnEllipse a b p) →
        (a ^ 2 - b ^ 2) / a ≤ |c| → {p ∈ H | dist p (Erdos132.AxialEllipse.point c 0) = d}.card ≤ 2
'Erdos132.AxialEllipse.radial_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.common_support_card_le_two : ∀ (H : Finset Erdos132.TwoInteriorCircle.Plane) (a b c₁ c₂ : ℝ),
  0 < b →
    b < a →
      (∀ p ∈ H, Erdos132.AxialEllipse.OnEllipse a b p) →
        c₁ ≠ c₂ →
          0 < c₁ * c₂ →
            (a ^ 2 - b ^ 2) / a ≤ |c₁| →
              (a ^ 2 - b ^ 2) / a ≤ |c₂| →
                Finset.image (fun p => Erdos132.AxialEllipse.radialSquare a b c₁ (p.ofLp 0)) H =
                    Finset.image (fun p => Erdos132.AxialEllipse.radialSquare a b c₂ (p.ofLp 0)) H →
                  H.card ≤ 2
'Erdos132.AxialEllipse.common_support_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.same_side_axial_ellipse : ∀ (n : ℕ) (H : Finset Erdos132.TwoInteriorCircle.Plane) (a b c₁ c₂ : ℝ),
  8 ≤ n →
    0 < b →
      b < a →
        H.card = n - 2 →
          (∀ p ∈ H, Erdos132.AxialEllipse.OnEllipse a b p) →
            Erdos132.AxialEllipse.point c₁ 0 ∈ interior ((convexHull ℝ) ↑H) →
              Erdos132.AxialEllipse.point c₂ 0 ∈ interior ((convexHull ℝ) ↑H) →
                c₁ ≠ c₂ →
                  0 < c₁ * c₂ →
                    (a ^ 2 - b ^ 2) / a ≤ |c₁| →
                      (a ^ 2 - b ^ 2) / a ≤ |c₂| →
                        (insert (Erdos132.AxialEllipse.point c₁ 0) (insert (Erdos132.AxialEllipse.point c₂ 0) H)).card =
                            n ∧
                          ∃ d,
                            0 < d ∧
                              d <
                                  Metric.diam
                                    ↑(insert (Erdos132.AxialEllipse.point c₁ 0)
                                        (insert (Erdos132.AxialEllipse.point c₂ 0) H)) ∧
                                1 ≤
                                    Erdos132.TwoInteriorCircle.multiplicity
                                      (insert (Erdos132.AxialEllipse.point c₁ 0)
                                        (insert (Erdos132.AxialEllipse.point c₂ 0) H))
                                      d ∧
                                  Erdos132.TwoInteriorCircle.multiplicity
                                      (insert (Erdos132.AxialEllipse.point c₁ 0)
                                        (insert (Erdos132.AxialEllipse.point c₂ 0) H))
                                      d ≤
                                    n
'Erdos132.AxialEllipse.same_side_axial_ellipse' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.fixtureHull : Finset Erdos132.TwoInteriorCircle.Plane
'Erdos132.AxialEllipse.fixtureHull' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos132.AxialEllipse.ellipse_fixture : Erdos132.AxialEllipse.fixtureHull.card = 6 ∧
  (∀ p ∈ Erdos132.AxialEllipse.fixtureHull, Erdos132.AxialEllipse.OnEllipse 2 1 p) ∧
    Erdos132.AxialEllipse.point (8 / 5) 0 ∈ interior ((convexHull ℝ) ↑Erdos132.AxialEllipse.fixtureHull) ∧
      Erdos132.AxialEllipse.point (17 / 10) 0 ∈ interior ((convexHull ℝ) ↑Erdos132.AxialEllipse.fixtureHull) ∧
        8 ≤ 8 ∧
          0 < 1 ∧
            1 < 2 ∧
              8 / 5 ≠ 17 / 10 ∧ 0 < 8 / 5 * (17 / 10) ∧ (2 ^ 2 - 1 ^ 2) / 2 ≤ |8 / 5| ∧ (2 ^ 2 - 1 ^ 2) / 2 ≤ |17 / 10|
'Erdos132.AxialEllipse.ellipse_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```
