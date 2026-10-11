# Odd three-interior branch with one interior at the center

## Status: complete producer-checked one-center branch, including arbitrary-center translation

`ThreeInteriorCenter.lean` works with the inherited `TwoInteriorCircle.Plane`, actual finite hull/configuration, ordinary distance, and the inherited unordered loop-free `Sym2` multiplicity. Its original-geometry consumers use odd `n ≥ 9`, `H.card = n - 3`, a positive-radius circle centered at zero, and three distinct ambient interior points `0,u,v`. They do **not** assume antipodality, a transporter, stabilizer order, radial support equality, or a saturation certificate. Such facts are derived under the contrary multiplicity hypothesis and then used to refute it. The final existential consumers have only the original geometric hypotheses, not the contrary multiplicity premise. No original-geometry extreme-point assumption is needed; the satisfiability fixture additionally proves it.

This is a completed local producer unit. It is not an independent review, an adopted revision, or a solution to the other odd branches.

## Checked chain

1. `multiplicity_insert` and `card_radial_filter_insert` account for genuinely new vertices. `centered_multiplicity_decomposition` gives, away from radius `R`,
   `μ_X(d) = μ_H(d) + 4 + 2*[d = ‖u‖] + [d = dist u v]`.
   Coincidence `R = dist u v` is permitted; no exclusion was added.
2. `centered_contrary_model` derives actual configuration cardinality and diameter, exact counting saturation, equal positive interior radii strictly below `R`, radial support equality, and a genuine nonidentity full-hull transporter.
3. `centered_contrary_saturation` proves order at least three and saturation of every configuration support class except `R`. Divisibility eliminates a deficit of at most three; the exceptional order-three case is handled rather than assumed away.
4. `order_three_card_six_of_odd_saturation` reduces odd stabilizer order to order three and six actual hull vertices. The private six-vertex argument partitions the actual hull into two three-point orbits, finds an actual radius chord, uses the complex square/cyclotomic identity, and proves the inter-orbit transporter would preserve the whole hull. This contradicts order three.
5. `centered_contrary_even_order` therefore derives even full stabilizer order from the original geometry and contrary multiplicities.
6. `centered_contrary_support` derives actual antipodality, `diam H = 2*R`, `μ_H(R) = 0`, and
   `nonDiameterDistances H = (nonDiameterDistances X).erase R`.
   The support proof exhausts actual two-point neighbor fibers and excludes exactly the vertex and its antipode. No separate diameter-pair-count certificate is assumed.
7. `hull_squared_complement` pairs actual hull classes with squared sum `4*R²`. `radial_squared_complement` pairs actual radial classes with squared sum `2*(R²+‖u‖²)`.
8. Private finite-extrema lemmas prove that complementary squared sums determine the squared minimum-plus-maximum. Private `centered_contrary_of_short_pair` completes the contradiction **given** a distinct actual hull pair at distance at most `R`: zero radius-class multiplicity makes that chord strictly shorter than `R`; its complement is strictly longer; erasing `R` does not change either extremum; hence `‖u‖²=R²`, contradicting the strict interior radius bound.

## Completed consumers and exact proof boundary

The separately assigned `CircleShortChord.lean` was collected unchanged from finalized revision `e5c0f42e160b5b7995ee9e2ae6e0b0e044415d7c`; its exact hash is recorded below. Its API `Erdos132.CircleShortChord.exists_short_chord` requires only a positive radius, actual hull points on the circle, and at least six hull points, and returns distinct actual points at positive distance at most the radius. It was not redeveloped here.

- `centered_contrary` derives `False` from original centered geometry and contrary multiplicities. It derives `6 ≤ H.card`, calls the external short-chord theorem, and feeds the returned actual pair to the private extrema contradiction.
- `zero_center_witness` negates the contrary premise and supplies an occurring positive nondiameter length with multiplicity between one and `n`, without any bridge premise.
- `one_center_circle` is the original arbitrary-center consumer. With `X = insert O (insert u (insert v H))`, its hypotheses are exactly:
  `9 ≤ n`, `Odd n`, `H.card = n - 3`, `0 < R`, `∀ h ∈ H, dist h O = R`,
  `u ≠ O`, `v ≠ O`, `u ≠ v`, and ambient hull-interior membership of `O,u,v`.
  Its conclusion is
  `X.card = n ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧ 1 ≤ multiplicity X d ∧ multiplicity X d ≤ n`.

The translation map is the actual isometry `h ↦ h - O`. Existing checked APIs transport ambient convex-hull interior and unordered-pair multiplicity; diameter and finite cardinality are transported by isometry/injectivity. The three-interior cardinality theorem proves the actual configuration has exactly `n` points. No symmetry, ordering, support, transporter, short-chord, or multiplicity certificate was added to the final hypotheses. The strict positivity and strict diameter bound remain unchanged. Occurrence is represented by positive cardinality of the inherited pair filter (`1 ≤ multiplicity`), not by a diagonal pair or a relaxed length class.

There is no unpaid mathematical bridge in this one-center consumer. The other odd branches, overall theorem assembly, final independent review, and coordinator's fresh audit remain upstream and are not claimed here.

## Semantic and non-vacuity evidence

`original_centered_geometry_fixture` jointly instantiates all original geometric hypotheses at `n=9`, a six-point rational unit-circle hull with vertices `(±1,0),(0,±1),(3/5,4/5),(-3/5,-4/5)`, and two distinct nonzero small opposite interior points. The proof establishes ambient interior, not relative interior, and establishes actual extreme-point membership. Hull/configuration domains are nonempty; no `Fin 0` or empty-support fixture was substituted. The disposable final audit also compiled an explicit joint instantiation of every arbitrary-center consumer hypothesis, using `O = 0` and `dist_zero_right`. The contrary multiplicity premise is deliberately the negated target, not a satisfiability claim; the chain refutes it before the final existential theorem.

All natural subtraction is guarded by `9 ≤ n`; distances and positive radius retain their ordinary meanings. No new definitions, axioms, `native_decide`, trust-changing attributes, or `sorry`s were introduced. Intermediate odd-saturation analyses are contrary-model deductions, not claims of a satisfiable odd-saturation model.

## Final producer receipts

- `timeout --kill-after=2s 60s lake -q build +Erdos.Erdos132.ThreeInteriorCenter`: task `center-witness-build` succeeded (module build 18 seconds), establishing the centered consumers. Task `center-translation-build-2` then succeeded (module build 17 seconds), establishing the entire final 1209-line module including `one_center_circle`. Two local style-linter warnings remain (unnecessary `simpa` and unnecessary sequence focus), plus inherited dependency warnings; there were no errors or `sorry` warnings.
- `timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/CenterAudit.lean`: task `center-final-public-audit` succeeded. The leaf imported the final production module, printed full `#check @...` signatures and `#print axioms` for all **16** public declarations, and compiled the joint arbitrary-center hypothesis example. Every signature was inspected; there are no phantom section parameters or additional certificate premises on the final witness. Every axiom set is a subset of `{propext, Classical.choice, Quot.sound}`. In particular both existential consumers and `centered_contrary` have exactly the standard three, transitively auditing the private extrema endpoint and external short-chord dependency.
- Audited names: `multiplicity_insert`, `card_radial_filter_insert`, `centered_multiplicity_decomposition`, `centered_contrary_model`, `original_centered_geometry_fixture`, `eq_of_divisible_small_remainder`, `centered_contrary_saturation`, `order_three_card_six_of_odd_saturation`, `even_order_of_saturation`, `centered_contrary_even_order`, `centered_contrary_support`, `hull_squared_complement`, `radial_squared_complement`, `centered_contrary`, `zero_center_witness`, `one_center_circle` (all in `Erdos132.ThreeInteriorCenter`). The divisibility arithmetic helper uses only `propext` and `Quot.sound`; the others use the standard three.
- The final leaf was removed after the audit. Production contains no exploratory `#check`, `#print`, or `#eval` commands. A source hygiene scan found no `sorry`, axioms, or `native_decide` in the local module.
- Translation repair: nonzero translated points were proved directly with `sub_eq_zero.mp`; the first attempted `simp only` did not discharge that elaborated goal. The repaired version was built and then audited, not handed off untested.
- API infrastructure: `parallelogram_law_with_norm` requires explicit scalar type `ℝ`; this was verified by indexed declaration inspection and a successful build. Finset extremum APIs were checked in a disposable compiler probe.
- Actual observed timing for this final resumption: resumed at supplied clock `17:18:10Z`; final consumer build and all-public audit were verified by final cleanup clock `17:23:33Z` on 2026-10-11. This is observed elapsed wall time, not a token/CPU estimate or a total-campaign effort estimate.

## Exact external source inventory

The following files were copied unmodified from the supplied revisions, not authored here:

From `ba82c72cc5741b38685cf98e06e84667a15e4fe2`:

| File | SHA-256 |
| --- | --- |
| CircleRotation.lean | `13a31899aa0cfca29c9b4ddf82661714e8660fe0744519cd61d003ebc04de0f7` |
| CircleRotationTransport.lean | `643d6121613abf8dcca238a9e55cfce3ae857d75e127148cc571874da885aeff` |
| CircleRotationTransport.md | `ac6bb9ca1d37d90792f76efe8c4e05e8b5704873c03f9c6acafe10f375b18ed5` |
| RadialTransport.lean | `db8652f3b9ccc205be41a2421011091e8263ecb2257866b649178b53d2a500f6` |
| ThreeInteriorRadial.lean | `cab7c6a514b218811c6f66fbe2b22de88e5725560e78bf68cdfb86dc89777ba3` |
| ThreeInteriorRadial.md | `a5df955a8e3e4f81174f24ae32fcfcc896cc699e8558fee8ded87ea61c8dd1b1` |

From `f6bbed345ce67c9357a2b279b83d57dc98a0e9f7`:

| File | SHA-256 |
| --- | --- |
| ThreeInteriorCounting.lean | `1db0c49b92162704614f764f6b2ead4c4c3a24bbea04a7f54c975496a9253881` |
| ThreeInteriorCounting.md | `25a195492eb5c02b5a9e1e85f9e0f7875f0c4f02c7c7593545d7ac42ff313d34` |

From `abeb5e430158fc5dca288318572d466a02f09afa`:

| File | SHA-256 |
| --- | --- |
| CircleRotationOrder.lean | `f4ca0de476f6170f2e494784cbeb0e80f8937ce0004c7bd6e3be3a833ec0adb7` |

From finalized `e5c0f42e160b5b7995ee9e2ae6e0b0e044415d7c`:

| File | SHA-256 |
| --- | --- |
| CircleShortChord.lean | `2abc6588177796237da2204a078e604f9219970627d5a3bae8f7fb5950aeb7b2` |

Final local proof: `ThreeInteriorCenter.lean` SHA-256 `b25203d36913687bf00268381a99a6fa3840e3a4531ea0b8347eda4f2b9f5e11`.
