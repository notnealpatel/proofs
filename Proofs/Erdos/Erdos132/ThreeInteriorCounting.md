# Odd three-interior counting and saturation

## Public entry point

`Erdos132.ThreeInteriorCounting.counting_saturation` consumes only the original
geometry and contrary multiplicity hypothesis:

- `n : ℕ`, `9 ≤ n`, `Odd n`;
- `H : Finset Plane`, `H.card = n - 3`;
- `R : ℝ`, `0 < R`, and `‖h‖ = R` for every `h ∈ H`;
- pairwise distinct `u`, `v`, `w`, each in the **ambient** interior of
  `convexHull ℝ (H : Set Plane)`;
- every occurring positive distance strictly below the actual diameter of
  `X = insert u (insert v (insert w H))` has true multiplicity at least `n + 1`.

It imports only `Erdos.Erdos132.TwoInteriorCircle`. Its `Plane`, unordered loop-free
`pairs`, `pairDist`, and `multiplicity` are the inherited definitions without changes.
The support `S` is exactly the inherited `nonDiameterDistances X`.
`mem_nonDiameterDistances_iff_positive` proves that membership means an occurring
positive ordinary distance strictly below the actual diameter; the support is not
replaced by a radial surrogate.

The conclusion, as a transparent conjunction, is:

```text
X.card = n
Metric.diam X = Metric.diam H
0 < Metric.diam H
H.card = 2 * S.card
n = 2 * S.card + 3
3 ≤ S.card
∀ z ∈ {u,v,w}, z ≠ 0 →
  H.image (fun h => dist h z) = S ∧
  (∀ d ∈ S, (H.filter (fun h => dist h z = d)).card = 2) ∧
  (∀ h ∈ H, (H.filter (fun b => dist b z = dist h z)).card = 2)
```

The off-center guard is essential: the result does **not** assume or conclude that
all three interiors are off-center. A center interior has one radial fiber of size
`H.card`, and the frozen argument treats that branch separately.

## Proof ingredients

1. Strict disk containment excludes all three interiors from `H`, so distinctness
   gives `X.card = H.card + 3 = n`.
2. The convex-hull diameter bound and inclusion of `H` give diameter preservation;
   `H.card ≥ 6` gives positive diameter. Strict interiority puts every radial pair
   in the actual non-diameter support.
3. At least one interior is off-center. Two-circle intersection gives capacity two
   for its radial fibers, yielding `n - 3 ≤ 2 * S.card`.
4. The inherited `nonDiameter_pair_budget` reserves an attained diameter pair in
   the **unordered** pair count. It gives
   `S.card * (n + 1) + 1 ≤ Nat.choose n 2`.
5. `odd_size_of_pair_budget` proves `2 * S.card ≤ n - 2` from that budget; odd
   parity and the lower bound force `n - 3 = 2 * S.card`.
6. For each off-center interior, inherited `saturated_fibers` turns equality of
   total capacity into size-two fibers throughout `S`; their positive cardinality
   proves equality with the actual hull radial image.

`original_geometry_fixture` jointly witnesses every original geometric premise at
`n = 9`, using `rational_circle_fixture` and a third interior at the midpoint of its
two interior points. It deliberately does not witness the contrary multiplicity
premise. An additional concrete arithmetic example checks the odd budget lemma at
`n = 9`, `q = 3`.

## Validation

The final production source passed the bounded narrow target:

```sh
timeout --kill-after=2s 60s lake -q build +Erdos.Erdos132.ThreeInteriorCounting
```

A separate disposable leaf imported that compiled module, checked the full public
signature with `#check @...counting_saturation`, and printed axiom dependencies of
all seven public theorems. Every list was exactly
`[propext, Classical.choice, Quot.sound]`. The leaf passed
`lake env lean -j 1 -M 4000` under a separate 60-second limit, and was removed
with the exploratory probe. Production contains no audit commands or `sorry`.
The build emitted only the three inherited `TwoInteriorCircle` linter warnings.
These checks establish elaboration and the stated axiom boundary; the fixture
checks original-premise non-vacuity, not satisfiability of the contrary premise.

## Boundary of this unit

For the named full odd-three-interior consumer, this unit pays the counting and
saturation bridge from original geometry plus contrary multiplicity. It assumes
no downstream saturation, reflection, rotation, transporter, or orbit certificate.
The rotation/transporter and the final centered/off-center case contradictions
remain outside this unit. It does not establish the full odd theorem, an even-order
result, or a global Erdős #132 result.
