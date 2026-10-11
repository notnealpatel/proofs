# Equal-radius radial bridge

`ThreeInteriorRadial.norm_eq_of_saturated_common_support` proves Check027's
conditional equal-radius unit with the prescribed objects and hypotheses:
a finite planar hull of cardinality at least six, a positive common circle
radius, two nonzero centers, exactly two vertices in every radial fiber at
each center, and equality of the two radial distance supports. It adds no
interiority, parity, centroid, width, or equal-norm premise.

* **Common axis:** saturation and cardinality give at least two squared
  radial values. Writing `v = a • u`, the inherited `radial_square_affine`
  makes the squared support an invariant finite affine set.
  `opposite_centers_of_support` uses `finite_affine_slope`, whose min/max
  width comparison forces `a = 1` or `a = -1`. Both give equal norms.
* **Distinct axes:** the inherited reflection-saturation lemma supplies
  permutations of the hull. Their sum is fixed by each reflection and
  hence belongs to both axis lines. Distinct lines force that sum to zero.
  Fiberwise summation counts each squared support value twice. Expanding
  squared distances with the zero sum gives
  `sum (dist h u)^2 = card H * (R^2 + norm u^2)` and likewise for `v`.
  Common support and positive cardinality imply equal norms.

A concrete joint-satisfiability witness uses the eight points
`(±3, ±4)` and `(±4, ±3)`, radius `5`, and centers `(1,0)` and `(0,1)`.
Every radial fiber has two vertices, the supports agree, and the axes
are distinct. Choosing `(1,0)` for both centers also witnesses the
common-axis premises. This witness is kernel-checked in the module.

The unit is downstream-ready for the odd-three-interior theorem; it does
not establish that theorem's upstream saturation/common-support premises,
its transporter argument, or its final contradiction.
