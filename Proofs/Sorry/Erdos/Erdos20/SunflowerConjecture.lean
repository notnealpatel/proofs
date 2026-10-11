import Erdos.Erdos20.SunflowerConjecture

/-
  Erdős Problem #20 — the **sunflower conjecture** in the shape OEIS A332077
  states it. This is the explicit admission archive: the open conjecture
  and its dependent OEIS form below both depend on `sorryAx`.
  The full source/status ledger is retained here. All infrastructure it
  describes is proved in the imported production module — the definition of the
  sunflower number, its finiteness, its lower bounds, its agreement with the
  tabulated OEIS terms, and the equivalence of the two sunflower conventions
  in play — is proved.

  ══════════════════════════════════════════════════════════════════════
  PRIMARY SOURCE (verbatim, `goof oeis show A332077`, re-pulled 2026-08-05)
  ══════════════════════════════════════════════════════════════════════

  id: A332077

  name:
    "Square array of sunflower numbers Sun(m,n) = minimal number of distinct
    sets of cardinality <= m such that there is a sunflower with at least n
    sets among them, read by falling antidiagonals; m, n >= 1."

  terms:
    "1,2,1,3,2,1,4,7,2,1,5,11,21,2,1,6,21"

  comments:
    "A sunflower S is a collection of sets such that all pairwise
    intersections of distinct A, B in S are equal. The intersection of all
    the sets is called the core or kernel of S."

    "Some authors (e.g., Wikipedia) use \"more than\" instead of \"at least\"
    in the definition, which corresponds to an index n decreased by 1. We use
    the same conventions Tao (but following OEIS standards we use m,n instead
    of k,r). Also, some authors (e.g., Abbott et al. and the Polymath wiki
    page) use f(k,r) = Sun(k,r) - 1 which is not the minimal number of
    required sets, but such that any collection of *more than* f(k,r) sets
    has the given property."

    "Bell et al. improve Rao's bound [as reproved by Tao] from
    Sun(m,n) <= O(n log(mn))^m for m, n >= 2 to the slightly cleaner bound
    Sun(m,n) <= O(n log m)^m for m, n >= 2. [Pers. comm. from L. Warnke.] -
    _M. F. Hasler_, May 02 2021"

  formulas:
    "Sun(m,n) = n for n <= 2 and all m;"
    "Sun(1,n) = n for all n: see Examples for explanation."
    "Sun(2,n) = n(n-1)+1 if n is odd, (n-1)^2+n/2 if n is even.
     (Abbott-Hanson-Sauer)"
    "(n-1)^m <= Sun(m,n) <= (n-1)^m*m! + 1. (Erdös & Rado)"
    "Sun(m,n) <= O(n log(mn))^m for m, n >= 2. (Rao)"
    "Sun(m,n) <= O(n log m)^m for m, n >= 2. (Bell-Chueluecha-Warnke)"
    "Sunflower conjecture: Sun(m,n) <= (n*O(1))^m."

  xrefs: "Cf. A236397, A266696."
  keywords: "nonn,tabl,hard,more,nice"

  Erdős #20 itself, and the Erdős–Rado bound, are pinned verbatim in
  `Erdos/Erdos20/ErdosRado.lean`; this file consumes that file's
  `erdos_rado_sunflower_same_card`.

  ══════════════════════════════════════════════════════════════════════
  THE `O(1)` IS WRITTEN AS AN EXPLICIT EXISTENTIAL
  ══════════════════════════════════════════════════════════════════════

  "Sun(m,n) <= (n*O(1))^m" is asymptotic notation over the two-parameter
  family; the only reading under which it is a single mathematical claim is
  "there is one absolute constant that works for every m and n".  So the
  archived form is

      ∃ C : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Sun m n ≤ (n * C) ^ m.

  `C : ℕ` rather than `C : ℝ` costs nothing: a real constant may be rounded
  up (`(n * ⌈C⌉)^m ≥ (n * C)^m`) and a natural constant is already real, so
  the two existentials are equivalent.  That rounding step is NOT formalized
  here — this file's `Sun` is `ℕ`-valued and the `ℕ` form is what is stated.

  The guards `1 ≤ m` and `1 ≤ n` are A332077's own ("m, n >= 1") and they are
  load-bearing, not decoration: `m = 0` makes the claim FALSE.  Under the
  definitions below the only sets of cardinality ≤ 0 are `∅`, so no family of
  ≥ 2 such sets exists and `Sun 0 n = 2` vacuously, while `(n * C) ^ 0 = 1`.

  ══════════════════════════════════════════════════════════════════════
  TWO SUNFLOWER CONVENTIONS, AND WHY BOTH APPEAR HERE
  ══════════════════════════════════════════════════════════════════════

  A332077's own notion (comment 1, verbatim above) is: a collection whose
  pairwise intersections of distinct members are all equal.  That is
  `IsOeisSunflower` below; `isOeisSunflower_iff_pairwise_inter_eq` checks
  that the `∃ K` packaging is literally the quoted "all ... are equal".

  `Erdos/Erdos20/Sunflower.lean`'s `IsSunflowerWith sub K` — which the brief
  for this file requires, and which the rest of `Erdos20/` is built on — is
  STRICTLY STRONGER: it names the kernel, demands `K ⊆ S`, and demands
  NONEMPTY PETALS `S \ K ≠ ∅`.  The gap is real and not an artifact:

    • `{{0}, {0,1}, {0,2}}` has all three pairwise intersections `= {0}`, so
      it is a `3`-set sunflower for A332077, but `{0} \ {0} = ∅` so it is not
      an `IsSunflowerWith`-sunflower.
    • `{∅, {0}}` likewise: an A332077 `2`-set sunflower, not an
      `IsSunflowerWith` one.

  Consequently the two threshold functions differ, and the gap is UNBOUNDED,
  not a constant: `sunOeis_two_petals` and `sun_two_petals` prove
  `SunOeis m 2 = 2` (the source's tabulated value) against `Sun m 2 = m + 2`.
  So both functions are defined here.  They are sandwiched, sorry-free:

      SunOeis m n ≤ Sun m n ≤ SunOeis m (n+1)                    (n ≥ 1)

  the right inequality because deleting from an A332077 sunflower the at most
  one member that equals the kernel leaves an `IsSunflowerWith` sunflower
  (`hasSunflower_of_isOeisSunflower`).  The sandwich costs only a `+1` in the
  petal index, which the `∃ C` form absorbs: `sunflowerConjecture_iff` proves,
  sorry-free, that the conjecture for `Sun` and the conjecture for `SunOeis`
  are the SAME statement (with `C ↦ 2 * C`).  The separate archive places its single `sorry`
  on the `Sun` form, and derives `sunflower_conjecture_oeis` from it.
  Production retains this independent equivalence and does not import Sorry.

  ══════════════════════════════════════════════════════════════════════
  NON-VACUITY LEDGER
  ══════════════════════════════════════════════════════════════════════

  `Sun m n = sInf {N | …}` and `Nat.sInf ∅ = 0`, so a conjecture about `Sun`
  is worthless until the set is known nonempty.  Proved here:

    • `sun_le_erdosRado`  (n ≥ 2):  Sun m n ≤ (m+1)·((n-1)^m·m!) + 1
      — via `erdos_rado_sunflower_same_card`, so the set is nonempty and
      `Sun` is a genuine minimum, not the `sInf ∅` junk value.
    • `sunflowerProperty_one_petal`:  the n = 1 column is nonempty too.
    • `two_le_sun`     (n ≥ 1):  2 ≤ Sun m n     (so `Sun` is never 0).
    • `le_sunOeis`     (m,n ≥ 1):  n ≤ SunOeis m n.
    • `not_sunflowerProperty_one`: the defining property genuinely FAILS at
      `N = 1`, so `Sun` is not pinned by a vacuous hypothesis.
    • `sun_one_petal`, `sun_two_petals`: two whole columns of `Sun` computed
      EXACTLY (`Sun m 1 = 2`, `Sun m 2 = m + 2`), each by a matching pair of
      "property holds at N" / "property fails at N - 1" theorems.

  Agreement with the tabulated terms "1,2,1,3,2,1,4,7,2,1,5,11,21,2,1,6,21"
  (falling antidiagonals: Sun(1,1); Sun(1,2),Sun(2,1); Sun(1,3),Sun(2,2),
  Sun(3,1); …) is machine-checked on every entry the array's first row and
  first two columns contribute — i.e. all of the listed terms except
  Sun(2,3)=7, Sun(2,4)=11, Sun(3,3)=21, Sun(2,5)=21:

    • `sunOeis_one_petal`      : SunOeis m 1 = 1   (formula "Sun(m,n) = n for n <= 2")
    • `sunOeis_two_petals`     : SunOeis m 2 = 2   (same formula line)
    • `sunOeis_one_uniformity` : SunOeis 1 n = n   (formula "Sun(1,n) = n for all n")

  ══════════════════════════════════════════════════════════════════════
  DEVIATIONS FROM THE SOURCE
  ══════════════════════════════════════════════════════════════════════

  (D1) Ground set.  A332077 speaks of sets simpliciter; here a family lives in
       `Finset (Finset (Fin g))` and `g` is universally quantified inside the
       definitions.  Any finite family of finite sets has a finite union and
       so embeds in some `Fin g`, but that reduction is not formalized: the
       Lean statement is the "all finite ground sets" instance.

  (D2) Sunflower notion.  As dissected above, `Sun` uses the strictly
       stronger `IsSunflowerWith`; `SunOeis` is the faithful one.  The two
       are related sorry-free and the conjecture is proved equivalent.

  (D3) Upper bound constant.  A332077 records `Sun(m,n) <= (n-1)^m*m! + 1`;
       this file proves only `Sun m n ≤ (m+1)·((n-1)^m·m!) + 1`.  The loss of
       the factor `m+1` is deliberate: A332077 uses "cardinality <= m", while
       `ErdosRado.lean` supplies the UNIFORM ("cardinality = k") Erdős–Rado
       lemma, and the naive "≤ k" restatement is not merely unproved but
       FALSE under the nonempty-petal convention — `ErdosRado.lean`'s
       `erdosRado_le_variant_fails` refutes it at `r = 1, k = 1, F = {∅}`.
       So the family is split into its `m+1` cardinality fibres and the
       uniform lemma applied to the largest.  Only finiteness is needed
       downstream, and the factor is harmless for it.

  (D4) Lower bound.  A332077's `(n-1)^m <= Sun(m,n)` is NOT formalized; it
       needs the `[n-1]^m` grid construction.  The weaker `n ≤ SunOeis m n`
       is proved instead (`le_sunOeis`), which suffices for non-vacuity.

  (D5) Rao / Bell–Chueluecha–Warnke.  The two `O(n log …)^m` formula lines
       are recorded above for completeness and are not stated in Lean; they
       need real logarithms and a second asymptotic constant, and neither is
       the conjecture this file archives.

  ══════════════════════════════════════════════════════════════════════
  NOVELTY
  ══════════════════════════════════════════════════════════════════════

  The sunflower conjecture is OPEN (A332077 keyword `hard`; Erdős #20).
  Nothing here proves any new mathematics: the separate archive records the faithful statement,
  and this production file supplies the bookkeeping that makes it auditable.  Mathlib
  as vendored contains no occurrence of "sunflower" (checked over
  `.lake/packages/mathlib/Mathlib/`, 2026-08-05).
-/


set_option autoImplicit false

/-- **Sunflower conjecture**, A332077 formula section, verbatim:
"Sunflower conjecture: Sun(m,n) <= (n*O(1))^m."

The `O(1)` is written as an explicit existential constant, as it must be for
the line to name a single claim: ONE constant `C` serving every `m ≥ 1` and
every `n ≥ 1`.  `1 ≤ m` is not decoration — `sun_two_petals 0` gives
`Sun 0 2 = 2` against `(2 * C) ^ 0 = 1`, and the production module's last `example`
machine-checks that dropping `1 ≤ m` turns the statement FALSE.

OPEN (Erdős #20; A332077 keyword `hard`).  This is the archive's single explicit admission.  Everything it needs in order to be a
non-vacuous claim is proved in the imported production module: `sunflowerProperty_nonempty` (so `Sun` is a
real minimum, not `Nat.sInf ∅`), `two_le_sun` (so `Sun` is never `0`),
`sun_le_erdosRado` (a finite upper bound exists), and
`sunflowerConjecture_iff` (this form and the A332077-faithful form are the
same statement). -/
theorem sunflower_conjecture :
    ∃ C : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Sun m n ≤ (n * C) ^ m := by
  sorry

/-- The sunflower conjecture as A332077 means it, i.e. on A332077's own
sunflower notion.  Derived from `sunflower_conjecture` through
`sunflowerConjecture_iff`; it introduces no `sorry` of its own. -/
theorem sunflower_conjecture_oeis :
    ∃ C : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → SunOeis m n ≤ (n * C) ^ m :=
  sunflowerConjecture_iff.mp sunflower_conjecture

