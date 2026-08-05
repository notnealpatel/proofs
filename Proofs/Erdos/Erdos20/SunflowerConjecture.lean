/-
  Erdős Problem #20 — the **sunflower conjecture** in the shape OEIS A332077
  states it.  This is a STATEMENT ARCHIVE: the conjecture itself is open and
  is the file's single `sorry`.  Everything else — the definition of the
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
  are the SAME statement (with `C ↦ 2 * C`).  So the single `sorry` is placed
  on the `Sun` form the brief asks for, and the A332077-faithful form
  `sunflower_conjecture_oeis` is derived from it with no further `sorry`.

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
  Nothing here proves any new mathematics: the file is a faithful statement
  archive plus the bookkeeping that makes the statement auditable.  Mathlib
  as vendored contains no occurrence of "sunflower" (checked over
  `.lake/packages/mathlib/Mathlib/`, 2026-08-05).
-/

import Erdos.Erdos20.ErdosRado

set_option autoImplicit false

open Finset
open scoped Nat

-- ════════════════════════════════════════════════════════════════════
-- A332077'S OWN SUNFLOWER NOTION
-- ════════════════════════════════════════════════════════════════════

/-- A332077's definition of a sunflower, verbatim: "A sunflower S is a
collection of sets such that all pairwise intersections of distinct A, B in S
are equal."  The common value `K` is the source's "core or kernel".

Note what is *absent*, by contrast with `IsSunflowerWith` of
`Erdos/Erdos20/Sunflower.lean`: no `K ⊆ S` clause (it is a consequence once
`sub` has two members, see `kernel_subset_of_pairwise_inter`) and, crucially,
no nonempty-petal clause `S \ K ≠ ∅`. -/
def IsOeisSunflower {g : ℕ} (sub : Finset (Finset (Fin g))) : Prop :=
  ∃ K : Finset (Fin g), ∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → S ∩ T = K

/-- The `∃ K` packaging of `IsOeisSunflower` is literally A332077's phrase
"all pairwise intersections of distinct A, B in S are equal". -/
theorem isOeisSunflower_iff_pairwise_inter_eq {g : ℕ}
    (sub : Finset (Finset (Fin g))) :
    IsOeisSunflower sub ↔
      ∀ A ∈ sub, ∀ B ∈ sub, A ≠ B → ∀ C ∈ sub, ∀ D ∈ sub, C ≠ D →
        A ∩ B = C ∩ D := by
  constructor
  · rintro ⟨K, hK⟩ A hA B hB hAB C hC D hD hCD
    rw [hK A hA B hB hAB, hK C hC D hD hCD]
  · intro h
    by_cases hex : ∃ A ∈ sub, ∃ B ∈ sub, A ≠ B
    · obtain ⟨A, hA, B, hB, hAB⟩ := hex
      exact ⟨A ∩ B, fun C hC D hD hCD => h C hC D hD hCD A hA B hB hAB⟩
    · push Not at hex
      exact ⟨∅, fun C hC D hD hCD => absurd (hex C hC D hD) hCD⟩

/-- Every `IsSunflowerWith` sunflower is an A332077 sunflower: the third
clause of `IsSunflowerWith` is exactly `IsOeisSunflower`'s only clause. -/
theorem IsSunflowerWith.isOeisSunflower {g : ℕ} {sub : Finset (Finset (Fin g))}
    {K : Finset (Fin g)} (h : IsSunflowerWith sub K) : IsOeisSunflower sub :=
  ⟨K, h.2.2⟩

/-- In an A332077 sunflower with at least two members the common pairwise
intersection is contained in every member — the `K ⊆ S` clause that
`IsSunflowerWith` postulates comes for free. -/
theorem kernel_subset_of_pairwise_inter {g : ℕ} {sub : Finset (Finset (Fin g))}
    {K : Finset (Fin g)}
    (hK : ∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → S ∩ T = K) (h2 : 1 < sub.card)
    {S : Finset (Fin g)} (hS : S ∈ sub) : K ⊆ S := by
  obtain ⟨T, hT, hTS⟩ := Finset.exists_mem_ne h2 S
  rw [← hK T hT S hS hTS]
  exact Finset.inter_subset_right

/-- **The convention bridge.**  An A332077 sunflower with `n + 1` sets yields
an `IsSunflowerWith` sunflower with `n` sets: at most one member can equal the
kernel `K` (the members are distinct), and deleting it leaves every remaining
member with `K ⊆ S` and `S ≠ K`, hence with a nonempty petal.

This is the only place the two conventions have to be reconciled, and it is
what makes `Sun m n ≤ SunOeis m (n+1)`. -/
theorem hasSunflower_of_isOeisSunflower {g : ℕ}
    {family sub : Finset (Finset (Fin g))} {n : ℕ} (hn : 1 ≤ n)
    (hsub : sub ⊆ family) (hcard : n + 1 ≤ sub.card)
    (hsf : IsOeisSunflower sub) : HasSunflower family n := by
  obtain ⟨K, hK⟩ := hsf
  have h2 : 1 < sub.card := by omega
  have hker : ∀ S ∈ sub, K ⊆ S := fun S hS =>
    kernel_subset_of_pairwise_inter hK h2 hS
  have hcard' : n ≤ (sub.erase K).card := by
    by_cases hKsub : K ∈ sub
    · rw [Finset.card_erase_of_mem hKsub]; omega
    · rw [Finset.erase_eq_of_notMem hKsub]; omega
  have hsf' : IsSunflowerWith (sub.erase K) K := by
    refine ⟨fun S hS => hker S (Finset.mem_of_mem_erase hS), ?_, ?_⟩
    · intro S hS
      have hSK : S ≠ K := Finset.ne_of_mem_erase hS
      have hKS : K ⊆ S := hker S (Finset.mem_of_mem_erase hS)
      rw [ne_eq, Finset.sdiff_eq_empty_iff_subset]
      exact fun hSsub => hSK (Finset.Subset.antisymm hSsub hKS)
    · exact fun S hS T hT hne =>
        hK S (Finset.mem_of_mem_erase hS) T (Finset.mem_of_mem_erase hT) hne
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hcard'
  exact ⟨t, (ht.trans (Finset.erase_subset _ _)).trans hsub, htcard, K,
    hsf'.subset ht⟩

-- ════════════════════════════════════════════════════════════════════
-- MONOTONICITY OF `HasSunflower`
-- ════════════════════════════════════════════════════════════════════

/-- A sunflower of a subfamily is a sunflower of the family. -/
theorem HasSunflower.mono_family {g : ℕ} {family family' : Finset (Finset (Fin g))}
    {k : ℕ} (h : HasSunflower family k) (hsub : family ⊆ family') :
    HasSunflower family' k := by
  obtain ⟨sub, hsubfam, hcard, K, hsf⟩ := h
  exact ⟨sub, hsubfam.trans hsub, hcard, K, hsf⟩

/-- "A sunflower with **at least** `k` sets" and "a sunflower with **exactly**
`k` sets" define the same threshold, because a subcollection of a sunflower is
a sunflower.  A332077 uses "at least"; `HasSunflower` uses "exactly". -/
theorem HasSunflower.of_le {g : ℕ} {family : Finset (Finset (Fin g))} {j k : ℕ}
    (h : HasSunflower family k) (hjk : j ≤ k) : HasSunflower family j := by
  obtain ⟨sub, hsubfam, hcard, K, hsf⟩ := h
  have hj : j ≤ sub.card := by omega
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hj
  exact ⟨t, ht.trans hsubfam, htcard, K, hsf.subset ht⟩

-- ════════════════════════════════════════════════════════════════════
-- THE SUNFLOWER NUMBERS
-- ════════════════════════════════════════════════════════════════════

/-- `SunflowerProperty m n N`: every family of at least `N` distinct sets,
each of cardinality at most `m`, inside any finite ground set, contains a
sunflower with `n` petals — in the `IsSunflowerWith` sense of
`Erdos/Erdos20/Sunflower.lean` (named kernel, nonempty petals). -/
def SunflowerProperty (m n N : ℕ) : Prop :=
  ∀ (g : ℕ) (family : Finset (Finset (Fin g))),
    (∀ S ∈ family, S.card ≤ m) → N ≤ family.card → HasSunflower family n

/-- `OeisSunflowerProperty m n N`: the same statement with A332077's own
sunflower notion `IsOeisSunflower` in place of `IsSunflowerWith`. -/
def OeisSunflowerProperty (m n N : ℕ) : Prop :=
  ∀ (g : ℕ) (family : Finset (Finset (Fin g))),
    (∀ S ∈ family, S.card ≤ m) → N ≤ family.card →
      ∃ sub ⊆ family, sub.card = n ∧ IsOeisSunflower sub

/-- The sunflower number of A332077, read through `IsSunflowerWith`:
"minimal number of distinct sets of cardinality <= m such that there is a
sunflower with at least n sets among them".

`Nat.sInf` returns `0` on the empty set, so this is only the intended minimum
once the defining set is known nonempty; that is `sunflowerProperty_nonempty`,
whose content is the Erdős–Rado bound. -/
noncomputable def Sun (m n : ℕ) : ℕ := sInf {N : ℕ | SunflowerProperty m n N}

/-- The sunflower number of A332077 read through A332077's own sunflower
notion.  This — not `Sun` — is the function whose values the source
tabulates; see `sunOeis_one_petal`, `sunOeis_two_petals`,
`sunOeis_one_uniformity`. -/
noncomputable def SunOeis (m n : ℕ) : ℕ :=
  sInf {N : ℕ | OeisSunflowerProperty m n N}

/-- The defining property is upward closed in the number of sets. -/
theorem SunflowerProperty.mono {m n N N' : ℕ} (h : SunflowerProperty m n N)
    (hNN' : N ≤ N') : SunflowerProperty m n N' :=
  fun g family hsmall hcard => h g family hsmall (hNN'.trans hcard)

/-- The A332077 property is upward closed in the number of sets. -/
theorem OeisSunflowerProperty.mono {m n N N' : ℕ}
    (h : OeisSunflowerProperty m n N) (hNN' : N ≤ N') :
    OeisSunflowerProperty m n N' :=
  fun g family hsmall hcard => h g family hsmall (hNN'.trans hcard)

/-- The stronger convention implies the A332077 one at the same threshold. -/
theorem SunflowerProperty.oeis {m n N : ℕ} (h : SunflowerProperty m n N) :
    OeisSunflowerProperty m n N := by
  intro g family hsmall hcard
  obtain ⟨sub, hsubfam, hsubcard, K, hsf⟩ := h g family hsmall hcard
  exact ⟨sub, hsubfam, hsubcard, hsf.isOeisSunflower⟩

/-- Any witness of the sunflower property at `N` gives `Sun m n ≤ N`. -/
theorem sun_le_of_sunflowerProperty {m n N : ℕ} (h : SunflowerProperty m n N) :
    Sun m n ≤ N :=
  Nat.sInf_le h

/-- Any witness of the OEIS sunflower property at `N` gives `SunOeis m n ≤ N`. -/
theorem sunOeis_le_of_oeisSunflowerProperty {m n N : ℕ}
    (h : OeisSunflowerProperty m n N) : SunOeis m n ≤ N :=
  Nat.sInf_le h

-- ════════════════════════════════════════════════════════════════════
-- FINITENESS VIA ERDŐS–RADO  (the non-vacuity engine)
-- ════════════════════════════════════════════════════════════════════

/-- **Erdős–Rado, fibre form.**  Splitting a family of sets of cardinality
`≤ m` into its `m + 1` cardinality fibres and applying the uniform lemma
`erdos_rado_sunflower_same_card` of `Erdos/Erdos20/ErdosRado.lean` to the
largest fibre gives the sunflower property at
`(m + 1) · ((n - 1) ^ m · m !) + 1`.

This is A332077's `Sun(m,n) <= (n-1)^m*m! + 1` weakened by the factor `m + 1`
(see DEVIATION D3 in the file header); only finiteness is used downstream.
`2 ≤ n` keeps `n - 1` off the `ℕ`-subtraction junk value and makes
`(n-1)^j * j !` monotone in `j`. -/
theorem sunflowerProperty_erdosRado {m n : ℕ} (hn : 2 ≤ n) :
    SunflowerProperty m n ((m + 1) * ((n - 1) ^ m * m !) + 1) := by
  intro g family hsmall hcard
  have hmaps : ∀ S ∈ family, S.card ∈ Finset.range (m + 1) := fun S hS =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hsmall S hS))
  have hsum : family.card =
      ∑ j ∈ Finset.range (m + 1), (family.filter (fun S => S.card = j)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hex : ∃ j ∈ Finset.range (m + 1),
      (n - 1) ^ m * m ! < (family.filter (fun S => S.card = j)).card := by
    by_contra hcon
    push Not at hcon
    have hle : family.card ≤ (m + 1) * ((n - 1) ^ m * m !) := by
      rw [hsum]
      calc ∑ j ∈ Finset.range (m + 1), (family.filter (fun S => S.card = j)).card
          ≤ ∑ _j ∈ Finset.range (m + 1), (n - 1) ^ m * m ! :=
            Finset.sum_le_sum hcon
        _ = (m + 1) * ((n - 1) ^ m * m !) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  obtain ⟨j, hjrange, hjcard⟩ := hex
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjrange)
  have hmono : (n - 1) ^ j * j ! ≤ (n - 1) ^ m * m ! :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hjm) (Nat.factorial_le hjm)
  have hfibre : HasSunflower (family.filter (fun S => S.card = j)) n :=
    erdos_rado_sunflower_same_card (k := j) (r := n) _ (by omega)
      (fun S hS => (Finset.mem_filter.mp hS).2) (by omega)
  exact hfibre.mono_family (Finset.filter_subset _ _)

/-- The `n = 1` column, which the Erdős–Rado fibre bound does not cover
(`(1-1)^m * m ! = 0`): any two distinct sets include a nonempty one, and a
single nonempty set is an `IsSunflowerWith` sunflower with kernel `∅`.

Two sets are genuinely needed — see `not_sunflowerProperty_one`. -/
theorem sunflowerProperty_one_petal (m : ℕ) : SunflowerProperty m 1 2 := by
  intro g family _ hcard
  obtain ⟨S, hS, hSne⟩ := Finset.exists_mem_ne (by omega : 1 < family.card) ∅
  refine ⟨{S}, Finset.singleton_subset_iff.mpr hS, Finset.card_singleton S, ∅,
    fun T _ => Finset.empty_subset T, ?_, ?_⟩
  · intro T hT
    rw [Finset.mem_singleton.mp hT, Finset.sdiff_empty]
    exact hSne
  · intro T hT U hU hne
    rw [Finset.mem_singleton.mp hT, Finset.mem_singleton.mp hU] at hne
    exact absurd rfl hne

/-- The set defining `Sun m n` is nonempty for every `n ≥ 1`, so `Sun` is a
genuine minimum rather than `Nat.sInf ∅ = 0`. -/
theorem sunflowerProperty_nonempty {m n : ℕ} (hn : 1 ≤ n) :
    {N : ℕ | SunflowerProperty m n N}.Nonempty := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    exact ⟨2, sunflowerProperty_one_petal m⟩
  · exact ⟨(m + 1) * ((n - 1) ^ m * m !) + 1, sunflowerProperty_erdosRado h2⟩

/-- `Sun m n` itself has the defining property. -/
theorem sunflowerProperty_sun {m n : ℕ} (hn : 1 ≤ n) :
    SunflowerProperty m n (Sun m n) :=
  Nat.sInf_mem (sunflowerProperty_nonempty hn)

/-- The Erdős–Rado upper bound on `Sun`, weakened by the factor `m + 1`
(DEVIATION D3). -/
theorem sun_le_erdosRado {m n : ℕ} (hn : 2 ≤ n) :
    Sun m n ≤ (m + 1) * ((n - 1) ^ m * m !) + 1 :=
  sun_le_of_sunflowerProperty (sunflowerProperty_erdosRado hn)

-- ════════════════════════════════════════════════════════════════════
-- LOWER BOUNDS
-- ════════════════════════════════════════════════════════════════════

/-- One set never suffices: the family `{∅}` has cardinality `1`, all of whose
members have cardinality `≤ m`, yet `IsSunflowerWith`'s nonempty-petal clause
rules out `∅` from every sunflower.  (This is exactly the instance
`ErdosRado.lean`'s `not_hasSunflower_of_mem_empty` isolates, and the reason
`Sun m 1 = 2` while A332077 records `Sun(m,1) = 1`.) -/
theorem not_sunflowerProperty_one {m n : ℕ} (hn : 1 ≤ n) :
    ¬ SunflowerProperty m n 1 := by
  intro h
  have hsmall : ∀ S ∈ ({∅} : Finset (Finset (Fin 1))), S.card ≤ m := by
    intro S hS
    rw [Finset.mem_singleton.mp hS, Finset.card_empty]
    exact Nat.zero_le m
  have hone : 1 ≤ ({∅} : Finset (Finset (Fin 1))).card := by
    rw [Finset.card_singleton]
  obtain ⟨sub, hsub, hcard, K, -, hpetal, -⟩ := h 1 {∅} hsmall hone
  obtain ⟨S, hS⟩ : sub.Nonempty := Finset.card_pos.mp (by omega)
  have hS0 : S = ∅ := Finset.mem_singleton.mp (hsub hS)
  have hempty : S \ K = ∅ := by rw [hS0]; exact Finset.empty_sdiff K
  exact hpetal S hS hempty

/-- `Sun` is never `0` or `1`; in particular it is never the `Nat.sInf ∅`
junk value. -/
theorem two_le_sun {m n : ℕ} (hn : 1 ≤ n) : 2 ≤ Sun m n := by
  by_contra hlt
  exact not_sunflowerProperty_one hn
    ((sunflowerProperty_sun hn).mono (by omega : Sun m n ≤ 1))

/-- The `n = 1` column of `Sun`, exactly: `Sun m 1 = 2` for every `m`.

A332077 records `Sun(m,1) = 1` there; the discrepancy is the nonempty-petal
convention of `IsSunflowerWith` and nothing else — `sunOeis_one_petal` below
recovers the source's value `1` from the source's own sunflower notion. -/
theorem sun_one_petal (m : ℕ) : Sun m 1 = 2 :=
  le_antisymm (sun_le_of_sunflowerProperty (sunflowerProperty_one_petal m))
    (two_le_sun le_rfl)

-- ════════════════════════════════════════════════════════════════════
-- THE `n = 2` COLUMN: THE CONVENTION GAP IS UNBOUNDED
-- ════════════════════════════════════════════════════════════════════

/-- The chain `∅ ⊂ {0} ⊂ {0,1} ⊂ ⋯ ⊂ Fin t` inside `Fin t`: `t + 1` distinct
sets, each of cardinality `≤ t`, pairwise comparable under `⊆`.  Comparable
sets never form an `IsSunflowerWith` sunflower — the smaller one's petal is
empty — so this chain witnesses `t + 1 < Sun t 2`. -/
def chainFamily (t : ℕ) : Finset (Finset (Fin t)) :=
  (Finset.range (t + 1)).image
    (fun j => Finset.univ.filter (fun i : Fin t => (i : ℕ) < j))

/-- The chain family on `Fin t` has exactly `t + 1` members. -/
theorem chainFamily_card (t : ℕ) : (chainFamily t).card = t + 1 := by
  have key : ∀ a b : ℕ, b ≤ t → a < b →
      (Finset.univ.filter (fun i : Fin t => (i : ℕ) < a)) ≠
        (Finset.univ.filter (fun i : Fin t => (i : ℕ) < b)) := by
    intro a b hbt hab heq
    have hat : a < t := by omega
    have hmem : (⟨a, hat⟩ : Fin t) ∈
        Finset.univ.filter (fun i : Fin t => (i : ℕ) < b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hab
    rw [← heq] at hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact absurd hmem (lt_irrefl a)
  rw [chainFamily, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd hab (key a b (by omega) h)
  · exact h
  · exact absurd hab.symm (key b a (by omega) h)

/-- Every subset of `Fin t` has at most `t` elements; in particular every
member of `chainFamily t` does. -/
theorem card_le_of_fin {t : ℕ} (S : Finset (Fin t)) : S.card ≤ t := by
  calc S.card ≤ Fintype.card (Fin t) := Finset.card_le_univ S
    _ = t := Fintype.card_fin t

/-- The chain family is totally ordered by inclusion. -/
theorem chainFamily_comparable (t : ℕ) {S T : Finset (Fin t)}
    (hS : S ∈ chainFamily t) (hT : T ∈ chainFamily t) : S ⊆ T ∨ T ⊆ S := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hT
  rcases Nat.le_total a b with h | h
  · refine Or.inl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  · refine Or.inr fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega

/-- A pairwise comparable family carries no `IsSunflowerWith` sunflower with
two petals: if `S ⊆ T` then the pairwise clause forces the kernel to be
`S ∩ T = S`, and then `S`'s petal `S \ S` is empty. -/
theorem not_hasSunflower_two_of_comparable {g : ℕ}
    {family : Finset (Finset (Fin g))}
    (hchain : ∀ S ∈ family, ∀ T ∈ family, S ⊆ T ∨ T ⊆ S) :
    ¬ HasSunflower family 2 := by
  rintro ⟨sub, hsub, hcard, K, -, hpetal, hpair⟩
  obtain ⟨S, T, hST, rfl⟩ := Finset.card_eq_two.mp hcard
  have hSmem : S ∈ ({S, T} : Finset (Finset (Fin g))) := Finset.mem_insert_self S {T}
  have hTmem : T ∈ ({S, T} : Finset (Finset (Fin g))) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self T)
  have hK : S ∩ T = K := hpair S hSmem T hTmem hST
  rcases hchain S (hsub hSmem) T (hsub hTmem) with h | h
  · refine hpetal S hSmem ?_
    rw [← hK, Finset.inter_eq_left.mpr h, Finset.sdiff_self]
  · refine hpetal T hTmem ?_
    rw [← hK, Finset.inter_eq_right.mpr h, Finset.sdiff_self]

/-- `m + 1` sets do not suffice for a two-petal `IsSunflowerWith` sunflower:
the chain `chainFamily m` is a counterexample. -/
theorem not_sunflowerProperty_two_petals (m : ℕ) :
    ¬ SunflowerProperty m 2 (m + 1) := by
  intro h
  refine not_hasSunflower_two_of_comparable
    (fun S hS T hT => chainFamily_comparable m hS hT)
    (h m (chainFamily m) (fun S _ => card_le_of_fin S) ?_)
  rw [chainFamily_card]

/-- `m + 2` sets always suffice: among `m + 2` distinct sets of cardinality
`≤ m` two are incomparable (otherwise `Finset.card` would be injective on the
family, forcing at most `m + 1` members), and an incomparable pair is an
`IsSunflowerWith` sunflower with kernel its intersection. -/
theorem sunflowerProperty_two_petals (m : ℕ) : SunflowerProperty m 2 (m + 2) := by
  intro g family hsmall hcard
  have hex : ∃ S ∈ family, ∃ T ∈ family, ¬ S ⊆ T ∧ ¬ T ⊆ S := by
    by_contra hcon
    push Not at hcon
    have hinj : Set.InjOn (Finset.card : Finset (Fin g) → ℕ) ↑family := by
      intro S hS T hT hcardST
      rcases Classical.em (S ⊆ T) with h | h
      · exact Finset.eq_of_subset_of_card_le h hcardST.ge
      · exact (Finset.eq_of_subset_of_card_le (hcon S hS T hT h) hcardST.le).symm
    have himg : family.image Finset.card ⊆ Finset.range (m + 1) := by
      intro j hj
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hsmall S hS))
    have hle : family.card ≤ m + 1 := by
      calc family.card = (family.image Finset.card).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range (m + 1)).card := Finset.card_le_card himg
        _ = m + 1 := Finset.card_range (m + 1)
    omega
  obtain ⟨S, hS, T, hT, hST, hTS⟩ := hex
  have hne : S ≠ T := fun h => hST (h ▸ Finset.Subset.refl S)
  have hmem : ∀ U ∈ ({S, T} : Finset (Finset (Fin g))), U = S ∨ U = T := by
    intro U hU
    rcases Finset.mem_insert.mp hU with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  refine ⟨{S, T}, ?_, ?_, S ∩ T, ?_, ?_, ?_⟩
  · intro U hU
    rcases hmem U hU with h | h
    · rw [h]; exact hS
    · rw [h]; exact hT
  · rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  · intro U hU
    rcases hmem U hU with h | h
    · rw [h]; exact Finset.inter_subset_left
    · rw [h]; exact Finset.inter_subset_right
  · intro U hU
    rw [ne_eq, Finset.sdiff_eq_empty_iff_subset]
    rcases hmem U hU with h | h
    · rw [h]
      exact fun hsub => hST (hsub.trans Finset.inter_subset_right)
    · rw [h]
      exact fun hsub => hTS (hsub.trans Finset.inter_subset_left)
  · intro U hU V hV hUV
    rcases hmem U hU with hu | hu <;> rcases hmem V hV with hv | hv
    · exact absurd (hu.trans hv.symm) hUV
    · rw [hu, hv]
    · rw [hu, hv]; exact Finset.inter_comm T S
    · exact absurd (hu.trans hv.symm) hUV

/-- The `n = 2` column of `Sun`, exactly: `Sun m 2 = m + 2`.

A332077 records `Sun(m,2) = 2` (formula line "Sun(m,n) = n for n <= 2 and all
m"), recovered here as `sunOeis_two_petals`.  So the gap between the two
sunflower conventions is not a constant: it grows with the uniformity `m`,
which is why `sunflowerConjecture_iff` transfers the conjecture by shifting
the PETAL index rather than by absorbing an additive constant. -/
theorem sun_two_petals (m : ℕ) : Sun m 2 = m + 2 := by
  refine le_antisymm
    (sun_le_of_sunflowerProperty (sunflowerProperty_two_petals m)) ?_
  by_contra hlt
  exact not_sunflowerProperty_two_petals m
    ((sunflowerProperty_sun (by omega)).mono (by omega : Sun m 2 ≤ m + 1))

-- ════════════════════════════════════════════════════════════════════
-- `SunOeis` AGAINST THE TABULATED TERMS
-- ════════════════════════════════════════════════════════════════════

/-- The family of all singletons of `Fin t`: `t` distinct sets, each of
cardinality `1`.  It is the witness that `t` sets can fail to contain a
sunflower with `t + 1` sets, for the trivial reason that they are only `t`. -/
def singletonFamily (t : ℕ) : Finset (Finset (Fin t)) :=
  Finset.univ.image (fun i => ({i} : Finset (Fin t)))

/-- The singleton family on `Fin t` has exactly `t` members. -/
theorem card_singletonFamily (t : ℕ) : (singletonFamily t).card = t := by
  rw [singletonFamily,
    Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_univ, Fintype.card_fin]

/-- Every member of the singleton family is a singleton set. -/
theorem card_mem_singletonFamily (t : ℕ) {S : Finset (Fin t)}
    (hS : S ∈ singletonFamily t) : S.card = 1 := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
  exact Finset.card_singleton i

/-- Fewer than `n` sets can never force a sunflower with `n` sets. -/
theorem not_oeisSunflowerProperty_of_lt {m n N : ℕ} (hm : 1 ≤ m) (hN : N < n) :
    ¬ OeisSunflowerProperty m n N := by
  intro h
  obtain ⟨sub, hsub, hsubcard, -⟩ :=
    h (n - 1) (singletonFamily (n - 1))
      (fun S hS => by rw [card_mem_singletonFamily _ hS]; exact hm)
      (by rw [card_singletonFamily]; omega)
  have hle := Finset.card_le_card hsub
  rw [hsubcard, card_singletonFamily] at hle
  omega

/-- The set of `N` satisfying the OEIS sunflower property is nonempty for `n ≥ 1`. -/
theorem oeisSunflowerProperty_nonempty {m n : ℕ} (hn : 1 ≤ n) :
    {N : ℕ | OeisSunflowerProperty m n N}.Nonempty := by
  obtain ⟨N, hN⟩ := sunflowerProperty_nonempty (m := m) hn
  exact ⟨N, hN.oeis⟩

/-- `SunOeis m n` itself witnesses the OEIS sunflower property. -/
theorem oeisSunflowerProperty_sunOeis {m n : ℕ} (hn : 1 ≤ n) :
    OeisSunflowerProperty m n (SunOeis m n) :=
  Nat.sInf_mem (oeisSunflowerProperty_nonempty hn)

/-- `n ≤ SunOeis m n`: the trivial lower bound, and the guarantee that
`SunOeis` is not the `Nat.sInf ∅` junk value.  (A332077 records the far
stronger `(n-1)^m <= Sun(m,n)`, which is DEVIATION D4.) -/
theorem le_sunOeis {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : n ≤ SunOeis m n := by
  by_contra hlt
  push Not at hlt
  exact not_oeisSunflowerProperty_of_lt hm hlt (oeisSunflowerProperty_sunOeis hn)

/-- One set always contains an A332077 sunflower with one set: the pairwise
condition is vacuous on a singleton. -/
theorem oeisSunflowerProperty_one_petal (m : ℕ) : OeisSunflowerProperty m 1 1 := by
  intro g family _ hcard
  obtain ⟨sub, hsub, hsubcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨sub, hsub, hsubcard, ∅, fun A hA B hB hne =>
    absurd (Finset.card_le_one.mp hsubcard.le A hA B hB) hne⟩

/-- Any two distinct sets form an A332077 sunflower, with kernel their
intersection. -/
theorem oeisSunflowerProperty_two_petals (m : ℕ) : OeisSunflowerProperty m 2 2 := by
  intro g family _ hcard
  obtain ⟨sub, hsub, hsubcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨sub, hsub, hsubcard, ?_⟩
  obtain ⟨S, T, hST, rfl⟩ := Finset.card_eq_two.mp hsubcard
  refine ⟨S ∩ T, ?_⟩
  intro A hA B hB hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact absurd rfl hne
  · rfl
  · exact Finset.inter_comm _ _
  · exact absurd rfl hne

/-- Any `n` distinct sets of cardinality `≤ 1` form an A332077 sunflower with
kernel `∅`: two distinct such sets are disjoint. -/
theorem oeisSunflowerProperty_one_uniformity (n : ℕ) :
    OeisSunflowerProperty 1 n n := by
  intro g family hsmall hcard
  obtain ⟨sub, hsub, hsubcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨sub, hsub, hsubcard, ∅, ?_⟩
  intro S hS T hT hne
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  rw [Finset.mem_inter] at hx
  have hSx : S = {x} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hx.1, fun y hy => Finset.card_le_one.mp (hsmall S (hsub hS)) y hy x hx.1⟩
  have hTx : T = {x} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hx.2, fun y hy => Finset.card_le_one.mp (hsmall T (hsub hT)) y hy x hx.2⟩
  exact hne (hSx.trans hTx.symm)

/-- A332077's `Sun(m,1) = 1`, machine-checked (formula line "Sun(m,n) = n for
n <= 2 and all m").  Compare `sun_one_petal`: the value is `2` under the
nonempty-petal convention. -/
theorem sunOeis_one_petal {m : ℕ} (hm : 1 ≤ m) : SunOeis m 1 = 1 :=
  le_antisymm (sunOeis_le_of_oeisSunflowerProperty (oeisSunflowerProperty_one_petal m))
    (le_sunOeis hm le_rfl)

/-- A332077's `Sun(m,2) = 2`, machine-checked (same formula line). -/
theorem sunOeis_two_petals {m : ℕ} (hm : 1 ≤ m) : SunOeis m 2 = 2 :=
  le_antisymm (sunOeis_le_of_oeisSunflowerProperty (oeisSunflowerProperty_two_petals m))
    (le_sunOeis hm (by omega))

/-- A332077's `Sun(1,n) = n for all n`, machine-checked (formula line
"Sun(1,n) = n for all n: see Examples for explanation"), i.e. the entire first
row of the tabulated array `1, 2, 3, 4, 5, 6, …`. -/
theorem sunOeis_one_uniformity {n : ℕ} (hn : 1 ≤ n) : SunOeis 1 n = n :=
  le_antisymm
    (sunOeis_le_of_oeisSunflowerProperty (oeisSunflowerProperty_one_uniformity n))
    (le_sunOeis le_rfl hn)

-- ════════════════════════════════════════════════════════════════════
-- THE SANDWICH BETWEEN THE TWO CONVENTIONS
-- ════════════════════════════════════════════════════════════════════

/-- The stronger convention needs at least as many sets. -/
theorem sunOeis_le_sun {m n : ℕ} (hn : 1 ≤ n) : SunOeis m n ≤ Sun m n :=
  sunOeis_le_of_oeisSunflowerProperty (sunflowerProperty_sun hn).oeis

/-- One extra petal buys back the nonempty-petal clause: `hasSunflower_of_isOeisSunflower`
turns an A332077 sunflower with `n + 1` sets into an `IsSunflowerWith`
sunflower with `n` sets. -/
theorem sun_le_sunOeis_succ {m n : ℕ} (hn : 1 ≤ n) :
    Sun m n ≤ SunOeis m (n + 1) := by
  refine sun_le_of_sunflowerProperty ?_
  intro g family hsmall hcard
  obtain ⟨sub, hsub, hsubcard, hsf⟩ :=
    oeisSunflowerProperty_sunOeis (m := m) (n := n + 1) (by omega)
      g family hsmall hcard
  exact hasSunflower_of_isOeisSunflower hn hsub (by omega) hsf

-- ════════════════════════════════════════════════════════════════════
-- THE SUNFLOWER CONJECTURE
-- ════════════════════════════════════════════════════════════════════

/-- **Sunflower conjecture**, A332077 formula section, verbatim:
"Sunflower conjecture: Sun(m,n) <= (n*O(1))^m."

The `O(1)` is written as an explicit existential constant, as it must be for
the line to name a single claim: ONE constant `C` serving every `m ≥ 1` and
every `n ≥ 1`.  `1 ≤ m` is not decoration — `sun_two_petals 0` gives
`Sun 0 2 = 2` against `(2 * C) ^ 0 = 1`, and the last `example` of this file
machine-checks that dropping `1 ≤ m` turns the statement FALSE.

OPEN (Erdős #20; A332077 keyword `hard`).  This is the file's single `sorry`
and the reason the file exists.  Everything it needs in order to be a
non-vacuous claim is proved above: `sunflowerProperty_nonempty` (so `Sun` is a
real minimum, not `Nat.sInf ∅`), `two_le_sun` (so `Sun` is never `0`),
`sun_le_erdosRado` (a finite upper bound exists), and
`sunflowerConjecture_iff` (this form and the A332077-faithful form are the
same statement). -/
theorem sunflower_conjecture :
    ∃ C : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Sun m n ≤ (n * C) ^ m := by
  sorry

/-- The conjecture for the `IsSunflowerWith` convention and the conjecture for
A332077's own sunflower notion are the same statement: the sandwich
`SunOeis m n ≤ Sun m n ≤ SunOeis m (n+1)` costs only `C ↦ 2 * C`.  Proved
sorry-free — this is the audit that justifies putting the `sorry` on the
`Sun` form. -/
theorem sunflowerConjecture_iff :
    (∃ C : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Sun m n ≤ (n * C) ^ m) ↔
      (∃ C : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → SunOeis m n ≤ (n * C) ^ m) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun m n hm hn => (sunOeis_le_sun hn).trans (hC m n hm hn)⟩
  · rintro ⟨C, hC⟩
    refine ⟨2 * C, fun m n hm hn => ?_⟩
    have hstep : (n + 1) * C ≤ n * (2 * C) := by
      calc (n + 1) * C ≤ (2 * n) * C := Nat.mul_le_mul_right C (by omega)
        _ = n * (2 * C) := by ring
    calc Sun m n ≤ SunOeis m (n + 1) := sun_le_sunOeis_succ hn
      _ ≤ ((n + 1) * C) ^ m := hC m (n + 1) hm (by omega)
      _ ≤ (n * (2 * C)) ^ m := Nat.pow_le_pow_left hstep m

/-- The sunflower conjecture as A332077 means it, i.e. on A332077's own
sunflower notion.  Derived from `sunflower_conjecture` through
`sunflowerConjecture_iff`; it introduces no `sorry` of its own. -/
theorem sunflower_conjecture_oeis :
    ∃ C : ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → SunOeis m n ≤ (n * C) ^ m :=
  sunflowerConjecture_iff.mp sunflower_conjecture

-- ════════════════════════════════════════════════════════════════════
-- SATISFIABILITY WITNESSES
-- ════════════════════════════════════════════════════════════════════

/-- The hypotheses of `sunflowerProperty_erdosRado` are jointly satisfiable at
a concrete point, and its conclusion is a real (non-vacuous) statement there:
at `m = 1, n = 2` the bound reads `2 * (1 * 1) + 1 = 3`, and three distinct
sets of cardinality `≤ 1` really do contain two disjoint nonempty ones. -/
example : SunflowerProperty 1 2 3 := by
  have h := sunflowerProperty_erdosRado (m := 1) (n := 2) (by norm_num)
  norm_num at h
  exact h

/-- `SunflowerProperty` is inhabited at the `n = 1` column. -/
example : SunflowerProperty 5 1 2 := sunflowerProperty_one_petal 5

/-- …and genuinely fails one step lower, so `Sun 5 1 = 2` is a real minimum. -/
example : ¬ SunflowerProperty 5 1 1 := not_sunflowerProperty_one le_rfl

/-- A tabulated A332077 value, machine-checked: `Sun(1,4) = 4`, the fourth
term of the first row (terms "1,2,1,3,2,1,4,…" read by falling
antidiagonals). -/
example : SunOeis 1 4 = 4 := sunOeis_one_uniformity (by norm_num)

/-- A tabulated A332077 value, machine-checked: `Sun(3,1) = 1`. -/
example : SunOeis 3 1 = 1 := sunOeis_one_petal (by norm_num)

/-- A tabulated A332077 value, machine-checked: `Sun(2,2) = 2`. -/
example : SunOeis 2 2 = 2 := sunOeis_two_petals (by norm_num)

/-- The two conventions really do disagree: `Sun m 1 = 2` while
`SunOeis m 1 = 1`.  The sandwich still holds, as it must. -/
example : SunOeis 3 1 = 1 ∧ Sun 3 1 = 2 ∧ SunOeis 3 1 ≤ Sun 3 1 :=
  ⟨sunOeis_one_petal (by norm_num), sun_one_petal 3,
    sunOeis_le_sun (m := 3) (n := 1) le_rfl⟩

/-- …and the disagreement is unbounded in `m`: at `n = 2` the source's value
is `2` for every `m`, while `Sun m 2 = m + 2`.  Shown at `m = 7`. -/
example : SunOeis 7 2 = 2 ∧ Sun 7 2 = 9 ∧ SunOeis 7 2 ≤ Sun 7 2 :=
  ⟨sunOeis_two_petals (by norm_num), sun_two_petals 7,
    sunOeis_le_sun (m := 7) (n := 2) (by norm_num)⟩

/-- The sandwich `Sun m n ≤ SunOeis m (n+1)` is tight enough to be informative
at `n = 1`: `Sun m 1 = 2 = SunOeis m 2`. -/
example : Sun 4 1 = SunOeis 4 2 :=
  (sun_one_petal 4).trans (sunOeis_two_petals (by norm_num)).symm

/-- Ground truth for `chainFamily`: at `t = 2` it is the chain
`∅ ⊂ {0} ⊂ {0,1}`. -/
example : chainFamily 2 = {∅, {0}, {0, 1}} := by decide

/-- Ground truth for `singletonFamily`: at `t = 3` it is `{{0}, {1}, {2}}`. -/
example : singletonFamily 3 = {{0}, {1}, {2}} := by decide

/-- The guard `1 ≤ m` in `sunflower_conjecture` is load-bearing, not
decoration: dropping it makes the statement FALSE, because `(n * C) ^ 0 = 1`
while `Sun 0 2 = 2`.  (This is the one place where the `IsSunflowerWith`
convention matters for the *shape* of the archived claim: under A332077's own
notion `SunOeis 0 n` would still be `≤ 1` for `n ≤ 1`.) -/
example : ¬ ∃ C : ℕ, ∀ m n : ℕ, 1 ≤ n → Sun m n ≤ (n * C) ^ m := by
  rintro ⟨C, hC⟩
  have hbad := hC 0 2 (by norm_num)
  rw [sun_two_petals 0, pow_zero] at hbad
  omega

-- ════════════════════════════════════════════════════════════════════
-- SIGNATURE AUDIT
-- ════════════════════════════════════════════════════════════════════

#check @IsOeisSunflower
#check @isOeisSunflower_iff_pairwise_inter_eq
#check @IsSunflowerWith.isOeisSunflower
#check @kernel_subset_of_pairwise_inter
#check @hasSunflower_of_isOeisSunflower
#check @HasSunflower.mono_family
#check @HasSunflower.of_le
#check @SunflowerProperty
#check @OeisSunflowerProperty
#check @Sun
#check @SunOeis
#check @SunflowerProperty.mono
#check @OeisSunflowerProperty.mono
#check @SunflowerProperty.oeis
#check @sun_le_of_sunflowerProperty
#check @sunOeis_le_of_oeisSunflowerProperty
#check @sunflowerProperty_erdosRado
#check @sunflowerProperty_one_petal
#check @sunflowerProperty_nonempty
#check @sunflowerProperty_sun
#check @sun_le_erdosRado
#check @not_sunflowerProperty_one
#check @two_le_sun
#check @sun_one_petal
#check @chainFamily
#check @chainFamily_card
#check @card_le_of_fin
#check @chainFamily_comparable
#check @not_hasSunflower_two_of_comparable
#check @not_sunflowerProperty_two_petals
#check @sunflowerProperty_two_petals
#check @sun_two_petals
#check @singletonFamily
#check @card_singletonFamily
#check @card_mem_singletonFamily
#check @not_oeisSunflowerProperty_of_lt
#check @oeisSunflowerProperty_nonempty
#check @oeisSunflowerProperty_sunOeis
#check @le_sunOeis
#check @oeisSunflowerProperty_one_petal
#check @oeisSunflowerProperty_two_petals
#check @oeisSunflowerProperty_one_uniformity
#check @sunOeis_one_petal
#check @sunOeis_two_petals
#check @sunOeis_one_uniformity
#check @sunOeis_le_sun
#check @sun_le_sunOeis_succ
#check @sunflower_conjecture
#check @sunflowerConjecture_iff
#check @sunflower_conjecture_oeis

-- ════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT
--
-- Everything below is `[propext, Classical.choice, Quot.sound]` EXCEPT
-- `sunflower_conjecture` and its consequence `sunflower_conjecture_oeis`,
-- which carry `sorryAx`: that is the single intended `sorry`, the open
-- conjecture itself.
-- ════════════════════════════════════════════════════════════════════

#print axioms isOeisSunflower_iff_pairwise_inter_eq
#print axioms IsSunflowerWith.isOeisSunflower
#print axioms kernel_subset_of_pairwise_inter
#print axioms hasSunflower_of_isOeisSunflower
#print axioms HasSunflower.mono_family
#print axioms HasSunflower.of_le
#print axioms SunflowerProperty.mono
#print axioms OeisSunflowerProperty.mono
#print axioms SunflowerProperty.oeis
#print axioms sun_le_of_sunflowerProperty
#print axioms sunOeis_le_of_oeisSunflowerProperty
#print axioms sunflowerProperty_erdosRado
#print axioms sunflowerProperty_one_petal
#print axioms sunflowerProperty_nonempty
#print axioms sunflowerProperty_sun
#print axioms sun_le_erdosRado
#print axioms not_sunflowerProperty_one
#print axioms two_le_sun
#print axioms sun_one_petal
#print axioms chainFamily_card
#print axioms card_le_of_fin
#print axioms chainFamily_comparable
#print axioms not_hasSunflower_two_of_comparable
#print axioms not_sunflowerProperty_two_petals
#print axioms sunflowerProperty_two_petals
#print axioms sun_two_petals
#print axioms card_singletonFamily
#print axioms card_mem_singletonFamily
#print axioms not_oeisSunflowerProperty_of_lt
#print axioms oeisSunflowerProperty_nonempty
#print axioms oeisSunflowerProperty_sunOeis
#print axioms le_sunOeis
#print axioms oeisSunflowerProperty_one_petal
#print axioms oeisSunflowerProperty_two_petals
#print axioms oeisSunflowerProperty_one_uniformity
#print axioms sunOeis_one_petal
#print axioms sunOeis_two_petals
#print axioms sunOeis_one_uniformity
#print axioms sunOeis_le_sun
#print axioms sun_le_sunOeis_succ
#print axioms sunflowerConjecture_iff
#print axioms sunflower_conjecture
#print axioms sunflower_conjecture_oeis
