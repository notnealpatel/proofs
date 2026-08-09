/-
  The general fixed-divisor theorem for affine-exponential families
  `n ↦ A · b ^ n + B` over ℤ, for an arbitrary base `b : ℕ`.
  THE DELIVERABLE of this lane.

  ── What this file is ───────────────────────────────────────────────
  A covering system `{a_i (mod d_i)}` together with, for each class, a
  divisor `p_i > 1` satisfying

      `b ^ d_i ≡ 1 (mod p_i)`   and   `p_i ∣ A · b ^ a_i + B`

  forces `A · b ^ n + B` to have a divisor in `{p_i}` for *every*
  `n : ℕ`.  That is the entire mathematical content of the Sierpiński,
  Riesel and Erdős-1950 constructions and of their base-`b`
  generalizations, and it is stated here once, for arbitrary `b : ℕ`,
  arbitrary `A B : ℤ`, arbitrary covering data, and arbitrary divisors.

  The base parameter costs nothing.  The per-class step is unchanged —
  only `b ^ d ≡ 1 (mod p)` is ever used about `b`, never primitivity of
  the order, never `gcd (b, p) = 1`, never `2 ≤ b`.  Decidability
  survives verbatim: `b ^ d % p = 1 % p` is as ground a check as
  `2 ^ d % p = 1 % p` (`isFixedDivisorSystemBase_iff`).

  The applications are the instantiations:

    | family              | `b`  | `A`  | `B` | file                              |
    | ------------------- | ---- | ---- | --- | --------------------------------- |
    | `k · 2 ^ n + 1`     | `2`  | `k`  | `1` | `Erdos.Covering.Sierpinski`       |
    | `k · 2 ^ n - 1`     | `2`  | `k`  | `-1`| `Erdos.Covering.Riesel`           |
    | `m - 2 ^ n`         | `2`  | `-1` | `m` | `Erdos.Covering.Erdos1950Instance`|
    | `k · b ^ n + 1`     | any  | `k`  | `1` | `Erdos.Covering.Sierpinski`       |
    | `k · b ^ n - 1`     | any  | `k`  | `-1`| `Erdos.Covering.Riesel`           |

  ── Two layers, one proof ───────────────────────────────────────────
  `IsFixedDivisorSystemBase b A B T` (§1) is the general certificate;
  `IsFixedDivisorSystem A B T` is the base-2 one that predates it and
  that the three classical applications consume.  §3 proves the general
  theorem; §4 obtains every base-2 statement — verbatim, with its
  original name and signature — as the `b = 2` instance along the
  bridge `isFixedDivisorSystem_iff_base_two`.  No mathematics is proved
  twice, and no downstream file changed.

  One translation exists only in the general layer:
  `IsFixedDivisorSystemBase.of_modEq_base` moves the *base* along a
  congruence modulo the divisors, turning a single certificate into a
  statement about infinitely many bases.

  ── Source pins (verbatim, 2026-08-05) ──────────────────────────────
  The base-`b` notions are pinned to primary sources, quoted here and
  re-quoted at the statements they justify.

  * Wikipedia, "Riesel number", § "Riesel number base b"
    (`goof wiki article "Riesel number"`):
      "One can generalize the Riesel problem to an integer base b ≥ 2.
       A **Riesel number base b** is a positive integer k such that
       gcd(k − 1, b − 1) = 1."
      "In the following list, we only consider those positive integers
       k such that gcd(k − 1, b − 1) = 1, and all integer n must be
       ≥ 1."
      "Example 1: All numbers congruent to 84687 mod 10124569 and not
       congruent to 1 mod 5 are Riesel numbers base 6, because of the
       covering set {7, 13, 31, 37, 97}."
      "Example 2: 6 is a Riesel number to all bases b congruent to 34
       mod 35, because if b is congruent to 34 mod 35, then 6×b^n − 1
       is divisible by 5 for all even n and divisible by 7 for all odd
       n."
  * OEIS A273987 (`goof oeis show A273987`), name: "Smallest Riesel
    number to base n."; terms begin
    "509203,63064644938,9,346802,84687,408034255082,14,4,10176,…";
    comment: "a(2), a(3), a(5), a(6), a(7), a(10), a(15), a(22),
    a(23), a(30), ... are only conjectural (see links)."
  * OEIS A123159 (`goof oeis show A123159`), name: "Conjectured
    smallest Sierpiński numbers of the second kind S, base
    b=2,3,4,5,..., where S*b^n+1 is composite for all n>=1 and
    gcd(S+1, b-1) = 1."; terms begin
    "78557,125050976086,66741,159986,174308,1112646039348,1,2344,
    9175,1490,521,132,4,…".

  Both base-`b` sequences are conjectural at their headline entries and
  neither is claimed here; what is claimed is the certified direction —
  that the pinned witnesses ARE Riesel/Sierpiński numbers to their
  bases — never that they are the smallest.

  ── This file imports none of them ──────────────────────────────────
  The framework stands on `Erdos.Covering.Basic` and Mathlib alone.
  In particular it does **not** import
  `Erdos.Covering.NotTwoPowerPlusPrime`: the retrofit showing that
  file's bespoke fixed-divisor argument to be the `A = -1`, `B = m`
  instance lives in the leaf module `Erdos.Covering.Erdos1950Instance`,
  which imports both.  The dependency graph is

      Basic ──▸ FixedDivisor ──▸ { Sierpinski, Riesel }
        │             │
        │             └──────────▸ Erdos1950Instance ◂── NotTwoPowerPlusPrime
        └──────────────────────────────────────────────┘

  so the general theorem is not an after-the-fact generalization of any
  single proof.

  ── Prior art ───────────────────────────────────────────────────────
  Cowles and Gamboa, "Verifying Sierpiński and Riesel Numbers in ACL2",
  EPTCS 70 (2011), 31–39, arXiv:1110.4671, machine-verified in ACL2
  that `78557` is a Sierpiński number and `509203` is a Riesel number
  (`books/workshops/2011/cowles-gamboa-sierpinski/support/`
  `verifying-macros.lisp`, lines 771 and 813).  Their abstract is
  explicit that the artefact is per-number: "Given a k and its cover,
  ACL2 is used to systematically verify that each integer of the given
  form has a non-trivial factor in the cover"; the macro that generates
  the per-number proof obligations is itself unverified.  The general
  criterion — covering system plus paired divisors implies fixed
  divisor — is what is formalized here.  A survey on 2026-07-31 of
  Mathlib, google-deepmind/formal-conjectures, plby/lean-proofs and the
  Isabelle AFP found no statement of it in any proof assistant.
  Priority on the two concrete numbers belongs to Cowles–Gamboa, and
  `78557` additionally has a bespoke `native_decide` proof in
  formal-conjectures; see the application files, which say so.

  ── Encoding ────────────────────────────────────────────────────────
  The certificate is a `Finset (ℕ × ℕ × ℕ)` of triples `(a, d, p)`:
  residue, modulus, divisor.  Carrying the divisor inside the Finset —
  rather than a `Finset (ℕ × ℕ)` plus a partner function `ℕ × ℕ → ℕ` —
  makes every concrete certificate a single Finset literal and every
  hypothesis a bounded `∀ t ∈ T`, hence `decide`-able with no function
  definition to elaborate.  The projection `residueClasses` recovers
  the `Finset (ℕ × ℕ)` that `Erdos.Covering.Basic` consumes, so the
  coverage check still routes through the proved equivalence
  `covers_iff_forall_range`.

  ── Contents ────────────────────────────────────────────────────────
  * `residueClasses`, `fixedDivisors` — the two projections of a
    certificate, with ground checks.
  * `Composite` — `1 < n ∧ ¬ n.Prime`, matching `Nat.Composite` of
    google-deepmind/formal-conjectures.
  * `IsFixedDivisorSystem A B T` — the base-2 certificate predicate.
  * `IsFixedDivisorSystemBase b A B T` — the base-`b` one.
  * `covers_residueClasses_iff_forall_range`,
    `isFixedDivisorSystem_iff`, `isFixedDivisorSystemBase_iff` — the
    `decide`-able characterizations.
  * `isFixedDivisorSystem_iff_base_two` — the bridge between the two
    layers.
  * `pow_intModEq_pow_mod`, `pow_intModEq_of_mod_eq` — the order
    bridge: `b ^ n (mod p)` depends only on `n mod d`.
  * `dvd_affine_pow_of_mod_eq` — the per-class step, for a single
    triple `(a, d, p)`.
  * `IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd` — **the
    general theorem**.
  * `IsFixedDivisorSystemBase.composite`, `.not_prime` — the
    compositeness corollary.
  * `IsFixedDivisorSystemBase.of_dvd_sub_const`, `.of_dvd_sub_coeff`,
    `.of_modEq_base`, `intCast_dvd_sub_of_mod_eq` — translation: one
    certificate serves a whole arithmetic progression in `A`, in `B`,
    or in the base `b`.
  * §4 — the base-2 layer: `two_pow_intModEq_pow_mod`,
    `two_pow_intModEq_of_mod_eq`, `dvd_affine_two_pow_of_mod_eq`,
    `IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd`, `.nonempty`,
    `.composite`, `.not_prime`, `.of_dvd_sub_const`,
    `.of_dvd_sub_coeff` — each the `b = 2` instance of its §3 or §5
    original, with the statement it always had.
  * §6 — drop-one negative controls. Fields (b) `covers`,
    (c) `two_pow_modEq_one` and (d) `divisor_dvd` are each shown
    necessary for the general theorem by a certificate satisfying the
    other three at which its conclusion FAILS. Field (a)
    `one_lt_divisor` is different and is documented as such at the
    control: it is NOT in the proof cone of
    `exists_mem_fixedDivisors_dvd`, which stays true without it. It is
    load-bearing for `.composite`/`.not_prime`, and for the predicate
    being a non-trivial certificate at all. Control (e) shows the base
    parameter is not inert: Selfridge's certificate is valid in base
    `2` and false in base `3`.
  * §7 — satisfiability: four concrete models, two in base `2` with
    opposite sign patterns, one in base `6` and one in base `14`, at
    which all four fields hold jointly.

  Axiom audit: see the `#print axioms` block at the end.  Every
  declaration is sorry-free.  No `native_decide`, no custom axioms.
-/

import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 CERTIFICATES: DEFINITIONS
-- ════════════════════════════════════════════════════════════════════

/-- The residue classes of a certificate `T : Finset (ℕ × ℕ × ℕ)` of
    triples `(a, d, p)`: forget the divisor, keeping the pair
    `(a, d)` that `Erdos.Covering.Basic` consumes. -/
def residueClasses (T : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.image fun t => (t.1, t.2.1)

/-- The divisors of a certificate `T : Finset (ℕ × ℕ × ℕ)` of triples
    `(a, d, p)`: forget the class, keeping `p`.  In the classical
    applications these are the primes of the *covering set*. -/
def fixedDivisors (T : Finset (ℕ × ℕ × ℕ)) : Finset ℕ :=
  T.image fun t => t.2.2

/-- `n` is composite: `1 < n` and `n` is not prime.  This is the shape
    of `Nat.Composite` in google-deepmind/formal-conjectures
    (`FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean`,
    `abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime`), which
    current Mathlib does not provide. -/
def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- Membership in `residueClasses`. -/
theorem mem_residueClasses {T : Finset (ℕ × ℕ × ℕ)} {q : ℕ × ℕ} :
    q ∈ residueClasses T ↔ ∃ t ∈ T, (t.1, t.2.1) = q :=
  Finset.mem_image

/-- Membership in `fixedDivisors`. -/
theorem mem_fixedDivisors {T : Finset (ℕ × ℕ × ℕ)} {p : ℕ} :
    p ∈ fixedDivisors T ↔ ∃ t ∈ T, t.2.2 = p :=
  Finset.mem_image

-- Ground checks for the two projections and for `Composite`, on the
-- Sierpiński certificate of `Erdos.Covering.Sierpinski`.
example :
    residueClasses {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19),
      (27, 36, 37), (3, 9, 73)} =
      {(0, 2), (1, 4), (1, 3), (11, 12), (15, 18), (27, 36), (3, 9)} := by decide

example :
    fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19),
      (27, 36, 37), (3, 9, 73)} = {3, 5, 7, 13, 19, 37, 73} := by decide

-- The projections collapse repeats, as images do: two classes sharing
-- a divisor contribute one divisor.
example : fixedDivisors {(0, 2, 3), (1, 2, 3)} = {3} := by decide
example : residueClasses {(0, 2, 3), (0, 2, 5)} = {(0, 2)} := by decide

-- `Composite` at the boundary: `0`, `1`, and the primes are excluded.
example : Composite 4 := ⟨by norm_num, by norm_num⟩
example : Composite 9 := ⟨by norm_num, by norm_num⟩
example : ¬ Composite 0 := fun h => absurd h.1 (by norm_num)
example : ¬ Composite 1 := fun h => absurd h.1 (by norm_num)
example : ¬ Composite 2 := fun h => h.2 (by norm_num)
example : ¬ Composite 7 := fun h => h.2 (by norm_num)

/-- **Fixed-divisor certificate** for the family `n ↦ A · 2 ^ n + B`.

    `T` is a finite set of triples `(a, d, p)` — residue, modulus,
    divisor — such that

    * every divisor exceeds `1` (without this the certificate `{(0,1,1)}`
      would satisfy the remaining fields for *every* `A` and `B`,
      making the certificate vacuous as a certificate even though
      `exists_mem_fixedDivisors_dvd` itself survives its removal;
      see the negative control (a) in §5);
    * the classes `a (mod d)` cover ℤ;
    * `2 ^ d ≡ 1 (mod p)`, i.e. `d` is a multiple of the multiplicative
      order of `2` mod `p` — minimality is never needed;
    * `p ∣ A · 2 ^ a + B`, the base case of the class.

    `IsFixedDivisorSystem A B T` says exactly that `T` certifies a fixed
    divisor for `A · 2 ^ n + B`; the theorem is
    `IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd`. -/
structure IsFixedDivisorSystem (A B : ℤ) (T : Finset (ℕ × ℕ × ℕ)) : Prop where
  /-- Every divisor is strictly greater than `1`. -/
  one_lt_divisor : ∀ t ∈ T, 1 < t.2.2
  /-- The residue classes `a (mod d)` cover every integer. -/
  covers : Covers (residueClasses T)
  /-- `d` annihilates `2` mod `p`: `2 ^ d ≡ 1 (mod p)`. -/
  two_pow_modEq_one : ∀ t ∈ T, 2 ^ t.2.1 ≡ 1 [MOD t.2.2]
  /-- `p` divides the family at the base exponent `a` of its class. -/
  divisor_dvd : ∀ t ∈ T, (t.2.2 : ℤ) ∣ A * 2 ^ t.1 + B

/-- **Fixed-divisor certificate in base `b`** for the family
    `n ↦ A · b ^ n + B`.  This is `IsFixedDivisorSystem` with the
    literal `2` replaced by an arbitrary base `b : ℕ`; the base-2
    predicate is its `b = 2` instance
    (`isFixedDivisorSystem_iff_base_two`), and every theorem about it
    below is proved once, in base `b`, and specialized.

    `T` is a finite set of triples `(a, d, p)` — residue, modulus,
    divisor — such that

    * every divisor exceeds `1`;
    * the classes `a (mod d)` cover ℤ;
    * `b ^ d ≡ 1 (mod p)`, i.e. `d` is a multiple of the multiplicative
      order of `b` mod `p` — minimality is never needed.  Coprimality
      of `b` and `p` is nowhere assumed: for `1 ≤ d` the congruence
      already implies it, and for `d = 0` it is not wanted, since the
      class `a (mod 0)` is the singleton `{a}` and nothing beyond the
      base divisibility below is used on it;
    * `p ∣ A · b ^ a + B`, the base case of the class.

    No hypothesis on `b` is needed for the theorem
    `IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd`: at `b = 0`
    and `b = 1` the predicate is still meaningful, merely degenerate.
    The applications (`Erdos.Covering.Sierpinski`,
    `Erdos.Covering.Riesel`) carry `2 ≤ b` where they need it. -/
structure IsFixedDivisorSystemBase (b : ℕ) (A B : ℤ)
    (T : Finset (ℕ × ℕ × ℕ)) : Prop where
  /-- Every divisor is strictly greater than `1`. -/
  one_lt_divisor : ∀ t ∈ T, 1 < t.2.2
  /-- The residue classes `a (mod d)` cover every integer. -/
  covers : Covers (residueClasses T)
  /-- `d` annihilates `b` mod `p`: `b ^ d ≡ 1 (mod p)`. -/
  pow_modEq_one : ∀ t ∈ T, b ^ t.2.1 ≡ 1 [MOD t.2.2]
  /-- `p` divides the family at the base exponent `a` of its class. -/
  divisor_dvd : ∀ t ∈ T, (t.2.2 : ℤ) ∣ A * (b : ℤ) ^ t.1 + B

-- ════════════════════════════════════════════════════════════════════
-- §2 DECIDABLE CHARACTERIZATION
-- ════════════════════════════════════════════════════════════════════

/-- Coverage by the classes of a certificate, reduced to the finite
    check on `0, …, L - 1` for any positive common multiple `L` of the
    moduli.  This is `Erdos.Covering.covers_iff_forall_range` composed
    with the image projection, restated over the triples so that no
    `Finset.image` appears in the `decide`-able side. -/
theorem covers_residueClasses_iff_forall_range {T : Finset (ℕ × ℕ × ℕ)}
    (L : ℕ) (hL : 0 < L) (hdvd : ∀ t ∈ T, t.2.1 ∣ L) :
    Covers (residueClasses T) ↔
      ∀ r ∈ Finset.range L, ∃ t ∈ T, r % t.2.1 = t.1 % t.2.1 := by
  have hdvd' : ∀ q ∈ residueClasses T, q.2 ∣ L := by
    intro q hq
    obtain ⟨t, htT, rfl⟩ := mem_residueClasses.mp hq
    exact hdvd t htT
  rw [covers_iff_forall_range L hL hdvd']
  constructor
  · intro hf r hr
    obtain ⟨q, hqC, hq⟩ := hf r hr
    obtain ⟨t, htT, rfl⟩ := mem_residueClasses.mp hqC
    exact ⟨t, htT, hq⟩
  · intro hf r hr
    obtain ⟨t, htT, ht⟩ := hf r hr
    exact ⟨(t.1, t.2.1), mem_residueClasses.mpr ⟨t, htT, rfl⟩, ht⟩

/-- Decidable characterization of `IsFixedDivisorSystem`, for any
    positive common multiple `L` of the moduli: all four fields become
    bounded quantifications over `T` and `Finset.range L`, hence
    checkable by kernel `decide`. -/
theorem isFixedDivisorSystem_iff (A B : ℤ) (T : Finset (ℕ × ℕ × ℕ)) (L : ℕ)
    (hL : 0 < L) (hdvd : ∀ t ∈ T, t.2.1 ∣ L) :
    IsFixedDivisorSystem A B T ↔
      (∀ t ∈ T, 1 < t.2.2) ∧
        (∀ r ∈ Finset.range L, ∃ t ∈ T, r % t.2.1 = t.1 % t.2.1) ∧
          (∀ t ∈ T, 2 ^ t.2.1 % t.2.2 = 1 % t.2.2) ∧
            ∀ t ∈ T, (t.2.2 : ℤ) ∣ A * 2 ^ t.1 + B := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (covers_residueClasses_iff_forall_range L hL hdvd).mp h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (covers_residueClasses_iff_forall_range L hL hdvd).mpr h2, h3, h4⟩

/-- Decidable characterization of `IsFixedDivisorSystemBase`, for any
    positive common multiple `L` of the moduli: all four fields become
    bounded quantifications over `T` and `Finset.range L`, hence
    checkable by kernel `decide`.  Generalizing the base costs nothing
    here — `b ^ d % p = 1 % p` is as ground a check as `2 ^ d % p`. -/
theorem isFixedDivisorSystemBase_iff (b : ℕ) (A B : ℤ) (T : Finset (ℕ × ℕ × ℕ))
    (L : ℕ) (hL : 0 < L) (hdvd : ∀ t ∈ T, t.2.1 ∣ L) :
    IsFixedDivisorSystemBase b A B T ↔
      (∀ t ∈ T, 1 < t.2.2) ∧
        (∀ r ∈ Finset.range L, ∃ t ∈ T, r % t.2.1 = t.1 % t.2.1) ∧
          (∀ t ∈ T, b ^ t.2.1 % t.2.2 = 1 % t.2.2) ∧
            ∀ t ∈ T, (t.2.2 : ℤ) ∣ A * (b : ℤ) ^ t.1 + B := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (covers_residueClasses_iff_forall_range L hL hdvd).mp h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (covers_residueClasses_iff_forall_range L hL hdvd).mpr h2, h3, h4⟩

/-- The base-2 predicate is the `b = 2` instance of the base-`b` one.
    The two differ only in how the numeral `2` reaches ℤ — as the
    literal `(2 : ℤ)` on the left, as the cast `((2 : ℕ) : ℤ)` on the
    right — so this is the bridge along which every base-2 theorem of
    §4 is obtained from its base-`b` original in §3. -/
theorem isFixedDivisorSystem_iff_base_two {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)} :
    IsFixedDivisorSystem A B T ↔ IsFixedDivisorSystemBase 2 A B T := by
  have hcast : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun t ht => ?_⟩
    rw [hcast]
    exact h4 t ht
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun t ht => ?_⟩
    have hdvd := h4 t ht
    rwa [hcast] at hdvd

-- ════════════════════════════════════════════════════════════════════
-- §3 THE GENERAL THEOREM, IN BASE `b`
-- ════════════════════════════════════════════════════════════════════

/-- If `b ^ d ≡ 1 (mod p)` then `b ^ m (mod p)` depends only on
    `m mod d`.  No positivity hypothesis on `d` is needed: for `d = 0`
    the statement is `b ^ m ≡ b ^ m`.  None on `b` either. -/
theorem pow_intModEq_pow_mod {b p d : ℕ} (hpow : b ^ d ≡ 1 [MOD p]) (m : ℕ) :
    (b : ℤ) ^ m ≡ (b : ℤ) ^ (m % d) [ZMOD (p : ℤ)] := by
  have hpowZ : (b : ℤ) ^ d ≡ 1 [ZMOD (p : ℤ)] := by
    have hcast := Int.natCast_modEq_iff.mpr hpow
    push_cast at hcast
    exact hcast
  conv_lhs => rw [← Nat.div_add_mod m d, pow_add, pow_mul]
  calc ((b : ℤ) ^ d) ^ (m / d) * (b : ℤ) ^ (m % d)
      ≡ 1 ^ (m / d) * (b : ℤ) ^ (m % d) [ZMOD (p : ℤ)] :=
        Int.ModEq.mul (hpowZ.pow _) (Int.ModEq.refl _)
    _ = (b : ℤ) ^ (m % d) := by rw [one_pow, one_mul]

/-- Two exponents in the same class mod `d` give congruent powers of
    `b` mod `p`, whenever `b ^ d ≡ 1 (mod p)`.  The residue `a` need
    not be reduced mod `d`. -/
theorem pow_intModEq_of_mod_eq {b p d a n : ℕ} (hpow : b ^ d ≡ 1 [MOD p])
    (h : n % d = a % d) : (b : ℤ) ^ n ≡ (b : ℤ) ^ a [ZMOD (p : ℤ)] := by
  calc (b : ℤ) ^ n ≡ (b : ℤ) ^ (n % d) [ZMOD (p : ℤ)] := pow_intModEq_pow_mod hpow n
    _ = (b : ℤ) ^ (a % d) := by rw [h]
    _ ≡ (b : ℤ) ^ a [ZMOD (p : ℤ)] := (pow_intModEq_pow_mod hpow a).symm

/-- **One class, one divisor** — the per-class step, stated for a
    single triple `(a, d, p)`, arbitrary base `b` and arbitrary
    `A B : ℤ`.  If `b ^ d ≡ 1 (mod p)` and `p` divides the family at
    the base exponent `a`, then `p` divides it at every exponent
    `n ≡ a (mod d)`.

    This is the sole engine of the general theorem, and the step the
    base generalization leaves entirely unchanged. -/
theorem dvd_affine_pow_of_mod_eq {A B : ℤ} {b p d a n : ℕ}
    (hpow : b ^ d ≡ 1 [MOD p]) (hbase : (p : ℤ) ∣ A * (b : ℤ) ^ a + B)
    (hn : n % d = a % d) : (p : ℤ) ∣ A * (b : ℤ) ^ n + B := by
  have hfam : A * (b : ℤ) ^ n + B ≡ A * (b : ℤ) ^ a + B [ZMOD (p : ℤ)] :=
    ((pow_intModEq_of_mod_eq hpow hn).mul_left A).add_right B
  exact Int.modEq_zero_iff_dvd.mp (hfam.trans (Int.modEq_zero_iff_dvd.mpr hbase))

/-- **The general fixed-divisor theorem, in base `b`.**  If `T`
    certifies a fixed divisor for the family `n ↦ A · b ^ n + B` — its
    classes cover ℤ, each modulus `d` satisfies `b ^ d ≡ 1 (mod p)` for
    its partner divisor `p`, and `p ∣ A · b ^ a + B` at the base
    exponent — then for *every* exponent `n` some `p ∈ fixedDivisors T`
    divides `A · b ^ n + B`.

    Stated over ℤ so that `B = -1` (Riesel) and `A = -1` (Erdős 1950)
    are literal instances with no ℕ-subtraction guard. -/
theorem IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd {b : ℕ} {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T) (n : ℕ) :
    ∃ p ∈ fixedDivisors T, (p : ℤ) ∣ A * (b : ℤ) ^ n + B := by
  -- Pick the class of the certificate containing the exponent `n`.
  obtain ⟨q, hqC, hcong⟩ := h.covers (n : ℤ)
  obtain ⟨t, htT, rfl⟩ := mem_residueClasses.mp hqC
  have hmod : n % t.2.1 = t.1 % t.2.1 := Int.natCast_modEq_iff.mp hcong
  exact ⟨t.2.2, mem_fixedDivisors.mpr ⟨t, htT, rfl⟩,
    dvd_affine_pow_of_mod_eq (h.pow_modEq_one t htT) (h.divisor_dvd t htT) hmod⟩

/-- A certificate is nonempty: some class must contain the exponent
    `0`. -/
theorem IsFixedDivisorSystemBase.nonempty {b : ℕ} {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T) :
    T.Nonempty := by
  obtain ⟨q, hqC, -⟩ := h.covers 0
  obtain ⟨t, htT, -⟩ := mem_residueClasses.mp hqC
  exact ⟨t, htT⟩

/-- **Compositeness corollary, base `b`.**  If `N : ℕ` is a value of
    the certified family, `(N : ℤ) = A · b ^ n + B`, and `N` exceeds a
    bound `M` on the divisors of the certificate, then `N` is
    composite: it is a multiple of some `p` with `1 < p ≤ M < N`.

    The bound is passed as an explicit `M` rather than
    `(fixedDivisors T).max'` so that no nonemptiness side condition
    leaks into the statement.  `M < N` is not cosmetic: in base `14`
    the certificate `{(1, 2, 3), (0, 2, 5)}` for `4 · 14 ^ n + 1` has
    `M = 5` and the value at `n = 0` is `5` itself, which is prime.
    See `Erdos.Covering.not_composite_four_mul_fourteen_pow_zero_add_one`
    in `Erdos.Covering.Sierpinski` §6. -/
theorem IsFixedDivisorSystemBase.composite {b : ℕ} {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T) {M N n : ℕ}
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hN : (N : ℤ) = A * (b : ℤ) ^ n + B)
    (hMN : M < N) : Composite N := by
  obtain ⟨p, hp, hdvd⟩ := h.exists_mem_fixedDivisors_dvd n
  obtain ⟨t, htT, rfl⟩ := mem_fixedDivisors.mp hp
  have hp1 : 1 < t.2.2 := h.one_lt_divisor t htT
  have hpM : t.2.2 ≤ M := hM t.2.2 hp
  have hpN : t.2.2 ∣ N := by
    have hZ : ((t.2.2 : ℕ) : ℤ) ∣ (N : ℤ) := by rw [hN]; exact hdvd
    exact_mod_cast hZ
  refine ⟨by omega, fun hprime => ?_⟩
  rcases hprime.eq_one_or_self_of_dvd t.2.2 hpN with h1 | h2 <;> omega

/-- **Compositeness corollary, base `b`, primality phrasing.**  Under
    the hypotheses of `IsFixedDivisorSystemBase.composite`, `N` is not
    prime. -/
theorem IsFixedDivisorSystemBase.not_prime {b : ℕ} {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T) {M N n : ℕ}
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hN : (N : ℤ) = A * (b : ℤ) ^ n + B)
    (hMN : M < N) : ¬ N.Prime :=
  (h.composite hM hN hMN).2

-- ════════════════════════════════════════════════════════════════════
-- §4 THE BASE-2 LAYER, AS THE `b = 2` INSTANCE
-- ════════════════════════════════════════════════════════════════════

/-! Every statement in this section is the one that was proved here
before the base parameter existed, verbatim; only the proofs changed,
and each is now a one-line specialization of its §3 original along
`isFixedDivisorSystem_iff_base_two`.  The three applications
(`Erdos.Covering.Sierpinski`, `Erdos.Covering.Riesel`,
`Erdos.Covering.Erdos1950Instance`) consume this section unchanged. -/

/-- The cast that separates the two layers: the ℕ-numeral `2` sent to
    ℤ is the ℤ-numeral `2`. -/
private theorem natCast_two_int : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num

/-- If `2 ^ d ≡ 1 (mod p)` then `2 ^ m (mod p)` depends only on
    `m mod d`.  No positivity hypothesis on `d` is needed: for `d = 0`
    the statement is `2 ^ m ≡ 2 ^ m`.  The `b = 2` case of
    `pow_intModEq_pow_mod`. -/
theorem two_pow_intModEq_pow_mod {p d : ℕ} (hpow : 2 ^ d ≡ 1 [MOD p]) (m : ℕ) :
    (2 : ℤ) ^ m ≡ 2 ^ (m % d) [ZMOD (p : ℤ)] := by
  have h := pow_intModEq_pow_mod (b := 2) hpow m
  rwa [natCast_two_int] at h

/-- Two exponents in the same class mod `d` give congruent powers of
    `2` mod `p`, whenever `2 ^ d ≡ 1 (mod p)`.  The residue `a` need
    not be reduced mod `d`.  The `b = 2` case of
    `pow_intModEq_of_mod_eq`. -/
theorem two_pow_intModEq_of_mod_eq {p d a n : ℕ} (hpow : 2 ^ d ≡ 1 [MOD p])
    (h : n % d = a % d) : (2 : ℤ) ^ n ≡ 2 ^ a [ZMOD (p : ℤ)] := by
  have hb := pow_intModEq_of_mod_eq (b := 2) hpow h
  rwa [natCast_two_int] at hb

/-- **One class, one divisor** — the per-class step, stated for a
    single triple `(a, d, p)` and arbitrary `A B : ℤ`.  If
    `2 ^ d ≡ 1 (mod p)` and `p` divides the family at the base exponent
    `a`, then `p` divides it at every exponent `n ≡ a (mod d)`.

    This generalizes `Erdos.Covering.dvd_sub_two_pow_of_modEq` of
    `NotTwoPowerPlusPrime.lean`, which is the case `A = -1`, `B = m`;
    the re-derivation is `dvd_sub_two_pow_of_modEq_of_general` in
    `Erdos.Covering.Erdos1950Instance`.  The `b = 2` case of
    `dvd_affine_pow_of_mod_eq`. -/
theorem dvd_affine_two_pow_of_mod_eq {A B : ℤ} {p d a n : ℕ}
    (hpow : 2 ^ d ≡ 1 [MOD p]) (hbase : (p : ℤ) ∣ A * 2 ^ a + B)
    (hn : n % d = a % d) : (p : ℤ) ∣ A * 2 ^ n + B := by
  have hb : (p : ℤ) ∣ A * ((2 : ℕ) : ℤ) ^ a + B := by rwa [natCast_two_int]
  have hmain := dvd_affine_pow_of_mod_eq (b := 2) hpow hb hn
  rwa [natCast_two_int] at hmain

/-- **The general fixed-divisor theorem.**  If `T` certifies a fixed
    divisor for the family `n ↦ A · 2 ^ n + B` — its classes cover ℤ,
    each modulus `d` satisfies `2 ^ d ≡ 1 (mod p)` for its partner
    divisor `p`, and `p ∣ A · 2 ^ a + B` at the base exponent — then
    for *every* exponent `n` some `p ∈ fixedDivisors T` divides
    `A · 2 ^ n + B`.

    Stated over ℤ so that `B = -1` (Riesel) and `A = -1` (Erdős 1950)
    are literal instances with no ℕ-subtraction guard.  The `b = 2`
    case of `IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd`. -/
theorem IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystem A B T) (n : ℕ) :
    ∃ p ∈ fixedDivisors T, (p : ℤ) ∣ A * 2 ^ n + B := by
  obtain ⟨p, hp, hdvd⟩ :=
    (isFixedDivisorSystem_iff_base_two.mp h).exists_mem_fixedDivisors_dvd n
  exact ⟨p, hp, by rwa [natCast_two_int] at hdvd⟩

/-- A certificate is nonempty: some class must contain the exponent
    `0`. -/
theorem IsFixedDivisorSystem.nonempty {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)}
    (h : IsFixedDivisorSystem A B T) : T.Nonempty :=
  (isFixedDivisorSystem_iff_base_two.mp h).nonempty

/-- **Compositeness corollary.**  If `N : ℕ` is a value of the
    certified family, `(N : ℤ) = A · 2 ^ n + B`, and `N` exceeds a
    bound `M` on the divisors of the certificate, then `N` is
    composite: it is a multiple of some `p` with `1 < p ≤ M < N`.

    The bound is passed as an explicit `M` rather than
    `(fixedDivisors T).max'` so that no nonemptiness side condition
    leaks into the statement. -/
theorem IsFixedDivisorSystem.composite {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)}
    (h : IsFixedDivisorSystem A B T) {M N n : ℕ}
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hN : (N : ℤ) = A * 2 ^ n + B)
    (hMN : M < N) : Composite N :=
  (isFixedDivisorSystem_iff_base_two.mp h).composite hM
    (by rw [hN, natCast_two_int]) hMN

/-- **Compositeness corollary, primality phrasing.**  Under the
    hypotheses of `IsFixedDivisorSystem.composite`, `N` is not
    prime. -/
theorem IsFixedDivisorSystem.not_prime {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)}
    (h : IsFixedDivisorSystem A B T) {M N n : ℕ}
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hN : (N : ℤ) = A * 2 ^ n + B)
    (hMN : M < N) : ¬ N.Prime :=
  (h.composite hM hN hMN).2

-- ════════════════════════════════════════════════════════════════════
-- §5 TRANSLATION: THE SAME CERTIFICATE SERVES A WHOLE PROGRESSION
-- ════════════════════════════════════════════════════════════════════

/-- Moving the constant term `B` by a multiple of every divisor keeps
    the certificate valid.  This is what makes Erdős's 1950 theorem an
    instance: there `B` is the variable `m`, ranging over an arithmetic
    progression modulo the product of the divisors (see
    `Erdos.Covering.Erdos1950Instance`). -/
theorem IsFixedDivisorSystemBase.of_dvd_sub_const {b : ℕ} {A B B' : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T)
    (hBB : ∀ p ∈ fixedDivisors T, (p : ℤ) ∣ B' - B) :
    IsFixedDivisorSystemBase b A B' T where
  one_lt_divisor := h.one_lt_divisor
  covers := h.covers
  pow_modEq_one := h.pow_modEq_one
  divisor_dvd := by
    intro t ht
    have hbase := h.divisor_dvd t ht
    have hshift := hBB t.2.2 (mem_fixedDivisors.mpr ⟨t, ht, rfl⟩)
    have hsum := dvd_add hbase hshift
    have heq : A * (b : ℤ) ^ t.1 + B + (B' - B) = A * (b : ℤ) ^ t.1 + B' := by ring
    rwa [heq] at hsum

/-- Moving the coefficient `A` by a multiple of every divisor keeps the
    certificate valid.  This is what makes Sierpiński and Riesel
    numbers come in arithmetic progressions — hence Sierpiński's 1960
    theorem that infinitely many exist, and its base-`b` analogue. -/
theorem IsFixedDivisorSystemBase.of_dvd_sub_coeff {b : ℕ} {A A' B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T)
    (hAA : ∀ p ∈ fixedDivisors T, (p : ℤ) ∣ A' - A) :
    IsFixedDivisorSystemBase b A' B T where
  one_lt_divisor := h.one_lt_divisor
  covers := h.covers
  pow_modEq_one := h.pow_modEq_one
  divisor_dvd := by
    intro t ht
    have hbase := h.divisor_dvd t ht
    have hshift :=
      (hAA t.2.2 (mem_fixedDivisors.mpr ⟨t, ht, rfl⟩)).mul_right ((b : ℤ) ^ t.1)
    have hsum := dvd_add hbase hshift
    have heq :
        A * (b : ℤ) ^ t.1 + B + (A' - A) * (b : ℤ) ^ t.1 = A' * (b : ℤ) ^ t.1 + B := by
      ring
    rwa [heq] at hsum

/-- **Moving the base.**  A certificate for base `b` is a certificate
    for every base `b'` congruent to `b` modulo each of its divisors:
    both `b ^ d ≡ 1` and `A · b ^ a + B ≡ 0` are congruences mod `p`,
    so they only see `b mod p`.

    This has no base-2 counterpart — it is the one translation the
    generalization creates rather than transports — and it is what
    turns a single certificate into a statement about infinitely many
    *bases*.  Wikipedia's "Riesel number" article, § "Riesel number
    base b", Example 2 is exactly such a statement; it is formalized as
    `Erdos.Covering.isRieselNumberBase_six_of_modEq_34`. -/
theorem IsFixedDivisorSystemBase.of_modEq_base {b b' : ℕ} {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T)
    (hbb : ∀ p ∈ fixedDivisors T, b' ≡ b [MOD p]) :
    IsFixedDivisorSystemBase b' A B T where
  one_lt_divisor := h.one_lt_divisor
  covers := h.covers
  pow_modEq_one := by
    intro t ht
    have hb := hbb t.2.2 (mem_fixedDivisors.mpr ⟨t, ht, rfl⟩)
    exact (hb.pow t.2.1).trans (h.pow_modEq_one t ht)
  divisor_dvd := by
    intro t ht
    have hb := hbb t.2.2 (mem_fixedDivisors.mpr ⟨t, ht, rfl⟩)
    have hbZ : (b' : ℤ) ≡ (b : ℤ) [ZMOD ((t.2.2 : ℕ) : ℤ)] := Int.natCast_modEq_iff.mpr hb
    have hfam : A * (b' : ℤ) ^ t.1 + B ≡ A * (b : ℤ) ^ t.1 + B
        [ZMOD ((t.2.2 : ℕ) : ℤ)] :=
      ((hbZ.pow t.1).mul_left A).add_right B
    exact Int.modEq_zero_iff_dvd.mp
      (hfam.trans (Int.modEq_zero_iff_dvd.mpr (h.divisor_dvd t ht)))

/-- Moving the constant term `B` by a multiple of every divisor keeps
    the certificate valid; the `b = 2` case of
    `IsFixedDivisorSystemBase.of_dvd_sub_const`. -/
theorem IsFixedDivisorSystem.of_dvd_sub_const {A B B' : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystem A B T)
    (hBB : ∀ p ∈ fixedDivisors T, (p : ℤ) ∣ B' - B) :
    IsFixedDivisorSystem A B' T :=
  isFixedDivisorSystem_iff_base_two.mpr
    ((isFixedDivisorSystem_iff_base_two.mp h).of_dvd_sub_const hBB)

/-- Moving the coefficient `A` by a multiple of every divisor keeps the
    certificate valid; the `b = 2` case of
    `IsFixedDivisorSystemBase.of_dvd_sub_coeff`. -/
theorem IsFixedDivisorSystem.of_dvd_sub_coeff {A A' B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystem A B T)
    (hAA : ∀ p ∈ fixedDivisors T, (p : ℤ) ∣ A' - A) :
    IsFixedDivisorSystem A' B T :=
  isFixedDivisorSystem_iff_base_two.mpr
    ((isFixedDivisorSystem_iff_base_two.mp h).of_dvd_sub_coeff hAA)

/-- A ℕ-level congruence `m % P = M` as an integer divisibility.  Cast
    before subtracting, per STYLE.md: `(M : ℤ)` may exceed `(m : ℤ)`
    only when `m < M`, which `m % P = M` excludes, but the ℤ statement
    needs no such argument. -/
theorem intCast_dvd_sub_of_mod_eq {P M m : ℕ} (hm : m % P = M) :
    (P : ℤ) ∣ (m : ℤ) - (M : ℤ) := by
  refine ⟨((m / P : ℕ) : ℤ), ?_⟩
  have hdm : P * (m / P) + m % P = m := Nat.div_add_mod m P
  rw [hm] at hdm
  have hcast : ((P * (m / P) + M : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast hdm
  -- `Nat.cast_add`/`Nat.cast_mul` only: `push_cast` would rewrite
  -- `((m / P : ℕ) : ℤ)` to the truncating `(m : ℤ) / (P : ℤ)` and
  -- strand the witness supplied to `Dvd.intro`.
  rw [Nat.cast_add, Nat.cast_mul] at hcast
  linarith

-- ════════════════════════════════════════════════════════════════════
-- §6 DROP-ONE NEGATIVE CONTROLS: EVERY FIELD IS LOAD-BEARING
-- ════════════════════════════════════════════════════════════════════

/-! Fields (b), (c) and (d) are each shown necessary for the general
theorem by a certificate satisfying the other three at which its
conclusion FAILS.

Field (a) `one_lt_divisor` is NOT of that form, and saying otherwise
would overstate it: `exists_mem_fixedDivisors_dvd` does not mention
`one_lt_divisor` in its proof cone and remains true without it. What
control (a) exhibits is that dropping the field makes the certificate
worthless rather than the theorem false — `{(0, 1, 1)}` satisfies the
other three for every `A` and `B`, and its conclusion, while true, says
only that `1` divides something. The field is genuinely load-bearing
for `.composite`/`.not_prime`, which do consume it.

Control (e) is about the parameter rather than a field: the base `b` is
not inert decoration, and a certificate valid in one base generally
fails in another.

Together with the satisfiability witnesses of §7 these pin the
predicate from both sides. -/

-- ── (a) `one_lt_divisor` ────────────────────────────────────────────
-- Without it the certificate `{(0, 1, 1)}` satisfies the other three
-- fields for *every* `A` and `B` — modulus `1` covers ℤ, `2 ^ 1 ≡ 1`
-- mod `1`, and `1` divides everything — so `IsFixedDivisorSystem`
-- would be a tautology and certify nothing.
example (A B : ℤ) :
    Covers (residueClasses {(0, 1, 1)}) ∧
      (∀ t ∈ ({(0, 1, 1)} : Finset (ℕ × ℕ × ℕ)), 2 ^ t.2.1 ≡ 1 [MOD t.2.2]) ∧
        ∀ t ∈ ({(0, 1, 1)} : Finset (ℕ × ℕ × ℕ)), (t.2.2 : ℤ) ∣ A * 2 ^ t.1 + B := by
  refine ⟨(covers_residueClasses_iff_forall_range 1 (by decide) (by decide)).mpr (by decide),
    by decide, ?_⟩
  intro t ht
  fin_cases ht
  simp

-- The field really is violated by that certificate …
example : ¬ IsFixedDivisorSystem 1 1 {(0, 1, 1)} := fun h =>
  absurd (h.one_lt_divisor (0, 1, 1) (by decide)) (by decide)

-- … and its conclusion would be worthless: `1 * 2 ^ 1 + 1 = 3` is
-- prime, so no compositeness can follow from a divisor equal to `1`.
example : ¬ Composite 3 := fun h => h.2 (by norm_num)

-- ── (b) `covers` ────────────────────────────────────────────────────
-- The single class `0 (mod 2)` with divisor `3` satisfies the other
-- three fields for `A = 78557`, `B = 1` (`3 ∣ 78557 + 1 = 78558`),
-- but its classes miss the odd exponents.
example : (∀ t ∈ ({(0, 2, 3)} : Finset (ℕ × ℕ × ℕ)), 1 < t.2.2) ∧
    (∀ t ∈ ({(0, 2, 3)} : Finset (ℕ × ℕ × ℕ)), 2 ^ t.2.1 ≡ 1 [MOD t.2.2]) ∧
      ∀ t ∈ ({(0, 2, 3)} : Finset (ℕ × ℕ × ℕ)),
        (t.2.2 : ℤ) ∣ (78557 : ℤ) * 2 ^ t.1 + 1 := by decide

example : ¬ Covers (residueClasses {(0, 2, 3)}) := fun h =>
  absurd ((covers_residueClasses_iff_forall_range 2 (by decide) (by decide)).mp h)
    (by decide)

-- The conclusion of the general theorem fails at `n = 1`:
-- `78557 · 2 + 1 = 157115 = 5 · 7 · 67 · 67` is not divisible by `3`.
example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 1 + 1 := by
  decide

-- ── (c) `two_pow_modEq_one` ─────────────────────────────────────────
-- The certificate `{(0, 1, 2)}` for `A = B = 1` covers ℤ (modulus `1`),
-- has `1 < 2`, and `2 ∣ 2 ^ 0 + 1 = 2`; only `2 ^ 1 ≡ 1 (mod 2)` fails.
example : (∀ t ∈ ({(0, 1, 2)} : Finset (ℕ × ℕ × ℕ)), 1 < t.2.2) ∧
    Covers (residueClasses {(0, 1, 2)}) ∧
      ∀ t ∈ ({(0, 1, 2)} : Finset (ℕ × ℕ × ℕ)),
        (t.2.2 : ℤ) ∣ (1 : ℤ) * 2 ^ t.1 + 1 :=
  ⟨by decide,
    (covers_residueClasses_iff_forall_range 1 (by decide) (by decide)).mpr (by decide),
    by decide⟩

example : ¬ ∀ t ∈ ({(0, 1, 2)} : Finset (ℕ × ℕ × ℕ)), 2 ^ t.2.1 ≡ 1 [MOD t.2.2] := by
  decide

-- The conclusion fails at `n = 1`: `2 ^ 1 + 1 = 3` is odd.
example : ¬ ∃ p ∈ fixedDivisors {(0, 1, 2)}, (p : ℤ) ∣ (1 : ℤ) * 2 ^ 1 + 1 := by decide

-- ── (d) `divisor_dvd` ───────────────────────────────────────────────
-- `{0 (mod 2), 1 (mod 2)}` with divisor `3` covers ℤ, has `1 < 3` and
-- `2 ^ 2 ≡ 1 (mod 3)`; it simply is not attached to the family
-- `2 ^ n + 1`, and the base divisibility is what detects that.
example : (∀ t ∈ ({(0, 2, 3), (1, 2, 3)} : Finset (ℕ × ℕ × ℕ)), 1 < t.2.2) ∧
    Covers (residueClasses {(0, 2, 3), (1, 2, 3)}) ∧
      ∀ t ∈ ({(0, 2, 3), (1, 2, 3)} : Finset (ℕ × ℕ × ℕ)),
        2 ^ t.2.1 ≡ 1 [MOD t.2.2] :=
  ⟨by decide,
    (covers_residueClasses_iff_forall_range 2 (by decide) (by decide)).mpr (by decide),
    by decide⟩

example : ¬ ∀ t ∈ ({(0, 2, 3), (1, 2, 3)} : Finset (ℕ × ℕ × ℕ)),
    (t.2.2 : ℤ) ∣ (1 : ℤ) * 2 ^ t.1 + 1 := by decide

-- The conclusion fails at `n = 0`: `2 ^ 0 + 1 = 2` is not divisible
-- by `3`.
example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 2, 3)}, (p : ℤ) ∣ (1 : ℤ) * 2 ^ 0 + 1 := by
  decide

-- ── (e) the base `b` ────────────────────────────────────────────────
-- The base is not inert.  Selfridge's certificate is valid in base `2`
-- (§7) and invalid in base `3`: the triple `(0, 2, 3)` needs
-- `3 ^ 2 ≡ 1 (mod 3)`, and `9 % 3 = 0 ≠ 1 % 3`.
example : ¬ IsFixedDivisorSystemBase 3 78557 1
    {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19), (27, 36, 37),
      (3, 9, 73)} := fun h =>
  absurd (h.pow_modEq_one (0, 2, 3) (by decide)) (by decide)

-- And its conclusion fails in base `3` at `n = 1`:
-- `78557 · 3 + 1 = 235672 = 2 ^ 3 · 89 · 331`, divisible by none of
-- `{3, 5, 7, 13, 19, 37, 73}`.
example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13),
    (15, 18, 19), (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 3 ^ 1 + 1 := by
  decide

-- ════════════════════════════════════════════════════════════════════
-- §7 SATISFIABILITY WITNESSES
-- ════════════════════════════════════════════════════════════════════

/-! The negative controls of §6 pin the two predicates from one side;
STYLE.md requires the other — concrete models at which all four fields
hold *jointly*, so that neither predicate is contradictory and neither
general theorem is vacuous.

Selfridge's seven-class certificate for `78557 · 2 ^ n + 1` is the
base-2 model, spelled here with literal numerals so that this file
depends on none of its applications.  `Erdos.Covering.Sierpinski`
develops it into `isSierpinskiNumber_78557`; `Erdos.Covering.Riesel`
and `Erdos.Covering.Erdos1950Instance` supply two more base-2 models,
at `(A, B) = (509203, -1)` and `(-1, m)` respectively.

Two further models have `b ≠ 2`, so that the base parameter is
witnessed non-trivially at both signs of `B`; they are developed in the
application files. -/

example : IsFixedDivisorSystem 78557 1
    {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19), (27, 36, 37),
      (3, 9, 73)} :=
  (isFixedDivisorSystem_iff 78557 1 _ 36 (by decide) (by decide)).mpr (by decide)

-- The conclusion at that model is not trivially true: the divisors are
-- seven distinct primes, all far below the values of the family, and
-- the exponent `n = 27` really does need the class `27 (mod 36)`.
example : fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19),
    (27, 36, 37), (3, 9, 73)} = {3, 5, 7, 13, 19, 37, 73} := by decide
example : ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13),
    (15, 18, 19), (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 27 + 1 := by
  decide

-- A second model with a different sign pattern, so that neither
-- `B = 1` nor a positive `A` is doing hidden work: Riesel's
-- certificate at `(A, B) = (509203, -1)`.
example : IsFixedDivisorSystem 509203 (-1)
    {(0, 2, 3), (1, 4, 5), (2, 3, 7), (7, 12, 13), (7, 8, 17), (3, 24, 241)} :=
  (isFixedDivisorSystem_iff 509203 (-1) _ 24 (by decide) (by decide)).mpr (by decide)

-- ── Base 6, `(A, B) = (84687, -1)` ──────────────────────────────────
-- Wikipedia, "Riesel number", § "Riesel number base b", Example 1:
-- "All numbers congruent to 84687 mod 10124569 and not congruent to 1
-- mod 5 are Riesel numbers base 6, because of the covering set
-- {7, 13, 31, 37, 97}."  `Erdos.Covering.Riesel` develops it into
-- `isRieselNumberBase_six_84687`.
example : IsFixedDivisorSystemBase 6 84687 (-1)
    {(0, 2, 7), (3, 12, 13), (1, 6, 31), (1, 4, 37), (11, 12, 97)} :=
  (isFixedDivisorSystemBase_iff 6 84687 (-1) _ 12 (by decide) (by decide)).mpr (by decide)

-- This model is NOT a covering system in the distinct-moduli sense of
-- `Erdos.Covering.Basic`: `13` and `97` share the modulus `12`.  Only
-- `Covers` is a field of `IsFixedDivisorSystemBase`, and the gap is
-- real — the base-2 certificates of the application files do have
-- distinct moduli, this one does not.
example : ¬ IsCoveringSystem
    (residueClasses {(0, 2, 7), (3, 12, 13), (1, 6, 31), (1, 4, 37), (11, 12, 97)}) := by
  intro h
  have hmem3 : ((3, 12) : ℕ × ℕ) ∈ residueClasses
      ({(0, 2, 7), (3, 12, 13), (1, 6, 31), (1, 4, 37), (11, 12, 97)} :
        Finset (ℕ × ℕ × ℕ)) := by decide
  have hmem11 : ((11, 12) : ℕ × ℕ) ∈ residueClasses
      ({(0, 2, 7), (3, 12, 13), (1, 6, 31), (1, 4, 37), (11, 12, 97)} :
        Finset (ℕ × ℕ × ℕ)) := by decide
  have heq : ((3, 12) : ℕ × ℕ) = (11, 12) :=
    h.injOn_mod (Finset.mem_coe.mpr hmem3) (Finset.mem_coe.mpr hmem11) rfl
  exact absurd heq (by decide)

-- ── Base 14, `(A, B) = (4, 1)` ──────────────────────────────────────
-- A123159 (`Conjectured smallest Sierpiński numbers of the second kind
-- S, base b=2,3,4,5,..., where S*b^n+1 is composite for all n>=1 and
-- gcd(S+1, b-1) = 1`) has `a(14) = 4`; A146563's comment names the
-- covering set as two primes splitting the exponents by parity.
-- `Erdos.Covering.Sierpinski` develops it into
-- `isSierpinskiNumberBase_fourteen_four`.
example : IsFixedDivisorSystemBase 14 4 1 {(1, 2, 3), (0, 2, 5)} :=
  (isFixedDivisorSystemBase_iff 14 4 1 _ 2 (by decide) (by decide)).mpr (by decide)

-- ════════════════════════════════════════════════════════════════════
-- §8 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms residueClasses
#print axioms fixedDivisors
#print axioms Composite
#print axioms mem_residueClasses
#print axioms mem_fixedDivisors
#print axioms IsFixedDivisorSystem
#print axioms IsFixedDivisorSystemBase
#print axioms covers_residueClasses_iff_forall_range
#print axioms isFixedDivisorSystem_iff
#print axioms isFixedDivisorSystemBase_iff
#print axioms isFixedDivisorSystem_iff_base_two
#print axioms pow_intModEq_pow_mod
#print axioms pow_intModEq_of_mod_eq
#print axioms dvd_affine_pow_of_mod_eq
#print axioms IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd
#print axioms IsFixedDivisorSystemBase.nonempty
#print axioms IsFixedDivisorSystemBase.composite
#print axioms IsFixedDivisorSystemBase.not_prime
#print axioms IsFixedDivisorSystemBase.of_dvd_sub_const
#print axioms IsFixedDivisorSystemBase.of_dvd_sub_coeff
#print axioms IsFixedDivisorSystemBase.of_modEq_base
#print axioms two_pow_intModEq_pow_mod
#print axioms two_pow_intModEq_of_mod_eq
#print axioms dvd_affine_two_pow_of_mod_eq
#print axioms IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd
#print axioms IsFixedDivisorSystem.nonempty
#print axioms IsFixedDivisorSystem.composite
#print axioms IsFixedDivisorSystem.not_prime
#print axioms IsFixedDivisorSystem.of_dvd_sub_const
#print axioms IsFixedDivisorSystem.of_dvd_sub_coeff
#print axioms intCast_dvd_sub_of_mod_eq

end Erdos.Covering

