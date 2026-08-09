/-
  Riesel numbers: `509203` is one, as an instance of the general
  fixed-divisor theorem of `Erdos.Covering.FixedDivisor`.

  A *Riesel number* is an odd `k` such that `k · 2 ^ n - 1` is
  composite for every `n : ℕ` (Wikipedia, "Riesel number", pinned
  2026-07-31: "an odd natural number `k` for which `k × 2^n − 1` is
  composite for all natural numbers `n`").  Riesel (1956) showed
  `509203` has this property, as does `509203` plus any positive
  multiple of `11184810`; it is conjectured to be the least.

  ── The certificate ─────────────────────────────────────────────────
  Six triples `(a, d, p)` — residue, modulus, prime:

    | a  |  0 |  1 |  2 |  7 |  7 |   3 |
    | d  |  2 |  4 |  3 | 12 |  8 |  24 |
    | p  |  3 |  5 |  7 | 13 | 17 | 241 |

  The prime set `{3, 5, 7, 13, 17, 241}` and the moduli
  `{2, 4, 3, 12, 8, 24}` are *identical* to those of the Erdős-1950
  construction in `Erdos.Covering.NotTwoPowerPlusPrime`; only the
  residues differ.  Every `2 ^ d ≡ 1 (mod p)` fact therefore transfers
  verbatim — the multiplicative orders `orderOf_two_zmod_three`,
  `…_five`, `…_seven`, `…_thirteen`, `…_seventeen`, `…_241` are already
  proved there — and this file introduces no new order mathematics.
  That reuse is the cleanest available evidence that the layer is
  infrastructure rather than a bespoke script.

  ── ℕ subtraction ───────────────────────────────────────────────────
  `k * 2 ^ n - 1` is ℕ subtraction, hence totalized.  It is guarded by
  the oddness conjunct of `IsRieselNumber`: `¬ 2 ∣ k` forces `k ≠ 0`,
  hence `1 ≤ k * 2 ^ n`, so the subtraction never hits its junk value.
  `cast_riesel_family` is the explicit ℤ bridge used throughout.

  ── Prior art ───────────────────────────────────────────────────────
  * **ACL2, Cowles–Gamboa 2011.**  "Verifying Sierpiński and Riesel
    Numbers in ACL2", EPTCS 70, 31–39, arXiv:1110.4671, machine-checked
    that `509203` is a Riesel number:
    `books/workshops/2011/cowles-gamboa-sierpinski/support/`
    `verifying-macros.lisp` line 813 invokes
    `(verify-riesel riesel-witness-509203 509203 (3 5 7 13 17 241))`.
    **The concrete number is theirs first.**  Their artefact is
    per-number: the macro that emits the proof obligations is itself
    unverified, and no general criterion is formalized.
  * **Lean/Isabelle/Coq.**  A survey (2026-07-31) of Mathlib,
    google-deepmind/formal-conjectures, plby/lean-proofs and the
    Isabelle AFP found no Riesel-number definition or theorem.
    formal-conjectures has a Sierpiński predicate and a `native_decide`
    proof of `78557`, but nothing for Riesel.  So `IsRieselNumber` and
    `isRieselNumber_509203` appear to be the first in a proof assistant
    other than ACL2 — and, more to the point, the first *instance of a
    general theorem* anywhere.

  ── Contents ────────────────────────────────────────────────────────
  * `IsRieselNumber` — the standard predicate, defined here in the
    shape of `Nat.IsSierpinskiNumber` of formal-conjectures since that
    repository has no Riesel counterpart.
  * `rieselCert509203` — the six-triple certificate, with ground checks
    and drop-one negative controls.
  * `isRieselNumber_of_isFixedDivisorSystem` — the general Riesel
    criterion.
  * `isRieselNumber_509203` — Riesel's number.
  * `isRieselNumber_add_mul`, `exists_lt_isRieselNumber` — the whole
    progression `509203 + 11184810 · t`, hence infinitude.
  * §6, base `b` (all of it downstream of
    `IsFixedDivisorSystemBase`, none of it touching the base-2
    material above):
      - `IsRieselNumberBase b k` — the Wikipedia predicate, quoted
        verbatim at the definition, with its `n ≥ 1` convention.
      - `isRieselNumberBase_of_isFixedDivisorSystemBase` — the base-`b`
        criterion.
      - `isRieselNumber_iff_base_two` — the exact difference between
        the two predicates at `b = 2`: oddness and the exponent `0`.
      - `isRieselNumberBase_six_84687`,
        `isRieselNumberBase_six_add_mul`,
        `infinite_setOf_isRieselNumberBase_six` — Wikipedia's Example
        1 (`A273987`'s `a(6)`), its progression and its infinitude.
      - `isRieselNumberBase_six_of_modEq_34`,
        `infinite_setOf_isRieselNumberBase_six_base` — Wikipedia's
        Example 2: `6` is a Riesel number to *infinitely many bases*,
        via `IsFixedDivisorSystemBase.of_modEq_base`.  This is the
        statement shape the base parameter creates; base `2` has
        nothing like it.

  Axiom audit: see the `#print axioms` block at the end.  Every
  declaration is sorry-free.  No `native_decide`, no custom axioms.
-/

import Mathlib
import Erdos.Covering.Basic
import Erdos.Covering.FixedDivisor

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 THE PREDICATE
-- ════════════════════════════════════════════════════════════════════

/-- `k` is a **Riesel number**: `k` is odd and `k · 2 ^ n - 1` is
    composite for every natural number `n`.

    google-deepmind/formal-conjectures has no Riesel predicate (checked
    2026-07-31: its file tree contains `SierpinskiNumber.lean` and no
    occurrence of "Riesel"), so this is the standard notion defined in
    the shape of their `Nat.IsSierpinskiNumber`
    (`¬ 2 ∣ k ∧ ∀ n, (k * 2 ^ n + 1).Composite`) with `+1` replaced by
    `-1`, keeping the two artefacts directly comparable.

    The ℕ subtraction is guarded by `¬ 2 ∣ k`, which forces `k ≠ 0` and
    hence `1 ≤ k * 2 ^ n`; see `cast_riesel_family`. -/
def IsRieselNumber (k : ℕ) : Prop :=
  ¬ 2 ∣ k ∧ ∀ n, Composite (k * 2 ^ n - 1)

/-- The ℤ form of the Riesel family, valid whenever `k` is nonzero —
    which the oddness conjunct of `IsRieselNumber` supplies.  Cast
    before subtracting, per STYLE.md. -/
theorem cast_riesel_family {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ((k * 2 ^ n - 1 : ℕ) : ℤ) = (k : ℤ) * 2 ^ n - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hgrow : k * 1 ≤ k * 2 ^ n := Nat.mul_le_mul_left k h1
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

-- Ground checks: the ℤ bridge at small arguments, and the junk value
-- it excludes.
example : ((509203 * 2 ^ 3 - 1 : ℕ) : ℤ) = (509203 : ℤ) * 2 ^ 3 - 1 :=
  cast_riesel_family (by decide) 3
example : (0 : ℕ) * 2 ^ 5 - 1 = 0 := by decide  -- the guarded junk value

-- Ground checks for `IsRieselNumber`: small numbers fail it, for each
-- of the possible reasons.

-- `2` is even.
example : ¬ IsRieselNumber 2 := fun h => h.1 (by decide)

-- `1 · 2 ^ 0 - 1 = 0` is not composite (`1 < 0` fails).
example : ¬ IsRieselNumber 1 := fun h => absurd (h.2 0).1 (by norm_num)

-- `3 · 2 ^ 0 - 1 = 2` is prime.
example : ¬ IsRieselNumber 3 := fun h => (h.2 0).2 (by norm_num)

-- `5 · 2 ^ 2 - 1 = 19` is prime, though `5 - 1 = 4` and `5 · 2 - 1 = 9`
-- are both composite.
example : ¬ IsRieselNumber 5 := fun h => (h.2 2).2 (by norm_num)
example : Composite (5 * 2 ^ 0 - 1) := ⟨by norm_num, by norm_num⟩
example : Composite (5 * 2 ^ 1 - 1) := ⟨by norm_num, by norm_num⟩

-- ════════════════════════════════════════════════════════════════════
-- §2 THE CERTIFICATE FOR 509203
-- ════════════════════════════════════════════════════════════════════

/-- Riesel's covering data for `509203 · 2 ^ n - 1`, as triples
    `(residue, modulus, prime)`.  The primes are the covering set
    `{3, 5, 7, 13, 17, 241}` — the same set as Erdős's 1950
    construction — and each modulus is the multiplicative order of `2`
    modulo its prime. -/
def rieselCert509203 : Finset (ℕ × ℕ × ℕ) :=
  {(0, 2, 3), (1, 4, 5), (2, 3, 7), (7, 12, 13), (7, 8, 17), (3, 24, 241)}

-- Ground checks for `rieselCert509203`.
example : rieselCert509203.card = 6 := by decide
example : ((3, 24, 241) : ℕ × ℕ × ℕ) ∈ rieselCert509203 := by decide
example : ((23, 24, 241) : ℕ × ℕ × ℕ) ∉ rieselCert509203 := by decide

/-- The divisors of the certificate are the covering set quoted in the
    literature (Wikipedia, "Riesel number": `509203 × 2^n − 1` has
    covering set `{3, 5, 7, 13, 17, 241}`; Cowles–Gamboa's ACL2
    invocation `(verify-riesel … 509203 (3 5 7 13 17 241))`). -/
theorem fixedDivisors_rieselCert509203 :
    fixedDivisors rieselCert509203 = {3, 5, 7, 13, 17, 241} := by decide

/-- **The moduli coincide with Erdős's 1950 data.**  Together with
    `fixedDivisors_rieselCert509203` this says the covering set and the
    moduli are `{3, 5, 7, 13, 17, 241}` and `{2, 3, 4, 8, 12, 24}` —
    exactly the pairs of `Erdos.Covering.NotTwoPowerPlusPrime`, only
    the residues differ.  So every `2 ^ d ≡ 1 (mod p)` fact, and the
    six `orderOf (2 : ZMod p) = d` theorems proved there, transfer with
    nothing new to prove.

    The two literals are restated verbatim for `erdosCert1950` in
    `Erdos.Covering.Erdos1950Instance` §2; this file deliberately does
    not import that module, so that no application depends on another. -/
theorem image_snd_residueClasses_rieselCert509203 :
    (residueClasses rieselCert509203).image Prod.snd = {2, 3, 4, 8, 12, 24} := by decide

/-- Every divisor of the certificate is prime. -/
theorem prime_of_mem_fixedDivisors_rieselCert509203 :
    ∀ p ∈ fixedDivisors rieselCert509203, Nat.Prime p := by
  rw [fixedDivisors_rieselCert509203]
  intro p hp
  fin_cases hp <;> norm_num

/-- The classes of the certificate form a covering system in the
    classical distinct-moduli sense of `Erdos.Covering.Basic`: moduli
    `{2, 4, 3, 12, 8, 24}`, pairwise distinct, all exceeding `1`,
    covering ℤ.  Verified by `decide` at the common multiple
    `L = 24`. -/
theorem isCoveringSystem_rieselCert509203 :
    IsCoveringSystem (residueClasses rieselCert509203) :=
  (isCoveringSystem_iff 24 (by decide) (by decide)).mpr (by decide)

/-- **The certificate is valid.**  All four fields of
    `IsFixedDivisorSystem` hold for `A = 509203`, `B = -1`, verified by
    kernel `decide` through `isFixedDivisorSystem_iff` at the common
    multiple `L = 24` of the moduli. -/
theorem isFixedDivisorSystem_rieselCert509203 :
    IsFixedDivisorSystem 509203 (-1) rieselCert509203 :=
  (isFixedDivisorSystem_iff 509203 (-1) rieselCert509203 24 (by decide) (by decide)).mpr
    (by decide)

-- ── Drop-one negative controls ──────────────────────────────────────
-- Deleting any single triple leaves an exponent `n` at which *no*
-- remaining prime divides `509203 · 2 ^ n - 1`, so the certificate is
-- irredundant.

example : ¬ ∃ p ∈ fixedDivisors {(1, 4, 5), (2, 3, 7), (7, 12, 13), (7, 8, 17),
    (3, 24, 241)}, (p : ℤ) ∣ (509203 : ℤ) * 2 ^ 0 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (2, 3, 7), (7, 12, 13), (7, 8, 17),
    (3, 24, 241)}, (p : ℤ) ∣ (509203 : ℤ) * 2 ^ 1 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (7, 12, 13), (7, 8, 17),
    (3, 24, 241)}, (p : ℤ) ∣ (509203 : ℤ) * 2 ^ 11 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (2, 3, 7), (7, 8, 17),
    (3, 24, 241)}, (p : ℤ) ∣ (509203 : ℤ) * 2 ^ 19 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (2, 3, 7), (7, 12, 13),
    (3, 24, 241)}, (p : ℤ) ∣ (509203 : ℤ) * 2 ^ 15 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (2, 3, 7), (7, 12, 13),
    (7, 8, 17)}, (p : ℤ) ∣ (509203 : ℤ) * 2 ^ 3 - 1 := by decide

-- ════════════════════════════════════════════════════════════════════
-- §3 THE RIESEL CRITERION AND RIESEL'S NUMBER
-- ════════════════════════════════════════════════════════════════════

/-- **The Riesel criterion.**  An odd `k` is a Riesel number as soon as
    the family `n ↦ k · 2 ^ n - 1` admits *any* fixed-divisor
    certificate whose divisors are bounded by some `M` with
    `M + 1 < k`.

    The bound is `M + 1 < k` rather than `M < k` because the family
    sits one below `k · 2 ^ n`; at `n = 0` its value is exactly
    `k - 1`.  As in the Sierpiński case the family grows without bound,
    so no dyadic-block argument is needed. -/
theorem isRieselNumber_of_isFixedDivisorSystem {k M : ℕ} {T : Finset (ℕ × ℕ × ℕ)}
    (hodd : ¬ 2 ∣ k) (h : IsFixedDivisorSystem (k : ℤ) (-1) T)
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hMk : M + 1 < k) :
    IsRieselNumber k := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hodd (dvd_zero 2)
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  refine ⟨hodd, fun n => ?_⟩
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hgrow : k * 1 ≤ k * 2 ^ n := Nat.mul_le_mul_left k h1
  have hN : ((k * 2 ^ n - 1 : ℕ) : ℤ) = (k : ℤ) * 2 ^ n + (-1) := by
    rw [cast_riesel_family hk1 n]
    ring
  exact h.composite hM hN (by omega)

/-- **`509203` is a Riesel number.**  Riesel (1956), via the covering
    set `{3, 5, 7, 13, 17, 241}`; machine-verified first by
    Cowles–Gamboa in ACL2 (2011), with no counterpart in Lean,
    Isabelle or Coq as of 2026-07-31.  Here it is the `A = 509203`,
    `B = -1` instance of `IsFixedDivisorSystem.composite`, with kernel
    `decide` only. -/
theorem isRieselNumber_509203 : IsRieselNumber 509203 := by
  have hcert : IsFixedDivisorSystem ((509203 : ℕ) : ℤ) (-1) rieselCert509203 := by
    have hcast : ((509203 : ℕ) : ℤ) = (509203 : ℤ) := by norm_num
    rw [hcast]
    exact isFixedDivisorSystem_rieselCert509203
  exact isRieselNumber_of_isFixedDivisorSystem (M := 241) (by decide) hcert
    (by decide) (by decide)

-- ════════════════════════════════════════════════════════════════════
-- §4 THE WHOLE PROGRESSION, AND INFINITUDE
-- ════════════════════════════════════════════════════════════════════

/-- The modulus of the Riesel progression:
    `2 · 3 · 5 · 7 · 13 · 17 · 241 = 11184810`.  This is exactly
    `Erdos.Covering.erdosModulus1950`; Wikipedia records that `509203`
    plus any positive multiple of `11184810` is again a Riesel
    number. -/
def rieselModulus : ℕ := 11184810

-- Ground checks for `rieselModulus`.
example : rieselModulus = 2 * 3 * 5 * 7 * 13 * 17 * 241 := by decide
example : rieselModulus = 11184810 := by decide  -- = `erdosModulus1950`
example : ∀ p ∈ fixedDivisors rieselCert509203, p ∣ rieselModulus := by decide
example : rieselModulus % 2 = 0 := by decide
example : (509203 : ℕ) % 2 = 1 := by decide

/-- The same certificate serves the whole progression: shifting the
    coefficient by a multiple of `11184810` shifts it by a multiple of
    every covering prime.  This is
    `IsFixedDivisorSystem.of_dvd_sub_coeff`. -/
theorem isFixedDivisorSystem_riesel_add_mul (t : ℕ) :
    IsFixedDivisorSystem ((509203 + rieselModulus * t : ℕ) : ℤ) (-1)
      rieselCert509203 := by
  have hcast : ((509203 + rieselModulus * t : ℕ) : ℤ)
      = (509203 : ℤ) + 11184810 * (t : ℤ) := by
    show ((509203 + 11184810 * t : ℕ) : ℤ) = (509203 : ℤ) + 11184810 * (t : ℤ)
    push_cast
    ring
  rw [hcast]
  refine isFixedDivisorSystem_rieselCert509203.of_dvd_sub_coeff ?_
  intro p hp
  have hall : ∀ q ∈ fixedDivisors rieselCert509203, q ∣ 11184810 := by decide
  have hpd : (p : ℤ) ∣ (11184810 : ℤ) := by exact_mod_cast hall p hp
  have heq : (509203 : ℤ) + 11184810 * (t : ℤ) - 509203 = 11184810 * (t : ℤ) := by ring
  rw [heq]
  exact hpd.mul_right _

/-- **Every member of the progression `509203 + 11184810 · t` is a
    Riesel number** (Riesel 1956; Wikipedia, "Riesel number").
    Oddness is preserved because the modulus is even. -/
theorem isRieselNumber_add_mul (t : ℕ) :
    IsRieselNumber (509203 + rieselModulus * t) := by
  refine isRieselNumber_of_isFixedDivisorSystem (M := 241) ?_
    (isFixedDivisorSystem_riesel_add_mul t) (by decide) ?_
  · show ¬ 2 ∣ 509203 + 11184810 * t
    omega
  · show 241 + 1 < 509203 + 11184810 * t
    omega

/-- **Infinitely many Riesel numbers exist.**  Beyond every bound `B`
    there is one, namely `509203 + 11184810 · (B + 1)`. -/
theorem exists_lt_isRieselNumber (B : ℕ) :
    ∃ k, B < k ∧ IsRieselNumber k := by
  refine ⟨509203 + rieselModulus * (B + 1), ?_, isRieselNumber_add_mul (B + 1)⟩
  show B < 509203 + 11184810 * (B + 1)
  omega

/-- The set of Riesel numbers is infinite. -/
theorem infinite_setOf_isRieselNumber :
    {k : ℕ | IsRieselNumber k}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨k, hk, hkR⟩ := exists_lt_isRieselNumber B
  have hle : k ≤ B := hB hkR
  omega

-- ════════════════════════════════════════════════════════════════════
-- §5 NON-VACUITY OF THE HEADLINE THEOREM
-- ════════════════════════════════════════════════════════════════════

-- The first few members of the family are genuinely composite,
-- certified independently of the covering argument.
example : Composite (509203 * 2 ^ 0 - 1) := ⟨by norm_num, by norm_num⟩  -- 509202 = 2·3²·28289
example : Composite (509203 * 2 ^ 1 - 1) := ⟨by norm_num, by norm_num⟩  -- 1018405 = 5·353·577
example : Composite (509203 * 2 ^ 2 - 1) := ⟨by norm_num, by norm_num⟩  -- 2036811 = 3·7·23·4217
example : Composite (509203 * 2 ^ 3 - 1) := ⟨by norm_num, by norm_num⟩  -- 4073623 = 241·16903

-- … and they are the values the theorem speaks about.
example : 509203 * 2 ^ 3 - 1 = 4073623 := by decide
example : Composite 4073623 := isRieselNumber_509203.2 3

-- The predicted divisor, class by class, matching the table in the
-- module header.
example : (3 : ℕ) ∣ 509203 * 2 ^ 0 - 1 := by decide     -- n ≡ 0 (mod 2)
example : (5 : ℕ) ∣ 509203 * 2 ^ 1 - 1 := by decide     -- n ≡ 1 (mod 4)
example : (7 : ℕ) ∣ 509203 * 2 ^ 2 - 1 := by decide     -- n ≡ 2 (mod 3)
example : (13 : ℕ) ∣ 509203 * 2 ^ 7 - 1 := by decide    -- n ≡ 7 (mod 12)
example : (17 : ℕ) ∣ 509203 * 2 ^ 15 - 1 := by decide   -- n ≡ 7 (mod 8)
example : (241 : ℕ) ∣ 509203 * 2 ^ 3 - 1 := by decide   -- n ≡ 3 (mod 24)

-- ════════════════════════════════════════════════════════════════════
-- §6 RIESEL NUMBERS TO AN ARBITRARY BASE
-- ════════════════════════════════════════════════════════════════════

/-! Everything above is base `2`.  The general fixed-divisor theorem of
`Erdos.Covering.FixedDivisor` is stated for an arbitrary base `b`, and
this section spends that generality on the base-`b` Riesel problem.

── Source, verbatim (Wikipedia, "Riesel number", § "Riesel number base
b", `goof wiki article "Riesel number"`, 2026-08-05) ────────────────

  "One can generalize the Riesel problem to an integer base b ≥ 2. A
   **Riesel number base b** is a positive integer k such that
   gcd(k − 1, b − 1) = 1. (if gcd(k − 1, b − 1) > 1, then
   gcd(k − 1, b − 1) is a trivial factor of k×b^n − 1 (Definition of
   trivial factors for the conjectures: Each and every n-value has the
   same factor)) For every integer b ≥ 2, there are infinitely many
   Riesel numbers base b."

  "In the following list, we only consider those positive integers k
   such that gcd(k − 1, b − 1) = 1, and all integer n must be ≥ 1."

  "Example 1: All numbers congruent to 84687 mod 10124569 and not
   congruent to 1 mod 5 are Riesel numbers base 6, because of the
   covering set {7, 13, 31, 37, 97}."

SOURCE TYPO, FLAGGED.  Example 1 continues "Besides, these k are not
trivial since gcd(k + 1, 6 − 1) = 1 for these k", with a PLUS sign,
contradicting the article's own definition and its "In the following
list" sentence, both of which say `gcd(k − 1, b − 1) = 1`.  The minus
form is the right one — it is what "not congruent to 1 mod 5" encodes,
since `k ≡ 1 (mod 5)` iff `5 ∣ k − 1` — and it is what is formalized.
(The typo is harmless for `84687` itself, which satisfies both.)
Example 2's parallel clause has the minus sign and is quoted intact
below.

  "Example 2: 6 is a Riesel number to all bases b congruent to 34 mod
   35, because if b is congruent to 34 mod 35, then 6×b^n − 1 is
   divisible by 5 for all even n and divisible by 7 for all odd n."

── OEIS A273987 (`goof oeis show A273987`, 2026-08-05) ──────────────

  name: "Smallest Riesel number to base n."
  terms: "509203,63064644938,9,346802,84687,408034255082,14,4,10176,
    862,25,302,4,36370321851498,9,86,246,144,8,560,4461,476,4,36,149,
    8,144,4,1369,134718,10,16,6,287860,4,7772,13,4,81,8,15137,672,4,
    22564,8177,14,3226,36,16"
  comment: "a(2), a(3), a(5), a(6), a(7), a(10), a(15), a(22), a(23),
    a(30), ... are only conjectural (see links)."

Indexing starts at `n = 2`, so `a(2) = 509203` and `a(6) = 84687`.
Both are listed as *conjectural*, and MINIMALITY IS NOT CLAIMED HERE:
what is proved is that `84687` IS a Riesel number base `6`, never that
it is the least.

── What this framework can and cannot reach ─────────────────────────

`a(4) = 9` and `a(9) = 4` are NOT covering-system results —
`9 · 4 ^ n − 1 = (3 · 2 ^ n − 1)(3 · 2 ^ n + 1)` is an algebraic
factorization, the base-`b` analogue of the Izotov phenomenon named in
the non-goals of the base-2 arc.  No fixed-divisor certificate exists
for them and none is attempted. -/

/-- `k` is a **Riesel number base `b`**: `gcd (k - 1, b - 1) = 1` — the
    non-triviality condition, stated over ℤ so that no ℕ subtraction is
    truncated — and `k · b ^ n - 1` is composite for every `n ≥ 1`.

    This is the Wikipedia definition quoted above, with its `n ≥ 1`
    convention.  The bound is not cosmetic: at `n = 0` the value is
    `k - 1` whatever the base, and for `k = 6` that is the prime `5`,
    so the theorem `isRieselNumberBase_six_of_modEq_34` below would be
    FALSE if the quantifier started at `n = 0`.  `IsRieselNumber`
    (base 2, `∀ n`) is therefore *stronger* than `IsRieselNumberBase 2`
    rather than equal to it; `isRieselNumber_iff_base_two` records the
    exact difference.

    The ℕ subtraction `k * b ^ n - 1` is totalized, and safely: at the
    degenerate arguments it lands on `0`, and `Composite 0` is false,
    so the predicate is false rather than vacuously true.  See the
    ground checks below for `b = 0` and `b = 1`. -/
def IsRieselNumberBase (b k : ℕ) : Prop :=
  IsCoprime ((k : ℤ) - 1) ((b : ℤ) - 1) ∧ ∀ n, 1 ≤ n → Composite (k * b ^ n - 1)

/-- The non-triviality condition transported from ℕ, where it is
    checkable, to the ℤ statement of `IsRieselNumberBase`. -/
theorem isCoprime_intCast_sub_one {k b : ℕ} (hk : 1 ≤ k) (hb : 1 ≤ b)
    (h : Nat.Coprime (k - 1) (b - 1)) : IsCoprime ((k : ℤ) - 1) ((b : ℤ) - 1) := by
  have hkc : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hk]; norm_num
  have hbc : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hb]; norm_num
  rw [hkc, hbc]
  exact Nat.isCoprime_iff_coprime.mpr h

-- Ground checks for `IsRieselNumberBase`.

-- `11` fails base `6` on non-triviality alone: `gcd (10, 5) = 5`, and
-- indeed `5 ∣ 11 · 6 ^ n - 1` for every `n`.
example : ¬ IsRieselNumberBase 6 11 := by
  rintro ⟨hcop, -⟩
  have h5 : (5 : ℤ) ∣ ((11 : ℤ) - 1) := by norm_num
  have h5' : (5 : ℤ) ∣ ((6 : ℤ) - 1) := by norm_num
  have hunit : (5 : ℤ) = 1 ∨ (5 : ℤ) = -1 :=
    Int.isUnit_iff.mp (hcop.isUnit_of_dvd' h5 h5')
  omega

-- `5` fails base `6` on compositeness: `5 · 6 - 1 = 29` is prime.
example : ¬ IsRieselNumberBase 6 5 := fun h => (h.2 1 (by norm_num)).2 (by norm_num)

-- The guarded ℕ subtraction is safe at `k = 0`: the value is the junk
-- `0`, and `Composite 0` is false, so the predicate is false.
example : ¬ IsRieselNumberBase 6 0 := fun h => absurd (h.2 1 (by norm_num)).1 (by norm_num)

-- Degenerate bases are excluded by the predicate itself, with no
-- `2 ≤ b` hypothesis needed: at `b = 1` the family is the constant
-- `k - 1`, and non-triviality forces `k ∈ {0, 2}`, at both of which
-- that constant fails to be composite.
example (k : ℕ) : ¬ IsRieselNumberBase 1 k := by
  rintro ⟨hcop, hcomp⟩
  have hval : Composite (k * 1 ^ 1 - 1) := hcomp 1 (by norm_num)
  rw [pow_one, mul_one] at hval
  have hk3 : 3 ≤ k := by have hlt := hval.1; omega
  rw [Nat.cast_one, sub_self] at hcop
  have hunit : (k : ℤ) - 1 = 1 ∨ (k : ℤ) - 1 = -1 :=
    Int.isUnit_iff.mp (isCoprime_zero_right.mp hcop)
  omega

-- At `b = 0` the family is the junk `0` for every `n ≥ 1`.
example (k : ℕ) : ¬ IsRieselNumberBase 0 k := by
  rintro ⟨-, hcomp⟩
  have hval : Composite (k * 0 ^ 1 - 1) := hcomp 1 (by norm_num)
  rw [pow_one, Nat.mul_zero] at hval
  exact absurd hval.1 (by norm_num)

/-- The ℤ form of the base-`b` Riesel family, valid whenever the ℕ
    subtraction does not truncate.  Cast before subtracting, per
    STYLE.md. -/
theorem cast_riesel_base_family {k b n : ℕ} (h : 1 ≤ k * b ^ n) :
    ((k * b ^ n - 1 : ℕ) : ℤ) = (k : ℤ) * (b : ℤ) ^ n - 1 := by
  rw [Nat.cast_sub h]
  push_cast
  ring

/-- **The Riesel criterion, base `b`.**  `k` is a Riesel number base
    `b` as soon as it passes the non-triviality test and the family
    `n ↦ k · b ^ n - 1` admits *any* base-`b` fixed-divisor certificate
    whose divisors are bounded by some `M` with `M + 1 < k · b`.

    The bound is `M + 1 < k · b`, not `M + 1 < k`, because the
    quantifier starts at `n = 1`: the smallest certified value is
    `k · b - 1`.  In base `2` this is weaker than
    `isRieselNumber_of_isFixedDivisorSystem`'s `M + 1 < k`, and the
    slack is exactly what lets small multipliers such as `k = 6` work
    in a large base. -/
theorem isRieselNumberBase_of_isFixedDivisorSystemBase {b k M : ℕ}
    {T : Finset (ℕ × ℕ × ℕ)} (hcop : IsCoprime ((k : ℤ) - 1) ((b : ℤ) - 1))
    (h : IsFixedDivisorSystemBase b (k : ℤ) (-1) T)
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hMk : M + 1 < k * b) :
    IsRieselNumberBase b k := by
  refine ⟨hcop, fun n hn => ?_⟩
  have hpow : b ≤ b ^ n := Nat.le_self_pow (by omega) b
  have hgrow : k * b ≤ k * b ^ n := Nat.mul_le_mul_left k hpow
  have hone : 1 ≤ k * b ^ n := by omega
  have hN : ((k * b ^ n - 1 : ℕ) : ℤ) = (k : ℤ) * (b : ℤ) ^ n + (-1) := by
    rw [cast_riesel_base_family hone]
    ring
  exact h.composite hM hN (by omega)

/-- The base-2 predicate is strictly stronger than the base-`b` one at
    `b = 2`, and this iff isolates the difference exactly: oddness, and
    the exponent `n = 0`.  Both extra conjuncts are needed.
    `IsRieselNumberBase 2` drops the oddness requirement, which the
    classical definition carries (A076337: "Riesel numbers: odd numbers
    n such that for all k >= 1 the numbers n*2^k - 1 are composite"),
    because at `b = 2` the non-triviality condition
    `gcd (k - 1, 1) = 1` is vacuous; and it drops `n = 0`. -/
theorem isRieselNumber_iff_base_two {k : ℕ} :
    IsRieselNumber k ↔ ¬ 2 ∣ k ∧ Composite (k - 1) ∧ IsRieselNumberBase 2 k := by
  have hzero : k * 2 ^ 0 - 1 = k - 1 := by rw [pow_zero, Nat.mul_one]
  constructor
  · rintro ⟨hodd, hcomp⟩
    refine ⟨hodd, hzero ▸ hcomp 0, ?_, fun n _ => hcomp n⟩
    rw [Nat.cast_ofNat, show ((2 : ℤ) - 1) = 1 by norm_num]
    exact isCoprime_one_right
  · rintro ⟨hodd, hzeroc, -, hbase⟩
    refine ⟨hodd, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hzero ▸ hzeroc
    · exact hbase n hn

/-- `509203` is a Riesel number base `2` in the base-`b` sense too —
    the base-2 layer is a model of the base-`b` predicate, not a
    parallel universe. -/
theorem isRieselNumberBase_two_509203 : IsRieselNumberBase 2 509203 :=
  (isRieselNumber_iff_base_two.mp isRieselNumber_509203).2.2

-- ── Wikipedia Example 1: base 6, k = 84687 ──────────────────────────

/-- The base-`6` covering data for `84687 · 6 ^ n - 1`, as triples
    `(residue, modulus, prime)`.  The primes are the covering set
    `{7, 13, 31, 37, 97}` quoted by Wikipedia, and each modulus is the
    multiplicative order of `6` modulo its prime. -/
def rieselCertBase6_84687 : Finset (ℕ × ℕ × ℕ) :=
  {(0, 2, 7), (3, 12, 13), (1, 6, 31), (1, 4, 37), (11, 12, 97)}

-- Ground checks for `rieselCertBase6_84687`.
example : rieselCertBase6_84687.card = 5 := by decide
example : ((11, 12, 97) : ℕ × ℕ × ℕ) ∈ rieselCertBase6_84687 := by decide
example : ((0, 2, 3) : ℕ × ℕ × ℕ) ∉ rieselCertBase6_84687 := by decide

/-- The divisors of the base-`6` certificate are the covering set
    `{7, 13, 31, 37, 97}` quoted in Wikipedia's Example 1. -/
theorem fixedDivisors_rieselCertBase6_84687 :
    fixedDivisors rieselCertBase6_84687 = {7, 13, 31, 37, 97} := by decide

/-- Every divisor of the base-`6` certificate is prime. -/
theorem prime_of_mem_fixedDivisors_rieselCertBase6_84687 :
    ∀ p ∈ fixedDivisors rieselCertBase6_84687, Nat.Prime p := by
  rw [fixedDivisors_rieselCertBase6_84687]
  intro p hp
  fin_cases hp <;> norm_num

/-- **The base-`6` certificate is valid.**  All four fields of
    `IsFixedDivisorSystemBase` hold for `b = 6`, `A = 84687`, `B = -1`,
    verified by kernel `decide` through `isFixedDivisorSystemBase_iff`
    at the common multiple `L = 12` of the moduli. -/
theorem isFixedDivisorSystemBase_rieselCertBase6_84687 :
    IsFixedDivisorSystemBase 6 84687 (-1) rieselCertBase6_84687 :=
  (isFixedDivisorSystemBase_iff 6 84687 (-1) rieselCertBase6_84687 12
    (by decide) (by decide)).mpr (by decide)

-- ── Drop-one negative controls for the base-6 certificate ───────────
-- Deleting any single triple leaves an exponent `n` at which *no*
-- remaining prime divides `84687 · 6 ^ n - 1`, so the certificate is
-- irredundant.

example : ¬ ∃ p ∈ fixedDivisors {(3, 12, 13), (1, 6, 31), (1, 4, 37), (11, 12, 97)},
    (p : ℤ) ∣ (84687 : ℤ) * 6 ^ 0 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 7), (1, 6, 31), (1, 4, 37), (11, 12, 97)},
    (p : ℤ) ∣ (84687 : ℤ) * 6 ^ 3 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 7), (3, 12, 13), (1, 4, 37), (11, 12, 97)},
    (p : ℤ) ∣ (84687 : ℤ) * 6 ^ 7 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 7), (3, 12, 13), (1, 6, 31), (11, 12, 97)},
    (p : ℤ) ∣ (84687 : ℤ) * 6 ^ 5 - 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 7), (3, 12, 13), (1, 6, 31), (1, 4, 37)},
    (p : ℤ) ∣ (84687 : ℤ) * 6 ^ 11 - 1 := by decide

/-- **`84687` is a Riesel number base `6`.**  Wikipedia, "Riesel
    number", § "Riesel number base b", Example 1: "All numbers
    congruent to 84687 mod 10124569 and not congruent to 1 mod 5 are
    Riesel numbers base 6, because of the covering set
    {7, 13, 31, 37, 97}."  A273987 lists it as `a(6)`, conjecturally
    the smallest; minimality is not claimed. -/
theorem isRieselNumberBase_six_84687 : IsRieselNumberBase 6 84687 := by
  have hcert : IsFixedDivisorSystemBase 6 ((84687 : ℕ) : ℤ) (-1) rieselCertBase6_84687 := by
    have hcast : ((84687 : ℕ) : ℤ) = (84687 : ℤ) := by norm_num
    rw [hcast]
    exact isFixedDivisorSystemBase_rieselCertBase6_84687
  refine isRieselNumberBase_of_isFixedDivisorSystemBase (M := 97) ?_ hcert (by decide)
    (by norm_num)
  exact isCoprime_intCast_sub_one (by norm_num) (by norm_num) (by norm_num)

-- ── The whole base-6 progression, and infinitude ────────────────────

/-- The modulus of the base-`6` Riesel progression:
    `30 · 7 · 13 · 31 · 37 · 97 = 303737070`.  Wikipedia's Example 1
    uses the bare product `10124569 = 7 · 13 · 31 · 37 · 97` together
    with the side condition "not congruent to 1 mod 5"; multiplying by
    `30` pins the residue mod `5` (hence non-triviality) once and for
    all, at the cost of thinning the progression. -/
def rieselModulusBase6 : ℕ := 303737070

-- Ground checks for `rieselModulusBase6`.
example : rieselModulusBase6 = 30 * 7 * 13 * 31 * 37 * 97 := by decide
example : rieselModulusBase6 = 30 * 10124569 := by decide  -- Wikipedia's 10124569
example : ∀ p ∈ fixedDivisors rieselCertBase6_84687, p ∣ rieselModulusBase6 := by decide
example : (84687 : ℕ) % 5 = 2 := by decide  -- ≠ 1, so non-triviality holds
example : rieselModulusBase6 % 5 = 0 := by decide

/-- The same base-`6` certificate serves the whole progression:
    shifting the coefficient by a multiple of `303737070` shifts it by
    a multiple of every covering prime.  This is
    `IsFixedDivisorSystemBase.of_dvd_sub_coeff`. -/
theorem isFixedDivisorSystemBase_riesel_base6_add_mul (t : ℕ) :
    IsFixedDivisorSystemBase 6 ((84687 + rieselModulusBase6 * t : ℕ) : ℤ) (-1)
      rieselCertBase6_84687 := by
  have hcast : ((84687 + rieselModulusBase6 * t : ℕ) : ℤ)
      = (84687 : ℤ) + 303737070 * (t : ℤ) := by
    show ((84687 + 303737070 * t : ℕ) : ℤ) = (84687 : ℤ) + 303737070 * (t : ℤ)
    push_cast
    ring
  rw [hcast]
  refine isFixedDivisorSystemBase_rieselCertBase6_84687.of_dvd_sub_coeff ?_
  intro p hp
  have hall : ∀ q ∈ fixedDivisors rieselCertBase6_84687, q ∣ 303737070 := by decide
  have hpd : (p : ℤ) ∣ (303737070 : ℤ) := by exact_mod_cast hall p hp
  have heq : (84687 : ℤ) + 303737070 * (t : ℤ) - 84687 = 303737070 * (t : ℤ) := by ring
  rw [heq]
  exact hpd.mul_right _

/-- **Every member of the progression `84687 + 303737070 · t` is a
    Riesel number base `6`.**  Non-triviality is preserved because the
    modulus is divisible by `5`, so the whole progression sits at
    `k ≡ 2 (mod 5)` and never at the excluded `k ≡ 1 (mod 5)`. -/
theorem isRieselNumberBase_six_add_mul (t : ℕ) :
    IsRieselNumberBase 6 (84687 + rieselModulusBase6 * t) := by
  refine isRieselNumberBase_of_isFixedDivisorSystemBase (M := 97) ?_
    (isFixedDivisorSystemBase_riesel_base6_add_mul t) (by decide) ?_
  · refine isCoprime_intCast_sub_one (by omega) (by norm_num) ?_
    show Nat.Coprime (84687 + rieselModulusBase6 * t - 1) (6 - 1)
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr ?_)
    show ¬ (5 : ℕ) ∣ 84687 + 303737070 * t - 1
    omega
  · show 97 + 1 < (84687 + 303737070 * t) * 6
    omega

/-- **Infinitely many Riesel numbers base `6` exist.**  Beyond every
    bound `B` there is one, namely `84687 + 303737070 · (B + 1)`.  This
    is the base-`6` case of Wikipedia's "For every integer b ≥ 2, there
    are infinitely many Riesel numbers base b". -/
theorem exists_lt_isRieselNumberBase_six (B : ℕ) :
    ∃ k, B < k ∧ IsRieselNumberBase 6 k := by
  refine ⟨84687 + rieselModulusBase6 * (B + 1), ?_, isRieselNumberBase_six_add_mul (B + 1)⟩
  show B < 84687 + 303737070 * (B + 1)
  omega

/-- The set of Riesel numbers base `6` is infinite. -/
theorem infinite_setOf_isRieselNumberBase_six :
    {k : ℕ | IsRieselNumberBase 6 k}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨k, hk, hkR⟩ := exists_lt_isRieselNumberBase_six B
  have hle : k ≤ B := hB hkR
  omega

-- ── Wikipedia Example 2: k = 6, infinitely many BASES ───────────────

/-- The two-class covering data behind Wikipedia's Example 2, as
    triples `(residue, modulus, prime)`: `5` divides `6 · b ^ n - 1`
    for even `n` and `7` divides it for odd `n`, whenever
    `b ≡ 34 (mod 35)`.

    Both moduli are `2`, so — like the base-`6` certificate — this is a
    cover without distinct moduli, hence not an `IsCoveringSystem` in
    the classical sense of `Erdos.Covering.Basic`. -/
def rieselCertSixBase34 : Finset (ℕ × ℕ × ℕ) := {(0, 2, 5), (1, 2, 7)}

example : fixedDivisors rieselCertSixBase34 = {5, 7} := by decide

/-- The certificate is valid at the base `34`, the least base in the
    class `34 (mod 35)`. -/
theorem isFixedDivisorSystemBase_rieselCertSixBase34 :
    IsFixedDivisorSystemBase 34 6 (-1) rieselCertSixBase34 :=
  (isFixedDivisorSystemBase_iff 34 6 (-1) rieselCertSixBase34 2
    (by decide) (by decide)).mpr (by decide)

/-- **`6` is a Riesel number to every base `b ≡ 34 (mod 35)`.**
    Wikipedia, "Riesel number", § "Riesel number base b", Example 2:
    "6 is a Riesel number to all bases b congruent to 34 mod 35,
    because if b is congruent to 34 mod 35, then 6×b^n − 1 is divisible
    by 5 for all even n and divisible by 7 for all odd n. Besides, 6 is
    not a trivial k in these bases b since gcd(6 − 1, b − 1) = 1 for
    these bases b."

    The base moves by `IsFixedDivisorSystemBase.of_modEq_base`, the one
    translation with no base-2 counterpart: a single certificate,
    checked once at `b = 34`, transports to every base in the class. -/
theorem isRieselNumberBase_six_of_modEq_34 {b : ℕ} (hb : b % 35 = 34) :
    IsRieselNumberBase b 6 := by
  have hcert : IsFixedDivisorSystemBase b ((6 : ℕ) : ℤ) (-1) rieselCertSixBase34 := by
    have hcast : ((6 : ℕ) : ℤ) = (6 : ℤ) := by norm_num
    rw [hcast]
    refine isFixedDivisorSystemBase_rieselCertSixBase34.of_modEq_base ?_
    intro p hp
    have hp' : p ∈ ({5, 7} : Finset ℕ) := by
      rw [show fixedDivisors rieselCertSixBase34 = {5, 7} from by decide] at hp
      exact hp
    fin_cases hp'
    · show b % 5 = 34 % 5
      omega
    · show b % 7 = 34 % 7
      omega
  refine isRieselNumberBase_of_isFixedDivisorSystemBase (M := 7) ?_ hcert (by decide) (by omega)
  refine isCoprime_intCast_sub_one (by norm_num) (by omega) ?_
  show Nat.Coprime (6 - 1) (b - 1)
  exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by omega)

/-- **Infinitely many bases make `6` a Riesel number.**  Beyond every
    bound `B` there is such a base, namely `34 + 35 · (B + 1)`.  This
    is the statement the base parameter buys and base `2` cannot
    express. -/
theorem exists_lt_isRieselNumberBase_six_base (B : ℕ) :
    ∃ b, B < b ∧ IsRieselNumberBase b 6 := by
  have hb : (34 + 35 * (B + 1)) % 35 = 34 := by omega
  exact ⟨34 + 35 * (B + 1), by omega, isRieselNumberBase_six_of_modEq_34 hb⟩

/-- The set of bases to which `6` is a Riesel number is infinite. -/
theorem infinite_setOf_isRieselNumberBase_six_base :
    {b : ℕ | IsRieselNumberBase b 6}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨b, hb, hbR⟩ := exists_lt_isRieselNumberBase_six_base B
  have hle : b ≤ B := hB hbR
  omega

-- ── Non-vacuity of the base-b headline theorems ─────────────────────

-- The first few members of the base-`6` family at `k = 84687` are
-- genuinely composite, certified independently of the covering
-- argument.
example : Composite (84687 * 6 ^ 1 - 1) := ⟨by norm_num, by norm_num⟩  -- 508121 = 31·37·443
example : Composite (84687 * 6 ^ 2 - 1) := ⟨by norm_num, by norm_num⟩  -- 3048731 = 7·435533
example : Composite (84687 * 6 ^ 3 - 1) := ⟨by norm_num, by norm_num⟩  -- 18292391 = 13·1407107

-- … and they are the values the theorem speaks about.
example : 84687 * 6 ^ 3 - 1 = 18292391 := by decide
example : Composite 18292391 := isRieselNumberBase_six_84687.2 3 (by norm_num)

-- The predicted divisor, class by class.
example : (7 : ℕ) ∣ 84687 * 6 ^ 2 - 1 := by decide    -- n ≡ 0 (mod 2)
example : (13 : ℕ) ∣ 84687 * 6 ^ 3 - 1 := by decide   -- n ≡ 3 (mod 12)
example : (31 : ℕ) ∣ 84687 * 6 ^ 7 - 1 := by decide   -- n ≡ 1 (mod 6)
example : (37 : ℕ) ∣ 84687 * 6 ^ 5 - 1 := by decide   -- n ≡ 1 (mod 4)
example : (97 : ℕ) ∣ 84687 * 6 ^ 11 - 1 := by decide  -- n ≡ 11 (mod 12)

-- Example 2 at its least base: `6 · 34 ^ n - 1`.
example : Composite (6 * 34 ^ 1 - 1) := ⟨by norm_num, by norm_num⟩  -- 203 = 7·29
example : Composite (6 * 34 ^ 2 - 1) := ⟨by norm_num, by norm_num⟩  -- 6935 = 5·19·73
example : Composite 203 :=
  (isRieselNumberBase_six_of_modEq_34 (b := 34) (by decide)).2 1 (by norm_num)

-- THE `n ≥ 1` BOUND IS LOAD-BEARING, not a convention we could drop:
-- at `n = 0` the value is `6 - 1 = 5`, which is prime.  This is why
-- `IsRieselNumberBase` quantifies over `n ≥ 1` and why
-- `isRieselNumber_iff_base_two` needs its extra `Composite (k - 1)`
-- conjunct.
example : ¬ Composite (6 * 34 ^ 0 - 1) := fun h => h.2 (by norm_num)

-- ════════════════════════════════════════════════════════════════════
-- §7 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms IsRieselNumber
#print axioms cast_riesel_family
#print axioms rieselCert509203
#print axioms fixedDivisors_rieselCert509203
#print axioms image_snd_residueClasses_rieselCert509203
#print axioms prime_of_mem_fixedDivisors_rieselCert509203
#print axioms isCoveringSystem_rieselCert509203
#print axioms isFixedDivisorSystem_rieselCert509203
#print axioms isRieselNumber_of_isFixedDivisorSystem
#print axioms isRieselNumber_509203
#print axioms rieselModulus
#print axioms isFixedDivisorSystem_riesel_add_mul
#print axioms isRieselNumber_add_mul
#print axioms exists_lt_isRieselNumber
#print axioms infinite_setOf_isRieselNumber
#print axioms IsRieselNumberBase
#print axioms isCoprime_intCast_sub_one
#print axioms cast_riesel_base_family
#print axioms isRieselNumberBase_of_isFixedDivisorSystemBase
#print axioms isRieselNumber_iff_base_two
#print axioms isRieselNumberBase_two_509203
#print axioms rieselCertBase6_84687
#print axioms fixedDivisors_rieselCertBase6_84687
#print axioms prime_of_mem_fixedDivisors_rieselCertBase6_84687
#print axioms isFixedDivisorSystemBase_rieselCertBase6_84687
#print axioms isRieselNumberBase_six_84687
#print axioms rieselModulusBase6
#print axioms isFixedDivisorSystemBase_riesel_base6_add_mul
#print axioms isRieselNumberBase_six_add_mul
#print axioms exists_lt_isRieselNumberBase_six
#print axioms infinite_setOf_isRieselNumberBase_six
#print axioms rieselCertSixBase34
#print axioms isFixedDivisorSystemBase_rieselCertSixBase34
#print axioms isRieselNumberBase_six_of_modEq_34
#print axioms exists_lt_isRieselNumberBase_six_base
#print axioms infinite_setOf_isRieselNumberBase_six_base

end Erdos.Covering
