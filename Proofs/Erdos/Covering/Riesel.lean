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
-- §6 AXIOM AUDIT
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

end Erdos.Covering
