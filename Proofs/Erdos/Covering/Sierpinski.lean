/-
  Sierpiński numbers: `78557` is one, as an instance of the general
  fixed-divisor theorem of `Erdos.Covering.FixedDivisor`.

  A *Sierpiński number* is an odd `k` such that `k · 2 ^ n + 1` is
  composite for every `n : ℕ`.  Sierpiński (1960) proved infinitely
  many exist; Selfridge (1962, unpublished) exhibited `78557` with the
  covering set `{3, 5, 7, 13, 19, 37, 73}`, conjecturally the least
  Sierpiński number.

  ── The certificate ─────────────────────────────────────────────────
  Seven triples `(a, d, p)` — residue, modulus, prime:

    | a  |  0 |  1 |  1 | 11 | 15 | 27 |  3 |
    | d  |  2 |  4 |  3 | 12 | 18 | 36 |  9 |
    | p  |  3 |  5 |  7 | 13 | 19 | 37 | 73 |

  The moduli `{2, 4, 3, 12, 18, 36, 9}` are pairwise distinct, all
  exceed `1`, all divide `L = 36`, and the seven classes cover every
  residue mod `36` with no gap.  `ord_p(2)` equals `d` in every column,
  so `2 ^ d ≡ 1 (mod p)`; and `p ∣ 78557 · 2 ^ a + 1` in every column.
  All of this is verified by kernel `decide` through
  `isFixedDivisorSystem_iff` at `L = 36`.

  ── Prior art (read before claiming anything) ───────────────────────
  * **ACL2, Cowles–Gamboa 2011.**  "Verifying Sierpiński and Riesel
    Numbers in ACL2", EPTCS 70, 31–39, arXiv:1110.4671, machine-checked
    that `78557` is a Sierpiński number:
    `books/workshops/2011/cowles-gamboa-sierpinski/support/`
    `verifying-macros.lisp` line 771 invokes
    `(verify-sierpinski sierpinski-witness-78557 78557 (3 5 7 13 19 37 73))`.
    **The concrete number is theirs first.**  What they did not do is
    formalize the general criterion: their macro emits per-number proof
    obligations and the emission process is itself unverified.
  * **Lean 4, google-deepmind/formal-conjectures.**
    `FormalConjectures/Wikipedia/SierpinskiNumber.lean` contains a
    sorry-free `theorem selfridge_78557 : Nat.IsSierpinskiNumber 78557`.
    **It is therefore not a Lean first either.**  That proof uses
    `native_decide` twice — once for the 36 base residues, once for
    `(2 : ℕ) ^ 36 ≡ 1 [MOD p]` at each covering prime (a multiple of
    the order, equal to it only at `p = 37`; order minimality is no
    more needed there than here) — and is bespoke to `78557`; it
    proves no general statement.

  Our contribution, stated precisely: `isSierpinskiNumber_78557` is an
  instantiation of `IsFixedDivisorSystem.composite`, a theorem about
  arbitrary `A · 2 ^ n + B`, at `A = 78557`, `B = 1`; it uses kernel
  `decide` only, so `#print axioms` reports no `ofReduceBool` and no
  compiler-minted decidability axiom; and the same general theorem
  yields `Erdos.Covering.Riesel` and the Erdős-1950 retrofit with no new
  covering-system mathematics.  We claim no priority on the number.

  ── Contents ────────────────────────────────────────────────────────
  * `IsSierpinskiNumber` — matching `Nat.IsSierpinskiNumber` of
    formal-conjectures, with non-examples pinning it.
  * `sierpinskiCert78557` — the seven-triple certificate, with ground
    checks and drop-one negative controls.
  * `isSierpinskiNumber_of_isFixedDivisorSystem` — the general
    Sierpiński criterion: odd `k` plus any certificate for `(k, 1)`
    whose divisors are bounded by some `M < k`.
  * `isSierpinskiNumber_78557` — Selfridge's number.
  * `isSierpinskiNumber_add_mul`, `exists_lt_isSierpinskiNumber` —
    the whole progression `78557 + 140100870 · t`, hence Sierpiński's
    1960 infinitude theorem.
  * §6, base `b` (all of it downstream of
    `IsFixedDivisorSystemBase`, none of it touching the base-2
    material above):
      - `IsSierpinskiNumberBase b k` — A123159's predicate, quoted
        verbatim at the definition, with its `n ≥ 1` convention.
      - `isSierpinskiNumberBase_of_isFixedDivisorSystemBase` — the
        base-`b` criterion.
      - `isSierpinskiNumber_iff_base_two` — the exact difference
        between the two predicates at `b = 2`: oddness and the
        exponent `0`.
      - `isSierpinskiNumberBase_fourteen_four`,
        `isSierpinskiNumberBase_fourteen_add_mul`,
        `infinite_setOf_isSierpinskiNumberBase_fourteen` — A123159's
        `a(14) = 4`, its progression and its infinitude.
      - `not_composite_four_mul_fourteen_pow_zero_add_one` — the
        `n = 0` failure that A146563's comment overstates away, kept
        as a theorem.

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

/-- `k` is a **Sierpiński number**: `k` is odd and `k · 2 ^ n + 1` is
    composite for every natural number `n`.

    This matches `Nat.IsSierpinskiNumber` of
    google-deepmind/formal-conjectures
    (`FormalConjecturesForMathlib/NumberTheory/SierpinskiNumber.lean`):
    `def IsSierpinskiNumber (k : ℕ) : Prop := ¬ 2 ∣ k ∧ ∀ n, (k * 2 ^ n + 1).Composite`,
    with `Erdos.Covering.Composite` standing in for their
    `Nat.Composite` (`1 < n ∧ ¬n.Prime`), which current Mathlib does
    not provide.  Oddness is what makes the predicate non-vacuous —
    `¬ 2 ∣ k` also forces `k ≠ 0`, so no positivity hypothesis is
    needed. -/
def IsSierpinskiNumber (k : ℕ) : Prop :=
  ¬ 2 ∣ k ∧ ∀ n, Composite (k * 2 ^ n + 1)

-- Ground checks for `IsSierpinskiNumber`: the predicate is not
-- satisfied by small numbers, for each of the two possible reasons.

-- `2` is even.
example : ¬ IsSierpinskiNumber 2 := fun h => h.1 (by decide)

-- `1 · 2 ^ 0 + 1 = 2` is prime.
example : ¬ IsSierpinskiNumber 1 := fun h => (h.2 0).2 (by norm_num)

-- `3 · 2 ^ 1 + 1 = 7` is prime, though `3 · 2 ^ 0 + 1 = 4` is not.
example : ¬ IsSierpinskiNumber 3 := fun h => (h.2 1).2 (by norm_num)
example : Composite (3 * 2 ^ 0 + 1) := ⟨by norm_num, by norm_num⟩

-- `5 · 2 ^ 1 + 1 = 11` is prime.
example : ¬ IsSierpinskiNumber 5 := fun h => (h.2 1).2 (by norm_num)

-- ════════════════════════════════════════════════════════════════════
-- §2 THE CERTIFICATE FOR 78557
-- ════════════════════════════════════════════════════════════════════

/-- Selfridge's covering data for `78557 · 2 ^ n + 1`, as triples
    `(residue, modulus, prime)`.  The primes are the classical covering
    set `{3, 5, 7, 13, 19, 37, 73}` and each modulus is the
    multiplicative order of `2` modulo its prime. -/
def sierpinskiCert78557 : Finset (ℕ × ℕ × ℕ) :=
  {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19), (27, 36, 37), (3, 9, 73)}

-- Ground checks for `sierpinskiCert78557`.
example : sierpinskiCert78557.card = 7 := by decide
example : ((27, 36, 37) : ℕ × ℕ × ℕ) ∈ sierpinskiCert78557 := by decide
example : ((5, 6, 43) : ℕ × ℕ × ℕ) ∉ sierpinskiCert78557 := by decide

/-- The divisors of the certificate are the covering set quoted in the
    literature (Wikipedia, "Sierpiński number"; Cowles–Gamboa's ACL2
    invocation `(verify-sierpinski … 78557 (3 5 7 13 19 37 73))`). -/
theorem fixedDivisors_sierpinskiCert78557 :
    fixedDivisors sierpinskiCert78557 = {3, 5, 7, 13, 19, 37, 73} := by decide

/-- Every divisor of the certificate is prime. -/
theorem prime_of_mem_fixedDivisors_sierpinskiCert78557 :
    ∀ p ∈ fixedDivisors sierpinskiCert78557, Nat.Prime p := by
  rw [fixedDivisors_sierpinskiCert78557]
  intro p hp
  fin_cases hp <;> norm_num

/-- The classes of the certificate form a covering system in the
    classical distinct-moduli sense of `Erdos.Covering.Basic`: moduli
    `{2, 4, 3, 12, 18, 36, 9}`, pairwise distinct, all exceeding `1`,
    covering ℤ.  Verified by `decide` at the common multiple `L = 36`.

    The general theorem needs only `Covers`; this records that the data
    really is a covering system and not a degenerate cover. -/
theorem isCoveringSystem_sierpinskiCert78557 :
    IsCoveringSystem (residueClasses sierpinskiCert78557) :=
  (isCoveringSystem_iff 36 (by decide) (by decide)).mpr (by decide)

/-- **The certificate is valid.**  All four fields of
    `IsFixedDivisorSystem` hold for `A = 78557`, `B = 1`, verified by
    kernel `decide` through `isFixedDivisorSystem_iff` at the common
    multiple `L = 36` of the moduli. -/
theorem isFixedDivisorSystem_sierpinskiCert78557 :
    IsFixedDivisorSystem 78557 1 sierpinskiCert78557 :=
  (isFixedDivisorSystem_iff 78557 1 sierpinskiCert78557 36 (by decide) (by decide)).mpr
    (by decide)

-- ── Drop-one negative controls ──────────────────────────────────────
-- Deleting any single triple leaves an exponent `n` at which *no*
-- remaining prime divides `78557 · 2 ^ n + 1`, so the certificate is
-- irredundant: no proper subset certifies anything.  (Each prime
-- divides on exactly one class modulo its own modulus, so an uncovered
-- residue really is an undivided exponent.)

example : ¬ ∃ p ∈ fixedDivisors {(1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19),
    (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 0 + 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 3, 7), (11, 12, 13), (15, 18, 19),
    (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 5 + 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (11, 12, 13), (15, 18, 19),
    (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 7 + 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (15, 18, 19),
    (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 11 + 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13),
    (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 15 + 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13),
    (15, 18, 19), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 27 + 1 := by decide

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13),
    (15, 18, 19), (27, 36, 37)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 3 + 1 := by decide

-- ════════════════════════════════════════════════════════════════════
-- §3 THE SIERPIŃSKI CRITERION AND SELFRIDGE'S NUMBER
-- ════════════════════════════════════════════════════════════════════

/-- **The Sierpiński criterion.**  An odd `k` is a Sierpiński number as
    soon as the family `n ↦ k · 2 ^ n + 1` admits *any* fixed-divisor
    certificate whose divisors are bounded by some `M < k`.

    Only `M < k` is needed for the compositeness bound, because
    `k · 2 ^ n + 1 > k` for every `n`.  Unlike the Erdős-1950 setting
    there is no top-end problem: the family grows without bound and no
    dyadic-block argument is required. -/
theorem isSierpinskiNumber_of_isFixedDivisorSystem {k M : ℕ} {T : Finset (ℕ × ℕ × ℕ)}
    (hodd : ¬ 2 ∣ k) (h : IsFixedDivisorSystem (k : ℤ) 1 T)
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hMk : M < k) :
    IsSierpinskiNumber k := by
  refine ⟨hodd, fun n => ?_⟩
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hgrow : k * 1 ≤ k * 2 ^ n := Nat.mul_le_mul_left k h1
  have hN : ((k * 2 ^ n + 1 : ℕ) : ℤ) = (k : ℤ) * 2 ^ n + 1 := by push_cast; ring
  exact h.composite hM hN (by omega)

/-- **`78557` is a Sierpiński number.**  Selfridge (1962), via the
    covering set `{3, 5, 7, 13, 19, 37, 73}`; machine-verified first by
    Cowles–Gamboa in ACL2 (2011) and in Lean by
    google-deepmind/formal-conjectures (`selfridge_78557`, using
    `native_decide`).  Here it is the `A = 78557`, `B = 1` instance of
    `IsFixedDivisorSystem.composite`, with kernel `decide` only. -/
theorem isSierpinskiNumber_78557 : IsSierpinskiNumber 78557 := by
  have hcert : IsFixedDivisorSystem ((78557 : ℕ) : ℤ) 1 sierpinskiCert78557 := by
    have hcast : ((78557 : ℕ) : ℤ) = (78557 : ℤ) := by norm_num
    rw [hcast]
    exact isFixedDivisorSystem_sierpinskiCert78557
  exact isSierpinskiNumber_of_isFixedDivisorSystem (M := 73) (by decide) hcert
    (by decide) (by decide)

-- ════════════════════════════════════════════════════════════════════
-- §4 THE WHOLE PROGRESSION, AND INFINITUDE
-- ════════════════════════════════════════════════════════════════════

/-- The modulus of the Sierpiński progression:
    `2 · 3 · 5 · 7 · 13 · 19 · 37 · 73 = 140100870`, the product of the
    covering set with an extra factor `2` to preserve oddness. -/
def sierpinskiModulus : ℕ := 140100870

-- Ground checks for `sierpinskiModulus`.
example : sierpinskiModulus = 2 * 3 * 5 * 7 * 13 * 19 * 37 * 73 := by decide
example : ∀ p ∈ fixedDivisors sierpinskiCert78557, p ∣ sierpinskiModulus := by decide
example : sierpinskiModulus % 2 = 0 := by decide
example : (78557 : ℕ) % 2 = 1 := by decide

/-- The same certificate serves the whole progression: shifting the
    coefficient by a multiple of `140100870` shifts it by a multiple of
    every covering prime.  This is
    `IsFixedDivisorSystem.of_dvd_sub_coeff`. -/
theorem isFixedDivisorSystem_sierpinski_add_mul (t : ℕ) :
    IsFixedDivisorSystem ((78557 + sierpinskiModulus * t : ℕ) : ℤ) 1
      sierpinskiCert78557 := by
  have hcast : ((78557 + sierpinskiModulus * t : ℕ) : ℤ)
      = (78557 : ℤ) + 140100870 * (t : ℤ) := by
    show ((78557 + 140100870 * t : ℕ) : ℤ) = (78557 : ℤ) + 140100870 * (t : ℤ)
    push_cast
    ring
  rw [hcast]
  refine isFixedDivisorSystem_sierpinskiCert78557.of_dvd_sub_coeff ?_
  intro p hp
  have hall : ∀ q ∈ fixedDivisors sierpinskiCert78557, q ∣ 140100870 := by decide
  have hpd : (p : ℤ) ∣ (140100870 : ℤ) := by exact_mod_cast hall p hp
  have heq : (78557 : ℤ) + 140100870 * (t : ℤ) - 78557 = 140100870 * (t : ℤ) := by ring
  rw [heq]
  exact hpd.mul_right _

/-- **Every member of the progression `78557 + 140100870 · t` is a
    Sierpiński number** — the certificate translates along the
    progression by `IsFixedDivisorSystem.of_dvd_sub_coeff`, the modulus
    being twice the product of the covering primes.  Oddness is
    preserved because that modulus is even. -/
theorem isSierpinskiNumber_add_mul (t : ℕ) :
    IsSierpinskiNumber (78557 + sierpinskiModulus * t) := by
  refine isSierpinskiNumber_of_isFixedDivisorSystem (M := 73) ?_
    (isFixedDivisorSystem_sierpinski_add_mul t) (by decide) ?_
  · show ¬ 2 ∣ 78557 + 140100870 * t
    omega
  · show 73 < 78557 + 140100870 * t
    omega

/-- **Sierpiński (1960): infinitely many Sierpiński numbers exist.**
    Beyond every bound `B` there is a Sierpiński number, namely
    `78557 + 140100870 · (B + 1)`. -/
theorem exists_lt_isSierpinskiNumber (B : ℕ) :
    ∃ k, B < k ∧ IsSierpinskiNumber k := by
  refine ⟨78557 + sierpinskiModulus * (B + 1), ?_, isSierpinskiNumber_add_mul (B + 1)⟩
  show B < 78557 + 140100870 * (B + 1)
  omega

/-- The set of Sierpiński numbers is infinite. -/
theorem infinite_setOf_isSierpinskiNumber :
    {k : ℕ | IsSierpinskiNumber k}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨k, hk, hkS⟩ := exists_lt_isSierpinskiNumber B
  have hle : k ≤ B := hB hkS
  omega

-- ════════════════════════════════════════════════════════════════════
-- §5 NON-VACUITY OF THE HEADLINE THEOREM
-- ════════════════════════════════════════════════════════════════════

-- The inner `∀ n` of `isSierpinskiNumber_78557` is not vacuous, and
-- its conclusion is not trivially true: the first few members of the
-- family are genuinely composite, certified independently of the
-- covering argument.
example : Composite (78557 * 2 ^ 0 + 1) := ⟨by norm_num, by norm_num⟩  -- 78558 = 2·3·13093
example : Composite (78557 * 2 ^ 1 + 1) := ⟨by norm_num, by norm_num⟩  -- 157115 = 5·7·67²
example : Composite (78557 * 2 ^ 2 + 1) := ⟨by norm_num, by norm_num⟩  -- 314229 = 3·104743
example : Composite (78557 * 2 ^ 3 + 1) := ⟨by norm_num, by norm_num⟩  -- 628457 = 73·8609

-- … and they are the values the theorem speaks about.
example : 78557 * 2 ^ 3 + 1 = 628457 := by decide
example : Composite 628457 := isSierpinskiNumber_78557.2 3

-- The predicted divisor, class by class, matching the table in the
-- module header.
example : (3 : ℕ) ∣ 78557 * 2 ^ 0 + 1 := by decide    -- n ≡ 0 (mod 2)
example : (5 : ℕ) ∣ 78557 * 2 ^ 1 + 1 := by decide    -- n ≡ 1 (mod 4)
example : (7 : ℕ) ∣ 78557 * 2 ^ 4 + 1 := by decide    -- n ≡ 1 (mod 3)
example : (13 : ℕ) ∣ 78557 * 2 ^ 11 + 1 := by decide  -- n ≡ 11 (mod 12)
example : (19 : ℕ) ∣ 78557 * 2 ^ 15 + 1 := by decide  -- n ≡ 15 (mod 18)
example : (37 : ℕ) ∣ 78557 * 2 ^ 27 + 1 := by decide  -- n ≡ 27 (mod 36)
example : (73 : ℕ) ∣ 78557 * 2 ^ 3 + 1 := by decide   -- n ≡ 3 (mod 9)

-- ════════════════════════════════════════════════════════════════════
-- §6 SIERPIŃSKI NUMBERS TO AN ARBITRARY BASE
-- ════════════════════════════════════════════════════════════════════

/-! Everything above is base `2`.  The general fixed-divisor theorem of
`Erdos.Covering.FixedDivisor` is stated for an arbitrary base `b`, and
this section spends that generality on the base-`b` Sierpiński problem.

── Source, verbatim (`goof oeis show A123159`, 2026-08-05) ──────────

  name: "Conjectured smallest Sierpiński numbers of the second kind S,
    base b=2,3,4,5,..., where S*b^n+1 is composite for all n>=1 and
    gcd(S+1, b-1) = 1."
  terms: "78557,125050976086,66741,159986,174308,1112646039348,1,2344,
    9175,1490,521,132,4,91218919470156,2500,278,398,765174,8,1002,
    6694,182,30651,262638,221,8,4554,4,867,6360528,1,1854,6,214018,
    1886,2604,14,166134,826477,8,13372,2256,4,53474"
  comment: "Some values with base b=2^x+1 for integers x have also been
    calculated - see the links."
  xrefs: "Cf. A076336."

Indexing starts at `b = 2`, so `a(2) = 78557` and `a(14) = 4`.  The
sequence name says *conjectured*; MINIMALITY IS NOT CLAIMED HERE.
What is proved is that `4` IS a Sierpiński number base `14`.

── Source, verbatim (`goof oeis show A146563`, 2026-08-05) ──────────

  name: "First instance prime-cover Sierpinski bases."
  comment: "A prime-cover Sierpinski base is the lowest base b such
    that k*b^n + 1 can generate a Sierpinski number from cover sets
    with prime length. For example, b = 14 provides Sierpinski number
    k = 4 such that 4*14^n + 1 is always composite for any integer n.
    The covering set comprises 2 primes each providing prime factors
    for even or odd values of n in k*b^n + 1, so-called 2-cover, 2 =
    1st prime. Sequence generated for 2-, 3-, 5- 7- and 11-cover."

SOURCE DISCREPANCY, FLAGGED RATHER THAN COPIED.  A146563's comment
says `4 * 14 ^ n + 1` is "always composite for any integer n".  That is
FALSE at `n = 0`: `4 · 14 ^ 0 + 1 = 5` is prime, and it is prime for
the covering prime's own reason — `5` is the certificate's divisor for
the even class, and at `n = 0` the divisor equals the value.  A123159's
"for all n>=1" is the correct convention and the one formalized here;
the failure at `n = 0` is recorded as a theorem below
(`not_composite_four_mul_fourteen_pow_zero_add_one`), not glossed. -/

/-- `k` is a **Sierpiński number base `b`**: `gcd (k + 1, b - 1) = 1` —
    the non-triviality condition, stated over ℤ so that the ℕ
    subtraction `b - 1` is not truncated — and `k · b ^ n + 1` is
    composite for every `n ≥ 1`.

    This is A123159's definition, quoted verbatim above, with its
    `n ≥ 1` convention.  The bound is not cosmetic: `4 · 14 ^ 0 + 1 = 5`
    is prime, so no base-`b` statement can quantify over `n ≥ 0`
    uniformly.  `IsSierpinskiNumber` (base 2, `∀ n`) is therefore
    *stronger* than `IsSierpinskiNumberBase 2` rather than equal to it;
    `isSierpinskiNumber_iff_base_two` records the exact difference.

    Non-triviality is what `¬ 2 ∣ k` cannot be: at `b = 2` the
    condition `gcd (k + 1, 1) = 1` is vacuous, which is why the
    classical base-2 definition uses oddness instead.  Neither
    condition implies the other, and the bridge theorem carries
    both. -/
def IsSierpinskiNumberBase (b k : ℕ) : Prop :=
  IsCoprime ((k : ℤ) + 1) ((b : ℤ) - 1) ∧ ∀ n, 1 ≤ n → Composite (k * b ^ n + 1)

/-- The non-triviality condition transported from ℕ, where it is
    checkable, to the ℤ statement of `IsSierpinskiNumberBase`. -/
theorem isCoprime_intCast_add_one {k b : ℕ} (hb : 1 ≤ b)
    (h : Nat.Coprime (k + 1) (b - 1)) : IsCoprime ((k : ℤ) + 1) ((b : ℤ) - 1) := by
  have hkc : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  have hbc : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hb]; norm_num
  rw [hkc, hbc]
  exact Nat.isCoprime_iff_coprime.mpr h

-- Ground checks for `IsSierpinskiNumberBase`.

-- `12` fails base `14` on non-triviality alone: `gcd (13, 13) = 13`,
-- and indeed `13 ∣ 12 · 14 ^ n + 1` for every `n`.
example : ¬ IsSierpinskiNumberBase 14 12 := by
  rintro ⟨hcop, -⟩
  have h13 : (13 : ℤ) ∣ ((12 : ℤ) + 1) := by norm_num
  have h13' : (13 : ℤ) ∣ ((14 : ℤ) - 1) := by norm_num
  have hunit : (13 : ℤ) = 1 ∨ (13 : ℤ) = -1 :=
    Int.isUnit_iff.mp (hcop.isUnit_of_dvd' h13 h13')
  omega

-- `1` fails base `14` on compositeness: `1 · 14 + 1 = 15` is composite
-- but `1 · 14 ^ 2 + 1 = 197` is prime.
example : ¬ IsSierpinskiNumberBase 14 1 := fun h => (h.2 2 (by norm_num)).2 (by norm_num)

-- Degenerate bases are excluded by the predicate itself, with no
-- `2 ≤ b` hypothesis needed: at `b = 1` the family is the constant
-- `k + 1`, and non-triviality forces `k = 0`, at which that constant
-- is `1` and not composite.
example (k : ℕ) : ¬ IsSierpinskiNumberBase 1 k := by
  rintro ⟨hcop, hcomp⟩
  have hval : Composite (k * 1 ^ 1 + 1) := hcomp 1 (by norm_num)
  rw [pow_one, mul_one] at hval
  have hk1 : 1 ≤ k := by have hlt := hval.1; omega
  rw [Nat.cast_one, sub_self] at hcop
  have hunit : (k : ℤ) + 1 = 1 ∨ (k : ℤ) + 1 = -1 :=
    Int.isUnit_iff.mp (isCoprime_zero_right.mp hcop)
  omega

-- At `b = 0` the family is the constant `1` for every `n ≥ 1`.
example (k : ℕ) : ¬ IsSierpinskiNumberBase 0 k := by
  rintro ⟨-, hcomp⟩
  have hval : Composite (k * 0 ^ 1 + 1) := hcomp 1 (by norm_num)
  rw [pow_one, Nat.mul_zero] at hval
  exact absurd hval.1 (by norm_num)

/-- **The Sierpiński criterion, base `b`.**  `k` is a Sierpiński number
    base `b` as soon as it passes the non-triviality test and the
    family `n ↦ k · b ^ n + 1` admits *any* base-`b` fixed-divisor
    certificate whose divisors are bounded by some `M < k · b + 1`.

    The bound is `M < k · b + 1`, not `M < k`, because the quantifier
    starts at `n = 1`: the smallest certified value is `k · b + 1`.  In
    base `2` this is weaker than
    `isSierpinskiNumber_of_isFixedDivisorSystem`'s `M < k`, and the
    slack is exactly what lets a multiplier as small as `k = 4` work in
    base `14`, where `k = 4 < 5 = M` and the base-2 criterion would not
    apply. -/
theorem isSierpinskiNumberBase_of_isFixedDivisorSystemBase {b k M : ℕ}
    {T : Finset (ℕ × ℕ × ℕ)} (hcop : IsCoprime ((k : ℤ) + 1) ((b : ℤ) - 1))
    (h : IsFixedDivisorSystemBase b (k : ℤ) 1 T)
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hMk : M < k * b + 1) :
    IsSierpinskiNumberBase b k := by
  refine ⟨hcop, fun n hn => ?_⟩
  have hpow : b ≤ b ^ n := Nat.le_self_pow (by omega) b
  have hgrow : k * b ≤ k * b ^ n := Nat.mul_le_mul_left k hpow
  have hN : ((k * b ^ n + 1 : ℕ) : ℤ) = (k : ℤ) * (b : ℤ) ^ n + 1 := by push_cast; ring
  exact h.composite hM hN (by omega)

/-- The base-2 predicate is strictly stronger than the base-`b` one at
    `b = 2`, by exactly the exponent `n = 0` and the oddness
    requirement.  Both extra conjuncts are needed:
    `IsSierpinskiNumberBase 2` drops oddness, which the classical
    definition carries (A076336: "(Provable) Sierpiński numbers: odd
    numbers n such that for all k >= 1 the numbers n*2^k + 1 are
    composite"), and it drops `n = 0`. -/
theorem isSierpinskiNumber_iff_base_two {k : ℕ} :
    IsSierpinskiNumber k ↔ ¬ 2 ∣ k ∧ Composite (k + 1) ∧ IsSierpinskiNumberBase 2 k := by
  have hzero : k * 2 ^ 0 + 1 = k + 1 := by rw [pow_zero, Nat.mul_one]
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

/-- `78557` is a Sierpiński number base `2` in the base-`b` sense too —
    the base-2 layer is a model of the base-`b` predicate, not a
    parallel universe. -/
theorem isSierpinskiNumberBase_two_78557 : IsSierpinskiNumberBase 2 78557 :=
  (isSierpinskiNumber_iff_base_two.mp isSierpinskiNumber_78557).2.2

-- ── A123159's `a(14) = 4`: base 14, k = 4 ───────────────────────────

/-- The base-`14` covering data for `4 · 14 ^ n + 1`, as triples
    `(residue, modulus, prime)`.  `3` divides the family at odd
    exponents, `5` at even ones; this is A146563's "2-cover".

    Both moduli are `2`, so this is a cover *without distinct moduli*,
    hence not an `IsCoveringSystem` in the classical Erdős sense of
    `Erdos.Covering.Basic` — only `Covers` is a field of
    `IsFixedDivisorSystemBase`, and the base-`b` witnesses are where
    that gap starts to matter. -/
def sierpinskiCertBase14_4 : Finset (ℕ × ℕ × ℕ) := {(1, 2, 3), (0, 2, 5)}

-- Ground checks for `sierpinskiCertBase14_4`.
example : sierpinskiCertBase14_4.card = 2 := by decide
example : ((0, 2, 5) : ℕ × ℕ × ℕ) ∈ sierpinskiCertBase14_4 := by decide
example : ((0, 2, 3) : ℕ × ℕ × ℕ) ∉ sierpinskiCertBase14_4 := by decide

/-- The divisors of the base-`14` certificate are `{3, 5}`, the two primes
    that A146563's comment describes as splitting even/odd exponents. -/
theorem fixedDivisors_sierpinskiCertBase14_4 :
    fixedDivisors sierpinskiCertBase14_4 = {3, 5} := by decide

/-- Both divisors of the base-`14` certificate are prime. -/
theorem prime_of_mem_fixedDivisors_sierpinskiCertBase14_4 :
    ∀ p ∈ fixedDivisors sierpinskiCertBase14_4, Nat.Prime p := by
  rw [fixedDivisors_sierpinskiCertBase14_4]
  intro p hp
  fin_cases hp <;> norm_num

/-- The base-`14` certificate is a cover but not a covering system:
    `3` and `5` share the modulus `2`. -/
theorem not_isCoveringSystem_sierpinskiCertBase14_4 :
    ¬ IsCoveringSystem (residueClasses sierpinskiCertBase14_4) := by
  intro h
  have hmem1 : ((1, 2) : ℕ × ℕ) ∈ residueClasses sierpinskiCertBase14_4 := by decide
  have hmem0 : ((0, 2) : ℕ × ℕ) ∈ residueClasses sierpinskiCertBase14_4 := by decide
  have heq : ((1, 2) : ℕ × ℕ) = (0, 2) :=
    h.injOn_mod (Finset.mem_coe.mpr hmem1) (Finset.mem_coe.mpr hmem0) rfl
  exact absurd heq (by decide)

/-- **The base-`14` certificate is valid.**  All four fields of
    `IsFixedDivisorSystemBase` hold for `b = 14`, `A = 4`, `B = 1`,
    verified by kernel `decide` through `isFixedDivisorSystemBase_iff`
    at the common multiple `L = 2` of the moduli. -/
theorem isFixedDivisorSystemBase_sierpinskiCertBase14_4 :
    IsFixedDivisorSystemBase 14 4 1 sierpinskiCertBase14_4 :=
  (isFixedDivisorSystemBase_iff 14 4 1 sierpinskiCertBase14_4 2
    (by decide) (by decide)).mpr (by decide)

-- ── Drop-one negative controls for the base-14 certificate ──────────
-- Deleting either triple leaves an exponent at which the remaining
-- prime does not divide `4 · 14 ^ n + 1`.

example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 5)}, (p : ℤ) ∣ (4 : ℤ) * 14 ^ 1 + 1 := by decide
example : ¬ ∃ p ∈ fixedDivisors {(1, 2, 3)}, (p : ℤ) ∣ (4 : ℤ) * 14 ^ 2 + 1 := by decide

/-- **`4` is a Sierpiński number base `14`.**  A123159's `a(14) = 4`;
    A146563's comment names the covering set as two primes splitting
    the exponents by parity.  Conjecturally the smallest such `k`;
    minimality is not claimed. -/
theorem isSierpinskiNumberBase_fourteen_four : IsSierpinskiNumberBase 14 4 := by
  have hcert : IsFixedDivisorSystemBase 14 ((4 : ℕ) : ℤ) 1 sierpinskiCertBase14_4 := by
    have hcast : ((4 : ℕ) : ℤ) = (4 : ℤ) := by norm_num
    rw [hcast]
    exact isFixedDivisorSystemBase_sierpinskiCertBase14_4
  refine isSierpinskiNumberBase_of_isFixedDivisorSystemBase (M := 5) ?_ hcert (by decide)
    (by norm_num)
  exact isCoprime_intCast_add_one (by norm_num) (by norm_num)

/-- **The `n = 0` failure, stated rather than glossed.**
    `4 · 14 ^ 0 + 1 = 5` is prime, so A146563's "always composite for
    any integer n" is false as written and `IsSierpinskiNumberBase`
    must start at `n = 1`.  This is also the sharpest possible witness
    that `IsFixedDivisorSystemBase.composite`'s hypothesis `M < N` is
    load-bearing: here `M = N = 5`. -/
theorem not_composite_four_mul_fourteen_pow_zero_add_one :
    ¬ Composite (4 * 14 ^ 0 + 1) := fun h => h.2 (by norm_num)

-- The divisor predicted by the certificate is still there at `n = 0`;
-- it is the value itself, which is why compositeness fails.
example : (5 : ℕ) ∣ 4 * 14 ^ 0 + 1 := by decide
example : 4 * 14 ^ 0 + 1 = 5 := by decide

-- ── The whole base-14 progression, and infinitude ───────────────────

/-- The modulus of the base-`14` Sierpiński progression:
    `15 · 13 · 14 = 2730`.  The factor `15 = 3 · 5` is the product of
    the covering primes, which keeps the certificate valid; the factor
    `13 = 14 - 1` keeps the non-triviality residue fixed; the factor
    `14` keeps `k` off the multiples of the base, the base-`b` form of
    the classical oddness requirement. -/
def sierpinskiModulusBase14 : ℕ := 2730

-- Ground checks for `sierpinskiModulusBase14`.
example : sierpinskiModulusBase14 = 15 * 13 * 14 := by decide
example : sierpinskiModulusBase14 = 2 * 3 * 5 * 7 * 13 := by decide
example : ∀ p ∈ fixedDivisors sierpinskiCertBase14_4, p ∣ sierpinskiModulusBase14 := by decide
example : sierpinskiModulusBase14 % 13 = 0 := by decide
example : sierpinskiModulusBase14 % 14 = 0 := by decide
example : (4 : ℕ) % 14 = 4 := by decide  -- `14 ∤ k` along the progression

/-- The same base-`14` certificate serves the whole progression:
    shifting the coefficient by a multiple of `2730` shifts it by a
    multiple of both covering primes.  This is
    `IsFixedDivisorSystemBase.of_dvd_sub_coeff`. -/
theorem isFixedDivisorSystemBase_sierpinski_base14_add_mul (t : ℕ) :
    IsFixedDivisorSystemBase 14 ((4 + sierpinskiModulusBase14 * t : ℕ) : ℤ) 1
      sierpinskiCertBase14_4 := by
  have hcast : ((4 + sierpinskiModulusBase14 * t : ℕ) : ℤ)
      = (4 : ℤ) + 2730 * (t : ℤ) := by
    show ((4 + 2730 * t : ℕ) : ℤ) = (4 : ℤ) + 2730 * (t : ℤ)
    push_cast
    ring
  rw [hcast]
  refine isFixedDivisorSystemBase_sierpinskiCertBase14_4.of_dvd_sub_coeff ?_
  intro p hp
  have hall : ∀ q ∈ fixedDivisors sierpinskiCertBase14_4, q ∣ 2730 := by decide
  have hpd : (p : ℤ) ∣ (2730 : ℤ) := by exact_mod_cast hall p hp
  have heq : (4 : ℤ) + 2730 * (t : ℤ) - 4 = 2730 * (t : ℤ) := by ring
  rw [heq]
  exact hpd.mul_right _

/-- **Every member of the progression `4 + 2730 · t` is a Sierpiński
    number base `14`.**  Non-triviality is preserved because `13`
    divides the modulus, so the whole progression sits at
    `k ≡ 4 (mod 13)` and `k + 1 ≡ 5` is never a multiple of `13`. -/
theorem isSierpinskiNumberBase_fourteen_add_mul (t : ℕ) :
    IsSierpinskiNumberBase 14 (4 + sierpinskiModulusBase14 * t) := by
  refine isSierpinskiNumberBase_of_isFixedDivisorSystemBase (M := 5) ?_
    (isFixedDivisorSystemBase_sierpinski_base14_add_mul t) (by decide) ?_
  · refine isCoprime_intCast_add_one (by norm_num) ?_
    show Nat.Coprime (4 + sierpinskiModulusBase14 * t + 1) (14 - 1)
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr ?_)
    show ¬ (13 : ℕ) ∣ 4 + 2730 * t + 1
    omega
  · show 5 < (4 + 2730 * t) * 14 + 1
    omega

/-- **Infinitely many Sierpiński numbers base `14` exist.**  Beyond
    every bound `B` there is one, namely `4 + 2730 · (B + 1)`. -/
theorem exists_lt_isSierpinskiNumberBase_fourteen (B : ℕ) :
    ∃ k, B < k ∧ IsSierpinskiNumberBase 14 k := by
  refine ⟨4 + sierpinskiModulusBase14 * (B + 1), ?_,
    isSierpinskiNumberBase_fourteen_add_mul (B + 1)⟩
  show B < 4 + 2730 * (B + 1)
  omega

/-- The set of Sierpiński numbers base `14` is infinite. -/
theorem infinite_setOf_isSierpinskiNumberBase_fourteen :
    {k : ℕ | IsSierpinskiNumberBase 14 k}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨k, hk, hkS⟩ := exists_lt_isSierpinskiNumberBase_fourteen B
  have hle : k ≤ B := hB hkS
  omega

-- ── Non-vacuity of the base-b headline theorems ─────────────────────

-- The first few members of the base-`14` family at `k = 4` are
-- genuinely composite, certified independently of the covering
-- argument.
example : Composite (4 * 14 ^ 1 + 1) := ⟨by norm_num, by norm_num⟩  -- 57 = 3·19
example : Composite (4 * 14 ^ 2 + 1) := ⟨by norm_num, by norm_num⟩  -- 785 = 5·157
example : Composite (4 * 14 ^ 3 + 1) := ⟨by norm_num, by norm_num⟩  -- 10977 = 3·3659

-- … and they are the values the theorem speaks about.
example : 4 * 14 ^ 3 + 1 = 10977 := by decide
example : Composite 10977 := isSierpinskiNumberBase_fourteen_four.2 3 (by norm_num)

-- The predicted divisor, class by class.
example : (3 : ℕ) ∣ 4 * 14 ^ 1 + 1 := by decide  -- n ≡ 1 (mod 2)
example : (5 : ℕ) ∣ 4 * 14 ^ 2 + 1 := by decide  -- n ≡ 0 (mod 2)

-- ════════════════════════════════════════════════════════════════════
-- §7 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms IsSierpinskiNumber
#print axioms sierpinskiCert78557
#print axioms fixedDivisors_sierpinskiCert78557
#print axioms prime_of_mem_fixedDivisors_sierpinskiCert78557
#print axioms isCoveringSystem_sierpinskiCert78557
#print axioms isFixedDivisorSystem_sierpinskiCert78557
#print axioms isSierpinskiNumber_of_isFixedDivisorSystem
#print axioms isSierpinskiNumber_78557
#print axioms sierpinskiModulus
#print axioms isFixedDivisorSystem_sierpinski_add_mul
#print axioms isSierpinskiNumber_add_mul
#print axioms exists_lt_isSierpinskiNumber
#print axioms infinite_setOf_isSierpinskiNumber
#print axioms IsSierpinskiNumberBase
#print axioms isCoprime_intCast_add_one
#print axioms isSierpinskiNumberBase_of_isFixedDivisorSystemBase
#print axioms isSierpinskiNumber_iff_base_two
#print axioms isSierpinskiNumberBase_two_78557
#print axioms sierpinskiCertBase14_4
#print axioms fixedDivisors_sierpinskiCertBase14_4
#print axioms prime_of_mem_fixedDivisors_sierpinskiCertBase14_4
#print axioms not_isCoveringSystem_sierpinskiCertBase14_4
#print axioms isFixedDivisorSystemBase_sierpinskiCertBase14_4
#print axioms isSierpinskiNumberBase_fourteen_four
#print axioms not_composite_four_mul_fourteen_pow_zero_add_one
#print axioms sierpinskiModulusBase14
#print axioms isFixedDivisorSystemBase_sierpinski_base14_add_mul
#print axioms isSierpinskiNumberBase_fourteen_add_mul
#print axioms exists_lt_isSierpinskiNumberBase_fourteen
#print axioms infinite_setOf_isSierpinskiNumberBase_fourteen

end Erdos.Covering
