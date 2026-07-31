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
-- §6 AXIOM AUDIT
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

end Erdos.Covering
