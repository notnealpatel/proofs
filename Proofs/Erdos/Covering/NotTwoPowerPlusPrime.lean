/-
  Erdős's 1950 theorem: infinitely many odd integers are not of the
  form `2^k + p` with `p` prime.

  Erdős, "On integers of the form 2^k + p and some related problems",
  Summa Brasiliensis Mathematicae 2 (1950), 113–123.  The theorem
  exhibits an infinite arithmetic progression of odd integers `m` such
  that `m - 2^k` is composite for every `k ≥ 1` with `2^k < m`.  This is
  the covering-system payoff of `Erdos.Covering.Basic`.

  ── The construction ────────────────────────────────────────────────
  Take the covering system
    `C = {0 (mod 2), 0 (mod 3), 1 (mod 4), 3 (mod 8), 7 (mod 12),
          23 (mod 24)}`
  and pair each modulus `d` with a prime `p` whose multiplicative order
  for the base `2` is exactly `d`:

    | d | 2 | 3 | 4 | 8 | 12 |  24 |
    | p | 3 | 7 | 5 | 17| 13 | 241 |

  Set `P = 2 · 3 · 5 · 7 · 13 · 17 · 241 = 11184810` and
  `M = 7629217`.  The residue `M` is chosen by CRT so that
  `M ≡ 2^a (mod p)` for each class `(a, d)` of `C` with partner prime
  `p`, and `M ≡ 1 (mod 2)`.  Then for every `m ≡ M (mod P)` and every
  `k`, picking the class `(a, d) ∈ C` with `k ≡ a (mod d)` gives

    `m ≡ M ≡ 2^a ≡ 2^(a + d·⌊k/d⌋) = 2^k  (mod p)`,

  so `p ∣ m - 2^k`.  Since `p ≤ 241`, any `m - 2^k` exceeding `241` is a
  proper multiple of `p`, hence composite.  `P` is even and `M` is odd,
  so every member of the progression is odd.

  ── TRAP: `Erdos.Covering.erdosSystem` is NOT usable here ────────────
  The classical five-class system `erdosSystem` of `Basic.lean` has
  moduli `{2, 3, 4, 6, 12}`, and modulus `6` cannot be paired: a prime
  `p` with `orderOf (2 : ZMod p) = 6` would be a primitive prime divisor
  of `2^6 - 1 = 63 = 3^2 · 7`, but the only primes dividing `63` are
  `3` and `7`, with `orderOf (2 : ZMod 3) = 2` and
  `orderOf (2 : ZMod 7) = 3`.  This is exactly the Zsigmondy exception
  at base `2`, exponent `6`, and `d = 6` together with the degenerate
  `d = 1` are the *only* exponents with no prime of order `d` for the
  base `2` (verified in Sage for `d < 65`; Zsigmondy in general).
  A bounded factoring will falsely report `d = 31` as an exception —
  `2^31 - 1 = 2147483647` is itself prime, with order `31`.  Any
  attempt to run the argument below on `erdosSystem` silently has no
  prime to attach to the class `5 (mod 6)`.  Hence the separate
  six-class system `erdosSystem1950` defined here, whose moduli
  `{2, 3, 4, 8, 12, 24}` all admit partner primes.

  ── ℤ vs ℕ subtraction ──────────────────────────────────────────────
  The divisibility core is stated in ℤ — `(p : ℤ) ∣ (m : ℤ) - 2 ^ k` —
  per STYLE.md's cast-before-subtracting rule, so it holds
  unconditionally in `k` with no `2 ^ k < m` guard and no truncation
  junk.  The compositeness statements necessarily mention the natural
  number `m - 2 ^ k` (`Nat.Prime` lives on ℕ) and each carries the
  guard `2 ^ k + 241 < m`, which implies `2 ^ k < m`.

  ── Contents ────────────────────────────────────────────────────────
  * `erdosSystem1950`, `isCoveringSystem_erdosSystem1950` — the
    six-class covering system, verified by `decide` at `L = 24`, with
    drop-one negative controls showing every class is needed.
  * `orderOf_two_zmod_*` — the six order facts
    `orderOf (2 : ZMod p) = d`, and the bridge
    `two_pow_modEq_one_of_pow_eq_one`.  These document *why* the
    pairing works and are NOT in the dependency cone of any theorem
    below: deleting §2 outright leaves `erdos_1950` provable.  What the
    argument actually consumes is `2 ^ d ≡ 1 [MOD p]`, discharged by
    `decide` directly at each call site.  Order *minimality* is never
    needed — only that `d` is *a* multiple of the order.
  * `dvd_sub_two_pow_of_modEq` — the reusable one-class divisibility
    step, stated for arbitrary `P`, `M`, `p`, `d`, `a`.
  * `exists_mem_erdosPrimes1950_dvd` — the fixed-divisor theorem: every
    `m ≡ M (mod P)` and every `k` admit `p ∈ {3,5,7,13,17,241}` with
    `(p : ℤ) ∣ (m : ℤ) - 2 ^ k`.
  * `not_prime_sub_two_pow` — compositeness of `m - 2 ^ k`.
  * `not_prime_sub_two` — the A039669 / Erdős #1142 corollary: no
    member of the progression above `243` has `m - 2` prime, hence
    none is a term of A039669.
  * `exists_gt_odd_not_prime_sub_two_pow_of_lt` — infinitude with the
    side condition `2 ^ k + 241 < m`.
  * `erdos_1950` — the full theorem, side condition removed.
  * `erdos_1950_not_two_pow_add_prime` — the same statement in the
    literal `2 ^ k + p` phrasing of the paper title.

  ── Novelty and prior art ───────────────────────────────────────────
  Claim: first machine-checked proof of Erdős's 1950 theorem that
  infinitely many odd integers are not of the form `2^k + p`.

  Prior art in proof assistants, none of which proves this theorem:
  * google-deepmind/formal-conjectures,
    `FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean` — a
    sorry-free `CoveringSystem`/`StrictCoveringSystem` definition over
    commutative semirings.  Definitions only; `Erdos.Covering.Basic` is
    therefore not the first covering-system definition in an assistant.
  * google-deepmind/formal-conjectures, `.../ErdosProblems/1142.lean` —
    the A039669 property (`Erdos1142Prop`) as a `sorry`'d statement.
    The corollary `not_prime_sub_two` below — an explicit infinite
    arithmetic progression of A039669 non-terms — has no counterpart
    there.
  * plby/lean-proofs,
    `src/v4.24.0/ErdosProblems/Erdos275.lean` (also `Erdos280.lean`,
    `Erdos281.lean`) — sorry-free Lean 4 proofs of covering-congruence
    results (Crittenden–Vanden Eynden style) via a bespoke local
    `IsCoveringSystem` over `List ArithmeticProgression`.  Genuine
    covering-system reasoning has therefore been formalized before; we
    claim no priority on that.
  Characterization of the contribution, not a priority claim: this is
  the first pairing of a reusable covering-system layer with a
  classical number-theoretic consequence of covering systems.

  Search-bound provenance for A039669: "No other terms below 2^120.
  - Max Alekseyev, Dec 08 2011" (OEIS A039669 comment, pinned
  2026-07-30) is the citable bound.  Erdős problem #1142 (open, OEIS
  A039669) asks whether A039669 is infinite or has any term beyond
  `105`; this file does not resolve it — it proves the complementary
  side, that an explicit infinite progression consists of non-terms.

  Axiom audit: see the `#print axioms` block at the end of the file.
  Every declaration is sorry-free.  No `native_decide`, no custom
  axioms.
-/

import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 THE SIX-CLASS COVERING SYSTEM
-- ════════════════════════════════════════════════════════════════════

/-- The covering system used by Erdős (1950) to build integers not of
    the form `2^k + p`:
    `{0 (mod 2), 0 (mod 3), 1 (mod 4), 3 (mod 8), 7 (mod 12),
      23 (mod 24)}`.
    Each of its moduli `{2, 3, 4, 8, 12, 24}` admits a prime `p` with
    `orderOf (2 : ZMod p)` equal to that modulus (proved in §2), which
    is what the construction needs.  This is not a scarce property —
    by Zsigmondy's theorem the *only* `d ≥ 2` admitting no such prime
    is `d = 6` — but `6` is exactly the modulus appearing in the
    five-class `erdosSystem` of `Basic.lean`, which is therefore
    unusable here; see the module header. -/
def erdosSystem1950 : Finset (ℕ × ℕ) :=
  {(0, 2), (0, 3), (1, 4), (3, 8), (7, 12), (23, 24)}

-- Ground checks: six classes, the expected moduli, no collapse.
example : erdosSystem1950.card = 6 := by decide
example : erdosSystem1950.image Prod.snd = {2, 3, 4, 8, 12, 24} := by decide
example : ((23, 24) : ℕ × ℕ) ∈ erdosSystem1950 := by decide
example : ((5, 6) : ℕ × ℕ) ∉ erdosSystem1950 := by decide

/-- **Satisfiability witness for `IsCoveringSystem` at the 1950
    system.** The six classes have distinct moduli, all exceeding `1`,
    and cover every integer.  Verified by kernel `decide` through
    `isCoveringSystem_iff` at the common multiple `L = 24`. -/
theorem isCoveringSystem_erdosSystem1950 : IsCoveringSystem erdosSystem1950 :=
  (isCoveringSystem_iff 24 (by decide) (by decide)).mpr (by decide)

-- ── Drop-one negative controls: the system is irredundant ───────────
-- Deleting any single class leaves a residue mod 24 uncovered, so no
-- proper subsystem covers ℤ.  (Uncovered witnesses: 2, 15, 1, 11, 7,
-- 23 respectively.)

example : ¬ Covers ({(0, 3), (1, 4), (3, 8), (7, 12), (23, 24)} : Finset (ℕ × ℕ)) :=
  fun h => absurd ((covers_iff_forall_range 24 (by decide) (by decide)).mp h) (by decide)

example : ¬ Covers ({(0, 2), (1, 4), (3, 8), (7, 12), (23, 24)} : Finset (ℕ × ℕ)) :=
  fun h => absurd ((covers_iff_forall_range 24 (by decide) (by decide)).mp h) (by decide)

example : ¬ Covers ({(0, 2), (0, 3), (3, 8), (7, 12), (23, 24)} : Finset (ℕ × ℕ)) :=
  fun h => absurd ((covers_iff_forall_range 24 (by decide) (by decide)).mp h) (by decide)

example : ¬ Covers ({(0, 2), (0, 3), (1, 4), (7, 12), (23, 24)} : Finset (ℕ × ℕ)) :=
  fun h => absurd ((covers_iff_forall_range 24 (by decide) (by decide)).mp h) (by decide)

example : ¬ Covers ({(0, 2), (0, 3), (1, 4), (3, 8), (23, 24)} : Finset (ℕ × ℕ)) :=
  fun h => absurd ((covers_iff_forall_range 24 (by decide) (by decide)).mp h) (by decide)

example : ¬ Covers ({(0, 2), (0, 3), (1, 4), (3, 8), (7, 12)} : Finset (ℕ × ℕ)) :=
  fun h => absurd ((covers_iff_forall_range 24 (by decide) (by decide)).mp h) (by decide)

-- ════════════════════════════════════════════════════════════════════
-- §2 THE PARTNER PRIMES AND THEIR ORDERS FOR THE BASE 2
-- ════════════════════════════════════════════════════════════════════

/-- The six primes attached to the moduli of `erdosSystem1950`:
    `orderOf (2 : ZMod p)` equals `2, 3, 4, 8, 12, 24` for
    `p = 3, 7, 5, 17, 13, 241` respectively. -/
def erdosPrimes1950 : Finset ℕ := {3, 5, 7, 13, 17, 241}

-- Ground checks for `erdosPrimes1950`.
example : erdosPrimes1950.card = 6 := by decide
example : ∀ p ∈ erdosPrimes1950, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num
example : erdosPrimes1950.max' (by decide) = 241 := by decide

/-! The six order facts.  Each uses the standard order certificate
`orderOf_eq_of_pow_and_pow_div_prime`: `x ^ n = 1` together with
`x ^ (n / q) ≠ 1` for every prime `q ∣ n`.  For the concrete
`n ∈ {2, 3, 4, 8, 12, 24}` the prime divisors `q` are enumerated by
`interval_cases` under `q ≤ n`, and each residual claim is a kernel
`decide` in a finite `ZMod`.

NOT IN THE DEPENDENCY CONE: no proof below invokes any of these, nor
the bridge lemma that follows them.  They certify that each modulus of
`erdosSystem1950` is matched by a prime — the fact that forces the
choice of covering system — but the divisibility argument consumes
only `2 ^ d ≡ 1 [MOD p]`, proved directly by `decide` at each of the
six call sites in `exists_mem_erdosPrimes1950_dvd`. -/

/-- `2` has multiplicative order `2` mod `3`; partner of the class
    `0 (mod 2)`. -/
theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) (by
    intro q hq hqd
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hqd
    interval_cases q <;> revert hq hqd <;> decide)

/-- `2` has multiplicative order `3` mod `7`; partner of the class
    `0 (mod 3)`. -/
theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) (by
    intro q hq hqd
    have hle : q ≤ 3 := Nat.le_of_dvd (by norm_num) hqd
    interval_cases q <;> revert hq hqd <;> decide)

/-- `2` has multiplicative order `4` mod `5`; partner of the class
    `1 (mod 4)`. -/
theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) (by
    intro q hq hqd
    have hle : q ≤ 4 := Nat.le_of_dvd (by norm_num) hqd
    interval_cases q <;> revert hq hqd <;> decide)

/-- `2` has multiplicative order `8` mod `17`; partner of the class
    `3 (mod 8)`. -/
theorem orderOf_two_zmod_seventeen : orderOf (2 : ZMod 17) = 8 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) (by
    intro q hq hqd
    have hle : q ≤ 8 := Nat.le_of_dvd (by norm_num) hqd
    interval_cases q <;> revert hq hqd <;> decide)

/-- `2` has multiplicative order `12` mod `13`; partner of the class
    `7 (mod 12)`. -/
theorem orderOf_two_zmod_thirteen : orderOf (2 : ZMod 13) = 12 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) (by
    intro q hq hqd
    have hle : q ≤ 12 := Nat.le_of_dvd (by norm_num) hqd
    interval_cases q <;> revert hq hqd <;> decide)

/-- `2` has multiplicative order `24` mod `241`; partner of the class
    `23 (mod 24)`.  `241` is the primitive prime divisor of
    `2 ^ 24 - 1 = 16777215 = 3^2 · 5 · 7 · 13 · 17 · 241`. -/
theorem orderOf_two_zmod_241 : orderOf (2 : ZMod 241) = 24 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) (by
    intro q hq hqd
    have hle : q ≤ 24 := Nat.le_of_dvd (by norm_num) hqd
    interval_cases q <;> revert hq hqd <;> decide)

/-- Bridge from the `ZMod` order data to the ℕ-level congruence that
    the divisibility argument actually consumes.  Note that only
    `(2 : ZMod p) ^ d = 1` is needed — minimality of `d` (i.e. that `d`
    is the *order* and not merely a multiple of it) is never used.  The
    order facts above are documentation: they certify that each modulus
    of `erdosSystem1950` really is matched by a prime, which is where
    the choice of covering system is forced. -/
theorem two_pow_modEq_one_of_pow_eq_one {p d : ℕ} (h : (2 : ZMod p) ^ d = 1) :
    2 ^ d ≡ 1 [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact h

-- The six congruences `2 ^ d ≡ 1 [MOD p]`, each obtained from the
-- corresponding order fact by `pow_orderOf_eq_one`.
example : 2 ^ 2 ≡ 1 [MOD 3] :=
  two_pow_modEq_one_of_pow_eq_one (orderOf_two_zmod_three ▸ pow_orderOf_eq_one (2 : ZMod 3))
example : 2 ^ 3 ≡ 1 [MOD 7] :=
  two_pow_modEq_one_of_pow_eq_one (orderOf_two_zmod_seven ▸ pow_orderOf_eq_one (2 : ZMod 7))
example : 2 ^ 4 ≡ 1 [MOD 5] :=
  two_pow_modEq_one_of_pow_eq_one (orderOf_two_zmod_five ▸ pow_orderOf_eq_one (2 : ZMod 5))
example : 2 ^ 8 ≡ 1 [MOD 17] :=
  two_pow_modEq_one_of_pow_eq_one (orderOf_two_zmod_seventeen ▸ pow_orderOf_eq_one (2 : ZMod 17))
example : 2 ^ 12 ≡ 1 [MOD 13] :=
  two_pow_modEq_one_of_pow_eq_one (orderOf_two_zmod_thirteen ▸ pow_orderOf_eq_one (2 : ZMod 13))
example : 2 ^ 24 ≡ 1 [MOD 241] :=
  two_pow_modEq_one_of_pow_eq_one (orderOf_two_zmod_241 ▸ pow_orderOf_eq_one (2 : ZMod 241))

-- ════════════════════════════════════════════════════════════════════
-- §3 THE PROGRESSION
-- ════════════════════════════════════════════════════════════════════

/-- The modulus of the Erdős progression:
    `P = 2 · 3 · 5 · 7 · 13 · 17 · 241 = 11184810`, the product of `2`
    with the six partner primes. -/
def erdosModulus1950 : ℕ := 11184810

/-- The residue of the Erdős progression, `M = 7629217`, pinned by CRT:
    `M ≡ 1 (mod 2)`, `M ≡ 2^0 (mod 3)`, `M ≡ 2^0 (mod 7)`,
    `M ≡ 2^1 (mod 5)`, `M ≡ 2^3 (mod 17)`, `M ≡ 2^7 (mod 13)`,
    `M ≡ 2^23 (mod 241)`. -/
def erdosResidue1950 : ℕ := 7629217

-- Ground checks: the factorization of `P`, the CRT residues of `M`,
-- and `M < P` (so `M` really is the least member of the progression).
example : erdosModulus1950 = 2 * 3 * 5 * 7 * 13 * 17 * 241 := by decide
example : ∀ p ∈ erdosPrimes1950, p ∣ erdosModulus1950 := by decide
example : erdosResidue1950 < erdosModulus1950 := by decide
example : erdosResidue1950 % 2 = 1 := by decide
example : erdosModulus1950 % 2 = 0 := by decide
example : erdosResidue1950 % 3 = 2 ^ 0 % 3 := by decide
example : erdosResidue1950 % 7 = 2 ^ 0 % 7 := by decide
example : erdosResidue1950 % 5 = 2 ^ 1 % 5 := by decide
example : erdosResidue1950 % 17 = 2 ^ 3 % 17 := by decide
example : erdosResidue1950 % 13 = 2 ^ 7 % 13 := by decide
example : erdosResidue1950 % 241 = 2 ^ 23 % 241 := by decide

-- ════════════════════════════════════════════════════════════════════
-- §4 THE FIXED-DIVISOR THEOREM
-- ════════════════════════════════════════════════════════════════════

/-- **One covering class, one prime.** If `m ≡ M (mod P)`, if `p ∣ P`,
    if `2 ^ d ≡ 1 (mod p)` and `M ≡ 2 ^ a (mod p)`, then every exponent
    `k` in the residue class `a (mod d)` satisfies `p ∣ m - 2 ^ k` (in
    ℤ, so no subtraction guard is needed).

    This is the reusable step: the six instances below differ only in
    the numerals substituted for `p`, `d`, `a`. -/
theorem dvd_sub_two_pow_of_modEq {P M p d a m k : ℕ} (hm : m % P = M)
    (hpP : p ∣ P) (hpow : 2 ^ d ≡ 1 [MOD p]) (hres : M ≡ 2 ^ a [MOD p])
    (hk : k % d = a) :
    (p : ℤ) ∣ (m : ℤ) - 2 ^ k := by
  -- Transport the two ℕ congruences to ℤ.
  have hpowZ : (2 : ℤ) ^ d ≡ 1 [ZMOD (p : ℤ)] := by
    have hcast := Int.natCast_modEq_iff.mpr hpow
    push_cast at hcast
    exact hcast
  have hresZ : (M : ℤ) ≡ 2 ^ a [ZMOD (p : ℤ)] := by
    have hcast := Int.natCast_modEq_iff.mpr hres
    push_cast at hcast
    exact hcast
  -- `m ≡ M (mod P)` in ℤ, from `m = P * (m / P) + M`.
  have hPm : (P : ℤ) ∣ (m : ℤ) - (M : ℤ) := by
    refine ⟨((m / P : ℕ) : ℤ), ?_⟩
    have hdm : P * (m / P) + m % P = m := Nat.div_add_mod m P
    rw [hm] at hdm
    have hcast : ((P * (m / P) + M : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast hdm
    rw [Nat.cast_add, Nat.cast_mul] at hcast
    linarith
  have hmM : (m : ℤ) ≡ (M : ℤ) [ZMOD (p : ℤ)] :=
    (Int.modEq_iff_dvd.mpr (dvd_trans (Int.natCast_dvd_natCast.mpr hpP) hPm)).symm
  -- `2 ^ k = (2 ^ d) ^ (k / d) * 2 ^ a ≡ 2 ^ a (mod p)`.
  have hpowk : (2 : ℤ) ^ k ≡ 2 ^ a [ZMOD (p : ℤ)] := by
    conv_lhs => rw [← Nat.div_add_mod k d, hk]
    rw [pow_add, pow_mul]
    calc ((2 : ℤ) ^ d) ^ (k / d) * 2 ^ a
        ≡ 1 ^ (k / d) * 2 ^ a [ZMOD (p : ℤ)] :=
          Int.ModEq.mul (hpowZ.pow _) (Int.ModEq.refl _)
      _ = 2 ^ a := by rw [one_pow, one_mul]
  have hzero : (m : ℤ) - 2 ^ k ≡ 0 [ZMOD (p : ℤ)] := by
    have hsub := (hmM.trans hresZ).sub hpowk
    simpa using hsub
  exact Int.modEq_zero_iff_dvd.mp hzero

-- **Satisfiability of `dvd_sub_two_pow_of_modEq`.** All five
-- hypotheses hold jointly at `P = 11184810`, `M = 7629217`, `p = 5`,
-- `d = 4`, `a = 1`, `m = 7629217`, `k = 9`: `m % P = M`, `5 ∣ P`,
-- `2 ^ 4 ≡ 1 [MOD 5]`, `M ≡ 2 ^ 1 [MOD 5]`, `9 % 4 = 1`.  The
-- conclusion is not trivially true there:
-- `7629217 - 2 ^ 9 = 7628705 = 5 · 7 · 211 · 1033`, a nonzero multiple
-- of `5` — so neither `p = 1` nor a vanishing difference is doing the
-- work.
example : ((5 : ℕ) : ℤ) ∣ ((7629217 : ℕ) : ℤ) - 2 ^ 9 :=
  dvd_sub_two_pow_of_modEq (P := 11184810) (M := 7629217) (p := 5) (d := 4)
    (a := 1) (m := 7629217) (k := 9) (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- The same instantiation, checked independently in ℕ.
example : (7629217 : ℕ) - 2 ^ 9 = 5 * 1525741 := by decide

/-- The covering property of `erdosSystem1950`, transported to natural
    exponents: every `k : ℕ` lies in one of the six residue classes. -/
theorem erdosSystem1950_covers_nat (k : ℕ) :
    k % 2 = 0 ∨ k % 3 = 0 ∨ k % 4 = 1 ∨ k % 8 = 3 ∨ k % 12 = 7 ∨ k % 24 = 23 := by
  obtain ⟨q, hqS, hcong⟩ := isCoveringSystem_erdosSystem1950.covers (k : ℤ)
  have h : k % q.2 = q.1 % q.2 := Int.natCast_modEq_iff.mp hcong
  -- `simp only []` reduces the `Prod.fst`/`Prod.snd` projections that
  -- `fin_cases` leaves on the six substituted pairs; `omega` then places
  -- each concrete congruence in the matching disjunct.
  fin_cases hqS <;> simp only [] at h <;> omega

/-- **Fixed-divisor theorem (Erdős 1950).** For every `m` in the
    arithmetic progression `m ≡ M (mod P)` and every exponent `k`, one
    of the six primes `3, 5, 7, 13, 17, 241` divides `m - 2 ^ k`.

    Stated in ℤ per STYLE.md (cast before subtracting), which also
    removes the need for the hypothesis `1 ≤ k`: the conclusion holds
    for `k = 0` as well (`3 ∣ m - 1`). -/
theorem exists_mem_erdosPrimes1950_dvd (m k : ℕ)
    (hm : m % erdosModulus1950 = erdosResidue1950) :
    ∃ p ∈ erdosPrimes1950, (p : ℤ) ∣ (m : ℤ) - 2 ^ k := by
  rcases erdosSystem1950_covers_nat k with hk | hk | hk | hk | hk | hk
  · exact ⟨3, by decide, dvd_sub_two_pow_of_modEq hm (by decide) (by decide) (by decide) hk⟩
  · exact ⟨7, by decide, dvd_sub_two_pow_of_modEq hm (by decide) (by decide) (by decide) hk⟩
  · exact ⟨5, by decide, dvd_sub_two_pow_of_modEq hm (by decide) (by decide) (by decide) hk⟩
  · exact ⟨17, by decide, dvd_sub_two_pow_of_modEq hm (by decide) (by decide) (by decide) hk⟩
  · exact ⟨13, by decide, dvd_sub_two_pow_of_modEq hm (by decide) (by decide) (by decide) hk⟩
  · exact ⟨241, by decide, dvd_sub_two_pow_of_modEq hm (by decide) (by decide) (by decide) hk⟩

-- ════════════════════════════════════════════════════════════════════
-- §5 COMPOSITENESS
-- ════════════════════════════════════════════════════════════════════

/-- **Compositeness.** For `m` in the progression and `1 ≤ k` with
    `2 ^ k + 241 < m`, the number `m - 2 ^ k` is not prime: it is a
    proper multiple of one of the six primes, all of which are at most
    `241 < m - 2 ^ k`.

    `1 ≤ k` records the classical range of exponents (Erdős's question
    is about `2 ^ k + p` with `k ≥ 1`); the argument does not need it,
    since `exists_mem_erdosPrimes1950_dvd` also covers `k = 0`. -/
theorem not_prime_sub_two_pow (m k : ℕ)
    (hm : m % erdosModulus1950 = erdosResidue1950) (hk : 1 ≤ k)
    (hlt : 2 ^ k + 241 < m) : ¬ Nat.Prime (m - 2 ^ k) := by
  obtain ⟨p, hp, hdvd⟩ := exists_mem_erdosPrimes1950_dvd m k hm
  have hple : p ≤ 241 := by fin_cases hp <;> decide
  have hp1 : 1 < p := by fin_cases hp <;> decide
  -- All `hk` contributes is `2 ≤ 2 ^ k`; see the docstring.
  have hk2 : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2k : 2 ^ k ≤ m := by omega
  have hcast : ((m - 2 ^ k : ℕ) : ℤ) = (m : ℤ) - 2 ^ k := by
    rw [Nat.cast_sub h2k]
    push_cast
    ring
  have hdvdN : p ∣ m - 2 ^ k := by
    have hZ : (p : ℤ) ∣ ((m - 2 ^ k : ℕ) : ℤ) := by rw [hcast]; exact hdvd
    exact_mod_cast hZ
  intro hprime
  -- `p` divides `m - 2 ^ k`, is not `1`, and is at most `241 < m - 2 ^ k`.
  rcases hprime.eq_one_or_self_of_dvd p hdvdN with hone | hself
  · omega
  · omega

-- ════════════════════════════════════════════════════════════════════
-- §6 THE A039669 COROLLARY
-- ════════════════════════════════════════════════════════════════════

/-- **An infinite arithmetic progression of A039669 non-terms.**
    A039669 (pinned 2026-07-30) is "Positive numbers `m` such that
    `m - 2^k` is a prime for all `k > 0` with `2^k < m`"; known terms
    `4, 7, 15, 21, 45, 75, 105`.  Erdős problem #1142 asks whether
    there are infinitely many such `m`, or any beyond `105`; the
    problem is open, and Alekseyev reports no further term below
    `2^120` (OEIS comment, 2011-12-08).

    Taking `k = 1` in `not_prime_sub_two_pow`: no
    `m ≡ 7629217 (mod 11184810)` with `244 ≤ m` has `m - 2` prime, so
    no such `m` is a term of A039669.  Every member of this progression
    already lies inside Alekseyev's searched range up to `2^120`, so
    the content here is structural rather than numerical: it is an
    *infinite* explicit family of non-terms, proved rather than
    searched.

    `244 ≤ m` is redundant: `hm` alone forces `7629217 ≤ m`, since
    `m < P` gives `m = M` and otherwise `m ≥ P`.  It is kept because it
    is the honest side condition for the `k = 1` instance of
    `not_prime_sub_two_pow` and makes the guard visible at the use
    site.  The same holds for `Odd m` in §7, which also follows from
    `hm`. -/
theorem not_prime_sub_two (m : ℕ)
    (hm : m % erdosModulus1950 = erdosResidue1950) (hB : 244 ≤ m) :
    ¬ Nat.Prime (m - 2) := by
  have h := not_prime_sub_two_pow m 1 hm le_rfl (by simp only [pow_one]; omega)
  rwa [pow_one] at h

-- ════════════════════════════════════════════════════════════════════
-- §7 INFINITUDE
-- ════════════════════════════════════════════════════════════════════

/-- **Infinitude, with the side condition.** Beyond every bound `B`
    there is an odd `m` in the progression for which `m - 2 ^ k` is
    composite for all `1 ≤ k` with `2 ^ k + 241 < m`. -/
theorem exists_gt_odd_not_prime_sub_two_pow_of_lt (B : ℕ) :
    ∃ m, B < m ∧ m % erdosModulus1950 = erdosResidue1950 ∧ Odd m ∧
      ∀ k, 1 ≤ k → 2 ^ k + 241 < m → ¬ Nat.Prime (m - 2 ^ k) := by
  have hmod : (erdosResidue1950 + erdosModulus1950 * (B + 1)) % erdosModulus1950
      = erdosResidue1950 := by
    rw [Nat.add_mul_mod_self_left]
    decide
  refine ⟨erdosResidue1950 + erdosModulus1950 * (B + 1), ?_, hmod, ?_, ?_⟩
  · show B < 7629217 + 11184810 * (B + 1)
    omega
  · rw [Nat.odd_iff]
    show (7629217 + 11184810 * (B + 1)) % 2 = 1
    omega
  · intro k hk hlt
    exact not_prime_sub_two_pow _ k hmod hk hlt

-- ════════════════════════════════════════════════════════════════════
-- §8 ERDŐS 1950, IN FULL
-- ════════════════════════════════════════════════════════════════════

/-- **Erdős 1950.** Beyond every bound `B` there is an odd `m` such
    that `m - 2 ^ k` is composite for *every* `k ≥ 1` with `2 ^ k < m`;
    equivalently, infinitely many odd integers are not of the form
    `2 ^ k + p` with `p` prime.

    The side condition of the previous theorem is removed by placing
    `m` in the upper part of a dyadic block: choosing
    `m ≡ M (mod P)` with `2 ^ K + 241 < m < 2 ^ (K+1)` forces every
    `k` with `2 ^ k < m` to satisfy `k ≤ K`, hence
    `2 ^ k + 241 ≤ 2 ^ K + 241 < m`. -/
theorem erdos_1950 (B : ℕ) :
    ∃ m, B < m ∧ Odd m ∧ ∀ k, 1 ≤ k → 2 ^ k < m → ¬ Nat.Prime (m - 2 ^ k) := by
  -- Block exponent `K = B + 25`, so `2 ^ K ≥ 2 ^ 25 = 33554432` exceeds
  -- both `B` and `M + 241 + P = 18814268`.
  set K : ℕ := B + 25 with hKdef
  obtain ⟨t, ht, htbig, htB⟩ : ∃ t, 2 ^ K = t ∧ 33554432 ≤ t ∧ B < t := by
    refine ⟨2 ^ K, rfl, ?_, ?_⟩
    · calc (33554432 : ℕ) = 2 ^ 25 := by norm_num
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hnext : 2 ^ (K + 1) = 2 * t := by rw [pow_succ, ht]; ring
  -- The least progression member strictly above `2 ^ K + 241`.
  set m : ℕ :=
    erdosResidue1950 + erdosModulus1950 * ((t + 241) / erdosModulus1950 + 1) with hmdef
  have hmod : m % erdosModulus1950 = erdosResidue1950 := by
    rw [hmdef, Nat.add_mul_mod_self_left]
    decide
  have hlow : t + 241 < m := by
    rw [hmdef]
    show t + 241 < 7629217 + 11184810 * ((t + 241) / 11184810 + 1)
    omega
  have hhigh : m < 2 * t := by
    rw [hmdef]
    show 7629217 + 11184810 * ((t + 241) / 11184810 + 1) < 2 * t
    omega
  refine ⟨m, by omega, ?_, ?_⟩
  · rw [Nat.odd_iff, hmdef]
    show (7629217 + 11184810 * ((t + 241) / 11184810 + 1)) % 2 = 1
    omega
  · intro k hk hklt
    -- `2 ^ k < m < 2 ^ (K + 1)` forces `k ≤ K`, hence `2 ^ k ≤ 2 ^ K = t`.
    have hkK : k ≤ K := by
      by_contra hcon
      have hge : 2 ^ (K + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2k : 2 ^ k ≤ t := ht ▸ Nat.pow_le_pow_right (by norm_num) hkK
    exact not_prime_sub_two_pow m k hmod hk (by omega)

/-- **Erdős 1950, in the `2 ^ k + p` phrasing.** Beyond every bound `B`
    there is an odd integer `m` that is *not* of the form `2 ^ k + p`
    with `k ≥ 1` and `p` prime.  Hence infinitely many odd integers
    admit no such representation.

    This is `erdos_1950` restated: `m = 2 ^ k + p` with `p` prime forces
    `2 ^ k < m` and `p = m - 2 ^ k`, which `erdos_1950` rules out. -/
theorem erdos_1950_not_two_pow_add_prime (B : ℕ) :
    ∃ m, B < m ∧ Odd m ∧ ¬ ∃ k p : ℕ, 1 ≤ k ∧ Nat.Prime p ∧ m = 2 ^ k + p := by
  obtain ⟨m, hB, hodd, hmain⟩ := erdos_1950 B
  refine ⟨m, hB, hodd, ?_⟩
  rintro ⟨k, p, hk, hp, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  exact hmain k hk (by omega) (by simpa using hp)

-- ════════════════════════════════════════════════════════════════════
-- §9 SATISFIABILITY WITNESSES AND GROUND CHECKS
-- ════════════════════════════════════════════════════════════════════

-- The hypotheses of §5–§6 are jointly instantiable at `m = M`, the
-- least member of the progression: `M % P = M` (as `M < P`) and
-- `2 ^ 1 + 241 = 243 < M`.
example : erdosResidue1950 % erdosModulus1950 = erdosResidue1950 := by decide
example : (1 : ℕ) ≤ 1 ∧ 2 ^ 1 + 241 < erdosResidue1950 ∧ 244 ≤ erdosResidue1950 := by
  decide

-- The predicted fixed divisor, class by class, at `m = M = 7629217`
-- (and at `m = M + P = 18814027` for `k = 23`, where `2 ^ 23 > M`).
-- These check the pairing table of the module header row by row.
example : (3 : ℕ) ∣ 7629217 - 2 ^ 2 := by decide     -- k ≡ 0 (mod 2)
example : (7 : ℕ) ∣ 7629217 - 2 ^ 9 := by decide     -- k ≡ 0 (mod 3)
example : (5 : ℕ) ∣ 7629217 - 2 ^ 1 := by decide     -- k ≡ 1 (mod 4)
example : (17 : ℕ) ∣ 7629217 - 2 ^ 11 := by decide   -- k ≡ 3 (mod 8)
example : (13 : ℕ) ∣ 7629217 - 2 ^ 7 := by decide    -- k ≡ 7 (mod 12)
example : (241 : ℕ) ∣ 18814027 - 2 ^ 23 := by decide -- k ≡ 23 (mod 24)

-- The conclusions are genuinely nontrivial: these are composite, and
-- `norm_num` certifies it independently of the covering argument.
-- (7629215 = 5·11·23·37·163, 7629213 = 3·563·4517,
--  7629209 = 7·17·61·1051, 7629089 = 13·19·67·461,
--  10425419 = 181·239·241.)
example : ¬ Nat.Prime (7629217 - 2 ^ 1) := by norm_num
example : ¬ Nat.Prime (7629217 - 2 ^ 2) := by norm_num
example : ¬ Nat.Prime (7629217 - 2 ^ 3) := by norm_num
example : ¬ Nat.Prime (7629217 - 2 ^ 7) := by norm_num
example : ¬ Nat.Prime (18814027 - 2 ^ 23) := by norm_num

-- The witness `erdos_1950` produces at `B = 0`: block exponent
-- `K = 25`, `t = 2 ^ 25 = 33554432`, so
-- `m = M + P · ((t + 241)/P + 1) = 7629217 + 11184810 · 4 = 52368457`,
-- which lies strictly inside `(2 ^ 25 + 241, 2 ^ 26)` as the dyadic
-- block argument requires.
example : (52368457 : ℕ) % erdosModulus1950 = erdosResidue1950 := by decide
example : 2 ^ 25 + 241 < 52368457 ∧ (52368457 : ℕ) < 2 ^ 26 := by decide
example : Odd (52368457 : ℕ) := Nat.odd_iff.mpr (by decide)
example : ¬ Nat.Prime (52368457 - 2 ^ 25) := by norm_num  -- 18814025 = 5²·83·9067

-- NON-VACUITY of the inner `∀ k` in §7 and §8.  A theorem whose inner
-- quantifier ranged over an empty set of exponents would assert
-- nothing, so pin the exponent ranges of the two `B = 0` witnesses.
--
-- §8 `erdos_1950` at `B = 0` gives `m = 52368457`; the guard
-- `2 ^ k < m` holds exactly for `1 ≤ k ≤ 25`, so 25 exponents are
-- constrained.
example : 2 ^ 25 < 52368457 ∧ ¬ ((2 : ℕ) ^ 26 < 52368457) := by decide

-- §7 `exists_gt_odd_not_prime_sub_two_pow_of_lt` at `B = 0` gives
-- `m = M + P = 18814027`; the guard `2 ^ k + 241 < m` holds exactly
-- for `1 ≤ k ≤ 24`, so 24 exponents are constrained.
example : erdosResidue1950 + erdosModulus1950 * (0 + 1) = 18814027 := by decide
example : 2 ^ 24 + 241 < 18814027 ∧ ¬ ((2 : ℕ) ^ 25 + 241 < 18814027) := by decide
example : ¬ Nat.Prime (18814027 - 2 ^ 24) := by norm_num  -- 2036811 = 3·7·23·4217

-- ════════════════════════════════════════════════════════════════════
-- §10 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms erdosSystem1950
#print axioms isCoveringSystem_erdosSystem1950
#print axioms erdosPrimes1950
#print axioms orderOf_two_zmod_three
#print axioms orderOf_two_zmod_seven
#print axioms orderOf_two_zmod_five
#print axioms orderOf_two_zmod_seventeen
#print axioms orderOf_two_zmod_thirteen
#print axioms orderOf_two_zmod_241
#print axioms two_pow_modEq_one_of_pow_eq_one
#print axioms erdosModulus1950
#print axioms erdosResidue1950
#print axioms dvd_sub_two_pow_of_modEq
#print axioms erdosSystem1950_covers_nat
#print axioms exists_mem_erdosPrimes1950_dvd
#print axioms not_prime_sub_two_pow
#print axioms not_prime_sub_two
#print axioms exists_gt_odd_not_prime_sub_two_pow_of_lt
#print axioms erdos_1950
#print axioms erdos_1950_not_two_pow_add_prime

end Erdos.Covering
