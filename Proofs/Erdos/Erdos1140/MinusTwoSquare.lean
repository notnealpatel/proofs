/-
  Erdos/Erdos1140/MinusTwoSquare — erdosproblems.com #1140: the `n` for
  which `n - 2x²` is prime for every `x` with `2x² < n`.

  GROUND TRUTH PINNING (`goof erdos fetch 1140`, pulled 2026-08-05).

  Problem statement, verbatim:

    "Do there exist infinitely many $n$ such that $n-2x^2$ is prime for
    all $x$ with $2x^2<n$?"

  Database section, verbatim:

    "The known such $n$ are\[2,5,7,13,31,61,181,199.\]It is known that
    these are, with at most one exception, all such $n$. Theorem 4.1 of
    Epure and Gica \cite{EpGi10} implies that the only such $n\equiv
    1\pmod{4}$ are $5,13,61,181$. Epure and Gica also remark that their
    method, coupled with a result of Mollin and Williams \cite{MoWi89},
    implies that the only such $n\equiv 3\pmod{4}$ are $7,31,199$, and at
    most one other exception.

    See also [1141]."

  References section, verbatim:

    "[EpGi10] Epure, Mihai and Gica, Alexandru, *Principal quadratic real
    fields in connection with some additive problems*. Bull. Math. Soc.
    Sci. Math. Roumanie (N.S.) (2010), 251--259.

    [MoWi89] Mollin, R. A. and Williams, H. C., *Period four and real
    quadratic fields of class number one*. Proc. Japan Acad. Ser. A Math.
    Sci. (1989), 89--93."

  No OEIS entry exists for the member list: `goof oeis match
  "2,5,7,13,31,61,181,199"` and the same query without its first or last
  term all return 0 results (2026-08-05). The Erdős database is therefore
  the sole primary source pinned here.

  WHAT THE SOURCE DOES AND DOES NOT SETTLE. The three mod-4 classes are
  exhaustive once the even case is disposed of, and the even case is
  elementary (§5 below, proved): `x = 0` is always in range, so any such
  `n` is itself prime, and an even prime is `2`. So the database's two
  cited results — Epure–Gica Theorem 4.1 for `n ≡ 1 (mod 4)`, and their
  method with Mollin–Williams for `n ≡ 3 (mod 4)` — together bound the
  full solution set by nine elements, and the answer to the problem as
  posed is NO. Both cited results are class-number-one statements about
  real quadratic fields, far outside current Mathlib; they are this
  file's two intended `sorry`s (§8). Everything else is proved.

  THE VACUITY TRAP, AND WHY `0 < n` IS PART OF THE PREDICATE. The raw
  body `∀ x, 2x² < n → (n - 2x²).Prime` is satisfied *vacuously* at
  `n = 0`: no `x` has `2x² < 0`. It is the only vacuous solution — at
  `n ≥ 1` the value `x = 0` is always in range, which is also why every
  member is prime. `n = 1` is therefore excluded on its merits
  (`1` is not prime), not by the guard. §2 discloses this explicitly.

  A TRAP IN THE OBSTRUCTION ARGUMENT (§6). Terence Tao, in the #1140
  comment thread (post-3742, 06:25 on 25 Jan 2026), verbatim: "$p|n-2x^2$
  and $n-2x^2>1$ does not quite imply that $n-2x^2$ is composite, because
  it could be equal to $p$." The congruence obstructions below are stated
  so that this cannot happen: `not_dvd_sub_of_two_mul_sq` carries the
  hypothesis `P + q < n`, i.e. `q < n - P` *strictly*, so `q ∣ (n - P)`
  with `n - P` prime is a genuine contradiction.

  CONTENTS.
    § 1 `AllPrimeMinusTwoSq` (raw body), `IsAllPrimeMinusTwoSq` (guarded
        predicate), the finite-range reformulation, `Decidable` instances.
    § 2 Degeneracy disclosure: `n = 0` is the unique vacuous solution;
        above the guard the quantified domain is nonempty, and every
        member is prime.
    § 3 The eight membership certificates of the database list, checked
        by kernel reduction.
    § 4 Negative controls, each with its explicit witness `x`.
    § 5 The even case, PROVED: a member divisible by `2` equals `2`. This
        is what makes the source's mod-4 dichotomy exhaustive.
    § 6 The congruence obstruction, PROVED: every member `n > 5`
        satisfies `n ≡ 1 (mod 6)`. Cuts the §7 search by a factor of six.
    § 7 The finite completeness window: no member in `(199, 10 ^ 6]`.
        Kernel-checked to `10 ^ 4`, `native_decide`-checked to `10 ^ 6`.
    § 8 ARCHIVED (this file's two intended `sorry`s): Epure–Gica Thm 4.1,
        and Mollin–Williams + Epure–Gica for `n ≡ 3 (mod 4)`.
    § 9 Consequences, no new `sorry`: the solution set is finite (the
        answer NO), and differs from the database's eight-element list by
        at most one element.
    § 10 Axiom audit.

  TRUST SURFACE OF §7. The `native_decide` sweep is granted by this
  lane's brief and is the only one in the file. It is deliberately routed
  through `NoSmallFactor` — trial division by the primes below `100` —
  and *not* through `Nat.Prime`. Reason: Mathlib's kernel-facing
  `Nat.decidablePrime` is swapped for the fast `Nat.decidablePrime'` by a
  `@[csimp]` lemma, and `@[csimp]` axiom dependencies do not surface in
  downstream `#print axioms` (lean4#7463; STYLE.md). Routing the sweep
  through `NoSmallFactor` keeps that swap out of the trusted base; what
  remains is the irreducible `native_decide` baseline (the Lean compiler
  plus core's `@[extern]` GMP `Nat` primitives). `sweep_kernel` re-checks
  the same statement to `10 ^ 4` with no native evaluation at all, so the
  `10 ^ 4` window carries only the `decide` trust surface.

  Since `NoSmallFactor` appears in §7 only as a *hypothesis*, weakening
  primality to it makes each swept statement **stronger**;
  `noSmallFactor_of_prime` is the only direction the window proof needs.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib

set_option autoImplicit false

namespace Erdos1140

-- ════════════════════════════════════════════════════════════════════
-- §1 THE PREDICATE
-- ════════════════════════════════════════════════════════════════════

/-- The **raw body** of the #1140 condition: `n - 2x²` is prime for every
`x` with `2x² < n`.

The source quantifies `x` over the integers; `2x²` depends only on `|x|`,
so quantifying over `ℕ` is the same condition.

The `ℕ` subtraction `n - 2 * x ^ 2` is totalized (it returns `0` once
`n ≤ 2x²`), so without a guard the statement would be about the junk
value. The guard is the hypothesis `2 * x ^ 2 < n` — the problem's own
range condition — which forces `0 < n - 2 * x ^ 2`; no `x` outside that
range is constrained.

This predicate is *vacuously true* at `n = 0` (§2). The membership
condition of the problem is `IsAllPrimeMinusTwoSq`. -/
def AllPrimeMinusTwoSq (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/-- **Membership in the #1140 solution set**: `0 < n`, and `n - 2x²` is
prime for every `x` with `2x² < n`.

The guard `0 < n` is not cosmetic: without it the vacuous solution
`n = 0` of `AllPrimeMinusTwoSq` sits in the solution set (§2). -/
def IsAllPrimeMinusTwoSq (n : ℕ) : Prop :=
  0 < n ∧ AllPrimeMinusTwoSq n

/-- `IsAllPrimeMinusTwoSq` spelled out. -/
theorem isAllPrimeMinusTwoSq_def (n : ℕ) :
    IsAllPrimeMinusTwoSq n ↔ 0 < n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2) :=
  Iff.rfl

/-- The unbounded `∀ x` collapses to a finite range: if `n ≤ 2B²` then
only `x < B` can satisfy `2x² < n`. This is what makes the predicate
kernel-decidable. -/
theorem allPrimeMinusTwoSq_iff_forall_lt {n B : ℕ} (hB : n ≤ 2 * B ^ 2) :
    AllPrimeMinusTwoSq n ↔
      ∀ x ∈ Finset.range B, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2) := by
  constructor
  · intro h x _ hx
    exact h x hx
  · intro h x hx
    have hxB : x < B := by
      by_contra hge
      have hBx : B ≤ x := Nat.not_lt.mp hge
      have hsq : B ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hBx 2
      omega
    exact h x (Finset.mem_range.mpr hxB) hx

/-- Decision procedure for `AllPrimeMinusTwoSq`, at the crude but always
valid bound `B = n` (`n ≤ 2n²`). At a fixed `n` prefer
`allPrimeMinusTwoSq_iff_forall_lt` at the tight `B ≈ √(n/2)`, as §3
does. -/
instance decidableAllPrimeMinusTwoSq : DecidablePred AllPrimeMinusTwoSq := fun n =>
  decidable_of_iff _
    (allPrimeMinusTwoSq_iff_forall_lt (n := n) (B := n) (by nlinarith)).symm

instance decidableIsAllPrimeMinusTwoSq : DecidablePred IsAllPrimeMinusTwoSq := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ AllPrimeMinusTwoSq n))

-- ════════════════════════════════════════════════════════════════════
-- §2 DEGENERACY DISCLOSURE
-- ════════════════════════════════════════════════════════════════════

/-- At `n = 0` the raw body is **vacuously true**: no `x` satisfies
`2x² < 0`. -/
theorem allPrimeMinusTwoSq_zero : AllPrimeMinusTwoSq 0 := fun _ hx => absurd hx (by omega)

/-- … and the guard is what removes it from the solution set. -/
theorem not_isAllPrimeMinusTwoSq_zero : ¬ IsAllPrimeMinusTwoSq 0 :=
  fun h => absurd h.1 (by norm_num)

/-- **Nonvacuity above the guard.** `n = 0` is the *only* vacuous
solution: at every `n ≥ 1` the value `x = 0` is in range, so
`IsAllPrimeMinusTwoSq n` constrains at least one prime at every `n` the
problem is about. -/
theorem two_mul_sq_lt_of_pos {n : ℕ} (hn : 0 < n) : 2 * (0 : ℕ) ^ 2 < n := by
  simpa using hn

/-- The first of those constraints, made explicit: **every member is
itself prime** (take `x = 0`). This is what the database list
`2, 5, 7, 13, 31, 61, 181, 199` reflects, and what §5 turns into the even
case. -/
theorem prime_of_isAllPrimeMinusTwoSq {n : ℕ} (h : IsAllPrimeMinusTwoSq n) : Nat.Prime n := by
  have h0 : Nat.Prime (n - 2 * (0 : ℕ) ^ 2) := h.2 0 (two_mul_sq_lt_of_pos h.1)
  simpa using h0

-- ════════════════════════════════════════════════════════════════════
-- §3 THE EIGHT MEMBERSHIP CERTIFICATES
-- ════════════════════════════════════════════════════════════════════

/-! The eight `n` of the database list. Each is discharged by kernel
reduction of the bounded reformulation at the tight bound `B`, the least
`B` with `n ≤ 2B²`. `decide +kernel` is ordinary kernel reduction: the
trust surface is exactly that of `decide`, only the (much slower)
elaborator-side replay of the same reduction is skipped. -/

/-- #1140 list, term 1: `n = 2`. The single value in range is `2`. -/
theorem cert_2 : IsAllPrimeMinusTwoSq 2 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 1) (by norm_num)).mpr (by decide +kernel)⟩

/-- #1140 list, term 2: `n = 5`. Values in range: `5, 3`. -/
theorem cert_5 : IsAllPrimeMinusTwoSq 5 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 2) (by norm_num)).mpr (by decide +kernel)⟩

/-- #1140 list, term 3: `n = 7`. Values in range: `7, 5`. -/
theorem cert_7 : IsAllPrimeMinusTwoSq 7 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 2) (by norm_num)).mpr (by decide +kernel)⟩

/-- #1140 list, term 4: `n = 13`. Values in range: `13, 11, 5`. -/
theorem cert_13 : IsAllPrimeMinusTwoSq 13 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 3) (by norm_num)).mpr (by decide +kernel)⟩

/-- #1140 list, term 5: `n = 31`. Values in range: `31, 29, 23, 13`. -/
theorem cert_31 : IsAllPrimeMinusTwoSq 31 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 4) (by norm_num)).mpr (by decide +kernel)⟩

/-- #1140 list, term 6: `n = 61`. Values in range: `61, 59, 53, 43, 29,
11`. -/
theorem cert_61 : IsAllPrimeMinusTwoSq 61 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 6) (by norm_num)).mpr (by decide +kernel)⟩

/-- #1140 list, term 7: `n = 181`. Values in range: `181, 179, 173, 163,
149, 131, 109, 83, 53, 19`. -/
theorem cert_181 : IsAllPrimeMinusTwoSq 181 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 10) (by norm_num)).mpr (by decide +kernel)⟩

/-- #1140 list, term 8: `n = 199`, the largest known member. Values in
range: `199, 197, 191, 181, 167, 149, 127, 101, 71, 37`. -/
theorem cert_199 : IsAllPrimeMinusTwoSq 199 :=
  ⟨by norm_num,
    (allPrimeMinusTwoSq_iff_forall_lt (B := 10) (by norm_num)).mpr (by decide +kernel)⟩

-- ════════════════════════════════════════════════════════════════════
-- §4 NEGATIVE CONTROLS
-- ════════════════════════════════════════════════════════════════════

/-- `1` fails at `x = 0`: `1` is not prime. It is excluded on its merits,
not by the `0 < n` guard — the raw body already fails here. -/
theorem not_allPrimeMinusTwoSq_one : ¬ AllPrimeMinusTwoSq 1 := fun h => by
  have h1 : Nat.Prime (1 - 2 * (0 : ℕ) ^ 2) := h 0 (by norm_num)
  norm_num at h1

/-- `3` fails at `x = 1`: `3 - 2 = 1` is not prime — though it passes at
`x = 0` (`3` is prime), so the failure is due to a later `x`. -/
theorem not_isAllPrimeMinusTwoSq_three : ¬ IsAllPrimeMinusTwoSq 3 := fun h => by
  have h1 : Nat.Prime (3 - 2 * (1 : ℕ) ^ 2) := h.2 1 (by norm_num)
  norm_num at h1

/-- `4` fails at `x = 0`: `4` is not prime. -/
theorem not_isAllPrimeMinusTwoSq_four : ¬ IsAllPrimeMinusTwoSq 4 := fun h => by
  have h1 : Nat.Prime (4 - 2 * (0 : ℕ) ^ 2) := h.2 0 (by norm_num)
  norm_num at h1

/-- `11` fails at `x = 1`: `11 - 2 = 9 = 3²`. It passes at `x = 0` and at
`x = 2` (`11 - 8 = 3`), so a single well-chosen `x` is what refutes it. -/
theorem not_isAllPrimeMinusTwoSq_eleven : ¬ IsAllPrimeMinusTwoSq 11 := fun h => by
  have h1 : Nat.Prime (11 - 2 * (1 : ℕ) ^ 2) := h.2 1 (by norm_num)
  norm_num at h1

/-- `211` fails at `x = 1`: `211 - 2 = 209 = 11 · 19`. This is the first
`n` above the largest known member `199` surviving *both* cheap
constraints — primality of `n` itself (§2) and `n ≡ 1 (mod 6)` (§6). The
only other candidate in between is `205 = 5 · 41`, which §2 already
kills. So `211` is the smallest place where the window sweep of §7 has to
do real work. -/
theorem not_isAllPrimeMinusTwoSq_211 : ¬ IsAllPrimeMinusTwoSq 211 := fun h => by
  have h1 : Nat.Prime (211 - 2 * (1 : ℕ) ^ 2) := h.2 1 (by norm_num)
  norm_num at h1

-- ════════════════════════════════════════════════════════════════════
-- §5 THE EVEN CASE, PROVED
-- ════════════════════════════════════════════════════════════════════

/-- **The even case of #1140, proved.** A member divisible by `2` is
`2` itself: by `prime_of_isAllPrimeMinusTwoSq` every member is prime, and
the only even prime is `2`.

This is the elementary third of the classification. Together with §8's
two archived class-number inputs it makes the database's mod-4 dichotomy
exhaustive. -/
theorem eq_two_of_two_dvd {n : ℕ} (h : IsAllPrimeMinusTwoSq n) (h2 : 2 ∣ n) : n = 2 :=
  ((prime_of_isAllPrimeMinusTwoSq h).eq_one_or_self_of_dvd 2 h2).resolve_left
    (by norm_num) |>.symm

/-- The even case in the form §9 consumes it: the two even residues mod
`4` both force `n = 2`, so only `n % 4 = 1` and `n % 4 = 3` — the two
classes the source's cited results cover — remain. -/
theorem eq_two_of_mod_four_even {n : ℕ} (h : IsAllPrimeMinusTwoSq n)
    (h4 : n % 4 = 0 ∨ n % 4 = 2) : n = 2 :=
  eq_two_of_two_dvd h (by omega)

-- ════════════════════════════════════════════════════════════════════
-- §6 THE CONGRUENCE OBSTRUCTION, PROVED
-- ════════════════════════════════════════════════════════════════════

/-- The single step of the obstruction: if `n - 2x²` is prime and
*strictly* exceeds `q ≥ 2`, then `q` does not divide `n - 2x²`. The
doubled square is passed as a separate numeral `P` with `2 * x ^ 2 = P`
so that the call sites stay `omega`-friendly.

The strictness `P + q < n` is exactly what answers Tao's objection quoted
in the module header: without it, `q ∣ (n - P)` is compatible with
`n - P` prime, namely when `n - P = q`. -/
theorem not_dvd_sub_of_two_mul_sq {n q x P : ℕ} (h : IsAllPrimeMinusTwoSq n) (hq : 2 ≤ q)
    (hP : 2 * x ^ 2 = P) (hlt : P + q < n) : ¬ q ∣ (n - P) := by
  subst hP
  have hp : Nat.Prime (n - 2 * x ^ 2) := h.2 x (by omega)
  exact (Nat.prime_def_lt'.mp hp).2 q hq (by omega)

/-- **Every member `n > 5` satisfies `n ≡ 1 (mod 6)`**, proved.

Two obstructions combine. Parity: `x = 0` makes `n` prime and `n > 2`, so
`n` is odd. Modulus `3`: the doubled squares `2x² mod 3` take the value
`0` at `x ≡ 0` and the value `2` at `x ≡ ±1`, so `x = 0, 1` already
realise the whole image `{0, 2}`. Forbidding `3 ∣ n - 2x²` at those two
values kills the residues `n ≡ 0` and `n ≡ 2 (mod 3)`, leaving
`n ≡ 1 (mod 3)`. The bound `5 < n` is what `x = 1` needs: `2 + 3 < n`.
(The residue `1` survives precisely because `2` is a non-residue mod `3`,
so `2x²` never lands on it — which is why this obstruction cuts by a
factor of three rather than eliminating everything.)

Checks out on the database list: `7, 13, 31, 61, 181, 199` are all
`≡ 1 (mod 6)`; the two members `2` and `5` are the ones below the
bound. -/
theorem mod_six_of_isAllPrimeMinusTwoSq {n : ℕ} (hn : 5 < n) (h : IsAllPrimeMinusTwoSq n) :
    n % 6 = 1 := by
  have d2 : ¬ (2 : ℕ) ∣ (n - 0) :=
    not_dvd_sub_of_two_mul_sq h (q := 2) (x := 0) (by norm_num) (by norm_num) (by omega)
  have d30 : ¬ (3 : ℕ) ∣ (n - 0) :=
    not_dvd_sub_of_two_mul_sq h (q := 3) (x := 0) (by norm_num) (by norm_num) (by omega)
  have d31 : ¬ (3 : ℕ) ∣ (n - 2) :=
    not_dvd_sub_of_two_mul_sq h (q := 3) (x := 1) (by norm_num) (by norm_num) (by omega)
  have r2 : n % 2 = 1 := by
    by_contra hne
    exact d2 (by omega)
  have r3 : n % 3 = 1 := by
    by_contra hne
    have hc : n % 3 = 0 ∨ n % 3 = 2 := by omega
    rcases hc with hc | hc
    · exact d30 (by omega)
    · exact d31 (by omega)
  omega

-- ════════════════════════════════════════════════════════════════════
-- §7 THE FINITE COMPLETENESS WINDOW
-- ════════════════════════════════════════════════════════════════════

section Window

/-- The primes below `100`, as a literal list; pinned exactly by the two
ground checks below. -/
def smallFactorList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- Ground check: every entry of `smallFactorList` is a prime below
`100`. -/
theorem prime_of_mem_smallFactorList {d : ℕ} (hd : d ∈ smallFactorList) :
    Nat.Prime d ∧ d < 100 := by
  have key : ∀ e ∈ smallFactorList, Nat.Prime e ∧ e < 100 := by decide +kernel
  exact key d hd

/-- Ground check: every prime below `100` is an entry of
`smallFactorList`. With `prime_of_mem_smallFactorList` this pins the list
exactly. -/
theorem mem_smallFactorList_of_prime {d : ℕ} (hd : Nat.Prime d) (hlt : d < 100) :
    d ∈ smallFactorList := by
  have key : ∀ e ∈ Finset.range 100, Nat.Prime e → e ∈ smallFactorList := by decide +kernel
  exact key d (Finset.mem_range.mpr hlt) hd

/-- `NoSmallFactor c`: `2 ≤ c`, and no prime below `100` is a *proper*
divisor of `c`. This is a deliberately cheap **necessary condition** for
primality, and it is what the sweeps of this section test.

It is *equivalent* to `Nat.Prime` only below `101 ^ 2 = 10201`
(`prime_iff_noSmallFactor`); above that it is strictly weaker — e.g.
`10201 = 101 ^ 2` satisfies it (see the ground checks). That is harmless
here, and is in fact what makes the window affordable: the sweeps use
`NoSmallFactor` as a *hypothesis*, so replacing primality by a weaker
condition makes each swept statement **stronger**, and
`noSmallFactor_of_prime` is the only direction the window proof needs.

Two further reasons for the detour, both about trust rather than speed
(module header): deciding `Nat.Prime p` through Mathlib's kernel-facing
instance costs `Θ(p)` reduction steps, and its compiled replacement is
installed by a `@[csimp]` lemma whose axiom dependencies would not
surface in `#print axioms` under `native_decide`. This costs at most 25
divisibility tests through core `Nat` arithmetic only, with early exit at
the first proper divisor found. The conjunct `2 ≤ c` excludes `c = 0`
and `c = 1`, which pass trial division vacuously. -/
def NoSmallFactor (c : ℕ) : Prop :=
  2 ≤ c ∧ ∀ d ∈ smallFactorList, d ∣ c → d = c

instance decidableNoSmallFactor : DecidablePred NoSmallFactor := fun c =>
  inferInstanceAs (Decidable (2 ≤ c ∧ ∀ d ∈ smallFactorList, d ∣ c → d = c))

/-- Primality implies `NoSmallFactor`, at any size. This is the only
direction the window proof uses. -/
theorem noSmallFactor_of_prime {c : ℕ} (h : Nat.Prime c) : NoSmallFactor c :=
  ⟨h.two_le, fun d hd hdvd =>
    (h.eq_one_or_self_of_dvd d hdvd).resolve_left
      (by have h2 := (prime_of_mem_smallFactorList hd).1.two_le; omega)⟩

/-- Ground truth for `NoSmallFactor`: below `101 ^ 2 = 10201` it is
*exactly* `Nat.Prime`. (A composite `c` has `minFac c ^ 2 ≤ c`, so
`minFac c < 101`, and `minFac c` is prime, hence at most `97`, hence
listed.) -/
theorem prime_iff_noSmallFactor {c : ℕ} (hc : c < 10201) :
    Nat.Prime c ↔ NoSmallFactor c := by
  refine ⟨noSmallFactor_of_prime, fun ⟨h2, hd⟩ => ?_⟩
  by_contra hnp
  have hpos : 0 < c := by omega
  have hdvd : c.minFac ∣ c := Nat.minFac_dvd c
  have hsq : c.minFac * c.minFac ≤ c := by
    have hs := Nat.minFac_sq_le_self hpos hnp
    rwa [pow_two] at hs
  have hpp : Nat.Prime c.minFac := Nat.minFac_prime (by omega)
  have h2p : 2 ≤ c.minFac := hpp.two_le
  have hlt : c.minFac < c := by nlinarith
  have hb : c.minFac < 101 := by nlinarith
  have hb' : c.minFac < 100 := by
    by_contra hge
    have heq : c.minFac = 100 := by omega
    rw [heq] at hpp
    norm_num at hpp
  exact absurd (hd _ (mem_smallFactorList_of_prime hpp hb') hdvd) (by omega)

-- Ground checks for `NoSmallFactor` at the boundaries.
example : ¬ NoSmallFactor 0 := by decide
example : ¬ NoSmallFactor 1 := by decide
example : NoSmallFactor 2 := by decide
example : NoSmallFactor 97 := by decide
example : ¬ NoSmallFactor 10199 := by decide

-- … and the disclosure that it is strictly weaker than primality, first
-- failing at `101 ^ 2 = 10201`.
example : NoSmallFactor 10201 ∧ ¬ Nat.Prime 10201 := ⟨by decide, by norm_num⟩

/-- The hypothesis supplier for the sweeps: a member makes every
`n - 2x²` in range pass the `NoSmallFactor` test. Only `x < 16` is used
below — that is already enough to eliminate every non-member up to
`10 ^ 6`. -/
theorem forall_noSmallFactor_of_isAllPrimeMinusTwoSq {n : ℕ} (h : IsAllPrimeMinusTwoSq n) :
    ∀ x ∈ List.range 16, 2 * x ^ 2 < n → NoSmallFactor (n - 2 * x ^ 2) :=
  fun x _ hx => noSmallFactor_of_prime (h.2 x hx)

/-- The five candidates `1 ≤ n ≤ 5`, below the reach of §6's `5 < n`
obstruction: only `2` and `5` are members. -/
theorem sweep_le_five : ∀ n ∈ Finset.Icc 1 5, IsAllPrimeMinusTwoSq n → n = 2 ∨ n = 5 := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- **Kernel-checked sweep to `10 ^ 4`.** The `1666` candidates
`n = 6j + 1` with `7 ≤ n ≤ 9997`: only `7, 13, 31, 61, 181, 199` survive
trial division by the primes below `100` at `x < 16`.

No `native_decide`: this is ordinary kernel reduction, so the `10 ^ 4`
window of `mem_of_isAllPrimeMinusTwoSq_of_le_10000` carries exactly the
`decide` trust surface.

The bound `10 ^ 4` is a *build-budget* choice, not a capability limit:
kernel cost is linear in the candidate count here (measured on this
toolchain: `J = 1666` ≈ 3 s, `J = 16666` ≈ 42 s), so a kernel-checked
`10 ^ 5` window is reachable at roughly a minute of elaboration. Raise
`J` here and in `mem_of_isAllPrimeMinusTwoSq_of_le_10000` together — the
sweep is stated so that only the two numerals change. -/
theorem sweep_kernel : ∀ j ∈ List.range' 1 1666,
    (∀ x ∈ List.range 16, 2 * x ^ 2 < 6 * j + 1 → NoSmallFactor (6 * j + 1 - 2 * x ^ 2)) →
    6 * j + 1 ∈ ({7, 13, 31, 61, 181, 199} : Finset ℕ) := by decide +kernel

/-- **`native_decide` sweep to `10 ^ 6`.** The `166666` candidates
`n = 6j + 1` with `7 ≤ n ≤ 999997`: only `7, 13, 31, 61, 181, 199`
survive. `sweep_kernel` is the same statement restricted to `j ≤ 1666`.

Enlarged trust surface, granted by this lane's brief and disclosed in the
module header: the Lean compiler and core's `@[extern]` `Nat`
primitives. No `Nat.Prime` — hence no Mathlib `@[csimp]` — is in the
evaluated term. This is the file's only `native_decide`. -/
theorem sweep_native : ∀ j ∈ List.range' 1 166666,
    (∀ x ∈ List.range 16, 2 * x ^ 2 < 6 * j + 1 → NoSmallFactor (6 * j + 1 - 2 * x ^ 2)) →
    6 * j + 1 ∈ ({7, 13, 31, 61, 181, 199} : Finset ℕ) := by native_decide

/-- Index bound for the sweeps. The slack `6J + 6` rather than `6J + 1`
is what lets the window bounds be round numbers: `n ≡ 1 (mod 6)` and
`n ≤ 6J + 6` already force `n ≤ 6J + 1`, so `j ≤ J`. -/
theorem index_bound {n j J : ℕ} (hj : n = 6 * j + 1) (h1 : 5 < n) (h2 : n ≤ 6 * J + 6) :
    j ∈ List.range' 1 J := by
  rw [List.mem_range'_1]
  omega

/-- The window, parametrised by which sweep supplies the elimination.
`5 < n ≤ 6J + 6` and membership force `n ∈ {7, 13, 31, 61, 181, 199}`. -/
theorem mem_of_gt_five {n J : ℕ} (h1 : 5 < n) (h2 : n ≤ 6 * J + 6)
    (hsweep : ∀ j ∈ List.range' 1 J,
      (∀ x ∈ List.range 16, 2 * x ^ 2 < 6 * j + 1 → NoSmallFactor (6 * j + 1 - 2 * x ^ 2)) →
      6 * j + 1 ∈ ({7, 13, 31, 61, 181, 199} : Finset ℕ))
    (h : IsAllPrimeMinusTwoSq n) : n ∈ ({7, 13, 31, 61, 181, 199} : Finset ℕ) := by
  have h6 : n % 6 = 1 := mod_six_of_isAllPrimeMinusTwoSq h1 h
  obtain ⟨j, hj⟩ : ∃ j, n = 6 * j + 1 := ⟨n / 6, by omega⟩
  have hf : ∀ x ∈ List.range 16, 2 * x ^ 2 < 6 * j + 1 →
      NoSmallFactor (6 * j + 1 - 2 * x ^ 2) := by
    rw [← hj]
    exact forall_noSmallFactor_of_isAllPrimeMinusTwoSq h
  rw [hj]
  exact hsweep j (index_bound hj h1 (by omega)) hf

/-- Assembly of the two ranges `n ≤ 5` and `5 < n`, parametrised by the
sweep. -/
theorem mem_of_isAllPrimeMinusTwoSq_of_le_aux {n J : ℕ} (hn : n ≤ 6 * J + 6)
    (hsweep : ∀ j ∈ List.range' 1 J,
      (∀ x ∈ List.range 16, 2 * x ^ 2 < 6 * j + 1 → NoSmallFactor (6 * j + 1 - 2 * x ^ 2)) →
      6 * j + 1 ∈ ({7, 13, 31, 61, 181, 199} : Finset ℕ))
    (h : IsAllPrimeMinusTwoSq n) :
    n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Finset ℕ) := by
  by_cases h5 : n ≤ 5
  · have hmem := sweep_le_five n (Finset.mem_Icc.mpr ⟨h.1, h5⟩) h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have hmem := mem_of_gt_five (by omega) hn hsweep h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    omega

/-- **The completeness window at `N = 10 ^ 4`, kernel-checked.** Sorry-
free and `native_decide`-free: the only `n ≤ 10 ^ 4` satisfying the #1140
condition are the eight of the database list. -/
theorem mem_of_isAllPrimeMinusTwoSq_of_le_10000 {n : ℕ} (hn : n ≤ 10000)
    (h : IsAllPrimeMinusTwoSq n) : n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Finset ℕ) :=
  mem_of_isAllPrimeMinusTwoSq_of_le_aux (J := 1666) (by omega) sweep_kernel h

/-- **The completeness window at `N = 10 ^ 6`** (implication form).
Sorry-free: the only `n ≤ 10 ^ 6` satisfying the #1140 condition are the
eight of the database list — so if the source's "at most one exception"
exists, it exceeds `10 ^ 6`. Uses `sweep_native`. -/
theorem mem_of_isAllPrimeMinusTwoSq_of_le {n : ℕ} (hn : n ≤ 1000000)
    (h : IsAllPrimeMinusTwoSq n) : n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Finset ℕ) :=
  mem_of_isAllPrimeMinusTwoSq_of_le_aux (J := 166666) (by omega) sweep_native h

/-- **The completeness window at `N = 10 ^ 6`** (set-equality form).
Sorry-free. -/
theorem setOf_isAllPrimeMinusTwoSq_le :
    {n : ℕ | n ≤ 1000000 ∧ IsAllPrimeMinusTwoSq n} =
      ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ) := by
  ext n
  constructor
  · rintro ⟨hn, h⟩
    have hmem := mem_of_isAllPrimeMinusTwoSq_of_le hn h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨by norm_num, cert_2⟩, ⟨by norm_num, cert_5⟩, ⟨by norm_num, cert_7⟩,
      ⟨by norm_num, cert_13⟩, ⟨by norm_num, cert_31⟩, ⟨by norm_num, cert_61⟩,
      ⟨by norm_num, cert_181⟩, ⟨by norm_num, cert_199⟩]

end Window

-- ════════════════════════════════════════════════════════════════════
-- §8 THE ARCHIVED LITERATURE INPUTS (this file's two `sorry`s)
-- ════════════════════════════════════════════════════════════════════

-- Satisfiability of the §8 hypotheses, jointly instantiated: both
-- archived statements are about nonempty situations, not vacuities.
example : IsAllPrimeMinusTwoSq 5 ∧ 5 % 4 = 1 := ⟨cert_5, by norm_num⟩
example : IsAllPrimeMinusTwoSq 181 ∧ 181 % 4 = 1 := ⟨cert_181, by norm_num⟩
example : (7 : ℕ) ∈ {n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} := ⟨cert_7, by norm_num⟩
example : (31 : ℕ) ∈ {n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} := ⟨cert_31, by norm_num⟩
example : (199 : ℕ) ∈ {n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} := ⟨cert_199, by norm_num⟩

/-- **Epure–Gica, Theorem 4.1** (erdosproblems.com #1140, verbatim:
"Theorem 4.1 of Epure and Gica \cite{EpGi10} implies that the only such
$n\equiv 1\pmod{4}$ are $5,13,61,181$").

INTENDED SORRY — archived literature input, disclosed in the module
header; one of this file's two. The cited result is a class-number-one
statement about principal real quadratic fields (Bull. Math. Soc. Sci.
Math. Roumanie 2010, 251–259); that machinery is far outside current
Mathlib, so this is archived rather than proved.

Note this class carries *no* exception in the source — the "at most one
exception" is attached only to `n ≡ 3 (mod 4)`.

Evidence in this file: `5, 13, 61, 181` are members (`cert_5`, `cert_13`,
`cert_61`, `cert_181`) and are exactly the members `≡ 1 (mod 4)` up to
`10 ^ 6` (`mem_of_isAllPrimeMinusTwoSq_of_le`, `native_decide`-checked;
`mem_of_isAllPrimeMinusTwoSq_of_le_10000` kernel-checked to `10 ^ 4`). -/
theorem epure_gica_thm_4_1 {n : ℕ} (h : IsAllPrimeMinusTwoSq n) (h4 : n % 4 = 1) :
    n ∈ ({5, 13, 61, 181} : Finset ℕ) := by
  -- intended sorry: archived class-number input [EpGi10, Thm 4.1].
  sorry

/-- **Mollin–Williams + Epure–Gica for `n ≡ 3 (mod 4)`**
(erdosproblems.com #1140, verbatim: "Epure and Gica also remark that
their method, coupled with a result of Mollin and Williams
\cite{MoWi89}, implies that the only such $n\equiv 3\pmod{4}$ are
$7,31,199$, and at most one other exception").

INTENDED SORRY — archived literature input, disclosed in the module
header; the second of this file's two. `Set.Subsingleton` on the set
difference is exactly "at most one other exception": the members
`≡ 3 (mod 4)` beyond `7, 31, 199` are pairwise equal, hence number at
most one. The exception is not effectively bounded — it comes from the
ineffective (Siegel–Tatuzawa) side of real quadratic class number one —
which is why no finite computation, this file's `10 ^ 6` window included,
can remove it.

Evidence in this file: `7, 31, 199` are members (`cert_7`, `cert_31`,
`cert_199`) and are exactly the members `≡ 3 (mod 4)` up to `10 ^ 6`
(`mem_of_isAllPrimeMinusTwoSq_of_le`), so any exception exceeds
`10 ^ 6`. -/
theorem mollin_williams_epure_gica :
    ({n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} \ ({7, 31, 199} : Set ℕ)).Subsingleton := by
  -- intended sorry: archived class-number input [MoWi89] + [EpGi10].
  sorry

-- ════════════════════════════════════════════════════════════════════
-- §9 CONSEQUENCES — no new `sorry`
-- ════════════════════════════════════════════════════════════════════

/-- The database's own summary, verbatim: "It is known that these are,
with at most one exception, all such $n$." Formally: the solution set
differs from the eight-element list by at most one element.

The three mod-4 classes are covered by §5 (even, proved), by
`epure_gica_thm_4_1` (`n ≡ 1`), and by `mollin_williams_epure_gica`
(`n ≡ 3`). No new `sorry`; `sorryAx`-dependent through those two. -/
theorem exceptional_subsingleton :
    ({n : ℕ | IsAllPrimeMinusTwoSq n} \
      ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ)).Subsingleton := by
  refine mollin_williams_epure_gica.anti ?_
  rintro n ⟨hn, hnot⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
  obtain ⟨hn2, hn5, hn7, hn13, hn31, hn61, hn181, hn199⟩ := hnot
  have h4 : n % 4 = 3 := by
    rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega) with h | h | h | h
    · exact absurd (eq_two_of_mod_four_even hn (Or.inl h)) hn2
    · -- the `n ≡ 1 (mod 4)` class is closed exactly by Epure–Gica
      have hmem := epure_gica_thm_4_1 hn h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    · exact absurd (eq_two_of_mod_four_even hn (Or.inr h)) hn2
    · exact h
  refine ⟨⟨hn, h4⟩, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hn7, hn31, hn199⟩

/-- **Erdős #1140, resolution: the answer is NO** — there are *not*
infinitely many `n` with `n - 2x²` prime for all `x` with `2x² < n`,
because there are only finitely many such `n` at all.

No new `sorry`; `sorryAx`-dependent through the two §8 literature inputs.
The bound is nine: the eight members of the database list plus the at
most one unlocated exception `≡ 3 (mod 4)`. -/
theorem erdos_1140 : {n : ℕ | IsAllPrimeMinusTwoSq n}.Finite := by
  have hknown : ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ).Finite :=
    (((((((Set.finite_singleton 199).insert 181).insert 61).insert 31).insert 13).insert
      7).insert 5).insert 2
  have hsub : {n : ℕ | IsAllPrimeMinusTwoSq n} ⊆
      ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ) ∪
        ({n : ℕ | IsAllPrimeMinusTwoSq n} \ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ)) := by
    intro n hn
    by_cases hm : n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ)
    · exact Or.inl hm
    · exact Or.inr ⟨hn, hm⟩
  exact (hknown.union exceptional_subsingleton.finite).subset hsub

/-- The problem as posed — "Do there exist infinitely many $n$ such that
$n-2x^2$ is prime for all $x$ with $2x^2<n$?" — answered: **no**.

No new `sorry`; `sorryAx`-dependent through `erdos_1140`. -/
theorem not_infinite_setOf_isAllPrimeMinusTwoSq :
    ¬ {n : ℕ | IsAllPrimeMinusTwoSq n}.Infinite :=
  Set.not_infinite.mpr erdos_1140

end Erdos1140

-- ════════════════════════════════════════════════════════════════════
-- §10 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

/-! ## Axiom audit

`Erdos1140.epure_gica_thm_4_1` and
`Erdos1140.mollin_williams_epure_gica` are the two intended `sorry`s and
report `sorryAx`, as do the three §9 declarations derived from them.

Every other declaration rests on a subset of `{propext,
Classical.choice, Quot.sound}` — with the single, disclosed exception of
`Erdos1140.sweep_native` and the two window theorems downstream of it
(`mem_of_isAllPrimeMinusTwoSq_of_le`, `setOf_isAllPrimeMinusTwoSq_le`),
which additionally report

    Erdos1140.sweep_native._native.native_decide.ax_1_1

That is the granted `native_decide`, and this per-declaration axiom is
exactly how it surfaces on this toolchain (Lean 4.33.0-rc1) — which also
makes the subset check a sound `native_decide` detector everywhere else
in the file. `mem_of_isAllPrimeMinusTwoSq_of_le_10000` is the same result
at `10 ^ 4` with that axiom absent.

The `decide +kernel` uses above are ordinary kernel reduction: the trust
surface is exactly that of `decide`, only the (much slower)
elaborator-side replay of the same reduction is skipped. No `axiom`, no
`@[csimp]`/`@[implemented_by]`/`@[extern]` declared here. -/

#print axioms Erdos1140.AllPrimeMinusTwoSq
#print axioms Erdos1140.IsAllPrimeMinusTwoSq
#print axioms Erdos1140.isAllPrimeMinusTwoSq_def
#print axioms Erdos1140.allPrimeMinusTwoSq_iff_forall_lt
#print axioms Erdos1140.decidableAllPrimeMinusTwoSq
#print axioms Erdos1140.decidableIsAllPrimeMinusTwoSq
#print axioms Erdos1140.allPrimeMinusTwoSq_zero
#print axioms Erdos1140.not_isAllPrimeMinusTwoSq_zero
#print axioms Erdos1140.two_mul_sq_lt_of_pos
#print axioms Erdos1140.prime_of_isAllPrimeMinusTwoSq
#print axioms Erdos1140.cert_2
#print axioms Erdos1140.cert_5
#print axioms Erdos1140.cert_7
#print axioms Erdos1140.cert_13
#print axioms Erdos1140.cert_31
#print axioms Erdos1140.cert_61
#print axioms Erdos1140.cert_181
#print axioms Erdos1140.cert_199
#print axioms Erdos1140.not_allPrimeMinusTwoSq_one
#print axioms Erdos1140.not_isAllPrimeMinusTwoSq_three
#print axioms Erdos1140.not_isAllPrimeMinusTwoSq_four
#print axioms Erdos1140.not_isAllPrimeMinusTwoSq_eleven
#print axioms Erdos1140.not_isAllPrimeMinusTwoSq_211
#print axioms Erdos1140.eq_two_of_two_dvd
#print axioms Erdos1140.eq_two_of_mod_four_even
#print axioms Erdos1140.not_dvd_sub_of_two_mul_sq
#print axioms Erdos1140.mod_six_of_isAllPrimeMinusTwoSq
#print axioms Erdos1140.smallFactorList
#print axioms Erdos1140.prime_of_mem_smallFactorList
#print axioms Erdos1140.mem_smallFactorList_of_prime
#print axioms Erdos1140.NoSmallFactor
#print axioms Erdos1140.decidableNoSmallFactor
#print axioms Erdos1140.noSmallFactor_of_prime
#print axioms Erdos1140.prime_iff_noSmallFactor
#print axioms Erdos1140.forall_noSmallFactor_of_isAllPrimeMinusTwoSq
#print axioms Erdos1140.sweep_le_five
#print axioms Erdos1140.sweep_kernel
#print axioms Erdos1140.sweep_native
#print axioms Erdos1140.index_bound
#print axioms Erdos1140.mem_of_gt_five
#print axioms Erdos1140.mem_of_isAllPrimeMinusTwoSq_of_le_aux
#print axioms Erdos1140.mem_of_isAllPrimeMinusTwoSq_of_le_10000
#print axioms Erdos1140.mem_of_isAllPrimeMinusTwoSq_of_le
#print axioms Erdos1140.setOf_isAllPrimeMinusTwoSq_le
#print axioms Erdos1140.epure_gica_thm_4_1
#print axioms Erdos1140.mollin_williams_epure_gica
#print axioms Erdos1140.exceptional_subsingleton
#print axioms Erdos1140.erdos_1140
#print axioms Erdos1140.not_infinite_setOf_isAllPrimeMinusTwoSq
