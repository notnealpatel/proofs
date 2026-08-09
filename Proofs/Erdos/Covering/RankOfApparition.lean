/-
  The rank of apparition α(m) and the zero sets of Fibonacci-like
  sequences.  The α-layer that `Erdos.Covering.FixedDivisor` needs in
  order to reach Fibonacci-like primefree families (Wilf's A083216).

  ── Why this file exists ────────────────────────────────────────────
  `FixedDivisor.lean` certifies a fixed divisor for `A · 2 ^ n + B` from
  a covering system plus, per class `(a, d, p)`, the order condition
  `2 ^ d ≡ 1 (mod p)`.  The Fibonacci-like analogue is NOT a periodicity
  condition: for a Fibonacci-like `s` and a prime `p`, `s mod p` is
  periodic with the Pisano period `π(p)`, but its ZERO SET is a single
  residue class modulo the strictly smaller

      α(p) = the rank of apparition = least `n > 0` with `p ∣ F n`,

  and α(p) is a proper divisor of π(p) for most primes — measured at
  (p, α, π) = (3, 4, 8), (5, 5, 20), (7, 8, 16), (13, 7, 28),
  (47, 16, 32), (2521, 60, 120), and among those eight measurements
  α = π only at (2, 3, 3) and (11, 10, 10).  That last clause is a fact
  about these eight primes and NOT a general one: α(p) = π(p) holds for
  infinitely many primes, and already for 2, 11, 19, 29, 31, 59, 71, 79,
  101, 131, 139, 151, 179, 181, 191, 199 below 200.  Of the eight
  tuples above only (3, 4, 8) and (2521, 60, 120) are checked in this
  file (§2); the other six are prose.  The per-class hypothesis a
  covering argument can
  actually use is therefore

      ∀ n, n % d = a % d → (p : ℤ) ∣ s n

  and `IsFibonacciLike.forall_mod_eq_dvd` below produces exactly that
  from `α(p) ∣ d` and one base divisibility `(p : ℤ) ∣ s a`.  The
  converse — that no larger zero set is possible — is
  `IsFibonacciLike.setOf_dvd_eq_empty_or_residueClass`.

  ── Terminology and sources ─────────────────────────────────────────
  "Rank of apparition", also "Fibonacci entry point": Wikipedia,
  *Pisano period*, §"Number of zeros in a cycle" — "The ratio of the
  Pisano period of n and the number of zeros modulo n in the cycle gives
  the rank of apparition or Fibonacci entry point of n.  That is,
  smallest index k such that n divides F(k)"; the notation α(m) is
  Renault's.  OEIS A001177 ("Fibonacci entry points: a(n) = least k >= 1
  such that n divides Fibonacci number F_k"), terms
  1, 3, 4, 6, 5, 12, 8, 6, 12, 15, 10, 12, 7, …, and A001602 for the
  prime-indexed subsequence.  Theorem (2) below is A001177's comment
  "All solutions to F_m == 0 (mod n) are given by m == 0 (mod a(n)).
  For a proof see, e.g., Vajda, p. 73."

  ── Mathlib inventory (enumerated, not guessed) ─────────────────────
  Enumerated 2026-07-31 against mathlib rev 3edb3c0658f6 (Lean
  4.33.0-rc1) as vendored in `.lake/packages/mathlib`:
  `grep -ric "apparition"` and `grep -ric "pisano"` over the whole
  `Mathlib/` tree return zero hits in zero files; the full declaration
  listings of `Mathlib/Data/Nat/Fib/Basic.lean`,
  `Mathlib/Data/Int/Fib/{Basic,Lemmas}.lean` and
  `Mathlib/Data/Nat/DvdSequence.lean` contain `Nat.fib_gcd`,
  `Nat.fib_coprime_fib_succ`, `Nat.fib_add`, `Nat.isDvdSequence_fib`,
  `Int.gcd_fib`, `Int.fib_dvd` and no rank-of-apparition, Pisano-period
  or general Lucas-sequence notion.  So `rankOfApparition` and
  everything in §3–§7 is built here from `Nat.fib_gcd` and
  `Nat.fib_add`.

  ── Contents ────────────────────────────────────────────────────────
  * §1 `fibPairShift`, `exists_pos_dvd_fib` — every `m > 0` divides some
    positive-index Fibonacci number.  The witness is the order of the
    Fibonacci shift as a permutation of `ZMod m × ZMod m`.
  * §2 `rankOfApparition`, its guard `rankOfApparition_zero`, and the
    minimality API.
  * §3 `dvd_fib_iff_rankOfApparition_dvd` — `m ∣ F n ↔ α(m) ∣ n`.
  * §4 `IsFibonacciLike`, `IsFibonacciLike.apply_add` — the shift
    identity `s (m + k + 1) = s m · F k + s (m+1) · F (k+1)`,
    generalizing `Nat.fib_add`.
  * §5 `IsFibonacciLike.dvd_of_mod_eq`, `.forall_mod_eq_dvd` — the
    per-class step, the direct analogue of
    `Erdos.Covering.dvd_affine_two_pow_of_mod_eq`.  No primality and no
    non-degeneracy needed.
  * §6 non-degeneracy: `IsFibonacciLike.not_dvd_succ_of_dvd`.
  * §7 `IsFibonacciLike.dvd_iff_mod_eq` and
    `.setOf_dvd_eq_empty_or_residueClass` — the zero set is empty or one
    class mod α(p).  Primality and non-degeneracy are both required and
    both are shown load-bearing in §9.
  * §8 satisfiability: `lucas` (OEIS A000032) and the named ranks
    α(2) = 3, α(3) = 4, α(4) = 6, α(5) = 5.  Both branches of §7 are
    inhabited — `exists_isFibonacciLike_setOf_dvd_eq_empty` (Lucas at
    p = 5: no Lucas number is divisible by 5) and
    `exists_isFibonacciLike_setOf_dvd_eq_residueClass` (Lucas at p = 3:
    the class 2 mod α(3) = 4, a *nonzero* base, which `Nat.fib` cannot
    exhibit since F 0 = 0).  `.setOf_dvd_eq_empty_of_forall_lt` reduces
    the empty branch to a check over one period.
  * §9 negative controls, each a refutation of §7 with one hypothesis
    deleted: `exists_not_prime_setOf_dvd_ne_empty_and_ne_residueClass`
    (primality — at the composite m = 4 with s = 2·F the zero set is
    {n | 3 ∣ n}, two classes mod α(4) = 6, not one) and
    `exists_degenerate_setOf_dvd_ne_empty_and_ne_residueClass`
    (non-degeneracy — at p = 3 with s = 3·F the zero set is all of ℕ,
    and `univ_ne_setOf_mod_eq` shows that is no residue class).
  * §10 axiom audit.

  Axiom audit: see §10.  Every declaration is sorry-free.  No
  `native_decide`, no custom axioms — and this is *checked*, not
  asserted: §10 runs `#print axioms` on the headline theorems and then
  sweeps every constant this module adds, failing the build unless each
  one's axioms lie in {propext, Classical.choice, Quot.sound}.  The
  sweep is an allowlist-subset test because `native_decide` mints a
  fresh axiom named after the declaration that used it, so no fixed
  axiom name can be grepped for.
-/

import Mathlib

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 EXISTENCE: EVERY POSITIVE `m` DIVIDES SOME FIBONACCI NUMBER
-- ════════════════════════════════════════════════════════════════════

/-- The Fibonacci shift on pairs modulo `m`: `(x, y) ↦ (y, x + y)`.  It
    is a permutation of `ZMod m × ZMod m` because the recurrence runs
    backwards, `(x, y) ↦ (y - x, x)`; this invertibility is exactly what
    makes the Fibonacci sequence *purely* periodic mod `m`, hence what
    forces `0` to recur. -/
def fibPairShift (m : ℕ) : Equiv.Perm (ZMod m × ZMod m) where
  toFun q := (q.2, q.1 + q.2)
  invFun q := (q.2 - q.1, q.1)
  left_inv q := by simp
  right_inv q := by simp

/-- `fibPairShift` computes as advertised. -/
theorem fibPairShift_apply (m : ℕ) (q : ZMod m × ZMod m) :
    fibPairShift m q = (q.2, q.1 + q.2) := rfl

-- Ground checks for `fibPairShift` at `m = 5`, where `F` mod `5` runs
-- `0, 1, 1, 2, 3, 0, 3, 3, 1, 4, 0, …`.
example : fibPairShift 5 (0, 1) = (1, 1) := by decide
example : fibPairShift 5 (3, 4) = (4, 2) := by decide
example : (fibPairShift 5).symm (1, 1) = (0, 1) := by decide

/-- The `n`-th iterate of the shift, started at `(F 0, F 1) = (0, 1)`,
    is `(F n, F (n+1))` mod `m`. -/
theorem fibPairShift_pow_apply (m n : ℕ) :
    (fibPairShift m ^ n) (0, 1) = ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, fibPairShift_apply]
    simp [Nat.fib_add_two]

/-- **Every positive `m` divides some Fibonacci number of positive
    index.**  This is what makes `rankOfApparition m` meaningful for
    `m > 0`; the witness is `orderOf (fibPairShift m)`, positive because
    `Equiv.Perm (ZMod m × ZMod m)` is a finite group. -/
theorem exists_pos_dvd_fib {m : ℕ} (hm : 0 < m) : ∃ n, 0 < n ∧ m ∣ Nat.fib n := by
  haveI : NeZero m := ⟨hm.ne'⟩
  refine ⟨orderOf (fibPairShift m), orderOf_pos _, ?_⟩
  have hiter := fibPairShift_pow_apply m (orderOf (fibPairShift m))
  rw [pow_orderOf_eq_one] at hiter
  have hzero : ((Nat.fib (orderOf (fibPairShift m)) : ZMod m)) = 0 :=
    (congrArg Prod.fst hiter).symm
  exact (ZMod.natCast_eq_zero_iff _ _).mp hzero

-- ════════════════════════════════════════════════════════════════════
-- §2 THE DEFINITION
-- ════════════════════════════════════════════════════════════════════

/-- The **rank of apparition** `α(m)` of `m` (OEIS A001177, also
    "Fibonacci entry point"): the least `n > 0` with `m ∣ F n`.

    Junk value: `sInf ∅ = 0`, so `rankOfApparition 0 = 0`
    (`rankOfApparition_zero`) — `0 ∣ F n` forces `n = 0`, and the index
    `0` is excluded by the `0 < n` conjunct.  For every `m > 0` the set
    is nonempty (`exists_pos_dvd_fib`) and `0 < rankOfApparition m`
    (`rankOfApparition_pos`), so `0 < m` is the guard that keeps every
    statement below off the junk value.  The `0 < n` conjunct is itself
    a guard: without it the infimum would be `0` for every `m`, since
    `m ∣ F 0 = 0` always. -/
noncomputable def rankOfApparition (m : ℕ) : ℕ := sInf {n | 0 < n ∧ m ∣ Nat.fib n}

/-- For `m > 0` the rank of apparition is positive and does what it
    says: `m ∣ F (α m)`. -/
theorem rankOfApparition_spec {m : ℕ} (hm : 0 < m) :
    0 < rankOfApparition m ∧ m ∣ Nat.fib (rankOfApparition m) :=
  Nat.sInf_mem (by obtain ⟨n, hn⟩ := exists_pos_dvd_fib hm; exact ⟨n, hn⟩)

/-- For `m > 0` the rank of apparition is positive. -/
theorem rankOfApparition_pos {m : ℕ} (hm : 0 < m) : 0 < rankOfApparition m :=
  (rankOfApparition_spec hm).1

/-- `m` divides the Fibonacci number at its own rank of apparition. -/
theorem dvd_fib_rankOfApparition {m : ℕ} (hm : 0 < m) :
    m ∣ Nat.fib (rankOfApparition m) := (rankOfApparition_spec hm).2

/-- Minimality: any positive index at which `m` divides a Fibonacci
    number is at least the rank of apparition.  No hypothesis on `m` is
    needed — the hypotheses already witness nonemptiness. -/
theorem rankOfApparition_le {m n : ℕ} (hn : 0 < n) (h : m ∣ Nat.fib n) :
    rankOfApparition m ≤ n := Nat.sInf_le ⟨hn, h⟩

/-- The computation rule for concrete ranks: `α(m) = n` as soon as `n`
    is a positive index with `m ∣ F n` and no smaller positive index
    works.  Both side conditions are decidable, so concrete ranks are
    settled by `decide`. -/
theorem rankOfApparition_eq_of {m n : ℕ} (hn : 0 < n) (hdvd : m ∣ Nat.fib n)
    (hmin : ∀ k < n, 0 < k → ¬ m ∣ Nat.fib k) : rankOfApparition m = n := by
  refine le_antisymm (rankOfApparition_le hn hdvd) (not_lt.mp fun hlt => ?_)
  obtain ⟨hpos, hd⟩ : rankOfApparition m ∈ {n | 0 < n ∧ m ∣ Nat.fib n} :=
    Nat.sInf_mem ⟨n, hn, hdvd⟩
  exact hmin _ hlt hpos hd

/-- **The junk value, stated.**  `rankOfApparition 0 = 0`: the defining
    set is empty because `0 ∣ F n` forces `F n = 0`, hence `n = 0`,
    which the `0 < n` conjunct excludes. -/
theorem rankOfApparition_zero : rankOfApparition 0 = 0 :=
  Nat.sInf_eq_zero.mpr <| Or.inr <| Set.eq_empty_of_forall_notMem fun _ hn =>
    absurd (Nat.fib_eq_zero.mp (zero_dvd_iff.mp hn.2)) hn.1.ne'

-- Ground checks against OEIS A001177 (`α(1), …, α(13)` =
-- 1, 3, 4, 6, 5, 12, 8, 6, 12, 15, 10, 12, 7) and against the tuples
-- measured for the covering arc: α(3) = 4, α(7) = 8, α(47) = 16,
-- α(2521) = 60.
example : rankOfApparition 1 = 1 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 2 = 3 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 3 = 4 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 4 = 6 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 5 = 5 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 6 = 12 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 7 = 8 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 13 = 7 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 47 = 16 := rankOfApparition_eq_of (by norm_num) (by decide) (by decide)
example : rankOfApparition 2521 = 60 :=
  rankOfApparition_eq_of (by norm_num) (by decide) (by decide)

-- The rank is NOT the Pisano period.  The Pisano period is the least
-- `n > 0` at which the pair `(F n, F (n+1))` returns to `(0, 1)`; these
-- checks pin it at `8` for `p = 3` (against α(3) = 4) and at `120` for
-- `p = 2521` (against α(2521) = 60), reproducing two of the tuples that
-- the covering-arc certificate measured.
example : ∀ n < 8, 0 < n → ¬ (Nat.fib n % 3 = 0 ∧ Nat.fib (n + 1) % 3 = 1) := by decide
example : Nat.fib 8 % 3 = 0 ∧ Nat.fib 9 % 3 = 1 := by decide
example : ∀ n < 120, 0 < n → ¬ (Nat.fib n % 2521 = 0 ∧ Nat.fib (n + 1) % 2521 = 1) := by decide
example : Nat.fib 120 % 2521 = 0 ∧ Nat.fib 121 % 2521 = 1 := by decide

-- ════════════════════════════════════════════════════════════════════
-- §3 THE DIVISIBILITY CHARACTERIZATION
-- ════════════════════════════════════════════════════════════════════

/-- **`m ∣ F n ↔ α(m) ∣ n`.**  The Fibonacci numbers divisible by `m`
    are exactly those whose index is a multiple of the rank of
    apparition — including `n = 0`, where both sides hold (`m ∣ F 0 = 0`
    and `α(m) ∣ 0`).

    `←` is the divisibility-sequence property `Nat.isDvdSequence_fib`;
    `→` is the strong divisibility property `Nat.fib_gcd` plus
    minimality.  This is the statement recorded in OEIS A001177's
    comment "All solutions to `F_m ≡ 0 (mod n)` are given by
    `m ≡ 0 (mod a(n))`", attributed there to Vajda p. 73. -/
theorem dvd_fib_iff_rankOfApparition_dvd {m : ℕ} (hm : 0 < m) (n : ℕ) :
    m ∣ Nat.fib n ↔ rankOfApparition m ∣ n := by
  obtain ⟨hpos, hdvd⟩ := rankOfApparition_spec hm
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact dvd_zero _
    · -- `m` divides both `F n` and `F α`, hence their gcd `F (gcd n α)`.
      have hg : m ∣ Nat.fib (Nat.gcd n (rankOfApparition m)) := by
        rw [Nat.fib_gcd]; exact Nat.dvd_gcd h hdvd
      have hgpos : 0 < Nat.gcd n (rankOfApparition m) := Nat.gcd_pos_of_pos_left _ hn
      -- Minimality pins that gcd at `α` itself, so `α ∣ n`.
      have hge : rankOfApparition m ≤ Nat.gcd n (rankOfApparition m) :=
        rankOfApparition_le hgpos hg
      have hle : Nat.gcd n (rankOfApparition m) ∣ rankOfApparition m :=
        Nat.gcd_dvd_right _ _
      have hgcd : Nat.gcd n (rankOfApparition m) = rankOfApparition m :=
        Nat.le_antisymm (Nat.le_of_dvd hpos hle) hge
      exact hgcd ▸ Nat.gcd_dvd_left n (rankOfApparition m)
  · intro h
    exact dvd_trans hdvd (Nat.isDvdSequence_fib _ _ h)

-- The guard `0 < m` costs nothing: at `m = 0` both sides degenerate to
-- `n = 0` and the equivalence still holds, by `rankOfApparition_zero`.
example (n : ℕ) : (0 : ℕ) ∣ Nat.fib n ↔ rankOfApparition 0 ∣ n := by
  rw [rankOfApparition_zero, zero_dvd_iff, zero_dvd_iff, Nat.fib_eq_zero]

-- ════════════════════════════════════════════════════════════════════
-- §4 FIBONACCI-LIKE SEQUENCES
-- ════════════════════════════════════════════════════════════════════

/-- `s : ℕ → ℤ` is **Fibonacci-like** if it satisfies the Fibonacci
    recurrence `s (n+2) = s (n+1) + s n`.  The initial pair
    `(s 0, s 1)` is unconstrained; `Nat.fib`, the Lucas numbers and
    Wilf's primefree sequence A083216 are all instances. -/
def IsFibonacciLike (s : ℕ → ℤ) : Prop := ∀ n, s (n + 2) = s (n + 1) + s n

-- Ground checks for `IsFibonacciLike`: Fibonacci itself, the Lucas
-- numbers `L n = 2 F (n+1) - F n` = 2, 1, 3, 4, 7, 11, …, and a
-- negative control (`n ↦ n` fails first at `n = 2`).
example : IsFibonacciLike (fun n => (Nat.fib n : ℤ)) := by
  intro n; push_cast [Nat.fib_add_two]; ring

example : IsFibonacciLike (fun n => 2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n) := by
  intro n; push_cast [Nat.fib_add_two]; ring

example : (fun n => 2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n) 0 = 2 := by decide
example : (fun n => 2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n) 4 = 7 := by decide

example : ¬ IsFibonacciLike (fun n => (n : ℤ)) := fun h => by
  have h2 := h 2
  norm_num at h2

/-- Simultaneous form of the shift identity, proved by one-step
    induction on `k` with both consecutive instances carried. -/
theorem IsFibonacciLike.apply_add_aux {s : ℕ → ℤ} (hs : IsFibonacciLike s) (m k : ℕ) :
    s (m + k + 1) = s m * Nat.fib k + s (m + 1) * Nat.fib (k + 1) ∧
      s (m + k + 2) = s m * Nat.fib (k + 1) + s (m + 1) * Nat.fib (k + 2) := by
  induction k with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [show m + 0 + 2 = m + 2 from rfl, hs m, show Nat.fib 1 = 1 from rfl,
      show Nat.fib (0 + 2) = 1 from rfl]
    push_cast
    ring
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    rw [show m + (k + 1) + 2 = m + k + 1 + 2 from by omega, hs (m + k + 1),
      show m + k + 1 + 1 = m + k + 2 from rfl, ih2, ih1]
    push_cast [Nat.fib_add_two]
    ring

/-- **The shift identity.**  A Fibonacci-like sequence restarted at
    index `m` is the same combination of Fibonacci numbers that
    `Nat.fib_add` records for `Nat.fib` itself:

        `s (m + k + 1) = s m · F k + s (m+1) · F (k+1)`.

    Taking `s = Nat.fib` recovers `Nat.fib_add` verbatim.  Everything in
    §5–§7 is a consequence of this identity and §3. -/
theorem IsFibonacciLike.apply_add {s : ℕ → ℤ} (hs : IsFibonacciLike s) (m k : ℕ) :
    s (m + k + 1) = s m * Nat.fib k + s (m + 1) * Nat.fib (k + 1) := (hs.apply_add_aux m k).1

-- The identity specializes to `Nat.fib_add`.
example (m k : ℕ) :
    (Nat.fib (m + k + 1) : ℤ) = Nat.fib m * Nat.fib k + Nat.fib (m + 1) * Nat.fib (k + 1) :=
  IsFibonacciLike.apply_add (s := fun n => (Nat.fib n : ℤ))
    (fun n => by push_cast [Nat.fib_add_two]; ring) m k

-- ════════════════════════════════════════════════════════════════════
-- §5 TRANSPORT ALONG A CLASS — THE PER-CLASS STEP
-- ════════════════════════════════════════════════════════════════════

/-- **Forward transport.**  If `m` divides `s a` and divides `F k`, it
    divides `s (a + k)`.  Immediate from the shift identity: both
    summands of `s a · F (k-1) + s (a+1) · F k` are then multiples of
    `m`. -/
theorem IsFibonacciLike.dvd_add_of_dvd {m : ℕ} {s : ℕ → ℤ} (hs : IsFibonacciLike s)
    {a k : ℕ} (hfib : m ∣ Nat.fib k) (ha : (m : ℤ) ∣ s a) : (m : ℤ) ∣ s (a + k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using ha
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show a + (j + 1) = a + j + 1 from rfl, hs.apply_add a j]
    exact _root_.dvd_add (ha.mul_right _)
      (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hfib) _)

/-- **Backward transport.**  If `m` divides `F k` and divides
    `s (a + k)`, it divides `s a`.  The shift identity leaves
    `m ∣ s a · F (k-1)`, and `m ∣ F k` forces `m` coprime to `F (k-1)`
    because consecutive Fibonacci numbers are coprime
    (`Nat.fib_coprime_fib_succ`) — so the factor `F (k-1)` cancels with
    no primality assumption on `m`. -/
theorem IsFibonacciLike.dvd_of_dvd_add {m : ℕ} {s : ℕ → ℤ} (hs : IsFibonacciLike s)
    {a k : ℕ} (hfib : m ∣ Nat.fib k) (hak : (m : ℤ) ∣ s (a + k)) : (m : ℤ) ∣ s a := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hak
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show a + (j + 1) = a + j + 1 from rfl, hs.apply_add a j] at hak
    have hfibZ : (m : ℤ) ∣ (Nat.fib (j + 1) : ℤ) := Int.natCast_dvd_natCast.mpr hfib
    have hmul : (m : ℤ) ∣ s a * Nat.fib j := by
      have hsub := dvd_sub hak (hfibZ.mul_left (s (a + 1)))
      simpa using hsub
    have hcop : Nat.Coprime m (Nat.fib j) :=
      Nat.Coprime.coprime_dvd_left hfib (Nat.fib_coprime_fib_succ j).symm
    exact (Nat.isCoprime_iff_coprime.mpr hcop).dvd_of_dvd_mul_right hmul

/-- **One class, one divisor** — the per-class step, and the direct
    analogue of `Erdos.Covering.dvd_affine_two_pow_of_mod_eq` for the
    Fibonacci-like family.  If `α(m) ∣ d` and `m` divides the sequence
    at the base index `a` of its class, then `m` divides the sequence at
    every index `n ≡ a (mod d)`.

    `α(m) ∣ d` plays the role that `2 ^ d ≡ 1 (mod p)` plays in
    `FixedDivisor.lean`: it is the condition making the modulus `d`
    compatible with the divisor.  Neither primality of `m` nor any
    non-degeneracy of `s` is needed — this direction is the one the
    covering layer consumes, and it is the cheap one. -/
theorem IsFibonacciLike.dvd_of_mod_eq {m : ℕ} (hm : 0 < m) {s : ℕ → ℤ}
    (hs : IsFibonacciLike s) {a d n : ℕ} (hd : rankOfApparition m ∣ d)
    (ha : (m : ℤ) ∣ s a) (hn : n % d = a % d) : (m : ℤ) ∣ s n := by
  rcases le_total a n with h | h
  · have hdvd : d ∣ n - a := (Nat.modEq_iff_dvd' h).mp hn.symm
    have hfib : m ∣ Nat.fib (n - a) :=
      (dvd_fib_iff_rankOfApparition_dvd hm _).mpr (hd.trans hdvd)
    have hgoal : (m : ℤ) ∣ s (a + (n - a)) := hs.dvd_add_of_dvd hfib ha
    rwa [show a + (n - a) = n from by omega] at hgoal
  · have hdvd : d ∣ a - n := (Nat.modEq_iff_dvd' h).mp hn
    have hfib : m ∣ Nat.fib (a - n) :=
      (dvd_fib_iff_rankOfApparition_dvd hm _).mpr (hd.trans hdvd)
    have ha' : (m : ℤ) ∣ s (n + (a - n)) := by rwa [show n + (a - n) = a from by omega]
    exact hs.dvd_of_dvd_add hfib ha'

/-- **The covering-layer interface.**  `IsFibonacciLike.dvd_of_mod_eq`
    packaged as the hypothesis shape a covering argument consumes:
    `∀ n, n % d = a % d → (m : ℤ) ∣ s n`, i.e. "`m` divides `s` on the
    whole class `a (mod d)`".  Supplying this for every class of a
    covering system is what forces a fixed divisor on the whole
    sequence. -/
theorem IsFibonacciLike.forall_mod_eq_dvd {m : ℕ} (hm : 0 < m) {s : ℕ → ℤ}
    (hs : IsFibonacciLike s) {a d : ℕ} (hd : rankOfApparition m ∣ d)
    (ha : (m : ℤ) ∣ s a) : ∀ n, n % d = a % d → (m : ℤ) ∣ s n :=
  fun _ hn => hs.dvd_of_mod_eq hm hd ha hn

-- ════════════════════════════════════════════════════════════════════
-- §6 NON-DEGENERACY
-- ════════════════════════════════════════════════════════════════════

/-- If `p` divides two consecutive terms of a Fibonacci-like sequence
    then it divides the initial pair — run the recurrence backwards,
    `s n = s (n+2) - s (n+1)`.  Contrapositively, a sequence whose
    initial pair is not both divisible by `p` never has two consecutive
    terms divisible by `p`. -/
theorem IsFibonacciLike.dvd_head_of_dvd_succ {p : ℕ} {s : ℕ → ℤ} (hs : IsFibonacciLike s) :
    ∀ n, (p : ℤ) ∣ s n → (p : ℤ) ∣ s (n + 1) → (p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1 := by
  intro n
  induction n with
  | zero => intro h0 h1; exact ⟨h0, h1⟩
  | succ n ih =>
    intro h1 h2
    have h2' : (p : ℤ) ∣ s (n + 2) := h2
    have hn : (p : ℤ) ∣ s n := by
      have heq : s n = s (n + 2) - s (n + 1) := by rw [hs n]; ring
      rw [heq]
      exact dvd_sub h2' h1
    exact ih hn h1

/-- **The non-degeneracy step.**  Under the hypothesis that `p` does not
    divide both `s 0` and `s 1`, no two consecutive terms are both
    divisible by `p`.  Without it a Fibonacci-like sequence can be
    divisible by `p` everywhere (take `s = 0`), and then its zero set is
    all of `ℕ`, which is not a class modulo `α(p) ≥ 3` — see the
    negative control in §9. -/
theorem IsFibonacciLike.not_dvd_succ_of_dvd {p : ℕ} {s : ℕ → ℤ} (hs : IsFibonacciLike s)
    (hnd : ¬ ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1)) {n : ℕ} (h : (p : ℤ) ∣ s n) :
    ¬ (p : ℤ) ∣ s (n + 1) :=
  fun h' => hnd (hs.dvd_head_of_dvd_succ n h h')

/-- Coprime initial terms give the non-degeneracy hypothesis at every
    `p > 1` at once.  Wilf's primefree sequence A083216 satisfies
    `gcd (a 0) (a 1) = 1`, so this is the form in which the hypothesis
    will be discharged there. -/
theorem not_dvd_zero_and_one_of_isCoprime {p : ℕ} (hp : 1 < p) {s : ℕ → ℤ}
    (h : IsCoprime (s 0) (s 1)) : ¬ ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1) := by
  rintro ⟨h0, h1⟩
  rcases Int.isUnit_iff.mp (h.isUnit_of_dvd' h0 h1) with heq | heq <;> omega

-- ════════════════════════════════════════════════════════════════════
-- §7 THE ZERO SET IS EMPTY OR ONE CLASS MOD α(p)
-- ════════════════════════════════════════════════════════════════════

/-- The gap between two indices at which a prime `p` divides a
    Fibonacci-like sequence is a multiple of `α(p)`.  Here primality is
    genuinely used: the shift identity gives `p ∣ s (a+1) · F k`, and
    non-degeneracy rules out `p ∣ s (a+1)`, so `p ∣ F k` needs `p`
    prime. -/
theorem IsFibonacciLike.rankOfApparition_dvd {p : ℕ} (hp : p.Prime) {s : ℕ → ℤ}
    (hs : IsFibonacciLike s) (hnd : ¬ ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1)) {a k : ℕ}
    (ha : (p : ℤ) ∣ s a) (hak : (p : ℤ) ∣ s (a + k)) : rankOfApparition p ∣ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact dvd_zero _
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show a + (j + 1) = a + j + 1 from rfl, hs.apply_add a j] at hak
    have hmul : (p : ℤ) ∣ s (a + 1) * Nat.fib (j + 1) := by
      have hsub := dvd_sub hak (ha.mul_right ((Nat.fib j : ℤ)))
      simpa using hsub
    have hns : ¬ (p : ℤ) ∣ s (a + 1) := hs.not_dvd_succ_of_dvd hnd ha
    have hfib : (p : ℤ) ∣ (Nat.fib (j + 1) : ℤ) :=
      (Int.Prime.dvd_mul' hp hmul).resolve_left hns
    exact (dvd_fib_iff_rankOfApparition_dvd hp.pos _).mp (Int.natCast_dvd_natCast.mp hfib)

/-- **The zero set, relative to one of its members.**  For a prime `p`,
    a Fibonacci-like `s` not divisible by `p` at both initial terms, and
    a known index `a` with `p ∣ s a`:

        `p ∣ s n  ↔  n % α(p) = a % α(p)`.

    So the zero set is exactly the residue class of `a` modulo the rank
    of apparition — not modulo the Pisano period, which is a strictly
    larger modulus for most primes. -/
theorem IsFibonacciLike.dvd_iff_mod_eq {p : ℕ} (hp : p.Prime) {s : ℕ → ℤ}
    (hs : IsFibonacciLike s) (hnd : ¬ ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1)) {a : ℕ}
    (ha : (p : ℤ) ∣ s a) (n : ℕ) :
    (p : ℤ) ∣ s n ↔ n % rankOfApparition p = a % rankOfApparition p := by
  constructor
  · intro hn
    rcases le_total a n with h | h
    · have hak : (p : ℤ) ∣ s (a + (n - a)) := by rwa [show a + (n - a) = n from by omega]
      exact ((Nat.modEq_iff_dvd' h).mpr (hs.rankOfApparition_dvd hp hnd ha hak)).symm
    · have hak : (p : ℤ) ∣ s (n + (a - n)) := by rwa [show n + (a - n) = a from by omega]
      exact (Nat.modEq_iff_dvd' h).mpr (hs.rankOfApparition_dvd hp hnd hn hak)
  · intro h
    exact hs.dvd_of_mod_eq hp.pos dvd_rfl ha h

/-- **THE TRANSPORT THEOREM.**  For a prime `p` and a Fibonacci-like
    `s : ℕ → ℤ` whose initial pair is not both divisible by `p`, the
    zero set of `s` modulo `p` is either empty or exactly one residue
    class modulo the rank of apparition `α(p)`:

        `{n | (p : ℤ) ∣ s n} = ∅  ∨
           ∃ a < α(p), {n | (p : ℤ) ∣ s n} = {n | n % α(p) = a}`.

    Both branches occur (§8) and both hypotheses are load-bearing (§9).
    This is the structural fact behind the covering certificates for
    Fibonacci-like primefree sequences: a class in such a certificate is
    forced to have modulus a multiple of `α(p)`, and never needs the
    Pisano period. -/
theorem IsFibonacciLike.setOf_dvd_eq_empty_or_residueClass {p : ℕ} (hp : p.Prime)
    {s : ℕ → ℤ} (hs : IsFibonacciLike s) (hnd : ¬ ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1)) :
    {n : ℕ | (p : ℤ) ∣ s n} = ∅ ∨
      ∃ a < rankOfApparition p,
        {n : ℕ | (p : ℤ) ∣ s n} = {n : ℕ | n % rankOfApparition p = a} := by
  rcases Set.eq_empty_or_nonempty {n : ℕ | (p : ℤ) ∣ s n} with hempty | ⟨a, ha⟩
  · exact Or.inl hempty
  · refine Or.inr ⟨a % rankOfApparition p, Nat.mod_lt _ (rankOfApparition_pos hp.pos), ?_⟩
    ext n
    exact hs.dvd_iff_mod_eq hp hnd ha n

-- ════════════════════════════════════════════════════════════════════
-- §8 SATISFIABILITY — BOTH BRANCHES OF §7 ARE INHABITED
-- ════════════════════════════════════════════════════════════════════

-- A disjunction is cheap to prove and cheap to make vacuous: `Or.inl`
-- alone would discharge §7 if the empty branch were the only reachable
-- one, and the theorem would then say nothing about residue classes.
-- This section instantiates every hypothesis of §7 jointly at concrete
-- models landing in each branch.

/-- The **Lucas numbers** `L n = 2 · F (n+1) − F n`, i.e.
    2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, … — OEIS A000032,
    "Lucas numbers beginning at 2: `L(n) = L(n-1) + L(n-2)`, `L(0) = 2`,
    `L(1) = 1`".  This is the standard Fibonacci-like sequence that is
    not a scalar multiple of `Nat.fib`, and it supplies both §8
    witnesses: `{n | 5 ∣ L n}` is empty
    (`setOf_dvd_lucas_five_eq_empty`) while `{n | 3 ∣ L n}` is the class
    `2 mod α(3) = 4` (`setOf_dvd_lucas_three`) — a class with *nonzero*
    base, which `Nat.fib` itself can never exhibit since `F 0 = 0` puts
    `0` in every one of its zero sets. -/
def lucas (n : ℕ) : ℤ := 2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ)

-- Ground checks for `lucas` against A000032 (2, 1, 3, 4, 7, …, 47).
example : lucas 0 = 2 := by decide
example : lucas 1 = 1 := by decide
example : lucas 2 = 3 := by decide
example : lucas 4 = 7 := by decide
example : lucas 8 = 47 := by decide

/-- The Lucas numbers satisfy the Fibonacci recurrence. -/
theorem isFibonacciLike_lucas : IsFibonacciLike lucas := by
  intro n
  simp only [lucas]
  push_cast [Nat.fib_add_two]
  ring

/-- `α(2) = 3` (OEIS A001177 at `n = 2`), in named form so §9 can cite
    it.  `F 1 = F 2 = 1` and `F 3 = 2`. -/
theorem rankOfApparition_two : rankOfApparition 2 = 3 :=
  rankOfApparition_eq_of (by norm_num) (by decide) (by decide)

/-- `α(3) = 4` (OEIS A001177 at `n = 3`), the first of the tuples the
    header records, `(p, α, π) = (3, 4, 8)`.  `F 4 = 3`. -/
theorem rankOfApparition_three : rankOfApparition 3 = 4 :=
  rankOfApparition_eq_of (by norm_num) (by decide) (by decide)

/-- `α(4) = 6` (OEIS A001177 at `n = 4`).  `4` is composite; this is the
    modulus the §9 primality control runs at.  `F 6 = 8`. -/
theorem rankOfApparition_four : rankOfApparition 4 = 6 :=
  rankOfApparition_eq_of (by norm_num) (by decide) (by decide)

/-- `α(5) = 5` (OEIS A001177 at `n = 5`), matching the header's
    `(p, α, π) = (5, 5, 20)`.  `F 5 = 5`. -/
theorem rankOfApparition_five : rankOfApparition 5 = 5 :=
  rankOfApparition_eq_of (by norm_num) (by decide) (by decide)

/-- **One period decides the branch.**  If `m` divides no term of `s` at
    any index below `α(m)`, then it divides no term at all.  This is
    what makes the empty branch of §7 checkable by `decide` at a
    concrete `m`: only the `α(m)` indices `0, …, α(m) - 1` need testing,
    never the whole sequence.

    Neither primality of `m` nor non-degeneracy of `s` is needed — only
    `0 < m`, to keep `α(m)` off its junk value.  The proof folds an
    arbitrary index `n` down to `n % α(m)` using §5. -/
theorem IsFibonacciLike.setOf_dvd_eq_empty_of_forall_lt {m : ℕ} (hm : 0 < m) {s : ℕ → ℤ}
    (hs : IsFibonacciLike s) (h : ∀ a < rankOfApparition m, ¬ (m : ℤ) ∣ s a) :
    {n : ℕ | (m : ℤ) ∣ s n} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun n hn => ?_
  have hlt : n % rankOfApparition m < rankOfApparition m :=
    Nat.mod_lt _ (rankOfApparition_pos hm)
  refine h _ hlt ?_
  exact hs.dvd_of_mod_eq hm dvd_rfl hn (Nat.mod_mod_of_dvd n dvd_rfl)

/-- **The empty branch is inhabited.**  No Lucas number is divisible by
    `5`: mod `5` the Lucas numbers cycle `2, 1, 3, 4, 2, 1, 3, 4, …`
    with period `4`, never hitting `0`.  Since `α(5) = 5`, checking the
    five indices `0, 1, 2, 3, 4` settles it. -/
theorem setOf_dvd_lucas_five_eq_empty : {n : ℕ | (5 : ℤ) ∣ lucas n} = ∅ := by
  have h := isFibonacciLike_lucas.setOf_dvd_eq_empty_of_forall_lt (m := 5) (by norm_num)
    (by rw [rankOfApparition_five]; decide)
  simpa using h

/-- **§7's first disjunct is not vacuous.**  Every hypothesis of
    `IsFibonacciLike.setOf_dvd_eq_empty_or_residueClass` is satisfied
    jointly — at `p = 5`, `s = lucas` — with the zero set empty. -/
theorem exists_isFibonacciLike_setOf_dvd_eq_empty :
    ∃ (p : ℕ) (s : ℕ → ℤ), p.Prime ∧ IsFibonacciLike s ∧
      ¬ ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1) ∧ {n : ℕ | (p : ℤ) ∣ s n} = ∅ := by
  refine ⟨5, lucas, by norm_num, isFibonacciLike_lucas, by decide, ?_⟩
  simpa using setOf_dvd_lucas_five_eq_empty

/-- The Lucas zero set at `p = 3` is the class `2 mod 4`: mod `3` the
    Lucas numbers cycle `2, 1, 0, 1, 1, 2, 0, 2, …`, vanishing exactly
    at `n ≡ 2 (mod α(3)) = 2 (mod 4)`. -/
theorem setOf_dvd_lucas_three : {n : ℕ | (3 : ℤ) ∣ lucas n} = {n : ℕ | n % 4 = 2} := by
  have hp : Nat.Prime 3 := by norm_num
  have hnd : ¬ (((3 : ℕ) : ℤ) ∣ lucas 0 ∧ ((3 : ℕ) : ℤ) ∣ lucas 1) := by decide
  have ha : ((3 : ℕ) : ℤ) ∣ lucas 2 := by decide
  ext n
  have hiff := isFibonacciLike_lucas.dvd_iff_mod_eq hp hnd ha n
  rw [rankOfApparition_three] at hiff
  simpa using hiff

/-- The Fibonacci zero set at `p = 3` is the class `0 mod 4`.  Here §3
    alone suffices: `3 ∣ F n ↔ α(3) ∣ n ↔ 4 ∣ n`. -/
theorem setOf_dvd_fib_three :
    {n : ℕ | (3 : ℤ) ∣ (Nat.fib n : ℤ)} = {n : ℕ | n % 4 = 0} := by
  ext n
  simp only [Set.mem_ofPred_eq]
  rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast,
    dvd_fib_iff_rankOfApparition_dvd (by norm_num) n, rankOfApparition_three,
    Nat.dvd_iff_mod_eq_zero]

/-- The base class of §7 depends on the sequence and not only on `p`: at
    the same prime `3` and the same modulus `α(3) = 4`, `Nat.fib` sits
    in the class `0` and `lucas` in the class `2`, so the two zero sets
    are distinct (indeed disjoint).  This rules out a reading of §7 in
    which the class is always the one containing `0`. -/
theorem setOf_dvd_fib_three_ne_setOf_dvd_lucas_three :
    {n : ℕ | (3 : ℤ) ∣ (Nat.fib n : ℤ)} ≠ {n : ℕ | (3 : ℤ) ∣ lucas n} := by
  intro h
  have h0 : (0 : ℕ) ∈ {n : ℕ | (3 : ℤ) ∣ (Nat.fib n : ℤ)} := by decide
  rw [h] at h0
  exact absurd h0 (by decide)

/-- **§7's second disjunct is not vacuous.**  Every hypothesis is
    satisfied jointly — at `p = 3`, `s = lucas` — with the zero set a
    genuine, nonempty residue class at the nonzero base `a = 2`.  The
    `a ≠ 0` conjunct is part of the statement on purpose: `a` is
    existentially bound, so without it the theorem would also be
    witnessed by `Nat.fib` at `a = 0` and the word "nonzero" would live
    only in this docstring.  `setOf_dvd_fib_three_ne_setOf_dvd_lucas_three`
    below shows the two classes are genuinely different. -/
theorem exists_isFibonacciLike_setOf_dvd_eq_residueClass :
    ∃ (p : ℕ) (s : ℕ → ℤ) (a : ℕ), p.Prime ∧ IsFibonacciLike s ∧
      ¬ ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1) ∧ a < rankOfApparition p ∧ a ≠ 0 ∧
      {n : ℕ | (p : ℤ) ∣ s n} = {n : ℕ | n % rankOfApparition p = a} ∧
      {n : ℕ | (p : ℤ) ∣ s n}.Nonempty := by
  refine ⟨3, lucas, 2, by norm_num, isFibonacciLike_lucas, by decide, ?_, by norm_num,
    ?_, ?_⟩
  · rw [rankOfApparition_three]; norm_num
  · rw [rankOfApparition_three]
    simpa using setOf_dvd_lucas_three
  · exact ⟨2, by decide⟩

-- ════════════════════════════════════════════════════════════════════
-- §9 NEGATIVE CONTROLS — BOTH HYPOTHESES OF §7 ARE LOAD-BEARING
-- ════════════════════════════════════════════════════════════════════

-- Each control is the statement of §7 with one hypothesis deleted (and
-- explicitly negated), witnessed at a concrete model.  So each is a
-- refutation of the corresponding strengthening of §7, not a comment
-- about one.

/-- The zero set of `2 · F` modulo the composite `4` is `{n | 3 ∣ n}` —
    the multiples of `α(2) = 3`, because `4 ∣ 2 · F n ↔ 2 ∣ F n`.  Since
    `α(4) = 6`, that is the union of the *two* classes `0` and `3`
    modulo `α(4)`, not one.  This is precisely what §7 forbids for
    primes, and it is why the proof of §7 needs `Int.Prime.dvd_mul'`. -/
theorem setOf_dvd_two_mul_fib_four :
    {n : ℕ | (4 : ℤ) ∣ 2 * (Nat.fib n : ℤ)} = {n : ℕ | n % 3 = 0} := by
  ext n
  simp only [Set.mem_ofPred_eq]
  have hcast : ((4 : ℤ) ∣ 2 * (Nat.fib n : ℤ)) ↔ (2 ∣ Nat.fib n) := by
    rw [← Int.natCast_dvd_natCast (m := 2) (n := Nat.fib n)]
    push_cast
    omega
  rw [hcast, dvd_fib_iff_rankOfApparition_dvd (by norm_num) n, rankOfApparition_two,
    Nat.dvd_iff_mod_eq_zero]

/-- **Control (a): `hp : p.Prime` is load-bearing.**  Drop primality and
    §7 is false.  At the composite `m = 4` and `s = 2 · F` — which is
    Fibonacci-like and *does* satisfy the non-degeneracy hypothesis,
    since `4 ∤ s 1 = 2` — the zero set is neither empty nor a single
    residue class modulo `α(4) = 6`: it contains both `0` and `3`, whose
    residues mod `6` differ.  (`setOf_dvd_two_mul_fib_four` identifies
    it exactly, as `{n | 3 ∣ n}`.)

    So every hypothesis of §7 except primality holds here, and the
    conclusion fails; primality cannot be weakened to `0 < m`. -/
theorem exists_not_prime_setOf_dvd_ne_empty_and_ne_residueClass :
    ∃ (m : ℕ) (s : ℕ → ℤ), ¬ m.Prime ∧ 0 < m ∧ IsFibonacciLike s ∧
      ¬ ((m : ℤ) ∣ s 0 ∧ (m : ℤ) ∣ s 1) ∧
      ¬ ({n : ℕ | (m : ℤ) ∣ s n} = ∅ ∨
          ∃ a < rankOfApparition m,
            {n : ℕ | (m : ℤ) ∣ s n} = {n : ℕ | n % rankOfApparition m = a}) := by
  refine ⟨4, fun n => 2 * (Nat.fib n : ℤ), by norm_num, by norm_num,
    (fun n => by push_cast [Nat.fib_add_two]; ring), by decide, ?_⟩
  have h0 : (0 : ℕ) ∈ {n : ℕ | ((4 : ℕ) : ℤ) ∣ 2 * (Nat.fib n : ℤ)} := by decide
  have h3 : (3 : ℕ) ∈ {n : ℕ | ((4 : ℕ) : ℤ) ∣ 2 * (Nat.fib n : ℤ)} := by decide
  rw [rankOfApparition_four]
  rintro (hempty | ⟨a, -, hclass⟩)
  · rw [hempty] at h0
    exact h0
  · rw [hclass] at h0 h3
    simp only [Set.mem_ofPred_eq] at h0 h3
    omega

/-- **The degenerate case, positively.**  If `p` divides both initial
    terms of a Fibonacci-like sequence then it divides every term — the
    converse of §6's `IsFibonacciLike.dvd_head_of_dvd_succ`, run
    forwards.  Proved by carrying both consecutive divisibilities
    through a one-step induction. -/
theorem IsFibonacciLike.dvd_of_dvd_zero_of_dvd_one {p : ℕ} {s : ℕ → ℤ}
    (hs : IsFibonacciLike s) (h0 : (p : ℤ) ∣ s 0) (h1 : (p : ℤ) ∣ s 1) (n : ℕ) :
    (p : ℤ) ∣ s n := by
  have key : ∀ k, (p : ℤ) ∣ s k ∧ (p : ℤ) ∣ s (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show (p : ℤ) ∣ s (k + 2)
      rw [hs k]
      exact dvd_add ih.2 ih.1
  exact (key n).1

/-- Under degeneracy the zero set is all of `ℕ`. -/
theorem IsFibonacciLike.setOf_dvd_eq_univ {p : ℕ} {s : ℕ → ℤ} (hs : IsFibonacciLike s)
    (h0 : (p : ℤ) ∣ s 0) (h1 : (p : ℤ) ∣ s 1) : {n : ℕ | (p : ℤ) ∣ s n} = Set.univ :=
  Set.eq_univ_of_forall (hs.dvd_of_dvd_zero_of_dvd_one h0 h1)

/-- `Set.univ` is not a residue class modulo any `d > 1`: `0` and `1`
    would have to share a residue.  This is the step that turns "the
    degenerate zero set is everything" into an actual refutation of §7,
    and it is where `1 < d` is needed — modulo `d = 1` the single class
    `{n | n % 1 = 0}` *is* all of `ℕ`. -/
theorem univ_ne_setOf_mod_eq {d : ℕ} (hd : 1 < d) (a : ℕ) :
    (Set.univ : Set ℕ) ≠ {n : ℕ | n % d = a} := by
  intro h
  have hmem : ∀ n : ℕ, n % d = a := fun n => by
    have hn : n ∈ ({n : ℕ | n % d = a} : Set ℕ) := h ▸ Set.mem_univ n
    exact hn
  have h0 := hmem 0
  have h1 := hmem 1
  rw [Nat.zero_mod] at h0
  rw [Nat.mod_eq_of_lt hd] at h1
  omega

/-- **Control (b): `hnd` non-degeneracy is load-bearing.**  Drop it and
    §7 is false.  At the prime `p = 3` and `s = 3 · F` — Fibonacci-like,
    with `3 ∣ s 0 = 0` and `3 ∣ s 1 = 3`, so the deleted hypothesis is
    exactly what fails — the zero set is all of `ℕ`
    (`IsFibonacciLike.setOf_dvd_eq_univ`), which is neither empty nor a
    residue class modulo `α(3) = 4 > 1` (`univ_ne_setOf_mod_eq`).

    Note the witness is not the zero sequence: `3 · F` is unbounded and
    takes infinitely many distinct values, so the failure is not an
    artifact of a trivial model. -/
theorem exists_degenerate_setOf_dvd_ne_empty_and_ne_residueClass :
    ∃ (p : ℕ) (s : ℕ → ℤ), p.Prime ∧ IsFibonacciLike s ∧
      ((p : ℤ) ∣ s 0 ∧ (p : ℤ) ∣ s 1) ∧
      ¬ ({n : ℕ | (p : ℤ) ∣ s n} = ∅ ∨
          ∃ a < rankOfApparition p,
            {n : ℕ | (p : ℤ) ∣ s n} = {n : ℕ | n % rankOfApparition p = a}) := by
  refine ⟨3, fun n => 3 * (Nat.fib n : ℤ), by norm_num,
    (fun n => by push_cast [Nat.fib_add_two]; ring), ⟨by decide, by decide⟩, ?_⟩
  have huniv : {n : ℕ | ((3 : ℕ) : ℤ) ∣ 3 * (Nat.fib n : ℤ)} = Set.univ :=
    IsFibonacciLike.setOf_dvd_eq_univ (fun n => by push_cast [Nat.fib_add_two]; ring)
      (by decide) (by decide)
  rw [huniv, rankOfApparition_three]
  rintro (hempty | ⟨a, -, hclass⟩)
  · have hmem : (0 : ℕ) ∈ (∅ : Set ℕ) := hempty ▸ Set.mem_univ 0
    exact hmem
  · exact univ_ne_setOf_mod_eq (by norm_num) a hclass

-- ════════════════════════════════════════════════════════════════════
-- §10 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

-- The headline theorems, printed individually.

#print axioms dvd_fib_iff_rankOfApparition_dvd
#print axioms IsFibonacciLike.apply_add
#print axioms IsFibonacciLike.forall_mod_eq_dvd
#print axioms IsFibonacciLike.dvd_iff_mod_eq
#print axioms IsFibonacciLike.setOf_dvd_eq_empty_or_residueClass
#print axioms exists_isFibonacciLike_setOf_dvd_eq_empty
#print axioms exists_isFibonacciLike_setOf_dvd_eq_residueClass
#print axioms exists_not_prime_setOf_dvd_ne_empty_and_ne_residueClass
#print axioms exists_degenerate_setOf_dvd_ne_empty_and_ne_residueClass

/-
  A per-declaration `#print axioms` is a *report*, not a check: nothing
  fails if one of them prints an extra name, and nothing covers the
  declarations nobody thought to print.  The sweep below is the check.

  It matters that the check is an allowlist-*subset* test rather than a
  test for particular axiom names.  `native_decide` does not add
  `Lean.ofReduceBool`; it mints a fresh axiom per declaration, named
  after that declaration — measured here on this toolchain, a
  `native_decide` proof of `theorem viaNative` yields

      'viaNative' depends on axioms: [viaNative._native.native_decide.ax_1_1]

  so grepping for a fixed axiom name detects nothing.  Any such axiom
  fails the subset test below, whatever it is called.

  Scope, stated exactly: the sweep ranges over `env.constants.map₂`,
  the constants *this module* adds — the 44 enumerated declarations
  plus the compiler-generated auxiliaries (`_proof_*`, `match_*`,
  equation lemmas) they induce.  The enumeration is cross-checked
  against the sweep, so a declaration cannot escape by being forgotten,
  and `throwError` makes a violation a build failure rather than a log
  line.

  TWO LIMITS, both measured rather than assumed, neither closable from
  inside this file:

  (1) Lean does not retain `example`s in the environment, so the
      `example` ground checks in §1–§9 contribute no constant at all and
      are outside the sweep — a `native_decide` inside an `example`
      would be invisible to it.  Their tactics are in fact only
      `decide`, `norm_num`, `push_cast`, `ring`, `intro`, `rw` and
      `have`, all kernel-clean, and the cold build emits no warnings.

  (2) The sweep is POSITIONAL: `run_cmd` runs where it is written, so it
      sees only declarations above it.  Anything appended below §10
      passes silently — `sorry` would still warn, but `native_decide`
      would not.  Today nothing follows but `end Erdos.Covering`.  Add
      new declarations ABOVE this block, not below it.
-/

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  -- The enumerated public declarations of this file, §1 through §9.
  let enumerated : List Name :=
    [``fibPairShift, ``fibPairShift_apply, ``fibPairShift_pow_apply,
      ``exists_pos_dvd_fib, ``rankOfApparition, ``rankOfApparition_spec,
      ``rankOfApparition_pos, ``dvd_fib_rankOfApparition, ``rankOfApparition_le,
      ``rankOfApparition_eq_of, ``rankOfApparition_zero,
      ``dvd_fib_iff_rankOfApparition_dvd, ``IsFibonacciLike,
      ``IsFibonacciLike.apply_add_aux, ``IsFibonacciLike.apply_add,
      ``IsFibonacciLike.dvd_add_of_dvd, ``IsFibonacciLike.dvd_of_dvd_add,
      ``IsFibonacciLike.dvd_of_mod_eq, ``IsFibonacciLike.forall_mod_eq_dvd,
      ``IsFibonacciLike.dvd_head_of_dvd_succ,
      ``IsFibonacciLike.not_dvd_succ_of_dvd, ``not_dvd_zero_and_one_of_isCoprime,
      ``IsFibonacciLike.rankOfApparition_dvd, ``IsFibonacciLike.dvd_iff_mod_eq,
      ``IsFibonacciLike.setOf_dvd_eq_empty_or_residueClass, ``lucas,
      ``isFibonacciLike_lucas, ``rankOfApparition_two, ``rankOfApparition_three,
      ``rankOfApparition_four, ``rankOfApparition_five,
      ``IsFibonacciLike.setOf_dvd_eq_empty_of_forall_lt,
      ``setOf_dvd_lucas_five_eq_empty,
      ``exists_isFibonacciLike_setOf_dvd_eq_empty, ``setOf_dvd_lucas_three,
      ``setOf_dvd_fib_three, ``setOf_dvd_fib_three_ne_setOf_dvd_lucas_three,
      ``exists_isFibonacciLike_setOf_dvd_eq_residueClass,
      ``setOf_dvd_two_mul_fib_four,
      ``exists_not_prime_setOf_dvd_ne_empty_and_ne_residueClass,
      ``IsFibonacciLike.dvd_of_dvd_zero_of_dvd_one,
      ``IsFibonacciLike.setOf_dvd_eq_univ, ``univ_ne_setOf_mod_eq,
      ``exists_degenerate_setOf_dvd_ne_empty_and_ne_residueClass]
  let env ← getEnv
  -- (i) every constant this module adds must pass the allowlist, and
  --     this module must declare no axiom of its own.
  let mut sweptNames : Array Name := #[]
  for (declName, info) in env.constants.map₂.toList do
    sweptNames := sweptNames.push declName
    if let .axiomInfo _ := info then
      throwError "§10 FAILED: this module declares an axiom, {declName}"
    for ax in ← Lean.collectAxioms declName do
      unless allowed.contains ax do
        throwError "§10 FAILED: {declName} depends on the axiom {ax}"
  -- (ii) the enumeration must be covered by the sweep, so that the
  --      sweep cannot pass by having quietly ranged over nothing.
  for declName in enumerated do
    unless sweptNames.contains declName do
      throwError "§10 FAILED: enumerated declaration {declName} was not swept"
  logInfo m!"§10 axiom audit PASSED: {enumerated.length} enumerated declarations, \
    {sweptNames.size} module constants swept (enumerated + compiler-generated \
    auxiliaries); every one has axioms ⊆ \{propext, Classical.choice, Quot.sound}; \
    this module declares no axiom."

end Erdos.Covering
