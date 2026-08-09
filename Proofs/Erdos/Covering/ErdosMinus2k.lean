/-
  Erdos/Covering/ErdosMinus2k — OEIS A039669 / erdosproblems.com #1142:
  the positive integers `m` for which `m - 2 ^ k` is prime for every `k`
  with `1 < 2 ^ k < m`.

  DEF-OWNER module for the predicate; `Erdos.Covering.ErdosRows`
  (OEIS A089654) consumes it.

  GROUND TRUTH PINNING (fetched live 2026-07-30).

  OEIS A039669, name: "Positive numbers m such that m - 2^k is a prime
  for all k > 0 with 2^k < m." Terms: 4, 7, 15, 21, 45, 75, 105.
  Keywords: nonn,hard,more. Comments: "Erdős conjectures that these are
  the only values of n with this property."; "No other terms below
  2^120. - Max Alekseyev, Dec 08 2011"; "Presumably, Mientka and
  Weitzenkamp are including 1 and 2. - Robert Israel, Dec 23 2015".

  erdosproblems.com #1142, OPEN: "Are there infinitely many n (or any
  n > 105) such that n - 2^k is prime for all 1 < 2^k < n?" Published
  record: no other such n ≤ 2^44 (Mientka–Weitzenkamp 1969); and the
  number of n ≤ N is < exp(-c·log log log N/log log N · log N)·N
  (Vaughan 1973, via Montgomery's sieve). 2^120 above is the citable
  search bound; a 2^128 figure circulating in our notes traces only to
  an unrefereed 2026-05-10 forum comment on #1142 using probabilistic
  primality, and is not cited here (Formalize/A039669-erdos-minus-2k.md).

  THE VACUITY TRAP, AND WHY `2 < m` IS PART OF THE PREDICATE.
  The raw body `∀ k, 0 < k → 2 ^ k < m → (m - 2 ^ k).Prime` is satisfied
  *vacuously* at m = 0, 1, 2: no k ≥ 1 has 2 ^ k < m. The full solution
  set of the raw body below 200000 is {0, 1, 2, 4, 7, 15, 21, 45, 75,
  105} (Sage, 2026-07-30) — which is why the OEIS listing starts at 4,
  and what Robert Israel's comment above is about. A Lean statement of
  the conjecture without the guard is FALSE, not merely vacuous. The
  guard is folded into `IsAllPrimeMinusPow`; §2 exhibits the three
  degenerate solutions of the unguarded body `AllPrimeMinusPow`
  explicitly, and proves the quantified domain is nonempty above the
  guard.

  PRIOR ART. The statement has been formalized before: the repository
  google-deepmind/formal-conjectures (Apache 2.0) contains
  `FormalConjectures/ErdosProblems/1142.lean` with

      def Erdos1142Prop (n : ℕ) : Prop :=
        2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

  which `IsAllPrimeMinusPow` reproduces on the nose, so the two are
  visibly the same object (`isAllPrimeMinusPow_def` records the
  unfolding). There the conjecture is stated in the infinitude form and
  is `sorry`'d; the Mientka–Weitzenkamp window
  `{n | n ≤ 2 ^ 44 ∧ Erdos1142Prop n} = {4, 7, 15, 21, 45, 75, 105}` is
  also `sorry`'d; the seven membership certificates are proved. Nothing
  here claims priority on the statement, on the guard, or on the
  certificates.

  WHAT IS NEW HERE: the finite completeness window of §6 is *proved*,
  not assumed — `{m | m ≤ 10 ^ 9 ∧ IsAllPrimeMinusPow m} = {4, 7, 15,
  21, 45, 75, 105}` is checked by the Lean kernel. It is the same shape
  as the archived `2 ^ 44` window, at a bound the kernel can actually
  reach. Getting there needs the §5 covering-congruence reduction, not
  brute force: a naive kernel sweep over all `m ≤ N` dies around
  `N = 10 ^ 4` (the kernel costs ≈ 0.2 ms and ≈ 60 kB per step of a
  decidable bounded quantifier, so both time and memory are linear in
  the number of candidates examined). The reduction cuts the `10 ^ 9`
  search to 3721 candidates, which the kernel clears in well under a
  minute.

  CONTENTS.
    § 1 `AllPrimeMinusPow` (raw body), `IsAllPrimeMinusPow` (guarded
        predicate = A039669 membership), the unfolding lemma, the
        finite-range reformulation `allPrimeMinusPow_iff_forall_lt`, and
        the `Decidable` instances it powers.
    § 2 Degeneracy disclosure: the three vacuous solutions of the raw
        body, their exclusion by the guard, and `exists_pow_lt_of_two_lt`
        — above the guard the domain of the `∀ k` is nonempty, so the
        predicate has content at every m the conjecture is about.
    § 3 The seven membership certificates, kernel-checked.
    § 4 Negative controls: 3, 5, 6 and 106 fail, each with its witness k.
    § 5 The covering-congruence reduction. If `2` is a primitive root
        mod `q` then the exponents `k = 1, …, q - 1` make `2 ^ k` run
        through every nonzero residue mod `q`, so once `m` is past
        `2 ^ (q-1) + q` the primality of all the `m - 2 ^ k` forces
        `q ∣ m`. Applied at `q = 3, 5, 11, 13, 19, 29` (and `q = 2` for
        parity) this pins `m` to the single residue class `1181895`
        mod `2363790` above `2 ^ 28 + 29`, cutting the `10 ^ 9` search
        to 3721 candidates. `q = 7, 17, 23, 31` are unusable: `2` is not
        a primitive root there.
    § 6 The finite completeness window at N = 10 ^ 9, kernel-checked, in
        both the implication form and the set-equality form.
    § 7 ARCHIVED (the file's single intended `sorry`): `erdos_1142`, the
        Erdős completeness conjecture. Two corollaries are derived from
        it with no new `sorry` (`sorryAx`-dependent through it).
    § 8 Axiom audit.

  ROUTE for the archived `sorry`. Open (erdosproblems #1142). The
  standard machinery for statements of this shape is covering
  congruences — Erdős 1950, "On integers of the form 2^k + p and some
  related problems" — which is what `Erdos.Covering.Basic` provides
  (`IsCoveringSystem`, `isCoveringSystem_erdosSystem`, and the decidable
  characterization `isCoveringSystem_iff`); §5 here is a small instance
  of exactly that idea. The complementary Erdős-1950 statement (a
  covering system forces a whole arithmetic progression of `n` to have
  *some* `n - 2^k` composite) is the subject of the sibling module
  `Erdos.Covering.NotTwoPowerPlusPrime`. The two are not the same
  problem: covering congruences produce infinitely many *counterexamples*
  and so cannot by themselves settle a *finiteness* claim, which is why
  #1142 is open while Erdős 1950 is a theorem. Indeed §5's reduction
  extends to every prime `q` with `2` a primitive root mod `q`, and
  Artin's conjecture (also open) is what would make that supply
  infinite.

  Axiom audit (2026-07-31, Lean 4.33.0-rc1, 73 declarations):
  `erdos_1142` and its two
  corollaries report `sorryAx`; every other declaration reports a subset
  of {propext, Classical.choice, Quot.sound}. No `native_decide`, no
  `axiom`, no `@[csimp]`/`@[implemented_by]`/`@[extern]`. The
  `decide +kernel` uses below are ordinary kernel reduction: the trust
  surface is exactly that of `decide`, only the (much slower)
  elaborator-side replay of the same reduction is skipped.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 THE PREDICATE
-- ════════════════════════════════════════════════════════════════════

/-- The **raw body** of the A039669 membership condition: `m - 2 ^ k` is
prime for every `k ≥ 1` with `2 ^ k < m`.

The `ℕ` subtraction `m - 2 ^ k` is totalized (it returns `0` once
`m ≤ 2 ^ k`), so without a guard the statement would be about the junk
value. The guard is the hypothesis `2 ^ k < m` — the OEIS entry's own
range condition — which forces `0 < m - 2 ^ k`; no `k` outside that
range is constrained.

This predicate is *vacuously true* at `m = 0, 1, 2` (§2). The sequence's
actual membership condition is `IsAllPrimeMinusPow`. -/
def AllPrimeMinusPow (m : ℕ) : Prop :=
  ∀ k, 0 < k → 2 ^ k < m → Nat.Prime (m - 2 ^ k)

/-- **Membership in OEIS A039669**: `2 < m`, and `m - 2 ^ k` is prime for
every `k` with `1 < 2 ^ k < m`. This is the predicate of erdosproblems
#1142, and is definitionally the `Erdos1142Prop` of
google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/1142.lean` (module header);
`isAllPrimeMinusPow_def` records the unfolding.

The guard `2 < m` is not cosmetic: without it the three vacuous
solutions `m = 0, 1, 2` of `AllPrimeMinusPow` falsify the completeness
conjecture outright (§2). -/
def IsAllPrimeMinusPow (m : ℕ) : Prop :=
  2 < m ∧ AllPrimeMinusPow m

/-- `IsAllPrimeMinusPow` spelled out — the exact shape of `Erdos1142Prop`
in google-deepmind/formal-conjectures. -/
theorem isAllPrimeMinusPow_def (m : ℕ) :
    IsAllPrimeMinusPow m ↔ 2 < m ∧ ∀ k, 0 < k → 2 ^ k < m → Nat.Prime (m - 2 ^ k) :=
  Iff.rfl

/-- The unbounded `∀ k` collapses to a finite range: if `m ≤ 2 ^ B` then
only exponents `k < B` can satisfy `2 ^ k < m`. This is what makes the
predicate kernel-decidable. -/
theorem allPrimeMinusPow_iff_forall_lt {m B : ℕ} (hB : m ≤ 2 ^ B) :
    AllPrimeMinusPow m ↔ ∀ k ∈ Finset.Ico 1 B, 2 ^ k < m → Nat.Prime (m - 2 ^ k) := by
  constructor
  · intro h k hk hlt
    exact h k (Finset.mem_Ico.mp hk).1 hlt
  · intro h k hk1 hlt
    have hkB : k < B :=
      (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp (lt_of_lt_of_le hlt hB)
    exact h k (Finset.mem_Ico.mpr ⟨hk1, hkB⟩) hlt

/-- Decision procedure for `AllPrimeMinusPow`, at the crude but always
valid bound `B = m` (`m < 2 ^ m`). It runs `m` exponent tests, so it is
practical only for small `m`; at a fixed `m` prefer
`allPrimeMinusPow_iff_forall_lt` at the tight `B ≈ log₂ m`, as §3 does. -/
instance decidableAllPrimeMinusPow : DecidablePred AllPrimeMinusPow := fun m =>
  decidable_of_iff _
    (allPrimeMinusPow_iff_forall_lt (m := m) (B := m) Nat.lt_two_pow_self.le).symm

instance decidableIsAllPrimeMinusPow : DecidablePred IsAllPrimeMinusPow := fun m =>
  inferInstanceAs (Decidable (2 < m ∧ AllPrimeMinusPow m))

-- ════════════════════════════════════════════════════════════════════
-- §2 DEGENERACY DISCLOSURE
-- ════════════════════════════════════════════════════════════════════

/-- Below the guard the raw body is **vacuously true**: for `m ≤ 2` no
`k ≥ 1` satisfies `2 ^ k < m`, since `2 = 2 ^ 1 ≤ 2 ^ k`. -/
theorem allPrimeMinusPow_of_le_two {m : ℕ} (hm : m ≤ 2) : AllPrimeMinusPow m := by
  intro k hk hlt
  have h2 : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

-- The three vacuous solutions of the raw body, spelled out. They are
-- exactly why the OEIS listing starts at 4 (cf. Robert Israel's comment)
-- and why `IsAllPrimeMinusPow` carries a guard.
example : AllPrimeMinusPow 0 := allPrimeMinusPow_of_le_two (by norm_num)
example : AllPrimeMinusPow 1 := allPrimeMinusPow_of_le_two (by norm_num)
example : AllPrimeMinusPow 2 := allPrimeMinusPow_of_le_two (by norm_num)

-- … and the guard is what removes them from the sequence.
example : ¬ IsAllPrimeMinusPow 0 := fun h => absurd h.1 (by norm_num)
example : ¬ IsAllPrimeMinusPow 1 := fun h => absurd h.1 (by norm_num)
example : ¬ IsAllPrimeMinusPow 2 := fun h => absurd h.1 (by norm_num)

/-- **Nonvacuity above the guard.** Past the guard the quantified domain
of `AllPrimeMinusPow` is never empty: `k = 1` always qualifies. So
`IsAllPrimeMinusPow m` constrains at least one prime at every `m` the
conjecture is about. -/
theorem exists_pow_lt_of_two_lt {m : ℕ} (hm : 2 < m) : ∃ k, 0 < k ∧ 2 ^ k < m :=
  ⟨1, Nat.one_pos, by simpa using hm⟩

/-- The first of those constraints, made explicit: a term of A039669 is
two more than a prime. (The OEIS entry records the resulting prime list
`2, 5, 13, 19, 43, 73, 103` in David Morales Marciel's comment.) -/
theorem prime_sub_two_of_isAllPrimeMinusPow {m : ℕ} (h : IsAllPrimeMinusPow m) :
    Nat.Prime (m - 2) := by
  have h1 := h.2 1 Nat.one_pos (by simpa using h.1)
  simpa using h1

-- ════════════════════════════════════════════════════════════════════
-- §3 THE SEVEN MEMBERSHIP CERTIFICATES
-- ════════════════════════════════════════════════════════════════════

/-- A039669(1) = 4: `4 - 2 = 2` is prime. -/
theorem isAllPrimeMinusPow_4 : IsAllPrimeMinusPow 4 :=
  ⟨by norm_num, (allPrimeMinusPow_iff_forall_lt (B := 2) (by norm_num)).mpr (by decide)⟩

/-- A039669(2) = 7: `5, 3` are prime. -/
theorem isAllPrimeMinusPow_7 : IsAllPrimeMinusPow 7 :=
  ⟨by norm_num, (allPrimeMinusPow_iff_forall_lt (B := 3) (by norm_num)).mpr (by decide)⟩

/-- A039669(3) = 15: `13, 11, 7` are prime. -/
theorem isAllPrimeMinusPow_15 : IsAllPrimeMinusPow 15 :=
  ⟨by norm_num, (allPrimeMinusPow_iff_forall_lt (B := 4) (by norm_num)).mpr (by decide)⟩

/-- A039669(4) = 21: `19, 17, 13, 5` are prime. -/
theorem isAllPrimeMinusPow_21 : IsAllPrimeMinusPow 21 :=
  ⟨by norm_num, (allPrimeMinusPow_iff_forall_lt (B := 5) (by norm_num)).mpr (by decide)⟩

/-- A039669(5) = 45: `43, 41, 37, 29, 13` are prime. -/
theorem isAllPrimeMinusPow_45 : IsAllPrimeMinusPow 45 :=
  ⟨by norm_num, (allPrimeMinusPow_iff_forall_lt (B := 6) (by norm_num)).mpr (by decide)⟩

/-- A039669(6) = 75: `73, 71, 67, 59, 43, 11` are prime. -/
theorem isAllPrimeMinusPow_75 : IsAllPrimeMinusPow 75 :=
  ⟨by norm_num, (allPrimeMinusPow_iff_forall_lt (B := 7) (by norm_num)).mpr (by decide)⟩

/-- A039669(7) = 105: `103, 101, 97, 89, 73, 41` are prime. The largest
known term; #1142 asks whether any larger one exists. -/
theorem isAllPrimeMinusPow_105 : IsAllPrimeMinusPow 105 :=
  ⟨by norm_num, (allPrimeMinusPow_iff_forall_lt (B := 7) (by norm_num)).mpr (by decide)⟩

-- ════════════════════════════════════════════════════════════════════
-- §4 NEGATIVE CONTROLS
-- ════════════════════════════════════════════════════════════════════

/-- `3` fails at `k = 1`: `3 - 2 = 1` is not prime. Note `3` is the
smallest `m` at which the raw body says anything at all (§2). -/
theorem not_isAllPrimeMinusPow_3 : ¬ IsAllPrimeMinusPow 3 := fun h => by
  have h1 : Nat.Prime (3 - 2 ^ 1) := h.2 1 Nat.one_pos (by norm_num)
  norm_num at h1

/-- `5` fails at `k = 2`: `5 - 4 = 1` is not prime — though it passes at
`k = 1` (`5 - 2 = 3`), so the failure is due to a later exponent. -/
theorem not_isAllPrimeMinusPow_5 : ¬ IsAllPrimeMinusPow 5 := fun h => by
  have h1 : Nat.Prime (5 - 2 ^ 2) := h.2 2 (by norm_num) (by norm_num)
  norm_num at h1

/-- `6` fails at `k = 1`: `6 - 2 = 4` is composite. -/
theorem not_isAllPrimeMinusPow_6 : ¬ IsAllPrimeMinusPow 6 := fun h => by
  have h1 : Nat.Prime (6 - 2 ^ 1) := h.2 1 Nat.one_pos (by norm_num)
  norm_num at h1

/-- `106` fails at `k = 1`: `106 - 2 = 104 = 2³ · 13`. The first
non-member above the largest known term. -/
theorem not_isAllPrimeMinusPow_106 : ¬ IsAllPrimeMinusPow 106 := fun h => by
  have h1 : Nat.Prime (106 - 2 ^ 1) := h.2 1 Nat.one_pos (by norm_num)
  norm_num at h1

-- ════════════════════════════════════════════════════════════════════
-- §5 THE COVERING-CONGRUENCE REDUCTION
-- ════════════════════════════════════════════════════════════════════

section Reduction

/-- The single step of the reduction: if `m - 2 ^ k` is prime and
strictly exceeds `q ≥ 2`, then `q` does not divide `m - 2 ^ k`. The power
is passed as a separate numeral `P` with `2 ^ k = P` so that the call
sites stay `omega`-friendly. -/
theorem not_dvd_sub_of_pow_eq {m q k P : ℕ} (h : IsAllPrimeMinusPow m) (hq : 2 ≤ q)
    (hk : 0 < k) (hP : 2 ^ k = P) (hlt : P + q < m) : ¬ q ∣ (m - P) := by
  subst hP
  have hp : Nat.Prime (m - 2 ^ k) := h.2 k hk (by omega)
  exact (Nat.prime_def_lt'.mp hp).2 q hq (by omega)

/-- An odd divisor pins an odd multiple: if `a ∣ m` and `m` is odd then
`m = 2a·u + a` for some `u`. This turns the divisibility constraints of
this section into an arithmetic progression the kernel can enumerate. -/
theorem exists_eq_two_mul_add_of_dvd_of_odd {m a : ℕ} (hd : a ∣ m) (hm : ¬ 2 ∣ m) :
    ∃ u, m = 2 * a * u + a := by
  obtain ⟨c, rfl⟩ := hd
  have hodd : Odd (a * c) := Nat.odd_iff.mpr (by omega)
  obtain ⟨-, hco⟩ := Nat.odd_mul.mp hodd
  obtain ⟨d, rfl⟩ := hco
  exact ⟨d, by ring⟩

set_option maxHeartbeats 2000000 in
/-- **The base layer.** For `21 < m` the exponent `k = 1` forces parity,
`k = 1, 2` force `3 ∣ m` and `k = 1, 2, 3, 4` force `5 ∣ m`, so
`m ≡ 15 (mod 30)`: `2` is a primitive root mod `3` and mod `5`, so
`2 ^ k` runs through every nonzero residue there, and each such residue
is forbidden to `m`. -/
theorem mod_thirty_of_isAllPrimeMinusPow {m : ℕ} (hm : 21 < m) (h : IsAllPrimeMinusPow m) :
    m % 30 = 15 := by
  have d2 : ¬ (2:ℕ) ∣ (m - 2) :=
    not_dvd_sub_of_pow_eq h (k := 1) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d31 : ¬ (3:ℕ) ∣ (m - 2) :=
    not_dvd_sub_of_pow_eq h (k := 1) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d32 : ¬ (3:ℕ) ∣ (m - 4) :=
    not_dvd_sub_of_pow_eq h (k := 2) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d51 : ¬ (5:ℕ) ∣ (m - 2) :=
    not_dvd_sub_of_pow_eq h (k := 1) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d52 : ¬ (5:ℕ) ∣ (m - 4) :=
    not_dvd_sub_of_pow_eq h (k := 2) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d53 : ¬ (5:ℕ) ∣ (m - 8) :=
    not_dvd_sub_of_pow_eq h (k := 3) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d54 : ¬ (5:ℕ) ∣ (m - 16) :=
    not_dvd_sub_of_pow_eq h (k := 4) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have r2 : m % 2 = 1 := by
    by_contra hne
    exact d2 (by omega)
  have r3 : m % 3 = 0 := by
    by_contra hne
    have hc : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hc with hc | hc
    · exact d32 (by omega)
    · exact d31 (by omega)
  have r5 : m % 5 = 0 := by
    by_contra hne
    have hc : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
    rcases hc with hc | hc | hc | hc
    · exact d54 (by omega)
    · exact d51 (by omega)
    · exact d53 (by omega)
    · exact d52 (by omega)
  omega

set_option maxHeartbeats 2000000 in
/-- **Layer `q = 11`.** `2` is a primitive root mod `11`, so `2 ^ k`
for `k = 1, …, 10` runs through all ten nonzero residues; each is
forbidden to `m` once `m - 2 ^ k` is a prime exceeding `11`, which needs
`2 ^ 10 + 11 < m`. -/
theorem eleven_dvd_of_isAllPrimeMinusPow {m : ℕ} (hm : 1035 < m) (h : IsAllPrimeMinusPow m) : 11 ∣ m := by
  have d1 : ¬ (11:ℕ) ∣ (m - 2) :=
    not_dvd_sub_of_pow_eq h (k := 1) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d2 : ¬ (11:ℕ) ∣ (m - 4) :=
    not_dvd_sub_of_pow_eq h (k := 2) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d3 : ¬ (11:ℕ) ∣ (m - 8) :=
    not_dvd_sub_of_pow_eq h (k := 3) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d4 : ¬ (11:ℕ) ∣ (m - 16) :=
    not_dvd_sub_of_pow_eq h (k := 4) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d5 : ¬ (11:ℕ) ∣ (m - 32) :=
    not_dvd_sub_of_pow_eq h (k := 5) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d6 : ¬ (11:ℕ) ∣ (m - 64) :=
    not_dvd_sub_of_pow_eq h (k := 6) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d7 : ¬ (11:ℕ) ∣ (m - 128) :=
    not_dvd_sub_of_pow_eq h (k := 7) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d8 : ¬ (11:ℕ) ∣ (m - 256) :=
    not_dvd_sub_of_pow_eq h (k := 8) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d9 : ¬ (11:ℕ) ∣ (m - 512) :=
    not_dvd_sub_of_pow_eq h (k := 9) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d10 : ¬ (11:ℕ) ∣ (m - 1024) :=
    not_dvd_sub_of_pow_eq h (k := 10) (by norm_num) (by norm_num) (by norm_num) (by omega)
  omega

set_option maxHeartbeats 2000000 in
/-- **Layer `q = 13`.** `2` is a primitive root mod `13`; the twelve
exponents `k = 1, …, 12` exhaust the nonzero residues, so `13 ∣ m` once
`2 ^ 12 + 13 < m`. -/
theorem thirteen_dvd_of_isAllPrimeMinusPow {m : ℕ} (hm : 4109 < m) (h : IsAllPrimeMinusPow m) : 13 ∣ m := by
  have d1 : ¬ (13:ℕ) ∣ (m - 2) :=
    not_dvd_sub_of_pow_eq h (k := 1) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d2 : ¬ (13:ℕ) ∣ (m - 4) :=
    not_dvd_sub_of_pow_eq h (k := 2) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d3 : ¬ (13:ℕ) ∣ (m - 8) :=
    not_dvd_sub_of_pow_eq h (k := 3) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d4 : ¬ (13:ℕ) ∣ (m - 16) :=
    not_dvd_sub_of_pow_eq h (k := 4) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d5 : ¬ (13:ℕ) ∣ (m - 32) :=
    not_dvd_sub_of_pow_eq h (k := 5) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d6 : ¬ (13:ℕ) ∣ (m - 64) :=
    not_dvd_sub_of_pow_eq h (k := 6) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d7 : ¬ (13:ℕ) ∣ (m - 128) :=
    not_dvd_sub_of_pow_eq h (k := 7) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d8 : ¬ (13:ℕ) ∣ (m - 256) :=
    not_dvd_sub_of_pow_eq h (k := 8) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d9 : ¬ (13:ℕ) ∣ (m - 512) :=
    not_dvd_sub_of_pow_eq h (k := 9) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d10 : ¬ (13:ℕ) ∣ (m - 1024) :=
    not_dvd_sub_of_pow_eq h (k := 10) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d11 : ¬ (13:ℕ) ∣ (m - 2048) :=
    not_dvd_sub_of_pow_eq h (k := 11) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d12 : ¬ (13:ℕ) ∣ (m - 4096) :=
    not_dvd_sub_of_pow_eq h (k := 12) (by norm_num) (by norm_num) (by norm_num) (by omega)
  omega

set_option maxHeartbeats 2000000 in
/-- **Layer `q = 19`.** `2` is a primitive root mod `19`; the eighteen
exponents `k = 1, …, 18` exhaust the nonzero residues, so `19 ∣ m` once
`2 ^ 18 + 19 < m`. -/
theorem nineteen_dvd_of_isAllPrimeMinusPow {m : ℕ} (hm : 262163 < m) (h : IsAllPrimeMinusPow m) : 19 ∣ m := by
  have d1 : ¬ (19:ℕ) ∣ (m - 2) :=
    not_dvd_sub_of_pow_eq h (k := 1) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d2 : ¬ (19:ℕ) ∣ (m - 4) :=
    not_dvd_sub_of_pow_eq h (k := 2) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d3 : ¬ (19:ℕ) ∣ (m - 8) :=
    not_dvd_sub_of_pow_eq h (k := 3) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d4 : ¬ (19:ℕ) ∣ (m - 16) :=
    not_dvd_sub_of_pow_eq h (k := 4) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d5 : ¬ (19:ℕ) ∣ (m - 32) :=
    not_dvd_sub_of_pow_eq h (k := 5) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d6 : ¬ (19:ℕ) ∣ (m - 64) :=
    not_dvd_sub_of_pow_eq h (k := 6) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d7 : ¬ (19:ℕ) ∣ (m - 128) :=
    not_dvd_sub_of_pow_eq h (k := 7) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d8 : ¬ (19:ℕ) ∣ (m - 256) :=
    not_dvd_sub_of_pow_eq h (k := 8) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d9 : ¬ (19:ℕ) ∣ (m - 512) :=
    not_dvd_sub_of_pow_eq h (k := 9) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d10 : ¬ (19:ℕ) ∣ (m - 1024) :=
    not_dvd_sub_of_pow_eq h (k := 10) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d11 : ¬ (19:ℕ) ∣ (m - 2048) :=
    not_dvd_sub_of_pow_eq h (k := 11) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d12 : ¬ (19:ℕ) ∣ (m - 4096) :=
    not_dvd_sub_of_pow_eq h (k := 12) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d13 : ¬ (19:ℕ) ∣ (m - 8192) :=
    not_dvd_sub_of_pow_eq h (k := 13) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d14 : ¬ (19:ℕ) ∣ (m - 16384) :=
    not_dvd_sub_of_pow_eq h (k := 14) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d15 : ¬ (19:ℕ) ∣ (m - 32768) :=
    not_dvd_sub_of_pow_eq h (k := 15) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d16 : ¬ (19:ℕ) ∣ (m - 65536) :=
    not_dvd_sub_of_pow_eq h (k := 16) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d17 : ¬ (19:ℕ) ∣ (m - 131072) :=
    not_dvd_sub_of_pow_eq h (k := 17) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d18 : ¬ (19:ℕ) ∣ (m - 262144) :=
    not_dvd_sub_of_pow_eq h (k := 18) (by norm_num) (by norm_num) (by norm_num) (by omega)
  omega

set_option maxHeartbeats 2000000 in
/-- **Layer `q = 29`.** `2` is a primitive root mod `29`; the
twenty-eight exponents `k = 1, …, 28` exhaust the nonzero residues, so
`29 ∣ m` once `2 ^ 28 + 29 < m`. The next usable prime is `37`, which
would need `m > 2 ^ 36 + 37`; `7, 17, 23, 31` are unusable because `2`
is not a primitive root there. -/
theorem twentynine_dvd_of_isAllPrimeMinusPow {m : ℕ} (hm : 268435485 < m) (h : IsAllPrimeMinusPow m) : 29 ∣ m := by
  have d1 : ¬ (29:ℕ) ∣ (m - 2) :=
    not_dvd_sub_of_pow_eq h (k := 1) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d2 : ¬ (29:ℕ) ∣ (m - 4) :=
    not_dvd_sub_of_pow_eq h (k := 2) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d3 : ¬ (29:ℕ) ∣ (m - 8) :=
    not_dvd_sub_of_pow_eq h (k := 3) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d4 : ¬ (29:ℕ) ∣ (m - 16) :=
    not_dvd_sub_of_pow_eq h (k := 4) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d5 : ¬ (29:ℕ) ∣ (m - 32) :=
    not_dvd_sub_of_pow_eq h (k := 5) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d6 : ¬ (29:ℕ) ∣ (m - 64) :=
    not_dvd_sub_of_pow_eq h (k := 6) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d7 : ¬ (29:ℕ) ∣ (m - 128) :=
    not_dvd_sub_of_pow_eq h (k := 7) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d8 : ¬ (29:ℕ) ∣ (m - 256) :=
    not_dvd_sub_of_pow_eq h (k := 8) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d9 : ¬ (29:ℕ) ∣ (m - 512) :=
    not_dvd_sub_of_pow_eq h (k := 9) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d10 : ¬ (29:ℕ) ∣ (m - 1024) :=
    not_dvd_sub_of_pow_eq h (k := 10) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d11 : ¬ (29:ℕ) ∣ (m - 2048) :=
    not_dvd_sub_of_pow_eq h (k := 11) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d12 : ¬ (29:ℕ) ∣ (m - 4096) :=
    not_dvd_sub_of_pow_eq h (k := 12) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d13 : ¬ (29:ℕ) ∣ (m - 8192) :=
    not_dvd_sub_of_pow_eq h (k := 13) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d14 : ¬ (29:ℕ) ∣ (m - 16384) :=
    not_dvd_sub_of_pow_eq h (k := 14) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d15 : ¬ (29:ℕ) ∣ (m - 32768) :=
    not_dvd_sub_of_pow_eq h (k := 15) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d16 : ¬ (29:ℕ) ∣ (m - 65536) :=
    not_dvd_sub_of_pow_eq h (k := 16) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d17 : ¬ (29:ℕ) ∣ (m - 131072) :=
    not_dvd_sub_of_pow_eq h (k := 17) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d18 : ¬ (29:ℕ) ∣ (m - 262144) :=
    not_dvd_sub_of_pow_eq h (k := 18) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d19 : ¬ (29:ℕ) ∣ (m - 524288) :=
    not_dvd_sub_of_pow_eq h (k := 19) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d20 : ¬ (29:ℕ) ∣ (m - 1048576) :=
    not_dvd_sub_of_pow_eq h (k := 20) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d21 : ¬ (29:ℕ) ∣ (m - 2097152) :=
    not_dvd_sub_of_pow_eq h (k := 21) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d22 : ¬ (29:ℕ) ∣ (m - 4194304) :=
    not_dvd_sub_of_pow_eq h (k := 22) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d23 : ¬ (29:ℕ) ∣ (m - 8388608) :=
    not_dvd_sub_of_pow_eq h (k := 23) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d24 : ¬ (29:ℕ) ∣ (m - 16777216) :=
    not_dvd_sub_of_pow_eq h (k := 24) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d25 : ¬ (29:ℕ) ∣ (m - 33554432) :=
    not_dvd_sub_of_pow_eq h (k := 25) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d26 : ¬ (29:ℕ) ∣ (m - 67108864) :=
    not_dvd_sub_of_pow_eq h (k := 26) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d27 : ¬ (29:ℕ) ∣ (m - 134217728) :=
    not_dvd_sub_of_pow_eq h (k := 27) (by norm_num) (by norm_num) (by norm_num) (by omega)
  have d28 : ¬ (29:ℕ) ∣ (m - 268435456) :=
    not_dvd_sub_of_pow_eq h (k := 28) (by norm_num) (by norm_num) (by norm_num) (by omega)
  omega

/-- `m ≡ 15 (mod 30)` unpacked. -/
theorem three_dvd_of_mod_thirty {m : ℕ} (h : m % 30 = 15) : 3 ∣ m := by omega

/-- `m ≡ 15 (mod 30)` unpacked. -/
theorem five_dvd_of_mod_thirty {m : ℕ} (h : m % 30 = 15) : 5 ∣ m := by omega

/-- `m ≡ 15 (mod 30)` unpacked: terms past `21` are odd. -/
theorem not_two_dvd_of_mod_thirty {m : ℕ} (h : m % 30 = 15) : ¬ 2 ∣ m := by omega

/-- `3 · 5 · 11 ∣ m` from the first three layers. -/
theorem dvd_165_of_mod_thirty {m : ℕ} (r30 : m % 30 = 15) (r11 : 11 ∣ m) : 165 ∣ m :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (three_dvd_of_mod_thirty r30)
      (five_dvd_of_mod_thirty r30)) r11

/-- `3 · 5 · 11 · 13 ∣ m` from the first four layers. -/
theorem dvd_2145_of_mod_thirty {m : ℕ} (r30 : m % 30 = 15) (r11 : 11 ∣ m) (r13 : 13 ∣ m) :
    2145 ∣ m :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (dvd_165_of_mod_thirty r30 r11) r13

/-- `3 · 5 · 11 · 13 · 19 ∣ m` from the first five layers. -/
theorem dvd_40755_of_mod_thirty {m : ℕ} (r30 : m % 30 = 15) (r11 : 11 ∣ m) (r13 : 13 ∣ m)
    (r19 : 19 ∣ m) : 40755 ∣ m :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (dvd_2145_of_mod_thirty r30 r11 r13) r19

/-- `3 · 5 · 11 · 13 · 19 · 29 ∣ m` from all six layers. -/
theorem dvd_1181895_of_mod_thirty {m : ℕ} (r30 : m % 30 = 15) (r11 : 11 ∣ m) (r13 : 13 ∣ m)
    (r19 : 19 ∣ m) (r29 : 29 ∣ m) : 1181895 ∣ m :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide)
    (dvd_40755_of_mod_thirty r30 r11 r13 r19) r29

end Reduction

-- ════════════════════════════════════════════════════════════════════
-- §6 THE FINITE COMPLETENESS WINDOW
-- ════════════════════════════════════════════════════════════════════

section Window

/-- The powers `2 ^ 1, …, 2 ^ 29`, as a literal list. `2 ^ 29 < 10 ^ 9 <
2 ^ 30`, so this is exhaustive for the window of this section. A literal
list is already in normal form, which is what keeps the kernel sweeps
below affordable: a `Finset.Ico` or `List.range` would be rebuilt by the
kernel at every candidate. -/
def powList : List ℕ :=
  [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
   262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864,
   134217728, 268435456, 536870912]

-- Ground checks for `powList`.
example : powList.length = 29 := by decide
example : powList.head? = some 2 := by decide
example : powList.getLast? = some 536870912 := by decide

/-- Every entry of `powList` is a positive power of two — the bridge
from the `∀ k` of `AllPrimeMinusPow` to the `∀ p ∈ powList` of the kernel
sweeps. -/
theorem exists_pow_eq_of_mem_powList {p : ℕ} (hp : p ∈ powList) :
    ∃ k, 0 < k ∧ 2 ^ k = p := by
  simp only [powList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨1, by norm_num⟩, ⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨4, by norm_num⟩, ⟨5, by norm_num⟩, ⟨6, by norm_num⟩, ⟨7, by norm_num⟩, ⟨8, by norm_num⟩, ⟨9, by norm_num⟩, ⟨10, by norm_num⟩, ⟨11, by norm_num⟩, ⟨12, by norm_num⟩, ⟨13, by norm_num⟩, ⟨14, by norm_num⟩, ⟨15, by norm_num⟩, ⟨16, by norm_num⟩, ⟨17, by norm_num⟩, ⟨18, by norm_num⟩, ⟨19, by norm_num⟩, ⟨20, by norm_num⟩, ⟨21, by norm_num⟩, ⟨22, by norm_num⟩, ⟨23, by norm_num⟩, ⟨24, by norm_num⟩, ⟨25, by norm_num⟩, ⟨26, by norm_num⟩, ⟨27, by norm_num⟩, ⟨28, by norm_num⟩, ⟨29, by norm_num⟩]

/-- The primes below `80`, as a literal list; pinned exactly by the two
ground checks below. -/
def smallFactorList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]

/-- Ground check: every entry of `smallFactorList` is a prime below 80. -/
theorem prime_of_mem_smallFactorList {d : ℕ} (hd : d ∈ smallFactorList) :
    Nat.Prime d ∧ d < 80 := by
  have key : ∀ e ∈ smallFactorList, Nat.Prime e ∧ e < 80 := by decide +kernel
  exact key d hd

/-- Ground check: every prime below 80 is an entry of `smallFactorList`.
With `prime_of_mem_smallFactorList` this pins the list exactly. -/
theorem mem_smallFactorList_of_prime {d : ℕ} (hd : Nat.Prime d) (hlt : d < 80) :
    d ∈ smallFactorList := by
  have key : ∀ e ∈ Finset.range 80, Nat.Prime e → e ∈ smallFactorList := by decide +kernel
  exact key d (Finset.mem_range.mpr hlt) hd

/-- `NoSmallFactor c`: `2 ≤ c`, and no prime below `80` is a *proper*
divisor of `c`. This is a deliberately cheap **necessary condition** for
primality, and it is what the kernel sweeps of this section test.

It is *equivalent* to `Nat.Prime` only below `83 ^ 2 = 6889`
(`prime_iff_noSmallFactor`); above that it is strictly weaker — e.g.
`6889 = 83 ^ 2` satisfies it (see the ground checks). That is harmless
here, and is in fact what makes the window affordable: the sweeps use
`NoSmallFactor` as a *hypothesis*, so replacing primality by a weaker
condition makes each swept statement **stronger**, and
`noSmallFactor_of_prime` is the only direction the window proof needs.

Deciding `Nat.Prime p` through Mathlib's kernel-facing instance costs
`Θ(p)` reduction steps, hopeless at `p ≈ 10 ^ 9`; this costs at most 22
divisibility tests, with early exit at the first proper divisor found.
The conjunct `2 ≤ c` excludes `c = 1`, which passes trial division
vacuously. -/
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

/-- Ground truth for `NoSmallFactor`: below `83 ^ 2 = 6889` it is
*exactly* `Nat.Prime`. (A composite `c` has `minFac c * minFac c ≤ c`, so
`minFac c < 83`, and `minFac c` is prime, hence at most `79`, hence
listed.) -/
theorem prime_iff_noSmallFactor {c : ℕ} (hc : c < 6889) :
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
  have hb : c.minFac < 83 := by nlinarith
  have hb' : c.minFac < 80 := by
    by_contra hge
    have hcases : c.minFac = 80 ∨ c.minFac = 81 ∨ c.minFac = 82 := by omega
    rcases hcases with heq | heq | heq <;> (rw [heq] at hpp; norm_num at hpp)
  exact absurd (hd _ (mem_smallFactorList_of_prime hpp hb') hdvd) (by omega)

-- Ground checks for `NoSmallFactor` at the boundaries.
example : ¬ NoSmallFactor 0 := by decide
example : ¬ NoSmallFactor 1 := by decide
example : NoSmallFactor 2 := by decide
example : NoSmallFactor 79 := by decide
example : ¬ NoSmallFactor 6887 := by decide

-- … and the disclosure that it is strictly weaker than primality, first
-- failing at `83 ^ 2 = 6889`.
example : NoSmallFactor 6889 ∧ ¬ Nat.Prime 6889 := ⟨by decide, by norm_num⟩

/-- The hypothesis supplier for the kernel sweeps: a term of A039669
makes every `m - 2 ^ k` in range pass the `NoSmallFactor` test. -/
theorem forall_noSmallFactor_of_isAllPrimeMinusPow {m : ℕ} (h : IsAllPrimeMinusPow m) :
    ∀ p ∈ powList, p < m → NoSmallFactor (m - p) := by
  intro p hp hlt
  obtain ⟨k, hk, rfl⟩ := exists_pow_eq_of_mem_powList hp
  exact noSmallFactor_of_prime (h.2 k hk hlt)

/-! ### The kernel sweeps, one per residue layer of §5. -/

set_option maxRecDepth 40000 in
/-- Layer 1: the 19 candidates `3 ≤ m ≤ 21`, below the reach of the §5
reduction. -/
theorem sweepR1 : ∀ m ∈ List.range' 3 19,
    (∀ p ∈ powList, p < m → NoSmallFactor (m - p)) →
    m ∈ ({4, 7, 15, 21} : Finset ℕ) := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 2: the 34 candidates `m ≡ 15 (mod 30)` with `21 < m ≤ 1035`. -/
theorem sweepR2 : ∀ j ∈ List.range' 1 34,
    (∀ p ∈ powList, p < 30 * j + 15 → NoSmallFactor (30 * j + 15 - p)) →
    30 * j + 15 ∈ ({45, 75, 105} : Finset ℕ) := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 3: the 9 candidates `m ≡ 165 (mod 330)` with `1035 < m ≤ 4109`.
None is a term. -/
theorem sweepR3 : ∀ t ∈ List.range' 3 9,
    (∀ p ∈ powList, p < 330 * t + 165 → NoSmallFactor (330 * t + 165 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 4: the 60 candidates `m ≡ 2145 (mod 4290)` with
`4109 < m ≤ 262163`. None is a term. -/
theorem sweepR4 : ∀ u ∈ List.range' 1 60,
    (∀ p ∈ powList, p < 4290 * u + 2145 → NoSmallFactor (4290 * u + 2145 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 5, part 1 of 7: `m ≡ 40755 (mod 81510)`, `v = 3, …, 472`.
The layer is split across seven declarations to bound the kernel's
peak memory, which grows with the size of a single reduction. -/
theorem sweepR5a : ∀ v ∈ List.range' 3 470,
    (∀ p ∈ powList, p < 81510 * v + 40755 → NoSmallFactor (81510 * v + 40755 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 5, part 2 of 7: `v = 473, …, 942`. -/
theorem sweepR5b : ∀ v ∈ List.range' 473 470,
    (∀ p ∈ powList, p < 81510 * v + 40755 → NoSmallFactor (81510 * v + 40755 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 5, part 3 of 7: `v = 943, …, 1412`. -/
theorem sweepR5c : ∀ v ∈ List.range' 943 470,
    (∀ p ∈ powList, p < 81510 * v + 40755 → NoSmallFactor (81510 * v + 40755 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 5, part 4 of 7: `v = 1413, …, 1882`. -/
theorem sweepR5d : ∀ v ∈ List.range' 1413 470,
    (∀ p ∈ powList, p < 81510 * v + 40755 → NoSmallFactor (81510 * v + 40755 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 5, part 5 of 7: `v = 1883, …, 2352`. -/
theorem sweepR5e : ∀ v ∈ List.range' 1883 470,
    (∀ p ∈ powList, p < 81510 * v + 40755 → NoSmallFactor (81510 * v + 40755 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 5, part 6 of 7: `v = 2353, …, 2822`. -/
theorem sweepR5f : ∀ v ∈ List.range' 2353 470,
    (∀ p ∈ powList, p < 81510 * v + 40755 → NoSmallFactor (81510 * v + 40755 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 5, part 7 of 7: `v = 2823, …, 3292`. -/
theorem sweepR5g : ∀ v ∈ List.range' 2823 470,
    (∀ p ∈ powList, p < 81510 * v + 40755 → NoSmallFactor (81510 * v + 40755 - p)) →
    False := by decide +kernel

set_option maxRecDepth 40000 in
/-- Layer 6: the 309 candidates `m ≡ 1181895 (mod 2363790)` with
`268435485 < m ≤ 10 ^ 9`; the last is `2363790 · 422 + 1181895 =
998701275`. None is a term. -/
theorem sweepR6 : ∀ w ∈ List.range' 114 309,
    (∀ p ∈ powList, p < 2363790 * w + 1181895 → NoSmallFactor (2363790 * w + 1181895 - p)) →
    False := by decide +kernel

/-! ### Assembling the layers. -/

/-- Index bound for layer 2. -/
theorem index_bound_two {m j : ℕ} (hj : m = 30 * j + 15) (h1 : 21 < m) (h2 : m ≤ 1035) :
    j ∈ List.range' 1 34 := by rw [List.mem_range'_1]; omega

/-- Index bound for layer 3. -/
theorem index_bound_three {m t : ℕ} (ht : m = 330 * t + 165) (h1 : 1035 < m) (h2 : m ≤ 4109) :
    t ∈ List.range' 3 9 := by rw [List.mem_range'_1]; omega

/-- Index bound for layer 4. -/
theorem index_bound_four {m u : ℕ} (hu : m = 4290 * u + 2145) (h1 : 4109 < m)
    (h2 : m ≤ 262163) : u ∈ List.range' 1 60 := by rw [List.mem_range'_1]; omega

/-- Index bound for layer 5. -/
theorem index_bound_five {m v : ℕ} (hv : m = 81510 * v + 40755) (h1 : 262163 < m)
    (h2 : m ≤ 268435485) : v ∈ List.range' 3 3290 := by rw [List.mem_range'_1]; omega

/-- Index bound for layer 6. -/
theorem index_bound_six {m w : ℕ} (hw : m = 2363790 * w + 1181895) (h1 : 268435485 < m)
    (h2 : m ≤ 1000000000) : w ∈ List.range' 114 309 := by rw [List.mem_range'_1]; omega

/-- Layer 5 with the seven-way chunk dispatch folded in. -/
theorem sweepR5 {v : ℕ} (hb : v ∈ List.range' 3 3290)
    (hf : ∀ p ∈ powList, p < 81510 * v + 40755 →
      NoSmallFactor (81510 * v + 40755 - p)) : False := by
  rw [List.mem_range'_1] at hb
  rcases (show v ≤ 472 ∨ (473 ≤ v ∧ v ≤ 942) ∨ (943 ≤ v ∧ v ≤ 1412) ∨
      (1413 ≤ v ∧ v ≤ 1882) ∨ (1883 ≤ v ∧ v ≤ 2352) ∨ (2353 ≤ v ∧ v ≤ 2822) ∨ 2823 ≤ v by
    omega) with hc | hc | hc | hc | hc | hc | hc
  · exact sweepR5a v (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hf
  · exact sweepR5b v (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hf
  · exact sweepR5c v (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hf
  · exact sweepR5d v (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hf
  · exact sweepR5e v (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hf
  · exact sweepR5f v (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hf
  · exact sweepR5g v (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hf

/-- Layer 1 of the window: `2 < m ≤ 21`. -/
theorem window_layer_one {m : ℕ} (h1 : 2 < m) (h2 : m ≤ 21) (h : IsAllPrimeMinusPow m) :
    m ∈ ({4, 7, 15, 21} : Finset ℕ) :=
  sweepR1 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    (forall_noSmallFactor_of_isAllPrimeMinusPow h)

/-- Layer 2 of the window: `21 < m ≤ 1035`. -/
theorem window_layer_two {m : ℕ} (h1 : 21 < m) (h2 : m ≤ 1035) (h : IsAllPrimeMinusPow m) :
    m ∈ ({45, 75, 105} : Finset ℕ) := by
  have r30 : m % 30 = 15 := mod_thirty_of_isAllPrimeMinusPow h1 h
  obtain ⟨j, hj⟩ : ∃ j, m = 30 * j + 15 := ⟨m / 30, by omega⟩
  have hf : ∀ p ∈ powList, p < 30 * j + 15 → NoSmallFactor (30 * j + 15 - p) := by
    rw [← hj]; exact forall_noSmallFactor_of_isAllPrimeMinusPow h
  rw [hj]
  exact sweepR2 j (index_bound_two hj h1 h2) hf

/-- Layer 3 of the window: `1035 < m ≤ 4109` contains no term. -/
theorem window_layer_three {m : ℕ} (h1 : 1035 < m) (h2 : m ≤ 4109)
    (h : IsAllPrimeMinusPow m) : False := by
  have r30 : m % 30 = 15 := mod_thirty_of_isAllPrimeMinusPow (by omega) h
  have hd : (165 : ℕ) ∣ m :=
    dvd_165_of_mod_thirty r30 (eleven_dvd_of_isAllPrimeMinusPow h1 h)
  obtain ⟨t, ht⟩ := exists_eq_two_mul_add_of_dvd_of_odd hd (not_two_dvd_of_mod_thirty r30)
  have ht' : m = 330 * t + 165 := by omega
  have hf : ∀ p ∈ powList, p < 330 * t + 165 → NoSmallFactor (330 * t + 165 - p) := by
    rw [← ht']; exact forall_noSmallFactor_of_isAllPrimeMinusPow h
  exact sweepR3 t (index_bound_three ht' h1 h2) hf

/-- Layer 4 of the window: `4109 < m ≤ 262163` contains no term. -/
theorem window_layer_four {m : ℕ} (h1 : 4109 < m) (h2 : m ≤ 262163)
    (h : IsAllPrimeMinusPow m) : False := by
  have r30 : m % 30 = 15 := mod_thirty_of_isAllPrimeMinusPow (by omega) h
  have hd : (2145 : ℕ) ∣ m :=
    dvd_2145_of_mod_thirty r30 (eleven_dvd_of_isAllPrimeMinusPow (by omega) h)
      (thirteen_dvd_of_isAllPrimeMinusPow h1 h)
  obtain ⟨u, hu⟩ := exists_eq_two_mul_add_of_dvd_of_odd hd (not_two_dvd_of_mod_thirty r30)
  have hu' : m = 4290 * u + 2145 := by omega
  have hf : ∀ p ∈ powList, p < 4290 * u + 2145 → NoSmallFactor (4290 * u + 2145 - p) := by
    rw [← hu']; exact forall_noSmallFactor_of_isAllPrimeMinusPow h
  exact sweepR4 u (index_bound_four hu' h1 h2) hf

/-- Layer 5 of the window: `262163 < m ≤ 2 ^ 28 + 29` contains no term. -/
theorem window_layer_five {m : ℕ} (h1 : 262163 < m) (h2 : m ≤ 268435485)
    (h : IsAllPrimeMinusPow m) : False := by
  have r30 : m % 30 = 15 := mod_thirty_of_isAllPrimeMinusPow (by omega) h
  have hd : (40755 : ℕ) ∣ m :=
    dvd_40755_of_mod_thirty r30 (eleven_dvd_of_isAllPrimeMinusPow (by omega) h)
      (thirteen_dvd_of_isAllPrimeMinusPow (by omega) h)
      (nineteen_dvd_of_isAllPrimeMinusPow h1 h)
  obtain ⟨v, hv⟩ := exists_eq_two_mul_add_of_dvd_of_odd hd (not_two_dvd_of_mod_thirty r30)
  have hv' : m = 81510 * v + 40755 := by omega
  have hf : ∀ p ∈ powList, p < 81510 * v + 40755 →
      NoSmallFactor (81510 * v + 40755 - p) := by
    rw [← hv']; exact forall_noSmallFactor_of_isAllPrimeMinusPow h
  exact sweepR5 (index_bound_five hv' h1 h2) hf

/-- Layer 6 of the window: `2 ^ 28 + 29 < m ≤ 10 ^ 9` contains no term. -/
theorem window_layer_six {m : ℕ} (h1 : 268435485 < m) (h2 : m ≤ 1000000000)
    (h : IsAllPrimeMinusPow m) : False := by
  have r30 : m % 30 = 15 := mod_thirty_of_isAllPrimeMinusPow (by omega) h
  have hd : (1181895 : ℕ) ∣ m :=
    dvd_1181895_of_mod_thirty r30 (eleven_dvd_of_isAllPrimeMinusPow (by omega) h)
      (thirteen_dvd_of_isAllPrimeMinusPow (by omega) h)
      (nineteen_dvd_of_isAllPrimeMinusPow (by omega) h)
      (twentynine_dvd_of_isAllPrimeMinusPow h1 h)
  obtain ⟨w, hw⟩ := exists_eq_two_mul_add_of_dvd_of_odd hd (not_two_dvd_of_mod_thirty r30)
  have hw' : m = 2363790 * w + 1181895 := by omega
  have hf : ∀ p ∈ powList, p < 2363790 * w + 1181895 →
      NoSmallFactor (2363790 * w + 1181895 - p) := by
    rw [← hw']; exact forall_noSmallFactor_of_isAllPrimeMinusPow h
  exact sweepR6 w (index_bound_six hw' h1 h2) hf

/-- **The finite completeness window, N = 10 ^ 9** (implication form).
Sorry-free: no `m ≤ 1000000000` other than `4, 7, 15, 21, 45, 75, 105`
satisfies the A039669 condition.

This is the shape of the archived `2 ^ 44` Mientka–Weitzenkamp window of
google-deepmind/formal-conjectures, at the largest bound this
covering-congruence reduction plus kernel sweep reaches. It is far short
of the `2 ^ 44` published search and the `2 ^ 120` OEIS search bound,
neither of which is a formal proof. -/
theorem mem_of_isAllPrimeMinusPow_of_le {m : ℕ} (hm : m ≤ 1000000000)
    (h : IsAllPrimeMinusPow m) : m ∈ ({4, 7, 15, 21, 45, 75, 105} : Finset ℕ) := by
  by_cases h1 : m ≤ 21
  · have hmem := window_layer_one h.1 h1 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    omega
  by_cases h2 : m ≤ 1035
  · have hmem := window_layer_two (by omega) h2 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    omega
  by_cases h3 : m ≤ 4109
  · exact absurd (window_layer_three (by omega) h3 h) not_false
  by_cases h4 : m ≤ 262163
  · exact absurd (window_layer_four (by omega) h4 h) not_false
  by_cases h5 : m ≤ 268435485
  · exact absurd (window_layer_five (by omega) h5 h) not_false
  exact absurd (window_layer_six (by omega) hm h) not_false

/-- **The finite completeness window, N = 10 ^ 9** (set-equality form) —
the shape in which google-deepmind/formal-conjectures states (and
`sorry`s) the Mientka–Weitzenkamp `2 ^ 44` window. Sorry-free. -/
theorem setOf_isAllPrimeMinusPow_le :
    {m : ℕ | m ≤ 1000000000 ∧ IsAllPrimeMinusPow m} =
      ({4, 7, 15, 21, 45, 75, 105} : Set ℕ) := by
  ext m
  constructor
  · rintro ⟨hm, h⟩
    have hmem := mem_of_isAllPrimeMinusPow_of_le hm h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨by norm_num, isAllPrimeMinusPow_4⟩, ⟨by norm_num, isAllPrimeMinusPow_7⟩,
      ⟨by norm_num, isAllPrimeMinusPow_15⟩, ⟨by norm_num, isAllPrimeMinusPow_21⟩,
      ⟨by norm_num, isAllPrimeMinusPow_45⟩, ⟨by norm_num, isAllPrimeMinusPow_75⟩,
      ⟨by norm_num, isAllPrimeMinusPow_105⟩]

end Window

-- ════════════════════════════════════════════════════════════════════
-- §7 THE ARCHIVED CONJECTURE (the file's single intended `sorry`)
-- ════════════════════════════════════════════════════════════════════

/-- **Erdős' completeness conjecture for A039669** (OEIS A039669 comment,
pinned 2026-07-30: "Erdős conjectures that these are the only values of
n with this property"; erdosproblems.com #1142: "Are there infinitely
many n (or any n > 105) such that n - 2^k is prime for all 1 < 2^k < n?").

OPEN. INTENDED SORRY — archived conjecture, disclosed in the module
header; it is this file's only `sorry`. The same statement is `sorry`'d
in google-deepmind/formal-conjectures (in the infinitude form, plus the
`2 ^ 44` window); see the module header.

Evidence: `4, 7, 15, 21, 45, 75, 105` are members
(`isAllPrimeMinusPow_4` … `_105`); no other member `m ≤ 10 ^ 9`
(`mem_of_isAllPrimeMinusPow_of_le`, kernel-checked here); no other
member below `2 ^ 44` (Mientka–Weitzenkamp 1969) or below `2 ^ 120`
(Alekseyev, OEIS 2011-12-08); and the number of members up to `N` is
`o(N)` by Vaughan 1973.

ROUTE: see the module header. §5's covering-congruence reduction is the
standard tool applied as far as it goes; it shrinks each finite window
but cannot close the infinite one. -/
theorem erdos_1142 (m : ℕ) (h : IsAllPrimeMinusPow m) :
    m ∈ ({4, 7, 15, 21, 45, 75, 105} : Finset ℕ) := by
  -- intended sorry: open conjecture (Formalize/A039669-erdos-minus-2k.md,
  -- erdosproblems.com #1142).
  sorry

/-- A039669 as a set, granting `erdos_1142`. No new `sorry`;
`sorryAx`-dependent through `erdos_1142`. -/
theorem setOf_isAllPrimeMinusPow_of_erdos_1142 :
    {m : ℕ | IsAllPrimeMinusPow m} = ({4, 7, 15, 21, 45, 75, 105} : Set ℕ) := by
  ext m
  constructor
  · intro h
    have hmem := erdos_1142 m h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [isAllPrimeMinusPow_4, isAllPrimeMinusPow_7, isAllPrimeMinusPow_15,
      isAllPrimeMinusPow_21, isAllPrimeMinusPow_45, isAllPrimeMinusPow_75,
      isAllPrimeMinusPow_105]

/-- The negative answer to the first half of erdosproblems #1142 ("Are
there infinitely many n …?"), granting `erdos_1142`. No new `sorry`;
`sorryAx`-dependent through `erdos_1142`. -/
theorem not_infinite_setOf_isAllPrimeMinusPow_of_erdos_1142 :
    ¬ {m : ℕ | IsAllPrimeMinusPow m}.Infinite := by
  rw [Set.not_infinite, setOf_isAllPrimeMinusPow_of_erdos_1142]
  exact (((((Set.finite_singleton 105).insert 75).insert 45).insert 21).insert 15
    |>.insert 7).insert 4

end Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §8 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

/-! ## Axiom audit

`Erdos.Covering.erdos_1142` is the single intended `sorry` and reports
`sorryAx`, as do the two corollaries derived from it. Every other
declaration rests on a subset of `{propext, Classical.choice,
Quot.sound}`. The subset check is also the sound `native_decide`
detector on this toolchain: a use would surface as a per-declaration
`*._native.native_decide.ax_*` axiom. There is no `native_decide` in
this file. -/

#print axioms Erdos.Covering.AllPrimeMinusPow
#print axioms Erdos.Covering.IsAllPrimeMinusPow
#print axioms Erdos.Covering.isAllPrimeMinusPow_def
#print axioms Erdos.Covering.allPrimeMinusPow_iff_forall_lt
#print axioms Erdos.Covering.decidableAllPrimeMinusPow
#print axioms Erdos.Covering.decidableIsAllPrimeMinusPow
#print axioms Erdos.Covering.allPrimeMinusPow_of_le_two
#print axioms Erdos.Covering.exists_pow_lt_of_two_lt
#print axioms Erdos.Covering.prime_sub_two_of_isAllPrimeMinusPow
#print axioms Erdos.Covering.isAllPrimeMinusPow_4
#print axioms Erdos.Covering.isAllPrimeMinusPow_7
#print axioms Erdos.Covering.isAllPrimeMinusPow_15
#print axioms Erdos.Covering.isAllPrimeMinusPow_21
#print axioms Erdos.Covering.isAllPrimeMinusPow_45
#print axioms Erdos.Covering.isAllPrimeMinusPow_75
#print axioms Erdos.Covering.isAllPrimeMinusPow_105
#print axioms Erdos.Covering.not_isAllPrimeMinusPow_3
#print axioms Erdos.Covering.not_isAllPrimeMinusPow_5
#print axioms Erdos.Covering.not_isAllPrimeMinusPow_6
#print axioms Erdos.Covering.not_isAllPrimeMinusPow_106
#print axioms Erdos.Covering.not_dvd_sub_of_pow_eq
#print axioms Erdos.Covering.exists_eq_two_mul_add_of_dvd_of_odd
#print axioms Erdos.Covering.mod_thirty_of_isAllPrimeMinusPow
#print axioms Erdos.Covering.eleven_dvd_of_isAllPrimeMinusPow
#print axioms Erdos.Covering.thirteen_dvd_of_isAllPrimeMinusPow
#print axioms Erdos.Covering.nineteen_dvd_of_isAllPrimeMinusPow
#print axioms Erdos.Covering.twentynine_dvd_of_isAllPrimeMinusPow
#print axioms Erdos.Covering.three_dvd_of_mod_thirty
#print axioms Erdos.Covering.five_dvd_of_mod_thirty
#print axioms Erdos.Covering.not_two_dvd_of_mod_thirty
#print axioms Erdos.Covering.dvd_165_of_mod_thirty
#print axioms Erdos.Covering.dvd_2145_of_mod_thirty
#print axioms Erdos.Covering.dvd_40755_of_mod_thirty
#print axioms Erdos.Covering.dvd_1181895_of_mod_thirty
#print axioms Erdos.Covering.powList
#print axioms Erdos.Covering.exists_pow_eq_of_mem_powList
#print axioms Erdos.Covering.smallFactorList
#print axioms Erdos.Covering.prime_of_mem_smallFactorList
#print axioms Erdos.Covering.mem_smallFactorList_of_prime
#print axioms Erdos.Covering.NoSmallFactor
#print axioms Erdos.Covering.decidableNoSmallFactor
#print axioms Erdos.Covering.noSmallFactor_of_prime
#print axioms Erdos.Covering.prime_iff_noSmallFactor
#print axioms Erdos.Covering.forall_noSmallFactor_of_isAllPrimeMinusPow
#print axioms Erdos.Covering.sweepR1
#print axioms Erdos.Covering.sweepR2
#print axioms Erdos.Covering.sweepR3
#print axioms Erdos.Covering.sweepR4
#print axioms Erdos.Covering.sweepR5a
#print axioms Erdos.Covering.sweepR5b
#print axioms Erdos.Covering.sweepR5c
#print axioms Erdos.Covering.sweepR5d
#print axioms Erdos.Covering.sweepR5e
#print axioms Erdos.Covering.sweepR5f
#print axioms Erdos.Covering.sweepR5g
#print axioms Erdos.Covering.sweepR6
#print axioms Erdos.Covering.index_bound_two
#print axioms Erdos.Covering.index_bound_three
#print axioms Erdos.Covering.index_bound_four
#print axioms Erdos.Covering.index_bound_five
#print axioms Erdos.Covering.index_bound_six
#print axioms Erdos.Covering.sweepR5
#print axioms Erdos.Covering.window_layer_one
#print axioms Erdos.Covering.window_layer_two
#print axioms Erdos.Covering.window_layer_three
#print axioms Erdos.Covering.window_layer_four
#print axioms Erdos.Covering.window_layer_five
#print axioms Erdos.Covering.window_layer_six
#print axioms Erdos.Covering.mem_of_isAllPrimeMinusPow_of_le
#print axioms Erdos.Covering.setOf_isAllPrimeMinusPow_le
#print axioms Erdos.Covering.erdos_1142
#print axioms Erdos.Covering.setOf_isAllPrimeMinusPow_of_erdos_1142
#print axioms Erdos.Covering.not_infinite_setOf_isAllPrimeMinusPow_of_erdos_1142
