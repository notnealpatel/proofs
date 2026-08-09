/-
  Erdos/Covering/ErdosRows — OEIS A089654, the table
  `T(n, k) = 2n + 1 - 2^k` whose all-prime rows are Erdős' A039669
  restricted to odd values.

  Consumer module: the predicate layer lives in
  `Erdos.Covering.ErdosMinus2k`.

  GROUND TRUTH PINNING (fetched live 2026-07-30).

  OEIS A089654, name: "Table T(n,k), read by rows, related to a
  conjecture of P. Erdos (see A039669)." Keywords: easy,nonn,tabf.
  Formula (verbatim): "T(n, k) = 2*n+1-2^k, if T(n, k)>0." Listed rows
  (verbatim comments): row n=1: 1; n=2: 3, 1; n=3: 5, 3; n=4: 7, 5, 1;
  n=5: 9, 7, 3; n=6: 11, 9, 5; n=7: 13, 11, 7; n=8: 15, 13, 9, 1;
  n=9: 17, 15, 11, 3. In-entry conjecture (verbatim): "P. Erdos
  conjectures that T(n,k) are all primes for n = 3, 7, 10, 22, 37, 52
  and these are the only values of n with property . The conjecture has
  been verified for n up to 2^77. example : n=10; 19, 17, 13, 5 are all
  primes."

  All nine listed rows, the tenth row from the entry's own worked
  example, and the entry's first 29 `terms` in reading order are checked
  against `erdosRowList` in §2.

  THE POINT OF THE FILE. The entry states its conjecture as a claim about
  a table and cross-references A039669 without saying what the relation
  is. It is this: **A089654's conjecture is exactly A039669's conjecture
  restricted to odd m, under m = 2n + 1.** §3 proves the predicate half
  (`forall_prime_erdosRowList_iff_isAllPrimeMinusPow`), §4 proves the
  index half — `n ↦ 2n + 1` carries `{3, 7, 10, 22, 37, 52}` bijectively
  onto `{7, 15, 21, 45, 75, 105}`, which is exactly the odd part of
  `{4, 7, 15, 21, 45, 75, 105}` (4 being A039669's only even term) — and
  §7 derives the A089654 conjecture from
  `Erdos.Covering.erdos_1142` with **no new `sorry`**. What the OEIS
  entry offers as a cross-reference is thereby a machine-checked
  identification.

  Note the guard `0 < n`. The row of n = 0 is empty (`2·0 + 1 = 1` has no
  `k ≥ 1` with `2 ^ k < 1`), so "all entries of row 0 are prime" holds
  vacuously while `2 · 0 + 1 = 1` is not a term of A039669. This is the
  A089654-side shadow of the vacuity trap documented in
  `Erdos.Covering.ErdosMinus2k`; §3 exhibits it. The entry's own row
  indexing starts at n = 1, consistent with the guard.

  PRIOR ART. A sweep for a formalization of A089654 in
  google-deepmind/formal-conjectures, Mathlib, the Isabelle AFP,
  Coq/Rocq, Mizar, HOL Light and Metamath found none
  (orchestrator sweep, 2026-07-30). The A039669 statement itself *has*
  been formalized before — see the prior-art note in
  `Erdos.Covering.ErdosMinus2k`, which this file consumes.

  CONTENTS.
    § 1 `erdosRow`, `erdosRowList` (a row as a list, in the entry's
        reading order), and the row-membership / no-repeats facts.
    § 2 Ground truth: all nine rows listed by the entry, the tenth from
        its worked example, the first 29 terms in reading order, and the
        row lengths.
    § 3 The bridge, sorry-free: all-prime rows ⟺ `AllPrimeMinusPow`
        at `2n + 1`, and (for `0 < n`) ⟺ `IsAllPrimeMinusPow (2n + 1)`.
    § 4 The index bijection and the odd-part identification, sorry-free.
    § 5 Certificates for `n = 3, 7, 10, 22, 37, 52`, and negative
        controls at `n = 1, 2, 11`.
    § 6 The finite window at `n ≤ 499999999`, sorry-free, inherited
        from the `m ≤ 10 ^ 9` window of `Erdos.Covering.ErdosMinus2k`.
    § 7 The A089654 conjecture, derived from the archived
        `Erdos.Covering.erdos_1142` with no new `sorry`.
    § 8 Axiom audit.

  Axiom audit (2026-07-31, Lean 4.33.0-rc1, 26 declarations): this file
  introduces **no `sorry` of its own**. `erdos_a089654` and
  `setOf_forall_prime_erdosRowList_of_erdos_1142` report `sorryAx`
  through `Erdos.Covering.erdos_1142` alone; every other declaration
  reports a subset of {propext, Classical.choice, Quot.sound}. No
  `native_decide`, no `axiom`, no
  `@[csimp]`/`@[implemented_by]`/`@[extern]`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib
import Erdos.Covering.ErdosMinus2k

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 THE TABLE
-- ════════════════════════════════════════════════════════════════════

/-- **OEIS A089654**, `T(n, k) = 2n + 1 - 2 ^ k`, verbatim from the
entry's formula field.

The `ℕ` subtraction is totalized (it returns `0` once `2 ^ k ≥ 2n + 1`),
which is exactly the entry's own proviso "if T(n, k) > 0": every
statement below guards it with `2 ^ k < 2 * n + 1`, and no `k` outside
that range is part of row `n`. Row indices start at `k = 1`, matching
the entry's listed rows (`row n = 1 : 1`, i.e. `T(1,1) = 3 - 2 = 1`). -/
def erdosRow (n k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k

/-- Row `n` of A089654 as a list, in the entry's reading order
(`k = 1, 2, 3, …`, hence descending values). The exponent search bound
`2n + 2` is harmless: `2 ^ k < 2n + 1` already forces `k < 2 ^ k < 2n + 1`. -/
def erdosRowList (n : ℕ) : List ℕ :=
  ((List.range (2 * n + 2)).filter fun k => 0 < k ∧ 2 ^ k < 2 * n + 1).map (erdosRow n)

/-- **Row membership**: `erdosRowList n` consists of exactly the
`erdosRow n k` for the `k` with `1 ≤ k` and `2 ^ k < 2n + 1`. This is the
row-length fact in usable form. -/
theorem mem_erdosRowList {n x : ℕ} :
    x ∈ erdosRowList n ↔ ∃ k, 0 < k ∧ 2 ^ k < 2 * n + 1 ∧ erdosRow n k = x := by
  simp only [erdosRowList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨-, hk0, hk2⟩, rfl⟩
    exact ⟨k, hk0, hk2, rfl⟩
  · rintro ⟨k, hk0, hk2, rfl⟩
    have hklt : k < 2 * n + 2 := lt_of_lt_of_le Nat.lt_two_pow_self (by omega)
    exact ⟨k, ⟨hklt, hk0, hk2⟩, rfl⟩

/-- Inside a row the entries are pairwise distinct: `k ↦ 2n + 1 - 2 ^ k`
is injective on the range where the subtraction is not truncated. -/
theorem erdosRow_injOn {n k l : ℕ} (hk : 2 ^ k < 2 * n + 1) (hl : 2 ^ l < 2 * n + 1)
    (h : erdosRow n k = erdosRow n l) : k = l := by
  have hpow : (2 : ℕ) ^ k = 2 ^ l := by
    simp only [erdosRow] at h
    omega
  exact Nat.pow_right_injective le_rfl hpow

/-- Row `n` has no repeated entries, so its length is the number of
admissible exponents `k`. -/
theorem nodup_erdosRowList (n : ℕ) : (erdosRowList n).Nodup := by
  refine List.Nodup.map_on ?_ (List.Nodup.filter _ (List.nodup_range))
  intro k hk l hl h
  simp only [List.mem_filter, decide_eq_true_eq] at hk hl
  exact erdosRow_injOn hk.2.2 hl.2.2 h

-- ════════════════════════════════════════════════════════════════════
-- §2 GROUND TRUTH AGAINST THE OEIS ENTRY
-- ════════════════════════════════════════════════════════════════════

-- The nine rows the entry lists verbatim in its comments …
example : erdosRowList 1 = [1] := by decide
example : erdosRowList 2 = [3, 1] := by decide
example : erdosRowList 3 = [5, 3] := by decide
example : erdosRowList 4 = [7, 5, 1] := by decide
example : erdosRowList 5 = [9, 7, 3] := by decide
example : erdosRowList 6 = [11, 9, 5] := by decide
example : erdosRowList 7 = [13, 11, 7] := by decide
example : erdosRowList 8 = [15, 13, 9, 1] := by decide
example : erdosRowList 9 = [17, 15, 11, 3] := by decide

-- … and the tenth row, from the entry's own worked example
-- ("example : n=10; 19, 17, 13, 5 are all primes").
example : erdosRowList 10 = [19, 17, 13, 5] := by decide

-- The entry's `terms` field, first 29 entries, in reading order.
example :
    ((List.range' 1 10).map erdosRowList).flatten =
      [1, 3, 1, 5, 3, 7, 5, 1, 9, 7, 3, 11, 9, 5, 13, 11, 7, 15, 13, 9, 1, 17, 15, 11, 3,
       19, 17, 13, 5] := by decide

-- Row lengths (the `tabf` shape: lengths 1, 2, 2, 3, 3, 3, 3, 4, 4, 4).
example : (List.range' 1 10).map (fun n => (erdosRowList n).length) =
    [1, 2, 2, 3, 3, 3, 3, 4, 4, 4] := by decide

-- Degeneracy: the row of `n = 0` is empty. The entry indexes rows from
-- `n = 1`; §3 shows why the `0 < n` guard is load-bearing.
example : erdosRowList 0 = [] := by decide

-- ════════════════════════════════════════════════════════════════════
-- §3 THE BRIDGE TO A039669
-- ════════════════════════════════════════════════════════════════════

/-- **The bridge, exponent form.** Row `n` of A089654 is all-prime iff
the raw A039669 body holds at `m = 2n + 1`. Definitional: `erdosRow n k`
*is* `(2n + 1) - 2 ^ k`. -/
theorem forall_prime_erdosRow_iff (n : ℕ) :
    (∀ k, 0 < k → 2 ^ k < 2 * n + 1 → Nat.Prime (erdosRow n k)) ↔
      AllPrimeMinusPow (2 * n + 1) :=
  Iff.rfl

/-- **The bridge, list form.** Every entry of row `n` is prime iff the
raw A039669 body holds at `m = 2n + 1`. -/
theorem forall_prime_erdosRowList_iff (n : ℕ) :
    (∀ x ∈ erdosRowList n, Nat.Prime x) ↔ AllPrimeMinusPow (2 * n + 1) := by
  constructor
  · intro h k hk hlt
    exact h _ (mem_erdosRowList.mpr ⟨k, hk, hlt, rfl⟩)
  · intro h x hx
    obtain ⟨k, hk, hlt, rfl⟩ := mem_erdosRowList.mp hx
    exact h k hk hlt

/-- **The bridge, guarded exponent form** — the full iff between
A089654's row condition and A039669 membership. The hypothesis `0 < n`
is exactly what supplies A039669's guard `2 < 2n + 1`. -/
theorem forall_prime_erdosRow_iff_isAllPrimeMinusPow {n : ℕ} (hn : 0 < n) :
    (∀ k, 0 < k → 2 ^ k < 2 * n + 1 → Nat.Prime (erdosRow n k)) ↔
      IsAllPrimeMinusPow (2 * n + 1) := by
  rw [forall_prime_erdosRow_iff]
  exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

/-- **The bridge, guarded list form.** -/
theorem forall_prime_erdosRowList_iff_isAllPrimeMinusPow {n : ℕ} (hn : 0 < n) :
    (∀ x ∈ erdosRowList n, Nat.Prime x) ↔ IsAllPrimeMinusPow (2 * n + 1) := by
  rw [forall_prime_erdosRowList_iff]
  exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

-- The `0 < n` guard is load-bearing, and the reason is the A089654 shadow
-- of the A039669 vacuity trap: row 0 is empty, so it is vacuously
-- all-prime, while `2 · 0 + 1 = 1` is not a term of A039669.
example : ∀ x ∈ erdosRowList 0, Nat.Prime x := by decide
example : ¬ IsAllPrimeMinusPow (2 * 0 + 1) := fun h => absurd h.1 (by norm_num)

-- ════════════════════════════════════════════════════════════════════
-- §4 THE INDEX BIJECTION AND THE ODD PART OF A039669
-- ════════════════════════════════════════════════════════════════════

/-- `n ↦ 2n + 1` carries A089654's conjectured index set onto the odd
part of A039669. -/
theorem image_two_mul_add_one_eq :
    ({3, 7, 10, 22, 37, 52} : Finset ℕ).image (fun n => 2 * n + 1) =
      ({7, 15, 21, 45, 75, 105} : Finset ℕ) := by decide

/-- The index bijection, as an iff usable on an arbitrary `n`. -/
theorem mem_a089654_index_iff (n : ℕ) :
    n ∈ ({3, 7, 10, 22, 37, 52} : Finset ℕ) ↔
      2 * n + 1 ∈ ({7, 15, 21, 45, 75, 105} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- `{7, 15, 21, 45, 75, 105}` is exactly the odd part of A039669's
known terms. -/
theorem filter_odd_a039669 :
    ({4, 7, 15, 21, 45, 75, 105} : Finset ℕ).filter (fun m => ¬ 2 ∣ m) =
      ({7, 15, 21, 45, 75, 105} : Finset ℕ) := by decide

/-- … and `4` is the only even one. -/
theorem filter_even_a039669 :
    ({4, 7, 15, 21, 45, 75, 105} : Finset ℕ).filter (fun m => 2 ∣ m) =
      ({4} : Finset ℕ) := by decide

-- ════════════════════════════════════════════════════════════════════
-- §5 CERTIFICATES AND NEGATIVE CONTROLS
-- ════════════════════════════════════════════════════════════════════

/-- Row 3 = `[5, 3]`, all prime. (A039669: `2 · 3 + 1 = 7`.) -/
theorem forall_prime_erdosRowList_3 : ∀ x ∈ erdosRowList 3, Nat.Prime x :=
  (forall_prime_erdosRowList_iff_isAllPrimeMinusPow (by norm_num)).mpr isAllPrimeMinusPow_7

/-- Row 7 = `[13, 11, 7]`, all prime. (A039669: `15`.) -/
theorem forall_prime_erdosRowList_7 : ∀ x ∈ erdosRowList 7, Nat.Prime x :=
  (forall_prime_erdosRowList_iff_isAllPrimeMinusPow (by norm_num)).mpr isAllPrimeMinusPow_15

/-- Row 10 = `[19, 17, 13, 5]`, all prime — the entry's worked example.
(A039669: `21`.) -/
theorem forall_prime_erdosRowList_10 : ∀ x ∈ erdosRowList 10, Nat.Prime x :=
  (forall_prime_erdosRowList_iff_isAllPrimeMinusPow (by norm_num)).mpr isAllPrimeMinusPow_21

/-- Row 22 = `[43, 41, 37, 29, 13]`, all prime. (A039669: `45`.) -/
theorem forall_prime_erdosRowList_22 : ∀ x ∈ erdosRowList 22, Nat.Prime x :=
  (forall_prime_erdosRowList_iff_isAllPrimeMinusPow (by norm_num)).mpr isAllPrimeMinusPow_45

/-- Row 37 = `[73, 71, 67, 59, 43, 11]`, all prime. (A039669: `75`.) -/
theorem forall_prime_erdosRowList_37 : ∀ x ∈ erdosRowList 37, Nat.Prime x :=
  (forall_prime_erdosRowList_iff_isAllPrimeMinusPow (by norm_num)).mpr isAllPrimeMinusPow_75

/-- Row 52 = `[103, 101, 97, 89, 73, 41]`, all prime — the largest known.
(A039669: `105`.) -/
theorem forall_prime_erdosRowList_52 : ∀ x ∈ erdosRowList 52, Nat.Prime x :=
  (forall_prime_erdosRowList_iff_isAllPrimeMinusPow (by norm_num)).mpr isAllPrimeMinusPow_105

-- The four rows named in the docstrings above but not listed by the
-- entry, checked against `erdosRowList` (row 11 is the negative control
-- just below).
example : erdosRowList 11 = [21, 19, 15, 7] := by decide
example : erdosRowList 22 = [43, 41, 37, 29, 13] := by decide
example : erdosRowList 37 = [73, 71, 67, 59, 43, 11] := by decide
example : erdosRowList 52 = [103, 101, 97, 89, 73, 41] := by decide

-- The rows the conjecture excludes really are excluded: `1` is not prime
-- (rows 1 and 2 end in it) and `21 = 3 · 7` is not (row 11).
theorem not_forall_prime_erdosRowList_1 : ¬ ∀ x ∈ erdosRowList 1, Nat.Prime x := by decide
theorem not_forall_prime_erdosRowList_2 : ¬ ∀ x ∈ erdosRowList 2, Nat.Prime x := by decide
theorem not_forall_prime_erdosRowList_11 : ¬ ∀ x ∈ erdosRowList 11, Nat.Prime x := by decide

-- ════════════════════════════════════════════════════════════════════
-- §6 THE FINITE WINDOW (sorry-free)
-- ════════════════════════════════════════════════════════════════════

/-- **A089654's conjecture, verified for `n ≤ 499999999`.** Sorry-free:
inherited through the bridge from the kernel-checked A039669 window
`Erdos.Covering.mem_of_isAllPrimeMinusPow_of_le` at `m ≤ 10 ^ 9`
(`2 · 499999999 + 1 = 999999999`). The entry claims verification to
`n = 2 ^ 77`; that is a computation, not a proof. -/
theorem mem_of_forall_prime_erdosRowList_of_le {n : ℕ} (hn : 0 < n) (hle : n ≤ 499999999)
    (h : ∀ x ∈ erdosRowList n, Nat.Prime x) : n ∈ ({3, 7, 10, 22, 37, 52} : Finset ℕ) := by
  have hm : IsAllPrimeMinusPow (2 * n + 1) :=
    (forall_prime_erdosRowList_iff_isAllPrimeMinusPow hn).mp h
  have hmem := mem_of_isAllPrimeMinusPow_of_le (by omega) hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  omega

/-- The same window in set-equality form. -/
theorem setOf_forall_prime_erdosRowList_le :
    {n : ℕ | 0 < n ∧ n ≤ 499999999 ∧ ∀ x ∈ erdosRowList n, Nat.Prime x} =
      ({3, 7, 10, 22, 37, 52} : Set ℕ) := by
  ext n
  constructor
  · rintro ⟨hn, hle, h⟩
    have hmem := mem_of_forall_prime_erdosRowList_of_le hn hle h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨by norm_num, by norm_num, forall_prime_erdosRowList_3⟩,
      ⟨by norm_num, by norm_num, forall_prime_erdosRowList_7⟩,
      ⟨by norm_num, by norm_num, forall_prime_erdosRowList_10⟩,
      ⟨by norm_num, by norm_num, forall_prime_erdosRowList_22⟩,
      ⟨by norm_num, by norm_num, forall_prime_erdosRowList_37⟩,
      ⟨by norm_num, by norm_num, forall_prime_erdosRowList_52⟩]

-- ════════════════════════════════════════════════════════════════════
-- §7 THE A089654 CONJECTURE (no new `sorry`)
-- ════════════════════════════════════════════════════════════════════

/-- **The A089654 conjecture** (OEIS A089654 comment, pinned 2026-07-30:
"P. Erdos conjectures that T(n,k) are all primes for n = 3, 7, 10, 22,
37, 52 and these are the only values of n with property").

OPEN, but **not an independent `sorry`**: it is derived here from the
archived `Erdos.Covering.erdos_1142` through the §3 bridge and the §4
index bijection, so this file adds no `sorry` of its own. That
derivation is the content: A089654's conjecture is A039669's conjecture
restricted to odd `m`, and nothing more. -/
theorem erdos_a089654 {n : ℕ} (hn : 0 < n) (h : ∀ x ∈ erdosRowList n, Nat.Prime x) :
    n ∈ ({3, 7, 10, 22, 37, 52} : Finset ℕ) := by
  have hm : IsAllPrimeMinusPow (2 * n + 1) :=
    (forall_prime_erdosRowList_iff_isAllPrimeMinusPow hn).mp h
  have hmem := erdos_1142 (2 * n + 1) hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  omega

/-- A089654's all-prime rows as a set, granting `erdos_1142`. No new
`sorry`; `sorryAx`-dependent through `erdos_1142` alone. -/
theorem setOf_forall_prime_erdosRowList_of_erdos_1142 :
    {n : ℕ | 0 < n ∧ ∀ x ∈ erdosRowList n, Nat.Prime x} =
      ({3, 7, 10, 22, 37, 52} : Set ℕ) := by
  ext n
  constructor
  · rintro ⟨hn, h⟩
    have hmem := erdos_a089654 hn h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨by norm_num, forall_prime_erdosRowList_3⟩,
      ⟨by norm_num, forall_prime_erdosRowList_7⟩,
      ⟨by norm_num, forall_prime_erdosRowList_10⟩,
      ⟨by norm_num, forall_prime_erdosRowList_22⟩,
      ⟨by norm_num, forall_prime_erdosRowList_37⟩,
      ⟨by norm_num, forall_prime_erdosRowList_52⟩]

end Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §8 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

/-! ## Axiom audit

This file introduces no `sorry`. `erdos_a089654` and
`setOf_forall_prime_erdosRowList_of_erdos_1142` report `sorryAx` through
`Erdos.Covering.erdos_1142` alone; every other declaration rests on a
subset of `{propext, Classical.choice, Quot.sound}`. The subset check is
also the sound `native_decide` detector on this toolchain: a use would
surface as a per-declaration `*._native.native_decide.ax_*` axiom. There
is no `native_decide` in this file. -/

#print axioms Erdos.Covering.erdosRow
#print axioms Erdos.Covering.erdosRowList
#print axioms Erdos.Covering.mem_erdosRowList
#print axioms Erdos.Covering.erdosRow_injOn
#print axioms Erdos.Covering.nodup_erdosRowList
#print axioms Erdos.Covering.forall_prime_erdosRow_iff
#print axioms Erdos.Covering.forall_prime_erdosRowList_iff
#print axioms Erdos.Covering.forall_prime_erdosRow_iff_isAllPrimeMinusPow
#print axioms Erdos.Covering.forall_prime_erdosRowList_iff_isAllPrimeMinusPow
#print axioms Erdos.Covering.image_two_mul_add_one_eq
#print axioms Erdos.Covering.mem_a089654_index_iff
#print axioms Erdos.Covering.filter_odd_a039669
#print axioms Erdos.Covering.filter_even_a039669
#print axioms Erdos.Covering.forall_prime_erdosRowList_3
#print axioms Erdos.Covering.forall_prime_erdosRowList_7
#print axioms Erdos.Covering.forall_prime_erdosRowList_10
#print axioms Erdos.Covering.forall_prime_erdosRowList_22
#print axioms Erdos.Covering.forall_prime_erdosRowList_37
#print axioms Erdos.Covering.forall_prime_erdosRowList_52
#print axioms Erdos.Covering.not_forall_prime_erdosRowList_1
#print axioms Erdos.Covering.not_forall_prime_erdosRowList_2
#print axioms Erdos.Covering.not_forall_prime_erdosRowList_11
#print axioms Erdos.Covering.mem_of_forall_prime_erdosRowList_of_le
#print axioms Erdos.Covering.setOf_forall_prime_erdosRowList_le
#print axioms Erdos.Covering.erdos_a089654
#print axioms Erdos.Covering.setOf_forall_prime_erdosRowList_of_erdos_1142
