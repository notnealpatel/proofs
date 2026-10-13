import NumberComplexity.ComplexityPatterns

/-!
# Quarantined admissions

The original source and disclosure documentation is retained below as historical context.
Descriptions of the original file refer to its pre-quarantine layout: independent proven
infrastructure now lives in the imported production module; the admissions and their
admission-dependent consequences live only here. No proof closure is claimed.
-/

/-
  NumberComplexity/ComplexityPatterns — record values of integer
  complexity (OEIS A005520): `a(n)` = the smallest number whose
  Mahler–Popken complexity (A005245, `NumberComplexity.complexity`)
  equals `n`, and the two patterns asserted in the A005520 entry.

    · `exists_le_complexityRec_eq` / `exists_complexityRec_eq` /
      `exists_pos_complexity_eq`
        — discrete intermediate-value property of the norm (it steps
          up by at most one, `‖m+1‖ ≤ ‖m‖ + 1`, and is unbounded,
          `2·m ≤ 2^‖m‖`), hence surjectivity: every `n` is a
          complexity value, so the record `smallestOfComplexity n`
          is well defined via `Nat.find`.
    · `smallestOfComplexity n`
        — A005520: least `m` with `complexityRec m = n` (equivalently
          `complexity m = n` by the master theorem of IntComplexity).
          JUNK VALUE: `smallestOfComplexity 0 = 0` (pinned), inherited
          from `complexity 0 = 0`.
    · order/spec API — `complexityRec_smallestOfComplexity`,
      `smallestOfComplexity_le`, `smallestOfComplexity_eq_iff`,
      `le_smallestOfComplexity` (`n ≤ a(n)`),
      `smallestOfComplexity_le_of_le_complexityRec`,
      `smallestOfComplexity_injective`,
      `smallestOfComplexity_strictMono` (the record sequence is
      strictly increasing),
      `smallestOfComplexity_eq_self_iff` (`a(n) = n ↔ n ≤ 5`).
    · packed table `tblData` / `tbl` (private)
        — kernel-checkable table `‖0‖ … ‖719‖` packed into a single
          natural number, one byte per value; the A005245 recurrence
          is re-derived for every row inside the kernel by four
          `decide +kernel` chunk checks, and
          `smallestOfComplexity_eq_of_tbl` turns one scan into a
          record certificate. No `native_decide` anywhere: the
          trusted base stays the kernel. (A `List ℕ` table is
          infeasible here: `O(N³)` kernel reduction blows a 12 GB
          memory budget at table size ~167.)
    · record certificates — `smallestOfComplexity_one` …
      `smallestOfComplexity_twentyThree`, kernel-checked against the
      live OEIS A005520 data (`oeis show A005520` and b-file
      b005520.txt, pulled 2026-07-30): a(1..23) = 1, 2, 3, 4, 5, 7,
      10, 11, 17, 22, 23, 41, 47, 59, 89, 107, 167, 179, 263, 347,
      467, 683, 719.
    · `smallestOfComplexity_prime` — the certified-range restriction
      of the prime pattern: `a(n)` is prime for `2 ≤ n ≤ 23` outside
      the composite records `a(4) = 4`, `a(7) = 10`, `a(10) = 22`.
    · the two OPEN pattern claims of the entry, stated exactly and
      left as INTENDED, DISCLOSED sorries:
        (i)  after 1438 = 2·719, all terms through 8206559 = a(53)
             are prime (J. V. Post 2006);
        (ii) all known terms a(45) = 590399 … a(89) = 872573642639
             are ≡ −1 (mod 120) (E. Pegg Jr 2001 / A. Karttunen 2015).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/

set_option autoImplicit false

namespace NumberComplexity

/-! ## 6. The open pattern claims of the A005520 entry

Both claims below are the card's claims (i) and (ii), stated exactly
as the OEIS entry asserts them. Each is a FINITE, decidable-in-
principle statement about record values that have been computed in
the literature (Pegg 2001, Post 2006, Iraids 2011 b-file) but lie far
beyond kernel `decide` reach (the window of claim (i) starts at
a(26) = 1439 and runs to a(53) = 8206559; claim (ii) runs to
a(89) = 872573642639). No structural explanation is known for either
pattern. The `sorry`s are INTENDED and disclosed; they are the open
content of the card. -/

/-- OPEN — card claim (i), OEIS A005520 (J. V. Post, Apr 07 2006):
"After 1438 = 2·719, all elements through 8206559 are primes." Every
record value in the window `(1438, 8206559]` is prime. Per the
b-file (pulled 2026-07-30) the terms in this window are
a(26) = 1439 … a(53) = 8206559, so the hypotheses are jointly
satisfiable (at `n = 26`, per data — itself beyond kernel reach).
The claim is finite: `n ≤ a(n)` (`le_smallestOfComplexity`) bounds
the indices concerned by `n ≤ 8206559`. -/
theorem smallestOfComplexity_prime_of_1438_lt {n : ℕ}
    (h1 : 1438 < smallestOfComplexity n)
    (h2 : smallestOfComplexity n ≤ 8206559) :
    Nat.Prime (smallestOfComplexity n) := by
  sorry

/-- OPEN — card claim (ii), OEIS A005520 (E. Pegg Jr, Apr 10 2001;
range clarified by A. Karttunen, Dec 14 2015): all known terms
a(45) = 590399 through a(89) = 872573642639 are ≡ −1 (mod 120).
The index domain `45 ≤ n ≤ 89` is nonempty, and the pattern genuinely
starts at 45: a(44) = 540539 ≡ 59 (mod 120) per the b-file (pulled
2026-07-30). -/
theorem smallestOfComplexity_mod_120 {n : ℕ} (h45 : 45 ≤ n) (h89 : n ≤ 89) :
    smallestOfComplexity n % 120 = 119 := by
  sorry

end NumberComplexity
