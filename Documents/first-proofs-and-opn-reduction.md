# Settling OEIS conjectures by formal verification

*(Working title. The previous one — "Two first proofs and an odd-perfect
reduction, from OEIS conjectures, formally verified" — described §§1–3
only, and is stale now that §§5–6 are promoted and §3 is recommended for
demotion to a remark. Pick the final title after the §8.1 running order
is fixed; if that recommendation is taken the paper is about A354741,
A000670, A114976 and A014701, and the odd-perfect material is a remark.)*

**STATUS: POINTER SHEET (updated 2026-07-31).** Accurate file pointers and
calibrated novelty claims only — the maintainer reviews this and writes the
paper from it. Claim discipline: "first recorded proof," never "novel
mathematics" without literature grounding. Pointers for §§1–3 were verified
2026-07-30; §§5–6 were promoted out of the ledger 2026-07-31, with their
pointers read off the files and their OEIS and prior-art claims checked
against live entries and retrieved papers the same day. A running-order
recommendation is in §8.1.

**This is one of three drafts.** The covering material that was §4 now
lives in `covering-criterion.md`, and the frontier work it points to in
`covering-certificates.md`; see the §4 stub for the division of labour.
The single-arc `PLAN.md` at the repo root scopes the *covering* extension
lanes with measured costs and belongs to those two drafts, not this one;
fold it back into `Formalize/INDEX` when that arc closes. The campaign
PLAN.md was retired into `Formalize/INDEX` (commit `9ce3a87`) and the
novelty content it carried for Result I is inlined in §1.3.

**Claim-discipline warning, earned the hard way, and it applies to all
three drafts.** During the covering sweep, **seven** prior-art or fact
claims were believed and turned out false — including two asserted by the
orchestrator. Every one was caught only by fetching the artifact
directly, never by reasoning or by a second search. Before citing any
prior-art claim from any of these sheets, re-fetch the artifact.
`.tasks/main/docs/novelty-ErdosCovering.md` §4 lists the first six; the
seventh is the retracted `1141→1148` filename-gap claim, dissected in
`covering-criterion.md` §3.2. Its failure mode is the instructive one: it
reasoned about a directory listing under a guessed naming convention
instead of retrieving the listing. A subsequent agent also reported
formal-conjectures as containing *no* covering-system files at all — also
false, and also produced by searching rather than fetching. Retrieve the
tree (`api.github.com/repos/.../git/trees/main?recursive=1`); do not
infer it.

An eighth, caught in-flight on 2026-07-31 and worth the same billing:
the ledger row for §5 claimed it "retires Conjecture labels at A000670,
A354242, A002050." Reading the three entries shows it touches **one**,
and only half of that one's comment. Ledger rows are not evidence; they
are unverified summaries of unverified summaries.

A **ninth**, caught later the same day and the same genre as the
seventh: `novelty-Practical.md` claimed "first formalization of
practical numbers in any proof assistant," listing "GitHub" among the
swept corpora — without fetching google-deepmind/formal-conjectures,
the very repo the covering sweep in this corpus was citing that same
week. Upstream has had `Nat.IsPractical`
(`FormalConjecturesForMathlib/NumberTheory/PracticalNumbers.lean`)
since 2026-03-15 and a *proved* `factorial_isPractical`
(`ErdosProblems/18.lean`) since 2026-04-13 — verified twice by
independent recursive tree enumeration. The ledger carries the dated
retraction; the surviving claim is "first formalization of Stewart's
criterion and the Coleman layer" (§9). Corollary for method: a corpus
listed as swept is not swept until the artifact is fetched, even when
— especially when — the same corpus is being cited elsewhere in the
project.

Candidate venues (USER decision pending): JIS, INTEGERS, or an ITP/CPP
formalization-track case study. Related-work anchor to verify at writing time:
AlphaProof A051293 paper (arXiv:2605.22763).

**A051293 subsumption note (2026-07-31).** The in-tree
`Counting.lean:cloitre_conjecture (M)` proves Cloitre's asymptotic
expansion of A051293 with Fubini-number coefficients at *general* M,
sorry-free; the DeepMind paper's `target_theorem_0` proves only M = 5
via a hard-coded quintic. `Proofs/Enumerative/A051293/Cloitre.lean`
(new) derives their exact statement as a corollary, pins the in-tree
definition to OEIS terms 1..10 by kernel `decide` (previously zero
ground-truth anchors — the real gap), and documents that Cloitre's
general-m phrasing on the entry is false as written (the o-term's
placement inside the prefactor forces `fubini(m+1) = 0`; his explicit
M = 5 instance shows the intended reading). This is a related-work
*upgrade*: the machine-checked result here strictly subsumes the
published theorem the anchor cites. Also note the paper's expansion
coefficients tie A051293 to A000670 — a cross-arc link between §5's
Fubini layer and the A051293 layer that neither draft previously
recorded.

---

## 1. Result I — A114976: parity of mean-divisor subsets detects squares

`a(n)` = number of nonempty divisor subsets of `n` containing their own
arithmetic mean (stated `/`-free via `IsMeanDiv`). Proved sorry-free:
`Odd (a n) ↔ IsSquare n`; the sharper `a(n) ≡ τ(n) (mod 2)`; and
`a(n) = 2 ↔ n prime` (folklore tier, completeness only). Source: OEIS
A114976 unattributed "It appears that..." observations.

### 1.1 Pointers

- File `Proofs/Enumerative/MeanDivisors.lean`, commit `6677024`.
- Defs: `IsMeanDiv` (:48), `meanDivSubsets` (:73), `a` (:78),
  `meanSubsets` (:112).
- Theorems: `a_modEq_card_divisors` (:239),
  `odd_card_divisors_iff_isSquare` (:294), `odd_a_iff_isSquare` (:318),
  `a_eq_two_iff_prime` (:420).
- Ground checks `a(1..10)` vs live entry, in-file.

### 1.2 Mechanism (one line, for the paper's remark)

Mean-toggle involution: each divisor `m | n` contributes an odd count of
mean-`m` subsets; toggling `m`'s membership pairs off everything else. The
OEIS ROUTE's reflection involution is provably wrong — a documented deviation
worth a remark.

### 1.3 Novelty claim — NO-REFERENCE-FOUND (first-proof candidate)

Sweep 2026-07-29 (inlined here from retired PLAN.md §6): the parity ↔ square
claim and the `a(n) ≡ τ(n) mod 2` congruence are framed as open conjecture by
OEIS; nothing in Ramanathan/Barnes-adjacent literature, the A051293/A063776/
A000016 entries, or the AlphaProof A051293 paper (arXiv:2605.22763) states
them. The campaign's strongest first-proof candidate. Re-run a fresh sweep at
submission time.

## 2. Result II — A014701: Rebert's keep-or-double walk

Walk: first step length 1; before each later step, keep or double the current
length; steps add to position. Proved sorry-free: the minimal step count
0 → n is `⌊log₂(n+1)⌋ + popcount(n+1) − 1` (= Chandah-sutra count `a(n+1)`),
in additive normal form `k + 2 = (Nat.bits (n+1)).length + popCount (n+1)`
for the least `k`, with load-bearing guard `1 ≤ n` (the n = 0 junk
coincidence is documented in-file — cautionary example for a methodology
remark). Source: OEIS A014701, Jean-Marc Rebert, 2025-05-15, labeled
"Conjecture" in-entry as of 2026-07-30.

### 2.1 Pointers

- File `Proofs/NumberComplexity/StepWalk.lean`, commit `fa83e94`.
- Defs: `popCount` (:70), `binCost` (:75), `Reach` (:219),
  `Reachable` (:225).
- Key lemmas: `binCost_mul_pow_add` (:167), `binCost_add_pow_le` (:199),
  `binCost_le_of_reachable` (:274), `reach_of_binary` (:284),
  `exists_isLeast_reachable` (:347).
- Main theorems: `rebert_conjecture` (:368, IsLeast iff),
  `rebert_conjecture_iInf` (:395).
- Mechanism: scalar potential (`binCost`) + exchange lemma for the lower
  bound; binary expansion realizes the upper bound.
- Independent verification: vacuity audit BFS'd three rival readings of
  Rebert's prose (85/85 vs 42/73/42); 86/86 published terms kernel-checked
  (`.tasks/main/docs/review-vacuity-StepWalk.md`).

### 2.2 Novelty claim — NO-REFERENCE-FOUND (first-proof candidate)

Sweep `.tasks/main/docs/novelty-StepWalk.md`: classical ingredients are Knuth
TAOCP §4.6.3 and Gruber–Holzer MFCS 2021 (Lemma 8); A056792's
add-1-or-double walk is structurally distinct (worth a remark distinguishing
the models). UNCHECKED: SeqFan archives — check before submission.

## 3. Result III (conditional) — A083207 implies an odd-perfect constraint

The verbatim Ianakiev conjecture (OEIS A083207, 2020-04-24: d > 1, d ∣ k,
τ(d)·σ(d) = k ⟹ k Zumkeller; OPEN, the file's one disclosed sorry) implies
blocking lemma (L): no odd perfect number N — writing τ(N) = 2w, w odd,
forced by Euler parity — has w·N a perfect square. Epistemic status, candid
and disclosed at every declaration site: conditional twice over (takes the
open conjecture as hypothesis; vacuously true if no OPN exists) — the same
genre as published OPN constraint theorems. For these instances even the
necessary parity 2 ∣ σ(k) is equivalent to (L), so practical-number
machinery cannot bypass the obstruction.

### 3.1 Pointers

- File `Proofs/Enumerative/ZumkellerTauSigma.lean`, commit `8eef184`,
  namespace `ZumkellerTauSigma`.
- Reduction theorems: `two_dvd_sigma_one_of_odd_perfect` (:854),
  `not_isSquare_half_sigma_zero_mul_of_perfect` (:884).
- Supporting layer (unconditional, sorry-free): `card_divisors_parity`
  (:679), `isZumkeller_two_pow_mul_iff` (:326) plus Neder's criterion,
  `sum_divisors_mod_two_of_isSquare`, `sigma_zero_mod_four_eq_two`,
  `exists_sigma_zero_eq_two_mul_odd_of_perfect`.
- Audit trail: `.tasks/main/docs/review-vacuity-ZumkellerTauSigma.md`
  (SOUND; hypothesis byte-identical to card; perfection/oddness proved
  load-bearing by counter-probes), `review-style-ZumkellerTauSigma.md`,
  writer notes `Enumerative-ZumkellerTauSigma.md` (sieve to 10⁷: 103
  qualifying d, all conjecture-consistent).

### 3.2 Novelty claim — NO-REFERENCE-FOUND on all three questions

Sweep `.tasks/main/docs/novelty-ZumkellerTauSigma.md` (2026-07-30):

- **(L) itself:** NO-REFERENCE-FOUND — the constraint involves the p-adic
  valuation of τ(m²) at the Euler prime, outside Euler form, Steuerwald,
  Touchard, and prime-counting bounds. Sources checked: Wikipedia/MathWorld
  OPN, Ochem–Rao page, Dandapat–Hunsucker–Pomerance 1975, Nielsen 2006,
  12 targeted searches.
- **The A083207↔OPN connection:** NO-REFERENCE-FOUND — no OEIS comment,
  preprint, or Zumkeller paper (Rao–Peng 2009, Somu et al. 2023, Mahanta
  et al. 2020) mentions it.
- **Hardness claim:** ACCURATE as a hedged literature statement.
- Framing: "a previously unrecorded connection between Ianakiev's Zumkeller
  observation and odd-perfect-number structure theory" — the reduction is a
  short argument; the value is the connection plus the machine-checked
  certificate. UNCHECKED (low risk): Guy UPINT B1, Dickson vol. I, SeqFan.

## 4. Result IV — the covering-system arc → SPLIT OUT

**Moved 2026-07-31 to `Manuscripts/Drafts/covering-criterion.md`.** This
section recommended its own material become a separate ITP/CPP submission
and then kept it inline for two revisions; that split is now executed. Do
not re-add it here.

Why it is not in this paper: it settles no OEIS conjecture, contains zero
new mathematics (Erdős 1950, Sierpiński 1960, Selfridge 1962 throughout),
and its comparison points are Cowles–Gamboa 2011 and Dahmen–Hölzl–Lewis
ITP 2019 rather than the OEIS-conjecture framing of §§1–2 and §§5–6. See
§8.1 for the running-order consequence.

The three drafts and their division of labour:

| draft | content | venue |
|---|---|---|
| this sheet | A354741, A000670, A114976, A014701; A083207 as a remark | JIS / INTEGERS |
| `covering-criterion.md` | the decidable criterion, Erdős 1950, Sierpiński, Riesel, archives | ITP / CPP / JAR |
| `covering-certificates.md` | compositional coverage certificates; Erdős #2 lower bound | ITP / CPP, after the above |

`covering-criterion.md` §7 and `covering-certificates.md` §3 carry the
measured `decide` ceiling that ties the second and third together. Extension
lanes with costs: `PLAN.md` (repo root).

## 5. Result V — A000670: Bala's totient-period conjecture (a 1988 theorem, machine-checked)

**Promoted out of the §9 ledger 2026-07-31.**

**Scope correction, made the same day the section was written.** The
ledger row said this "retires live Conjecture labels at A000670, A354242,
A002050," and the first draft of this section repeated it. Reading the
three entries shows that is **wrong**, in two independent ways:

- **A354242 and A002050 are different sequences.** A354242 has e.g.f.
  `1/√(5 − 4·exp x)`; A002050 counts simplices in the barycentric
  subdivision of an `n`-simplex. Bala posted the *same* conjecture on
  each (2022-07-07 and 2023-08-03), but a theorem about `fubini` proves
  neither. Our formalization touches **one** label, not three.
- **Even at A000670 it settles only half the comment.** Bala's comment
  has two sentences. The second is strictly stronger and is *not*
  proved: "More generally, we conjecture that the same property holds
  for integer sequences having an e.g.f. of the form `G(exp(x) − 1)`,
  where `G(x)` is an integral power series." A354242 and A002050 are
  instances of that general class — which is presumably why Bala posted
  it three times.

Verified against the live entries 2026-07-31; all three comments are
still labelled "Conjecture". State the contribution as **one entry, one
half of one comment**, and note that the general e.g.f. statement is the
interesting open question this work does *not* answer.

Peter Bala conjectured (A000670 comments, 2022-07-08) that for every
`k ≥ 1` the residue sequence `fubini n % k` is eventually periodic with
period dividing `φ(k)`. Proved for general `k`, sorry-free. The entry's
own worked example — "modulo 16 we obtain `[1, 1, 3, 13, 11, 13, 11,
13, 11, 13, …]`, with an apparent period of 2 beginning at a(4)" —
matches the file's closed form `(fubini n : ZMod 16) = 12 − (−1)ⁿ` for
`3 ≤ n`.

### 5.1 Pointers

- File `Proofs/Enumerative/FubiniMod.lean` (680 lines), commit `c37e31e`;
  instances `51d04f5`. Imports `Enumerative.Fubini`.
- Main theorem `fubini_mod_eventuallyPeriodic_conjecture` (:607):
  `∀ k, 1 ≤ k → ∃ N P, P ∣ Nat.totient k ∧ 0 < P ∧
   ∀ n, N ≤ n → fubini (n + P) ≡ fubini n [MOD k]`.
- Fixed-modulus warm-ups with closed forms: `fubini_odd` (:166) and
  `fubini_mod_two_eventuallyPeriodic` (:348) for `k = 2`;
  `fubini_add_two_modEq_four` (:332) / `_mod_four_` (:355) for `k = 4`;
  `fubini_add_two_modEq_sixteen` (:323) / `_mod_sixteen_` (:362) for
  `k = 16`, where `(fubini n : ZMod 16) = 12 - (-1)^n` for `3 ≤ n`.
- Ground values kernel-checked against live OEIS data
  `1, 1, 3, 13, 75, 541, 4683, 47293, …`. No `native_decide`.

### 5.2 Mechanism

Modulo `k` the truncated sum `c k n = ∑_{j<k} 2^{k-1-j}·jⁿ` satisfies the
same recurrence as `fubini` and starts at `2^k - 1`, giving
`(2^k - 1)·fubini n ≡ c k n (mod k)`. At a prime power `p^m` the
right-hand side is `φ(p^m)`-periodic once `n ≥ m` (Euler for `j` coprime
to `p`, nilpotence otherwise), the left factor is invertible, and a
Chinese-remainder induction glues prime-power periods into `φ k`.

### 5.3 Novelty — LIKELY-KNOWN. Do not oversell this one.

The file says so itself and the manuscript must not contradict it: *"it
is a formalization, not a novelty claim."* The route is
**B. Poonen, *Periodicity of a combinatorial sequence*, Fibonacci
Quarterly 26 (1988), 70–76** — his Theorem 2 is the prime-power
statement, and his **Theorem 6 identifies the exact period modulo `r` as
an lcm of prime-power periods, which divides `φ r`**. That is Bala's
conjecture. The prime-power case is also Barsky's theorem via p-adic
analysis of the e.g.f. `1/(2 - eˣ)`.

So the mathematics is Poonen's, from 1988, and the honest contribution is
three-part and none of it is a theorem: **(a)** the *connection* — that
Bala's 2022 conjecture is a corollary of Poonen 1988 appears nowhere on
the entries, which is why the labels are still live; **(b)** an
elementary self-contained proof (`poonen_congr` by strong induction, not
via Good's real-analytic series identity); **(c)** the machine check.

**Consequence for framing:** the *novelty* is weak (Poonen has the
mathematics) and, after the scope correction above, the *impact* is one
OEIS label rather than three. Lead with the Bala→Poonen connection, which
appears on none of the entries; never with "we proved Bala's conjecture."

**VERIFIED 2026-07-31 against the paper itself**
(`References/poonen/paper.txt`), and the attribution holds:

- *Poonen's sequence is the Fubini numbers.* He defines `ω(n)` as "the
  number of possible outcomes in a race among `n` horses with multiple
  ties permitted", notes it was "first studied by A. Cayley", e.g.f.
  `1/(2 − eˣ)`. That is A000670.
- *Theorem 2* is the prime-power statement: for `q = p^m`, `ω(n + φ(q)) ≡
  ω(n) (mod q)` for all `n ≥ m`.
- *Theorem 6* gives the exact period modulo general `r` as an lcm of
  prime-power periods, and the paper draws the consequence explicitly:
  "even when `r` is odd, the period modulo `r` is not necessarily `φ(r)`,
  **although it must be a factor of `φ(r)`**." Smallest witness: `r = 15`,
  period `lcm(φ3, φ5) = 4`, not `φ(15) = 8`.
- *Barsky is confirmed too* — "Analyse p-adique et suites classiques de
  nombres" (1982, rev. 1995), `References/s05barsky/paper.txt`,
  Proposition 1: `g_{n+(p−1)p^h} ≡ g_n (mod p^h)` for `n ≥ h`, for the
  same e.g.f. `1/(2 − eˣ)`, proved by p-adic analytic continuation
  (Amice's criterion) rather than congruences.

So Bala's A000670 conjecture **is not a conjecture** — it has been a
theorem since 1988, and independently since ~1982. The LK grade is right
and the label at A000670 is simply stale.

*Caveat for the writing stage:* both local copies are OCR'd scans with
mangled symbols (`ω`→`oo`, `φ`→`<f>`). Verbatim quotation in a
submission must come from the publisher's PDF, not these files.

### 5.4 The interesting open problem is the one we did NOT prove

Bala's second sentence — the general class of integer sequences with
e.g.f. `G(exp(x) − 1)` for `G` an integral power series — is **open**,
and neither Poonen nor Barsky settles it. Poonen's paper concerns exactly
one sequence. Barsky's Theorem 10 does treat sequences with e.g.f.
`∑ bₙ(eˣ − 1)ⁿ`, but it establishes p-adic analyticity — hence eventual
periodicity mod `p^h` for *some* period — and not the sharper claim that
the period divides `φ(p^h)`. That gap is real and sequence-dependent.
A354242 and A002050 sit in the gap.

This is worth a paragraph in the paper, because it inverts the natural
reading: the part we formalized is 38 years old, and the part still open
is the part Bala posted three times. A formalization of the *general*
statement — or a counterexample to it — would be a genuine result, and
the `poonen_congr` machinery in the file is the natural starting point.
(Not-checked-to-exhaustion: whether any later paper proves the general
class. Sweep before claiming it is open.)

## 6. Result VI — A354741: almost every Boolean matrix has full row rank

**Also promoted out of the §9 ledger**, where it was flagged "strongest
un-scoped candidate." Unlike §5 this one carries a real
NO-REFERENCE-FOUND grade, and it is the strongest first-proof claim in
the corpus.

The fraction of `n × n` matrices over the Boolean semiring
`({0,1}, ∨, ∧)` with full Boolean row rank tends to `1`. Source: the
A354741 comment, unattributed, hedged as *"it appears from some
empirical computations."*

### 6.1 Pointers

- File `Proofs/BilinearComplexity/BooleanRankGeneric.lean` (654 lines),
  commit `3ec26ec`. Sorry-free.
- Defs: `RowLE` (:87), `rowsSum` (:103), `rowSpan` (:124),
  `BoolRowRankLE` (:147), `boolRowRank` (:175, `Nat.find` witnessed at
  `r = m`), `fullRowRankCount` (:439),
  `fullRowRankFraction` (:508, noncomputable, ℝ-valued).
- Main theorem `fullRowRankFraction_tendsto_one` (:562):
  `Tendsto fullRowRankFraction atTop (nhds 1)`.
- Load-bearing steps: `boolRowRank_eq_of_antichain` (:280),
  `card_filter_rowLE_le` (:326), `card_dominatedRowLE_le` (:393, at most
  `n·n·3ⁿ·2^(n(n−2))` bad matrices), `one_sub_le_fullRowRankFraction`
  (:523), `card_boolMatrix` (:431).
- Bridge to the committed rectangle-cover rank of `BooleanRank.lean`:
  `boolRank_le_boolRowRank` (:267).

### 6.2 Mechanism

Rows that are nonzero and pairwise incomparable under domination span
freely, so full row rank fails only when some row dominates another. A
union bound over ordered pairs gives the `(3/4)ⁿ` per-pair factor, hence
at most `n²(3/4)ⁿ` bad fraction, and the limit is a squeeze between
`1 − n²(3/4)ⁿ` and `1`.

### 6.3 Novelty — NO-REFERENCE-FOUND, and the contrast is the hook

Sweep `.tasks/main/docs/novelty-BooleanRankGeneric.md` (2026-07-30):
first recorded proof of the A354741 comment. The file is candid that the
ingredients are individually standard and the contribution is their
combination plus the machine check — say that, do not claim a novel
discovery.

What makes it worth reading is the **semiring dependence**, which is
sharp and countable-in-one-line: over `𝔽₂` the full-rank fraction tends
to `∏(1 − 2⁻ⁱ) ≈ 0.2888` (A048651); over the Boolean semiring it tends
to `1`. Genuinely distinct neighbours, all checked and none subsuming
this: Komlós 1967 and Kahn–Komlós–Szemerédi 1995 (real rank → 1);
Pourmoradnasseri–Theis 2017 (Schein rank, `(1−o(1))n` a.a.s.);
Izhakian–Janson–Rhodes 2015 (triangular rank `O(log n)`). The file also
pins the divergence concretely: A354741 row 3 is `1, 49, 306, 156` while
the 𝔽₂-rank triangle A286331 row 3 is `1, 49, 294, 168`, both computed
in-kernel over the same 512 matrices.

## 7. Artifact / reproducibility

- Branch `f5exp`; result commits `6677024`, `fa83e94`, `8eef184`; toolchain
  `leanprover/lean4:v4.33.0-rc1` + Mathlib (`lakefile.toml`,
  `lean-toolchain`). Full build green 2026-07-30 (8826 jobs).
- Axiom surfaces: exactly `{propext, Classical.choice, Quot.sound}` for all
  cited sorry-free theorems; the A083207 file additionally carries its one
  disclosed open-conjecture sorry (`sorryAx` confined to it). No
  `native_decide` in any result file (re-verified 2026-07-30; note the
  toolchain mints per-declaration `*._native.native_decide.ax_*` axioms,
  never `Lean.ofReduceBool` — the allowlist subset check is the sound
  detector).
- Methodology pointers for §-writing: `STYLE.md`; adversarial vacuity audits
  under `.tasks/main/docs/review-*`; statement-integrity discipline
  (satisfiability witnesses, junk-value guards, discriminating ground
  checks, live-OEIS ground truth).
- **Freeze before aging out:** `.tasks/` is untracked. Appendix material to
  copy into the paper repo at writing time: `novelty-StepWalk.md`,
  `novelty-ZumkellerTauSigma.md`, and the ledger docs cited in §8 (all
  under `.tasks/main/docs/`).

## 8. USER decisions pending

- Venue (§ header).
- OEIS contribution notes, first tier: A114976 and A014701 (entries still
  label the proved statements as conjectures); an A083207 comment noting
  the OPN connection.
- OEIS notes, folklore tier (optional, weaker): Lopes coprime case
  (A000001), A064097 log₂ lower bound (entry still says "Conjecture"),
  A003278/A191107/A055246 stale "Conjecture" label cleanup, A348262
  formula/subadditivity comment for the bare entry. **Bala's conjecture
  has been REMOVED from this tier and promoted to §5**; note that the
  parenthetical here previously read "retires Conjecture labels at
  A000670, A354242, A002050" and that is false — see §5, it is one entry
  and half of one comment.
- Scope: A354741 is now **§6**, no longer a ledger row.

### 8.1 Re-ranking recommendation — read this before choosing a venue

The paper as currently ordered leads with its three weakest items. What
the 2026-07-31 verification pass established, ranked by what a referee
would find worth reading:

**Lead with §6 (A354741).** It is the only NO-REFERENCE-FOUND item in the
corpus whose statement is both nontrivial and unconditional, and it has a
hook that survives compression to one sentence: *the limiting full-rank
probability is `∏(1 − 2⁻ⁱ) ≈ 0.2888` over `𝔽₂` and `1` over the Boolean
semiring.* Sharp, memorable, semiring-dependent, and pinned concretely by
the divergence at `n = 3` (`1, 49, 306, 156` vs `1, 49, 294, 168`).

**Then §5 (A000670)** — reframed, and the ranking is now settled rather
than provisional. The Poonen retrieval came back **confirming** the
attribution (§5.3), so §5 does not become the paper's lead: it is a short
"this conjecture is 38 years older than it looks" note plus a machine
check, whose real deliverable is retiring one stale OEIS label and
recording the Bala ⟸ Poonen/Barsky connection that appears on none of
the entries.

The genuinely interesting thing §5 surfaces is §5.4 — Bala's *general*
`G(exp(x) − 1)` conjecture is open, covered by neither Poonen nor
Barsky, and it is the statement he posted three times. Say so. A paper
that settles one 1988-known instance and then cleanly delimits what
remains open is more useful than one that implies it settled all three.

**Then §§1–2 (A114976, A014701).** Solid JIS-tier first proofs of stated
OEIS conjectures. They belong in the paper; they should not open it.

**Demote §3 (A083207 ⟹ OPN) to a remark.** It is conditional twice over —
it assumes an open conjecture *and* is vacuous if no odd perfect number
exists — so nothing can be built on it and it discharges nothing. The
connection is worth one paragraph and an A083207 OEIS comment. It is not
worth a numbered result section, and leading a paper with two conditional
layers invites the referee to discount everything after it.

**Split §4 out, and do not write its paper yet.** The recommendation to
separate stands and is strengthened: §4's comparison point is
Dahmen–Hölzl–Lewis ITP 2019 and Cowles–Gamboa 2011, not OEIS. But its
honest headline today is *"a clean tool for a closed problem class"* —
true, useful, and not interesting. Every classical target in reach
(Sierpiński, Riesel, Erdős 1950, Brier, base-b) has small `lcm`, and the
2026-07-31 measurement shows the `decide` route dies between `L = 16384`
and `L = 65536`, by memory exhaustion rather than time. That is a
structural ceiling, not a tuning problem.

What would make §4 publishable is the item now scoped in
`Manuscripts/Drafts/covering-certificates.md`: a compositional coverage
certificate, and with it the first machine verification of a
minimum-modulus record system. Write §4's paper *after* that lands, with
the criterion as its infrastructure chapter rather than its headline.

**Venue consequence.** If the running order becomes §6, §5, §1, §2 with
§3 as a remark, the paper is a JIS/INTEGERS submission about settling
OEIS conjectures, and §4 is not in it at all. That is a cleaner and more
defensible object than the current five-way mix.
- **Scope, covering arc (§4): separate ITP/CPP paper, or a result in this
  one?** My recommendation is separate — its contribution is a reusable
  criterion and its comparison point is Dahmen–Hölzl–Lewis ITP 2019, not
  the OEIS-conjecture framing of §§1–3. Extension lanes are scoped in
  `PLAN.md`; lanes F (Hough–Nielsen 2019) and the Mathlib-upstream
  question both need an explicit yes/no before dispatch.
- ~~OEIS note, new candidate: **A006285** (de Polignac)~~ — **WITHDRAWN.**
  The claim that `erdos_1950_not_two_pow_add_prime` "is precisely the
  infinitude statement for that sequence … stronger than the folklore-tier
  items above" was false on both halves; see the retraction in §4.2. The
  entry already carries infinitude with attribution (Crocker; Van der
  Corput 1950; Erdős 1950; Habsieger–Roblot 2006), so there is nothing to
  contribute mathematically, and the ranking was backwards — label
  retirement changes an entry's epistemic status, this does not. Demote to
  a formalization link at most, or drop.

## 9. Ledger — other landed results (out of scope; pointers + verdicts)

Full sweep docs under `.tasks/main/docs/` (all re-verified or freshly swept
2026-07-30). Tiers: NRF = NO-REFERENCE-FOUND (first-proof candidate),
LK = LIKELY-KNOWN (first recorded proof is the ceiling), KC =
KNOWN-CLASSICAL (no claim).

| Result | File / commit | Verdict | Sweep doc |
|---|---|---|---|
| A354741 Boolean row-rank fraction → 1 | `BilinearComplexity/BooleanRankGeneric.lean` / `3ec26ec` | **NRF** — strongest un-scoped candidate | `novelty-BooleanRankGeneric.md` |
| A348262 {1,+,^} master equality + pow-subadditivity | `NumberComplexity/HamiltonBallinger.lean` / `f499c59` | **NRF** (modest: entry/norm unstudied, statements easy) | `novelty-HamiltonBallinger.md` |
| A005520 record `a(n) = n ⟺ n ≤ 5` iff | `NumberComplexity/ComplexityPatterns.lean` / `3559616` | **NRF** (small) | `novelty-ComplexityPatterns.md` |
| A060938 Schmidt submultiplicativity | `GroupTPP/MaxIrrepDegree.lean` / `3d513bd` | LK (Serre/Isaacs corollary) | `novelty-MaxIrrepDegree.md` |
| A076142 `l ≤ quasilog` | `NumberComplexity/QuasilogChainGap.lean` / `bf57463` | LK (Scholz–Brauer ingredients) | `novelty-QuasilogChainGap.md` |
| A000001 coprime submultiplicativity (Lopes) | `GroupCount/Submult.lean` / `559c2f0` | LK folklore (Ren arXiv:2405.04794 says "clear," no proof anywhere) | `novelty-Submult.md` |
| A064097 log₂ lower bound | `NumberComplexity/Quasilog.lean` / `67b13d1` | LK (entry still labels it "Conjecture," Wilson 2013) | `novelty-Quasilog.md` |
| A267632 odd-row palindromicity | `Enumerative/PalindromeRows.lean` / `5976abf` | LK (Hadjicostas + necklace symmetry, unrecorded) | `novelty-PalindromeRows.md` |
| A046057(1)=1, A046057(2)=4 minimality pins | `GroupCount/DennisSurjectivity.lean` / `24c754e` | LK (values published, no recorded proofs — possibly first rigorous proofs of any A046057 entries) | `novelty-GroupCountE2.md` |
| A003278/A191107/A055246 identities | `Enumerative/StanleyDigits.lean` / `1b6db2c` | LK (stale OEIS labels; de-facto-known via in-entry closed forms) | `novelty-StanleyDigits.md` |
| A000670 Bala totient-period conjecture — **proved in full** (general k; file sorry-free) | `Enumerative/FubiniMod.lean` / `c37e31e` (instances `51d04f5`) | LK — first recorded proof of the general statement; ingredients Poonen 1988/Barsky are classical; "Conjecture" labels still live at A000670/A354242/A002050 | `novelty-FubiniMod.md` |
| Nat.Practical layer + Stewart step; Coleman conjecture archived (multiperfect ⟹ practical, odd part OPN-hard) | `Enumerative/Practical.lean` / `6b4d720` | KC math (Srinivasan 1948, Stewart 1954) — formalization-first (see below); Coleman itself NRF-outside-OEIS, open | `novelty-Practical.md` |
| **Coleman⟹no-odd-perfect reduction** (machine-checked, conditional) + weak Coleman (even perfect ⟹ practical, Euler direction re-proved locally) | `Enumerative/Practical.lean` / `d84bcbc` | **NRF-connection** — apparently unrecorded (conjecture has zero literature); same genre as §3, thinner (one step from folklore evenness); ranks below A083207. A007691 OEIS-comment candidate | `novelty-Practical.md` |
| Stewart's structure theorem, full iff (both directions) | `Enumerative/StewartCriterion.lean` / `55a8a97` | KC math (Stewart 1954, Sierpiński 1955) — the flagship formalization theorem of the practical-number arc; the arc-level "first-in-any-system" claim is RETRACTED (see repo-level claims below), the Stewart iff itself remains first | `novelty-Practical.md` |
| σ-parity bridge (practical ⟹ Zumkeller iff 2∣σ, = Bhaskara Rao–Peng 2013 Prop. `proppraczu`) + Perfect ⟹ Zumkeller (unconditional, incl. hypothetical odd) + Coleman ⟹ A007691 ⊆ A083207 for n > 1 (conditional, ZTS-genre) + nine instance certificates; Ianakiev σ-half conjecture archived as statement | `Enumerative/ZumkellerSigmaHalf.lean` + `Enumerative/MultiperfectZumkeller.lean` / working tree 2026-07-31 | **KC — consolidation, cite Bhaskara Rao–Peng, NO novelty claim on the bridge.** The Coleman ⟹ A007691-Zumkeller *ordering* composes three OEIS-recorded facts and appears unrecorded as such — one-sentence remark, not a result | `novelty-Practical.md` CORRECTION |
| Peebles poster Thm 4: A236397(n) ≤ A090245(n), sorry-free; sliceRank bridge chain; Peebles conjecture + CLP bound archived | `BilinearComplexity/CapsetSliceRank.lean` / `01060f0` | LK — first-recorded-complete-proof candidate (poster states it bare, thesis PDF dead, not subsumed by ASU/Naslund–Sawin); formalization claims route-scoped only (Dahmen–Hölzl–Lewis ITP 2019 has EG in Lean 3) | `novelty-CapsetSliceRank.md` |
| A003313 low-range doubling law | `NumberComplexity/SlizkovDoubling.lean` / `cb84c0f` | KC (Knuth; boundary at k = 191 per A086878) | `novelty-SlizkovDoubling.md` |
| gnu(p²) = 2 | `GroupCount/CdoIteration.lean` / `46feb48` | KC math (Netto 1882) — formalization-first (see below) | `novelty-GroupCountE2.md` |
| Every prime group-deficient | `GroupCount/GroupPerfect.lean` / `0c5e638` | KC math; "group-perfect" vocabulary orphaned to A090052 | `novelty-GroupCountE2.md` |

**Repo-level formalization-novelty claims** (distinct from math novelty;
relevant to an ITP/CPP framing):

- First proof-assistant treatment of integer complexity in any system
  (no Lean/Coq/Isabelle formalization of Mahler–Popken, A005245, A005520,
  or variants found) — `novelty-ComplexityPatterns.md`.
- ~~First formalization of practical numbers in any proof assistant~~ —
  **RETRACTED 2026-07-31** (ninth claim-discipline entry, see the
  warning block): formal-conjectures has `Nat.IsPractical` (2026-03-15)
  and a proved `factorial_isPractical` (2026-04-13). Mathlib proper
  remains clean (leandoc miss + package grep). **Surviving claim:**
  first formalization of Stewart's criterion (both directions), the
  σ-characterization layer, weak Coleman, the Coleman archive, and the
  OPN-hardness reduction — none has an upstream counterpart. Upstream's
  definition also lacks a positivity guard (`IsPractical 0` holds);
  agreement for `0 < n` is machine-checked, a documented upstream-PR
  hook — `novelty-Practical.md` CORRECTION section.
- The classification→count gap: Mathlib and recent Lean papers (Harper–Wu
  arXiv:2501.09769; Li Xiang arXiv:2606.26141) classify p²/p³ groups but
  nobody formalizes gnu; the gnu function and its certified values appear
  unique to this project — `novelty-GroupCountE2.md`.
- First formalization of the general **fixed-divisor criterion for
  covered exponential families** in any proof assistant, and first
  machine-checked proof of Erdős 1950 — §4, `novelty-ErdosCovering.md`.
  Wording deliberately not "the general covering-system criterion": the
  hypothesis is *coverage*, not `IsCoveringSystem` (see §4.1), and the
  loose phrasing claims more than the theorem states. Explicitly NOT
  claimed: priority on covering-system definitions (DeepMind has one,
  and applies it in the sorry'd `erdos_7`), on proof-level use of
  covering systems (plby/lean-proofs `Erdos275.lean` is sorry-free), or
  on the concrete Sierpiński/Riesel numbers (ACL2 2011 has both).
- **Terminology caveat, unresolved.** "Fixed divisor" classically
  (Bouniakowsky/Schinzel) means a single `d` dividing *every* value of a
  family; here no such `d` exists, since the covering primes each divide
  only some terms. The standard name for `{3,5,7,13,19,37,73}` is a
  *covering set*. `FixedDivisor.lean` / `IsFixedDivisorSystem` /
  `fixedDivisors` are therefore at odds with established usage — cheap to
  rename now, expensive if a referee raises it.

**Queue implication surfaced by the FubiniMod sweep — RESOLVED same day:**
the general-k sorry was discharged (`c37e31e`) via an elementary
Poonen-style truncation argument (no p-adics); the file is now sorry-free.
