# PLAN: formalization campaign — state, handoff, and loop

Rewritten 2026-07-29 at the mid-campaign quota halt, after the first
commit drain. This file is the authoritative campaign state for the next
orchestrator. The dispatch/review/commit protocol lives in
`./Prompts/User/ORCHESTRATING`; the deliverable bar is `./STYLE.md`
(both read in FULL before acting). The original card set is
`Formalize/INDEX`.

## 1. Committed state (branch `notnealpatel-f5exp`)

Seven lanes are DONE — written, reviewed (style + vacuity), findings
fixed, built green, committed one per lane:

| Commit | File | What landed |
|---|---|---|
| 39af612 | `Proofs/Enumerative/IsZumkeller.lean` | A083207 predicate, decidable, half-σ form; coprime closure engine `IsZumkeller.mul_of_coprime : IsZumkeller m → m.Coprime n → IsZumkeller (m*n)` (positivity derivable, dropped per audit) |
| 5976abf | `Proofs/Enumerative/PalindromeRows.lean` | A267632 odd-case palindrome PROVED at `k ≤ n` (stronger than card's truncated range — endpoints kernel-verified, disclosed); `n = 2^j` intended sorry |
| f2cd3df | `Proofs/Erdos/Covering/Basic.lean` | Covering systems + proved decidable coverage equivalence; Erdős witness by kernel `decide` at L = 12 |
| 70c8faf | `Proofs/Erdos/CoveringNumber.lean` | Transversal number τ, junk/honest zeros pinned + characterized; 18 theorems |
| 867bd21 | `Proofs/BilinearComplexity/Capset.lean` | Char-3 bridge (distinctness as theorem), `capsetNumber = addRothNumber univ`; n = 0..2 exact, 9 ≤ a(3), 20 ≤ a(4) vs A090245 |
| 14cfacd | `Proofs/GroupCount/Structures.lean` | `GroupStructure n ≃ Group (Fin n)`, Fintype/DecidableEq; counts match A034383 (n = 3 count by `native_decide`, trust-noted) |
| 67b13d1 | `Proofs/NumberComplexity/Quasilog.lean` | A064097 def + complete additivity + `Nat.log 2 n ≤ a n` PROVED; 2.5·log upper bound intended sorry (HOLD tier) |

All committed axiom surfaces are exactly
`{propext, Classical.choice, Quot.sound}` (single disclosed exception:
the anonymous `native_decide` count example in Structures.lean:248).

**NOT yet committed** (deliberately): `lakefile.toml` (adds
`NumberComplexity`, `GroupCount` libs + defaultTargets), the seven
root aggregators (five modified `Proofs/<Lib>.lean` + the two new roots
`Proofs/NumberComplexity.lean`, `Proofs/GroupCount.lean`), this PLAN.md,
and all 28 remaining campaign `.lean` files: 6 unreviewed writer files
(§2), 6 LANE HALTED annotated stubs (§4), and 16 pristine
never-dispatched event-release stubs (`import Mathlib` +
`autoImplicit false` only — the §3 dispatch targets: MaxIrrepDegree,
Gnu, Submult, CdoIteration, DennisSurjectivity, GroupPerfect,
KnuthStolarsky, SlizkovDoubling, QuasilogChainGap, ShearAdditionChains,
CapsetSliceRank, BooleanRankGeneric, ErdosMinus2k, ErdosRows,
HamiltonBallinger, ComplexityPatterns).

**UPDATE — scaffolding landed** as `45bc8cf` (`all:` commit): lakefile
libs, all seven aggregators, and all 22 stubs. The committed aggregators
deliberately OMIT the import lines for the six §2 modules; those lines
exist only in the working tree. Convention: **each §2 lane commits
post-review as its `.lean` file PLUS its aggregator import line.** Still
uncommitted: this PLAN.md and the six §2 files. The full-build gate
passed at commit time (8820 jobs; intended sorries only).

## 2. Written, awaiting review — do NOT commit until reviewed

Writer reports were clean and axiom-audited in each case; the quota halt
killed or preempted their review pairs. Notes in `.tasks/main/docs/`.

- **W1** `NumberComplexity/AdditionChain.lean` — A003313: `IsAddChain`,
  `l` (subtype-indexed ⨅, attained), `l_two_pow`, `log_two_le_l`,
  decision procedure. One `decide +kernel` use, commented (NOT
  native_decide). Unblocks E3.
- **W2** `NumberComplexity/IntComplexity.lean` — A005245: `Expr` layer,
  noncomputable `complexity`, computable `complexityRec` + master
  equality; every concrete value kernel-decidable. Unblocks E9.
- **W8** `Enumerative/MeanDivisors.lean` — A114976: BOTH open OEIS
  observations PROVED (`a n = 2 ↔ n.Prime`; `Odd (a n) ↔ IsSquare n`)
  plus `a n ≡ τ(n) [MOD 2]`. Card's reflection involution is provably
  wrong; replaced by the mean-toggle involution (documented deviation —
  statements kept the mandated `/`-free shape).
- **W10** `Enumerative/FubiniMod.lean` — A000670 mod 2/4/16 PROVED
  against the existing `fubini`; general-k conjecture intended sorry;
  zero native_decide (dodged the imported native-backed simp lemma).
- **W11** `BilinearComplexity/BooleanRank.lean` — Boolean rank over a
  fresh `BoolSemiring` synonym. CRITICAL for consumers: Mathlib's `Bool`
  is xor-based 𝔽₂ — downstream (E6) MUST use `BoolSemiring`. Unblocks E6.
- **W9** `Enumerative/StanleyDigits.lean` — A003278: greedy =
  base-3-digits-{0,1} PROVED (44 decls, sorry-free), plus the Jeffery
  identities `3·a(n) = A191107 + 2`, `6·a(n) = A055246 + 5` and Bos's
  `A191107(n) = A003278(2n−1)` — all previously unattributed/conjectured
  in the OEIS entries. native_decide only in anonymous ground checks.
  Documented deviation: A055246 formalized via Jeffery's rule form, not
  the Cantor-interval definition.

Review protocol per lane: `vacuity-cop` + `reviewer` in parallel
(VACUITY_AUDIT grade for the def files W1/W2/W11), pointers not
content, orchestrator applies fixes, module rebuild, then commit in the
same per-lane style as §1.

## 3. Work that remains (dispatch DAG)

Ready NOW (def layer committed + reviewed):
- **E1** ← W5a: `A060938-schmidt-submult` → `Proofs/GroupTPP/MaxIrrepDegree.lean`
  — **TOP TARGET** (`sup` of max `charDegrees` over structures; engine
  `charDegrees_prod` at `Proofs/GroupTPP/CharDegreesMul.lean:274`; pin
  n = 0 sup; submultiplicativity carries `0 < m`, `0 < n`), and
  **W5b** `Proofs/GroupCount/Gnu.lean` (iso-class quotient; the
  native_decide-vs-certificates trust fork is a USER decision — the
  agent reports, never picks).
- **E4** ← W6: four Zumkeller lanes (stubs annotated; see §4).
- **E5** ← W12: `A236397-peebles` + SliceRank bridge → `CapsetSliceRank.lean`.
- **E7** ← W13: `A039669-erdos-minus-2k` (PIN the 2^128 bound from the
  entry) and `A089654-erdos-rows` → `Proofs/Erdos/Covering/`.
- **E8** ← W14: `A391599-erdos-lovasz` → `ErdosLovasz.lean` (carry
  `∅ ∉ F` in every statement; never `open Metric`).

Blocked on §2 reviews: **E3** ← W1 (KnuthStolarsky, SlizkovDoubling,
QuasilogChainGap, ShearEC T5 bridge), **E6** ← W11 (BooleanRankGeneric),
**E9** ← W2 (HamiltonBallinger, ComplexityPatterns).
Blocked on E1: **E2** ← W5b + USER trust-fork resolution (Submult
coprime case, CdoIteration, DennisSurjectivity, GroupPerfect).

Re-dispatch: **W4** `NumberComplexity/StepWalk.lean` (A014701) — writer
crashed on an API error with zero output; card self-contained.

HOLD (do not dispatch; reasons verified): A064097 2.5·log upper bound;
A267632 `n = 2^j`; A000001 non-coprime submultiplicativity; the EC
Mordell-Weil rank cards (needs a USER design decision on a rank
functional layer); A250109 (circuit-model design decision); A085805
(Sage computation first).

Backlog tier (after the above): A061256 Burnside, A092482/A093682,
A135908/A135909, A062733, `Nat.Practical` def lane (unlocks
A007691-coleman + Stewart).

## 4. Handoff conventions (established this session)

1. **LANE HALTED comments.** Every stub whose lane was stopped carries a
   leading `/- LANE HALTED (date, reason) ... -/` block documenting the
   card, state at halt, and what re-dispatch needs (currently: the four
   E4 Zumkeller files, `ErdosLovasz.lean`, `StepWalk.lean`). The
   re-dispatched writer replaces the whole file, comment included.
2. **Vacuity plaintext dumps.** An audit halted mid-run dumps partial
   findings as PLAINTEXT to `.tasks/main/docs/<ProofFileBaseName>.txt`
   (existing: `Structures.txt`, `Capset.txt`, `Quasilog.txt`). Completed
   audits use `review-vacuity-<Name>.md`; style reviews
   `review-style-<Name>.md`; writer notes `<Lib>-<Name>.md`. All under
   `.tasks/main/docs/` (untracked).
3. **leandoc env.** Every leandoc invocation needs the prefix
   `LEANDOC_DOT_LAKE=~/p/proofs/.lake` (broken otherwise; also recorded
   in agent memory). Put it in every subagent prompt that mentions
   leandoc.
4. **Ownership fences.** `lakefile.toml` and root aggregators
   (`Proofs/<Lib>.lean`) are orchestrator-owned. Writers write exactly
   ONE named file, never run git, never create Scratch files, build only
   their own module via `flock .lake/agent.lock lake build <Module>`
   (untruncated; retry on lock contention).
5. **Ground truth.** OEIS values live via `oeis show <seq>`, never model
   memory. A failed satisfiability/ground check is evidence of a wrong
   statement: halt the lane, escalate — never weaken silently.
6. **Commits.** `Proofs/<Lib>: <10-word summary` + short prose body;
   one commit per reviewed lane; scaffolding separate; no
   Co-Authored-By; NEVER push. Commit only at drain points, never while
   writers are mid-file.

## 5. Orchestration loop (next orchestrator, start here)

1. Read `Prompts/User/ORCHESTRATING` and `STYLE.md` in FULL. Check
   `goof sys` for headroom. This file is the campaign state; trust §1–§4.
2. Resume point: verify W9 StanleyDigits landed (writer report, module
   builds); commit the scaffolding (§1); full-build gate.
3. Per-lane loop: dispatch prover writer (one file; STYLE-first
   one-liner; fences of §4) → on return, vacuity-cop + reviewer in
   parallel → orchestrator fixes non-security findings itself →
   module green → lane done → fire the dependent event release (§3) →
   commit at the next drain point.
4. USER hard stops: the W5b gnu trust fork; any failed satisfiability
   example; any proposal to weaken/strengthen a card statement to make
   it provable; any security finding.
5. Priority when constrained — **USER directive: prioritize lanes that
   PROVE unproved OEIS comments/conjectures; those are the candidate
   novel results.** Order:
   a. §2 reviews (cheap; three of the six — MeanDivisors, FubiniMod,
      StanleyDigits — already contain proofs of OEIS-conjectured
      statements and are unbankable until reviewed+committed);
   b. E1 MaxIrrepDegree (A060938 submultiplicativity — proves an
      unproved OEIS comment; TOP TARGET);
   c. E4 ZumkellerTauSigma + siblings (Ianakiev A083207 observations,
      attack via the committed closure engine);
   d. E3 QuasilogChainGap (`0 ≤` part provable, A076142 comment) and the
      other OEIS-comment statement lanes (E9, E7, E8, E5, E6);
   e. W4 re-dispatch; backlog (mine `oeis` comments per the
      oeis-conjecture-mining practice for further unproved-comment
      targets).
   Novelty discipline: an elementary proof of an OEIS-conjectured
   comment is a "first recorded proof," NEVER a claimed novel result
   without a literature check (flash-agent sweep; see §6).

## 6. Novelty status of proved OEIS observations (literature checks)

Flash literature sweeps were dispatched 2026-07-29 for the four lanes
that proved OEIS-recorded observations. Verdicts land in this section;
update file docstrings/OEIS attributions accordingly.

- **A267632 odd-case palindrome (W7, committed)** — LIKELY-KNOWN:
  one-line corollary of Ramanathan 1944 / Barnes 1959 (Hadjicostas's
  2019 OEIS comments supply all ingredients); no explicit statement
  found anywhere; OEIS labels it "observation-conjecture." Frame as
  first explicit recorded proof; consider an OEIS attribution note.
- **A114976 observations (W8)** — NO-REFERENCE-FOUND for the parity ↔
  square claim and the `a(n) ≡ τ(n) mod 2` congruence: OEIS frames both
  as open conjecture; nothing in Ramanathan/Barnes-adjacent literature,
  A051293/A063776/A000016 entries, or the AlphaProof A051293 paper
  (arXiv:2605.22763) states them. W8's mean-toggle involution proof is
  the campaign's strongest first-proof candidate — PRIORITIZE its review
  and commit; consider an OEIS contribution + short note. The
  `a(n) = 2 ⟺ prime` claim is folklore (trivial from the definition).
- **A000670 mod 2/4/16 (W10)** — oddness KNOWN (Bala, OEIS 2013;
  elementary); mod 4 KNOWN (corollary of Barsky's congruence / Poonen
  1988, Fib. Quart. 26(1) 70–76); mod 16 LIKELY-KNOWN (periodicity and
  period bounds published — Barsky, Poonen, Asgari–Jahangiri JIS 21
  (2018) for r ≥ 2; the explicit `12 − (−1)^n` closed form may be
  unwritten but follows from published bounds + finite check). NOT a
  novelty candidate — cite Poonen 1988 and Barsky in the W10 docstring
  at review time.
- **A003278 Jeffery/Bos identities (W9)** — CONJECTURED-IN-OEIS-ONLY,
  no published proof; but PARI closed forms in the same entries (Ryde
  2021, van Tol 2026: all three sequences are affine images of
  `fromdigits(binary(n−1), 3)`) trivially imply them — the OEIS
  "Conjecture" labels are stale. W9 is thus the first rigorous proof of
  formally-unproved but de-facto-known identities: LOW novelty tier
  (below W8). The greedy = digits characterization is classical — cite
  Odlyzko–Stanley 1978 (unpublished Bell Labs memo, the standard
  reference; Szekeres-era origin) in the W9 docstring at review time.
