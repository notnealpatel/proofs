# STATE7 — publication triage

Distilled 2026-08-10 from `.tasks/main/docs/
triage-publishability.md` (opened 2026-07-31) and the
fourteen per-arc result sheets beside it (shard 7 of the
doc-retirement campaign). This file supersedes those docs.

Claim discipline, carried unchanged from the source sheet:

- [M] measured or retrieved directly (by the original
  orchestrator, or — where dated 2026-08-10 — by this
  distillation against the tree at `7b0e828`);
- [A] agent-reported, artifact fetched but not
  independently re-verified — a lead, re-fetch before
  citing;
- [O] open, nobody has checked.

Nine prior-art claims in this repo were believed and
turned out false (see the falsified-claims section).
**Every "first formalization" below is [A] unless marked
otherwise and must be re-fetched before it appears in a
submission.** Never upgrade [A] to fact.

Scale at triage time [M, 2026-07-31]: 135 non-`Scratch`
Lean files, 119 fully sorry-free, 2629 declarations,
60122 lines; 26 bare `sorry` across 16 files, all
disclosed as intended archives.

Calibration that drove the sort: across all 17 grading
documents, *no result was graded as new mathematics* [A];
the strongest verdicts are "first recorded proof" of
folklore and "first formalization in any assistant". But
that grading campaign covered the OEIS arc only —
`GroupTPP`, `Erdos20`, `BilinearComplexity`, `ShearEC`
were never novelty-graded, and that is where the surveys
found the original mathematics (two literature refutations,
two internal-task refutations, and one machine-checked exact
value). The tiering reflects that asymmetry.

## tier 1 — publishable, needs writing not research

### the Erdős-problem corpus (ITP / CPP / JAR)

Strongest single unit; the only bundle with original
mathematics that survived scrutiny. No manuscript exists.

| item | file | class |
|---|---|---|
| spread lemma (MNSZ route, 2824 ln) | `Proofs/Erdos/Erdos20/SpreadLemma.lean` | first formalization |
| refutation of Mishra v1 Lemma 3 | `Proofs/Erdos/Erdos20/Counterexample.lean` | original |
| refutation of spread-defect bridge, r* ≥ 4 | `Proofs/Erdos/Erdos20/SpreadDefect.lean` | original |
| shifted-family sunflower theorem | `Proofs/Erdos/Erdos20/ShiftedSunflower.lean` | first formalization |
| C(2n,n) not squarefree, elementary part | `Proofs/Erdos/Erdos175/NotSquarefree.lean` | first formalization |
| A(x) ≪ x^{1/2} (Tao's dyadic argument) | `Proofs/Erdos/Erdos440/LcmCount.lean` | first formalization |
| Schinzel–Szekeres 31/30, unconditional | `Proofs/Erdos/Erdos542/SchinzelSzekeres.lean` | first formalization |
| Alon–Friedland–Kalai via Chevalley–Warning | `Proofs/Erdos/Erdos715/RegularSubgraph.lean` | first formalization |
| Burr–Erdős k = 2 (HHP07 Thm 1(i)) | `Proofs/Erdos/Erdos880/BurrErdos.lean` | first formalization |
| Naslund–Sawin bound on m(n,3) | `Proofs/Erdos/Erdos857/NaslundSawin.lean` | first formalization |

Three things carry the paper:

1. The spread lemma has no prior formalization in any
   assistant [A] — AFP `Sunflowers` is classical
   Erdős–Rado only; Mathlib has no sunflower content.
   Corpora checked: AFP combinatorics index (54 entries),
   Mathlib `Combinatorics/SetFamily/` tree, GitHub search.
2. The Mishra refutation appears independent and first
   [A]. arXiv:2606.02667 v1 claimed full Erdős–Rado via a
   bridge lemma τ(S(F)) ≤ 3τ(F)²; v2 retitled to the
   shifted case with no erratum and no version note. No
   public record of the error was found. Witness: a
   17-set 4-uniform family on `Fin 20` with τ = 2 whose
   full shift endpoint is a 17-star.
3. erdosproblems.com listed `formalized: no` for #175,
   #440, #542, #715, #880 [M, 2026-07-31] — five solved
   problems formalized sorry-free here and never
   registered with the tracker. Still to do.

#857 status [M, 2026-07-31]: cold build exit 0; axiom
sweep over all 60 declarations clean; `nsMonomialCount`
matches the closed form on n = 0..12; bound first beats
2^n at n = 56 (Lean and Sage independently); independent
of `CapsetSliceRank`'s two archived sorries. Boundary to
state or imply a falsehood: Ahmadi–Norouzi
(arXiv:2606.30593) improved the polynomial factor to
O(n^{1/6}) [M, 2026-07-31]; #857 itself is open.

Spot-check 2026-08-10 [M]: all ten files exist; grep
shows zero `sorry` outside docstrings in each (grep-level
check, not a rebuild). The triage's prerequisite "wire
`Erdos.Erdos857.NaslundSawin` into a library root" is
already done — `Proofs/Erdos.lean:32` imports it.

### settling OEIS conjectures (JIS / INTEGERS)

Pointer sheet was `Manuscripts/Drafts/
first-proofs-and-opn-reduction.md`; that draft was
re-homed to `Documents/` in `7e2a9e2` and then absorbed
and deleted in `7b0e828` [M, 2026-08-10] — recover from
git if needed. Running order it fixed: lead A354741,
then A000670, then A114976 and A014701, odd-perfect
material demoted to a remark.

| result | file | verdict |
|---|---|---|
| A014701 Rebert keep-or-double walk | `Proofs/NumberComplexity/StepWalk.lean` | NRF, strongest first-proof claim |
| A354741 Boolean row-rank fraction → 1 | `Proofs/BilinearComplexity/BooleanRankGeneric.lean` | NRF |
| A000670 Bala totient-period, general k | `Proofs/Enumerative/FubiniMod.lean` | LK, first recorded proof |
| A114976 parity of mean-divisor subsets | `Proofs/Enumerative/MeanDivisors.lean` | NRF |

A014701 is the strongest: sorry-free, nontrivial
inductive potential argument, the most thorough novelty
sweep in the set, and OEIS still labeled it "Conjecture"
[A]. Carry the sweep's own warning verbatim: A354741
"should NOT be framed as a novel result — the
ingredients are standard and the statement is
unsurprising to experts."

### the matrix-multiplication corpus (ITP / CPP)

Large body of first formalizations, no manuscript,
nothing blocking one: `Strassen.lean` (R⟨2,2,2⟩ ≤ 7),
`Winograd.lean` (≥ 7, Hopcroft–Kerr), `SliceRank.lean`
(slice rank + Tao's diagonal lemma in full, over an
arbitrary field — what the #857 result consumes),
`Omega.lean`, `RankCalculus.lean`,
`KroneckerMatMul.lean`, the Cohn–Umans / Wedderburn
bridges, and the `AlgComplexity/Vp2/` circuit model with
the natural-proofs barrier. Needs one thesis sentence;
the natural one is "the polynomial method, end to end,
in Lean 4". `CapsetSliceRank`'s two sorries
(`peebles_conjecture`, CLP bound) are disclosed archives
outside the cone of everything else [M, 2026-07-31].

## tier 2 — each blocked on one named thing

(1) **TPP / Cohn–Umans corpus.** 25 first formalizations
(CU Thm 4.1, BCGPU barriers, Murthy 3.1/4.1,
Hedtke–Murthy, Nath–Das) plus originals: `WreathNg.lean`
refutes the originating task's conjecture n₂(G ≀ S_b) = 2
for b ≥ 5 (internal-task refutation; the correct answer
follows from Rasala / James–Kerber);
`IsoclinismInvariants.lean` refutes task Pf102's claim
that n_c is an isoclinism invariant and identifies k/|Z|
as the true one (internal-task refutation; the invariant
is attributed in-file to P. Hall);
`DihedralTPP/Sharpness.lean` gives β(D₁₂) = 16 — the
first machine-checked exact nonabelian TPP capacity; the
value appears in Hedtke–Murthy 2011 Table 1 row [12,4]
[M]. 28 of 29 files sorry-free. Blocked on a unifying thesis: decide whether
the paper is the library or the corrections.

(2) **Abelian direct factors increase TPP capacity
ratio.** `Proofs/GroupTPP/TPPLift.lean` (lift law,
sorry-free — exists, 0 sorry matches [M, 2026-08-10])
plus Sage evidence. Blocked on the open Hu9
author-verification gate, and on a reframe: the
manuscript itself concedes the refuted conjecture is
"project-internal, not a named open problem" [A], so the
publishable object is the exact β₀ values and the lift
law, with non-invariance as corollary.

(3) **Decidable fixed-divisor criterion for covered
exponential families.** `Documents/covering-criterion.md`
(re-homed from Manuscripts). Blocked on its own draft's
advice to wait: honest headline today is "a clean tool
for a closed problem class"; the `decide` ceiling is
L = 16384 with growth ≈ L^1.6, frontier systems sit at
L ≈ 10^4495. Write it after covering-certificates lands,
as that paper's infrastructure chapter. Secondary defect [M, 2026-07-31] **resolved** same day
in `f8eedec` (2026-07-31 19:31): §8 at line 536, §9 at
682, §10 at 803, and `Proofs/Erdos.lean:8` imports
`RankOfApparition`. No action needed.

(4) **Shear lower bound for modular inversion.**
`ShearEC/` arc sorry-free end-to-end to
`secp256k1_inversion_needs_256_shears`; original content
concentrated in `ShearQuadraticRank.lean`
(Strassen-style multiplicative-complexity bound, no
prior mechanization claimed [A]). Blocked on a venue and
a frame: the flagship bound is folklore formalized; the
paper must be about the shear model as a lower-bound
technique, not secp256k1.

(5) **Practical numbers / Stewart's structure theorem.**
`Proofs/Enumerative/StewartCriterion.lean` (full iff),
`Practical.lean`, `ZumkellerSigmaHalf.lean`,
`MultiperfectZumkeller.lean`. Verified [M, 2026-07-31]:
`Nat.coleman_multiperfect_practical` is the only
`sorryAx` carrier; all ten `coleman_instance_*` and nine
`zumkeller_instance_*` are unconditional. Blocked on
rescoping after a retraction: "first practical-number
formalization in any assistant" is **false** —
formal-conjectures landed `Nat.IsPractical` 2026-03-15.
What survives: the Stewart iff, plus the find that the
upstream predicate lacks a positivity guard and admits 0.
**Outstanding action [M, 2026-08-10]: the stale claim
still stands in `Formalize/A007691-coleman-practical.md`
("first practical-number formalization in ANY proof
assistant") and in `Formalize/INDEX:84-86` ("FIRST
practical-number formalization in any proof assistant")
despite the 2026-07-31 retraction. Correct both before
any citation.**

(6) **A051293 Cloitre expansion at every order.**
`Proofs/Enumerative/A051293/`. `cloitre_conjecture`
holds for every truncation order M, strictly stronger
than the published M = 5; 39 declarations axiom-clean
[M, 2026-07-31]. Blocked on framing against DeepMind's
AlphaProof Nexus proof (arXiv:2605.22763), first, and
recorded on OEIS 2026-06-18 [M, 2026-07-31]. The delta
is a routine extra expansion order; honest framing is a
short note, not a paper.

## blog-post tier

Several read better than tier-2 material; they are not
results. (1) The nine false prior-art claims and how
each was caught — the strongest, see below. (2) "Four
bounds, two mechanisms, one collapse"
(`Documents/four-way-chain.md`) — explicitly disclaims
any new theorem. (3) Rank of apparition as the right
axis, periodicity as the wrong one — for 13 of 18 primes
α(p) properly divides the Pisano period; doubles as the
covering paper's negative-result section. (4) The
doubly-conditional odd-perfect reductions — demote to a
remark, per their own drafts. (5) The small
first-recorded proofs collected (A005520 a(n) = n ⟺
n ≤ 5, the A348262 {1,+,^} layer, quasilog bounds,
Stanley-digit identities, doubling law, odd-row
palindromicity) — each LK or "NRF because the area is
unstudied"; collectively a post on stale OEIS conjecture
labels, individually not papers. (6) Engineering notes
from a 24 GB box: the zero-`native_decide` trust policy
with the kernel wall measured exactly, the covering
ceiling, and the `#eval` that enumerated 2^n and took
the box down twice [M, 2026-07-31]. (7)
`Documents/exotic-groups-for-mm.md` — develop the
VP-computability question into a real problem statement
or retire the file.

Excluded from tiers entirely: `Proofs/Scratch/`;
`Erdos/ErdosLovasz.lean` (statement archive, intended
sorries); `NederGap.lean`, `KnuthStolarsky.lean`,
`ShearAdditionChains.lean` (stubs); and
`PeelingSupport.lean`, which carries the one repo sorry
NOT documented as an intended archive
(`cover_outmass_even`) [A] — close it or disclose it.

## the nine falsified prior-art claims

Institutional memory about failure modes; substance
preserved verbatim from the triage sheet. Every one was
caught by *retrieving* an artifact, never by reasoning
or a second search.

1. "DeepMind's `1142.lean` uses `native_decide`." False
   — it is kernel `decide` inside
   `simp_all (config := { decide := true })`.
2. "GitHub search for 78557 in formal-conjectures
   returns 0 results." False — `selfridge_78557` exists
   and is proved. Wrong search scope.
3. "First proof-level use of covering systems in a proof
   assistant." False — plby/lean-proofs `Erdos275.lean`
   is sorry-free and uses covering systems.
4. Zsigmondy exception set "{1, 6, 31}." False — it is
   {1, 6}; 2³¹ − 1 is prime. A bounded-factoring Sage
   run stopped before the Mersenne prime.
5. "`systemd-run --user` does not enforce `MemoryMax` on
   this box." False — it does; wrong cgroup hierarchy.
6. "The A039669 raw predicate has two vacuous solutions
   {1,2}." False — three, {0,1,2}; the sweep enumerated
   from m = 1.
7. "First practical-number formalization in any proof
   assistant." False — formal-conjectures landed
   `Nat.IsPractical` 2026-03-15.
8. The retracted `1141→1148` filename-gap claim —
   reasoned about a directory listing under a guessed
   naming convention instead of retrieving the listing.
9. The A006285 / de Polignac OEIS-note candidate — false
   on both halves; the entry already carries infinitude
   with attribution.

The instructive shape: every failure was a search or an
inference standing in for a retrieval.

## per-arc result sheets

The fourteen sheets are writer self-reports; everything
below is [A] unless tagged [M]. All cited files exist in
the tree at `7b0e828` [M, 2026-08-10]; sorry counts
below are the sheets' claims, spot-checked by grep only.

**GroupCount/Gnu.lean** — `gnu n` defined as the card of
an isomorphism-class quotient of labeled group
structures on `Fin n`; sorry-free, 71 axiom checks
clean, zero `native_decide` [A]. Soundness +
completeness theorems make `gnu` count all groups of
order n. Values certified: gnu 0..5, 7, and `gnu p = 1`
for every prime; `gnu 2 = 1` certified twice by
independent routes. Institutional: the kernel wall for
*exact* gnu values is n = 2 — deciding n = 3 needs
recursion depth ≈ 1.59M and OOM-killed a 12 GB cgroup
after 114 s [A]; lower bounds via the `powOneCount`
invariant stay cheap far past the wall. Named follow-up:
reduced Latin-square enumeration (n = 6 drops from 6^43
raw tables to 80). Independent Sage brute force matches
A000001 through n = 6. Grade: infrastructure plus
certified values, not new mathematics.

**GroupCount/Submult.lean** — Lopes coprime
submultiplicativity `gnu i * gnu j ≤ gnu (i*j)` proved
sorry-free [A]; yields `2 ≤ gnu 12`, unreachable by
direct decision. Non-coprime case on HOLD and not stated
even as a sorry. Upstream candidate:
`nonempty_mulEquiv_fst_of_coprime` — Mathlib has no
coprime cancellation for direct products of finite
groups. Grade: clean first formalization of an OEIS
comment conjecture's coprime case.

**GroupCount/CdoIteration.lean** — CDO 2008 iteration
conjecture (`gnu` iterates reach 1) archived as the
single intended sorry, with a proved witness that the
`1 ≤ n` guard excludes a genuine counterexample at 0.
Stretch landed sorry-free: `gnu (p²) = 2` for all primes
via an elementary-abelian rank-2 classification —
closing an omission the Gnu sheet had listed as
not-cheap. Strata k ≤ 2 proved. Grade: archive plus one
real classification theorem.

**GroupCount/DennisSurjectivity.lean** — Dennis
gnu-surjectivity conjecture archived (one intended
sorry); A046057(1) = 1 and A046057(2) = 4 proved as
value-plus-minimality and `IsLeast` forms; a(3) = 75 out
of reach (needs gnu certified to 75). Grade: archive.

**GroupCount/GroupPerfect.lean** — A090052 group-perfect
conjectures archived (two intended sorries: no perfect
n ≥ 2; abundant density 0). Proved strata: deficiency
for all primes and 4, infinitude of deficients. No
positive abundant witness in-file (first is 32 with
gnu 32 = 51, beyond wall and classification). The
squarefree stratum is known (Hölder), so omitted, not
archived. Grade: archive.

**GroupTPP/MaxIrrepDegree.lean** — Schmidt's A060938
comment `a(m)a(n) ≤ a(mn)` proved sorry-free, via an
*equality* `maxCharDegree (G × H) = maxCharDegree G *
maxCharDegree H` [A]. Values a(0)..a(6) proved,
`4 ≤ a(36)` as nonvacuity; both directions of the
"a(n) = 1 iff abelian" comment at single-group level.
Upstream candidates: `sup_mem_of_ne_zero`,
`sup_bind_map_mul` (Multiset facts absent from Mathlib).
Grade: part of the tier-2 TPP corpus; the sheet claims
no novelty beyond first formalization.

**NumberComplexity/StepWalk.lean** — Rebert's A014701
conjecture proved in full as an iff:
`IsLeast {j | Reachable n j} k ↔ k + 2 =
(Nat.bits (n+1)).length + popCount (n+1)`; sorry-free,
`import Mathlib` only [A]; spot-check: file exists, no
sorry matches [M, 2026-08-10]. Optimality via a scalar
potential (`binCost`) invariant — strictly simpler than
the card's sketched interval-family route. Python BFS
confirms n ≤ 600. Grade: NRF, the strongest first-proof
claim in the OEIS arc (tier 1.2 lead candidate).

**NumberComplexity/ComplexityPatterns.lean** — A005520
record certificates a(1)..a(23) kernel-certified, plus
`a(n) = n ↔ n ≤ 5`, record strict monotonicity, and a
certified prime pattern on 2..23. Two OEIS claims
archived as intended sorries (Post prime window
(1438, 8206559]; Pegg/Karttunen mod-120 pattern), both
verified against the b-file computationally. Key
institutional memory: never certify DP tables as
`List ℕ` in the kernel (a(17) alone peaked 14.5 GB RSS);
pack the table into a single Nat literal (one byte per
entry) and re-derive the recurrence in-kernel by chunked
`decide +kernel` — 70 s total under a 12 GB fence.
Grade: certificates plus archives.

**NumberComplexity/HamiltonBallinger.lean** — {1,+,^}
complexity (A348262) built as a full mirror of the
IntComplexity layer with master realization theorem;
non-domination proved in both directions (n = 6 and
n = 8). The Hamilton–Ballinger finiteness claim archived
as the one intended sorry; card route: "none known".
Grade: layer plus archive.

**NumberComplexity/QuasilogChainGap.lean** — tier 1
proved sorry-free: `l n ≤ quasilog n` (A076142 ≥ 0) via
a formalized factor method (`factorChain`); `l_mul_le`
and `l_add_one_le` are reusable for any A003313 work.
Fourteen gap values certified including the first
nonzero terms gap 23 = gap 33 = 1, so the two definition
layers are provably distinct. The entry's "it seems"
limit (0.006 < c < 0.01) archived as the intended sorry.
Grade: first formalization plus archive.

**NumberComplexity/SlizkovDoubling.lean** — sanity bound
`l (2k) ≤ l k + 1` with sharpness on powers of two;
kernel value certificates l(3)..l(14); exact doubling
law on k ≤ 7. Slizkov's question archived as "the
answer is no" (`l k ≤ l (2k) + 1`, one intended sorry).
Independent C search: no deficit ≥ 1 for k ≤ 8192
(1.07e11 DFS nodes, values diff-clean against the
b-file on 1..16384); b-file scan k ≤ 50000 max deficit
0; first deficit-1 term is 375494703 per A230528.
Grade: archive with strong computational support.

**BilinearComplexity/BooleanRankGeneric.lean** — A354741
"it appears" comment is now a theorem:
`fullRowRankFraction_tendsto_one`, sorry-free, no
`native_decide`, union-bound mass exactly n²(3/4)ⁿ [A].
Semantics guardrails: ROW rank, not Schein rank (they
split at n = 4); Boolean (∨,∧) semiring, not 𝔽₂ (limit
0.2888 vs 1) — divergence exhibited in-kernel. Carry the
framing warning from tier 1.2. Grade: NRF, tier 1.2
lead per the absorbed running order.

**Enumerative/ZumkellerTauSigma.lean** — verdict HALT
with a machine-checked reason: any proof of Ianakiev's
A083207 τσ conjecture proves a new theorem about odd
perfect numbers. Blocking lemma (L): for every odd
perfect N with τ(N) = 2w, the number w·N is not a
perfect square; the implication conjecture ⟹ (L) is
kernel-checked in-file
(`not_isSquare_half_sigma_zero_mul_of_perfect`), with
Euler parity (`card_divisors_parity`) proved from
scratch. (L) is open; no known OPN result constrains
τ(N) modulo squares. This also kills the earlier
practical-number route in both directions. Sieve:
exactly 103 solutions d ≤ 10⁷, all even — but evenness
of all solutions is unprovable today. One intended sorry
(the verbatim card statement). Grade: the repo's
model hardness-reduction; high institutional value.

**Erdos/ErdosLovasz.lean** — statement archive for
Erdős #21 / A391599 (7 intended sorries; `g(3) = 6`
promoted to Tier 1, proved outright in §4) with a
headline correction: the card's and OEIS's "3n + O(1)"
speculation is REFUTED, not open — Sivashankar
(arXiv:2606.24878, Thm 1(ii)) gives g(r) ≥
((41−√19)/12 − ε)r with (41−√19)/12 = 3.0534… > 3; the
file proves the refutation sorry-free with the
literature bound as hypothesis. Constant correction: the
paper's (41−√19)/12 is strictly stronger than the 61/20
quoted on erdosproblems.com; the file archives the paper
constant and derives 61/20. Attribution correction 1:
"13 ≤ g(6)" is just [EL75] at n = 6, and [Ba21] is Barát
alone, not Barát–Wanless. Attribution correction 2:
erdosproblems.com/21 over-credits g(3) = 6 to [Tr14];
the true source is [FOT96] (JCTA 74 (1996) 33–42), as
recorded in ErdosLovasz.lean:84. τ bridge proved in both
directions; g(0..3) exact (g(3) = 6 sorry-free), g(3) ≤ 6
via a 6-edge witness verified twice computationally.
Grade: archive with three literature corrections worth
keeping.

## file dispositions

- .tasks/main/docs/triage-publishability.md — extracted: full tier sort, blockers, falsified-claims record, and outstanding actions preserved above.
- .tasks/main/docs/BilinearComplexity-BooleanRankGeneric.md — extracted: result, semantics guardrails, and framing warning preserved; tactic-level notes recoverable from the Lean file.
- .tasks/main/docs/Enumerative-ZumkellerTauSigma.md — extracted: HALT verdict, blocking lemma (L), and sieve counts preserved; the obstruction is also documented in the Lean file's docstrings.
- .tasks/main/docs/Erdos-ErdosLovasz.md — extracted: refutation headline, constant and attribution corrections, witness provenance preserved.
- .tasks/main/docs/GroupCount-CdoIteration.md — extracted: archive status and gnu(p²) = 2 stretch preserved; instance-search gotchas dropped as low value.
- .tasks/main/docs/GroupCount-DennisSurjectivity.md — extracted: archive status and moa values preserved.
- .tasks/main/docs/GroupCount-Gnu.md — extracted: kernel-wall measurements, trust policy, and reduced-Latin-square follow-up preserved.
- .tasks/main/docs/GroupCount-GroupPerfect.md — extracted: archive status and scope decisions preserved.
- .tasks/main/docs/GroupCount-Submult.md — extracted: theorem, Mathlib-gap upstream candidate, and HOLD status preserved.
- .tasks/main/docs/GroupTPP-MaxIrrepDegree.md — extracted: theorem, ground checks, and Multiset upstream candidates preserved.
- .tasks/main/docs/NumberComplexity-ComplexityPatterns.md — extracted: certificates, open archives, and the packed-Nat-table kernel pattern preserved.
- .tasks/main/docs/NumberComplexity-HamiltonBallinger.md — extracted: layer summary and archived finiteness claim preserved.
- .tasks/main/docs/NumberComplexity-QuasilogChainGap.md — extracted: tier-1 proof route, certified gaps, and reusable lemma pointers preserved.
- .tasks/main/docs/NumberComplexity-SlizkovDoubling.md — extracted: archive status and independent search outcome (max deficit 0 to 8192/50000) preserved.
- .tasks/main/docs/NumberComplexity-StepWalk.md — extracted: full-proof status and statement-design rationale preserved.
