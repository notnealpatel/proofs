Session 4 picks up after session 3 built the
formalization foundation layer. Context docs
live in .tasks/f5exp/docs/: the master plan is
formalization-roadmap.md; three campaign
analyses (*-analysis.md) carry constraints on
downstream claims — read them if you need to
make a novelty or publication assertion, but
they are not your focus. Your focus is forward
progress.

Where session 3 landed, all verified on disk
(lake build green, zero sorries in new work):

Pl7 (bilinear complexity core) — COMPLETE.
Four sorry-free files under
Proofs/Proofs/BilinearComplexity/ (835 lines):
Basic.lean (Tensor k a b c, rank, matMulTensor),
RankCalculus.lean (subadditivity, Kronecker
submultiplicativity, cyclic symmetry
definitional, GL invariance over CommSemiring),
Flattening.lean (n² ≤ R⟨n,n,n⟩ over
CommRing + Nontrivial),
Strassen.lean (R⟨2,2,2⟩ ≤ 7 by kernel decide).

Pl8 (character-degree foundation) — COMPLETE.
charDegrees sorry replaced with choice-free
definition via isotypicLengthMultiset ℂ[G].
Both counting theorems sorry-free:
Σ dᵢ² = |G| and #irreps = #ConjClasses G.
CharDegrees.lean: 30 sorries → 0. Two new
files: Wedderburn.lean (564 lines),
GroupAlgebraCenter.lean (199 lines, class-sum
center basis over CommSemiring).

Pl9 (TPP unification) — COMPLETE. Unified
capacity API: TripleProductPropertyR (right-
quotient, matching all literature) with
inversion bridge to left form, β(D₁₂) = 16
exact, rho0 moved to TPP layer, Hedtke-Murthy
Thm 3.1 as computational interface. Sorry-free.

New agent template: ~/.goof/agents/postdoc.tmpl
— identical to prover.tmpl but model:
claude-opus-4-8[1m]. Session 3 provers were
Fable 5; postdoc exists to test whether Opus
4.8 suffices for the next campaigns (cheaper,
probably adequate for bookkeeping-grade proofs,
uncertain for hard case analysis).

What the DAG shows ready (do not trust this
paragraph — read `goof tasks ready`): Pl10
(post-Wedderburn Xlib burndown, ~12 real sorry
obligations now attackable, agent: planner),
plus three legacy cards Pf3, Pf4, Ep542 from
prior sessions. Pl10 was wired by the Pl8
planner with a self-contained brief including
triage-first instructions and scope guards.

Three campaigns are NOT yet in the DAG and
need planning:

1. **Omega definition (roadmap priority 3).**
   Define omega := sInf {x | ∀ᶠ n, R⟨n,n,n⟩
   ≤ n^x}, prove 2 ≤ omega ≤ 3 from Pl7's
   results, then Murthy Thm 4.13 (TPP →
   tensor restriction). First campaign that
   needs BOTH pillars (Pl7 tensor rank + Pl8
   character degrees). Makes the upper-bound
   program speakable in Lean. Schoenhage's
   tau-theorem stays as one named sorry.
   Difficulty: medium. Postdoc-tier plausible.

2. **Winograd lower bound R⟨2,2,2⟩ ≥ 7.**
   Substitution-method case analysis. Combined
   with Pl7's ≤ 7, gives R⟨2,2,2⟩ = 7
   machine-checked. Self-contained. Difficulty:
   medium-hard. Prover (Fable 5) recommended
   for first attempt; postdoc as fallback.

3. **Slice rank foundations (roadmap priority
   5).** Slice rank of Tensor k a b c,
   sliceRank ≤ rank, Tao diagonal lemma.
   Self-contained, reuses Pl7's Tensor type.
   Difficulty: medium. Postdoc plausible.

All three are independent of each other AND
of Pl10 and the legacy cards. They can all
run in parallel.

You SHOULD check Pl7, Pl8, and Pl9 for any
contuitation work they might've scoped in
their cards' notes sections that apply to
the following dispatch.

You SHOULD dispatch the three topics above
to individual `planner` agents that will
self-plan and manage those campaigns. Where
`postdoc` is written, instruct that planner
to favorite scheduling `postdoc` agents
for Lean proving.

USER-blocked decisions (from the three
analysis docs, awaiting review in a separate
session — do not act on these, do not create
cards for them, do not prompt the USER about
them; they will arrive as directives):

- Whether to send Blasiak-Cohn an erratum
  note re: packing-bound sentence
- Whether to fix Xlib/TPP.lean provenance
  docstring and/or make TripleProductPropertyR
  the primary definition
- Mathlib upstream sequence and timing
  (Wedderburn uniqueness, class-sum basis,
  counting theorems, Holor coexistence)
- Publication strategy (single paper vs
  components, ITP/CPP venue, Winograd as
  gate)
- FDRep bridge lemma priority

None of these block any of the three new
campaigns or any ready card in the DAG.
Forward progress is fully unblocked.

---

Orchestration keeps the shape of prior
sessions: you steer mini-orchestrators
(planner) that plan task cards and execute
them on conjecturist, prover/postdoc, and
implementer agents. Task notifications are
the primary steering signal.

Dispatch sequence: read `goof tasks ready`,
dispatch everything in parallel routed on
`agent:`. 

You **MUST** ignore `Ep542`, `Pf3`, and `Pf4`.

The output to the USER stays **EXTREMELY
MINIMAL** — card bodies and docs artifacts
are the decision chain; no prose reports for
their own sake. Exceptions: proof or kill
verdicts and any rho_0 > 1 flag.

After startup is complete, start the following:

```
/loop 5m Run `git add .` and `git commit -m "all: o46max-4 checkpoint $(date)"`
```

