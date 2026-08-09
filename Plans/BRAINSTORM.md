# Fresh-context brief: formal-research governance project

## 1. Purpose and governing objective

This repository is a research monorepo for faithfully building, checking, understanding, and communicating mathematics. Mathlib upstreaming is not a present design constraint.

The scarce resource is the USER's mathematical attention, not model tokens, inference calls, or GPU time.

> Spend abundant machine attention so scarce human attention encounters only correct, consequential, well-contextualized mathematics worth understanding, judging, and explaining.

Success is therefore not primarily commits, completed tasks, generated tokens, or even theorem closure. It is measured by:

- precision of escalation to the USER;
- time to correct mathematical orientation;
- avoidable USER attention consumed;
- defects discovered after a result was marked ready;
- useful mathematical insight and intermediate lemmas;
- reliable state resumption without repeated dead ends;
- reproducibility;
- and outputs that become human understanding, human-written exposition, or deliberate rejection.

The system serves the USER's workflow. The USER remains authoritative over intent, semantic interpretation, significance, framing, priorities, trust acceptance, and final prose. Models prepare facts, candidates, adversarial analysis, and non-literary skeletons; they do not impersonate authorship.

A prior repository audit digest is at `thatnealpatel/proofs#3`.

## 2. Core conclusions

The exploratory review converged on five central conclusions.

### 2.1 Yah is already the execution substrate

Do not rebuild a weaker generic agent framework from the papers reviewed. Yah already supplies capabilities that most of them construct only partially:

- heterogeneous model and effort routing;
- parallel isolated subagents with explicit roles;
- mandatory correctness, style, security, and concurrency review routing where applicable;
- asynchronous tasks, steering, cancellation, and resumption;
- exact tool-mediated file observations, stale-state checks, and atomic edits;
- repository- and session-specific policy injection;
- deterministic Lean, Sage, shell, source-retrieval, and GitHub operations;
- fast local or in-network retrieval over Wikipedia, Erdős problems, OEIS, and Mathlib.

Use Yah to prototype and evaluate the missing research-governance layer. Do not begin by rebuilding scheduling, generic Planner/Worker orchestration, file handoff, or concurrency.

Yah is not automatically a sterile scientific environment. Closed model and harness behavior may hide prompts, context transformations, memory, model updates, and provider-side inference details. Record this opacity explicitly. Open-weight principal-researcher experiments need a stricter isolated execution path.

### 2.2 The missing work is semantic and epistemic

The reviewed systems are strong at execution, proof search, artifact packaging, or provenance, but they repeatedly collapse distinctions that this project must preserve:

1. what happened: events, runs, raw traces, tool calls, and artifact mutations;
2. what a model or human inferred: attributed interpretations and summaries;
3. what deterministic tools verified: observations and receipts;
4. what the USER or an authorized reviewer accepted: scoped decisions.

No item may silently migrate between these categories. A model rating is not evidence. Lean compilation is not semantic alignment. A human reading is not automatically USER acceptance. A failed search is not a mathematical refutation.

### 2.3 The two main research contributions are Capsule and dossier

The strongest differentiators from prior work are:

- a **Research Capsule**: the smallest mechanically defensible graph cut from which a fresh researcher can resume correctly;
- a **Research Result dossier**: a decision-specific, progressively disclosed human interface that directs scarce attention to consequential evidence and uncertainty.

The graph by itself is infrastructure. The research claims should concern resumption quality, epistemic correctness, and human-attention allocation.

### 2.4 Status must be derived, multidimensional, and scoped

Do not store a mutable scalar such as `status: verified`. Store immutable artifacts, events, observations, interpretations, evidence relations, and decisions. Derive views under an explicit policy.

Useful independent facets include:

- source identity and access;
- content support or challenge;
- formal compilation and proof completion;
- axiom and trust surface;
- source-to-Lean semantic alignment;
- mathematical state;
- execution state;
- USER acceptance;
- novelty and significance assessment;
- capsule position.

Every derived state is scoped to exact artifacts, environments, target claims, and policy revisions.

### 2.5 Complexity must earn itself through ablation

AlphaProof Nexus reports that a simple independent-agent-plus-compiler loop reproduced its nine Erdős successes post hoc, though at higher cost on hard cases. ARA reports that full failure traces can help or anchor depending on model capability. OpenProver's compact Whiteboard is useful despite being epistemically weak.

Every graph layer, memory mechanism, rating system, and agent topology must therefore be compared with simple baselines.

## 3. Human-facing Research Result dossier

The dossier, not a graph dump, task ledger, raw trace, chat summary, or generated paper, is the main human-facing unit.

### 3.1 Always-visible Decision page

Show:

- exact normalized claim;
- why it may matter, attributed and bounded;
- formal status without equating compilation with fidelity;
- strongest defensible novelty status and search boundary;
- correctness-critical risks and what the result does not establish;
- unresolved USER decisions;
- recommended next action;
- compact provenance and freshness indicators.

Correctness-critical anomalies must never be hidden by progressive disclosure.

### 3.2 Claim alignment

| Layer | Required content |
|---|---|
| Primary source | Exact quotation, artifact identity, and location |
| Intended interpretation | Normalized mathematical statement, attributed |
| Lean | Exact compiled signature in a pinned environment |
| Difference | Added guards, omitted assumptions, domain/type changes, strengthened or weakened conclusions |

Use the semantic-hallucination checklist from Lean Atlas:

- definition mismatch;
- missing or extra assumptions;
- goal substitution;
- quantifier or scope error;
- default-type or domain shift.

### 3.3 Proof-reading map

Show the 5-15 declarations the USER should understand:

- mathematical checkpoints;
- load-bearing lemmas;
- key definitions;
- actual versus intended dependencies;
- automation boundaries;
- conjectural, axiom, native, or external-computation dependencies;
- exact source links;
- recommended reading order.

Maintain three separate Lean-derived projections:

1. **formal spine**: actual type/value dependencies, signatures, axioms, and `sorry` observations;
2. **semantic review cone**: Lean Compass-style declarations capable of affecting target meaning;
3. **mathematical reading map**: conceptual proof structure and trajectory facts worth human understanding.

### 3.4 Adversarial findings

Include:

- alternate interpretations;
- vacuity and boundary probes;
- totalization traps;
- counterexamples;
- statement/prose/dependency disagreement;
- reviewer disagreement;
- unresolved assumptions;
- exploit or trust taint;
- stale artifacts and reviews.

### 3.5 Research context

Include:

- closest prior art;
- exact primary excerpts;
- bounded novelty evidence;
- corpora and queries checked;
- unchecked corpora;
- proved versus speculative consequences;
- related Erdős and OEIS entries;
- relevant Mathlib and external-reference neighborhoods.

A vector-search miss is evidence only about that query and index. It is never a global absence claim.

### 3.6 Reproduction receipt

Include:

- Git commit, blob, and worktree identities;
- Lean and dependency pins;
- exact declaration signatures;
- transitive `sorry` and axiom surfaces;
- commands, outputs, and checksums;
- model/run identity and context where available;
- environment, filesystem, network, and hardware details;
- verifier receipts;
- schema and policy versions.

### 3.7 Progressive-disclosure policy

Progressive disclosure should simplify the route through evidence, not hide epistemic weakness.

Provide explicit task-shaped routes:

- **Why do we believe this?** Evidence and claim alignment.
- **How should I read the proof?** Proof-reading map.
- **What could be wrong?** Adversarial findings.
- **Can I reproduce it?** Receipts and environment.
- **How did we get here?** Capsule and trajectory.

When an anomaly is detected, automatically surface:

1. expected state;
2. observed artifact or receipt;
3. impact on derived status;
4. evidence links;
5. recommended action.

The progressive-disclosure paper reviewed was a low-stakes emotion-classifier study. It supports testing direct use, timing, distraction, and user-controlled depth; it does not justify hiding errors or assuming a particular disclosure ladder improves mathematical correctness.

## 4. Research Capsule

A Research Capsule is a bounded snapshot or graph cut through the dynamic research state. It is the minimum structured state needed to resume without replaying prior chats.

It contains:

### Identity and objective

- research objective and scope;
- repository and environment snapshot;
- canonical target claims;
- governing policy version.

### Focus subgraph

- relevant nodes and typed edges;
- compressed completed branches;
- active frontier;
- blocked frontier;
- external dependencies;
- stale or disputed regions.

### Accepted state

- deterministic observations;
- established definitions;
- scoped evidence;
- explicit USER decisions;
- refuted or superseded hypotheses;
- unresolved semantic reviews.

### Trajectory summary

- routes attempted;
- route charters;
- pivots and merge points;
- exact obstructions;
- counterexamples;
- repaired and revived branches;
- links to raw trace intervals and artifacts.

### Continuation interface

- ready investigations;
- proposed experiments;
- USER judgment questions;
- resource and stopping conditions;
- expected next receipts.

### Provenance

- source artifacts;
- model runs and exact contexts where available;
- raw traces;
- tool and verifier receipts;
- extraction and compression provenance.

A Capsule is not a model-written handoff. Mechanical fields are regenerated from artifacts and native events. Narrative fields remain attributed. The full research package and graph remain available beneath it.

The primary benchmark is:

> Can a fresh principal-researcher instance resume from the Capsule without prior chat context, take a useful next action, and avoid known mistakes?

OpenProver's Whiteboard is the primary baseline: compact and useful, but rewritten solely by a Planner, untyped, and not mechanically grounded.

## 5. Planes, graphs, and canonical records

### 5.1 Two authority planes

#### Artifact and knowledge plane

Primarily derived:

- Lean declarations, source locations, signatures, and dependencies;
- mathematical assertions and definitions;
- primary sources and quotations;
- computations and datasets;
- manuscripts;
- immutable generated artifacts;
- proof, axiom, and trust observations;
- Git and environment identities.

#### Work and execution plane

Tracks:

- objectives and work units;
- attempts and runs;
- dependencies and eligibility;
- delegation and route charters;
- review and replanning;
- retries, failures, cancellation, and resource state;
- observed lifecycle events.

The bridge is explicit:

```text
work produces, tests, or repairs artifacts
artifacts motivate, regress, block, or invalidate work
```

The knowledge plane must not become a mutable task manager. The execution plane must not become an unverified knowledge base.

### 5.2 Derived graph projections

Maintain separate projections rather than one overloaded graph.

1. **Work DAG**: schedulable dependencies, readiness, ownership, blocking, retry, and replanning.
2. **Search graph**: proof candidates, strategies, exact goals, lineage, route charters, failures, and heuristic ratings.
3. **Formal artifact graph**: declarations, type/value dependencies, axioms, proof states, source positions, and external cross-references.
4. **Epistemic research graph**: assertions, evidence, interpretations, observations, decisions, refutations, repairs, supersessions, and revivals. This graph need not be acyclic.
5. **External reference graph**: Wikipedia links, OEIS cross-references, Erdős problem links, Mathlib cross-references, and literature neighborhoods. These edges aid discovery but are not evidentiary support by themselves.

The Capsule is a bounded projection across these graphs. The dossier is a decision-specific human projection across them.

### 5.3 Core objects

- **Assertion**: mathematical, computational, novelty, attribution, or manuscript proposition.
- **Artifact**: immutable/content-addressed source, Git object, Lean declaration in an environment, dataset, program, run output, manuscript revision, prompt, or trace.
- **Observation**: reproducible fact such as compilation, axiom set, quotation occurrence, checksum, bounded search result, or computation.
- **Interpretation**: attributed model or human reading of artifacts and observations.
- **Evidence relation**: `supports`, `refutes`, `proves`, `formalizes`, `quotes`, `computes_exactly`, `computes_bound`, `conditionally_implies`, `attributes`, or `supersedes`.
- **Decision**: scoped USER or reviewer judgment about fidelity, interest, framing, trust, readiness, or publication support.
- **Work unit**: intended investigation and acceptance oracle.
- **Run**: observed execution of a work unit.
- **Research Result**: dossier-worthy claim bundle.
- **Research Capsule**: bounded resumption state.

Important research relations include:

```text
depends_on  refines      splits       merges
supports    refutes      blocks       repairs
formalizes  verifies     supersedes   revives
generalizes specializes  motivated_by selected_over
```

Every edge records its origin. In particular, distinguish:

- inferred from Lean type;
- inferred from Lean value;
- declared intended dependency;
- human conceptual dependency;
- model interpretation;
- verifier observation.

## 6. Invariants

Begin with these invariants rather than a database schema.

1. No parentless assertion: every assertion has an attributed generating activity or explicit import event.
2. No surfaced result without typed evidence or an explicit unsupported marker.
3. No model interpretation presented as a deterministic observation.
4. No compilation result presented as semantic alignment.
5. No human review without the exact reviewed artifact and scope.
6. No USER acceptance inferred from silence, steering, or task completion.
7. No obstruction without exact target, assumptions, failure type, evidence, and revival conditions.
8. No timeout, failed tactic, or bounded-search failure promoted to `refutes`.
9. No changed declaration retaining stale proof, alignment, or review status.
10. No derived status that cannot be explained from events, receipts, decisions, and policy.
11. No generated summary treated as canonical history.
12. No correctness-critical anomaly hidden by progressive disclosure.
13. No source identifier or URL treated as proof that the source supports a claim.
14. No search miss treated as corpus-wide absence without an enumerated corpus and documented query.
15. No work completion state interpreted as epistemic verification.

F(AI)2R's useful invariant is “no parentless claim”; strengthen it with evidence requirements. Its linear verification ladder should not be copied because it mixes identity, access, AI interpretation, and human judgment.

## 7. Negative knowledge and belief maintenance

Negative knowledge requires a strict taxonomy:

- syntax or elaboration error;
- compilation failure;
- search timeout;
- bounded search exhausted;
- unresolved goal;
- failed tactic;
- failed high-level strategy;
- formal disproof of an exact formal subgoal;
- mathematical counterexample;
- statement mismatch;
- vacuity or boundary defect;
- hallucinated source or theorem;
- human-abandoned route;
- environment or resource failure.

Only formal disproofs and valid counterexamples normally justify `refutes`. An obstruction records:

- target and scope;
- assumptions and environment;
- route attempted;
- exact observation;
- verifier receipt where applicable;
- attributed lesson;
- justified consequence;
- conditions under which retrying is warranted.

### 7.1 Adjacent research surfaced by tool exploration

Wikipedia vector search plus outbound-link traversal surfaced older knowledge-representation work that is highly relevant and was not central in the reviewed agent papers:

- **Truth/reason maintenance systems**: justifications, base versus derived facts, dependency-directed backtracking, retraction, and multi-context maintenance.
- **Assumption-based TMS (ATMS)**: facts valid under explicit assumption environments and inconsistent assumption sets (“nogoods”). This maps directly to conditional claims, scoped obstructions, and revival after assumptions change.
- **Belief revision**: update versus revision, minimal change, contraction, merging, foundational versus deductively closed belief bases, and iterated revision. This suggests distinguishing artifact change from correction of a belief about the same artifact.
- **Dung argumentation frameworks**: attack relations, grounded/preferred/stable semantics, and skeptical versus credulous acceptance. This may help model contested evidence, but should not be adopted before a concrete need.
- **IBIS/design rationale**: `Question → Position → pro/con Argument`, suitable for preserving exploratory choices and USER decisions without pretending the map is a proof.

These are promising prior-art threads, not yet adopted designs. Their primary sources are listed in Section 15.

## 8. Formalization transaction model

LeanMarathon provides the strongest execution-plane pattern: many bounded, source-aware, externally checked transactions instead of one opaque multi-day run.

Each delegated formalization transaction should specify:

- objective and mathematical role;
- exact input artifact hashes;
- source material;
- allowed files, spans, and declarations;
- frozen target signatures;
- deterministic acceptance checks;
- valid failure outputs;
- delivery manifest and receipts.

### 8.1 Target review before proof search

A read-only reviewer compares:

```text
primary source
  -> normalized target
  -> explanatory blueprint/prose
  -> exact Lean type
```

Do not spend proof-search compute until discrepancies are repaired or explicitly accepted.

### 8.2 Repair-radius-aware decomposition

A good decomposition minimizes the downstream invalidation caused by correcting one mathematical commitment. Measure:

- declarations invalidated;
- proof work discarded;
- semantic review cone made stale;
- human re-review required;
- Capsule and dossier invalidation.

### 8.3 Source gap versus formalization drift

A blocker must distinguish:

- formalization drift from a valid source;
- ambiguity, gap, or falsity in the source;
- missing library infrastructure;
- operational search failure.

### 8.4 Whole-proof invalidation

If a statement or relevant context changes, preserve a completed proof byte-for-byte if it remains valid; otherwise invalidate it as a whole. Never permit plausible partial surgery to masquerade as retained verification. Preserve the old proof as a historical artifact linked to the superseded statement.

### 8.5 Cheap falsification first

Before expensive proving, test finite, numerical, empty, boundary, trivial-model, coercion, totalization, and vacuity cases. Failure to find a counterexample is only an observation.

### 8.6 Formal completion gate

At minimum record:

- exact target signature unchanged;
- compilation receipt;
- no `sorry` or `admit` in the relevant closure;
- transitive `sorryAx` report;
- complete axiom profile;
- native/unsafe/external execution use;
- dependency graph;
- environment and compiler identity;
- semantic review state.

Formal completion triggers dossier review; it does not automatically mean ready for the USER.

## 9. Exploration ecology

The model fleet is a research ecology, not a homogeneous pool.

Use explicit route charters such as:

- reconstruct the source proof;
- avoid the source route;
- search for a counterexample;
- compute first;
- minimize assumptions or typeclasses;
- derive a stronger structural lemma;
- translate to a standard notion;
- use a different mathematical representation;
- avoid heavy automation;
- challenge the formal statement itself;
- retrieval-blind independent derivation.

Twenty identical prompts are parallelism, not intellectual diversity.

Use adaptive escalation:

1. launch cheap independent branches with distinct charters;
2. collect formal and semantic progress signals;
3. identify reusable exact goals and intermediate lemmas;
4. escalate promising or structurally difficult branches to specialized provers or population search;
5. stop and Capsule when search becomes repetitive, semantically suspect, or human-blocked.

AlphaProof-style Elo, plausibility, clarity, or novelty ratings are attributed search interpretations. They are never truth confidence. High-rated incomplete sketches can merely restate the target behind `sorry` or hide hallucinated literature lemmas.

## 10. Retrieval and external knowledge

The local/in-network retrieval layer is a significant advantage.

### 10.1 Available capabilities

- `wiki`: millisecond vector title search, exact canonicalized articles, and complete outbound `links` enumeration.
- `erdos`: second-scale BM25 over comments/tags and full metadata enumeration; the raw binary additionally has exact live `fetch <N>` with statement, references, and complete threaded comments.
- `oeis`: second-scale name search, exact entry lookup with terms/comments/programs/xrefs, and term matching.
- `leandoc`: second-scale exact and BM25 lookup over Lean, Batteries, ImportGraph, and Mathlib sources, with signatures, bodies, files, lines, docstrings, and examples where indexed.

Treat these as high-speed external sensors, not canonical truth stores.

### 10.2 Retrieval-to-evidence pipeline

```text
semantic retrieval
  -> candidate entity
  -> exact canonical lookup
  -> source or code inspection
  -> observation
  -> attributed interpretation
  -> evidence relation or USER decision
```

Wikipedia and comments provide orientation and leads. OEIS comments and Erdős discussions are not substitutes for cited proofs. `leandoc` results must be tied to the project's actual Lean/Mathlib revision.

### 10.3 External reference graph

Keep reference edges separate from evidence:

- Wikipedia `links_to`;
- OEIS `xrefs`;
- Erdős-to-OEIS and related-problem links;
- Mathlib external cross-references;
- source citation links.

A link is not support. Use bounded neighborhood expansion for terminology, synonyms, related concepts, primary-reference discovery, and retrieval diversity. Record seed, direction, depth, complete enumerated neighbor set or response hash, ranking policy, selected nodes, and pages actually read.

### 10.4 Tool comparison findings

Raw binary and harness-native testing found:

- `wiki` native and raw commands have matching search/article/links shapes.
- `oeis` native and raw commands have matching show/search/match content; `match` is JSONL and should be treated accordingly.
- `erdos` native list/search match the raw index results, but the native tool lacks raw `erdos fetch <N>`. This prevents native access to exact statements, references, full comments, replies, authors, dates, and source links. Filed as `thatnealpatel/yah#707`.
- A native `tool_erdos list` call was observed truncated without a recoverable spill path, contrary to the spill design described in closed `thatnealpatel/yah#480`; the observation was added there. Raw `erdos list` can be redirected and filtered.

### 10.5 Lean mechanisms discovered through `leandoc`

Do not assume LeanArchitect or Lean Atlas must supply every extraction primitive. The indexed ecosystem already exposes useful machinery:

- `Lean.Name.transitivelyUsedConstants`: transitive declaration constants.
- `Mathlib.PrintSorries.collect` and `collectSorries`: transitive `sorry` discovery with source-oriented messages.
- `Mathlib.Command.MinImports.getAllDependencies`: command syntax, attributes, identifiers, and declaration dependencies.
- ImportGraph required/minimal-module functions.
- Batteries dependent and opaque collectors.
- `ExportCrossRefs.buildEntries`: stable JSON export of declaration cross-references.
- `Mathlib.CrossRef.Tag`: declaration links to Kerodon, LMFDB, Stacks, and Wikidata, including comments.

These can mechanically populate the formal and external-reference graphs. Verify them in the pinned project environment before adoption.

## 11. Provenance and sterile runs

Use F(AI)2R and W3C PROV as an interoperability substrate, not as the epistemic ontology.

Borrow:

- no-parentless-claim validation;
- append-only promotions, refusals, retractions, and decisions;
- content hashes and commit binding;
- “omit, do not estimate” telemetry;
- exact review-material handoff;
- generated audit views;
- release bundles with graph, dossier, receipts, traces, and checksums.

Every metric records whether it was observed, computed, or absent, plus source and basis.

For scientifically interpretable runs, record where available:

- model and weight checksum;
- inference engine and container;
- quantization and parallelism;
- prompt/template revision;
- exact context bundle;
- decoding parameters and seed;
- tools and versions;
- filesystem snapshot;
- network policy;
- hardware;
- outputs, events, and termination.

Isolate:

- fresh worktree or content-addressed source;
- explicit writable paths;
- no hidden memory;
- bounded network;
- immutable challenge artifacts;
- separate candidate and verifier environments.

Open weights do not prove clean training data. Exposed reasoning traces are not guaranteed causal explanations. Runtime sterility does not establish independent discovery; use unpublished, generated, blinded, or held-out problems where possible.

## 12. Storage posture

Do not begin with a generic plugin framework or database schema.

Likely durable storage:

- Git plus small reviewable manifests;
- content-addressed artifacts and receipts;
- append-only event history;
- generated dashboards, Capsules, dossiers, and exports;
- disposable derived indexes;
- SQLite initially for operational scheduling and queries;
- DuckDB/Parquet later for model and repository analytics;
- optional PROV-O/RO-Crate/nanopublication exports once semantics stabilize.

Neither SQLite nor DuckDB is the epistemic source of truth. Rendered LaTeX, graph colors, task ledgers, and status labels are views.

`.tasks/` remains frozen historical input. Mine it for leads, verify surviving facts against primary artifacts, reexpress useful objectives, and remove active dependencies. No canonical claim cites `.tasks/` as evidence.

Version manuscripts and selected provenance. The USER writes final exposition personally.

## 13. First bounded prototype

Do not build the general platform first. Run one real Yah-managed Lean campaign with:

- a source/statement alignment risk;
- several proof routes;
- at least one failed route or counterexample search;
- deterministic Lean output;
- a meaningful USER decision;
- explicit route charters;
- contract-scoped workers and independent critics;
- native event and artifact capture;
- typed failures;
- signature, dependency, `sorry`, and axiom receipts;
- source and retrieval provenance.

Derive from the same event prefix:

- work DAG;
- search graph;
- formal artifact graph;
- epistemic graph;
- external reference neighborhood;
- OpenProver-style Whiteboard baseline;
- Research Capsule;
- Research Result dossier.

### 13.1 Frozen-prefix resumption experiment

Predeclare cut points:

- after a failed branch;
- after an exact obstruction;
- after a verified lemma;
- after a counterexample;
- after a pivot;
- after a USER intervention;
- after a superseded definition.

Start a fresh principal researcher with no prior chat. Hold model, prompt charter, token budget, tools, environment, and seed policy fixed. Compare:

1. theorem only;
2. model-authored Whiteboard and repository summaries;
3. full raw history;
4. full graph;
5. Research Capsule;
6. Capsule plus dossier.

Run both representation-only and end-to-end comparisons. Charge extraction and retrieval costs. Do not compare a hand-polished Capsule against a native generated summary.

Primary metrics:

- usefulness of first action;
- active/blocked frontier recovery;
- repeated-dead-end rate;
- exact-obstruction recovery;
- time and tokens to orientation;
- “Why do we believe this?” accuracy;
- “What exactly did Lean prove?” accuracy;
- false promotion of interpretation to fact;
- USER attention required.

Secondary metrics:

- Lean closure;
- signature and axiom alignment;
- useful intermediate lemmas;
- route diversity;
- reproducibility.

### 13.2 Dossier experiment

Use the same underlying evidence in four interfaces:

1. graph/all-at-once dump;
2. overly compressed default;
3. progressive dossier;
4. progressive dossier with automatic anomaly escalation.

Measure correctness, defect detection, calibration, orientation, backtracking, delayed caveat recall, and active USER time—not preference or click count alone.

### 13.3 Candidate repository cases

- A114976 statement mismatch;
- Poonen versus Barsky attribution;
- clean theorem in a file containing unrelated `sorry`;
- native-execution trust case;
- stale Scratch/GroupSieve route;
- exact versus lower-bound computation;
- parallel Leanstral/Goedel campaign;
- whiteboard or speech capture;
- late target correction for repair-radius evaluation.

## 14. Immediate design questions

Before implementation, settle:

1. Formal sufficiency criterion for a Research Capsule.
2. Semantics of the USER's open/closed-circle drawing and disconnected chain.
3. Core ontology and edge provenance.
4. Negative-knowledge taxonomy and revival rules.
5. Status-facet derivation policy.
6. Target-scoped semantic review and invalidation.
7. Transaction contract and repair-radius metric.
8. Required queries:
   - Why do we believe this?
   - What exactly did Lean prove?
   - How did we reach it?
   - What remains unresolved?
   - What requires USER attention?
   - What should a fresh researcher do next?
   - Which manuscript claims are stale?
   - Which model mixture produced useful insight?
9. Two or three manually constructed ideal dossiers from real cases.

## 15. Sources and provenance of this brief

### 15.1 Primary paper sources read in full from fetched arXiv source

Each paper was fetched as LaTeX/text and assigned to one independent high-effort reader. These are recent preprints unless otherwise noted; reported empirical results remain author-reported unless independently reproduced.

- **Agent-Native Research Artifacts (ARA)**, *The Last Human-Written Paper: Agent-Native Research Artifacts*, arXiv:2604.24658. Source: <https://arxiv.org/abs/2604.24658>. Code: <https://github.com/Orchestra-Research/Agent-Native-Research-Artifact>.
- **MechMath Agent Team**, *MechMath Agent Team: LLM Driven Agents for Mathematical Research*, arXiv:2607.04394. Source: <https://arxiv.org/abs/2607.04394>. Project: <https://mechmath.github.io/>.
- **Lean Atlas**, *Lean Atlas: An Integrated Proof Environment for Scalable Human-AI Collaborative Formalization*, arXiv:2604.16347. Source: <https://arxiv.org/abs/2604.16347>. Code: <https://github.com/NyxFoundation/lean-atlas>.
- **OpenProver**, *OpenProver: Agentic and Interactive Theorem Proving with Lean 4*, arXiv:2607.09217. Source: <https://arxiv.org/abs/2607.09217>.
- **F(AI)2R**, *Who Did What, and Who Checked? Verifiable AI Provenance as an Executable Skill*, arXiv:2607.25637. Source: <https://arxiv.org/abs/2607.25637>.
- **LeanMarathon**, *Toward Reliable AI Co-Mathematicians through Long-Horizon Lean Autoformalization*, arXiv:2606.05400. Source: <https://arxiv.org/abs/2606.05400>. Code: <https://github.com/YuanheZ/LeanMarathon>.
- **AlphaProof Nexus**, *Advancing Mathematics Research with AI-Driven Formal Proof Search*, arXiv:2605.22763. Source: <https://arxiv.org/abs/2605.22763>.
- **LeanArchitect**, *Automating Blueprint Generation for Humans and AI*, arXiv:2601.22554. Source: <https://arxiv.org/abs/2601.22554>. Code: <https://github.com/hanwenzhu/LeanArchitect>.
- **LeanAgent**, *Lifelong Learning for Formal Theorem Proving*, arXiv:2410.06209; ICLR 2025. Source: <https://arxiv.org/abs/2410.06209>. Code: <https://github.com/lean-dojo/LeanAgent>.
- **Progressive Disclosure**, *Progressive Disclosure: Designing for Effective Transparency*, arXiv:1811.02164; later ACM TiiS. Source: <https://arxiv.org/abs/1811.02164>. DOI: <https://doi.org/10.1145/3374218>.

Fetched source copies from this exploration were placed under `/tmp/formal-research-papers/`; `/tmp` is not durable project storage.

### 15.2 Standards and authoritative technical sources consulted

- W3C PROV-O: <https://www.w3.org/TR/prov-o/>.
- RO-Crate specification and repository: <https://www.researchobject.org/ro-crate/> and <https://github.com/ResearchObject/ro-crate>.
- Nanopublication guidelines: <https://nanopub.net/guidelines/working_draft/>.
- Micropublications: Clark et al., *Micropublications: a semantic model for claims, evidence, arguments and annotations in biomedical communications*, <https://pmc.ncbi.nlm.nih.gov/articles/PMC4530550/>.
- Evidence Graph ontology: <https://fairscape.github.io/EVI/index.html>.

### 15.3 Adjacent primary sources surfaced by Wikipedia neighborhood traversal

These are high-priority prior-art leads. They were identified through canonical article/link traversal but were not deeply reviewed during this conversation; verify their full texts before relying on them.

- Jon Doyle, *A Truth Maintenance System*, Artificial Intelligence 12(3), 1979. DOI: <https://doi.org/10.1016/0004-3702(79)90008-7>.
- Johan de Kleer, *An Assumption-Based TMS*, Artificial Intelligence 28(2), 1986. DOI: <https://doi.org/10.1016/0004-3702(86)90080-9>.
- Carlos Alchourrón, Peter Gärdenfors, and David Makinson, *On the Logic of Theory Change: Partial Meet Contraction and Revision Functions*, Journal of Symbolic Logic 50(2), 1985. DOI: <https://doi.org/10.2307/2274239>.
- Phan Minh Dung, *On the Acceptability of Arguments and Its Fundamental Role in Nonmonotonic Reasoning, Logic Programming and n-Person Games*, Artificial Intelligence 77(2), 1995. DOI: <https://doi.org/10.1016/0004-3702(94)00041-X>.
- Werner Kunz and Horst Rittel, *Issues as Elements of Information Systems*, Working Paper 131, University of California, Berkeley, 1970.

### 15.4 Lean source mechanisms discovered with `leandoc`

Relevant exact declarations and files:

- `Lean.Name.transitivelyUsedConstants`, `ImportGraph/Imports/RequiredModules.lean`;
- `Mathlib.PrintSorries.collect` and `Mathlib.PrintSorries.collectSorries`, `Mathlib/Util/PrintSorries.lean`;
- `Mathlib.Command.MinImports.getAllDependencies`, `Mathlib/Tactic/MinImports.lean`;
- `Mathlib.CrossRef.Database` and `Mathlib.CrossRef.Tag`, `Mathlib/Tactic/CrossRefAttribute.lean`;
- `ExportCrossRefs.buildEntries`, `mathlib/scripts/export_crossrefs.lean`.

Always re-query `leandoc` and inspect the exact source in the pinned environment before implementation.

## Central principle

> The durable system must preserve what happened, what was inferred, what was verified, and what the USER accepted as four separate but connected layers.

Use Yah's existing power to make those layers operational. The Research Capsule makes them resumable. The Research Result dossier turns them into high-signal human attention. Everything else should support or test those claims.
