## patel.codes/proofs

**Respect project boundaries.** Work within the
USER's authority and your role. Preserve
workspace/cache isolation and use bounded execution.
Within this repository, do not author markdown files
except in Palomar/ with USER approval and the agent
and skill definitions under `.claude/`. Markdown
outside this repository, including external research
and handoff directories, is allowed. Change subjects
begin with the relevant path; wrap body paragraphs at
50 columns. Version control is `jj`; use it
idiomatically, never `git`, for commits.

**Preserve truth.** Distinguish sources, informal
arguments, conjectures, computations, interface
probes, and kernel-checked proofs. Preserve objects,
hypotheses, conclusions, and unpaid obligations;
never hide difficulty behind an oracle, certificate,
weakened statement, or inflated axioms. Adoption,
when authorized, requires independent exact-artifact
review, a fresh relevant build, and an imported
axiom audit allowing only propext, Classical.choice,
and Quot.sound, with no transitive Sorry. The audit
is evidence, not an adoption artifact. Report
semantic fidelity, non-vacuity, and residuals.

**Separate publication.** Search coverage and
uncertainty belong with novelty claims; no matches
are not novelty. Public claims and publication need
explicit USER authorization through the designated
publication steward. Observation, peer acceptance,
and successful verification do not enlarge authority.

- You **MUST NOT** manually write or modify files in `./References`.

- You **MUST NOT** truncate shell/bash output; doing so risks missing critical information
  that poisons all downstream reasoning. You SHOULD redirect unfamiliar output into `/tmp/**`
  and probe its shape before reading.

- You **MUST** treat a proof as complete when the file compiles with no `sorry`, no `admit`, and no errors.

- You **MUST** dispatch parallel `reviewer` agents scoped to vacuity, foundations, and style
  against all uncommitted Lean programs before staging or committing.

- You **MUST** use `flock .lake/agent.lock lake build ...` when trying to build proofs to avoid stomping on other agents.

- You **MUST** load `/leandoc` and use `leandoc` for retrieval for Lean semantic search and symbol search before using other tools.

- You SHOULD use `exact?`, `apply?`, `#loogle` and `#leansearch` as documented
  in `/leandoc` for tactic and lemma discovery.

- You **MUST** run `sage` and `python` commands wrapped in `timeout 300` by default.
  Anything that times out **MUST NOT** be retried; it should be escalated to the USER.

- You SHOULD use `.lean` files in `Scratch` for `#check`, `#eval`, or `#example`
  experiments before crystallizing them into non-`Scratch` Lean libraries.

- You SHOULD use reach for `/sage` first when looking for computational algebra
  intuitions; `sage` programs cannot be proofs, but they are useful for pre-proof
  orientation and proof-assisting activities. They can be used to produce counter-
  examples and witnesses.

- You SHOULD use `fetch` for arXiv and academic paper pdf links before `WebFetch`;
  `fetch` auto-canonicalizes into `.tex` or `.txt` for agents.

- You SHOULD use `sage -c "<sage code>"` for short queries or explorations.

- You SHOULD implement directly onto `main` unless told otherwise.

- Incomplete or speculative mathematics lives under `Proofs/Sorry/`; production
  libraries **MUST NOT** import `Proofs/Sorry/` directly or transitively.

### Lake

**Use Lake as a scalpel.** When Lean elaboration is
needed, build the narrowest module from the repository
root, through the shared build lock:

```shell
timeout --kill-after=2s 300s flock .lake/agent.lock lake -q build +Module.Name
```

Every build and check runs through `Bash` with an
explicit `timeout`. A normal module check has a 300s
external timeout (trace checking alone costs about
40s); a known cold finite computation may be justified
up to 600s. Inspect what rebuilt before raising a
bound, and do not retry an unchanged timeout. For a
disposable probe of a leaf file that imports only
Mathlib or already-built modules, elaborate without
the lock:

```shell
timeout --kill-after=2s 300s lake env lean -j 1 Proofs/Scratch/Probe.lean
```

Keep workspace cache isolation: do not copy build
trees, point `LEAN_PATH` across workspaces, delete
`.lake`, or invent another cache layout. Run `lake`
only from the repository root, never with `-d` or
`-R`. Keep stable finite computation separate from
changing bridges; explain module cache effects when
relevant. Longer work is allowed when justified and
bounded.
