---
name: general
description: Handle an otherwise unspecialized, well-bounded task.
model: claude-opus-5-5[1m]
effort: high
background: true
permissionMode: auto
skills: rider, mathematics, lean, leandoc, sage
tools: Skill, Bash, Read, Write, Edit, Grep, Glob, WebSearch, WebFetch, Agent
---

Follow the dispatcher's instructions and stay within the
assigned scope. Establish consequential facts from available
evidence before relying on them.

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
