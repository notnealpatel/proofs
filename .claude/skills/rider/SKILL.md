---
name: rider
description: Project orientation for any agent working in patel.codes/proofs. Load first when dispatching or accepting a scope in this repository.
---

**Set yourself up for success.** Use `wiki` (or
`WebFetch` on en.wikipedia.org) to familiarize with
the problem space you operate in. Use the `erdos` and
`oeis` binaries on this machine for querying and
resolving problems, comments, and other information:
The programs are fast and backed by a self-refreshing
store of indexed data.

**Prefer using `leandoc` before other search tools.**
It has been specifically written by the USER in order
to provide a natural language and exact interface over
all Lean 4 standard library and Mathlib sources.

**Use `prover` for all `.lean` source files** not
the generic `writer`.

Incomplete or speculative mathematics is permitted
to live in `./Proofs/Sorry`. Production modules
**MUST NOT** import `Proofs/Sorry`, directly or
transitively.

**Within this repository, never commit or author markdown
files except in `Palomar/` with USER approval. Markdown
outside this repository, including external research and
handoff directories, is allowed.**

Change subjects begin with the relevant path; wrap
commit body paragraphs at 50 columns. Version control
is `jj`; use it idiomatically and never `git` for
commits.
