We are going to focus on building out the
conceptual idea that I have described in
the ./Manuscripts/**/*.md files.

"Group sieve" names the tiered screening
cascade written as SCREEN_TPP_CANDIDATES
in exotic-groups-for-mm.md: filter the
non-abelian groups through cheap hard
rejects, then packing barriers, then
subgroup-lattice rejects, and rank the
survivors by TPP capacity ceiling. The
manuscripts never use the word "sieve";
this paragraph is its definition.

The group sieve is NOT a concept from any
literature (that I am aware) and it IS a
novel idea the USER has about how to find
a better construction for generic matrix
multiplication.

AlphaTensor and AlphaProof are related
but orthogonal concepts since they are
searching within certain sub-spaces for
targeted improvements.

The USER believes that he has the first
seed idea for building intuition (group
sieve) and wants to prove out a PoC before
scaling to 1000+ CPUs and 1 TiB+ of RAM.

The PoC bar, concretely: the sieve runs
end-to-end over a bounded group library
(all non-abelian groups of order <= 512
via GAP-in-Sage is a fine start), emitting
per-tier reject counts, a ranked survivor
list, and at least one survivor's capacity
ceiling checked against a known value from
the Murthy / BCGPU line. Falsifiable at
every tier; no scaling before the bar.

This repository has some unrelated and
related state in ./Proofs that should seed
various lines of thinking. One caveat:
Proofs/Vp2/Vp2.lean cites docs under
.tasks/research/ that did not survive the
branch seed. Its file header is the only
surviving record; do not chase those paths.

The elucidation of the group sieve is the
primary target; however, we also want to
hold at least two other autonomous tracks
at the same time. One of them will be
focused on the working proofs in ./Proofs:
drive them sorry-free where a proof is
genuinely in reach, and say plainly where
it is not. Exception: Vp2's sorries are
by design — the work there is the missing
infrastructure (border rank, smoothability,
VP), not the sorries themselves. The next
track will be focused on mining the Erdos
problems, using `wiki`, `oeis`, and any
other tools in surprising ways to see if
there's any easy burndown problems to
prove. Note `erdos search` only indexes
sparse comments+tags; drive the mining
from `erdos list` + `erdos fetch` + OEIS
cross-references.

The main track is the group sieve.

---

You will be orchestrating a network of
mini-orchestrators (planner) that in turn
have system prompts that allow them to
plan task cards (goof tasks) and then
execute those cards on `conjecturist` and
`prover` agents to close different areas
of exploration.

There should be some level of awareness
and steering that you manage at the top
level. Task notifications are the primary
steering signal. Before the fan out, start
`/loop 25m "Dispatch consumers to see if any steering is required."`
as a fallback heartbeat only — do not poll
faster; notifications already wake you.

You should prefer letting agents fly free
and clear and give them maximum freedom to
explore.

Only intervene when you see looping with no
end or genuine bad decisions being made because
of context pressure.

The output to the USER should be kept
**EXTREMELY MINIMAL** since all modes of
operation in the scope of this entire
host machine are fully autonomous. The
`goof tasks dag` plus card bodies are the
decision chain and provenance. Agents can
keep branching and working to close loops
and meet goals as they see fit — no prose
reports for their own sake; the docs
artifacts named on their cards are the
only writing that must exist.
