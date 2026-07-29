## `f5high-1`

I had to instruct the orchestrator for
the `f5high-1` session halt the agents
early since the quota got burned quickly.

The generated retrospective is at
`.tasks/f5exp/docs/retro-session1.md`.
A LESSONS.md was drafted for review in
informing how the `f5high-2.md` prompt
is materialized.

The brute forcing group sieve behavior
is unimpressive and to be expected. The
gap analysis is somewhat useful. The real
ass-bite was underspecifying the Erdos
Mining Campaign; the agents picked proved
things to formalize... which is not without
value; however, it begs the question: why.

The entire point is to go for unsolved
problems, which `erdos` CLI explicitly
allows for. However, in writing this, it
might actually be interesting to determine
in a different parallel track where a new
formalization of something that has been
proved might have a "high yield" in that
its Lean 4 code (while likely not anywhere
else, certainly not upstreamed to Mathlib)
might be useful to us for reference.

For these cases, we should use agents in
this experiment to formalize at least 2
more proven Erdos problems. Then after that,
we simply keep a document about which
formalizations are worth doing versus not
worth doing for my own custom proving infra
to pick up. This gives us the best of both
worlds: we can eval against the 5 that
Fable 5 spent time proving as well as extract
the time it took to how we do in our bespoke
infrarstructure.

```
What is the significance of the checkpoint data collected on the group sieve effort?
```
```
Its significance is real but specific: it is the first validated, resumable dataset produced by your sieve idea — and it is a screening dataset, not a discovery. Breaking that down along separate axes, since they carry different weight:

As proof the idea works at all. The sieve cascade is your construction, not something from the literature. The checkpoint data is the first evidence that it runs end-to-end as a falsifiable instrument: every tier predicate implements a specific corrected theorem (the grounding wave caught five manuscript-vs-literature discrepancies before they were coded), the 18/18 anchor harness passed, and the data reproduces known values where they exist — [32,49] gets CAP(2), tight against Murthy's exact ρ₀ = 2; [64,226] survives with ceiling 4.0 as expected; [10,1] rejects on the divisibility test. That anchor agreement is what makes the other 67,000 rows worth anything. Without it the dataset would be 67k unfalsifiable numbers.

As mathematical content. The headline empirical fact is the attrition shape: only 5.2% of nonabelian groups ≤ 511 are hard-rejected and 5.1% capped — 89.8% survive to Tier 2b with only packing ceilings recorded. That says the cheap structural tiers have thin discriminating power at small orders, and the sieve's real value has to come from Tier 4 ranking (Im3), which hasn't run. The data also quantifies the quasirandomness probe's prediction pointwise: the top-ceiling survivors (order-504 trivial-center groups with n(G) = 2, ceiling ≈ 16.87 from the BCGPU subset-packing bound) are exactly the maximally non-quasirandom shape the probe said survivors must have. And it produced two negative-space findings that are themselves informative: T2a never fired on the processed population, and the cascade cannot certify ρ₀ = 1 for [24,10]/[24,11] — which identified a concrete missing tier (product decomposition), already noted in Im4's card.

What it is not. No survivor has been shown to do anything. The ceilings are upper bounds — necessary-condition screens — so a high ceiling means "not yet excluded," never "promising confirmed." Nothing in the data approaches a TPP construction that would matter for matrix multiplication; that would require a survivor whose actual capacity, not ceiling, beats known constructions, and computing actual capacities is exactly the expensive step the sieve exists to ration. The dataset is a ranked haystack-in-progress.

As infrastructure. The per-order JSONL checkpoints are the resume substrate for the whole remaining pipeline: Im4 resumes the 256/384 gaps against them, Im2's order-512 stratum extends them, Im3's ranking consumes them, and Pl4's Gelfand-pair extension reuses the same enumeration machinery. The checkpoint analysis confirmed they're clean enough to build on — zero malformed lines, internally consistent ceilings, schema variance that's principled short-circuiting.

The honest caveat on all of it: coverage is 73.5% of nonabelian groups in range, with the gap concentrated at order 256 — the largest single stratum. Any aggregate claim from this data ("nothing below order 512 survives ranking," say) is unsound until Im4 closes that gap, which is why the PoC bar is still unmet and why the stale summary that omitted the gap was the remediation card's first item.

On novelty, keeping the axes separate: the individual bounds are all Murthy/BCGPU — known mathematics. What has no apparent precedent (per the session's grounding, which found no such survey in the literature) is the systematic per-group application of them as a screening instrument across the entire SmallGroups range. That's a new dataset and a new method, not new theorems — and whether it becomes mathematically significant depends entirely on whether Tier 4 ranking surfaces a survivor worth a real capacity computation.
```

## `f5high-2`

### TODO-1

```
Qr1 closed — quick outcome: Im5's engine already covers all four lamplighter targets ([24,13], [64,32], [160,235], [384,5790]; ids GAP-confirmed), the n(G) = smallest-prime-factor pattern checks out against checkpoint data, and no separate program was needed. Its numbers come out of the same pending run Im5 already surfaced:

cd Scratch/GroupSieve && sage rho0.sage -- --resume --per-target-timeout 3600

(4–8 h projected — a natural follow-on once the census finishes; the two shouldn't run concurrently if you want the census's ~30-min finish to hold.) No rho_0 > 1 flags yet — that gate opens when the rho0 data exists.
```

### TODO-2

```
cd Scratch/GroupSieve && sage tier4.sage
~50 min worst case, resumable. Queue order suggestion: census (nearly done) → tier4.sage (50 min) → rho0.sage (4–8 h, overnight candidate).
```

## `f5high-3`

