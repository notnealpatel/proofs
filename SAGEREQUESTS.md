# SAGEREQUESTS — USER-run Sage invocations

All sieve/sweep computations are USER-run per system.md policy; agents
deliver the programs and this queue. All commands run from
`Scratch/GroupSieve/` unless noted. Every program is resumable —
Ctrl-C is safe, re-run the same command to continue.

## Pending

### 1. gelfand.sage — Gelfand-pair screen, orders 2..100

```
cd Scratch/GroupSieve && sage gelfand.sage
```

- Options: `-- --resume`, `-- --order-min N --order-max M`,
  `-- --dry-run` (space stats only).
- Runtime: ~3 min projected, 5 min upper bound (1036 nonabelian
  groups at ~0.15s each).
- Output: `gelfand-screen.jsonl`; checkpoint
  `checkpoints/gelfand_progress.jsonl`.
- Provenance: Im7 / Pl4 CC campaign
  (`.tasks/f5exp/docs/Im7-gelfand-run.md`).

### 2. groupsieve.sage --stratum-b — order-512 fixed-seed sample

```
cd Scratch/GroupSieve && sage groupsieve.sage -- --stratum-b --pilot 200
```

then, after reviewing the pilot's runtime projection:

```
cd Scratch/GroupSieve && sage groupsieve.sage -- --stratum-b
```

- Deterministic uniform sample (seed 20260711, default 10,000 ids)
  from the 10,494,213 order-512 groups; Wilson 95% CI appended to
  the summary. Kept strictly separate from stratum A.
- Output: `checkpoints/stratum_b_512.jsonl` + SAMPLE ESTIMATE
  section in sieve-summary.md.
- Provenance: Im2 (`.tasks/f5exp/docs/Im2-stratum-b.md`).

### 3. rho0.sage — exact rho_0 for 73 targets (overnight candidate)

```
cd Scratch/GroupSieve && sage rho0.sage -- --resume --per-target-timeout 3600
```

- Exact subgroup TPP ratio engine; 73 targets across 4 categories,
  including the four lamplighters ([24,13], [64,32], [160,235],
  [384,5790]).
- Runtime: 4-8 h projected; order-160/384 lamplighters may report
  partial results at timeout.
- Output: `rho0-results.jsonl`.
- Gates: Pf3's computational kill-test reads this; Qr1's lamplighter
  table (`.tasks/f5exp/docs/Qr1-lamplighter.md`) fills from it; any
  rho_0 > 1 row is a surface-immediately flag.
- Provenance: Im5 (`.tasks/f5exp/docs/Im5-rho0-manifest.md`), Qr1.

### 4. lemma_sweep.sage — Lemma M / Lemma D kill-test, orders 2..64 + survivors

```
cd Scratch/GroupSieve && sage lemma_sweep.sage
```

- Options: `-- --shard I/N`, `-- --lemma-d` (also run Lemma D),
  `-- --limit K`, `-- --dry-run`.
- Space: 2604 targets (469 nonabelian groups order 2..64, plus 2135
  sieve survivors at orders 96/128).
- Runtime: ~2-3 hours single-core (Lemma M only); ~6 hours with
  `--lemma-d`. Shardable: `--shard 0/4` through `--shard 3/4`.
- Output: `lemma-sweep-results.jsonl` (or per-shard
  `lemma-sweep-results.shard{I}of{N}.jsonl`). Resume unions across
  all shard files.
- **Kill-test**: a single row with `"VIOLATION": true` or
  `"D_FAILURE": true` kills the Pf3 conjecture. Surface immediately.
- Gates: T3c tier activation in groupsieve.sage — the conjecture-gated
  prune (`T3C_CONJECTURE=1`) should not be enabled until this sweep
  completes with zero violations.
- Provenance: Pf3 (`.tasks/f5exp/docs/Pf3-abelian-factor.md`) + Im6.

Suggested order: 1 (3 min) -> 2 pilot -> 3 overnight -> 4, with 2's
full sample scheduled off the pilot's projection. Programs are
single-core; running two concurrently on this box is fine.

## Utilities (run as needed)

```
cd Scratch/GroupSieve && sage groupsieve.sage -- --harness-only   # 20-assertion falsifiability harness
cd Scratch/GroupSieve && sage groupsieve.sage -- --summary-only   # regenerate sieve-summary.md from checkpoints
cd Scratch/GroupSieve && sage census.sage -- --dry-run            # census target count + projection
cd Scratch/GroupSieve && sage gelfand.sage -- --dry-run           # gelfand space stats
```

`--summary-only` is regeneration-safe as of 2026-07-12 (hand-authored
sections moved to durable docs; the generator emits pointers).

## Completed (provenance)

| Invocation | Completed | Result |
|---|---|---|
| `sage groupsieve.sage -- --order-timeout 0` | 2026-07-12 01:09 UTC | Stratum A closed: 510/510 orders, 91,774 nonabelian records, harness 20/20 |
| `sage census.sage -- --workers 4` | 2026-07-12 ~02:22 UTC | 88,185 records, 0 errors, 10,256 (11.63%) with abelian direct factor; ~47 min on 4 cores |
| `sage tier4.sage` | 2026-07-12 ~03:00 UTC | 50/50 top-ceiling survivors, 0 timeouts, ~20s after orchestrator fixed 3 defects (pexpect gap -> libgap, RDF round(), cls[0] identity bug). snr uniformly 1.000 (Carter-subgroup degeneracy — see note in Im3-ranking.md); m(G) = 2 across the top-50 |

Cluster note: `census.sage` set the sharding pattern — deterministic
`--shard I/N` slices, resume unions across all shard files, so local
runs and future 256-way cluster runs interoperate on the same data.
