---
name: erdos
description: Search and retrieve Erdos problems from erdosproblems.com. Use when investigating open combinatorics/number theory problems, checking problem status, or finding related OEIS sequences.
---

# `erdos` — Erdos Problems Database

Local client for erdosproblems.com. Three commands:

```bash
erdos list                # all problems as JSON
erdos search <query>      # BM25 search over comments+tags
erdos fetch <N>           # full problem with comments
```

## List

Returns all ~1200 problems as a JSON object.

```bash
erdos list | jq '.results'
erdos list | jq '[.problems[] | select(.status.state == "open") | select(.prize != "no")] | length'
erdos list | jq '[.problems[] | select(.tags[] == "combinatorics")] | .[:5]'
```

Output shape:

```json
{"results": 1217, "problems": [{"number": "1", "prize": "$500", "status": {"state": "open", ...}, "oeis": ["A276661"], "tags": ["number theory"], "formalized": {"state": "yes", ...}}, ...]}
```

Each problem has: `number`, `prize`, `status` (`state` +
`last_update`), `oeis` (array of A-numbers), `tags`,
`formalized`, and optionally `comments` (search-only field
with matched text).

## Search

BM25 search over problem comments and tags.

```bash
erdos search "sunflower" | jq '.matches[:5]'
erdos search "prime gap" | jq '.matches[:3] | .[] | {number, prize, tags}'
erdos search "Ramsey" | jq '[.matches[] | select(.prize != "no")]'
```

Output shape:

```json
{"query": "...", "results": N, "matches": [{"number": "20", "prize": "$1000", "status": {...}, "oeis": [...], "tags": [...], "comments": "sunflower conjecture", "score": 6.1}, ...]}
```

## Fetch

Retrieves the full problem statement, structured sections,
and comments from erdosproblems.com.

```bash
erdos fetch 20 | jq '.statement'
erdos fetch 20 | jq '.comments | length'
erdos fetch 20 | jq '.sections[0][:200]'
```

Output shape:

```json
{"number": 20, "statement": "Let $f(n,k)$ be minimal...", "sections": ["Erdos and Rado...", "References..."], "comments": [...]}
```

`statement` and `sections` contain LaTeX. `sections` typically
includes progress notes and a bibliography.

## Cross-referencing with OEIS

Many problems link to OEIS sequences. Chain them:

```bash
erdos fetch 20 | jq '.number'
erdos list | jq '.problems[] | select(.number == "20") | .oeis'
# then:
oeis show A332077
```

## When to use

| Need | Tool |
|------|------|
| Is this an open problem? | `erdos search` or `erdos list` |
| Full problem statement | `erdos fetch <N>` |
| Prize problems | `erdos list` + jq filter on `.prize` |
| Problems by topic | `erdos list` + jq filter on `.tags` |
| Related sequences | `.oeis` field → `oeis show` |
| General math background | `wiki article` |
