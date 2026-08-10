---
name: oeis
description: Search and retrieve integer sequences from the OEIS. Use when identifying a sequence from terms, looking up a known sequence by ID, or searching by name.
---

# `oeis` — Integer Sequence Lookup

Local OEIS client. Three commands:

```bash
oeis show <AXXXXXX>       # full sequence entry
oeis search <query>       # search sequence names
oeis match <1,2,3,...>    # find sequences by terms
```

## Show

Returns a single JSON object with the full entry.

```bash
oeis show A000045 | jq '{id, name, terms: .terms[:60]}'
oeis show A000041 | jq '.formulas[:5]'
oeis show A000045 | jq '.comments[:5]'
oeis show A000045 | jq '.xrefs'
```

Fields: `id`, `name`, `terms` (comma-separated string),
`comments` (array), `formulas` (array), `programs` (array),
`keywords` (string), `xrefs` (array).

`terms` is a comma-separated string, not an array. Split
with `split(",")` in jq if needed:

```bash
oeis show A000045 | jq '[.terms | split(",") | .[:10] | .[] | select(. != "") | tonumber]'
```

## Search

BM25 search over sequence names. Returns JSON object.

```bash
oeis search "partition function" | jq '.matches[:5]'
oeis search "Euler totient" | jq -r '.matches[:5] | .[].id'
```

Output shape:

```json
{"query": "...", "results": 8382, "matches": [{"id": "A229225", "name": "...", "score": 12.8}, ...]}
```

Results can be large — always limit with `jq '.matches[:N]'`.

## Match

Find sequences containing a subsequence. **Output is JSONL**
(one JSON object per line), not an array.

```bash
oeis match "1,1,2,3,5,8,13" | head -5 | jq -c '{id, name}'
oeis match "2,3,5,7,11,13" | head -3
```

Each line shape: `{"id": "A000045", "name": "...", "terms": "..."}`

Every stdout line is JSON — pipe directly to jq, using `head`
to limit. The `N results` count prints to **stderr**, so it
never reaches a pipe; do not `tail -n +2` (that drops the
top-ranked result).

```bash
oeis match "1,4,9,16,25" | head -5 | jq -c '{id, name}'
```

## When to use

| Need | Tool |
|------|------|
| "What sequence is 1,1,2,5,14,42?" | `oeis match` |
| Look up A-number | `oeis show` |
| Find sequences about a topic | `oeis search` |
| Closed form for a sequence | `oeis show` → `.formulas` |
| Related sequences | `oeis show` → `.xrefs` |
| Article about a math concept | `wiki article` |
| Open Erdos problem | `erdos` |
