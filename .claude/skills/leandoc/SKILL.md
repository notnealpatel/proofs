---
name: leandoc
description: BM25 search and exact lookup over Lean 4 source code in .lake/packages/ and the core toolchain. Use before grepping mathlib.
---

# `leandoc` — Lean Source Search

Exact name lookup and BM25 search over `.lean` sources and compiled
`.ilean` metadata. Covers `.lake/packages/` (Mathlib etc.) and the
core Lean toolchain (`Init.*`, `Std.*`).

```bash
leandoc Nat.add_comm              # exact: toolchain theorem
leandoc Option.get!               # exact: generated name with punctuation
leandoc group homomorphism        # search: multi-word BM25
leandoc -v Finset.sum             # include BM25 scores
```

## Query classification

A single whitespace-free token is an **identifier query** resolved
against the text and compiled-name indices. Anything with whitespace
is a **search query** ranked by BM25. Queries are capped at 256
bytes.

## Output envelope

```json
{"mode": "exact|search|miss", "matches": [...], "candidates": [...]}
```

### Modes

**exact** — identifier found in source text or `.ilean` compiled
names. Source-indexed hits include `body` with the full declaration.
`kind:"generated"` means the name exists only in `.ilean` metadata
(no body, no signature; `line` is 0).

**search** — BM25-ranked results, never truncated. No body; follow
up with an exact query on a match name to get the declaration body.

**miss** — identifier not found. `matches` is empty. `candidates`
lists up to 10 names sharing the same final dotted component.

### Match fields

| Field | Present | Notes |
|-------|---------|-------|
| `name` | always | dotted Lean name |
| `kind` | always | `theorem`, `def`, `lemma`, `instance`, `structure`, `generated` |
| `signature` | source hits | absent for `kind:"generated"` |
| `body` | exact source hits | full declaration; absent in search/miss and for generated |
| `docstring` | if authored | |
| `file` | always | relative to packages or toolchain |
| `line` | always | 0 for generated names |
| `score` | `-v` only | BM25 score, search mode only |

### Common mistake

The root output is an **object**, not an array: `jq '.[:5]'` fails
with `Cannot index object with object`. Slice `.matches`, never the
root. Any older guidance showing `leandoc <query> | jq '.[:10]'`
predates the envelope — rewrite it as `jq '.matches[:10]'`.

## Workflow: search then inspect

Search mode returns names without bodies. Chain a follow-up exact
query to read the full declaration:

```bash
# 1. Search to discover
leandoc group homomorphism | jq -c '.matches[:5][] | {name, kind}'

# 2. Exact query to read the body
leandoc MonoidHom.map_mul | jq '.matches[0].body'
```

## jq recipes

```bash
leandoc <query> | jq -c '.matches[:5][] | {name, kind}'
leandoc <query> | jq '[.matches[] | select(.kind == "theorem")]'
leandoc <query> | jq '.matches[0].body'                          # exact-mode body
leandoc <query> | jq -r '.matches[:10][] | "\(.file):\(.line)  \(.name)"'
leandoc Bogus.Name | jq '.candidates'
```

## When to use

| Need | Tool |
|------|------|
| Name or concept | `leandoc` |
| Type signature shape | `#loogle` |
| English description | `#leansearch` |
| Proof, not a name | `exact?` / `apply?` |
| Grep for exact string | `grep` in `.lake/packages/mathlib/` |

## `#loogle` — type-pattern search

Searches by type signature with wildcards.

```lean
#loogle Summable ?f -> Summable (fun n => ?f (n + ?k))
#loogle Finset.sum (Finset.range ?n) ?f = Finset.sum (Finset.range ?n) _
```

## `#leansearch` — natural language search

End queries with a period or question mark.

```lean
#leansearch "If a series is summable then the shifted series is summable."
#leansearch "The binomial theorem for commutative semirings."
```

Both require network access and results appear in the Lean Infoview.

## `exact?` / `apply?` — proof search

Use when the goal is closable by a single lemma with no auxiliary
proof obligations. Times out on goals requiring synthesized subproofs.

- `exact? +grind` — uses `grind` to discharge subgoals
- `exact? -star` — skips star-indexed lemmas (faster)
- `set_option maxHeartbeats N in` controls time budget
- `apply?` is sometimes cheaper — it can leave subgoals open

No parallelism flag exists. Search is sequential.
