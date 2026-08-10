---
name: wiki
description: Search and retrieve Wikipedia articles as markdown. Use for definitions, known theorems, biographical context, and grounding claims against an encyclopedic source.
---

# `wiki` — Wikipedia Search and Retrieval

BM25-ranked search over all English Wikipedia article titles,
with full article retrieval as clean markdown. Backed by a
resident server (`wikisrv`) so queries are fast.

```bash
wiki search <query>       # search titles
wiki article <title>      # full article as markdown
wiki links <title>        # outgoing wikilinks
```

## Search

Returns JSON with BM25-scored title matches. Always pipe
through `jq` to limit output.

```bash
wiki search "Euler totient" | jq '.matches[:10]'
wiki search "sunflower conjecture" | jq -r '.matches[:5] | .[].title'
wiki search "prime gap" | jq '{results: .results, top: [.matches[:5] | .[].title]}'
```

Output shape:

```json
{"query": "...", "results": 26917, "matches": [{"title": "...", "score": 29.5}, ...]}
```

Results are capped at 100 by the server. Use jq to narrow
further — top 5 or 10 is usually sufficient.

## Article

Returns the full article as cleaned markdown with LaTeX math
preserved in `$...$` delimiters. Output goes to stdout as
plain text.

```bash
wiki article "Euler's totient function"
wiki article "Sunflower (mathematics)"
wiki article "Ramsey's theorem" | head -60
```

Redirects are followed automatically. Titles are case-sensitive
and must match exactly — use `wiki search` first to find the
right title if unsure.

For large articles, pipe through `head` or `grep` to find
specific sections:

```bash
wiki article "Prime number theorem" | grep -A 20 "## Proof"
```

## Links

Returns all outgoing wikilinks from an article as JSON.

```bash
wiki links "Euler's totient function" | jq '.links[:10]'
wiki links "Ramsey's theorem" | jq '[.links[] | select(test("conjecture"; "i"))]'
```

Output shape:

```json
{"title": "...", "links": ["number theory", "relatively prime", ...]}
```

Useful for discovering related topics and building a reading
graph around a concept.

## Error handling

Missing articles return exit code 1 with a diagnostic on
stderr. Always search first when unsure of the exact title.

## When to use

| Need | Tool |
|------|------|
| Definition or known theorem | `wiki article` |
| Find the right article title | `wiki search` |
| Related topics from an article | `wiki links` |
| Integer sequence identification | `oeis` |
| Open problem context | `erdos` |
| Lean 4 lemma names | `leandoc` |
