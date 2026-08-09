# Drafting context — Erdős #406 barrier: blog post and/or erdosproblems comment

```
TODO
- [ ] Venue decision: (a) blog post, (b) erdosproblems.com #406 comment, (c) both
      (comment compact, post narrative; both can share the fact-check table below).
- [ ] Public repository URL for links ([TODO-URL] below).
- [ ] USER publishes; nothing here is to be posted by an agent.
- [ ] DW16 is paywalled (user-supplied PDF at repo root, not redistributable):
      public quotes limited to short fair-use excerpts (Definition 5, Theorem 12
      statement, Table 1 line) — already the only ones used below.
- [ ] Optional pre-publication: fix parent PowerOfTwoDigits.lean docstring
      "2^j surviving residues" imprecision (should be 2^(j-1) exponent classes at
      modulus 3^j) before pointing public readers at the file tree.
```

Provenance: commit 4455bf3 (branch f5exp, 2026-08-07): `Proofs/Enumerative/
PowerOfTwoDigitsCount.lean` + `PowerOfTwoDigitsBarrier.lean`, both sorry-free,
axioms ⊆ {propext, Classical.choice, Quot.sound}, no native_decide, each passed
an adversarial vacuity audit (the barrier audit's one finding — a docstring
novelty overreach — was repaired pre-commit). Parent archive: commit 4bb6675
(wave 3). Sources read: [La09] in full (References/arXiv-math-0512006), [DW16]
in full (dupuy15.pdf, user-supplied), [LZ26] probed (References/arXiv-2601-12753).
Computations: Go, this session — mirror search exhaustive to n ≤ 10^7; Wieferich
grid a ≤ 200000, p ≤ 97; all headline computations re-verified in-kernel where
cited as such (see fact-check table).

---

## The headline, three registers

**One-liner.** A machine-checked boundary certificate for Erdős #406: the first
formalization of everything the known unconditional method proves — and a formal
proof that it can prove nothing more.

**Abstract-length.** We formalize in Lean 4 the exact frontier of congruence
methods on Erdős #406 (are 1, 4, 256 the only powers of 2 with ternary digits in
{0,1}?): the Narkiewicz–Lagarias counting bound N(x) ≤ 2·x^(log₃2) from one
side, and its provable optimality from the other — the sieve retains exactly 2^j
exponent classes at every depth, every surviving class is fully realized, and
every {0,1}-digit pattern (unit type) is realized by an actual power of 2 at
every finite 3-adic depth. The mechanism separating decidable from immortal
digit-set problems is the Wieferich window of Dupuy–Weirich: as contrast we
formally decide a windowed instance (18^n has all base-7 digits in {2,4} iff
n = 1). The pair (2, base 3) has window width zero; Erdős #406 is hard exactly
where its Wieferich window isn't.

**Guardrails (what must NOT be claimed).**
- No progress on #406 itself; the conjecture is exactly as open as before.
- Method barrier ≠ logical unprovability. Never suggest independence; the
  barrier is relative to congruence/low-digit techniques, and the techniques
  that decided neighboring strata (Stewart/Baker) are exactly outside it.
- Novelty phrasing, verbatim discipline: the dichotomy is "not stated in
  [La09], in [DW16], or in [LZ26]" — never "new", never "absent from the
  literature". Register precedent: DW16's own "appears to be absent in the
  literature" for their Conjecture-1 observation.
- The window mechanism itself is PUBLISHED (DW16 Definition 5 + Theorem 12;
  LZ26 number-field generalization). Genealogy: mechanism DW16 → generalized
  LZ26 → decidability application formalized here.
- "No congruence proof exists" is metamathematical commentary on the theorems,
  not itself a Lean theorem (the files say this explicitly; the post must too).

## Claim ledger (informal ↔ formal)

| Informal claim | Lean declaration | File |
|---|---|---|
| N(x) ≤ 2·x^(log₃2) ([La09] Thm 1.4, λ=1) | `card_erdos406_filter_le_rpow` | Count |
| ℕ window bound, any depth | `card_erdos406_filter_le` | Count |
| Exactly 2^j survivor classes (period 2·3^j, digit-depth j+1) | `card_sieveClasses` | Count |
| ord(2 mod 3^(j+1)) = 2·3^j — window width 0 for (2,3) | `orderOf_two_zmod_three_pow` | Barrier |
| Every admissible class fully realized | `sieveAt_of_mem_sieveClasses_of_modEq` | Barrier |
| Truncated count over m periods = m·2^j exactly (bound attained) | `card_range_mul_filter_sieveAt` | Barrier |
| Every {0,1}-digit unit residue is 2^n mod 3^(j+1) (fake solutions) | `exists_two_pow_mod_eq_of_base3ZeroOne` | Barrier |
| 18^n has all base-7 digits in {2,4} iff n = 1 | `base7TwoFour_eighteen_pow_iff` | Barrier |
| Window witnesses: 18³ ≡ 1 mod 7, 49, 343; 18³ % 2401 = 1030 | `eighteen_wieferich_window` | Barrier |

## Story beats (candidate arc for the blog post; cut freely)

1. **The seed.** #406, then the upside-down mirror: powers of 3 in base 5
   against four digit sets. Data (exhaustive to n ≤ 10^7): S={0,1,2} → n ∈
   {0,3,8}; S={3,4} → {1}; S={0,1,4} → {0,2,6}; S={0,2,3} → {1,7}. The random
   model predicts ≈2.4 solutions for the 3-digit sets and ≈1.1 for the 2-digit
   set — matching 3/3/2 and 1. Largest exponent 8, same as #406: cute, and
   exactly what geometric decay predicts (not a phenomenon).
2. **The sieve tree.** Low digits are periodic; survivor counts multiply by
   exactly |S| per depth once past depth 1. Same law in the original: 2^(j-1)
   survivors against period 2·3^(j-1) — the Narkiewicz exponent log₃2 is the
   tree's branching ratio, and it equals the Hausdorff dimension of the digit
   Cantor set.
3. **Wieferich windows.** Where does exact branching fail? Exactly at levels
   where the multiplicative group fails to grow — DW16's "p-Wieferich at r".
   Grid scan: Fermat quotients look perfectly random (counts match the 1/p
   heuristic on the nose: 16000 = 200000·(4/5)·(1/2)·(1/5) at p=5), but WHICH
   a's are degenerate is rigid algebra (Teichmüller APs: 57, 68, then +125;
   w=3 at 182, 443). Sporadic small pair: (18,7), from 18³ = 5832 = 17·343+1.
4. **Death.** Inside a window the tree can only prune; the search found 21
   instances where pruning kills everything AND solutions exist. Crown jewel,
   5-line proof, now kernel-checked: 18^n has all base-7 digits in {2,4} iff
   n = 1. (18³ ≡ 1 mod 7³, so the low-3-digit patterns cycle through
   {(1,0,0),(4,2,0),(2,4,6)}, each containing a forbidden digit; so solutions
   have 18^n < 343; check n = 0,1,2.)
5. **The dichotomy, and #406.** Post-window branching is exactly ×|S| ≥ 2 —
   it never kills. So sieve-decidability happens ONLY through windows. The pair
   (2,3) has window width zero (2² − 1 = 3, valuation exactly 1) — and mod 3,
   sporadic windows are group-theoretically impossible. Consequences,
   formalized: exact binary branching forever; every admissible pattern
   realized; every 3-adic unit is a limit of powers of 2, so the {0,1}-digit
   fake solutions are everywhere and 3-adically indistinguishable from real
   ones. Any proof of #406 must couple digit strings to Archimedean size —
   which is exactly what the methods that DID decide neighboring strata do
   (repdigits: one Zsygmondy-style prime; ≤K nonzero digits: Stewart/Baker).
   Bonus color: DW16's Table 1 notes 2 IS 3-Wieferich at 3 — the dual pair
   (3, base 2) has a window; the two Erdős-adjacent pairs sit on opposite
   poles.
6. **The formalization story (optional meta-beat).** Brief → prover → two
   adversarial vacuity audits. The audits earned their keep: one caught the
   coordinator's wrong digit list for 5832 (prover investigated instead of
   patching around it); one PROVED IN LEAN that a hypothesis was load-bearing
   by refuting the strengthened claim at v = 7 = (21)₃. Lean as claim hygiene,
   not just proof checking.

Tone options: (a) exploratory narrative ("we turned it upside down"), keeps
beats 1–6; (b) results-first technical note, beats 2–5 only; (c) thread-compact
(the comment below). Title candidates: "Why Erdős #406 is hard, kernel-checked";
"The exact frontier of the congruence sieve on Erdős' ternary conjecture";
"Wieferich windows and a machine-checked barrier"; "Turning an Erdős problem
upside down (and proving why it won't tip over)".

## Candidate erdosproblems.com #406 comment (compact seed; stands alone)

> The sieve behind Narkiewicz's bound N(X) ≤ 1.62·X^(log_3 2) (and Theorem 1.4
> of [La09], which gives constant 2 for all λ) is now formalized in Lean 4,
> including its exactness: at digit-depth j+1 the congruence sieve retains
> exactly 2^j of the 2·3^j exponent classes, every surviving class is fully
> realized, and every {0,1}-digit pattern with unit digit 1 occurs as
> 2^n mod 3^(j+1) — so congruence information at any fixed depth cannot decide
> the conjecture. By contrast, the same sieve completely decides digit-set
> instances where the pair has a Wieferich window in the sense of Dupuy–Weirich
> (2016): for example, 18^n has all base-7 digits in {2,4} exactly when n = 1,
> because 18^3 ≡ 1 (mod 7^3). The pair (2, 3) has no such window (2^2 − 1 = 3),
> which is one way to make precise why elementary congruence methods stall on
> this problem. Lean sources: [TODO-URL].

Thread-norm check: factual, no novelty claims, links out, no self-promotion
beyond the source pointer; consistent with the thread's existing DW16 comment
(post-2148), which this complements rather than repeats.

## Fact-check table

| Fact | Status |
|---|---|
| #406 witnesses n ∈ {0,2,8}; window n ≤ 1000 | kernel (parent, wave 3) |
| Mirror data (four sets, solutions as in beat 1) | Go, exhaustive n ≤ 10^7; n ≤ 1000 NOT kernel-checked (no Lean mirror by design) |
| Survivor counts 2^(j-1) vs period 2·3^(j-1) (depths 1–8) | kernel to depth 4 (parent + Count ground truths); Go to depth 8; all j: `card_sieveClasses` |
| N=19 instance: count 3, bound 8 (ℕ), 3 ≤ 2·19^α₀ ≈ 12.82 ≤ 38 (ℝ) | kernel (Count §7, post-polish) |
| Narkiewicz 1.62·X^α₀, α₀ = log₃2 ≈ 0.63093 | source-pinned ([Na80] via problem page + [DW16] p.1 + [La09]); 1.62 NOT formalized |
| [La09] Thm 1.4: Ñ_λ(X) ≤ 2X^α₀ ∀λ≠0 | source-pinned, paper.tex ≈528–548; λ=1 case formalized |
| ord(2 mod 3^(j+1)) = 2·3^j; 2 ≢ ±1 mod 9 | kernel (`orderOf_two_zmod_three_pow`); audit probed j=0,1,2 exhaustively |
| 18³ = 5832 = 17·343 + 1; digits₇(5832) = [1,0,0,3,2]; digits₇(18) = [4,2]; digits₇(324) = [2,4,6] | kernel (`eighteen_wieferich_window`, `digits_seven_eighteen_pow`) |
| Grid stats: p=5 w≥1 count 16000 = heuristic exactly; w≥2 = 3200; Teichmüller 57² ≡ −1 mod 125; 21 death instances w/ solutions | Go only (a ≤ 200000, p ≤ 97); NOT kernel-checked; phrase as computation |
| Every 3-adic unit is a limit of powers of 2 | formalized in finitary form (`exists_two_pow_mod_eq_of_not_dvd`); the Z₃-limit phrasing is gloss |
| DW16 Def 5, Thm 12, Remark 2 (Conj 1 ⇒ Erdős), Table 1 "2 is 3-Wieferich at 3" | source-pinned, quotes audited verbatim vs PDF |
| [LZ26] "α-Wieferich at r" = window level; r/r−1 convention differs from DW16's r/r+1 | source-pinned; conventions must not be conflated (files keep them straight) |
| Dichotomy "not stated in [La09]/[DW16]/[LZ26]" | search claim, three sources only — exact phrasing required |
| Saye verification 16 ≤ n ≤ 5.9×10^21 | source-pinned ([Sa22] via problem page); NOT re-verified beyond n ≤ 1000 |

## Iteration protocol

To iterate: pick venue + tone + length; say which beats to cut; whether the
mirror-seed origin stays (it is the charm, and the length). I draft against
this file, you edit; every number in a draft must trace to a row above — if a
draft needs a fact not in the table, the fact gets verified and added first.
