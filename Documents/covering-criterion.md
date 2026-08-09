# A decidable fixed-divisor criterion for covered exponential families

**STATUS: POINTER SHEET, split out of `first-proofs-and-opn-reduction.md`
2026-07-31.** That sheet's §4 recommended this material become a separate
ITP/CPP submission and then kept it inline; this file is that split, executed.
The OEIS sheet now carries a stub pointing here.

**Read the timing recommendation before starting the paper.** The honest
headline today is *"a clean tool for a closed problem class"* — true, useful,
and not interesting. Everything in reach is classical, and §7 shows the
apparatus has a hard ceiling well below anything at the research frontier.
The recommendation in `first-proofs-and-opn-reduction.md` §8.1 is to write
this paper **after** the work scoped in `covering-certificates.md` lands, with
the criterion demoted to that paper's infrastructure chapter. Writing it now
produces a competent tool paper; writing it later produces a tool paper with
a result attached.

**Claim discipline.** Seven prior-art claims in this arc were believed and
turned out false — including two asserted by the orchestrator, and one
(§3.2's retracted filename-gap claim) that survived a full review pass. Every
one was caught by *retrieving* an artifact, never by reasoning or by a second
search. Re-fetch before citing anything below. Canonical grading:
`.tasks/main/docs/novelty-ErdosCovering.md`.

**Contains zero new mathematics.** Every theorem is classical — Erdős 1950,
Sierpiński 1960, Selfridge 1962. All novelty is formalization priority.

---

## 1. The contribution

`IsFixedDivisorSystem A B T` takes a certificate `T : Finset (ℕ × ℕ × ℕ)` of
triples `(a, d, p)` — residue, modulus, divisor — asserting the classes cover
ℤ, `2^d ≡ 1 (mod p)`, `p ∣ A·2^a + B`, and `1 < p`. From it,
`exists_mem_fixedDivisors_dvd` yields a divisor from a fixed finite set at
*every* exponent `n`; `.composite` upgrades to compositeness. One affine
family covers all applications: Sierpiński `(A,B) = (k,1)`, Riesel `(k,−1)`,
Erdős 1950 `(−1,m)`, dual Sierpiński `(1,k)`.

- File `Proofs/Erdos/Covering/FixedDivisor.lean`, commit `9d873d7`.
- `IsFixedDivisorSystem` (:186), `isFixedDivisorSystem_iff` (:227),
  `dvd_affine_two_pow_of_mod_eq` (:277),
  `IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd` (:293),
  `.composite` (:319), `.not_prime` (:336),
  `.of_dvd_sub_const` (:351), `.of_dvd_sub_coeff` (:370).
- Layer consumed: `Proofs/Erdos/Covering/Basic.lean` (`f2cd3df`) —
  `Covers` (:56), `IsCoveringSystem` (:63, distinct moduli all > 1),
  `covers_iff_forall_range` (:81).

### 1.1 Two framing errors to avoid

**Do not call the hypothesis a covering system.** `IsFixedDivisorSystem`
requires only `Covers (residueClasses T)`, **not** `IsCoveringSystem`. It does
*not* require moduli to be distinct, does *not* require them to exceed `1`,
does *not* require divisors to be prime — only `1 < p` — and does *not* need
`d` to be the multiplicative order; any multiple serves. The criterion is
strictly more general than the covering-system language implies, and a
referee who reads "covering system" will look for `injOn_mod` and not find
it. `Sierpinski.lean:149` separately proves the 78557 data *is* a genuine
covering system — the right instinct, but it makes the understatement look
deliberate. State the hypothesis as coverage; sell the extra generality.

**"Fixed divisor" is the wrong term and should be renamed.** Classically
(Bouniakowsky, Schinzel) a fixed divisor is a single `d` dividing *every*
value of a family. Here no such `d` exists — the covering primes each divide
only some terms. The standard name for `{3,5,7,13,19,37,73}` is a **covering
set**. `FixedDivisor.lean` / `IsFixedDivisorSystem` / `fixedDivisors` are
therefore at odds with established usage: cheap to rename now, expensive if a
referee raises it.

## 2. Prior art — verified by retrieval 2026-07-31

**The anchor citation, and it is the prior art conceding the gap.**
Cowles–Gamboa, "Verifying Sierpiński and Riesel Numbers in ACL2", EPTCS 70
(2011) 31–39, arXiv:1110.4671:

> Although the theorem that is being proved is obviously true, there does not
> appear to be a way to prove it once and for all in ACL2, not even using
> `encapsulate`. Instead, a pair of theorems very much like the ones we have
> described needs to be proved from scratch for each different Sierpiński or
> Riesel number.

They also state the macro's generation process is unverified — "we don't
bother to check that every member of C is an odd prime." Quote the
impossibility claim, not the abstract; it is stronger, and it is them saying
it rather than us.

**google-deepmind/formal-conjectures.** `CoveringSystem.lean` is exactly 61
lines, four declarations, whose only theorem `iUnion_cosets` unfolds a
structure field. **Do not say "no theorem applies it"** — `7.lean` states
`erdos_7` over `StrictCoveringSystem ℤ`. The accurate claim is narrower and
still decisive: every use is a `sorry`'d conjecture *statement*, and no
theorem derives anything from a covering system. Their `CoveringSystem` is
indexed over a general ring with `Ideal` moduli — strictly more abstract than
`Finset (ℕ × ℕ)` and correspondingly **not decidable**. The contrast between
an abstract definition nobody can compute with and a decidable one carrying
certificates is the paper's cleanest one-sentence pitch.

**plby/lean-proofs.** `Erdos275.lean` (966 lines) proves that `r` classes
covering `2^r` consecutive integers cover ℤ — a theorem *about* covering
systems, not about what they imply for a family.

**danielchin/proofs `Erdos16.lean`** — ADDED 2026-07-31, found via the
erdosproblems #16 comment thread (posted 2026-02-25), fetched and read
directly. It formalizes Chen 2023's (arXiv:2312.04120) disproof of
Erdős #16, and on the way its lemmas `firstap`/`secondap` prove that two
infinite APs (residues 992077 and 3292241 mod 11184810) consist of
integers not of the form `p + 2^k` — via `decide`-checked coverage over
the *same* primes `{3,5,7,13,17,241}` at period 24 as our
`NotTwoPowerPlusPrime.lean`. That is a machine-checked instance of the
Erdős 1950 covering construction, five months before `add6611`.
Sorry-free by grep; axiom surface unaudited; its `density_zero` is
actually "contains no infinite AP" (a weaker constraint on the
exceptional set, making the disproof formally stronger — note the
definitional quirk when citing). Consequences: §3.1's first-claim is
narrowed below, and **comment-thread artifacts are part of the sweep
corpus** — enumerating the formal-conjectures tree alone is not a sweep
of "Lean".

**Clean:** Mathlib incl. `Archive/` + `Counterexamples/`, Isabelle AFP,
Coq/Rocq, Mizar, Metamath, HOL Light, Lean 3 mathlib.

## 3. Results

### 3.1 Erdős 1950 — first machine-checked *statement* of the theorem
    (narrowed 2026-07-31)

**STANDS-NARROW.** The unqualified "first machine-checked proof" died on
retrieval of Chin's `Erdos16.lean` (see §2): the covering construction —
an infinite AP of non-representable integers, same prime set, coverage
by `decide` — is machine-checked there as lemmas toward the #16
disproof, five months earlier. What remains first: the *statement-level
infinitude theorem*, named and stated as Erdős 1950's result rather
than left implicit in AP-containment lemmas, and the derivation from a
reusable criterion (`Erdos1950Instance.lean`). Scope the paper's claim
exactly so, and cite Chin.

Infinitely many odd integers are not of the form `2ᵏ + p`. Covering system
`{0(2),0(3),1(4),3(8),7(12),23(24)}` × primes `{3,7,5,17,13,241}`, CRT
witness `m ≡ 7629217 (mod 11184810)`. The top-end `k` is handled by dyadic
block placement, not a counting argument; `erdos_1950` carries no restriction
on `k`, since oddness excludes `k = 0` free.

- File `Proofs/Erdos/Covering/NotTwoPowerPlusPrime.lean`, commit `add6611`.
- `erdosSystem1950` (:145), `isCoveringSystem_erdosSystem1950` (:158),
  `erdosPrimes1950` (:191), `erdosModulus1950` (:298),
  `erdosResidue1950` (:304), `exists_mem_erdosPrimes1950_dvd` (:401),
  `not_prime_sub_two_pow` (:424), `not_prime_sub_two` (:474),
  `erdos_1950` (:517), `erdos_1950_not_two_pow_add_prime` (:563).
- Re-derived from §1 in `Erdos1950Instance.lean` (`9d873d7`):
  `exists_mem_erdosPrimes1950_dvd_of_general` (:125),
  `not_prime_sub_two_pow_of_general` (:139) — cone-verified, and strictly
  stronger than the committed form (drops `1 ≤ k`).

### 3.2 The retracted evidence sentence — keep this, it is the method note

The previous novelty evidence read "Not in formal-conjectures (~210
`ErdosNNN.lean`, filenames jump 1141→1148)". **Every clause is wrong:** the
naming convention is `FormalConjectures/ErdosProblems/NNN.lean`; there are
**509** such files, not ~210; and `1142.lean` **exists** — 1141, 1142, 1145,
1146, 1148 are all present, so there is no gap. Verified against the repo
tree via the GitHub API and by fetching the file.

The novelty claim survives on content, because #1142 is the *opposite*
problem: `Erdos1142Prop n := 2 < n ∧ ∀ k, 0 < k → 2^k < n → (n − 2^k).Prime`
asks for `n` with *every* `n − 2^k` prime; Erdős 1950 produces `m` with
*none*. Both of `1142.lean`'s research theorems (`erdos_1142`,
`erdos_1142.variants.mientka_weitzenkamp`) are `sorry`; only seven `test_*`
witnesses are proved. ~~Erdős 1950 itself is absent from every system
swept~~ — **CORRECTED 2026-07-31: false as stated.** The construction
appears as lemmas in Chin's `Erdos16.lean` (§2); the statement-level
theorem remains absent elsewhere. The original sentence is retained
struck-through because it is itself an instance of this section's
lesson: it was true of the corpora *enumerated*, and wrong about "every
system" because comment-thread artifacts were not in the enumeration.

This belongs in the paper as a **methodology remark**, not just an erratum: a
prior-art claim produced by reasoning about a directory listing under a
guessed naming convention, which survived review, and which one API call
falsified. That is a transferable lesson for formalization novelty claims
generally.

### 3.3 Sierpiński 78557 and Riesel 509203

Both via §1 with no bespoke covering argument, plus progression lemmas giving
Sierpiński's 1960 infinitude theorem for each.

- `Sierpinski.lean` (`9d873d7`): `IsSierpinskiNumber` (:94),
  `sierpinskiCert78557` (:121),
  `isSierpinskiNumber_of_isFixedDivisorSystem` (:202),
  `isSierpinskiNumber_78557` (:218), `infinite_setOf_isSierpinskiNumber`
  (:286) via `78557 + 140100870·t`.
- `Riesel.lean` (`9d873d7`): `IsRieselNumber` (:94), `rieselCert509203`
  (:141), `isRieselNumber_509203` (:251), `infinite_setOf_isRieselNumber`
  (:319) via `509203 + 11184810·t`. Its prime set and moduli are *identical*
  to Erdős 1950's; only residues differ.

**The concrete numbers are NOT firsts.** ACL2 has both
(`verifying-macros.lisp:771`, `:813`). DeepMind proves `selfridge_78557`
sorry-free but with `native_decide` twice. **STANDS-NARROW:** ours is the
first proof of 78557 *in Lean* avoiding `native_decide` — scope to Lean,
since ACL2 has no such tactic and the unqualified phrasing invites the
comparison. Riesel 509203 is on stronger footing: a repo-wide
`grep -iE 'riesel'` over formal-conjectures returns **zero hits**, so no Lean
Riesel content of any kind exists. `IsSierpinskiNumber` matches DeepMind's
definition exactly (`Iff.rfl`).

### 3.4 A039669 / A089654 archives

- `ErdosMinus2k.lean` (`7520b62`): `IsAllPrimeMinusPow` (:157), seven
  certificates (:235–260), four negative controls (:269–286), the
  covering-congruence reduction (:323–466), `NoSmallFactor` (:623),
  `setOf_isAllPrimeMinusPow_le` (:899) — the **10⁹ window**, sorry-free.
  `erdos_1142` (:942) is the one intended sorry.
- `ErdosRows.lean` (`7520b62`): `erdosRow` (:99),
  `forall_prime_erdosRow_iff_isAllPrimeMinusPow` (:196) — the bridge proving
  A089654's conjecture *is* A039669's odd part; `erdos_a089654` (:336).

**Anchors (added 2026-07-31).** A039669 has *two* live erdosproblems
anchors, not one: #1142 (its statement, open) and #236 (open,
`f(n) = o(log n)?`, whose OEIS links include A039669 alongside A109925).
The companion #237 was solved by Chen–Ding 2022 for arbitrary infinite
`A`, with Erdős 1950's `2^k` case as the seed — cite both when placing
the archive.

**Novelty.** A089654 — **STANDS**, first formalization anywhere. The A039669
*statement* — **DEAD**, DeepMind has it. The 10⁹ window — **STANDS-NARROW**:
DeepMind's 2⁴⁴ instance is `sorry`'d, so ours is the first sorry-free one,
but 10⁹ ≪ 2⁴⁴ and it discharges nothing upstream. The search reduction is
**DEAD/attributed** — Chris Nash, primepuzzles.net prob_003, 15 Sep 2000,
verbatim and reaching further (primes to 67). Cite Nash; never claim the
sieve.

### 3.5 Reach established this session, not yet built

- **Brier numbers.** `k = 3316923598096294713661` (Clavier), both
  certificates verified externally against all four fields, zero uncovered
  residues, all divisors prime. Sierpiński side `L = 48`, 7 triples; Riesel
  side `L = 180`, 13 triples; max 109 bits. **No shared skeleton** — the
  sides share only the prime 3 and the modulus 2, so a Brier certificate is
  two independent instances. No cheaper witness exists: the record number is
  also the smallest.
- **Dual Sierpiński is already in scope** as `(A,B) = (1,k)` — no new
  machinery. Witness by CRT through the Selfridge skeleton:
  `k ≡ 58049738 (mod 70050435)`, first odd member `128100173`.
- **Base-`b` parameterisation** (`PLAN.md` lane A′) is the highest-value
  extension: nothing in `FixedDivisor.lean` uses the numeral `2`, every proof
  goes through verbatim, decidability survives. Reaches base-`b`
  Sierpiński/Riesel (cf. A273987).

## 4. The abstraction result — a negative one worth publishing

The natural generalisation is "replace `2^n` by any sequence periodic mod
`p`." **That is the wrong axis, and the counterexample is the motivating
application.** Verified directly against Wilf's A083216: an 18-triple
certificate at `L = 8640` in which every modulus equals `α(p)`, the **rank of
apparition**, and for 13 of 18 primes `α(p)` is a *proper* divisor of the
Pisano period `π(p)` — `(p, d, α, π) = (3,4,4,8), (7,8,8,16), (47,16,16,32),
(2521,60,60,120), …`. So the sequence is **not** periodic mod `p` with period
`d`; only its **zero set** is.

The correct shared hypothesis is therefore

    for each (a, d, p):   ∀ n, n % d = a % d → p ∣ s n

which both families satisfy by *different* mechanisms — `ord_p(2)` for
exponential, `α(p)` for Fibonacci-like — and which is **not decidable as
stated**. Consequences, and they are the paper's most transferable content:

- the abstract layer is ~15 lines and buys **statement** reuse only;
- the `decide` pipeline lives in per-family bridges and does **not**
  abstract;
- "periodic mod p" is a natural-looking generalisation that silently
  excludes half its intended instances.

## 5. Honest boundaries — state these or imply falsehoods

- **Izotov (1995):** some fourth powers are Sierpiński **with no covering set
  at all**, via an aurifeuillean factorisation. This framework provably
  cannot reach them. *"Covering systems characterize Sierpiński numbers" is
  false* and easy to imply by accident.
- **The Sierpiński problem** (is 78557 least?) is a search question no
  covering argument touches; PrimeGrid is down to `k = 21181, 22699, 24737,
  55459, 67607`.
- **Nothing here touches the theorems *about* covering systems** — Hough
  2015, Hough–Nielsen 2019, BBMST 2022. Those prove universal non-existence
  by probabilistic methods and never construct a system. The committed
  definitions supply their statement vocabulary and ~200 lines of preamble,
  under 3% of the effort. Do not let a reader infer otherwise.

## 6. Audit trail

Vacuity: no vacuous statement found; one prose defect fixed (the
`FixedDivisor.lean` §5 preamble claimed all four certificate fields
load-bearing for the general theorem, but `one_lt_divisor` is absent from its
proof cone and is load-bearing only for `.composite`/`.not_prime`). Three
misdirected cross-references and two imprecise descriptions corrected. All
declarations swept cold for axioms, allowlist-subset check.

**Method note for anyone repeating the cone analysis:**
`Lean.ConstantInfo.value?` defaults `allowOpaque := false` and returns `none`
for *every* theorem, and constants must be read from the kernel environment —
a naive cone probe silently reports empty cones and yields false acquittals.

## 7. The ceiling — why this paper wants a sequel

Measured 2026-07-31 on a 24 GB box, cold `lake env lean`, recorded in
`Proofs/Scratch/CoverCeiling.lean`: coverage by kernel `decide` through
`covers_iff_forall_range` completes at `L = 16384` in 92 s and **exhausts
memory** at `L = 65536`. Growth ≈ `L^1.6`; three walls arrive in order —
`maxHeartbeats`, then `maxRecDepth`, then the OOM killer.

Everything this criterion reaches has tiny `L`: Selfridge 36, Erdős 1950 24,
Brier ≤ 180, Wilf 8640. Everything at the research frontier does not —
Krukenberg's minimum-modulus-18 system is at `L ≈ 4.75·10¹⁴` and
Nielsen/Owens at `L ≈ 10⁴⁴⁹⁵`. Hardware does not close this: an order of
magnitude more RAM buys about one rung out of ~4490.

That is the boundary of the present work, and it is the thesis of
`covering-certificates.md`, which scopes the compositional certificate that
would cross it. **This paper is that paper's infrastructure chapter.**

## 8. Venue and relation to the sibling drafts

Venue: ITP / CPP / JAR formalization track. Comparison points are
Cowles–Gamboa 2011 (ACL2) and Dahmen–Hölzl–Lewis ITP 2019, **not** the
OEIS-conjecture framing of the sibling sheet.

- `first-proofs-and-opn-reduction.md` — the OEIS results (A354741, A000670,
  A114976, A014701). Disjoint from this paper; its §4 is now a stub pointing
  here.
- `covering-certificates.md` — the sequel, and the reason to delay this
  submission. Its §7 explains the dependency in the other direction.

Extension lanes, all scoped with measured costs: `PLAN.md` (repo root).
