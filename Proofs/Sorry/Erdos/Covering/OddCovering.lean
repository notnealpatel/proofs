import Erdos.Covering.OddCovering

/-!
Quarantined admissions and their dependent consequences. Production supplies the
independent infrastructure; the declarations below retain their original statements
and proofs. The original source and disclosure documentation is retained below.
No mathematical proof closure is claimed.
-/

/-
  Erdős Problem #7 — covering systems with all moduli odd.

  ── The primary source, verbatim ────────────────────────────────────
  `goof erdos fetch 7`, pulled 2026-08-05.  Statement field, verbatim:

    "Is there a distinct covering system all of whose moduli are odd?"

  Sections field, verbatim (line breaks ours, LaTeX as stored):

    "Asked by Erd\H{o}s and Selfridge (sometimes also with Schinzel).
     They also asked whether there can be a covering system such that
     all the moduli are odd and squarefree. The answer to this stronger
     question is no, proved by Balister, Bollob\'{a}s, Morris,
     Sahasrabudhe, and Tiba \cite{BBMST22}.

     Hough and Nielsen \cite{HoNi19} proved that at least one modulus
     must be divisible by either $2$ or $3$. A simpler proof of this
     fact was provided by Balister, Bollob\'{a}s, Morris, Sahasrabudhe,
     and Tiba \cite{BBMST22}, who also prove that if an odd covering
     system exists then the least common multiple of its moduli must be
     divisible by $9$ or $15$.

     Selfridge has shown (as reported in \cite{Sc67}) that such a
     covering system exists if a covering system exists with moduli
     $n_1,\ldots,n_k$ such that no $n_i$ divides any other $n_j$ (but
     the latter has been shown not to exist, see [586]).

     Filaseta, Ford, and Konyagin \cite{FFK00} report that Erd\H{o}s,
     'convinced that an odd covering does exist, offered \$25 for a
     proof that no odd covering exists; Selfridge, convinced (at that
     point) that no odd covering exists, offered \$300 for the first
     explicit example...no award was promised to someone who gave a
     non-constructive proof that an odd covering of the integers
     exists...Selfridge (private communication) has informed us that he
     is now increasing his award to \$2000.'"

  References field, verbatim:

    "[BBMST22] Balister, Paul and Bollob\'{a}s, B\'{e}la and Morris,
     Robert and Sahasrabudhe, Julian and Tiba, Marius, *On the
     Erd\H{o}s covering problem: the density of the uncovered set*.
     Invent. Math. (2022), 377-414.
     [FFK00] Filaseta, M. and Ford, K. and Konyagin, S., *On an
     irreducibility theorem of {A}. Schinzel associated with coverings
     of the integers*. Illinois J. Math. (2000), 633--643.
     [HoNi19] Hough, Robert D. and Nielsen, Pace P., *Covering systems
     with restricted divisibility*. Duke Math. J. (2019), 3261-3295.
     [Sc67] Schinzel, A., *Reducibility of polynomials and covering
     systems of congruences*. Acta Arith. (1967/68), 91-101."

  Comment by *Zeraoulia Rafik*, 13:55 on 24 Jan 2026, verbatim (this is
  the source of §5 below):

    "I wrote a brief note recording a folklore necessary condition for
     Erdős Problem~\#7.  If $\{a_i \bmod m_i\}_{i=1}^k$ is a distinct
     covering system and $L=\mathrm{lcm}(m_1,\dots,m_k)$, then
     \[\sum_{\substack{d\mid L\\ d>1}} \frac{1}{d} \ge 1\qquad
     \text{equivalently}\qquad \sigma(L)\ge 2L,\] so $L$ must be
     abundant.  In particular, any \emph{odd} distinct covering would
     require odd abundant $L$, hence $L\ge 945$ (since $945$ is the
     smallest odd abundant number).  This observation appears in
     community discussions (e.g.\ MathOverflow); my note provides a
     self-contained proof and a small reproducible script listing
     candidate overall moduli $L$ (together with $\sigma(L)/L$) in a
     given range."

  Comment by *Adenwalla*, 03:11 on 05 Nov 2025, verbatim (the site was
  updated in response):  "The question should say 'distinct' covering
  system."

  ── Status: OPEN IN BOTH DIRECTIONS ─────────────────────────────────
  The database statement is a *question*, not a conjecture, and neither
  answer is known.  Erdős believed the answer is yes and staked $25 on
  a proof that it is no; Selfridge believed the answer is no and staked
  (ultimately) $2000 on an explicit example.  `erdos_7` below states
  the Erdős side — existence — because that is the side Erdős
  conjectured; it carries this file's single intended `sorry`.  That
  `sorry` is NOT evidence for the direction: if the Selfridge side is
  ever proved, `erdos_7` is false as stated and must be replaced by
  `¬ OddCoveringExists`.  Both sides are named in §3 so that either can
  be cited.

  The 2026 comment thread on the problem page records two AI-assisted
  attempts at the Selfridge side, both rejected.  Verbatim, *Nat
  Sothanaphan*, 15:48 on 06 May 2026, on the first:  "The assumed axiom
  bbmst_sf_lt_1 is false. ... Here sieveProd, as defined, has to be at
  least $1$. So the axiom that it is less than $1$ is impossible."  And
  the site owner *Thomas Bloom*, 10:10 on 07 May 2026:  "I will only
  allow further comments in this thread referring to this proof attempt
  if it is a link to a complete, self-contained, Lean formalisation,
  without any sorry or axioms appealing to external work."  Accordingly
  this file states published results as `Prop`-valued definitions
  (§6) — never as `sorry`-carrying theorems — so that nothing here can
  be mistaken for a formalization of [BBMST22] or [HoNi19].

  ── Relation to the upstream formalization ──────────────────────────
  `google-deepmind/formal-conjectures` states this problem over an
  ideal-theoretic covering system.  Retrieved 2026-08-05 from
  `https://raw.githubusercontent.com/google-deepmind/formal-conjectures/
  main/FormalConjectures/ErdosProblems/7.lean`, verbatim:

      /--
      Is there a covering system all of whose moduli are odd (and
      greater than 1)?
      -/
      @[category research open, AMS 11]
      theorem erdos_7 : answer(sorry) ↔
          ∃ (C : StrictCoveringSystem ℤ), ∀ i,
            ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
        sorry

  and from `FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`,
  verbatim:

      structure CoveringSystem (R : Type*) [CommSemiring R] where
        ι : Type
        [fintypeIndex : Fintype ι]
        residue : ι → R
        moduli : ι → Ideal R
        unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R)
          = @Set.univ R
        ne_bot : ∀ i, moduli i ≠ ⊥
        ne_top : ∀ i, moduli i ≠ ⊤

      structure StrictCoveringSystem (R : Type*) [CommSemiring R]
          extends CoveringSystem R where
        injective_moduli : moduli.Injective

  **The difference, stated explicitly.**  Upstream indexes by an
  abstract `Fintype ι` and carries moduli as elements of `Ideal ℤ`;
  `¬ moduli i ≤ Ideal.span {2}` is "the generator is odd", `ne_top` is
  "the generator is not 1", `ne_bot` is "the generator is not 0", and
  `injective_moduli` is distinctness.  Nothing in that presentation is
  a kernel check: `⋃ i, … = Set.univ` is an equality of `Set ℤ`, and the
  only `DecidableEq (Ideal ℤ)` Mathlib supplies is the `noncomputable`
  `Submodule.decidableEq`, which is `Classical.typeDecidableEq` and so
  reduces to nothing.

  This file instead encodes a system as a `Finset (ℕ × ℕ)` of
  (residue, modulus) pairs — the encoding already fixed by
  `Erdos.Covering.Basic` — for which `IsOddCoveringSystem` becomes a
  bounded, `decide`-able check (§2).  That is the contribution here and
  it is a *restatement*, not a proof of anything upstream leaves open.
  The two encodings agree on the mathematics; §4 discharges the one
  gap a reader should worry about, namely that restricting residues
  from `ℤ` to `ℕ` loses nothing.  The remaining differences —
  `Ideal ℤ` versus `ℕ` for the moduli, `Fintype ι` versus `Finset` for
  the index — are bookkeeping, and are NOT formally bridged here
  because `formal-conjectures` is not a dependency of this repository.

  ── Contents ────────────────────────────────────────────────────────
  * §1  `IsOddCoveringSystem`, `OddCoveringExists` — the predicate and
        the archived question, on top of `Erdos.Covering.Basic`.
  * §2  `isOddCoveringSystem_iff` — the decidable characterization:
        for any positive common multiple `L` of the moduli, all four
        defining clauses become bounded quantifications, so a claimed
        odd covering system is checkable by kernel `decide`.  Negative
        controls included.
  * §3  `erdos_7` — the archived question, the file's single intended
        `sorry`.
  * §4  `natResidue`, `isCoveringSystem_image_natResidue`,
        `oddCoveringExists_of_int_residues` — the ℤ-residue → ℕ-residue
        normalization, i.e. the ℕ-encoding of §1 is no restriction.
  * §5  `two_mul_lcm_le_sum_divisors` (σ(L) ≥ 2L for the lcm of ANY
        covering system), `odd_lcm_of_odd_mod`,
        `no_odd_abundant_lt_945`, and the corollary
        `nine_hundred_forty_five_le_lcm`: the lcm of an odd covering
        system is at least 945.  Sorry-free, and the Zeraoulia comment
        above is its source.
  * §6  `BBMSTNoOddSquarefreeCovering`, `HoughNielsenTwoOrThreeDvd`,
        `BBMSTLcmNineOrFifteen`, `SelfridgeAntichainReduction` — the
        published boundary results as `Prop`-valued definitions, with
        proved consequences that take them as explicit hypotheses.
  * §7  Ground truth and satisfiability.
  * §8  Axiom audit.

  ── Vacuity disclosure ──────────────────────────────────────────────
  Every statement whose hypothesis is `IsOddCoveringSystem S` is
  vacuously true if the answer to Erdős #7 is "no".  That is
  unavoidable and is flagged at each such theorem.  The mitigation is
  that each *component* is stated and instantiated in a range where it
  is not vacuous: `two_mul_lcm_le_sum_divisors` is about arbitrary
  covering systems (witness: `erdosSystem`), `odd_lcm_of_odd_mod` is
  about arbitrary odd-moduli families (witness: `oddCandidate`), and
  `no_odd_abundant_lt_945` is about natural numbers (witness: 945).

  ── Axiom audit ─────────────────────────────────────────────────────
  `erdos_7` carries the single intended `sorry` and reports `sorryAx`
  by construction; it is the only declaration allowed to.  Every other
  declaration reports a subset of
  {propext, Classical.choice, Quot.sound}.  No `native_decide`, no
  `admit`, no custom axioms.
-/



set_option autoImplicit false

namespace Erdos.Covering

/-- **Erdős Problem #7** (Erdős–Selfridge, sometimes with Schinzel):
    "Is there a distinct covering system all of whose moduli are odd?"
    OPEN; this is the file's single intended `sorry`.

    **Direction disclosure.**  The database statement is a question and
    neither answer is known.  This declaration states the *existence*
    side because that is the side Erdős conjectured — Filaseta–Ford–
    Konyagin report that he was "convinced that an odd covering does
    exist" and offered $25 for a proof that no odd covering exists,
    while Selfridge offered ultimately $2000 for an explicit example.
    The `sorry` is not evidence: `¬ OddCoveringExists` is equally
    unproved, and a proof of it would make this declaration false as
    stated.

    **Fidelity.**  `IsOddCoveringSystem` carries all four requirements
    of the database statement: distinct moduli
    (`IsCoveringSystem.injOn_mod` — the "distinct" the Adenwalla comment
    added), moduli greater than `1` (`IsCoveringSystem.one_lt_mod`),
    moduli odd (`IsOddCoveringSystem.odd_mod`), and coverage of every
    integer (`IsCoveringSystem.covers`, a quantifier over `ℤ`, not over
    a finite window).  Restricting residues to `ℕ` costs nothing:
    `oddCoveringExists_of_int_residues` in §4 derives this statement
    from the version with arbitrary integer residues.

    **Status and what a discharge would need.**  Neither side is in
    formalization reach.  The existence side would be settled by an
    explicit certificate, which `isOddCoveringSystem_iff` would then
    verify by `decide`; §5 proves any such certificate has lcm at least
    945.  The non-existence side would require the distortion-sieve
    machinery of [BBMST22], which proves only the squarefree case; see
    §6 and the header's record of two rejected 2026 attempts. -/
theorem erdos_7 : OddCoveringExists := by
  -- intended sorry: open question (Erdős #7; ROUTE: none known — see
  -- the docstring and §6).
  sorry

end Erdos.Covering
