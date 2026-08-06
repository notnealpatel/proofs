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
  `admit`, no custom axioms.  See the `#print axioms` block in §8.
-/

import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 THE PREDICATE AND THE ARCHIVED QUESTION
-- ════════════════════════════════════════════════════════════════════

/-- `IsOddCoveringSystem S`: the finite set `S` of (residue, modulus)
    pairs is a covering system in the classical distinct sense — moduli
    pairwise distinct and all greater than `1`, classes covering all of
    `ℤ` — and in addition every modulus is odd.  Together with
    `IsCoveringSystem.one_lt_mod` the oddness clause says every modulus
    is at least `3`. -/
structure IsOddCoveringSystem (S : Finset (ℕ × ℕ)) : Prop where
  /-- The underlying distinct covering system (`Erdos.Covering.Basic`). -/
  isCoveringSystem : IsCoveringSystem S
  /-- Every modulus is odd. -/
  odd_mod : ∀ p ∈ S, Odd p.2

/-- Odd moduli of a covering system are at least `3`: they exceed `1`
    by `IsCoveringSystem.one_lt_mod` and are not `2`. -/
theorem IsOddCoveringSystem.three_le_mod {S : Finset (ℕ × ℕ)}
    (h : IsOddCoveringSystem S) {p : ℕ × ℕ} (hp : p ∈ S) : 3 ≤ p.2 := by
  have hone : 1 < p.2 := h.isCoveringSystem.one_lt_mod p hp
  have hodd : ¬ (2 ∣ p.2) := (h.odd_mod p hp).not_two_dvd_nat
  omega

/-- **The question of Erdős #7**, as a `Prop`: is there a distinct
    covering system all of whose moduli are odd?  The negation
    `¬ OddCoveringExists` is the Selfridge side.  Neither is proved; see
    `erdos_7` in §3 for the archived form and the direction disclosure. -/
def OddCoveringExists : Prop := ∃ S : Finset (ℕ × ℕ), IsOddCoveringSystem S

-- ════════════════════════════════════════════════════════════════════
-- §2 THE DECIDABLE CHARACTERIZATION
-- ════════════════════════════════════════════════════════════════════

/-- **Decidable characterization of `IsOddCoveringSystem`.**  For any
    positive common multiple `L` of the moduli, the four defining
    clauses — moduli exceed `1`, moduli pairwise distinct, moduli odd,
    classes cover `0, …, L - 1` — are bounded quantifications over `S`
    and `Finset.range L`, hence checkable by kernel `decide`.  This is
    the restatement that the ideal-theoretic upstream form does not
    admit; see the header. -/
theorem isOddCoveringSystem_iff {S : Finset (ℕ × ℕ)} (L : ℕ) (hL : 0 < L)
    (hdvd : ∀ p ∈ S, p.2 ∣ L) :
    IsOddCoveringSystem S ↔
      (∀ p ∈ S, 1 < p.2) ∧ (∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q) ∧
        (∀ p ∈ S, Odd p.2) ∧
        (∀ r ∈ Finset.range L, ∃ p ∈ S, r % p.2 = p.1 % p.2) := by
  constructor
  · rintro ⟨hcs, hodd⟩
    obtain ⟨h1, h2, h3⟩ := (isCoveringSystem_iff L hL hdvd).mp hcs
    exact ⟨h1, h2, hodd, h3⟩
  · rintro ⟨h1, h2, hodd, h3⟩
    exact ⟨(isCoveringSystem_iff L hL hdvd).mpr ⟨h1, h2, h3⟩, hodd⟩

/-- A three-class family with distinct odd moduli `{3, 5, 7}`, all
    greater than `1`: it satisfies every clause of
    `isOddCoveringSystem_iff` except coverage.  Used below as the
    negative control that isolates coverage as the load-bearing
    clause. -/
def oddCandidate : Finset (ℕ × ℕ) := {(0, 3), (1, 5), (2, 7)}

-- Ground checks for `oddCandidate`: three classes, the expected moduli.
example : oddCandidate.card = 3 := by decide
example : oddCandidate.image Prod.snd = {3, 5, 7} := by decide
example : oddCandidate.lcm Prod.snd = 105 := by decide

/-- `oddCandidate` is not an odd covering system: the residue `104`
    below `L = 105` lies in none of its three classes.  Refuted by
    kernel `decide` through `isOddCoveringSystem_iff`, which is exactly
    how a claimed answer to Selfridge's $2000 question would be
    checked. -/
theorem not_isOddCoveringSystem_oddCandidate :
    ¬ IsOddCoveringSystem oddCandidate := fun h =>
  absurd ((isOddCoveringSystem_iff 105 (by decide) (by decide)).mp h) (by decide)

/-- The classical Erdős covering system fails only the oddness clause:
    it is a covering system (`Erdos.Covering.isCoveringSystem_erdosSystem`)
    but its modulus `2` is even. -/
theorem not_isOddCoveringSystem_erdosSystem :
    IsCoveringSystem erdosSystem ∧ ¬ IsOddCoveringSystem erdosSystem :=
  ⟨isCoveringSystem_erdosSystem, fun h =>
    absurd (h.odd_mod (0, 2) (by decide)) (by decide)⟩

-- ════════════════════════════════════════════════════════════════════
-- §3 THE ARCHIVED QUESTION (OPEN, the file's single intended `sorry`)
-- ════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════
-- §4 ℤ-RESIDUES NORMALIZE TO ℕ-RESIDUES
-- ════════════════════════════════════════════════════════════════════

/-- `natResidue (a, m)` replaces the integer residue `a` by its least
    non-negative representative `a % m`, leaving the modulus alone.
    This is the normalization that lets `Erdos.Covering.Basic` encode
    residues as naturals with no loss of generality. -/
def natResidue (q : ℤ × ℕ) : ℕ × ℕ := ((q.1 % (q.2 : ℤ)).toNat, q.2)

-- Ground checks: negative residues are moved into `[0, m)`, residues
-- already in range are untouched, and the modulus never changes.
example : natResidue (-1, 6) = (5, 6) := by decide
example : natResidue (-5, 12) = (7, 12) := by decide
example : natResidue (7, 12) = (7, 12) := by decide
example : (natResidue (-5, 12)).2 = 12 := by decide

/-- The modulus component is untouched by `natResidue`. -/
theorem natResidue_snd (q : ℤ × ℕ) : (natResidue q).2 = q.2 := rfl

/-- Shifting each residue of a covering system down by its modulus
    produces an integer-residue system with the same coverage.  Used to
    exhibit a concrete model of the hypotheses of
    `isCoveringSystem_image_natResidue` in §7. -/
theorem covers_image_sub_mod {S : Finset (ℕ × ℕ)} (h : IsCoveringSystem S)
    (n : ℤ) :
    ∃ q ∈ S.image (fun p : ℕ × ℕ => ((p.1 : ℤ) - (p.2 : ℤ), p.2)),
      n ≡ q.1 [ZMOD (q.2 : ℤ)] := by
  obtain ⟨p, hpS, hcong⟩ := h.covers n
  refine ⟨_, Finset.mem_image_of_mem _ hpS, ?_⟩
  exact hcong.trans (Int.sub_emod_right (p.1 : ℤ) (p.2 : ℤ)).symm

/-- **The ℕ-encoding is no restriction.**  From a finite family of
    integer residue classes with distinct moduli, all greater than `1`,
    covering `ℤ`, the pointwise normalization `natResidue` produces a
    covering system in the sense of `Erdos.Covering.Basic` with exactly
    the same set of moduli. -/
theorem isCoveringSystem_image_natResidue (T : Finset (ℤ × ℕ))
    (hone : ∀ q ∈ T, 1 < q.2)
    (hinj : Set.InjOn Prod.snd (T : Set (ℤ × ℕ)))
    (hcov : ∀ n : ℤ, ∃ q ∈ T, n ≡ q.1 [ZMOD (q.2 : ℤ)]) :
    IsCoveringSystem (T.image natResidue) ∧
      (T.image natResidue).image Prod.snd = T.image Prod.snd := by
  have himg : (T.image natResidue).image Prod.snd = T.image Prod.snd := by
    rw [Finset.image_image]
    rfl
  refine ⟨⟨?_, ?_, ?_⟩, himg⟩
  · -- every modulus exceeds `1`
    rintro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hone q hq
  · -- the moduli stay pairwise distinct
    rintro p hp p' hp' hpp'
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp hp'
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hp'
    have hqq' : q = q' := hinj (Finset.mem_coe.mpr hq) (Finset.mem_coe.mpr hq') hpp'
    rw [hqq']
  · -- coverage transfers, because `a % m ≡ a (mod m)`
    intro n
    obtain ⟨q, hq, hcong⟩ := hcov n
    refine ⟨natResidue q, Finset.mem_image_of_mem natResidue hq, ?_⟩
    have hm0 : ((q.2 : ℤ)) ≠ 0 := by
      have hone' : 1 < q.2 := hone q hq
      positivity
    have hnn : 0 ≤ q.1 % (q.2 : ℤ) := Int.emod_nonneg q.1 hm0
    show n ≡ (((q.1 % (q.2 : ℤ)).toNat : ℕ) : ℤ) [ZMOD ((q.2 : ℕ) : ℤ)]
    rw [Int.toNat_of_nonneg hnn]
    exact hcong.trans (Int.emod_emod_of_dvd q.1 dvd_rfl).symm

/-- **Erdős #7 is not weakened by the ℕ-residue encoding.**  If a
    distinct covering system with odd moduli exists with *arbitrary
    integer* residues, then `OddCoveringExists` holds.

    Vacuity note: the hypotheses of this implication are satisfiable
    exactly when the answer to Erdős #7 is yes, so no concrete joint
    instantiation can be given.  The satisfiable model lives one level
    down, at `isCoveringSystem_image_natResidue`, which is instantiated
    in §7 at `intSystem`. -/
theorem oddCoveringExists_of_int_residues (T : Finset (ℤ × ℕ))
    (hone : ∀ q ∈ T, 1 < q.2) (hodd : ∀ q ∈ T, Odd q.2)
    (hinj : Set.InjOn Prod.snd (T : Set (ℤ × ℕ)))
    (hcov : ∀ n : ℤ, ∃ q ∈ T, n ≡ q.1 [ZMOD (q.2 : ℤ)]) :
    OddCoveringExists := by
  obtain ⟨hcs, -⟩ := isCoveringSystem_image_natResidue T hone hinj hcov
  refine ⟨T.image natResidue, hcs, ?_⟩
  rintro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  rw [natResidue_snd]
  exact hodd q hq

-- ════════════════════════════════════════════════════════════════════
-- §5 THE DENSITY OBSTRUCTION: σ(L) ≥ 2L, AND L ≥ 945 WHEN L IS ODD
-- ════════════════════════════════════════════════════════════════════

/-- The residues below `L` in a fixed class mod `m` number at most
    `L / m`, whenever `m ∣ L`: the map `r ↦ r / m` is injective on the
    class (the remainder is pinned) and lands in `Finset.range (L / m)`. -/
theorem card_filter_range_mod_le (L m c : ℕ) (hdvd : m ∣ L) :
    ((Finset.range L).filter (fun r => r % m = c)).card ≤ L / m := by
  rw [← Finset.card_range (L / m)]
  refine Finset.card_le_card_of_injOn (fun r => r / m) ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hr
    exact Finset.mem_range.mpr (Nat.div_lt_div_of_lt_of_dvd hdvd hr.1)
  · intro r hr s hs hrs
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hr hs
    simp only at hrs
    have hkey : m * (r / m) + r % m = m * (s / m) + s % m := by
      rw [hrs, hr.2, hs.2]
    rwa [Nat.div_add_mod, Nat.div_add_mod] at hkey

/-- **The folklore density obstruction** (Zeraoulia Rafik's comment,
    quoted verbatim in the header).  If `S` is a distinct covering
    system and `L` is the lcm of its moduli, then `σ(L) ≥ 2L`, i.e. `L`
    is abundant or perfect.

    The proof is the counting argument: the class `a (mod m)` meets
    `{0, …, L-1}` in at most `L / m` residues, the classes cover all
    `L` of them, the moduli are distinct divisors of `L` exceeding `1`,
    and `∑_{d ∣ L} L / d = ∑_{d ∣ L} d = σ(L)`.  Splitting off the
    divisor `1` turns `L ≤ ∑_i L / m_i` into `L ≤ σ(L) - L`.

    This holds for arbitrary covering systems, odd or not; the witness
    `erdosSystem` (lcm 12, σ(12) = 28 ≥ 24) is in §7. -/
theorem two_mul_lcm_le_sum_divisors {S : Finset (ℕ × ℕ)} (h : IsCoveringSystem S) :
    2 * S.lcm Prod.snd ≤ ∑ d ∈ (S.lcm Prod.snd).divisors, d := by
  set L := S.lcm Prod.snd with hLdef
  have hdvd : ∀ p ∈ S, p.2 ∣ L := fun p hp => Finset.dvd_lcm hp
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · obtain ⟨p, hp, hp0⟩ := Finset.lcm_eq_zero_iff.mp h0
      have hone : 1 < p.2 := h.one_lt_mod p hp
      omega
    · exact hpos
  have hcov := (covers_iff_forall_range L hLpos hdvd).mp h.covers
  have hsub : Finset.range L ⊆
      S.biUnion (fun p => (Finset.range L).filter (fun r => r % p.2 = p.1 % p.2)) := by
    intro r hr
    obtain ⟨p, hpS, hpr⟩ := hcov r hr
    exact Finset.mem_biUnion.mpr ⟨p, hpS, Finset.mem_filter.mpr ⟨hr, hpr⟩⟩
  have hcard : L ≤ ∑ p ∈ S, L / p.2 := by
    calc L = (Finset.range L).card := (Finset.card_range L).symm
      _ ≤ (S.biUnion
            (fun p => (Finset.range L).filter (fun r => r % p.2 = p.1 % p.2))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ S, ((Finset.range L).filter (fun r => r % p.2 = p.1 % p.2)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ S, L / p.2 :=
          Finset.sum_le_sum fun p hp => card_filter_range_mod_le L p.2 _ (hdvd p hp)
  have himg : ∑ d ∈ S.image Prod.snd, L / d = ∑ p ∈ S, L / p.2 :=
    Finset.sum_image h.injOn_mod
  have hsubdiv : S.image Prod.snd ⊆ (L.divisors).erase 1 := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_erase.mpr
      ⟨(h.one_lt_mod p hp).ne', Nat.mem_divisors.mpr ⟨hdvd p hp, hLpos.ne'⟩⟩
  have hstep : ∑ d ∈ S.image Prod.snd, L / d ≤ ∑ d ∈ (L.divisors).erase 1, L / d :=
    Finset.sum_le_sum_of_subset hsubdiv
  have hsplit : L / 1 + ∑ d ∈ (L.divisors).erase 1, L / d = ∑ d ∈ L.divisors, L / d :=
    Finset.add_sum_erase _ _ (Nat.one_mem_divisors.mpr hLpos.ne')
  have hsigma : ∑ d ∈ L.divisors, L / d = ∑ d ∈ L.divisors, d :=
    Nat.sum_div_divisors L (fun x => x)
  omega

/-- The lcm of a family of odd moduli is odd: it divides their product,
    which is odd. -/
theorem odd_lcm_of_odd_mod {S : Finset (ℕ × ℕ)} (hodd : ∀ p ∈ S, Odd p.2) :
    Odd (S.lcm Prod.snd) :=
  (Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one hodd).of_dvd_nat
    (Finset.lcm_dvd fun _ hp => Finset.dvd_prod_of_mem _ hp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Kernel certificate for "945 is the smallest odd abundant number":
    for every `k < 472` the odd number `2k + 1 ≤ 943` satisfies
    `σ(2k+1) < 2(2k+1)`.  The divisor sum is expanded over
    `Finset.range` rather than over `Nat.divisors` because the kernel
    evaluates that form faster (measured on this toolchain: whole-module
    builds of 49 s with `Nat.divisors` against 42 s here);
    `no_odd_abundant_lt_945` reconciles the two through
    `Nat.filter_dvd_eq_divisors`.  This single `decide` dominates the
    module's ~42 s build, elaboration plus kernel recheck, and is why
    the `maxHeartbeats` and `maxRecDepth` bumps are here. -/
theorem no_odd_abundant_range :
    ∀ k ∈ Finset.range 472,
      ¬ (2 * (2 * k + 1) ≤
          ∑ d ∈ Finset.range (2 * k + 2), if d ∣ (2 * k + 1) then d else 0) := by
  decide

/-- **No odd number below 945 is abundant or perfect.**  (945 = 3³·5·7
    is abundant: σ(945) = 1920 > 1890; see §7.) -/
theorem no_odd_abundant_lt_945 {n : ℕ} (hodd : Odd n) (hlt : n < 945) :
    ∑ d ∈ n.divisors, d < 2 * n := by
  obtain ⟨k, hk⟩ := hodd
  have hbridge : ∑ d ∈ n.divisors, d
      = ∑ d ∈ Finset.range (2 * k + 2), if d ∣ (2 * k + 1) then d else 0 := by
    rw [hk, ← Nat.filter_dvd_eq_divisors (by omega), Finset.sum_filter]
  have hrange := no_odd_abundant_range k (Finset.mem_range.mpr (by omega))
  omega

/-- **945 is a lower bound for odd abundant numbers.**  If `n` is odd
    and `σ(n) ≥ 2n` then `945 ≤ n`. -/
theorem le_of_odd_of_two_mul_le_sum_divisors {n : ℕ} (hodd : Odd n)
    (habund : 2 * n ≤ ∑ d ∈ n.divisors, d) : 945 ≤ n := by
  by_contra hlt
  have := no_odd_abundant_lt_945 hodd (by omega)
  omega

/-- **Any odd covering system has lcm at least 945.**  Composite of
    `two_mul_lcm_le_sum_divisors` (the lcm is abundant or perfect),
    `odd_lcm_of_odd_mod` (the lcm is odd), and
    `le_of_odd_of_two_mul_le_sum_divisors` (945 is the least odd
    abundant number).  This is the formal form of the Zeraoulia comment
    quoted in the header, and it is the concrete obstruction any
    claimed answer to Selfridge's $2000 question must clear.

    Vacuity note: the hypothesis is the open existence question, so
    this statement is vacuously true if the answer to Erdős #7 is "no".
    Its three components are separately non-vacuous; see §7. -/
theorem nine_hundred_forty_five_le_lcm {S : Finset (ℕ × ℕ)}
    (h : IsOddCoveringSystem S) : 945 ≤ S.lcm Prod.snd :=
  le_of_odd_of_two_mul_le_sum_divisors (odd_lcm_of_odd_mod h.odd_mod)
    (two_mul_lcm_le_sum_divisors h.isCoveringSystem)

-- ════════════════════════════════════════════════════════════════════
-- §6 THE PUBLISHED BOUNDARY, AS STATEMENTS
-- ════════════════════════════════════════════════════════════════════

/-! The results below are theorems of the literature.  They are
recorded here as `Prop`-valued definitions and never as `sorry`-carrying
theorems: a `sorry`'d theorem is indistinguishable in an axiom sweep
from an open conjecture, and — per Thomas Bloom's 07 May 2026 ruling
quoted in the header — nothing in this file should be mistakable for a
formalization of [BBMST22] or [HoNi19].  Each is used only as an
explicit hypothesis. -/

/-- **[BBMST22], the squarefree case.**  Balister, Bollobás, Morris,
    Sahasrabudhe and Tiba proved that there is no covering system all of
    whose moduli are odd *and squarefree* — the stronger question Erdős
    and Selfridge also asked.  Statement only; not proved here. -/
def BBMSTNoOddSquarefreeCovering : Prop :=
  ∀ S : Finset (ℕ × ℕ), IsOddCoveringSystem S → ¬ ∀ p ∈ S, Squarefree p.2

/-- **[HoNi19].**  Hough and Nielsen proved that in any covering system
    at least one modulus is divisible by `2` or by `3`; [BBMST22] gives
    a simpler proof.  Statement only; not proved here. -/
def HoughNielsenTwoOrThreeDvd : Prop :=
  ∀ S : Finset (ℕ × ℕ), IsCoveringSystem S → ∃ p ∈ S, 2 ∣ p.2 ∨ 3 ∣ p.2

/-- **[BBMST22], the lcm condition.**  If an odd covering system exists
    then the lcm of its moduli is divisible by `9` or by `15`.
    Statement only; not proved here. -/
def BBMSTLcmNineOrFifteen : Prop :=
  ∀ S : Finset (ℕ × ℕ), IsOddCoveringSystem S →
    9 ∣ S.lcm Prod.snd ∨ 15 ∣ S.lcm Prod.snd

/-- **Selfridge's reduction**, as reported in [Sc67]: an odd covering
    system exists if a covering system exists whose moduli form an
    antichain under divisibility.  The database records that the
    antichain hypothesis is itself unsatisfiable (Erdős problem #586),
    so this implication is not a route to the existence side; it is
    archived because the primary source states it.  Statement only; not
    proved here. -/
def SelfridgeAntichainReduction : Prop :=
  (∃ S : Finset (ℕ × ℕ), IsCoveringSystem S ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ¬ (p.2 ∣ q.2)) → OddCoveringExists

/-- Consequence of [HoNi19]: in an odd covering system some modulus is
    divisible by `3`, since no odd modulus is divisible by `2`.

    Vacuity note: vacuously true if the answer to Erdős #7 is "no". -/
theorem exists_three_dvd_of_houghNielsen (hHN : HoughNielsenTwoOrThreeDvd)
    {S : Finset (ℕ × ℕ)} (h : IsOddCoveringSystem S) : ∃ p ∈ S, 3 ∣ p.2 := by
  obtain ⟨p, hp, h2 | h3⟩ := hHN S h.isCoveringSystem
  · exact absurd h2 (h.odd_mod p hp).not_two_dvd_nat
  · exact ⟨p, hp, h3⟩

/-- Consequence of [BBMST22]: an odd covering system must use a modulus
    that is not squarefree.

    Vacuity note: vacuously true if the answer to Erdős #7 is "no". -/
theorem exists_not_squarefree_of_bbmst (hBB : BBMSTNoOddSquarefreeCovering)
    {S : Finset (ℕ × ℕ)} (h : IsOddCoveringSystem S) :
    ∃ p ∈ S, ¬ Squarefree p.2 := by
  by_contra hcon
  push Not at hcon
  exact hBB S h hcon

/-- Consequence of [BBMST22]: either way, `3` divides the lcm of an odd
    covering system — and by `nine_hundred_forty_five_le_lcm` that lcm
    is at least 945.

    Vacuity note: vacuously true if the answer to Erdős #7 is "no". -/
theorem three_dvd_lcm_of_bbmstLcm (hBB : BBMSTLcmNineOrFifteen)
    {S : Finset (ℕ × ℕ)} (h : IsOddCoveringSystem S) :
    3 ∣ S.lcm Prod.snd ∧ 945 ≤ S.lcm Prod.snd := by
  refine ⟨?_, nine_hundred_forty_five_le_lcm h⟩
  rcases hBB S h with h9 | h15
  · exact dvd_trans (by norm_num) h9
  · exact dvd_trans (by norm_num) h15

-- ════════════════════════════════════════════════════════════════════
-- §7 GROUND TRUTH AND SATISFIABILITY
-- ════════════════════════════════════════════════════════════════════

section GroundTruth

-- ── §2: the decidable characterization is genuinely used ────────────

-- `oddCandidate` satisfies three of the four clauses of
-- `isOddCoveringSystem_iff`: moduli exceed 1, are pairwise distinct,
-- and are odd.  Only coverage fails, and it fails concretely.
example : (∀ p ∈ oddCandidate, 1 < p.2) ∧
    (∀ p ∈ oddCandidate, ∀ q ∈ oddCandidate, p.2 = q.2 → p = q) ∧
    (∀ p ∈ oddCandidate, Odd p.2) := by decide

example : ¬ ∀ r ∈ Finset.range 105, ∃ p ∈ oddCandidate, r % p.2 = p.1 % p.2 := by
  decide

-- The residue `104` is the concrete gap.
example : ¬ ∃ p ∈ oddCandidate, 104 % p.2 = p.1 % p.2 := by decide

-- `erdosSystem` satisfies coverage and distinctness but not oddness.
example : ¬ ∀ p ∈ erdosSystem, Odd p.2 := by decide

-- ── §4: the hypotheses of `isCoveringSystem_image_natResidue` at a
--        concrete model with genuinely negative residues ────────────

/-- The classical Erdős system rewritten with negative residues:
    `{-2 (mod 2), -3 (mod 3), -3 (mod 4), -1 (mod 6), -5 (mod 12)}`.
    It is `erdosSystem` shifted down by the moduli, so
    `covers_image_sub_mod` gives its coverage, and `natResidue` maps it
    back onto `erdosSystem`. -/
def intSystem : Finset (ℤ × ℕ) := {(-2, 2), (-3, 3), (-3, 4), (-1, 6), (-5, 12)}

example : intSystem = erdosSystem.image (fun p : ℕ × ℕ =>
    ((p.1 : ℤ) - (p.2 : ℤ), p.2)) := by decide

example : intSystem.image natResidue = erdosSystem := by decide

example : ∀ q ∈ intSystem, 1 < q.2 := by decide

example : Set.InjOn Prod.snd (intSystem : Set (ℤ × ℕ)) := by
  intro q hq q' hq' hqq'
  simp only [Finset.mem_coe] at hq hq'
  fin_cases hq <;> fin_cases hq' <;> simp_all

-- The joint instantiation: every hypothesis of
-- `isCoveringSystem_image_natResidue` holds at `intSystem`, and the
-- conclusion returns `erdosSystem`.
example : IsCoveringSystem erdosSystem := by
  have hcov : ∀ n : ℤ, ∃ q ∈ intSystem, n ≡ q.1 [ZMOD (q.2 : ℤ)] := by
    intro n
    have h := covers_image_sub_mod isCoveringSystem_erdosSystem n
    rwa [show erdosSystem.image (fun p : ℕ × ℕ => ((p.1 : ℤ) - (p.2 : ℤ), p.2))
      = intSystem from by decide] at h
  have hinj : Set.InjOn Prod.snd (intSystem : Set (ℤ × ℕ)) := by
    intro q hq q' hq' hqq'
    simp only [Finset.mem_coe] at hq hq'
    fin_cases hq <;> fin_cases hq' <;> simp_all
  obtain ⟨hcs, -⟩ :=
    isCoveringSystem_image_natResidue intSystem (by decide) hinj hcov
  rwa [show intSystem.image natResidue = erdosSystem from by decide] at hcs

-- ── §5: each component of the 945 bound at a non-vacuous witness ────

-- The counting lemma is sharp at `L = 12`, `m = 4`: the class
-- `1 (mod 4)` meets `{0, …, 11}` in exactly `12 / 4 = 3` residues.
example : ((Finset.range 12).filter (fun r => r % 4 = 1)).card = 3 := by decide

example : ((Finset.range 12).filter (fun r => r % 4 = 1)).card ≤ 12 / 4 :=
  card_filter_range_mod_le 12 4 1 (by decide)

-- `two_mul_lcm_le_sum_divisors` at `erdosSystem`: lcm 12, σ(12) = 28.
example : erdosSystem.lcm Prod.snd = 12 := by decide

example : ∑ d ∈ (12 : ℕ).divisors, d = 28 := by decide

example : 2 * erdosSystem.lcm Prod.snd ≤ ∑ d ∈ (erdosSystem.lcm Prod.snd).divisors, d :=
  two_mul_lcm_le_sum_divisors isCoveringSystem_erdosSystem

-- `odd_lcm_of_odd_mod` at `oddCandidate`: lcm 105, odd.
example : Odd (oddCandidate.lcm Prod.snd) := odd_lcm_of_odd_mod (by decide)

example : oddCandidate.lcm Prod.snd = 105 := by decide

-- 945 = 3³·5·7 really is abundant, so the bound is attained and
-- `le_of_odd_of_two_mul_le_sum_divisors` is not vacuous.
set_option maxRecDepth 10000 in
example : ∑ d ∈ (945 : ℕ).divisors, d = 1920 := by decide

example : Odd (945 : ℕ) := by decide

set_option maxRecDepth 10000 in
example : 945 ≤ 945 :=
  le_of_odd_of_two_mul_le_sum_divisors (n := 945) (by decide) (by decide)

-- …and the bound really bites below 945: `σ(315) = 624 < 630`.
example : ∑ d ∈ (315 : ℕ).divisors, d < 2 * 315 :=
  no_odd_abundant_lt_945 (by decide) (by decide)

-- The oddness hypothesis is load-bearing: `12` is even, abundant, and
-- far below 945.
example : 2 * 12 ≤ ∑ d ∈ (12 : ℕ).divisors, d := by decide

example : ¬ Odd (12 : ℕ) := by decide

-- ── §6: the conclusions of the archived literature statements are
--        satisfiable, at `erdosSystem` ──────────────────────────────

-- Hough–Nielsen's conclusion at the classical system: modulus 2.
example : ∃ p ∈ erdosSystem, 2 ∣ p.2 ∨ 3 ∣ p.2 :=
  ⟨(0, 2), by decide, Or.inl (by decide)⟩

-- `erdosSystem` has a non-squarefree modulus (4 and 12), so
-- [BBMST22]'s squarefree hypothesis is a real restriction.
example : ¬ Squarefree (4 : ℕ) := by decide

example : ∃ p ∈ erdosSystem, ¬ Squarefree p.2 := ⟨(1, 4), by decide, by decide⟩

-- The `9 ∣ L ∨ 15 ∣ L` conclusion is not satisfied by the classical
-- (even) system: its lcm is 12.
example : ¬ (9 ∣ erdosSystem.lcm Prod.snd ∨ 15 ∣ erdosSystem.lcm Prod.snd) := by
  decide

-- The smallest odd `L` divisible by 9 or 15 and at least 945 is
-- consistent with 945 itself: 9 ∣ 945.
example : 9 ∣ (945 : ℕ) := by decide

-- ── The archived statement is not degenerate ────────────────────────

-- `IsOddCoveringSystem` is not satisfied by the empty family: the
-- empty union covers nothing.
example : ¬ IsOddCoveringSystem (∅ : Finset (ℕ × ℕ)) := fun h => by
  obtain ⟨p, hp, -⟩ := h.isCoveringSystem.covers 0
  exact absurd hp (Finset.notMem_empty p)

-- Dropping the oddness clause makes the existence statement TRUE, so
-- oddness is exactly what is open.
example : ∃ S : Finset (ℕ × ℕ), IsCoveringSystem S :=
  ⟨erdosSystem, isCoveringSystem_erdosSystem⟩

-- Dropping coverage instead also makes it true — `oddCandidate` has
-- distinct odd moduli greater than 1.
example : ∃ S : Finset (ℕ × ℕ), (∀ p ∈ S, 1 < p.2) ∧
    Set.InjOn Prod.snd (S : Set (ℕ × ℕ)) ∧ (∀ p ∈ S, Odd p.2) := by
  refine ⟨oddCandidate, by decide, ?_, by decide⟩
  intro p hp q hq hpq
  simp only [Finset.mem_coe] at hp hq
  fin_cases hp <;> fin_cases hq <;> simp_all

end GroundTruth

-- ════════════════════════════════════════════════════════════════════
-- §8 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

/-! `erdos_7` carries the file's single intended `sorry` and reports
`sorryAx` by construction — it is listed first and is the *only*
declaration allowed to.  Every other declaration must report a subset of
{propext, Classical.choice, Quot.sound}.  That subset check is also the
sound `native_decide` detector on this toolchain: a use would surface as
a per-declaration `*._native.native_decide.ax_*` axiom.  This file
contains no `native_decide`. -/

#print axioms erdos_7

#print axioms IsOddCoveringSystem
#print axioms IsOddCoveringSystem.three_le_mod
#print axioms OddCoveringExists
#print axioms isOddCoveringSystem_iff
#print axioms oddCandidate
#print axioms not_isOddCoveringSystem_oddCandidate
#print axioms not_isOddCoveringSystem_erdosSystem
#print axioms natResidue
#print axioms natResidue_snd
#print axioms covers_image_sub_mod
#print axioms isCoveringSystem_image_natResidue
#print axioms oddCoveringExists_of_int_residues
#print axioms card_filter_range_mod_le
#print axioms two_mul_lcm_le_sum_divisors
#print axioms odd_lcm_of_odd_mod
#print axioms no_odd_abundant_range
#print axioms no_odd_abundant_lt_945
#print axioms le_of_odd_of_two_mul_le_sum_divisors
#print axioms nine_hundred_forty_five_le_lcm
#print axioms BBMSTNoOddSquarefreeCovering
#print axioms HoughNielsenTwoOrThreeDvd
#print axioms BBMSTLcmNineOrFifteen
#print axioms SelfridgeAntichainReduction
#print axioms exists_three_dvd_of_houghNielsen
#print axioms exists_not_squarefree_of_bbmst
#print axioms three_dvd_lcm_of_bbmstLcm
#print axioms intSystem

end Erdos.Covering
