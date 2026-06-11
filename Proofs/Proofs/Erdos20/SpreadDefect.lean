/-
  Erdős Problem #20 — Track B (spread vs compression), B2 goals
  G1/G2/G3: anti-spread families are small, the regularization loop in
  its honest form, and the REFUTATION of the spread-defect bridge
  (B1's Hypothesis H) at every spread level r* ≥ 4.

  Builds on Spread.lean (read-only API: `IsRSpread`, `linkAt`,
  `exists_isRSpread_linkAt`, `linkAt_uniform`, `HasSunflower.of_linkAt`)
  and, for §4, on the compressed-endpoint pipeline of
  ShiftedSunflower.lean (`IsFullShiftOf.hasSunflower`,
  `exists_isFullShiftOf`). Everything here is combinatorial, over ℚ,
  and axiom-clean ([propext, Classical.choice, Quot.sound] — no
  native_decide).

  WHAT IS PROVED

  · G1 — anti-spread families are small
    (`card_le_pow_of_forall_linkAt_not_isRSpread`; Kupavskii,
    "Delta-system method: a survey", arXiv:2508.20132, Observation 6):
    if F is k-uniform and no nonempty link of F at any Z with |Z| < k
    (including Z = ∅, whose link is F itself: `linkAt_empty`) is
    r-spread, then |F| ≤ r^k. This is the size engine of peeling: a
    family with no spread restriction is exponentially small. Proof:
    the maximizer witness of `exists_isRSpread_linkAt` has an r-spread
    link AND the size clause |F| ≤ |F_Z|·r^|Z|; the hypothesis forces
    the witness to width |Z| = k, where the link is at most {∅}.

    Hypothesis design — both qualifiers are load-bearing (ground
    certificates: Scratch/SpreadDefectSanity.lean):
    (i) |Z| < k: at any member Z ∈ F the link is {∅}, which is
        VACUOUSLY r-spread under `IsRSpread` for every r (every
        nonempty probe filters to the empty family), so quantifying
        over all Z would make the hypothesis unsatisfiable for
        nonempty F and the theorem vacuous.
    (ii) the nonempty-link guard: the EMPTY family is also vacuously
        r-spread under `IsRSpread`, so an unguarded hypothesis would
        be false for any family leaving some probe Z with |Z| < k
        uncovered (e.g. F = {{0,1}} on Fin 3 at Z = {2}) and would
        silently restrict the theorem to covering designs. The guard
        matches ALWZ Definition 1.10 (arXiv:1908.08483), where
        spreadness carries the size clause |F| ≥ κ^w and empty (and
        too-small) families never count as spread.
    Satisfiability witness (proved below, `not_isRSpread_singleton` +
    `forall_linkAt_not_isRSpread_pair`): F = {{0,1}} on Fin 3 with
    r = 2 — the nonempty links at Z = ∅, {0}, {1} are {{0,1}}, {{1}},
    {{0}}, each a singleton family with a full member-probe, never
    2-spread; the concluding example checks |F| = 1 ≤ 2² = r^k.

  · G2, loop (`exists_isRSpread_linkAt_loop`) — the regularization
    step of ALWZ (arXiv:1908.08483, Lemma 2.4: maximal popular witness
    K, pass to the link F_K, recurse) and Rao (arXiv:1909.04774,
    Theorem 1 from Lemma 2: "if the sets are not r-spread, then there
    is a nonempty set Z such that more than r^{k-|Z|} of the sets
    contain Z. By induction […]"), in the honest terminating form:
    every k-uniform F with |F| > r^k yields a witness Z with
      · |Z| < k                      (the loop terminates strictly
                                      before width 0),
      · IsRSpread r (linkAt Z F)     (the link is regularized),
      · (k − |Z|)-uniformity of the link,
      · (linkAt Z F).Nonempty        (the regime is inhabited),
      · |F| ≤ |linkAt Z F| · r^|Z|   (the SIZE CLAUSE: the link pays
                                      for all of F at cost r^|Z|),
      · r^(k−|Z|) < |linkAt Z F|     (the link beats its own
                                      threshold, so the loop's
                                      invariant is reproduced one
                                      width down).
    Without the size clause the statement is trivially satisfiable by
    degenerate links and useless downstream; Spread.lean's
    `exists_isRSpread_linkAt_uniform` derives it internally and then
    discards it — this restatement carries it. The ALWZ/Rao width
    recursion collapses into the single q(Z) = |F_Z|·r^|Z| maximization
    (Stoeckl, proof of Lemma 5, 'Entry material'), so no induction on
    width is needed; with a fixed spread parameter r the two routes
    prove the same statement (Rao's remark "r(p,k) can only increase
    with k" is what made the recursion sound for level-dependent r).

  · G2, conditional reduction (`hasSunflower_of_forall_linkAt_isRSpread`)
    — spread lemma ⇒ sunflower bound, with the probabilistic spread
    lemma as the SINGLE explicit hypothesis, now demanded only on the
    structurally decomposed instance: the links of F at witnesses
    |Z| < k carrying all six loop clauses — not on arbitrary families
    at arbitrary levels. `hasSunflower_of_forall_isRSpread_via_loop`
    is the machine-checked subsumption certificate: Spread.lean's
    per-level universally-quantified interface factors through the
    loop form by instantiation. Instantiating either hypothesis at
    r = C·s·log k is the ALWZ/Rao/BCW/Stoeckl bound (C ≤ 64,
    arXiv:2009.09327; mstoeckl.com sunflower notes); the lemma itself
    stays unformalized, blocked on Shannon-entropy infrastructure
    absent from Mathlib (CONSUMER_STOECKL_SPREAD.md §7).

  · G3 (§4) — the spread-defect bridge is REFUTED. Hypothesis H
    (task B1: τ(S(F))/τ(F) is bounded by a function of the spread
    radius r*(F) alone) is FALSE for fully compressed shift endpoints,
    at every spread level b ≥ 4:
    - `productFamily b k` — the standard product construction (all
      transversals of k blocks of size b, run at block size b instead
      of the sunflower-free s−1): |F| = b^k (`productFamily_card`),
      k-uniform, EXACTLY b-spread — `IsRSpread b` with equality on
      every inhabited probe (`productFamily_isRSpread`) and
      ¬`IsRSpread r` for every r > b (`productFamily_not_isRSpread`) —
      and τ(F) = b for EVERY k (`productFamily_sunflowerNumber`: the
      b constant transversals up, slot-projection at a free petal
      block down). The canonical low-τ inhabitant of the high-spread
      regime, structurally invisible to B1's zoo (its random families
      at |F| ≥ 4^k all carry large τ(F)).
    - `IsFullShiftOf.hasSunflower_of_isRSpread` — the τ-transport
      FLOOR (spread families shift violently, the opposite of H):
      every fully compressed endpoint of an r-spread (r ≥ 4)
      k-uniform family contains an s-sunflower whenever
      s^(2s-2) < 2^k. Mechanism: spreadness alone forces
      |F| ≥ r^k ≥ 4^k (`IsRSpread.pow_card_le`), cardinality survives
      the chain, and the compression headline
      (`IsFullShiftOf.hasSunflower`) converts size into endpoint
      sunflowers. The floor depends only on k — never on τ(F).
    - `spread_defect_unbounded` / `spread_defect_bridge_false` — the
      refutation: for every b ≥ 4 and every candidate constant g, the
      product family at k = 2(gb+1)² is exactly b-spread with
      τ(F) = b, yet EVERY fully compressed endpoint has
      τ > g·τ(F). So no function g(r*) of the spread radius alone
      bounds the τ-inflation of the full shift (the witnesses pin
      r* = b for all k), refuting H; with τ(F) = b fixed, the floor
      makes the ratio grow at least like Ω(k / log k) along k.

    CONVENTION HONESTY (G3): the refutation speaks of `IsFullShiftOf`
    endpoints — any shift chain landing on a fully compressed family,
    the durable Lean-side notion this development uses (cf.
    `mishra_v1_lemma3_false`). B1's S(F) is ONE canonical lex sweep,
    not iterated to a fixpoint. On the witness class the two coincide
    empirically: a single sweep of `productFamily` is already fully
    compressed at every computed size (machine-checked at b=4, k=2 in
    Scratch/SpreadDefectWitness.lean — sweep endpoint compressed,
    τ: 4 → 7, ratio 1.75; Go probe: ratios 1.75/2.50/3.25 at
    b=4, k=2/3/4, i.e. τ(S(F)) = (b−1)k+1, already growing in k at
    pinned r* = 4). Whether the single non-iterated sweep admits a
    bound at small fixed k is not settled here and no longer
    load-bearing. Consistency with the committed witness: familyB
    (Counterexample.lean, τ 2→17 at r* ≈ 2.03) killed the bridge in
    the LOW-spread regime; G3 kills it in the HIGH-spread regime
    r* ≥ 4 — opposite ends of the spread axis, no contradiction.

  HONESTY CONSTRAINTS

  · The discarded complement (P8, CONSUMER_ALWZ_PHASE1.md): at the
    regularization step both primary texts DISCARD the complement
    {S ∈ F : Z ⊄ S} — it is unbounded and unanalyzed (ALWZ Lemma 2.4;
    Rao Theorem 1; only the iterative bad sets of ALWZ Lemma 2.6 are
    bounded, by the Lemma 2.8 encoding argument). Accordingly NO
    statement in this file claims any bound on that complement; the
    size clause |F| ≤ |F_Z|·r^|Z| is a statement about the retained
    link only. Bounding the discarded complement is an open route
    toward removing the log k factor.
  · The ASU barrier (master brief §5 O1; Alon–Shpilka–Umans 2013):
    nothing here is, or implies, the full Erdős–Rado conjecture; the
    spread lemma is an explicit hypothesis in every sunflower-shaped
    statement, and the unconditional statements are size/structure
    accounting only. §4 stays at the τ-transport level: its sunflowers
    live in compressed ENDPOINTS only (exactly the already-proved
    headline regime), and its headline theorems CLOSE a bridge route
    rather than open one.

  UPGRADE PATH (recorded per dispatch; Rao, arXiv:1909.04774, p. 2,
  after Lemma 2): "As far as we know, it is possible that Lemma 2
  holds even when r(p,k) = O(p). Such a strengthening of Lemma 2 would
  imply the sunflower conjecture of Erdős and Rado." In this file's
  terms: a spread lemma valid at some r = O(s), fed to
  `hasSunflower_of_forall_linkAt_isRSpread`, would give
  f(k,s) ≤ (Cs)^k. We state nothing at that strength.

  FRONTIER

  · The spread lemma itself (the only unformalized piece of the
    (C·s·log k)^k bound) needs discrete Shannon entropy
    (H(X), H(X|Y), chain rule, subadditivity), absent from Mathlib —
    out of scope this campaign.
  · The discarded complement is unanalyzed in the literature (P8);
    any bound on it would strengthen the loop beyond the primary
    texts.
  · G3 outcome: REFUTED (§4, std-3 theorem — stronger than the
    certificate route the plan anticipated; ground certificate of the
    smallest instance in Scratch/SpreadDefectWitness.lean). The
    spread-defect theorem τ(S(F)) ≤ g(r*)·τ(F) is FALSE for fully
    compressed endpoints at every spread level r* = b ≥ 4
    (`spread_defect_unbounded`), so the τ-route from the shifted
    headline back to general families is closed in BOTH spread
    regimes (low: Counterexample.lean; high: §4), and Track B's
    positive deliverable is G2's conditional reduction above. Still
    open, not settled here: (i) any τ-transport with g depending on
    k — by the floor, g(4, k) must be Ω(k/log k), and the product
    family's measured endpoints suggest (b−1)k+1, i.e. Θ(k), is the
    truth; (ii) the single non-iterated lex sweep at fixed small k;
    (iii) per the matching-transport lemma
    (`empty_kernel_sunflower_le_sunflowerNumber`, Sunflower.lean) the
    violent inflation is carried entirely by NONEMPTY kernels — the
    endpoint stars — which is exactly the exclusion theorem's
    star-vs-spread collision running forward.

  SOURCES
  · Alweiss–Lovett–Wu–Zhang, arXiv:1908.08483 (Definition 1.10,
    Lemma 2.4, Lemmas 2.6/2.8, Theorem 2.5).
  · Rao, "Coding for Sunflowers", arXiv:1909.04774 (Theorem 1,
    Lemma 2 and the O(p) remark after it).
  · Bell–Chueluecha–Warnke, arXiv:2009.09327 (r = C·p·log k).
  · Kupavskii, "Delta-system method: a survey", arXiv:2508.20132
    (Observation 6: anti-spread ⇒ small).
  · Stoeckl, "Lecture notes on recent improvements for the sunflower
    lemma", mstoeckl.com (one-shot maximizer regularization, C ≤ 64).
  · §4's `productFamily` is the standard product construction of the
    sunflower lower bound f(k, s+1) > s^k (k blocks of size s,
    transversals — cf. the block-size-2 instance behind trackA's
    f'(k,3) ≥ 2^k finding, EXECUTION.md §4), run at block size b ≥ 4,
    where τ = b and the spread radius is exactly b.
  · Task B1 (this campaign): data/erdos20/trackB/B1_REPORT.md +
    spread_defect.json — 97 families, verdict "H SUPPORTED"; §4 shows
    the support was a zoo artifact (no low-τ high-spread families were
    sampled). The B1 kill criterion "r* ≥ 4, ratio > 8, growing
    with k" is hit by productFamily 4 k under the endpoint
    convention — provably for k large (the floor), and already at
    k ≈ 11 if the measured small-k law τ(S(F)) = (b−1)k+1 (k ≤ 4)
    persists — at sizes 4^k beyond exact-τ computation, which is why
    B1's zoo could not reach it.
  · Session briefs: data/erdos20/CONSUMER_ALWZ_SPR_V_COMP.md (§5 O1,
    §6 F5), data/erdos20/trackB/CONSUMER_ALWZ_PHASE1.md (P8),
    data/erdos20/CONSUMER_STOECKL_SPREAD.md (§5),
    data/erdos20/CONSUMER_KUPAVSKII25.md (§6a) — gitignored
    references; this header is self-contained.
-/

import Proofs.Erdos20.Spread

open Finset

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════
-- §1 LINK API COMPLEMENTS
--    Small extensions of Spread.lean's linkAt toolkit used by G1/G2:
--    the empty probe, nonemptiness, and the two degenerate-link facts
--    that drive the hypothesis design.
-- ════════════════════════════════════════════════════════════════════

section LinkApi

/-- The link at the empty probe is the family itself: G1's hypothesis
    "no nonempty link at |Z| < k is r-spread" includes, at Z = ∅,
    "F is not r-spread". -/
theorem linkAt_empty (F : Finset (Finset (Fin n))) : linkAt ∅ F = F := by
  unfold linkAt
  simp

/-- The link at `Z` is inhabited exactly when `Z` is contained in a
    member. Connects the nonempty-link guard of G1 to the witness
    clause `∃ S ∈ F, Z ⊆ S` of `exists_isRSpread_linkAt`. -/
theorem linkAt_nonempty_iff {Z : Finset (Fin n)} {F : Finset (Finset (Fin n))} :
    (linkAt Z F).Nonempty ↔ ∃ S ∈ F, Z ⊆ S := by
  unfold linkAt
  rw [Finset.image_nonempty, Finset.filter_nonempty_iff]

/-- The link of a singleton family at a probe inside its member. -/
theorem linkAt_singleton_family {Z S : Finset (Fin n)} (hZS : Z ⊆ S) :
    linkAt Z ({S} : Finset (Finset (Fin n))) = {S \ Z} := by
  unfold linkAt
  rw [Finset.filter_singleton, if_pos hZS, Finset.image_singleton]

/-- A singleton family with a nonempty member is never `r`-spread for
    `r > 1`: probe at the member itself. (The nonemptiness is
    necessary: `{∅}` — the link of a `k`-uniform family at one of its
    members — is vacuously `r`-spread for every `r`, which is exactly
    why G1 quantifies over `|Z| < k` only.) -/
theorem not_isRSpread_singleton {r : ℚ} {S : Finset (Fin n)}
    (hS : S.Nonempty) (hr : 1 < r) : ¬ IsRSpread r {S} := by
  intro h
  have h1 := h S hS
  rw [Finset.filter_singleton, if_pos (Finset.Subset.refl S)] at h1
  simp only [Finset.card_singleton, Nat.cast_one, one_mul] at h1
  exact absurd h1 (not_le.mpr (one_lt_pow₀ hr (Finset.card_ne_zero.mpr hS)))

end LinkApi

-- ════════════════════════════════════════════════════════════════════
-- §2 G1 — ANTI-SPREAD FAMILIES ARE SMALL (Kupavskii Obs 6)
--    The size engine of peeling: a family with no spread restriction
--    is exponentially small. Contrapositive of the loop's existence,
--    proved directly from the same maximizer.
-- ════════════════════════════════════════════════════════════════════

section AntiSpread

/-- **Anti-spread families are small** (Kupavskii, arXiv:2508.20132,
    Observation 6). If `F` is `k`-uniform and no nonempty link of `F`
    at any `Z` with `|Z| < k` — including `Z = ∅`, whose link is `F`
    itself — is `r`-spread, then `|F| ≤ r^k`.

    Proof: the maximizer witness `Z` of `exists_isRSpread_linkAt` has
    an `r`-spread nonempty link and the size clause
    `|F| ≤ |linkAt Z F|·r^|Z|`; the hypothesis forbids `|Z| < k`, the
    uniformity caps `|Z| ≤ k`, and at `|Z| = k` the link is at most
    `{∅}`, so `|F| ≤ r^k`.

    Hypothesis design (both qualifiers load-bearing — see header and
    Scratch/SpreadDefectSanity.lean): links at members are `{∅}` and
    vacuously spread, so quantifying over `|Z| ≤ k` would be
    unsatisfiable for nonempty `F`; empty links are vacuously spread,
    so dropping the nonempty-link guard would restrict the theorem to
    families covering every small probe. Satisfiable instance:
    `F = {{0,1}}` on `Fin 3`, `r = 2` (`forall_linkAt_not_isRSpread_pair`
    below). Side condition: `0 < r` only (the maximizer machinery and
    the empty-family case need nonnegative powers). -/
theorem card_le_pow_of_forall_linkAt_not_isRSpread {r : ℚ} {k : ℕ} (hr : 0 < r)
    {F : Finset (Finset (Fin n))} (hunif : ∀ S ∈ F, S.card = k)
    (hanti : ∀ Z : Finset (Fin n), Z.card < k → (linkAt Z F).Nonempty →
      ¬ IsRSpread r (linkAt Z F)) :
    (F.card : ℚ) ≤ r ^ k := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact (pow_pos hr k).le
  obtain ⟨Z, ⟨S₀, hS₀F, hZS₀⟩, hspread, hsize⟩ :=
    exists_isRSpread_linkAt r hr F hF
  -- the uniformity caps the witness width
  have hZk : Z.card ≤ k := by
    have h := Finset.card_le_card hZS₀
    rwa [hunif S₀ hS₀F] at h
  -- the anti-spread hypothesis forces the witness to the top width
  have hZeq : Z.card = k := by
    rcases lt_or_eq_of_le hZk with hlt | heq
    · exact absurd hspread
        (hanti Z hlt (linkAt_nonempty_iff.mpr ⟨S₀, hS₀F, hZS₀⟩))
    · exact heq
  -- at width 0 the link collapses into {∅}
  have hsub : linkAt Z F ⊆ {∅} := by
    intro E hE
    have hcard0 := linkAt_uniform hunif E hE
    rw [hZeq, Nat.sub_self] at hcard0
    exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp hcard0)
  have hle1 : ((linkAt Z F).card : ℚ) ≤ 1 := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_singleton ∅).le
  calc (F.card : ℚ) ≤ ((linkAt Z F).card : ℚ) * r ^ Z.card := hsize
    _ ≤ 1 * r ^ Z.card :=
        mul_le_mul_of_nonneg_right hle1 (pow_pos hr Z.card).le
    _ = r ^ k := by rw [one_mul, hZeq]

/-- Non-vacuity witness for G1's hypothesis: `F = {{0,1}}` on `Fin 3`
    with `r = 2`. The nonempty links at `|Z| < 2` are `{{0,1}}` (at
    `∅`), `{{1}}` (at `{0}`), `{{0}}` (at `{1}`) — singleton families
    with nonempty members, never `2`-spread. The uncovered probe
    `Z = {2}` has an empty link and is exempted by the guard (it is
    vacuously spread, so the unguarded hypothesis would fail here). -/
theorem forall_linkAt_not_isRSpread_pair :
    ∀ Z : Finset (Fin 3), Z.card < 2 →
      (linkAt Z ({{0, 1}} : Finset (Finset (Fin 3)))).Nonempty →
      ¬ IsRSpread 2 (linkAt Z ({{0, 1}} : Finset (Finset (Fin 3)))) := by
  intro Z hZcard hne
  obtain ⟨T, hT, hZT⟩ := linkAt_nonempty_iff.mp hne
  rw [Finset.mem_singleton] at hT
  subst hT
  rw [linkAt_singleton_family hZT]
  refine not_isRSpread_singleton ?_ (by norm_num)
  have hT2 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  rw [← Finset.card_pos, Finset.card_sdiff_of_subset hZT, hT2]
  omega

/-- G1 applied to the witness family: `|{{0,1}}| = 1 ≤ 2² = r^k`. -/
example : ((({{0, 1}} : Finset (Finset (Fin 3))).card : ℚ)) ≤ 2 ^ 2 :=
  card_le_pow_of_forall_linkAt_not_isRSpread (by norm_num)
    (by
      intro S hS
      rw [Finset.mem_singleton] at hS
      subst hS
      decide)
    forall_linkAt_not_isRSpread_pair

end AntiSpread

-- ════════════════════════════════════════════════════════════════════
-- §3 G2 — THE REGULARIZATION LOOP, HONEST FORM
--    ALWZ Lemma 2.4 / Rao Theorem 1 / Stoeckl one-shot, with the size
--    clause carried. The complement {S ∈ F : Z ⊄ S} is DISCARDED, as
--    in the primary texts: no statement below bounds it (P8).
-- ════════════════════════════════════════════════════════════════════

section RegularizationLoop

/-- **The regularization loop, honest form** (ALWZ arXiv:1908.08483
    Lemma 2.4; Rao arXiv:1909.04774 Theorem 1; Stoeckl one-shot
    maximizer): every `k`-uniform `F` above the threshold `r^k` yields
    a witness `Z` with `|Z| < k` whose link is `r`-spread,
    `(k − |Z|)`-uniform, nonempty, and LARGE in both senses:
    the size clause `|F| ≤ |linkAt Z F|·r^|Z|` (the link pays for all
    of `F` at cost `r^|Z|`) and its consequence
    `r^(k−|Z|) < |linkAt Z F|` (the link beats its own threshold —
    the loop invariant reproduced at width `k − |Z|`). Without the
    size clause the statement would be trivially satisfied by
    degenerate links; `exists_isRSpread_linkAt_uniform` derives it
    and discards it, this form carries it.

    HONESTY (P8): the complement `{S ∈ F : ¬ Z ⊆ S}` is discarded —
    the primary texts bound only the iterative bad sets (ALWZ
    Lemma 2.6/2.8), never this complement, and neither does this
    statement.

    Side condition: `0 < r` suffices (weaker than the `1 ≤ r` of
    `exists_isRSpread_linkAt_uniform`); for `r < 1` the threshold
    hypothesis is weak but the statement remains true and honest. -/
theorem exists_isRSpread_linkAt_loop {r : ℚ} {k : ℕ} (hr : 0 < r)
    {F : Finset (Finset (Fin n))} (hunif : ∀ S ∈ F, S.card = k)
    (hcard : r ^ k < (F.card : ℚ)) :
    ∃ Z : Finset (Fin n), Z.card < k ∧
      IsRSpread r (linkAt Z F) ∧
      (∀ E ∈ linkAt Z F, E.card = k - Z.card) ∧
      (linkAt Z F).Nonempty ∧
      (F.card : ℚ) ≤ ((linkAt Z F).card : ℚ) * r ^ Z.card ∧
      r ^ (k - Z.card) < ((linkAt Z F).card : ℚ) := by
  have hF : F.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast (pow_pos hr k).trans hcard
  obtain ⟨Z, ⟨S₀, hS₀F, hZS₀⟩, hspread, hsize⟩ :=
    exists_isRSpread_linkAt r hr F hF
  have hZk : Z.card ≤ k := by
    have h := Finset.card_le_card hZS₀
    rwa [hunif S₀ hS₀F] at h
  -- cancel r^|Z|: the link beats its own threshold
  have hsplit : r ^ k = r ^ (k - Z.card) * r ^ Z.card := by
    rw [← pow_add]
    congr 1
    omega
  have hthresh : r ^ (k - Z.card) < ((linkAt Z F).card : ℚ) := by
    have h1 : r ^ (k - Z.card) * r ^ Z.card <
        ((linkAt Z F).card : ℚ) * r ^ Z.card := by
      rw [← hsplit]
      exact lt_of_lt_of_le hcard hsize
    exact lt_of_mul_lt_mul_right h1 (pow_pos hr Z.card).le
  -- |Z| = k would cap the link at the single member ∅
  have hZk_lt : Z.card < k := by
    rcases lt_or_eq_of_le hZk with h | h
    · exact h
    · exfalso
      have h0 : k - Z.card = 0 := by omega
      rw [h0, pow_zero] at hthresh
      have hsub : linkAt Z F ⊆ {∅} := by
        intro E hE
        have hcard0 := linkAt_uniform hunif E hE
        rw [h0] at hcard0
        exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp hcard0)
      have hle1 : ((linkAt Z F).card : ℚ) ≤ 1 := by
        exact_mod_cast (Finset.card_le_card hsub).trans
          (Finset.card_singleton ∅).le
      linarith
  exact ⟨Z, hZk_lt, hspread, linkAt_uniform hunif,
    linkAt_nonempty_iff.mpr ⟨S₀, hS₀F, hZS₀⟩, hsize, hthresh⟩

/-- **Conditional ALWZ reduction, decomposition form**: IF the
    probabilistic spread lemma holds on the structurally decomposed
    instances — the links of `F` at witnesses `|Z| < k`, carrying all
    six loop clauses — THEN every `k`-uniform `F` with `|F| > r^k` has
    an `s`-sunflower. The spread lemma is the single explicit
    hypothesis, demanded only where the loop lands (compare
    Spread.lean's `hasSunflower_of_forall_isRSpread`, which demands it
    for every width and every family;
    `hasSunflower_of_forall_isRSpread_via_loop` below certifies the
    subsumption). Instantiating at `r = C·s·log k` is the
    ALWZ/Rao/BCW/Stoeckl `(C·s·log k)^k` bound.

    UPGRADE PATH (Rao, arXiv:1909.04774, p. 2, after Lemma 2): "As far
    as we know, it is possible that Lemma 2 holds even when
    r(p,k) = O(p). Such a strengthening of Lemma 2 would imply the
    sunflower conjecture of Erdős and Rado." A spread lemma valid at
    some `r = O(s)` fed to this hypothesis would give `f(k,s) ≤ (Cs)^k`;
    nothing at that strength is stated or claimed here (ASU barrier,
    master brief §5 O1). -/
theorem hasSunflower_of_forall_linkAt_isRSpread {r : ℚ} {s k : ℕ} (hr : 0 < r)
    {F : Finset (Finset (Fin n))}
    (spread_lemma : ∀ Z : Finset (Fin n), Z.card < k →
      IsRSpread r (linkAt Z F) →
      (∀ E ∈ linkAt Z F, E.card = k - Z.card) →
      (linkAt Z F).Nonempty →
      (F.card : ℚ) ≤ ((linkAt Z F).card : ℚ) * r ^ Z.card →
      r ^ (k - Z.card) < ((linkAt Z F).card : ℚ) →
      HasSunflower (linkAt Z F) s)
    (hunif : ∀ S ∈ F, S.card = k) (hcard : r ^ k < (F.card : ℚ)) :
    HasSunflower F s := by
  obtain ⟨Z, hZk, hspread, hunif', hne, hsize, hthresh⟩ :=
    exists_isRSpread_linkAt_loop hr hunif hcard
  exact (spread_lemma Z hZk hspread hunif' hne hsize hthresh).of_linkAt

/-- Subsumption certificate: the per-level universally-quantified
    spread-lemma interface of Spread.lean's
    `hasSunflower_of_forall_isRSpread` factors through the link-local
    decomposition form by instantiation at `k' = k − |Z|`,
    `G = linkAt Z F`. The loop form is the stronger reduction: its
    hypothesis demands the spread lemma only on links of `F`, never on
    arbitrary families. -/
theorem hasSunflower_of_forall_isRSpread_via_loop {r : ℚ} {s : ℕ} (hr : 1 ≤ r)
    (spread_lemma : ∀ k' : ℕ, ∀ G : Finset (Finset (Fin n)), 1 ≤ k' →
      (∀ S ∈ G, S.card = k') → IsRSpread r G →
      r ^ k' < (G.card : ℚ) → HasSunflower G s)
    {k : ℕ} {F : Finset (Finset (Fin n))}
    (hunif : ∀ S ∈ F, S.card = k) (hcard : r ^ k < (F.card : ℚ)) :
    HasSunflower F s :=
  hasSunflower_of_forall_linkAt_isRSpread (lt_of_lt_of_le one_pos hr)
    (fun Z hZk hspread hunif' _ _ hthresh =>
      spread_lemma (k - Z.card) (linkAt Z F) (by omega) hunif' hspread hthresh)
    hunif hcard

end RegularizationLoop

-- ════════════════════════════════════════════════════════════════════
-- §4 G3 — THE SPREAD-DEFECT BRIDGE IS FALSE (REFUTED)
--    Hypothesis H (B1): τ(S(F))/τ(F) is bounded by a function of the
--    spread radius r*(F) alone. FALSE at every spread level b ≥ 4: the
--    b-ary product family (k blocks of size b, members = transversals)
--    is EXACTLY b-spread with τ = b for every k, yet every fully
--    compressed shift endpoint of it carries s-sunflowers for every s
--    with s^(2s-2) < 2^k — the ratio is unbounded along k at pinned r*.
--    Mechanism (§4c): spreadness forces |F| ≥ r^k ≥ 4^k, and the
--    compression headline (IsFullShiftOf.hasSunflower) turns size into
--    endpoint sunflowers. Spread families shift violently, not tamely.
-- ════════════════════════════════════════════════════════════════════

section ProductFamily

/-- Unique block/slot decomposition: `b*i + c` with `c < b` determines
    `(i, c)` — divide by `b`. -/
theorem block_slot_inj {b i i' c c' : ℕ} (hc : c < b) (hc' : c' < b)
    (h : b * i + c = b * i' + c') : i = i' ∧ c = c' := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le c) hc
  have hi : i = i' := by
    have h1 : (b * i + c) / b = i := by
      rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hc, Nat.add_zero]
    have h2 : (b * i' + c') / b = i' := by
      rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hc', Nat.add_zero]
    rw [← h1, h, h2]
  subst hi
  exact ⟨rfl, by omega⟩

/-- The vertex of block `i`, slot `f i`, on the ground set `Fin (b*k)`
    cut into `k` contiguous blocks of size `b`. -/
def productVertex {b k : ℕ} (f : Fin k → Fin b) (i : Fin k) : Fin (b * k) :=
  ⟨b * i.val + (f i).val, by
    calc b * i.val + (f i).val < b * i.val + b := Nat.add_lt_add_left (f i).isLt _
      _ = b * (i.val + 1) := by ring
      _ ≤ b * k := Nat.mul_le_mul_left b i.isLt⟩

theorem productVertex_eq_iff {b k : ℕ} {f g : Fin k → Fin b} {i i' : Fin k} :
    productVertex f i = productVertex g i' ↔ i = i' ∧ f i = g i' := by
  constructor
  · intro h
    have hval : b * i.val + (f i).val = b * i'.val + (g i').val :=
      congrArg Fin.val h
    obtain ⟨h1, h2⟩ := block_slot_inj (f i).isLt (g i').isLt hval
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  · rintro ⟨rfl, h⟩
    exact Fin.ext (by show b * i.val + (f i).val = b * i.val + (g i).val; rw [h])

/-- The transversal of `f`: one vertex per block, slot `f i` in block `i`. -/
def productSet (b k : ℕ) (f : Fin k → Fin b) : Finset (Fin (b * k)) :=
  Finset.univ.image (productVertex f)

theorem mem_productSet {b k : ℕ} {f : Fin k → Fin b} {v : Fin (b * k)} :
    v ∈ productSet b k f ↔ ∃ i : Fin k, v = productVertex f i := by
  unfold productSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr fun i => eq_comm

theorem productSet_card (b k : ℕ) (f : Fin k → Fin b) :
    (productSet b k f).card = k := by
  unfold productSet
  rw [Finset.card_image_of_injOn fun i _ i' _ h => (productVertex_eq_iff.mp h).1,
    Finset.card_univ, Fintype.card_fin]

theorem productSet_injective (b k : ℕ) :
    Function.Injective (productSet b k) := by
  intro f g h
  funext i
  have hv : productVertex f i ∈ productSet b k g := by
    rw [← h]
    exact mem_productSet.mpr ⟨i, rfl⟩
  obtain ⟨i', hi'⟩ := mem_productSet.mp hv
  obtain ⟨h1, h2⟩ := productVertex_eq_iff.mp hi'
  subst h1
  exact h2

/-- **The `b`-ary product family**: all transversals of `k` blocks of
    size `b` — the Erdős–Rado product construction at block size `b`.
    `|F| = b^k`, `k`-uniform, EXACTLY `b`-spread
    (`productFamily_isRSpread` / `productFamily_not_isRSpread`), and
    `τ(F) = b` for every `k` (`productFamily_sunflowerNumber`): the
    canonical low-τ inhabitant of the high-spread regime. -/
def productFamily (b k : ℕ) : Finset (Finset (Fin (b * k))) :=
  Finset.univ.image (productSet b k)

theorem mem_productFamily {b k : ℕ} {S : Finset (Fin (b * k))} :
    S ∈ productFamily b k ↔ ∃ f : Fin k → Fin b, productSet b k f = S := by
  unfold productFamily
  simp [Finset.mem_image]

theorem productFamily_card (b k : ℕ) : (productFamily b k).card = b ^ k := by
  unfold productFamily
  rw [Finset.card_image_of_injective _ (productSet_injective b k),
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem productFamily_uniform (b k : ℕ) :
    ∀ S ∈ productFamily b k, S.card = k := by
  intro S hS
  obtain ⟨f, rfl⟩ := mem_productFamily.mp hS
  exact productSet_card b k f

theorem productFamily_nonempty {b k : ℕ} (hb : 0 < b) :
    (productFamily b k).Nonempty := by
  rw [← Finset.card_pos, productFamily_card]
  exact pow_pos hb k

end ProductFamily

section ProductFamilySpread

/-- The product family is `b`-spread — with EQUALITY on every inhabited
    probe: if `Z` is contained in a member then `|F_Z|·b^|Z| = b^k`.
    Counting: the transversals containing `Z` form a `piFinset` pinned
    to `Z`'s slots on `Z`'s blocks and free elsewhere, of size
    `b^(k-|Z|)`. -/
theorem productFamily_isRSpread (b k : ℕ) :
    IsRSpread (b : ℚ) (productFamily b k) := by
  intro Z hZne
  rcases ((productFamily b k).filter fun S => Z ⊆ S).eq_empty_or_nonempty with
    hemp | ⟨S₀, hS₀⟩
  · rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact_mod_cast Nat.zero_le _
  · rw [Finset.mem_filter] at hS₀
    obtain ⟨hS₀F, hZS₀⟩ := hS₀
    obtain ⟨f₀, rfl⟩ := mem_productFamily.mp hS₀F
    -- count members over Z by their generating functions
    have hcount : ((productFamily b k).filter fun S => Z ⊆ S).card
        = ((Finset.univ : Finset (Fin k → Fin b)).filter
            fun f => Z ⊆ productSet b k f).card := by
      unfold productFamily
      rw [Finset.filter_image]
      exact Finset.card_image_of_injOn ((productSet_injective b k).injOn)
    -- the function-side filter is a piFinset pinned on Z's blocks
    have hpi : (Finset.univ : Finset (Fin k → Fin b)).filter
          (fun f => Z ⊆ productSet b k f)
        = Fintype.piFinset (fun i =>
            if productVertex f₀ i ∈ Z then {f₀ i} else Finset.univ) := by
      ext g
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro hZg i
        split_ifs with hiZ
        · obtain ⟨i', hi'⟩ := mem_productSet.mp (hZg hiZ)
          obtain ⟨h1, h2⟩ := productVertex_eq_iff.mp hi'.symm
          cases h1
          rw [Finset.mem_singleton, h2]
        · exact Finset.mem_univ _
      · intro hg v hvZ
        obtain ⟨i, hi⟩ := mem_productSet.mp (hZS₀ hvZ)
        have hiZ : productVertex f₀ i ∈ Z := hi ▸ hvZ
        have hgi := hg i
        rw [if_pos hiZ, Finset.mem_singleton] at hgi
        rw [hi]
        exact mem_productSet.mpr ⟨i, productVertex_eq_iff.mpr ⟨rfl, hgi.symm⟩⟩
    -- the piFinset count: 1 on Z's blocks, b on free blocks
    have hcard_pi : (Fintype.piFinset (fun i =>
          if productVertex f₀ i ∈ Z then ({f₀ i} : Finset (Fin b))
          else Finset.univ)).card = b ^ (k - Z.card) := by
      rw [Fintype.card_piFinset]
      have hpoint : ∀ i : Fin k,
          (if productVertex f₀ i ∈ Z then ({f₀ i} : Finset (Fin b))
            else Finset.univ).card
          = if productVertex f₀ i ∈ Z then 1 else b := by
        intro i
        split_ifs
        · exact Finset.card_singleton _
        · rw [Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_congr rfl fun i _ => hpoint i, Finset.prod_ite,
        Finset.prod_const_one, Finset.prod_const, one_mul]
      congr 1
      -- Z's blocks biject with Z itself
      have htZ : ((Finset.univ : Finset (Fin k)).filter
            fun i => productVertex f₀ i ∈ Z).card = Z.card := by
        apply Finset.card_bij (fun i _ => productVertex f₀ i)
        · intro a ha
          exact (Finset.mem_filter.mp ha).2
        · intro a₁ ha₁ a₂ ha₂ h
          exact (productVertex_eq_iff.mp h).1
        · intro v hv
          obtain ⟨i, hi⟩ := mem_productSet.mp (hZS₀ hv)
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi ▸ hv⟩, hi.symm⟩
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin k)))
        (p := fun i => productVertex f₀ i ∈ Z)
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      omega
    -- assemble the ℕ identity |F_Z| · b^|Z| = b^k and cast
    have hZk : Z.card ≤ k := by
      calc Z.card ≤ (productSet b k f₀).card := Finset.card_le_card hZS₀
        _ = k := productSet_card b k f₀
    have hnat : ((productFamily b k).filter fun S => Z ⊆ S).card * b ^ Z.card
        = b ^ k := by
      rw [hcount, hpi, hcard_pi, ← pow_add, Nat.sub_add_cancel hZk]
    have heq : ((((productFamily b k).filter fun S => Z ⊆ S).card : ℚ))
        * (b : ℚ) ^ Z.card = ((productFamily b k).card : ℚ) := by
      rw [productFamily_card, ← hnat]
      push_cast
      ring
    exact le_of_eq heq

/-- The product family is not `r`-spread for any `r > b`: probe at a
    full member. Together with `productFamily_isRSpread` this pins the
    spread radius at r* = b exactly, independent of `k`. -/
theorem productFamily_not_isRSpread (b k : ℕ) (hb : 0 < b) (hk : 1 ≤ k)
    {r : ℚ} (hr : (b : ℚ) < r) : ¬ IsRSpread r (productFamily b k) := by
  intro hsp
  set S₀ := productSet b k (fun _ => (⟨0, hb⟩ : Fin b)) with hS₀def
  have hS₀F : S₀ ∈ productFamily b k := mem_productFamily.mpr ⟨_, rfl⟩
  have hS₀ne : S₀.Nonempty := by
    rw [← Finset.card_pos, hS₀def, productSet_card]
    omega
  have h := hsp S₀ hS₀ne
  have hmem : S₀ ∈ (productFamily b k).filter fun S => S₀ ⊆ S :=
    Finset.mem_filter.mpr ⟨hS₀F, Finset.Subset.refl _⟩
  have h1 : (1 : ℚ) ≤ (((productFamily b k).filter fun S => S₀ ⊆ S).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨S₀, hmem⟩
  rw [hS₀def, productSet_card] at h
  have hb0 : (0 : ℚ) ≤ (b : ℚ) := Nat.cast_nonneg b
  have hrpos : (0 : ℚ) < r := lt_of_le_of_lt hb0 hr
  have hFc : ((productFamily b k).card : ℚ) = (b : ℚ) ^ k := by
    rw [productFamily_card]
    push_cast
    ring
  have hlt : (b : ℚ) ^ k < r ^ k := by
    apply pow_lt_pow_left₀ hr hb0 (by omega)
  have hge : r ^ k ≤ (b : ℚ) ^ k := by
    calc r ^ k = 1 * r ^ k := (one_mul _).symm
      _ ≤ (((productFamily b k).filter fun S => S₀ ⊆ S).card : ℚ) * r ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ((productFamily b k).card : ℚ) := h
      _ = (b : ℚ) ^ k := hFc
  linarith

end ProductFamilySpread

section ProductFamilyTau

/-- Sunflowers in the product family have at most `b` petals: the
    kernel is a partial transversal, every petal is a transversal of
    the same free blocks, and projecting to the block of any petal
    vertex of one member is injective on the sunflower (a collision
    would push that vertex into the kernel). -/
theorem productFamily_sunflowerNumber_le (b k : ℕ) :
    sunflowerNumber (productFamily b k) ≤ b := by
  apply sunflowerNumber_le_of_forall
  rintro m ⟨sub, hsub, hcard, K, hsf⟩
  rw [← hcard]
  rcases sub.eq_empty_or_nonempty with rfl | ⟨S₀, hS₀⟩
  · simp
  · have hS₀F : S₀ ∈ productFamily b k := hsub hS₀
    obtain ⟨f₀, hf₀⟩ := mem_productFamily.mp hS₀F
    -- a petal vertex of S₀ and its block i⋆
    have hpetal := hsf.2.1 S₀ hS₀
    rw [ne_eq, Finset.sdiff_eq_empty_iff_subset] at hpetal
    obtain ⟨v₀, hv₀S, hv₀K⟩ := Finset.not_subset.mp hpetal
    obtain ⟨istar, histar⟩ := mem_productSet.mp (hf₀ ▸ hv₀S)
    -- slot projection at block i⋆ is injective on the sunflower
    calc sub.card ≤ (Finset.univ : Finset (Fin b)).card := by
          apply Finset.card_le_card_of_injOn
            (fun T => if h : ∃ f : Fin k → Fin b, productSet b k f = T
              then h.choose istar else f₀ istar)
          · intro T _
            exact Finset.mem_univ _
          · intro T hT T' hT' heq
            by_contra hne
            have hTm : T ∈ sub := Finset.mem_coe.mp hT
            have hT'm : T' ∈ sub := Finset.mem_coe.mp hT'
            have hTex : ∃ f, productSet b k f = T :=
              mem_productFamily.mp (hsub hTm)
            have hT'ex : ∃ f, productSet b k f = T' :=
              mem_productFamily.mp (hsub hT'm)
            simp only [dif_pos hTex, dif_pos hT'ex] at heq
            -- the common slot puts the block-i⋆ vertex in both members
            have hw : productVertex hTex.choose istar ∈ T := by
              have h : productVertex hTex.choose istar
                  ∈ productSet b k hTex.choose := mem_productSet.mpr ⟨istar, rfl⟩
              rwa [hTex.choose_spec] at h
            have hw' : productVertex hTex.choose istar ∈ T' := by
              have h : productVertex hTex.choose istar
                  ∈ productSet b k hT'ex.choose := mem_productSet.mpr
                ⟨istar, productVertex_eq_iff.mpr ⟨rfl, heq⟩⟩
              rwa [hT'ex.choose_spec] at h
            -- hence in the kernel, hence in S₀ at block i⋆ — that is v₀
            have hwK : productVertex hTex.choose istar ∈ K := by
              rw [← hsf.2.2 T hTm T' hT'm hne]
              exact Finset.mem_inter.mpr ⟨hw, hw'⟩
            have hwS₀ : productVertex hTex.choose istar ∈ productSet b k f₀ := by
              rw [hf₀]
              exact hsf.1 S₀ hS₀ hwK
            obtain ⟨i', hi'⟩ := mem_productSet.mp hwS₀
            obtain ⟨h1, -⟩ := productVertex_eq_iff.mp hi'
            cases h1
            have hfK : productVertex f₀ istar ∈ K := by rwa [hi'] at hwK
            rw [← histar] at hfK
            exact hv₀K hfK
      _ = b := by rw [Finset.card_univ, Fintype.card_fin]

/-- The matching of the `b` constant transversals: an empty-kernel
    `b`-sunflower, witnessing `τ(productFamily b k) ≥ b`. -/
theorem productFamily_hasSunflower (b k : ℕ) (hk : 1 ≤ k) :
    HasSunflower (productFamily b k) b := by
  have hinj : Set.InjOn (fun j : Fin b => productSet b k fun _ => j)
      ↑(Finset.univ : Finset (Fin b)) := by
    intro j _ j' _ h
    exact congrFun (productSet_injective b k h) ⟨0, hk⟩
  refine ⟨(Finset.univ : Finset (Fin b)).image
    fun j => productSet b k fun _ => j, ?_, ?_, ∅, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
    exact mem_productFamily.mpr ⟨_, rfl⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_fin]
  · intro T _
    exact Finset.empty_subset T
  · intro T hT
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
    rw [Finset.sdiff_empty]
    intro h0
    have hc := productSet_card b k fun _ => j
    rw [h0, Finset.card_empty] at hc
    omega
  · intro T₁ hT₁ T₂ hT₂ hne
    obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hT₁
    obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hT₂
    have hjj : j₁ ≠ j₂ := fun h => hne (by rw [h])
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
    obtain ⟨i₁, hi₁⟩ := mem_productSet.mp hv₁
    obtain ⟨i₂, hi₂⟩ := mem_productSet.mp hv₂
    rw [hi₁] at hi₂
    exact hjj (productVertex_eq_iff.mp hi₂).2

/-- `τ(productFamily b k) = b`, independent of the uniformity `k`. -/
theorem productFamily_sunflowerNumber (b k : ℕ) (hk : 1 ≤ k) :
    sunflowerNumber (productFamily b k) = b :=
  le_antisymm (productFamily_sunflowerNumber_le b k)
    (le_sunflowerNumber _ (productFamily_hasSunflower b k hk))

end ProductFamilyTau

section SpreadDefectRefuted

/-- Arithmetic for the witness scale: `s^(2(s-1)) < 2^(2s²)` for `s ≥ 1`,
    via `s < 2^s`. -/
theorem pow_two_mul_pred_lt_two_pow {s : ℕ} (hs : 1 ≤ s) :
    s ^ (2 * (s - 1)) < 2 ^ (2 * s * s) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have h1 : (t + 1) ^ (2 * (t + 1 - 1)) ≤ (2 ^ (t + 1)) ^ (2 * t) := by
    rw [Nat.add_sub_cancel]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have h2 : ((2 : ℕ) ^ (t + 1)) ^ (2 * t) = 2 ^ ((t + 1) * (2 * t)) := by
    rw [← pow_mul]
  have h3 : (2 : ℕ) ^ ((t + 1) * (2 * t)) < 2 ^ (2 * (t + 1) * (t + 1)) := by
    apply Nat.pow_lt_pow_right (by norm_num)
    nlinarith
  calc (t + 1) ^ (2 * (t + 1 - 1)) ≤ 2 ^ ((t + 1) * (2 * t)) := h2 ▸ h1
    _ < 2 ^ (2 * (t + 1) * (t + 1)) := h3

/-- **The τ-transport floor — spread families shift violently.** Every
    fully compressed shift endpoint of an `r`-spread (`r ≥ 4`)
    `k`-uniform family contains an `s`-sunflower for every `s` with
    `s^(2s-2) < 2^k`. Mechanism: spreadness forces `|F| ≥ r^k ≥ 4^k`
    (`IsRSpread.pow_card_le`), cardinality survives the chain, and the
    compression headline (`IsFullShiftOf.hasSunflower`) converts size
    into endpoint sunflowers. The floor depends only on `k`, never on
    `τ(F)` — the seed of the refutation below. -/
theorem IsFullShiftOf.hasSunflower_of_isRSpread {k s : ℕ} {r : ℚ}
    {F shifted : Finset (Finset (Fin n))} (hshift : IsFullShiftOf shifted F)
    (hr : 4 ≤ r) (hspread : IsRSpread r F)
    (hunif : ∀ S ∈ F, S.card = k) (hne : F.Nonempty)
    (hs : 1 ≤ s) (hsk : s ^ (2 * (s - 1)) < 2 ^ k) :
    HasSunflower shifted s := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [pow_zero] at hsk
      have := Nat.one_le_pow (2 * (s - 1)) s (by omega)
      omega
    · exact h
  have h4k : 4 ^ k ≤ F.card := by
    have h1 : ((4 : ℚ)) ^ k ≤ r ^ k := pow_le_pow_left₀ (by norm_num) hr k
    have h2 : r ^ k ≤ (F.card : ℚ) :=
      hspread.pow_card_le (by linarith) hunif hk hne
    have h3 : ((4 : ℚ)) ^ k ≤ (F.card : ℚ) := le_trans h1 h2
    exact_mod_cast h3
  apply hshift.hasSunflower hs hunif
  calc s ^ (2 * (s - 1)) * 2 ^ k < 2 ^ k * 2 ^ k :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).mpr hsk
    _ = 4 ^ k := by rw [← mul_pow]; norm_num
    _ ≤ F.card := h4k

/-- **G3 REFUTED — the spread-defect bridge is false at every spread
    level `b ≥ 4`**: for every candidate bound `g` there is a `k`-uniform
    family that is EXACTLY `b`-spread (r* = b, both directions pinned)
    with `τ(F) = b`, all of whose fully compressed shift endpoints
    inflate τ past `g·τ(F)`. Witness: `productFamily b k` at
    `k = 2(gb+1)²`. Endpoints exist unconditionally
    (`exists_isFullShiftOf`), so the final clause is never vacuous. -/
theorem spread_defect_unbounded (b g : ℕ) (hb : 4 ≤ b) :
    ∃ (N k : ℕ) (F : Finset (Finset (Fin N))),
      (∀ S ∈ F, S.card = k) ∧
      IsRSpread (b : ℚ) F ∧
      (∀ r : ℚ, (b : ℚ) < r → ¬ IsRSpread r F) ∧
      sunflowerNumber F = b ∧
      ∀ shifted : Finset (Finset (Fin N)),
        Nonempty (IsFullShiftOf shifted F) →
        g * sunflowerNumber F < sunflowerNumber shifted := by
  set s : ℕ := g * b + 1 with hs_def
  have hs1 : 1 ≤ s := by omega
  have hss : 1 ≤ s * s := Nat.mul_le_mul hs1 hs1
  set k : ℕ := 2 * s * s with hk_def
  have hk1 : 1 ≤ k := by
    have : 2 * s * s = 2 * (s * s) := by ring
    omega
  refine ⟨b * k, k, productFamily b k, productFamily_uniform b k,
    productFamily_isRSpread b k,
    fun r hr => productFamily_not_isRSpread b k (by omega) hk1 hr,
    productFamily_sunflowerNumber b k hk1, ?_⟩
  rintro shifted ⟨hfs⟩
  have hfloor : HasSunflower shifted s :=
    hfs.hasSunflower_of_isRSpread (by exact_mod_cast hb)
      (productFamily_isRSpread b k) (productFamily_uniform b k)
      (productFamily_nonempty (by omega)) hs1
      (pow_two_mul_pred_lt_two_pow hs1)
  have hτs : s ≤ sunflowerNumber shifted := le_sunflowerNumber _ hfloor
  rw [productFamily_sunflowerNumber b k hk1]
  omega

/-- **G3 REFUTED, bridge form** (mirrors `mishra_v1_lemma3_false`): no
    bound `τ(S(F)) ≤ g·τ(F)` holds uniformly over `b`-spread `k`-uniform
    families and their fully compressed shift endpoints, for any
    constant `g` and any spread level `b ≥ 4`. Since the witnesses have
    r* = b exactly, no function `g(r*)` of the spread radius alone can
    bound the τ-inflation of the full shift — Hypothesis H (B1) is
    false; its empirical support was an artifact of the zoo (random
    families at `|F| ≥ 4^k` carry large `τ(F)`; the product family
    pins `τ(F) = b`). -/
theorem spread_defect_bridge_false (b g : ℕ) (hb : 4 ≤ b) :
    ¬ ∀ (N k : ℕ) (F shifted : Finset (Finset (Fin N))),
        (∀ S ∈ F, S.card = k) → IsRSpread (b : ℚ) F →
        Nonempty (IsFullShiftOf shifted F) →
        sunflowerNumber shifted ≤ g * sunflowerNumber F := by
  intro hH
  obtain ⟨N, k, F, hunif, hspread, -, -, hkill⟩ := spread_defect_unbounded b g hb
  obtain ⟨shifted, hfs⟩ := exists_isFullShiftOf F
  have h1 := hH N k F shifted hunif hspread hfs
  have h2 := hkill shifted hfs
  omega

end SpreadDefectRefuted
