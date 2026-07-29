/-
  Erdős Problem #20 — R-spread families vs Frankl-shifted families.

  Formal interface between the two structural regimes of the modern
  sunflower literature (consumer brief:
  data/erdos20/CONSUMER_ALWZ_SPR_V_COMP.md):

  · the ALWZ/Rao/BCW spread regime [arXiv:1908.08483, 1909.04774,
    2009.09327]: R-spread families (no element-set is popular) contain
    sunflowers via the probabilistic spread lemma — NOT formalized here
    (that is the hard (C·s·log k)^k frontier);
  · the compression regime (ShiftedSunflower.lean): fully compressed
    families contain sunflowers unconditionally once
    |F| > s^(2s-2)·2^k (v2 headline, no log factor).

  MAIN RESULT (`IsShiftedFrom.lt_sunflowerNumber_of_isRSpread`): for
  SHIFTED families the two regimes are mutually exclusive. r-spreadness
  for any r > 2 already forces τ(F) > k — a (k+1)-sunflower in F
  itself, more petals than the uniformity. Proof: the star bound
  (v2 Lemma 5, `IsShiftedFrom.star_card_half`) pushes half of F onto
  the star at the least element m whenever τ(F) ≤ k, while r-spreadness
  at Z = {m} caps that star at |F|/r; for r > 2 the two collide on a
  nonempty family.

  Also packaged:
  · `IsRSpread` — the ALWZ Definition 1.10 / Tao formulation, in the
    division-free form |F_Z|·r^|Z| ≤ |F| over ℚ (brief §6 F1);
  · `exists_popular_witness` — failure of spreadness yields a popular
    witness Z (brief §6 F2; the object Rene's 2026-01-12 comment on
    erdosproblems.com/20 asks to exploit directly);
  · regularization (ALWZ Phase 1 / Stoeckl, proof of Lemma 5
    ('Entry material' section), brief §6 F5; full
    extraction in data/erdos20/CONSUMER_STOECKL_SPREAD.md §5.1, §7.3):
    a Z maximizing |F_Z|·r^|Z| has an r-spread link {S \ Z : Z ⊆ S∈F}
    at size cost r^|Z| (`exists_isRSpread_linkAt`, uniform interface
    `exists_isRSpread_linkAt_uniform`); sunflowers in the link lift
    back (`HasSunflower.of_linkAt`), so the probabilistic spread lemma
    is the ONLY unformalized piece of the (C·s·log k)^k bound —
    `hasSunflower_of_forall_isRSpread` proves the reduction with the
    spread lemma as an explicit hypothesis (no axiom, no sorry; per
    the Stoeckl brief §7.2 the lemma itself is blocked on
    Shannon-entropy infrastructure absent from Mathlib);
  · spreadness caps: r^k ≤ |F| (`IsRSpread.pow_card_le`, certifying that
    the |F| ≥ r^k hypothesis in ALWZ Theorem 1.1 is automatic) and
    k·r ≤ n (`IsRSpread.mul_le_ground`, the spread regime needs a large
    ground set — double counting element-stars);
  · `hasSunflower_or_spread_large_of_cover` — the counting skeleton of
    the spread/compressed decomposition question (brief §4): if F is
    covered by a designated spread part and a fully compressed part and
    beats the sum of the two thresholds, then either the spread part is
    large (only the unformalized spread lemma can continue there) or F
    already contains an s-sunflower inherited from the compressed part
    (sunflowers in subfamilies need no pullback, unlike shift endpoints,
    cf. Counterexample.lean).

  Honest framing: the main result is an easy composition of the already
  formalized star bound with the spread definition. Its value is
  locating ALL remaining difficulty of Erdős #20 for shifted families in
  the non-spread regime — consistent with shifting being a concentration
  operation (tau-inflation, Counterexample.lean) — and providing the
  formal vocabulary (popular witnesses, covers) for the decomposition
  program. It is NOT progress on the spread lemma itself.

  NOTATION MAP (literature → Lean):
    R-spread (ALWZ Def. 1.10 / Tao) → IsRSpread r F   (r : ℚ, probability-free)
    F_Z = {S ∈ F : Z ⊆ S}         → F.filter (fun S => Z ⊆ S)
    popular witness I             → Z from exists_popular_witness
    A_x (star at x)               → F.filter (fun S => x ∈ S)
-/

import Erdos.Erdos20.Sunflower
import Erdos.Erdos20.ShiftedSunflower

open Finset

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════
-- §1 SPREAD DEFINITION AND BASIC API
-- ════════════════════════════════════════════════════════════════════

section SpreadBasics

/-- A family `F` is `r`-spread if no nonempty `Z` is popular: the
    subfamily containing `Z` has density at most `r^(-|Z|)` in `F`.
    Division-free form over ℚ: `|F_Z| · r^|Z| ≤ |F|`. Larger `r` means
    more spread. (ALWZ arXiv:1908.08483 Definition 1.10; Tao's `R`-spread
    probability formulation `Pr[Z ⊆ S] ≤ R^(-|Z|)`.) -/
def IsRSpread (r : ℚ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ Z : Finset (Fin n), Z.Nonempty →
    ((F.filter fun S => Z ⊆ S).card : ℚ) * r ^ Z.card ≤ (F.card : ℚ)

/-- Spreadness is downward monotone in `r` (for nonnegative `r`). -/
theorem IsRSpread.mono {r r' : ℚ} {F : Finset (Finset (Fin n))}
    (h : IsRSpread r F) (hr' : 0 ≤ r') (hle : r' ≤ r) : IsRSpread r' F := by
  intro Z hZ
  calc ((F.filter fun S => Z ⊆ S).card : ℚ) * r' ^ Z.card
      ≤ ((F.filter fun S => Z ⊆ S).card : ℚ) * r ^ Z.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr' hle _) (by positivity)
    _ ≤ (F.card : ℚ) := h Z hZ

/-- The singleton instance of spreadness: every star is small,
    `|A_x| · r ≤ |F|`. -/
theorem IsRSpread.star_card_le {r : ℚ} {F : Finset (Finset (Fin n))}
    (h : IsRSpread r F) (x : Fin n) :
    ((F.filter fun S => x ∈ S).card : ℚ) * r ≤ (F.card : ℚ) := by
  have hx := h {x} (Finset.singleton_nonempty x)
  simpa [Finset.singleton_subset_iff] using hx

/-- A nonempty `r`-spread `k`-uniform family (`k ≥ 1`, `r ≥ 0`) has at
    least `r^k` members: take `Z` to be a member. This certifies that
    the `|F| ≥ r^k` hypothesis of ALWZ Theorem 1.1 is automatic. -/
theorem IsRSpread.pow_card_le {r : ℚ} {k : ℕ} {F : Finset (Finset (Fin n))}
    (h : IsRSpread r F) (hr : 0 ≤ r) (hunif : ∀ S ∈ F, S.card = k)
    (hk : 1 ≤ k) (hne : F.Nonempty) : r ^ k ≤ (F.card : ℚ) := by
  obtain ⟨S₀, hS₀⟩ := hne
  have hS₀ne : S₀.Nonempty := by
    rw [← Finset.card_pos, hunif S₀ hS₀]; omega
  have hZ := h S₀ hS₀ne
  rw [hunif S₀ hS₀] at hZ
  have hmem : S₀ ∈ F.filter fun S => S₀ ⊆ S :=
    Finset.mem_filter.mpr ⟨hS₀, Finset.Subset.refl S₀⟩
  have h1 : (1 : ℚ) ≤ ((F.filter fun S => S₀ ⊆ S).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨S₀, hmem⟩
  calc r ^ k = 1 * r ^ k := (one_mul _).symm
    _ ≤ ((F.filter fun S => S₀ ⊆ S).card : ℚ) * r ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (F.card : ℚ) := hZ

/-- Spreadness is capped by the dimension ratio: a nonempty `r`-spread
    `k`-uniform family on `Fin n` forces `k·r ≤ n`. Double counting:
    `∑_x |A_x| = k·|F|`, while each star obeys `|A_x| ≤ |F|/r`. The
    spread regime is only inhabited on large ground sets. -/
theorem IsRSpread.mul_le_ground {r : ℚ} {k : ℕ} {F : Finset (Finset (Fin n))}
    (h : IsRSpread r F) (hunif : ∀ S ∈ F, S.card = k) (hne : F.Nonempty) :
    (k : ℚ) * r ≤ (n : ℚ) := by
  classical
  -- double count incidences: ∑_x |A_x| = ∑_{S ∈ F} |S| = k·|F|
  have hdouble : ∑ x : Fin n, (F.filter fun S => x ∈ S).card = k * F.card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ S ∈ F, (∑ x : Fin n, if x ∈ S then 1 else 0) = k := by
      intro S hS
      rw [← Finset.card_filter, Finset.filter_univ_mem, hunif S hS]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]
  -- sum the singleton spread bounds over the ground set
  have hsum : ((k * F.card : ℕ) : ℚ) * r ≤ (n : ℚ) * (F.card : ℚ) := by
    rw [← hdouble, Nat.cast_sum, Finset.sum_mul]
    calc ∑ x : Fin n, ((F.filter fun S => x ∈ S).card : ℚ) * r
        ≤ ∑ _x : Fin n, (F.card : ℚ) :=
          Finset.sum_le_sum fun x _ => h.star_card_le x
      _ = (n : ℚ) * (F.card : ℚ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- cancel |F| > 0
  have hFpos : (0 : ℚ) < (F.card : ℚ) := by
    have h0 : 0 < F.card := Finset.card_pos.mpr hne
    exact_mod_cast h0
  apply le_of_mul_le_mul_right _ hFpos
  calc (k : ℚ) * r * (F.card : ℚ) = ((k * F.card : ℕ) : ℚ) * r := by
        push_cast; ring
    _ ≤ (n : ℚ) * (F.card : ℚ) := hsum

/-- Failure of spreadness produces a popular witness: a nonempty `Z`
    whose subfamily `F_Z` beats the `r^(-|Z|)` density bound. This is
    the object the ALWZ regularization loop extracts and restricts to
    at each step, and the object Rene's comment (erdosproblems.com/20,
    2026-01-12) asks to exploit directly to build a sunflower. -/
theorem exists_popular_witness {r : ℚ} {F : Finset (Finset (Fin n))}
    (h : ¬ IsRSpread r F) :
    ∃ Z : Finset (Fin n), Z.Nonempty ∧
      (F.card : ℚ) < ((F.filter fun S => Z ⊆ S).card : ℚ) * r ^ Z.card := by
  unfold IsRSpread at h
  push Not at h
  exact h

end SpreadBasics

-- ════════════════════════════════════════════════════════════════════
-- §2 SPREAD SHIFTED FAMILIES HAVE SUNFLOWERS BEYOND THE UNIFORMITY
--    The star bound concentrates shifted families; spreadness forbids
--    concentration. For r > 2 the only escape is τ(F) > k.
-- ════════════════════════════════════════════════════════════════════

section SpreadVsShifted

/-- **Spreadness and shiftedness are mutually exclusive regimes.**
    A nonempty `k`-uniform family (`k ≥ 1`) that is shifted from `m` and
    `r`-spread for some `r > 2` has `τ(F) > k`: it contains a sunflower
    with more petals than the uniformity. Proof: if `τ(F) ≤ k`, the star
    bound (v2 Lemma 5, `IsShiftedFrom.star_card_half`) gives
    `|F| ≤ 2·|A_m|`, while spreadness at `Z = {m}` gives `|A_m|·r ≤ |F|`;
    together `r ≤ 2`. -/
theorem IsShiftedFrom.lt_sunflowerNumber_of_isRSpread {m k : ℕ} {r : ℚ}
    {F : Finset (Finset (Fin n))} (hshift : IsShiftedFrom m F)
    (hunif : ∀ S ∈ F, S.card = k) (hk : 1 ≤ k) (hne : F.Nonempty)
    (hr : 2 < r) (hspread : IsRSpread r F) :
    k < sunflowerNumber F := by
  by_contra hτ
  push Not at hτ
  -- the ground-set bound m is realized, so m < n
  obtain ⟨S₀, hS₀⟩ := hne
  have hS₀ne : S₀.Nonempty := by
    rw [← Finset.card_pos, hunif S₀ hS₀]; omega
  obtain ⟨x₀, hx₀⟩ := hS₀ne
  have hmn : m < n := lt_of_le_of_lt (hshift.1 S₀ hS₀ x₀ hx₀) x₀.isLt
  -- star bound (compression) vs singleton spread bound at the least element
  have hstar := hshift.star_card_half hunif hτ hk hmn
  have hspr := hspread.star_card_le (⟨m, hmn⟩ : Fin n)
  set A := F.filter fun S => (⟨m, hmn⟩ : Fin n) ∈ S
  have hF1 : 1 ≤ F.card := Finset.card_pos.mpr ⟨S₀, hS₀⟩
  have hA1 : 1 ≤ A.card := by omega
  have hApos : (0 : ℚ) < (A.card : ℚ) := by
    have h0 : 0 < A.card := hA1
    exact_mod_cast h0
  have hcast : (F.card : ℚ) ≤ 2 * (A.card : ℚ) := by exact_mod_cast hstar
  have hlt : 2 * (A.card : ℚ) < r * (A.card : ℚ) :=
    mul_lt_mul_of_pos_right hr hApos
  have hle : r * (A.card : ℚ) ≤ 2 * (A.card : ℚ) :=
    calc r * (A.card : ℚ) = (A.card : ℚ) * r := mul_comm _ _
      _ ≤ (F.card : ℚ) := hspr
      _ ≤ 2 * (A.card : ℚ) := hcast
  linarith

/-- Petal form of the exclusion theorem: a nonempty `r`-spread (`r > 2`)
    shifted `k`-uniform family (`k ≥ 1`) contains a `(k+1)`-sunflower.
    For shifted families the spread regime of ALWZ is trivial: the
    sunflower exists in `F` itself, with no spread lemma and no log
    factor. All remaining difficulty lives in the non-spread regime. -/
theorem IsShiftedFrom.hasSunflower_succ_of_isRSpread {m k : ℕ} {r : ℚ}
    {F : Finset (Finset (Fin n))} (hshift : IsShiftedFrom m F)
    (hunif : ∀ S ∈ F, S.card = k) (hk : 1 ≤ k) (hne : F.Nonempty)
    (hr : 2 < r) (hspread : IsRSpread r F) :
    HasSunflower F (k + 1) :=
  hasSunflower_of_le_sunflowerNumber
    (hshift.lt_sunflowerNumber_of_isRSpread hunif hk hne hr hspread)

/-- The exclusion theorem for fully compressed families. -/
theorem IsFullyCompressed.hasSunflower_succ_of_isRSpread {k : ℕ} {r : ℚ}
    {F : Finset (Finset (Fin n))} (hcomp : IsFullyCompressed F)
    (hunif : ∀ S ∈ F, S.card = k) (hk : 1 ≤ k) (hne : F.Nonempty)
    (hr : 2 < r) (hspread : IsRSpread r F) :
    HasSunflower F (k + 1) :=
  hcomp.isShiftedFrom_zero.hasSunflower_succ_of_isRSpread
    hunif hk hne hr hspread

end SpreadVsShifted

-- ════════════════════════════════════════════════════════════════════
-- §3 DECOMPOSITION SKELETON (brief §4)
--    The counting interface of the open decomposition question. The
--    spread half is the unformalized frontier; the compressed half is
--    closed by ShiftedSunflower.lean, and its sunflower needs no
--    pullback because subfamily sunflowers are family sunflowers.
-- ════════════════════════════════════════════════════════════════════

section Decomposition

/-- Sunflowers transfer to superfamilies. -/
theorem HasSunflower.mono_family {F G : Finset (Finset (Fin n))} {s : ℕ}
    (h : HasSunflower F s) (hFG : F ⊆ G) : HasSunflower G s := by
  obtain ⟨sub, hsub, hcard, K, hsf⟩ := h
  exact ⟨sub, hsub.trans hFG, hcard, K, hsf⟩

/-- Counting skeleton of the spread/compressed decomposition question:
    if `F` is covered by a designated "spread part" `Fs` and a fully
    compressed `k`-uniform part `Fc ⊆ F`, and `|F|` beats the sum of a
    spread threshold `Ts` and the shifted-family threshold
    `s^(2s-2)·2^k`, then either the spread part is large — the regime
    where only ALWZ-type spread arguments can continue — or `F` already
    contains an `s`-sunflower, inherited from `Fc` with no pullback
    problem. Closing the first disjunct for ANY constructible cover is
    exactly the open decomposition question (brief §4 / §6 F7). -/
theorem hasSunflower_or_spread_large_of_cover {s k Ts : ℕ} (hs : 1 ≤ s)
    {F Fs Fc : Finset (Finset (Fin n))}
    (hcover : F ⊆ Fs ∪ Fc) (hFc : Fc ⊆ F)
    (hcomp : IsFullyCompressed Fc) (hunif : ∀ S ∈ Fc, S.card = k)
    (hcard : Ts + s ^ (2 * (s - 1)) * 2 ^ k < F.card) :
    Ts < Fs.card ∨ HasSunflower F s := by
  by_cases hFs : Ts < Fs.card
  · exact Or.inl hFs
  · push Not at hFs
    refine Or.inr ?_
    have h1 : F.card ≤ Fs.card + Fc.card :=
      le_trans (Finset.card_le_card hcover) (Finset.card_union_le Fs Fc)
    have h2 : s ^ (2 * (s - 1)) * 2 ^ k < Fc.card := by omega
    exact (hcomp.hasSunflower hs hunif h2).mono_family hFc

end Decomposition

-- ════════════════════════════════════════════════════════════════════
-- §4 REGULARIZATION (ALWZ Phase 1 / Stoeckl, proof of Lemma 5
--    ('Entry material' section))
--    The combinatorial half of the ALWZ proof, in Stoeckl's one-shot
--    form: a Z maximizing q(Z) = |F_Z|·r^|Z| has an r-spread link
--    {S \ Z : Z ⊆ S ∈ F}, at size cost r^|Z| — no restriction loop.
--    Sunflowers in the link lift back to F (kernel grows by Z), so
--    the probabilistic spread lemma is the ONLY unformalized piece of
--    the (C·s·log k)^k bound; `hasSunflower_of_forall_isRSpread`
--    packages that reduction with the spread lemma as an explicit
--    hypothesis (consumer brief: CONSUMER_STOECKL_SPREAD.md §5.1,
--    §7.3 — the entropy proof of the spread lemma itself is blocked
--    on Shannon-entropy infrastructure absent from Mathlib).
-- ════════════════════════════════════════════════════════════════════

section Regularization

/-- The link of `F` at `Z`: members containing `Z`, with `Z` removed.
    (Stoeckl, proof of Lemma 5 ('Entry material' section): the
    restricted family `{A_j \ S₀ : S₀ ⊆ A_j}`;
    generalizes `sunflowerLink` from a vertex to a set of vertices,
    staying on the same ground type — no relabeling.) -/
def linkAt (Z : Finset (Fin n)) (F : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  (F.filter fun S => Z ⊆ S).image fun S => S \ Z

/-- `S ↦ S \ Z` is injective on members containing `Z`. -/
theorem sdiff_injOn_filter (Z : Finset (Fin n)) (F : Finset (Finset (Fin n))) :
    Set.InjOn (fun S => S \ Z) ↑(F.filter fun S => Z ⊆ S) := by
  intro S hS T hT heq
  have hZS : Z ⊆ S := (Finset.mem_filter.mp hS).2
  have hZT : Z ⊆ T := (Finset.mem_filter.mp hT).2
  have heq' : S \ Z = T \ Z := heq
  calc S = S \ Z ∪ Z := (Finset.sdiff_union_of_subset hZS).symm
    _ = T \ Z ∪ Z := by rw [heq']
    _ = T := Finset.sdiff_union_of_subset hZT

/-- Membership in the link: sets disjoint from `Z` whose union with `Z`
    is a member of `F`. -/
theorem mem_linkAt {Z E : Finset (Fin n)} {F : Finset (Finset (Fin n))} :
    E ∈ linkAt Z F ↔ Disjoint E Z ∧ E ∪ Z ∈ F := by
  constructor
  · intro hE
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hE
    have hZS : Z ⊆ S := (Finset.mem_filter.mp hS).2
    exact ⟨Finset.sdiff_disjoint,
      by rw [Finset.sdiff_union_of_subset hZS]; exact (Finset.mem_filter.mp hS).1⟩
  · rintro ⟨hdisj, hmem⟩
    exact Finset.mem_image.mpr ⟨E ∪ Z,
      Finset.mem_filter.mpr ⟨hmem, Finset.subset_union_right⟩,
      Finset.union_sdiff_cancel_right hdisj⟩

/-- The link has the size of the subfamily over `Z`. -/
theorem linkAt_card (Z : Finset (Fin n)) (F : Finset (Finset (Fin n))) :
    (linkAt Z F).card = (F.filter fun S => Z ⊆ S).card :=
  Finset.card_image_of_injOn (sdiff_injOn_filter Z F)

/-- Probes disjoint from `Z` count subfamilies over `Z ∪ Z'`: the
    `Z'`-star of the link is the image of the `Z ∪ Z'`-subfamily. -/
theorem linkAt_filter_card {Z Z' : Finset (Fin n)} (F : Finset (Finset (Fin n)))
    (hdisj : Disjoint Z' Z) :
    ((linkAt Z F).filter fun E => Z' ⊆ E).card
      = (F.filter fun S => Z ∪ Z' ⊆ S).card := by
  unfold linkAt
  rw [Finset.filter_image, Finset.filter_filter]
  have hpred : ∀ S ∈ F, ((Z ⊆ S) ∧ Z' ⊆ S \ Z) ↔ Z ∪ Z' ⊆ S := by
    intro S _
    constructor
    · rintro ⟨hZ, hZ'⟩
      exact Finset.union_subset hZ (hZ'.trans Finset.sdiff_subset)
    · intro h
      obtain ⟨hZ, hZ'⟩ := Finset.union_subset_iff.mp h
      exact ⟨hZ, fun x hx => Finset.mem_sdiff.mpr
        ⟨hZ' hx, fun hxZ => Finset.disjoint_left.mp hdisj hx hxZ⟩⟩
  rw [Finset.filter_congr hpred]
  apply Finset.card_image_of_injOn
  exact Set.InjOn.mono
    (fun S hS => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hS).1,
       Finset.subset_union_left.trans (Finset.mem_filter.mp hS).2⟩)
    (sdiff_injOn_filter Z F)

/-- The link of a `k`-uniform family is `(k - |Z|)`-uniform. -/
theorem linkAt_uniform {Z : Finset (Fin n)} {F : Finset (Finset (Fin n))} {k : ℕ}
    (hunif : ∀ S ∈ F, S.card = k) :
    ∀ E ∈ linkAt Z F, E.card = k - Z.card := by
  intro E hE
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hE
  rw [Finset.card_sdiff_of_subset (Finset.mem_filter.mp hS).2,
    hunif S (Finset.mem_filter.mp hS).1]

/-- At a singleton the link specializes to `sunflowerLink`. -/
theorem linkAt_singleton (a : Fin n) (F : Finset (Finset (Fin n))) :
    linkAt {a} F = sunflowerLink a F := by
  unfold linkAt sunflowerLink
  rw [show (fun S : Finset (Fin n) => S \ {a}) = (fun S => S.erase a) from
        funext fun S => (Finset.erase_eq S a).symm,
    Finset.filter_congr fun S _ => Finset.singleton_subset_iff]

/-- Sunflowers in the link lift to the family: rejoin `Z` to every
    petal, the kernel grows by `Z`. (Stoeckl, proof of Lemma 5
    ('Entry material' section): the "cost" paragraph — the number of
    petals is preserved.) -/
theorem HasSunflower.of_linkAt {Z : Finset (Fin n)} {F : Finset (Finset (Fin n))}
    {s : ℕ} (h : HasSunflower (linkAt Z F) s) : HasSunflower F s := by
  obtain ⟨sub, hsub, hcard, K, hsf⟩ := h
  have hmem : ∀ E ∈ sub, Disjoint E Z ∧ E ∪ Z ∈ F :=
    fun E hE => mem_linkAt.mp (hsub hE)
  have hinj : Set.InjOn (fun E => E ∪ Z) ↑sub := by
    intro E₁ hE₁ E₂ hE₂ heq
    have heq' : E₁ ∪ Z = E₂ ∪ Z := heq
    calc E₁ = (E₁ ∪ Z) \ Z :=
          (Finset.union_sdiff_cancel_right (hmem E₁ hE₁).1).symm
      _ = (E₂ ∪ Z) \ Z := by rw [heq']
      _ = E₂ := Finset.union_sdiff_cancel_right (hmem E₂ hE₂).1
  refine ⟨sub.image fun E => E ∪ Z, ?_, ?_, K ∪ Z, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
    exact (hmem E hE).2
  · rw [Finset.card_image_of_injOn hinj, hcard]
  · -- kernel inclusion
    intro T hT
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.union_subset_union (hsf.1 E hE) (Finset.Subset.refl Z)
  · -- nonempty petals
    intro T hT
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
    have hpetal := hsf.2.1 E hE
    rw [ne_eq, Finset.sdiff_eq_empty_iff_subset] at hpetal
    obtain ⟨x, hxE, hxK⟩ := Finset.not_subset.mp hpetal
    have hxZ : x ∉ Z := Finset.disjoint_left.mp (hmem E hE).1 hxE
    rw [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.not_subset]
    exact ⟨x, Finset.mem_union.mpr (Or.inl hxE),
      fun habs => (Finset.mem_union.mp habs).elim hxK hxZ⟩
  · -- pairwise intersections
    intro T₁ hT₁ T₂ hT₂ hne
    obtain ⟨E₁, hE₁, rfl⟩ := Finset.mem_image.mp hT₁
    obtain ⟨E₂, hE₂, rfl⟩ := Finset.mem_image.mp hT₂
    have hEne : E₁ ≠ E₂ := fun h => hne (by rw [h])
    rw [← Finset.inter_union_distrib_right, hsf.2.2 E₁ hE₁ E₂ hE₂ hEne]

/-- **Regularization** (ALWZ Phase 1 / Stoeckl, proof of Lemma 5
    ('Entry material' section), one-shot form):
    every nonempty family has a witness `Z` — the maximizer of
    `q(Z) = |F_Z|·r^|Z|` — that is contained in a member, whose link is
    `r`-spread, and whose size cost is only `r^|Z|`:
    `|F| ≤ |linkAt Z F|·r^|Z|`. The popular-witness restriction loop of
    ALWZ collapses into the single maximization: for any probe `Z'`
    disjoint from `Z`, maximality `q(Z ∪ Z') ≤ q(Z)` is exactly the
    spread inequality of the link. -/
theorem exists_isRSpread_linkAt (r : ℚ) (hr : 0 < r)
    (F : Finset (Finset (Fin n))) (hF : F.Nonempty) :
    ∃ Z : Finset (Fin n), (∃ S ∈ F, Z ⊆ S) ∧
      IsRSpread r (linkAt Z F) ∧
      (F.card : ℚ) ≤ ((linkAt Z F).card : ℚ) * r ^ Z.card := by
  classical
  -- maximize q over all of Finset (Fin n) = univ.powerset
  obtain ⟨Z, _, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Fin n)).powerset)
    (fun W => ((F.filter fun S => W ⊆ S).card : ℚ) * r ^ W.card)
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have hmax' : ∀ W : Finset (Fin n),
      ((F.filter fun S => W ⊆ S).card : ℚ) * r ^ W.card
        ≤ ((F.filter fun S => Z ⊆ S).card : ℚ) * r ^ Z.card :=
    fun W => hmax W (Finset.mem_powerset.mpr (Finset.subset_univ W))
  -- the base point: q(∅) = |F|
  have hbase : (F.card : ℚ) ≤
      ((F.filter fun S => Z ⊆ S).card : ℚ) * r ^ Z.card := by
    simpa using hmax' ∅
  -- the subfamily over Z is nonempty: otherwise q(Z) = 0 < |F| ≤ q(Z)
  have hfilter_pos : 0 < (F.filter fun S => Z ⊆ S).card := by
    rcases Nat.eq_zero_or_pos (F.filter fun S => Z ⊆ S).card with h0 | hpos
    · exfalso
      rw [h0] at hbase
      norm_num at hbase
      exact hF.ne_empty hbase
    · exact hpos
  obtain ⟨S₀, hS₀⟩ := Finset.card_pos.mp hfilter_pos
  refine ⟨Z, ⟨S₀, (Finset.mem_filter.mp hS₀).1, (Finset.mem_filter.mp hS₀).2⟩,
    ?_, ?_⟩
  · -- spreadness of the link from maximality of q
    intro Z' _
    by_cases hdisj : Disjoint Z' Z
    · rw [linkAt_filter_card F hdisj, linkAt_card]
      have hcard_union : (Z ∪ Z').card = Z.card + Z'.card :=
        Finset.card_union_of_disjoint hdisj.symm
      apply le_of_mul_le_mul_right _ (pow_pos hr Z.card)
      calc ((F.filter fun S => Z ∪ Z' ⊆ S).card : ℚ) * r ^ Z'.card * r ^ Z.card
          = ((F.filter fun S => Z ∪ Z' ⊆ S).card : ℚ) * r ^ (Z ∪ Z').card := by
            rw [hcard_union, pow_add]; ring
        _ ≤ ((F.filter fun S => Z ⊆ S).card : ℚ) * r ^ Z.card := hmax' (Z ∪ Z')
    · -- probes meeting Z see an empty star: link members avoid Z
      have hempty : ((linkAt Z F).filter fun E => Z' ⊆ E) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro E hE
        have hE' := Finset.mem_filter.mp hE
        exact hdisj ((mem_linkAt.mp hE'.1).1.mono_left hE'.2)
      rw [hempty]
      simp
  · rw [linkAt_card]
    exact hbase

/-- Regularization, `k`-uniform form above the ALWZ threshold
    `|F| > r^k`: the witness `Z` has `|Z| < k`, the link is `r`-spread,
    `(k - |Z|)`-uniform, and itself beats its own threshold
    `r^(k-|Z|)`. This is the exact interface the (unformalized,
    entropy-blocked) spread lemma consumes. -/
theorem exists_isRSpread_linkAt_uniform {r : ℚ} {k : ℕ} (hr : 1 ≤ r)
    {F : Finset (Finset (Fin n))} (hunif : ∀ S ∈ F, S.card = k)
    (hcard : r ^ k < (F.card : ℚ)) :
    ∃ Z : Finset (Fin n), Z.card < k ∧
      IsRSpread r (linkAt Z F) ∧
      (∀ E ∈ linkAt Z F, E.card = k - Z.card) ∧
      r ^ (k - Z.card) < ((linkAt Z F).card : ℚ) := by
  have hr0 : (0 : ℚ) < r := lt_of_lt_of_le one_pos hr
  have hF : F.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast lt_trans (pow_pos hr0 k) hcard
  obtain ⟨Z, ⟨S, hSF, hZS⟩, hspread, hsize⟩ := exists_isRSpread_linkAt r hr0 F hF
  have hZk : Z.card ≤ k := by
    calc Z.card ≤ S.card := Finset.card_le_card hZS
      _ = k := hunif S hSF
  -- the link beats its own threshold: cancel r^|Z| in r^k < |link|·r^|Z|
  have hsplit : r ^ k = r ^ (k - Z.card) * r ^ Z.card := by
    rw [← pow_add]
    congr 1
    omega
  have hthresh : r ^ (k - Z.card) < ((linkAt Z F).card : ℚ) := by
    have h1 : r ^ (k - Z.card) * r ^ Z.card <
        ((linkAt Z F).card : ℚ) * r ^ Z.card := by
      rw [← hsplit]
      exact lt_of_lt_of_le hcard hsize
    exact lt_of_mul_lt_mul_right h1 (pow_pos hr0 Z.card).le
  -- |Z| = k would make the link a ≥2-element family of empty sets
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
      have hle : (linkAt Z F).card ≤ 1 :=
        le_trans (Finset.card_le_card hsub) (by simp)
      have : ((linkAt Z F).card : ℚ) ≤ 1 := by exact_mod_cast hle
      linarith
  exact ⟨Z, hZk_lt, hspread, linkAt_uniform hunif, hthresh⟩

/-- **Conditional ALWZ reduction**: IF the spread lemma holds at
    spreadness `r` and petal count `s` — every `r`-spread uniform
    family of positive uniformity above its `r^k'` threshold has an
    `s`-sunflower — THEN every `k`-uniform family with `|F| > r^k` has
    an `s`-sunflower. Instantiating `spread_lemma` at
    `r = C·s·log k` is exactly the ALWZ/Rao/BCW/Stoeckl bound
    (C ≤ 64); the hypothesis is the probabilistic frontier blocked on
    Shannon-entropy infrastructure (consumer brief §7.2), and
    everything before it is combinatorial and proved here. -/
theorem hasSunflower_of_forall_isRSpread {r : ℚ} {s : ℕ} (hr : 1 ≤ r)
    (spread_lemma : ∀ k' : ℕ, ∀ G : Finset (Finset (Fin n)), 1 ≤ k' →
      (∀ S ∈ G, S.card = k') → IsRSpread r G →
      r ^ k' < (G.card : ℚ) → HasSunflower G s)
    {k : ℕ} {F : Finset (Finset (Fin n))}
    (hunif : ∀ S ∈ F, S.card = k) (hcard : r ^ k < (F.card : ℚ)) :
    HasSunflower F s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- k = 0: F ⊆ {∅} caps |F| at 1, but the threshold forces |F| > 1
    exfalso
    have hsub : F ⊆ {∅} := fun S hS =>
      Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (hunif S hS))
    have h1 : F.card ≤ 1 := le_trans (Finset.card_le_card hsub) (by simp)
    have h1' : (F.card : ℚ) ≤ 1 := by exact_mod_cast h1
    rw [pow_zero] at hcard
    linarith
  · obtain ⟨Z, hZk, hspread, hunif', hthresh⟩ :=
      exists_isRSpread_linkAt_uniform hr hunif hcard
    exact (spread_lemma (k - Z.card) (linkAt Z F) (by omega)
      hunif' hspread hthresh).of_linkAt

end Regularization

-- ════════════════════════════════════════════════════════════════════
-- §5 NON-VACUITY
--    The exclusion theorem has inhabitants: {{0},{1},{2}} on Fin 3 is
--    shifted, 1-uniform, and (5/2)-spread, and the theorem produces its
--    2-sunflower. (Consistent with `mul_le_ground`: k·r = 5/2 ≤ 3 = n.)
-- ════════════════════════════════════════════════════════════════════

section NonVacuity

/- The And-of-bounded-foralls `Decidable` instance for `IsShiftedFrom`
   exceeds the default `synthInstance.maxSize`; split the conjunction and
   decide each side. ℚ arithmetic does not kernel-reduce, so the spread
   check uses `native_decide` (same trust model as Counterexample.lean). -/

example : IsShiftedFrom 0 ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) := by
  refine ⟨fun S _ x _ => Nat.zero_le _, ?_⟩
  native_decide

example : IsRSpread (5 / 2 : ℚ) ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) := by
  unfold IsRSpread
  native_decide

example : HasSunflower ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) 2 :=
  IsShiftedFrom.hasSunflower_succ_of_isRSpread (m := 0) (r := 5 / 2)
    (⟨fun S _ x _ => Nat.zero_le _, by native_decide⟩)
    (by native_decide)
    le_rfl
    (by native_decide)
    (by norm_num)
    (by unfold IsRSpread; native_decide)

end NonVacuity
