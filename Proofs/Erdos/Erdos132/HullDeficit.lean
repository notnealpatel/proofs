import Erdos.Erdos132.ThreeInteriorCounting

set_option autoImplicit false

open scoped BigOperators

namespace Erdos132.HullDeficit

open Erdos132.TwoInteriorCircle

/-- Unordered distinct pairs are monotone under inclusion of their endpoint sets. -/
theorem pairs_mono {α : Type*} {A B : Finset α} (hAB : A ⊆ B) :
    pairs A ⊆ pairs B := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
      obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs A a b).mp he
      exact (mk_mem_pairs B a b).mpr ⟨hAB ha, hAB hb, hab⟩

/-- Distance multiplicity cannot decrease when points are added. -/
theorem multiplicity_mono {α : Type*} [PseudoMetricSpace α] {A B : Finset α}
    (hAB : A ⊆ B) (r : ℝ) : TwoInteriorCircle.multiplicity A r ≤
      TwoInteriorCircle.multiplicity B r := by
  classical
  unfold TwoInteriorCircle.multiplicity
  exact Finset.card_le_card (fun e he =>
    Finset.mem_filter.mpr ⟨pairs_mono hAB (Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2⟩)

/-- If adding points preserves the diameter, every old occurring nondiameter
length remains an occurring nondiameter length. -/
theorem nonDiameterDistances_mono_of_diam_eq {A B : Finset Plane}
    (hAB : A ⊆ B)
    (hdiam : Metric.diam (B : Set Plane) = Metric.diam (A : Set Plane)) :
    nonDiameterDistances A ⊆ nonDiameterDistances B := by
  intro r hr
  obtain ⟨⟨a, ha, b, hb, hab, hrab⟩, hrD⟩ := (mem_nonDiameterDistances A r).mp hr
  apply (mem_nonDiameterDistances B r).mpr
  exact ⟨⟨a, hAB ha, b, hAB hb, hab, hrab⟩, hdiam ▸ hrD⟩

/-- The strict-subdiameter pair finset is monotone when endpoint inclusion and
preservation of the actual diameter are both available. -/
theorem strictPairs_mono_of_diam_eq {A B : Finset Plane}
    (hAB : A ⊆ B)
    (hdiam : Metric.diam (B : Set Plane) = Metric.diam (A : Set Plane)) :
    ((pairs A).filter fun e => pairDist e < Metric.diam (A : Set Plane)) ⊆
      ((pairs B).filter fun e => pairDist e < Metric.diam (B : Set Plane)) := by
  intro e he
  obtain ⟨heA, heD⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨pairs_mono hAB heA, hdiam ▸ heD⟩

/-- Exact deficit accounting on actual unordered pairs.  Each inherited class
is charged only for its missing multiplicity, while each genuinely new class
is charged its full contrary-hypothesis threshold. -/
theorem deficit_le_pair_difference {A B : Finset Plane}
    (hAB : A ⊆ B)
    (hdiam : Metric.diam (B : Set Plane) = Metric.diam (A : Set Plane))
    (hlarge : ∀ r ∈ nonDiameterDistances B, B.card + 1 ≤ multiplicity B r) :
    (∑ r ∈ nonDiameterDistances A, (B.card + 1 - multiplicity A r)) +
        ((nonDiameterDistances B \ nonDiameterDistances A).card * (B.card + 1)) ≤
      B.card.choose 2 - A.card.choose 2 := by
  classical
  let SA := nonDiameterDistances A
  let SB := nonDiameterDistances B
  let QA := (pairs A).filter fun e => pairDist e < Metric.diam (A : Set Plane)
  let QB := (pairs B).filter fun e => pairDist e < Metric.diam (B : Set Plane)
  have hS : SA ⊆ SB := nonDiameterDistances_mono_of_diam_eq hAB hdiam
  have hQ : QA ⊆ QB := strictPairs_mono_of_diam_eq hAB hdiam
  have hmono : ∀ r ∈ SA, multiplicity A r ≤ multiplicity B r := by
    intro r _hr
    exact multiplicity_mono hAB r
  have hinherited :
      ∑ r ∈ SA, (B.card + 1 - multiplicity A r) ≤
        ∑ r ∈ SA, (multiplicity B r - multiplicity A r) := by
    apply Finset.sum_le_sum
    intro r hr
    exact Nat.sub_le_sub_right (hlarge r (hS hr)) _
  have hnew : (SB \ SA).card * (B.card + 1) ≤
      ∑ r ∈ SB \ SA, multiplicity B r := by
    calc
      _ = ∑ _r ∈ SB \ SA, (B.card + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun r hr => hlarge r (Finset.mem_sdiff.mp hr).1)
  have hsumSplit :
      (∑ r ∈ SA, multiplicity B r) + (∑ r ∈ SB \ SA, multiplicity B r) =
        ∑ r ∈ SB, multiplicity B r := by
    rw [← Finset.sum_union]
    · congr 1
      exact Finset.union_sdiff_of_subset hS
    · exact Finset.disjoint_sdiff
  have hsumA : ∑ r ∈ SA, multiplicity A r = QA.card := by
    exact sum_nonDiameter_multiplicity A
  have hsumB : ∑ r ∈ SB, multiplicity B r = QB.card := by
    exact sum_nonDiameter_multiplicity B
  have hdiffSum :
      (∑ r ∈ SA, (multiplicity B r - multiplicity A r)) +
          (∑ r ∈ SA, multiplicity A r) = ∑ r ∈ SA, multiplicity B r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact Nat.sub_add_cancel (hmono r hr)
  have hdiff :
      (∑ r ∈ SA, (multiplicity B r - multiplicity A r)) +
          (∑ r ∈ SB \ SA, multiplicity B r) = QB.card - QA.card := by
    omega
  have hsdiff : QB \ QA ⊆ pairs B \ pairs A := by
    intro e he
    obtain ⟨heQB, heQA⟩ := Finset.mem_sdiff.mp he
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_filter.mp heQB).1, ?_⟩
    intro heA
    apply heQA
    exact Finset.mem_filter.mpr ⟨heA, hdiam ▸ (Finset.mem_filter.mp heQB).2⟩
  have hpairdiff : QB.card - QA.card ≤ B.card.choose 2 - A.card.choose 2 := by
    calc
      QB.card - QA.card = (QB \ QA).card := (Finset.card_sdiff_of_subset hQ).symm
      _ ≤ (pairs B \ pairs A).card := Finset.card_le_card hsdiff
      _ = (pairs B).card - (pairs A).card :=
        Finset.card_sdiff_of_subset (pairs_mono hAB)
      _ = B.card.choose 2 - A.card.choose 2 := by rw [card_pairs, card_pairs]
  calc
    _ ≤ (∑ r ∈ SA, (multiplicity B r - multiplicity A r)) +
        ∑ r ∈ SB \ SA, multiplicity B r := Nat.add_le_add hinherited hnew
    _ = QB.card - QA.card := hdiff
    _ ≤ _ := hpairdiff

/-- The two-element binomial coefficient splits into old, cross, and new pairs. -/
theorem choose_add_two (m h : ℕ) :
    (m + h).choose 2 = m.choose 2 + h * m + h.choose 2 := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hstep : h.succ.choose 2 = h + h.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      calc
        (m + h.succ).choose 2 = (m + h).choose 1 + (m + h).choose 2 := by
          rw [Nat.add_succ, Nat.choose_succ_succ]
        _ = (m + h) + (m.choose 2 + h * m + h.choose 2) := by
          rw [Nat.choose_one_right, ih]
        _ = m.choose 2 + h.succ * m + h.succ.choose 2 := by
          rw [hstep, Nat.succ_mul]
          omega

/-- For disjoint finite sets, the actual number of unordered pairs introduced
by adjoining `I` to `H` is `|I||H| + choose |I| 2`. -/
theorem choose_union_sub_choose (H I : Finset Plane) (hdisj : Disjoint H I) :
    (H ∪ I).card.choose 2 - H.card.choose 2 =
      I.card * H.card + I.card.choose 2 := by
  rw [Finset.card_union_of_disjoint hdisj, choose_add_two]
  omega

/-- Every pair involving an interior point is strictly shorter than the hull
diameter, so adjoining interiors creates no new diameter pair. -/
theorem diameter_multiplicity_union (H I : Finset Plane) (hcard : 2 ≤ H.card)
    (hInt : ∀ p ∈ I, p ∈ interior (convexHull ℝ (H : Set Plane))) :
    multiplicity (H ∪ I) (Metric.diam (H : Set Plane)) =
      multiplicity H (Metric.diam (H : Set Plane)) := by
  classical
  unfold TwoInteriorCircle.multiplicity
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b =>
      simp only [Finset.mem_filter, pairDist_mk]
      constructor
      · rintro ⟨he, habD⟩
        obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs (H ∪ I) a b).mp he
        rcases Finset.mem_union.mp ha with haH | haI
        · rcases Finset.mem_union.mp hb with hbH | hbI
          · exact ⟨(mk_mem_pairs H a b).mpr ⟨haH, hbH, hab⟩, habD⟩
          · have hlt := dist_lt_diam_hull H hcard (hInt b hbI)
              (subset_convexHull ℝ (H : Set Plane) haH)
            rw [dist_comm, habD] at hlt
            exact False.elim ((lt_irrefl _) hlt)
        · have hbHull : b ∈ convexHull ℝ (H : Set Plane) := by
            rcases Finset.mem_union.mp hb with hbH | hbI
            · exact subset_convexHull ℝ (H : Set Plane) hbH
            · exact interior_subset (hInt b hbI)
          have hlt := dist_lt_diam_hull H hcard (hInt a haI) hbHull
          rw [habD] at hlt
          exact False.elim ((lt_irrefl _) hlt)
      · rintro ⟨he, habD⟩
        obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs H a b).mp he
        exact ⟨(mk_mem_pairs (H ∪ I) a b).mpr
          ⟨Finset.mem_union_left I ha, Finset.mem_union_left I hb, hab⟩, habD⟩

/-- Actual nondiameter classes together with the actual diameter class fit in
the complete unordered-pair budget. -/
theorem support_diameter_budget (X : Finset Plane)
    (hlarge : ∀ r ∈ nonDiameterDistances X,
      X.card + 1 ≤ multiplicity X r) :
    (nonDiameterDistances X).card * (X.card + 1) +
        multiplicity X (Metric.diam (X : Set Plane)) ≤ X.card.choose 2 := by
  classical
  let Q := (pairs X).filter fun e => pairDist e < Metric.diam (X : Set Plane)
  let R := (pairs X).filter fun e => pairDist e = Metric.diam (X : Set Plane)
  have hclasses : (nonDiameterDistances X).card * (X.card + 1) ≤ Q.card := by
    rw [← sum_nonDiameter_multiplicity]
    calc
      _ = ∑ _r ∈ nonDiameterDistances X, (X.card + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum hlarge
  have hdisj : Disjoint Q R := by
    apply Finset.disjoint_left.mpr
    intro e heQ heR
    have hlt := (Finset.mem_filter.mp heQ).2
    have heq := (Finset.mem_filter.mp heR).2
    exact (ne_of_lt hlt) heq
  have hunion : Q ∪ R ⊆ pairs X := by
    intro e he
    rcases Finset.mem_union.mp he with heQ | heR
    · exact (Finset.mem_filter.mp heQ).1
    · exact (Finset.mem_filter.mp heR).1
  have hpair : Q.card + R.card ≤ (pairs X).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  change _ + R.card ≤ _
  rw [← card_pairs X]
  exact Nat.add_le_add_right hclasses R.card |>.trans hpair

/-- A nonempty hull attains its diameter, hence its actual diameter
multiplicity is positive. -/
theorem one_le_diameter_multiplicity (H : Finset Plane) (hcard : 2 ≤ H.card) :
    1 ≤ multiplicity H (Metric.diam (H : Set Plane)) := by
  classical
  obtain ⟨a, ha, b, hb, habD⟩ := exists_diameter_pair H
    (Finset.card_pos.mp (by omega : 0 < H.card))
  have hab : a ≠ b := by
    intro heq
    have hpos := diam_pos H hcard
    rw [← habD, heq, dist_self] at hpos
    exact (lt_irrefl 0) hpos
  apply Finset.card_pos.mpr
  exact ⟨s(a, b), Finset.mem_filter.mpr
    ⟨(mk_mem_pairs H a b).mpr ⟨ha, hb, hab⟩, pairDist_mk a b ▸ habD⟩⟩

/-- The requested `k,q,d` hull budget.  Here `k` includes the diameter class,
`q` counts genuinely new nondiameter classes, and `d` is the hull's actual
diameter multiplicity. -/
theorem hull_support_budget (H I : Finset Plane) (hcard : 2 ≤ H.card)
    (hInt : ∀ p ∈ I, p ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ r ∈ nonDiameterDistances (H ∪ I),
      (H ∪ I).card + 1 ≤ multiplicity (H ∪ I) r) :
    let k := (nonDiameterDistances H).card + 1
    let q := (nonDiameterDistances (H ∪ I) \ nonDiameterDistances H).card
    let n := (H ∪ I).card
    let d := multiplicity H (Metric.diam (H : Set Plane))
    (k + q - 1) * (n + 1) + d ≤ n.choose 2 ∧ k + q ≤ n / 2 := by
  classical
  let X := H ∪ I
  let SH := nonDiameterDistances H
  let SX := nonDiameterDistances X
  let k := SH.card + 1
  let q := (SX \ SH).card
  let n := X.card
  let d := multiplicity H (Metric.diam (H : Set Plane))
  change (k + q - 1) * (n + 1) + d ≤ n.choose 2 ∧ k + q ≤ n / 2
  have hdiam : Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) := by
    apply le_antisymm
    · apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      intro x hx y hy
      apply dist_le_diam_hull H
      · rcases Finset.mem_union.mp hx with hxH | hxI
        · exact subset_convexHull ℝ (H : Set Plane) hxH
        · exact interior_subset (hInt x hxI)
      · rcases Finset.mem_union.mp hy with hyH | hyI
        · exact subset_convexHull ℝ (H : Set Plane) hyH
        · exact interior_subset (hInt y hyI)
    · exact Metric.diam_mono (by intro x hx; exact Finset.mem_union_left I hx)
        X.finite_toSet.isBounded
  have hsub : SH ⊆ SX := nonDiameterDistances_mono_of_diam_eq
    (fun x hx => Finset.mem_union_left I hx) hdiam
  have hcardSX : k + q - 1 = SX.card := by
    have hsplit := Finset.card_union_of_disjoint (Finset.disjoint_sdiff :
      Disjoint SH (SX \ SH))
    rw [Finset.union_sdiff_of_subset hsub] at hsplit
    dsimp [k, q]
    omega
  have hdiamMult : multiplicity X (Metric.diam (X : Set Plane)) = d := by
    rw [hdiam]
    exact diameter_multiplicity_union H I hcard hInt
  have hbudget := support_diameter_budget X hlarge
  have hmain : (k + q - 1) * (n + 1) + d ≤ n.choose 2 := by
    simpa only [hcardSX, hdiamMult] using hbudget
  have hdpos : 1 ≤ d := one_le_diameter_multiplicity H hcard
  have hbudgetOne : (k + q - 1) * (n + 1) + 1 ≤ n.choose 2 :=
    (Nat.add_le_add_left hdpos _).trans hmain
  have hchoose : 2 * n.choose 2 ≤ n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  have htwice := (Nat.mul_le_mul_left 2 hbudgetOne).trans hchoose
  have hbound : 2 * (k + q - 1) ≤ n - 2 := by
    by_contra hn
    have hlo : n - 1 ≤ 2 * (k + q - 1) := by omega
    have hmul := Nat.mul_le_mul_right (n + 1) hlo
    nlinarith
  refine ⟨hmain, (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 ?_⟩
  have hkq : 1 ≤ k + q := by
    dsimp [k]
    omega
  have hn2 : 2 ≤ n := by
    dsimp [n, X]
    exact hcard.trans (Finset.card_le_card (fun x hx => Finset.mem_union_left I hx))
  calc
    (k + q) * 2 = 2 * (k + q - 1) + 2 := by omega
    _ ≤ (n - 2) + 2 := Nat.add_le_add_right hbound 2
    _ = n := by omega

/-- An explicit local hull lower bound `m / 2 ≤ k`, when supplied by a
separate convex-distance argument, turns the global support budget into a
bound on genuinely new distance classes. -/
theorem new_classes_le_of_local_lower {m h n k q : ℕ} (hn : n = m + h)
    (hlocal : m / 2 ≤ k) (hglobal : k + q ≤ n / 2) :
    q ≤ n / 2 - m / 2 := by
  omega

/-- Consequences of the conditional new-class bound for one, two, or three
interior points.  These are arithmetic only: the local geometric lower bound
remains an explicit premise. -/
theorem small_interior_new_class_bounds {m h n k q : ℕ} (hn : n = m + h)
    (hlocal : m / 2 ≤ k) (hglobal : k + q ≤ n / 2) :
    (h = 1 → Even m → q = 0) ∧
    (h = 1 → Odd m → q ≤ 1) ∧
    (h = 2 → q ≤ 1) ∧
    (h = 3 → Even m → q ≤ 1) ∧
    (h = 3 → Odd m → q ≤ 2) := by
  have hq := new_classes_le_of_local_lower hn hlocal hglobal
  constructor
  · rintro rfl ⟨a, rfl⟩
    omega
  constructor
  · rintro rfl ⟨a, rfl⟩
    omega
  constructor
  · rintro rfl
    omega
  constructor
  · rintro rfl ⟨a, rfl⟩
    omega
  · rintro rfl ⟨a, rfl⟩
    omega

/-- The geometric hull-deficit inequality, with every term computed from the
actual unordered-pair multiplicities and supports. -/
theorem hull_deficit (H I : Finset Plane) (hdisj : Disjoint H I)
    (_hcard : 2 ≤ H.card)
    (hInt : ∀ p ∈ I, p ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ r ∈ nonDiameterDistances (H ∪ I),
      (H ∪ I).card + 1 ≤ multiplicity (H ∪ I) r) :
    (∑ r ∈ nonDiameterDistances H,
        ((H ∪ I).card + 1 - multiplicity H r)) +
      ((nonDiameterDistances (H ∪ I) \ nonDiameterDistances H).card *
        ((H ∪ I).card + 1)) ≤
      I.card * H.card + I.card.choose 2 := by
  have hdiam : Metric.diam ((H ∪ I : Finset Plane) : Set Plane) =
      Metric.diam (H : Set Plane) := by
    apply le_antisymm
    · apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      intro x hx y hy
      apply dist_le_diam_hull H
      · rcases Finset.mem_union.mp hx with hxH | hxI
        · exact subset_convexHull ℝ (H : Set Plane) hxH
        · exact interior_subset (hInt x hxI)
      · rcases Finset.mem_union.mp hy with hyH | hyI
        · exact subset_convexHull ℝ (H : Set Plane) hyH
        · exact interior_subset (hInt y hyI)
    · exact Metric.diam_mono (by intro x hx; exact Finset.mem_union_left I hx)
        (H ∪ I).finite_toSet.isBounded
  have hbase := deficit_le_pair_difference (A := H) (B := H ∪ I)
    (fun x hx => Finset.mem_union_left I hx) hdiam hlarge
  rwa [choose_union_sub_choose H I hdisj] at hbase

/-- A uniform vertex-distance bound extends strictly to every ambient
interior point.  The comparison point need not lie in the hull. -/
theorem dist_lt_vertex_bound (H : Finset Plane) {p y : Plane} {L : ℝ}
    (hL : 0 < L) (hbound : ∀ h ∈ H, dist h y ≤ L)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) : dist p y < L := by
  have hK : ∀ x ∈ convexHull ℝ (H : Set Plane), dist x y ≤ L := by
    intro x hx
    obtain ⟨h, hh, hle⟩ := convexHull_exists_dist_ge hx y
    exact hle.trans (hbound h hh)
  by_cases hpy : p = y
  · simpa [hpy] using hL
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  let t : ℝ := ε / (2 * (‖p - y‖ + 1))
  have hnorm : 0 ≤ ‖p - y‖ := norm_nonneg _
  have hden : 0 < 2 * (‖p - y‖ + 1) := by positivity
  have ht : 0 < t := div_pos hε hden
  have htε : t * ‖p - y‖ < ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith
  let q := p + t • (p - y)
  have hqp : dist q p = t * ‖p - y‖ := by
    rw [dist_eq_norm]
    dsimp [q]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hq : q ∈ convexHull ℝ (H : Set Plane) :=
    hball (by simpa only [Metric.mem_ball, hqp] using htε)
  have hqy : dist q y = (1 + t) * dist p y := by
    rw [dist_eq_norm, dist_eq_norm]
    have hv : q - y = (1 + t) • (p - y) := by
      dsimp [q]
      module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t)]
  have hpos : 0 < dist p y := dist_pos.mpr hpy
  have hle := hK q hq
  rw [hqy] at hle
  nlinarith

/-- Geometric endpoint certificate for the refined cross-pair count.  If an
interior-to-hull edge has positive length `r`, its hull endpoint belongs to
`H.filter (fun v => ∃ w ∈ H, r < dist v w)`. -/
theorem cross_endpoint_mem_far_filter (H : Finset Plane) {p v : Plane} {r : ℝ}
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) (hv : v ∈ H)
    (hr : 0 < r) (hpv : dist p v = r) :
    v ∈ H.filter (fun x => ∃ w ∈ H, r < dist x w) := by
  apply Finset.mem_filter.mpr
  refine ⟨hv, ?_⟩
  by_contra hnone
  have hbound : ∀ w ∈ H, dist w v ≤ r := by
    intro w hw
    by_contra hle
    apply hnone
    exact ⟨w, hw, by simpa only [dist_comm] using lt_of_not_ge hle⟩
  have hlt := dist_lt_vertex_bound H hr hbound hp
  rw [hpv] at hlt
  exact (lt_irrefl r) hlt

/-- In the even one-interior equality regime, the pair budget saturates:
the hull has a unique diameter pair and every nondiameter class of the enlarged
configuration has multiplicity exactly `n + 1`. -/
theorem even_one_interior_saturation (H I : Finset Plane) (s : ℕ)
    (hdisj : Disjoint H I) (hIcard : I.card = 1) (hs : 5 ≤ s)
    (hXcard : (H ∪ I).card = 2 * s)
    (hk : (nonDiameterDistances H).card + 1 = s)
    (hq : (nonDiameterDistances (H ∪ I) \ nonDiameterDistances H).card = 0)
    (hInt : ∀ p ∈ I, p ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ r ∈ nonDiameterDistances (H ∪ I),
      (H ∪ I).card + 1 ≤ multiplicity (H ∪ I) r) :
    multiplicity H (Metric.diam (H : Set Plane)) = 1 ∧
      ∀ r ∈ nonDiameterDistances (H ∪ I),
        multiplicity (H ∪ I) r = (H ∪ I).card + 1 := by
  classical
  let X := H ∪ I
  let SH := nonDiameterDistances H
  let SX := nonDiameterDistances X
  have hHcardEq : H.card = 2 * s - 1 := by
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hIcard, hXcard] at hu
    omega
  have hHcard : 2 ≤ H.card := by omega
  have hdiam : Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) := by
    apply le_antisymm
    · apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      intro x hx y hy
      apply dist_le_diam_hull H
      · rcases Finset.mem_union.mp hx with hxH | hxI
        · exact subset_convexHull ℝ (H : Set Plane) hxH
        · exact interior_subset (hInt x hxI)
      · rcases Finset.mem_union.mp hy with hyH | hyI
        · exact subset_convexHull ℝ (H : Set Plane) hyH
        · exact interior_subset (hInt y hyI)
    · exact Metric.diam_mono (by intro x hx; exact Finset.mem_union_left I hx)
        X.finite_toSet.isBounded
  have hsub : SH ⊆ SX := nonDiameterDistances_mono_of_diam_eq
    (fun x hx => Finset.mem_union_left I hx) hdiam
  have hSXcard : SX.card = s - 1 := by
    have hsplit := Finset.card_union_of_disjoint (Finset.disjoint_sdiff :
      Disjoint SH (SX \ SH))
    rw [Finset.union_sdiff_of_subset hsub] at hsplit
    dsimp [X, SH, SX] at hsplit hq hk ⊢
    omega
  have hlower : X.card - 2 ≤ 2 * SX.card := by
    rw [hXcard, hSXcard]
    omega
  obtain ⟨_heven, _hthree, hsaturated, _hunique⟩ :=
    equality_structure X (by dsimp [X]; omega) hlower hlarge
  have hbudget := (hull_support_budget H I hHcard hInt hlarge).1
  have hdiamPos := one_le_diameter_multiplicity H hHcard
  have hchoose : (2 * s).choose 2 = (s - 1) * (2 * s + 1) + 1 := by
    apply choose_even_equality
    omega
  have hsminus : s + 0 - 1 = s - 1 := by omega
  have hdiamOne : multiplicity H (Metric.diam (H : Set Plane)) = 1 := by
    rw [hk, hq, hXcard, hsminus, hchoose] at hbudget
    omega
  exact ⟨hdiamOne, hsaturated⟩

/-- The hull/interior geometric hypotheses have a concrete joint model; this
checks that the accounting theorem is not based on contradictory geometry. -/
example : ∃ (H I : Finset Plane), Disjoint H I ∧ 2 ≤ H.card ∧
    ∀ p ∈ I, p ∈ interior (convexHull ℝ (H : Set Plane)) := by
  obtain ⟨H, u, _v, hcard, hcircle, _hext, hu, _hv, _huv⟩ := rational_circle_fixture
  have huH : u ∉ H := by
    intro huMem
    have huR := dist_center_lt_radius H 0 (by norm_num) hcircle hu
    exact (ne_of_lt huR) (hcircle u huMem)
  refine ⟨H, {u}, by simpa [Finset.disjoint_singleton_right], by omega, ?_⟩
  intro p hp
  have hpu : p = u := Finset.mem_singleton.mp hp
  simpa only [hpu] using hu

end Erdos132.HullDeficit
