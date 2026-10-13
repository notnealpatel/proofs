/-
  Erdős Problem #781 — monochromatic descending waves.
  Status: disproved (Alon–Spencer 1989).  Tier B archive target with a
  certificate probe.

  Verbatim statement (`goof erdos fetch 781`, pulled 2026-08-05):

    "Let $f(k)$ be the minimal $n$ such that any $2$-colouring of
    $\{1,\ldots,n\}$ contains a monochromatic $k$-term descending wave:
    a sequence $x_1<\cdots <x_k$ such that, for $1<j<k$,
    \[x_j \geq \frac{x_{j+1}+x_{j-1}}{2}.\]
    Estimate $f(k)$. In particular is it true that $f(k)=k^2-k+1$ for
    all $k$?"

  DB remarks: Brown–Erdős–Freedman [BEF90] proved
  k²−k+1 ≤ f(k) ≤ (k³−4k+9)/3.  Alon–Spencer [AlSp89] resolved the
  particular question: f(k) ≫ k³, so equality FAILS for large k.

  ⚠ Residual uncertainty (candidates doc): the first failing k is not
  documented — Alon–Spencer is asymptotic, so small k may still satisfy
  equality.  Probe with sage before committing to a certificate
  theorem; k = 4 needs 2^13 colorings, k = 5 needs 2^21 — both
  native_decide range.

  Formalization notes: x_j ≥ (x_{j+1} + x_{j−1})/2 ⟺ gaps are
  non-increasing: x_{j+1} − x_j ≤ x_j − x_{j−1}.  We encode the gap
  form (no division, no ℕ-subtraction junk: additively).

  Mathlib inventory (leandoc 2026-08-05): plain `Fin k → ℕ`,
  `StrictMono`; nothing else needed.  Van der Waerden machinery is in
  Mathlib (`Combinatorics.Schnirelmann`? — vdW is
  `exists_mono_homothetic_copy` / Hales–Jewett in
  Mathlib.Combinatorics.HalesJewett) but not needed for the statement.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E781

/-- `IsDescendingWave x`: `x 0 < x 1 < ⋯` with non-increasing gaps —
    `x (j+1) + x (j-1) ≤ 2 * x j` for interior `j`, stated additively as
    `x (j+2) + x j ≤ 2 * x (j+1)` over `j + 2 < k`. -/
def IsDescendingWave {k : ℕ} (x : Fin k → ℕ) : Prop :=
  StrictMono x ∧
    ∀ j : ℕ, ∀ h : j + 2 < k,
      x ⟨j + 2, h⟩ + x ⟨j, by omega⟩ ≤ 2 * x ⟨j + 1, by omega⟩

/-- The positive three-term arithmetic progression 1, 3, 5 is a wave. -/
theorem arithmetic_progression_wave : IsDescendingWave (fun i : Fin 3 => 2 * (i : ℕ) + 1) := by
  constructor
  · intro i j hij
    change 2 * i.val + 1 < 2 * j.val + 1
    have hv : i.val < j.val := hij
    omega
  · intro j hj
    change 2 * (j + 2) + 1 + (2 * j + 1) ≤ 2 * (2 * (j + 1) + 1)
    omega

/-- Ground truth: an arithmetic progression is a descending wave
    (equal gaps), e.g. `1, 3, 5`.  -- PROVABLE (decide). -/
example : IsDescendingWave (fun i : Fin 3 => 2 * (i : ℕ) + 1) :=
  arithmetic_progression_wave

/-- The increasing triple 1, 2, 4 fails the sole interior wave inequality. -/
theorem increasing_gaps_not_wave : ¬ IsDescendingWave (![1, 2, 4] : Fin 3 → ℕ) := by
  intro h
  have hi := h.2 0 (by decide)
  norm_num at hi

/-- Non-degeneracy: increasing gaps fail — `1, 2, 4` is not a
    descending wave (4 + 1 > 2·2).  -- PROVABLE (decide). -/
example : ¬ IsDescendingWave (![1, 2, 4] : Fin 3 → ℕ) :=
  increasing_gaps_not_wave

/-- `HasMonoDW n k`: every 2-coloring of `{1, …, n}` admits a
    monochromatic `k`-term descending wave inside `[1, n]`. -/
def HasMonoDW (n k : ℕ) : Prop :=
  ∀ c : ℕ → Bool, ∃ x : Fin k → ℕ,
    IsDescendingWave x ∧ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧
    ∃ b : Bool, ∀ i, c (x i) = b

/-- `fDW k`: the minimal such `n` — the `f(k)` of the problem.  The
    defining set is nonempty for `k ≥ 1` by BEF's upper bound, so
    `sInf` is honest. -/
noncomputable def fDW (k : ℕ) : ℕ := sInf {n : ℕ | HasMonoDW n k}

/-- Two increasing terms have no interior wave constraint. -/
theorem pair_wave (a b : ℕ) (hab : a < b) :
    IsDescendingWave (![a, b] : Fin 2 → ℕ) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j hj
    omega

/-- Three increasing terms are a wave when the sole interior inequality holds. -/
theorem triple_wave (a b d : ℕ) (hab : a < b) (hbd : b < d)
    (hd : d + a ≤ 2 * b) : IsDescendingWave (![a, b, d] : Fin 3 → ℕ) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using hd

/-- An increasing monochromatic pair in the interval supplies the two-term witness. -/
theorem mono_pair (c : ℕ → Bool) (n a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ n)
    (hab : a < b) (hc : c a = c b) :
    ∃ x : Fin 2 → ℕ, IsDescendingWave x ∧ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧
      ∃ color : Bool, ∀ i, c (x i) = color := by
  refine ⟨![a,b], pair_wave a b hab, ?_, c a, ?_⟩
  · intro i
    fin_cases i
    · change 1 ≤ a ∧ a ≤ n
      omega
    · change 1 ≤ b ∧ b ≤ n
      omega
  · intro i
    fin_cases i <;> simp_all

/-- Three points force a same-colored pair. -/
theorem hasMonoDW_two_upper : HasMonoDW 3 2 := by
  intro c
  by_cases h12 : c 1 = c 2
  · exact mono_pair c 3 1 2 (by decide) (by decide) (by decide) h12
  by_cases h13 : c 1 = c 3
  · exact mono_pair c 3 1 3 (by decide) (by decide) (by decide) h13
  have h23 : c 2 = c 3 := by
    cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;> simp_all
  exact mono_pair c 3 2 3 (by decide) (by decide) (by decide) h23

/-- Coloring only 2 true excludes every two-term witness below 3, including 0 and 1. -/
theorem not_hasMonoDW_two (n : ℕ) (hn : n < 3) : ¬ HasMonoDW n 2 := by
  intro h
  obtain ⟨x, hw, hx, b, hc⟩ := h (fun t => decide (t = 2))
  have h01 : x 0 < x 1 := hw.1 (by decide)
  have hx0 := hx 0
  have hx1 := hx 1
  have he0 : x 0 = 1 := by omega
  have he1 : x 1 = 2 := by omega
  have hc0 := hc 0
  have hc1 := hc 1
  simp [he0, he1] at hc0 hc1
  cases b <;> simp_all

/-- An increasing monochromatic triple with the interior inequality supplies a witness. -/
theorem mono_triple (c : ℕ → Bool) (n a b d : ℕ)
    (ha : 1 ≤ a) (hdn : d ≤ n) (hab : a < b) (hbd : b < d)
    (hd : d + a ≤ 2 * b) (hcab : c a = c b) (hcad : c a = c d) :
    ∃ x : Fin 3 → ℕ, IsDescendingWave x ∧ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧
      ∃ color : Bool, ∀ i, c (x i) = color := by
  refine ⟨![a,b,d], triple_wave a b d hab hbd hd, ?_, c a, ?_⟩
  · intro i
    fin_cases i
    · change 1 ≤ a ∧ a ≤ n
      omega
    · change 1 ≤ b ∧ b ≤ n
      omega
    · change 1 ≤ d ∧ d ≤ n
      omega
  · intro i
    fin_cases i <;> simp_all

/-- Four same-colored increasing points in 1 through 7 contain a descending triple. -/
theorem four_points (c : ℕ → Bool) (w x y z : ℕ)
    (hw : 1 ≤ w) (hz : z ≤ 7) (hwx : w < x) (hxy : x < y) (hyz : y < z)
    (hx : c w = c x) (hy : c w = c y) (hc : c w = c z) :
    ∃ t : Fin 3 → ℕ, IsDescendingWave t ∧ (∀ i, 1 ≤ t i ∧ t i ≤ 7) ∧
      ∃ color : Bool, ∀ i, c (t i) = color := by
  by_cases h : y + w ≤ 2 * x
  · exact mono_triple c 7 w x y hw (by omega) hwx hxy h hx hy
  have h' : z + w ≤ 2 * y := by omega
  exact mono_triple c 7 w y z hw hz (by omega) hyz h' hy hc

/-- Seven points have a color class of size at least four, hence a descending triple. -/
theorem hasMonoDW_three_upper : HasMonoDW 7 3 := by
  intro c
  classical
  let s := (Finset.Icc 1 7).filter (fun t => c t = false)
  let t := (Finset.Icc 1 7).filter (fun t => ¬ c t = false)
  have hsum : s.card + t.card = 7 := by
    simpa [s, t] using (Finset.Icc 1 7).card_filter_add_card_filter_not
      (fun t => c t = false)
  have hbig : ∃ b : Bool, 4 ≤ ((Finset.Icc 1 7).filter (fun t => c t = b)).card := by
    by_cases hs : 4 ≤ s.card
    · exact ⟨false, hs⟩
    · refine ⟨true, ?_⟩
      have ht : 4 ≤ t.card := by omega
      simpa [t, Bool.not_eq_false] using ht
  obtain ⟨b, hb⟩ := hbig
  obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq hb
  let e := u.orderEmbOfFin hcard
  have hem (i : Fin 4) : 1 ≤ e i ∧ e i ≤ 7 ∧ c (e i) = b := by
    have hi := hu (u.orderEmbOfFin_mem hcard i)
    simpa only [Finset.mem_filter, Finset.mem_Icc, and_assoc] using hi
  have h01 : e 0 < e 1 := e.strictMono (by decide)
  have h12 : e 1 < e 2 := e.strictMono (by decide)
  have h23 : e 2 < e 3 := e.strictMono (by decide)
  exact four_points c (e 0) (e 1) (e 2) (e 3) (hem 0).1 (hem 3).2.1
    h01 h12 h23 ((hem 0).2.2.trans (hem 1).2.2.symm)
    ((hem 0).2.2.trans (hem 2).2.2.symm) ((hem 0).2.2.trans (hem 3).2.2.symm)

/-- The true class {3,4,6} and false class {1,2,5} exclude descending triples below 7. -/
theorem not_hasMonoDW_three (n : ℕ) (hn : n < 7) : ¬ HasMonoDW n 3 := by
  intro h
  obtain ⟨x, hw, hx, b, hc⟩ := h (fun t => decide (t ∈ ({3,4,6} : Finset ℕ)))
  have h01 : x 0 < x 1 := hw.1 (by decide)
  have h12 : x 1 < x 2 := hw.1 (by decide)
  have hineq : x 2 + x 0 ≤ 2 * x 1 := hw.2 0 (by decide)
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  cases b <;> simp only [decide_eq_false_iff_not, decide_eq_true_eq,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hc0 hc1 hc2 <;> omega

-- Concrete joint models for the helper hypotheses, with nonempty Fin domains.
example : IsDescendingWave (![1, 2] : Fin 2 → ℕ) :=
  pair_wave 1 2 (by decide)
example : IsDescendingWave (![1, 2, 3] : Fin 3 → ℕ) :=
  triple_wave 1 2 3 (by decide) (by decide) (by decide)
example : ∃ x : Fin 2 → ℕ, IsDescendingWave x ∧
    (∀ i, 1 ≤ x i ∧ x i ≤ 3) ∧ ∃ b : Bool, ∀ i, (fun _ : ℕ => false) (x i) = b :=
  mono_pair (fun _ => false) 3 1 2 (by decide) (by decide) (by decide) rfl
example : ∃ x : Fin 3 → ℕ, IsDescendingWave x ∧
    (∀ i, 1 ≤ x i ∧ x i ≤ 7) ∧ ∃ b : Bool, ∀ i, (fun _ : ℕ => false) (x i) = b :=
  mono_triple (fun _ => false) 7 1 2 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl rfl
example : ∃ x : Fin 3 → ℕ, IsDescendingWave x ∧
    (∀ i, 1 ≤ x i ∧ x i ≤ 7) ∧ ∃ b : Bool, ∀ i, (fun _ : ℕ => false) (x i) = b :=
  four_points (fun _ => false) 1 2 3 4 (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl rfl rfl
example : ¬ HasMonoDW 2 2 := not_hasMonoDW_two 2 (by decide)
example : ¬ HasMonoDW 6 3 := not_hasMonoDW_three 6 (by decide)
example : HasMonoDW 3 2 := hasMonoDW_two_upper
example : HasMonoDW 7 3 := hasMonoDW_three_upper

/-- Sanity: `f(2) = 3` — two elements always form a descending wave
    (no interior condition), so this is pigeonhole on 3 points; and the
    coloring `1 ↦ tt, 2 ↦ ff` shows 2 does not suffice.
    -- PROVABLE (decide after an sInf-characterization lemma). -/
theorem fDW_two : fDW 2 = 3 := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le hasMonoDW_two_upper
  · have hm : HasMonoDW (fDW 2) 2 := Nat.sInf_mem (s := {n | HasMonoDW n 2}) ⟨3, hasMonoDW_two_upper⟩
    by_contra h
    exact not_hasMonoDW_two (fDW 2) (by omega) hm

/-- Sanity at the conjectured value for `k = 3`: `f(3) = 7 = 3²−3+1`.
    -- PROVABLE (native_decide scale: 2^7 colorings × wave search). -/
theorem fDW_three : fDW 3 = 7 := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le hasMonoDW_three_upper
  · have hm : HasMonoDW (fDW 3) 3 := Nat.sInf_mem (s := {n | HasMonoDW n 3}) ⟨7, hasMonoDW_three_upper⟩
    by_contra h
    exact not_hasMonoDW_three (fDW 3) (by omega) hm

/-- **BEF lower bound** (BEF90): `k² − k + 1 ≤ f(k)`.  Stated
    additively to dodge ℕ-subtraction: `k² + 1 ≤ f(k) + k`.
    The witness coloring is explicit in BEF90 — a blockwise coloring
    with block lengths 1, 1, 2, 3, … avoiding long monochromatic waves;
    a genuine finite-combinatorics target. -/
theorem bef_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    k ^ 2 + 1 ≤ fDW k + k := by
  sorry

/-- **BEF upper bound** (BEF90): `f(k) ≤ (k³ − 4k + 9)/3`, stated
    multiplicatively: `3 * f(k) + 4 * k ≤ k³ + 9`. -/
theorem bef_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    3 * fDW k + 4 * k ≤ k ^ 3 + 9 := by
  sorry

/-- **Erdős #781, Alon–Spencer resolution** (AlSp89): `f(k) ≫ k³`; in
    particular `f(k) = k² − k + 1` fails for all large `k` — the
    "in particular" question is answered NO.  Archived. -/
theorem alon_spencer :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      c * (k : ℝ) ^ 3 ≤ (fDW k : ℝ) := by
  sorry

/-- Corollary shape of the disproof — the equality claim fails at some
    explicit k (which one is undocumented; probe before proving:
    check k = 4 via 2^13-coloring sweep whether f(4) = 13).
    -- PROVABLE-in-principle (native_decide after the probe pins k). -/
theorem equality_fails : ∃ k : ℕ, 2 ≤ k ∧ fDW k + k ≠ k ^ 2 + 1 := by
  sorry

end ErdosCandidates.E781

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches source verbatim. BEF90 bounds and Alon-Spencer resolution match.
   - Descending-wave condition x_j >= (x_{j+1}+x_{j-1})/2 correctly re-encoded as
     x(j+2)+x(j) <= 2*x(j+1), avoiding division and NAT-subtraction. Equivalent to
     non-increasing gaps.
   - f(2)=3: correct; k=2 descending wave has no interior condition, so it is
     pigeonhole on 3 points.
   - BEF lower bound k^2+1 <= fDW k + k correctly encodes k^2-k+1 <= f(k).
   - BEF upper bound 3*fDW k + 4*k <= k^3+9 correctly encodes f(k) <= (k^3-4k+9)/3.
   - equality_fails correctly encodes fDW k != k^2-k+1.
   - Alon-Spencer asymptotic stated as existential constant, honest about threshold K.
   - Source has no comments; no comment-sourced claims to flag.
-/
