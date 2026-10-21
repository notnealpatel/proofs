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

/-- Block sizes of the BEF colouring: `k - 1 - ⌊i/2⌋`, floored at `1`. -/
private def bsize (k i : ℕ) : ℕ := max (k - 1 - i / 2) 1

/-- Start (0-based) of block `j`. -/
private def bstart (k j : ℕ) : ℕ := ∑ i ∈ Finset.range j, bsize k i

/-- Each block starts where the previous one ends. -/
private lemma bstart_succ (k j : ℕ) : bstart k (j + 1) = bstart k j + bsize k j :=
  Finset.sum_range_succ _ _

/-- Block `0` starts at position `0`. -/
private lemma bstart_zero (k : ℕ) : bstart k 0 = 0 := Finset.sum_range_zero _

/-- Block starts strictly increase, since every block is nonempty. -/
private lemma bstart_strictMono (k : ℕ) : StrictMono (bstart k) :=
  strictMono_nat_of_lt_succ fun j => by
    rw [bstart_succ]
    have h1 : 1 ≤ bsize k j := le_max_right _ _
    omega

/-- Every position lies before the end of some block. -/
private lemma bstart_exists (k q : ℕ) : ∃ j, q < bstart k (j + 1) :=
  ⟨q, by
    have h : q + 1 ≤ bstart k (q + 1) := (bstart_strictMono k).id_le (q + 1)
    omega⟩

/-- Block index of 0-based position `q`. -/
private def blk (k q : ℕ) : ℕ := Nat.find (bstart_exists k q)

/-- Position `q` lies in block `blk k q`. -/
private lemma blk_spec (k q : ℕ) : bstart k (blk k q) ≤ q ∧ q < bstart k (blk k q + 1) := by
  refine ⟨?_, Nat.find_spec (bstart_exists k q)⟩
  rcases h : blk k q with _ | j
  · simp [bstart_zero]
  · have hlt : j < blk k q := by omega
    have hmin := Nat.find_min (bstart_exists k q) hlt
    omega

/-- Block index is monotone in the position. -/
private lemma blk_mono (k : ℕ) {p q : ℕ} (hpq : p ≤ q) : blk k p ≤ blk k q := by
  have hp := blk_spec k p
  have hq := blk_spec k q
  have h : bstart k (blk k p) < bstart k (blk k q + 1) := by omega
  have := (bstart_strictMono k).lt_iff_lt.mp h
  omega

/-- Two positions in one block differ by less than the block size. -/
private lemma same_blk (k : ℕ) {p q : ℕ} (h : blk k p = blk k q) : q < p + bsize k (blk k p) := by
  have hp := blk_spec k p
  have hq := blk_spec k q
  rw [bstart_succ] at hq
  rw [← h] at hq
  omega

/-- Consecutive block sizes drop by at most one. -/
private lemma bsize_le_succ (k j : ℕ) : bsize k j ≤ bsize k (j + 1) + 1 := by
  unfold bsize
  omega

/-- Jumping at least two blocks ahead moves by at least the size of the starting block. -/
private lemma far_blk (k : ℕ) {p q : ℕ} (h : blk k p + 2 ≤ blk k q) : p + bsize k (blk k p) ≤ q := by
  have hp := blk_spec k p
  have hq := blk_spec k q
  have hmono : bstart k (blk k p + 2) ≤ bstart k (blk k q) := (bstart_strictMono k).monotone h
  rw [bstart_succ, bstart_succ] at hmono
  rw [bstart_succ] at hp
  have := bsize_le_succ k (blk k p)
  omega

/-- Closed form: the first `2m` blocks occupy `2mk - m(m+1)` positions, for `m < k`. -/
private lemma bstart_even (k : ℕ) : ∀ m, m + 1 ≤ k → bstart k (2 * m) + m * (m + 1) = 2 * m * k := by
  intro m
  induction m with
  | zero => intro _; simp [bstart_zero]
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, bstart_succ, bstart_succ]
    have h1 : bsize k (2 * m) = k - 1 - m := by unfold bsize; omega
    have h2 : bsize k (2 * m + 1) = k - 1 - m := by unfold bsize; omega
    rw [h1, h2]
    have e1 : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
    have e2 : (2 * m + 1 + 1) * k = 2 * m * k + 2 * k := by ring
    rw [e1, e2]
    omega

/-- Positions below `k² - k` lie in blocks of index at most `2k - 3`. -/
private lemma blk_lt (k q : ℕ) (hk : 1 ≤ k) (hq : q + 1 + k ≤ k ^ 2) : blk k q + 3 ≤ 2 * k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc := bstart_even (k' + 1) k' (by omega)
  have hsq : (k' + 1) ^ 2 = k' * (k' + 1) + (k' + 1) := by ring
  have h2 : 2 * k' * (k' + 1) = k' * (k' + 1) + k' * (k' + 1) := by ring
  by_contra hcon
  have hge : 2 * k' ≤ blk (k' + 1) q := by omega
  have hmono := (bstart_strictMono (k' + 1)).monotone hge
  have hs := (blk_spec (k' + 1) q).1
  omega

/-- The BEF colouring of 1-based position `p`: parity of its block. -/
private def col (k p : ℕ) : Bool := decide (blk k (p - 1) % 2 = 0)

/-- The BEF colouring of `[1, k² - k]` has no monochromatic `k`-term descending wave,
    stated for a wave listed as `y 0, …, y (k-1)`. -/
private lemma no_wave (k : ℕ) (hk : 2 ≤ k) (y : ℕ → ℕ) (b : Bool)
    (hmono : ∀ t, t + 1 < k → y t < y (t + 1))
    (hwave : ∀ t, t + 2 < k → y (t + 2) + y t ≤ 2 * y (t + 1))
    (hrange : ∀ t, t < k → 1 ≤ y t ∧ y t + k ≤ k ^ 2)
    (hcol : ∀ t, t < k → col k (y t) = b) : False := by
  set B : ℕ → ℕ := fun t => blk k (y t - 1) with hB
  have hpar : ∀ t, t < k → B t % 2 = B 0 % 2 := by
    intro t ht
    have h1 := hcol t ht
    have h0 := hcol 0 (by omega)
    simp only [col] at h1 h0
    rw [← h0] at h1
    simp only [hB]
    by_cases hz : blk k (y 0 - 1) % 2 = 0
    · simp only [hz, decide_true, decide_eq_true_eq] at h1
      omega
    · simp only [hz, decide_false, decide_eq_false_iff_not] at h1
      omega
  have hBmono : ∀ t, t + 1 < k → B t ≤ B (t + 1) := by
    intro t ht
    have := hmono t ht
    exact blk_mono k (by omega)
  have hgap : ∀ t u, t ≤ u → u + 1 < k → y (u + 1) + y t ≤ y (t + 1) + y u := by
    intro t u htu
    induction u, htu using Nat.le_induction with
    | base => intro _; omega
    | succ u htu ih =>
      intro hu
      have h1 := ih (by omega)
      have h2 : y (u + 1 + 1) + y u ≤ 2 * y (u + 1) := hwave u (by omega)
      omega
  have hstuck : ∀ t, t + 1 < k → B t = B (t + 1) → ∀ u, t ≤ u → u < k → B u = B t := by
    intro t ht hsame u htu
    induction u, htu using Nat.le_induction with
    | base => intro _; rfl
    | succ u htu ih =>
      intro hu
      have hBu := ih (by omega)
      have hle := hBmono u hu
      by_contra hne
      have hp1 := hpar u (by omega)
      have hp2 := hpar (u + 1) hu
      have hfar : B u + 2 ≤ B (u + 1) := by omega
      have hf := far_blk k hfar
      have hs := same_blk k hsame
      have hg := hgap t u htu hu
      have hyu := hrange u (by omega)
      have hyt := hrange t (by omega)
      have hyt1 := hrange (t + 1) ht
      have hyu1 := hrange (u + 1) hu
      simp only [hB] at hf hs hBu
      rw [hBu] at hf
      omega
  have hinc : ∀ s u, s ≤ u → u < k → y s + (u - s) ≤ y u := by
    intro s u hsu
    induction u, hsu using Nat.le_induction with
    | base => intro _; omega
    | succ u hsu ih =>
      intro hu
      have h1 := ih (by omega)
      have h2 := hmono u hu
      omega
  have hclaim : ∀ t, t < k → 2 * t ≤ B t ∨ ∃ s, s ≤ t ∧ 2 * s ≤ B s ∧ B s = B (k - 1) := by
    intro t
    induction t with
    | zero => intro _; left; omega
    | succ t ih =>
      intro ht
      rcases ih (by omega) with hl | ⟨s, hst, h2s, hsJ⟩
      · by_cases heq : B t = B (t + 1)
        · right
          exact ⟨t, by omega, hl, (hstuck t ht heq (k - 1) (by omega) (by omega)).symm⟩
        · left
          have hle := hBmono t ht
          have hp1 := hpar t (by omega)
          have hp2 := hpar (t + 1) ht
          omega
      · right
        exact ⟨s, by omega, h2s, hsJ⟩
  have hJ : B (k - 1) + 3 ≤ 2 * k := by
    have hr := hrange (k - 1) (by omega)
    exact blk_lt k (y (k - 1) - 1) (by omega) (by omega)
  rcases hclaim (k - 1) (by omega) with hl | ⟨s, hsk, h2s, hsJ⟩
  · omega
  · have hs := same_blk k (p := y s - 1) (q := y (k - 1) - 1) hsJ
    have hi := hinc s (k - 1) hsk (by omega)
    have hys := hrange s (by omega)
    have hyk := hrange (k - 1) (by omega)
    have hbs : bsize k (B s) ≤ k - 1 - s := by
      simp only [bsize]
      omega
    simp only [hB] at hbs h2s hsJ
    omega

/-- Coordinates of a combinatorial line are either constant or the line parameter. -/
private lemma line_coord {k : ℕ} {ι : Type} (l : Combinatorics.Line (Fin k) ι) (i : ι) :
    (∀ x : Fin k, l x i = x) ∨ ∃ a : Fin k, ∀ x : Fin k, l x i = a := by
  rcases h : l.idxFun i with _ | a
  · left; intro x; exact l.apply_none x i h
  · right; exact ⟨a, fun x => Combinatorics.Line.apply_some h⟩

/-- Finite van der Waerden for descending waves, via Hales–Jewett. -/
private lemma exists_hasMonoDW (k : ℕ) : ∃ n, HasMonoDW n k := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  refine ⟨1 + Fintype.card ι * (k - 1), fun c => ?_⟩
  obtain ⟨l, b, hl⟩ := hι fun v => c (1 + ∑ i, ((v i : Fin k) : ℕ))
  let x : Fin k → ℕ := fun t => 1 + ∑ i, ((l t i : Fin k) : ℕ)
  refine ⟨x, ⟨?_, ?_⟩, ?_, b, fun t => hl t⟩
  · intro t t' htt'
    simp only [x]
    have hsum : ∑ i, ((l t i : Fin k) : ℕ) < ∑ i, ((l t' i : Fin k) : ℕ) := by
      apply Finset.sum_lt_sum
      · intro i _
        rcases line_coord l i with h | ⟨a, h⟩
        · rw [h, h]; exact le_of_lt htt'
        · rw [h, h]
      · obtain ⟨i, hi⟩ := l.proper
        refine ⟨i, Finset.mem_univ _, ?_⟩
        rw [l.apply_none t i hi, l.apply_none t' i hi]
        exact htt'
    omega
  · intro j hj
    simp only [x]
    have hsum : ∑ i, ((l ⟨j + 2, hj⟩ i : Fin k) : ℕ) + ∑ i, ((l ⟨j, by omega⟩ i : Fin k) : ℕ)
        = 2 * ∑ i, ((l ⟨j + 1, by omega⟩ i : Fin k) : ℕ) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rcases line_coord l i with h | ⟨a, h⟩
      · rw [h, h, h]; simp only; omega
      · rw [h, h, h]; omega
    omega
  · intro t
    refine ⟨by simp [x], ?_⟩
    simp only [x]
    have hle : ∑ i, ((l t i : Fin k) : ℕ) ≤ ∑ _i : ι, (k - 1) := by
      apply Finset.sum_le_sum
      intro i _
      have := (l t i).isLt
      omega
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    omega

/-- **BEF lower bound** (BEF90): `k² − k + 1 ≤ f(k)`.  Stated
    additively to dodge ℕ-subtraction: `k² + 1 ≤ f(k) + k`.
    The witness coloring is explicit in BEF90 — a blockwise coloring
    with block lengths 1, 1, 2, 3, … avoiding long monochromatic waves;
    a genuine finite-combinatorics target. -/
theorem bef_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    k ^ 2 + 1 ≤ fDW k + k := by
  obtain ⟨N, hN⟩ := exists_hasMonoDW k
  have hm : HasMonoDW (fDW k) k := Nat.sInf_mem (s := {n | HasMonoDW n k}) ⟨N, hN⟩
  by_contra hlt
  obtain ⟨x, ⟨hxm, hxw⟩, hxr, b, hxc⟩ := hm (col k)
  let y : ℕ → ℕ := fun t => if h : t < k then x ⟨t, h⟩ else 0
  have hy : ∀ t (h : t < k), y t = x ⟨t, h⟩ := fun t h => dif_pos h
  apply no_wave k hk y b
  · intro t ht
    rw [hy t (by omega), hy (t + 1) ht]
    exact hxm (Fin.mk_lt_mk.mpr (Nat.lt_succ_self t))
  · intro t ht
    rw [hy t (by omega), hy (t + 1) (by omega), hy (t + 2) ht]
    exact hxw t ht
  · intro t ht
    rw [hy t ht]
    have hr := hxr ⟨t, ht⟩
    omega
  · intro t ht
    rw [hy t ht]
    exact hxc _

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
