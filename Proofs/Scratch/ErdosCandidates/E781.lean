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

/-- Ground truth: an arithmetic progression is a descending wave
    (equal gaps), e.g. `1, 3, 5`.  -- PROVABLE (decide). -/
example : IsDescendingWave (fun i : Fin 3 => 2 * (i : ℕ) + 1) := by
  sorry

/-- Non-degeneracy: increasing gaps fail — `1, 2, 4` is not a
    descending wave (4 + 1 > 2·2).  -- PROVABLE (decide). -/
example : ¬ IsDescendingWave (![1, 2, 4] : Fin 3 → ℕ) := by
  sorry

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

/-- Sanity: `f(2) = 3` — two elements always form a descending wave
    (no interior condition), so this is pigeonhole on 3 points; and the
    coloring `1 ↦ tt, 2 ↦ ff` shows 2 does not suffice.
    -- PROVABLE (decide after an sInf-characterization lemma). -/
theorem fDW_two : fDW 2 = 3 := by
  sorry

/-- Sanity at the conjectured value for `k = 3`: `f(3) = 7 = 3²−3+1`.
    -- PROVABLE (native_decide scale: 2^7 colorings × wave search). -/
theorem fDW_three : fDW 3 = 7 := by
  sorry

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
