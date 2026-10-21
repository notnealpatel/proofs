/-
  Erdős Problem #849 — Singmaster-type multiplicities in Pascal's
  triangle.
  Status: open.  Tier UC lemma mine (exact multiplicity of 120 and
  3003 are clean finite theorems).

  Verbatim statement (`goof erdos fetch 849`, pulled 2026-08-05):

    "Is it true that, for every integer $t\geq 1$, there is some
    integer $a$ such that\[\binom{n}{k}=a\](with $1\leq k\leq n/2$)
    has exactly $t$ solutions?"

  DB remarks: Erdős [Er96b] credits Erdős–Gordon; commonly known as
  (adjacent to) Singmaster's conjecture.  t = 3 at a = 120; t = 4 at
  a = 3003.  Nothing known for t ≥ 5.  Erdős and Singmaster both
  believed the answer is NO — an absolute bound on multiplicities.
  Matomäki–Radziwiłł–Shao–Tao–Teräväinen [MRSTT22]: at most two
  solutions when k ≥ exp((log n)^{2/3+ε}) and a large.

  OEIS anchors: A003016 (occurrences of n in Pascal's triangle),
  A003015 (numbers occurring ≥ 5 times), A059233 and others.

  Mathlib inventory: `Nat.choose`; multiplicity as `Set.ncard` of the
  solution set (finite: `C(n,k) ≥ n` for `1 ≤ k ≤ n/2`… C(n,1) = n,
  and C(n,k) is ≥ n for 1 ≤ k ≤ n−1, so solutions have `n ≤ a` —
  bounded search). -/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E849

/-- The solution set of `C(n,k) = a` in the half-triangle
    `1 ≤ k ≤ n/2` (encoded `2k ≤ n`). -/
def solutions (a : ℕ) : Set (ℕ × ℕ) :=
  {q : ℕ × ℕ | 1 ≤ q.2 ∧ 2 * q.2 ≤ q.1 ∧ q.1.choose q.2 = a}

/-- `multiplicity a`: the number of half-triangle representations. -/
noncomputable def multiplicity (a : ℕ) : ℕ := (solutions a).ncard

/-- Binomial monotonicity on the left half: for `j ≤ k` and `2k ≤ n`,
    `C(n,j) ≤ C(n,k)`. -/
private theorem choose_le_choose_of_le_of_two_mul_le {n j k : ℕ} (hjk : j ≤ k)
    (hk : 2 * k ≤ n) : n.choose j ≤ n.choose k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    have hlt : k < n / 2 := by omega
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left hlt)

/-- Every half-triangle solution `(n,k)` of `C(n,k) = a` has `n ≤ a`
    and `k ≤ a`. -/
private theorem le_of_mem_solutions {a : ℕ} {q : ℕ × ℕ} (hq : q ∈ solutions a) :
    q.1 ≤ a ∧ q.2 ≤ a := by
  obtain ⟨hk1, hkn, hchoose⟩ := hq
  have hn : q.1 ≤ a := by
    have hmono := choose_le_choose_of_le_of_two_mul_le hk1 hkn
    rw [Nat.choose_one_right, hchoose] at hmono
    exact hmono
  exact ⟨hn, by omega⟩

/-- Finiteness engine: for `a ≥ 2` every solution has `n ≤ a` (since
    `C(n,k) ≥ n` for `1 ≤ k ≤ n/2` via `C(n,1) = n ≤ C(n,k)` and
    binomial monotonicity in k up to n/2), so the solution set is
    finite and `ncard` is honest.
    -- PROVABLE (Mathlib: `Nat.choose_le_choose`-family monotonicity;
    effort S — the binomial monotonicity lemma is the reusable
    asset). -/
theorem solutions_finite (a : ℕ) (ha : 2 ≤ a) : (solutions a).Finite := by
  refine (Finset.finite_toSet (Finset.range (a + 1) ×ˢ Finset.range (a + 1))).subset ?_
  intro q hq
  obtain ⟨hn, hk⟩ := le_of_mem_solutions hq
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  omega

/-- Bounded-search certificate: if `a < C(N+1,2)`, every listed pair is a
    solution, `(a,1)` is listed, and a Boolean scan of the box
    `n, k ≤ N` finds no other solution with `k ≥ 2` (testing
    `n.descFactorial k = k! * a`), then the solution set is the list. -/
private theorem solutions_eq_of_check (a N : ℕ) (L : List (ℕ × ℕ))
    (hN : a < (N + 1).choose 2) (hL : ∀ q ∈ L, q ∈ solutions a) (ha : (a, 1) ∈ L)
    (hcheck : ((List.range (N + 1)).all fun n => (List.range (N + 1)).all fun k =>
      !(2 ≤ k && 2 * k ≤ n && n.descFactorial k == k.factorial * a) || (n, k) ∈ L) = true) :
    solutions a = ↑L.toFinset := by
  ext ⟨n, k⟩
  simp only [Finset.mem_coe, List.mem_toFinset]
  constructor
  · intro hq
    obtain ⟨hk1, hkn, hchoose⟩ := hq
    dsimp only at hk1 hkn hchoose
    rcases Nat.eq_or_lt_of_le hk1 with hk | hk
    · subst hk
      rw [Nat.choose_one_right] at hchoose
      subst hchoose
      exact ha
    · have hle2 : n.choose 2 ≤ a :=
        hchoose ▸ choose_le_choose_of_le_of_two_mul_le hk hkn
      have hnN : n < N + 1 := by
        by_contra hcon
        have hmono : (N + 1).choose 2 ≤ n.choose 2 :=
          Nat.choose_mono 2 (Nat.le_of_not_lt hcon)
        omega
      have hdesc : n.descFactorial k = k.factorial * a := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, hchoose]
      rw [List.all_eq_true] at hcheck
      have hrow := hcheck n (List.mem_range.mpr hnN)
      rw [List.all_eq_true] at hrow
      have hcell := hrow k (List.mem_range.mpr (by omega))
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not, beq_eq_false_iff_ne, decide_eq_true_eq] at hcell
      rcases hcell with ((hc | hc) | hc) | hc
      · omega
      · omega
      · exact absurd hdesc hc
      · exact hc
  · exact hL (n, k)

/-- Ground truth: `multiplicity 6 = 2` — `6 = C(6,1) = C(4,2)`.
    -- PROVABLE (bounded decide after `solutions_finite`). -/
example : multiplicity 6 = 2 := by
  have hsol : solutions 6 = ↑([(6, 1), (4, 2)] : List (ℕ × ℕ)).toFinset := by
    refine solutions_eq_of_check 6 4 _ (by decide) ?_ (by simp) (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by decide⟩
  rw [multiplicity, hsol, Set.ncard_coe_finset]
  decide

/-- **The t = 3 certificate**: `multiplicity 120 = 3` —
    `120 = C(120,1) = C(16,2) = C(10,3)`.
    -- PROVABLE (bounded search n ≤ 120; decide-scale). -/
theorem multiplicity_120 : multiplicity 120 = 3 := by
  have hsol : solutions 120 =
      ↑([(120, 1), (16, 2), (10, 3)] : List (ℕ × ℕ)).toFinset := by
    refine solutions_eq_of_check 120 16 _ (by decide) ?_ (by simp) (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨by norm_num, by norm_num, Nat.choose_one_right 120⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
  rw [multiplicity, hsol, Set.ncard_coe_finset]
  decide

/-- **The t = 4 certificate**: `multiplicity 3003 = 4` —
    `3003 = C(3003,1) = C(78,2) = C(15,5) = C(14,6)`.
    -- PROVABLE (bounded search n ≤ 3003; decide/native_decide). -/
theorem multiplicity_3003 : multiplicity 3003 = 4 := by
  have hsol : solutions 3003 =
      ↑([(3003, 1), (78, 2), (15, 5), (14, 6)] : List (ℕ × ℕ)).toFinset := by
    refine solutions_eq_of_check 3003 78 _ (by decide) ?_ (by simp) (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, by norm_num, Nat.choose_one_right 3003⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
  rw [multiplicity, hsol, Set.ncard_coe_finset]
  decide

/-- **Erdős #849 (OPEN)**: for every `t ≥ 1` some `a ≥ 2` has exactly
    `t` representations.  (Believed FALSE by Erdős and Singmaster —
    t = 5 has no known witness; 3003 is conjectured maximal.) -/
theorem erdos_849 (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 2 ≤ a ∧ multiplicity a = t := by
  sorry

/-- The complementary believed-truth (Singmaster direction), archived:
    multiplicities are absolutely bounded. -/
theorem multiplicity_bounded :
    ∃ B : ℕ, ∀ a : ℕ, 2 ≤ a → multiplicity a ≤ B := by
  sorry

/-- **MRSTT interior bound** ([MRSTT22]), archived: for every ε > 0
    there is `A` such that for `a ≥ A`, at most two solutions have
    `k ≥ exp((log n)^{2/3+ε})`. -/
theorem mrstt_interior (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, ∀ a : ℕ, A ≤ a →
      ({q : ℕ × ℕ | q ∈ solutions a ∧
        Real.exp (Real.log q.1 ^ ((2 : ℝ) / 3 + ε)) ≤ (q.2 : ℝ)}).ncard
        ≤ 2 := by
  sorry

/-- Sanity: `t = 1` and `t = 2` are realized — every prime `p` has
    `multiplicity p = 1` (only `C(p,1)`), and `multiplicity 6 = 2`.
    Keeps `erdos_849` honest at the small end (the content is t ≥ 5).
    -- PROVABLE (decide instances). -/
example : multiplicity 5 = 1 ∧ multiplicity 6 = 2 := by
  have hsol5 : solutions 5 = ↑([(5, 1)] : List (ℕ × ℕ)).toFinset := by
    refine solutions_eq_of_check 5 3 _ (by decide) ?_ (by simp) (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact ⟨by norm_num, by norm_num, by decide⟩
  have hsol6 : solutions 6 = ↑([(6, 1), (4, 2)] : List (ℕ × ℕ)).toFinset := by
    refine solutions_eq_of_check 6 4 _ (by decide) ?_ (by simp) (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact ⟨by norm_num, by norm_num, by decide⟩
  rw [multiplicity, multiplicity, hsol5, hsol6, Set.ncard_coe_finset, Set.ncard_coe_finset]
  decide

end ErdosCandidates.E849

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches erdos fetch 849.
   - t=3 at 120: C(120,1)=C(16,2)=C(10,3)=120 verified, exactly 3 half-triangle solutions.
   - t=4 at 3003: C(3003,1)=C(78,2)=C(15,5)=C(14,6)=3003 verified, exactly 4.
   - multiplicity 6 = 2: solutions are (6,1) and (4,2) in the half-triangle; correct.
   - Half-triangle convention 2*k <= n (i.e. k <= n/2) matches the source "1 <= k <= n/2".
   - Erdos/Singmaster believed NO, MRSTT bound k >= exp((log n)^{2/3+eps}) faithful.
   - No fidelity issues found.
-/
