/-
  Erdős Problem #856 — harmonic weight of sets with no k elements of
  equal pairwise lcm.
  Status: open.  Tier UA attack target (second client of the Erdos857
  sunflower layer).

  Verbatim statement (`goof erdos fetch 856`, pulled 2026-08-05):

    "Let $k\geq 3$ and $f_k(N)$ be the maximum value of
    $\sum_{n\in A}\frac{1}{n}$, where $A$ ranges over all subsets of
    $\{1,\ldots,N\}$ which contain no subset of size $k$ with the same
    pairwise least common multiple.

    Estimate $f_k(N)$."

  DB remarks: Erdős [Er70]: f_k(N) ≪ (log N)/(log log N), via: for every
  t there are < k solutions to t = a·p with a ∈ A, p prime, whence
  (∑ 1/n)(∑_{p<N} 1/p) < k ∑_{t<N²} 1/t ≪ log N.  Tang–Zhang
  [TaZh25b, arXiv:2512.20055]: (log N)^{b_k−o(1)} ≤ f_k(N) ≤
  (log N)^{c_k+o(1)}; for k = 3: (log N)^{0.438} ≤ f₃(N) ≤
  (log N)^{0.889}.  The exponents c_k are < 1 iff the Erdős–Szemerédi
  sunflower conjecture #857 holds for k-sunflowers (their capacity
  µ_k^S: f_k(N) ≪ (log N)^{µ_k^S − 1 + o(1)}; equality µ_k^S = 2 iff
  f_k(N) = (log N)^{1−o(1)}).

  Repo adjacency: `Proofs/Erdos/Erdos857/NaslundSawin.lean`
  (`SunflowerFree`, `Erdos857Free`, `erdos857M`, Naslund–Sawin capacity
  bound 3/2^{2/3}) — the k = 3 upper-bound exponent 0.889 comes from
  exactly that bound.

  Mathlib inventory (leandoc 2026-08-05): `Nat.lcm`, `Finset.sum` over
  ℚ, `Finset.powersetCard`; no lcm-pattern machinery — the defs below
  are fresh.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E856

/-- `EqualPairwiseLcm S`: all pairs of distinct elements of `S` have the
    same lcm.  (The forbidden pattern, for `|S| = k`.) -/
def EqualPairwiseLcm (S : Finset ℕ) : Prop :=
  ∃ L : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.lcm a b = L

/-- `LcmPatternFree k A`: no `k`-element subset of `A` has constant
    pairwise lcm. -/
def LcmPatternFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powersetCard k, ¬ EqualPairwiseLcm S

/-- The harmonic weight `∑_{n ∈ A} 1/n : ℚ`.  (`1/0 = 0` junk is
    guarded in the theorems by `A ⊆ Icc 1 N`.) -/
def harmonicWeight (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

/-- Ground truth: primes have pairwise lcm p·q all distinct, so
    `{2, 3, 5}` is 3-pattern-free; harmonic weight 31/30.
    -- PROVABLE (decide). -/
example : LcmPatternFree 3 ({2, 3, 5} : Finset ℕ) ∧
    harmonicWeight {2, 3, 5} = 31 / 30 := by
  sorry

/-- Non-degeneracy: `{6, 10, 15}` has all pairwise lcms equal to 30, so
    it is NOT 3-pattern-free.  The constraint has content.
    -- PROVABLE (decide). -/
example : ¬ LcmPatternFree 3 ({6, 10, 15} : Finset ℕ) := by
  sorry

/-- **Erdős #856, Er70 upper bound (the Tier-UA target)**:
    `f_k(N) ≪ log N / log log N`.  Stated with an explicit constant
    over ℝ.

    Proof sketch (attack plan, following the DB's own proof): if `A` is
    `k`-pattern-free then for every `t` there are `< k` pairs `(a, p)`
    with `a ∈ A`, `p` prime, `t = a p` — otherwise `k` products
    `a₁p₁ = ⋯ = a_kp_k = t` yield `k` elements whose pairwise lcms all
    equal `t` (needs the primes distinct and not dividing the `a_i` —
    the actual combinatorial core; handle the multiplicity bookkeeping
    with `Nat.Coprime`).  Multiply out:
    `harmonicWeight A · ∑_{p<N} 1/p < k · ∑_{t<N²} 1/t ≪ k log N`, and
    `∑_{p<N} 1/p ≫ log log N` (Mertens.  Mathlib:
    `Nat.Primes.sum_one_div_le`? — Mertens' second theorem exists as
    `mertens_second`-shaped results in Mathlib's
    `NumberTheory/MertensTheorems`; re-check name via leandoc before
    the campaign).  Effort M. -/
theorem erdos_856_upper_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A ⊆ Finset.Icc 1 N, LcmPatternFree k A →
        (harmonicWeight A : ℝ) ≤ C * Real.log N / Real.log (Real.log N) := by
  sorry

/-- Trivial harmonic bound — the sanity floor:
    `harmonicWeight A ≤ 1 + log N` for `A ⊆ [1, N]`.
    -- PROVABLE (harmonic-sum vs log comparison; the ℚ→ℝ cast plus
    `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`-free route via
    `Finset.sum_div` and integral comparison in Mathlib's
    `Real.log` API). -/
theorem harmonicWeight_le (N : ℕ) (hN : 1 ≤ N) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    (harmonicWeight A : ℝ) ≤ 1 + Real.log N := by
  sorry

/-- **Tang–Zhang lower bound, k = 3** (TaZh25b), archived:
    `f₃(N) ≥ (log N)^{0.438}` for large `N` — realized by an explicit
    pattern-free `A`.  The exponent is `log 1.551` from the
    Deuber–Erdős–Gunderson–Kostochka–Meyer sunflower-free construction;
    the bridge to the repo's SUNFLOWER assets is the interesting part:
    a sunflower-free family of subsets of primes maps to an lcm-pattern-
    free set of squarefree integers by `S ↦ ∏_{p∈S} p`. -/
theorem tang_zhang_lower_k3 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A ⊆ Finset.Icc 1 N, LcmPatternFree 3 A ∧
        Real.log N ^ (0.438 : ℝ) ≤ (harmonicWeight A : ℝ) := by
  sorry

/-- **The sunflower encoding lemma** — the reusable bridge (also serves
    #535): for squarefree integers, equal pairwise lcms of
    `∏_{p∈S_i} p` correspond to the `S_i` forming a weak sunflower
    (pairwise unions equal).  Fresh def; connects to
    `Erdos.Erdos857.WeakSunflower3` for k = 3.  -- PROVABLE (elementary
    squarefree factorization; `Nat.squarefree_prod` API). -/
theorem lcm_pattern_iff_union_pattern (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    Nat.lcm (∏ p ∈ S, p) (∏ p ∈ T, p) = ∏ p ∈ (S ∪ T), p := by
  sorry

end ErdosCandidates.E856

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Verbatim statement matches DB pull exactly.
   - EqualPairwiseLcm and LcmPatternFree correctly encode the forbidden pattern.
   - harmonicWeight uses (1:Q)/n; junk at n=0 is guarded by A <= Icc 1 N in theorems.
   - lcm(6,10)=lcm(6,15)=lcm(10,15)=30 verified: {6,10,15} is NOT 3-pattern-free.
   - harmonicWeight {2,3,5} = 1/2+1/3+1/5 = 31/30 verified.
   - Er70 upper bound log N / log log N: matches DB body.
   - Tang-Zhang k=3 lower exponent 0.438: log(1.551) = 0.4389, rounded. Matches DB.
   - Tang-Zhang k=3 upper exponent 0.889: 3/2^{2/3}-1 = 0.8899. Matches DB.
   - FLAG (minor, style): lcm_pattern_iff_union_pattern is stated as an equality of
     lcm(prod S, prod T) = prod (S union T) for prime sets, not as an iff about
     EqualPairwiseLcm. The docstring says "iff ... union pattern" but the theorem is
     just the lcm-product identity. The bridge to EqualPairwiseLcm/WeakSunflower3 is
     not formalized here. Not a fidelity error but the theorem name overpromises.
   - Attributions: Er70 for upper bound, TaZh25b for Tang-Zhang, Naslund-Sawin for
     the 3/2^{2/3} capacity — all match DB.
-/
