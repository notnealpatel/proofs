/-
  Erdős Problem #535 — sets of integers with no `r` elements of equal
  pairwise gcd, via the prime-power layer encoding into sunflowers.

  ══════════════════════════════════════════════════════════════════════
  PRIMARY SOURCES (verbatim)
  ══════════════════════════════════════════════════════════════════════

  [1] erdosproblems.com problem #535, statement (`goof erdos fetch 535`,
      pulled 2026-08-05), quoted verbatim:

        "Let $r\geq 3$, and let $f_r(N)$ denote the size of the largest
        subset of $\{1,\ldots,N\}$ such that no subset of size $r$ has
        the same pairwise greatest common divisor between all elements.
        Estimate $f_r(N)$."

  [2] Same source, remarks, quoted verbatim (LaTeX as delivered):

        "Erd\H{o}s \cite{Er64} proved that\[f_r(N) \leq
        N^{\frac{3}{4}+o(1)},\]and Abbott and Hanson \cite{AbHa70}
        improved this exponent to $1/2$. Erd\H{o}s \cite{Er64} proved the
        lower bound, for any $r \geq 3$,\[f_r(N) >
        N^{\frac{c_r}{\log\log N}}\]for some constant $c_r>0$, and
        conjectured this should also be an upper bound.

        This is intimately connected with the sunflower problem [20].
        Indeed, Erd\H{o}s \cite{Er64} noted that a positive solution to
        [20] would imply\[f_r(N) \leq N^{\frac{C_r}{\log\log N}}\]for some
        constant $C_r>0$." [...]

  [3] Same source, comment by "Hrishi" (20:59 on 27 Apr 2026), quoted
      verbatim — this is the encoding formalized below:

        "The key idea is to encode each integer $n$ by the set of its
        prime-power divisibility layers,

        $$S(n)=\{(p,j):1\leq j\leq v_p(n)\}.$$

        Then

        $$S(a)\cap S(b)=S(\gcd(a,b)),$$

        so an $r$-tuple whose pairwise gcds are all equal is exactly an
        $r$-sunflower in the corresponding set system."

  [4] Same source, reply by "Thomas Bloom" (06:59 on 29 Apr 2026), quoted
      verbatim — the novelty caveat:

        "Thanks! While it is good to have the detailed calculations
        written down, this is not new; it is precisely the argument
        sketched by Erdős in [Er64].

        The improved upper bound is an immediate consequence of the
        improved bounds for the sunflower problem now available, when
        inserted into Erdős' argument."

  [5] Same source, comment by "Cong" (10:24 on 16 Apr 2026), quoted
      verbatim — this pins `Ω` (with multiplicity), not `ω`, as the right
      uniformity parameter for the auxiliary sunflower statement:

        "The counterexample $A_m=\{2,4,8,\dots,2^m\}$ shows that the
        current auxiliary formulation with $\omega(n)=k$ is false: for
        $k=1$, this family can be arbitrarily large while still avoiding
        an $r$-tuple with constant pairwise gcd.

        What seems to be the correct fix is the one Erdős gives later. In
        [Er73], he says that Abbott pointed out the ordinary sunflower
        conjecture does not seem to suffice for deriving the conjectured
        upper bound for $f_3(x)$. He then replaces it by a slightly
        stronger conjecture in which the integers have exactly $n$ prime
        factors counted with multiplicity. In modern notation, this is
        $\Omega(n)=k$, not $\omega(n)=k$."

  [6] The Erdős–Rado bound consumed here is
      `erdos_rado_sunflower_same_card` of `Erdos/Erdos20/ErdosRado.lean`,
      whose own verbatim pins (AFP entry "The Sunflower Lemma of Erdős
      and Rado", OEIS A332077) live in that file's header.  Its shape:

        family of `k`-element subsets of `Fin n`, `1 ≤ r`,
        `(r - 1) ^ k * k ! < family.card`  ⟹  `HasSunflower family r`.

  ══════════════════════════════════════════════════════════════════════
  WHAT IS PROVED, AND WHAT IS NOT
  ══════════════════════════════════════════════════════════════════════

  MAIN RESULT (`card_le_of_isAlmostPrime`, `gcdSunflowerNumber_le`).
  If every element of a finite set `A ⊆ ℕ` is `k`-almost prime
  (`Ω a = k`, `a ≠ 0`) and no `r` elements of `A` have the same pairwise
  gcd, then

        A.card ≤ (r - 1) ^ k * k !.

  It is genuinely non-trivial: `A` ranges over an INFINITE universe — the
  set of `k`-almost primes — yet the bound depends on `k` and `r` only.
  It is SHARP at `k = 1`: `gcdSunflowerNumber 1 r = r - 1`
  (`gcdSunflowerNumber_one`), the extremal families being sets of `r - 1`
  distinct primes.

  RELATION TO THE AUXILIARY STATEMENT OF [5] — the theorem here is
  WEAKER, on both counts.  Erdős' corrected auxiliary problem as quoted
  in [5] forbids `r`-tuples with `(a_i, a_j) = d` for all `i ≠ j` AND
  `(a_i/d, d) = 1` for all `i`, and asks for a bound of the form `c_r^k`
  (the `c_r^k` figure appears in Cong's earlier comment, post-4279).
   • This file forbids ALL equal-pairwise-gcd `r`-tuples, dropping the
     coprime-quotient side condition.  That is a STRICTLY STRONGER
     hypothesis on `A`, so the theorem proved is strictly weaker than the
     [5] form.
   • This file proves the Erdős–Rado bound `(r - 1)^k · k !`, not `c_r^k`.
     The `c_r^k` form is Erdős' STRENGTHENING of the sunflower conjecture
     [20] — [5] records that "Abbott pointed out the ordinary sunflower
     conjecture does not seem to suffice" — and remains open.
  What is taken from [5] is only the choice of uniformity parameter: `Ω`
  (prime factors WITH multiplicity), not `ω` — [5] exhibits
  `{2, 4, …, 2^m}` as the counterexample that rules `ω` out.

  HONEST WEAKNESS OF THE `N`-FORM.  Summing the layer bound over
  `Ω a ≤ log₂ N` gives `fgcd_le_erdos_rado`:

        f_r(N) ≤ (log₂ N + 1) · (r - 1) ^ (log₂ N) · (log₂ N)!.

  That bound is TRUE but WEAKER THAN TRIVIAL: `f_r(N) ≤ N` always
  (`fgcd_le_self`), and the right-hand side already exceeds `N` at
  `N = 2` and grows like `N^{Θ(log log N)}`.  This is machine-checked at
  `N = 2` and `N = 1024` in `erdosRado_bound_weaker_than_trivial` /
  `erdosRado_bound_weaker_than_trivial_1024`.  The Erdős–Rado lemma alone
  cannot beat `f_r(N) ≤ N`: the crude bound `Ω a ≤ log₂ a` is far off for
  typical `a ≤ N` (`Ω` has normal order `log log a`), and repairing it needs
  the smooth/rough split plus Rankin's estimate of [3], which is not
  formalized here.  The `N`-form is recorded only because it is the
  literal shape the reduction produces; the layer bound is the content.

  NOVELTY.  The mathematics is classical — Bloom [4] states plainly that
  the encoding argument "is precisely the argument sketched by Erdős in
  [Er64]".  What is new here is the formal artifact: a machine-checked
  gcd → sunflower reduction consuming a machine-checked Erdős–Rado bound.
  Nothing about the OPEN problem (estimating `f_r(N)`) is settled, and no
  bound stated here is competitive with [2] or [3].

  ══════════════════════════════════════════════════════════════════════
  DEVIATION FROM [3]: THE SHAPE OF THE LAYER SET
  ══════════════════════════════════════════════════════════════════════

  [3] encodes `n` by the set of PAIRS `S(n) = {(p,j) : 1 ≤ j ≤ v_p(n)}`.
  This file uses the image of `S(n)` under the bijection `(p,j) ↦ p^j`
  from prime-power layers to prime powers:

        layerSet N n = {q ≤ N : q is a prime power and q ∣ n}.

  The two are the same set system up to that relabeling, since
  `p ^ j ∣ n ↔ 1 ≤ j ≤ v_p(n)` for prime `p` and `j ≥ 1`, and a prime
  power determines its base and exponent.  `card_layerSet` records the
  consequence `|layerSet N n| = Ω n`, i.e. that the relabeling is
  injective.  The payoff is that the encoding lemma
  `layerSet_inter` becomes `Nat.dvd_gcd_iff` with no side conditions.

  The truncation `q ≤ N` is what lands the family in `Finset (Fin (N+1))`,
  the ground type of [6].  It is harmless: every prime power dividing
  `n ≤ N` is itself `≤ N`.
-/

import Erdos.Erdos20.ErdosRado
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

open Finset
open scoped Nat ArithmeticFunction.Omega

namespace Erdos535

-- ════════════════════════════════════════════════════════════════════
-- THE FORBIDDEN PATTERN
-- ════════════════════════════════════════════════════════════════════

/-- `EqualPairwiseGcd S`: all pairs of distinct elements of `S` have the
same greatest common divisor.  This is the pattern problem #535 forbids.

Stated with a universally quantified pair-of-pairs rather than an
existential `∃ d`, which keeps it decidable; the two forms agree
(`equalPairwiseGcd_iff_exists`). -/
def EqualPairwiseGcd (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≠ b → c ≠ d → Nat.gcd a b = Nat.gcd c d

instance (S : Finset ℕ) : Decidable (EqualPairwiseGcd S) := by
  unfold EqualPairwiseGcd; infer_instance

example : EqualPairwiseGcd {2, 3, 5} := by decide
example : ¬ EqualPairwiseGcd {4, 6, 9} := by decide
example : EqualPairwiseGcd ({10} : Finset ℕ) := by decide

/-- The `∀`-form used here is equivalent to the `∃ d`-form in which the
problem is usually phrased. -/
theorem equalPairwiseGcd_iff_exists (S : Finset ℕ) :
    EqualPairwiseGcd S ↔ ∃ d : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.gcd a b = d := by
  constructor
  · intro h
    by_cases hex : ∃ x ∈ S, ∃ y ∈ S, x ≠ y
    · obtain ⟨x, hx, y, hy, hxy⟩ := hex
      exact ⟨Nat.gcd x y, fun a ha b hb hab => h a ha b hb x hx y hy hab hxy⟩
    · push Not at hex
      exact ⟨0, fun a ha b hb hab => absurd (hex a ha b hb) hab⟩
  · rintro ⟨d, hd⟩ a ha b hb c hc e he hab hce
    rw [hd a ha b hb hab, hd c hc e he hce]

/-- `GcdPatternFree r A`: no `r`-element subset of `A` has constant
pairwise gcd.  `f_r(N)` of [1] is the largest cardinality of a
`GcdPatternFree r` subset of `{1, …, N}`. -/
def GcdPatternFree (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powersetCard r, ¬ EqualPairwiseGcd S

instance (r : ℕ) (A : Finset ℕ) : Decidable (GcdPatternFree r A) := by
  unfold GcdPatternFree; infer_instance

/-- Being pattern-free passes to subsets. -/
theorem GcdPatternFree.subset {r : ℕ} {A B : Finset ℕ}
    (h : GcdPatternFree r A) (hBA : B ⊆ A) : GcdPatternFree r B := by
  intro S hS
  obtain ⟨hSB, hScard⟩ := Finset.mem_powersetCard.mp hS
  exact h S (Finset.mem_powersetCard.mpr ⟨hSB.trans hBA, hScard⟩)

-- ════════════════════════════════════════════════════════════════════
-- GROUND TRUTH FOR THE DEFINITIONS
-- ════════════════════════════════════════════════════════════════════

/-- `{2, 3, 5}` is NOT `3`-pattern-free: all three pairwise gcds equal
`1`.  The forbidden pattern includes the pairwise-coprime case, which is
the easiest thing to misread in [1]. -/
example : ¬ GcdPatternFree 3 ({2, 3, 5} : Finset ℕ) := by decide

/-- `{2, 4, 3}` IS `3`-pattern-free: its pairwise gcds are `2, 1, 1`. -/
example : GcdPatternFree 3 ({2, 4, 3} : Finset ℕ) := by decide

/-- `{4, 6, 9}` IS `3`-pattern-free (gcds `2, 1, 3`) and is uniformly
`2`-almost prime, so it instantiates every hypothesis of
`card_le_of_isAlmostPrime` at `k = 2`, `r = 3` jointly. -/
example : GcdPatternFree 3 ({4, 6, 9} : Finset ℕ) := by decide

/-- `{2, 3, 5}` IS `4`-pattern-free, vacuously: it has no `4`-subset.
Contrast with the `r = 3` example above — `r` genuinely matters. -/
example : GcdPatternFree 4 ({2, 3, 5} : Finset ℕ) := by decide

/-- `{4, 6, 9}` is uniformly `2`-almost prime.  (`Nat.IsAlmostPrime` is
not decidable — `Nat.primeFactorsList` is defined by well-founded
recursion — so this goes through the prime-power API rather than
`decide`.) -/
theorem isAlmostPrime_two_of_mem_four_six_nine :
    ∀ a ∈ ({4, 6, 9} : Finset ℕ), Nat.IsAlmostPrime 2 a := by
  have h4 : Nat.IsAlmostPrime 2 4 := by
    simpa using Nat.prime_two.sq_isAlmostPrime_two
  have h6 : Nat.IsAlmostPrime 2 6 := by
    simpa using Nat.prime_two.mul_isAlmostPrime_two Nat.prime_three
  have h9 : Nat.IsAlmostPrime 2 9 := by
    simpa using Nat.prime_three.sq_isAlmostPrime_two
  intro a ha
  fin_cases ha
  exacts [h4, h6, h9]

-- ════════════════════════════════════════════════════════════════════
-- THE PRIME-POWER LAYER ENCODING
-- ════════════════════════════════════════════════════════════════════

/-- `layerSet N a` is the set of prime powers `≤ N` dividing `a`, as a
subset of the ground set `Fin (N+1)`.

This is the encoding `S(·)` of [3] relabeled by `(p, j) ↦ p ^ j`; see the
DEVIATION note in the file header. -/
def layerSet (N a : ℕ) : Finset (Fin (N + 1)) :=
  {q ∈ Finset.univ | IsPrimePow (q : ℕ) ∧ (q : ℕ) ∣ a}

@[simp]
theorem mem_layerSet {N a : ℕ} {q : Fin (N + 1)} :
    q ∈ layerSet N a ↔ IsPrimePow (q : ℕ) ∧ (q : ℕ) ∣ a := by
  simp [layerSet]

/-- **The encoding lemma** of [3]: `S(a) ∩ S(b) = S(gcd a b)`.  Under the
prime-power relabeling this is exactly `Nat.dvd_gcd_iff`, and it needs no
hypotheses at all (both sides are `∅` when `a = b = 1`). -/
theorem layerSet_inter (N a b : ℕ) :
    layerSet N a ∩ layerSet N b = layerSet N (Nat.gcd a b) := by
  ext q
  simp only [Finset.mem_inter, mem_layerSet, Nat.dvd_gcd_iff]
  tauto

/-- Every prime power dividing `a ≤ N` is visible in `layerSet N a`; so a
containment of layer sets is a containment of prime-power divisibility. -/
theorem pow_dvd_of_layerSet_subset {N a b : ℕ} (haN : a ≤ N)
    {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hdvd : p ^ j ∣ a) (ha : a ≠ 0)
    (h : layerSet N a ⊆ layerSet N b) : p ^ j ∣ b := by
  have hlt : p ^ j < N + 1 :=
    Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hdvd).trans haN)
  have hmem : (⟨p ^ j, hlt⟩ : Fin (N + 1)) ∈ layerSet N a :=
    mem_layerSet.mpr ⟨(isPrimePow_nat_iff _).mpr ⟨p, j, hp, hj, rfl⟩, hdvd⟩
  exact (mem_layerSet.mp (h hmem)).2

/-- The encoding is injective on `{1, …, N}`: an integer in range is
determined by which prime powers divide it. -/
theorem layerSet_injOn (N : ℕ) : Set.InjOn (layerSet N) (Set.Icc 1 N) := by
  have key : ∀ x y : ℕ, x ≠ 0 → x ≤ N → y ≠ 0 → layerSet N x ⊆ layerSet N y →
      ∀ p, p.Prime → x.factorization p ≤ y.factorization p := by
    intro x y hx hxN hy hsub p hp
    rcases Nat.eq_zero_or_pos (x.factorization p) with h0 | h0
    · omega
    · exact (hp.pow_dvd_iff_le_factorization hy).mp
        (pow_dvd_of_layerSet_subset hxN hp h0
          ((hp.pow_dvd_iff_le_factorization hx).mpr le_rfl) hx hsub)
  intro a ha b hb hab
  have ha0 : a ≠ 0 := Nat.one_le_iff_ne_zero.mp ha.1
  have hb0 : b ≠ 0 := Nat.one_le_iff_ne_zero.mp hb.1
  refine Nat.factorization_inj ha0 hb0 (Finsupp.ext fun p => ?_)
  by_cases hp : p.Prime
  · exact le_antisymm (key a b ha0 ha.2 hb0 hab.le p hp) (key b a hb0 hb.2 ha0 hab.ge p hp)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The encoding has the uniformity the Erdős–Rado lemma wants:
`|layerSet N a| = Ω a`, the number of prime factors of `a` counted with
multiplicity.  (The prime powers dividing `a` are exactly the `p ^ j`
with `p` prime and `1 ≤ j ≤ v_p(a)`, and there are `∑_p v_p(a) = Ω a` of
them.) -/
theorem card_layerSet {N a : ℕ} (ha : a ≠ 0) (haN : a ≤ N) :
    (layerSet N a).card = Ω a := by
  classical
  have hapos : 0 < a := Nat.pos_of_ne_zero ha
  -- The prime powers dividing `a`, written as `p ^ j` with `1 ≤ j ≤ v_p(a)`.
  set T : Finset ℕ :=
    a.primeFactors.biUnion (fun p => (Finset.Icc 1 (a.factorization p)).image (p ^ ·)) with hT
  have hstepA : (layerSet N a).card = T.card := by
    refine Finset.card_bij (fun q _ => (q : ℕ)) ?_ ?_ ?_
    · intro q hq
      obtain ⟨hpp, hdvd⟩ := mem_layerSet.mp hq
      obtain ⟨p, j, hp, hj, hpj⟩ := (isPrimePow_nat_iff _).mp hpp
      have hpdvd : p ^ j ∣ a := hpj ▸ hdvd
      refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
      · exact Nat.mem_primeFactors.mpr
          ⟨hp, dvd_trans (dvd_pow_self p (by omega : j ≠ 0)) hpdvd, ha⟩
      · exact Finset.mem_image.mpr
          ⟨j, Finset.mem_Icc.mpr ⟨hj, (hp.pow_dvd_iff_le_factorization ha).mp hpdvd⟩, hpj⟩
    · intro q₁ _ q₂ _ h
      exact Fin.val_injective h
    · intro m hm
      obtain ⟨p, hp, hm'⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm'
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : p ^ j ∣ a := (hpprime.pow_dvd_iff_le_factorization ha).mpr hj2
      have hlt : p ^ j < N + 1 := Nat.lt_succ_of_le ((Nat.le_of_dvd hapos hdvd).trans haN)
      exact ⟨⟨p ^ j, hlt⟩, mem_layerSet.mpr ⟨(isPrimePow_nat_iff _).mpr ⟨p, j, hpprime, hj1, rfl⟩,
        hdvd⟩, rfl⟩
  -- The union is disjoint and each fibre has `v_p(a)` elements.
  have hstepB : T.card = ∑ p ∈ a.primeFactors, a.factorization p := by
    rw [hT, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      rw [Finset.card_image_of_injective _ (Nat.pow_right_injective hpprime.two_le),
        Nat.card_Icc, Nat.add_sub_cancel]
    · intro p hp p' hp' hne
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp'prime : p'.Prime := Nat.prime_of_mem_primeFactors hp'
      refine Finset.disjoint_left.mpr fun m hm hm' => hne ?_
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp hm'
      obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp hj
      have hpdvd' : p ∣ p' ^ j' := heq ▸ dvd_pow_self p (by omega : j ≠ 0)
      exact (Nat.prime_dvd_prime_iff_eq hpprime hp'prime).mp (hpprime.dvd_of_dvd_pow hpdvd')
  rw [hstepA, hstepB, ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization]

-- ════════════════════════════════════════════════════════════════════
-- Ω IS AT MOST log₂
-- ════════════════════════════════════════════════════════════════════

/-- `2 ^ Ω a ≤ a` for `a ≠ 0`: each of the `Ω a` prime factors is `≥ 2`
and their product is `a`. -/
theorem two_pow_cardFactors_le {a : ℕ} (ha : a ≠ 0) : 2 ^ Ω a ≤ a := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc 2 ^ a.primeFactorsList.length
      ≤ a.primeFactorsList.prod :=
        List.pow_card_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
    _ = a := Nat.prod_primeFactorsList ha

/-- `Ω a ≤ log₂ N` for `1 ≤ a ≤ N`. -/
theorem cardFactors_le_log {a N : ℕ} (ha : a ≠ 0) (haN : a ≤ N) :
    Ω a ≤ Nat.log 2 N := by
  have hN : N ≠ 0 := by omega
  exact (Nat.le_log_iff_pow_le one_lt_two hN).mpr ((two_pow_cardFactors_le ha).trans haN)

-- ════════════════════════════════════════════════════════════════════
-- THE MAIN REDUCTION
-- ════════════════════════════════════════════════════════════════════

/-- **Main theorem.**  A finite set `A` of `k`-almost primes with no `r`
elements of equal pairwise gcd satisfies `|A| ≤ (r - 1)^k · k !`.

Obtained by pushing `erdos_rado_sunflower_same_card` through the
prime-power layer encoding: the layer sets of `A` form a `k`-uniform
family with no `r`-sunflower, because an `r`-sunflower of layer sets is
exactly an `r`-subset of `A` with constant pairwise gcd.

The bound is uniform over the infinite universe of `k`-almost primes,
and is sharp at `k = 1` (`gcdSunflowerNumber_one`).

This is NOT the auxiliary statement of [5]: that one carries the extra
coprime-quotient condition `(a_i/d, d) = 1` on the forbidden tuples and
asks for `c_r^k`.  Dropping the side condition strengthens the hypothesis
on `A` and so weakens the theorem; see the header. -/
theorem card_le_of_isAlmostPrime {r k : ℕ} (hr : 2 ≤ r) {A : Finset ℕ}
    (hA : ∀ a ∈ A, Nat.IsAlmostPrime k a) (hfree : GcdPatternFree r A) :
    A.card ≤ (r - 1) ^ k * k ! := by
  classical
  by_contra hcon
  push Not at hcon
  -- `N` is a common ground bound, so every layer set lives in `Fin (N+1)`.
  set N : ℕ := A.sup id with hN
  have hne : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA a ha).1
  have hle : ∀ a ∈ A, a ≤ N := fun a ha => Finset.le_sup (f := id) ha
  have hIcc : ∀ a ∈ A, a ∈ Set.Icc 1 N := fun a ha =>
    ⟨Nat.one_le_iff_ne_zero.mpr (hne a ha), hle a ha⟩
  have hinj : Set.InjOn (layerSet N) (A : Set ℕ) :=
    (layerSet_injOn N).mono (fun a ha => hIcc a (Finset.mem_coe.mp ha))
  -- The encoded family is `k`-uniform and too large to avoid an `r`-sunflower.
  set F : Finset (Finset (Fin (N + 1))) := A.image (layerSet N) with hF
  have hFcard : F.card = A.card := Finset.card_image_of_injOn hinj
  have hFuniform : ∀ S ∈ F, S.card = k := by
    intro S hS
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
    rw [card_layerSet (hne a ha) (hle a ha), (hA a ha).2]
  obtain ⟨sub, hsubF, hsubcard, K, -, -, hpair⟩ :=
    erdos_rado_sunflower_same_card (k := k) (r := r) F (by omega) hFuniform
      (by rw [hFcard]; exact hcon)
  -- Pull the sunflower back through the encoding.
  set A' : Finset ℕ := {a ∈ A | layerSet N a ∈ sub} with hA'def
  have hA'sub : A' ⊆ A := Finset.filter_subset _ _
  have hA'image : A'.image (layerSet N) = sub := by
    refine Finset.Subset.antisymm (fun S hS => ?_) (fun S hS => ?_)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hsubF hS)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hS⟩, rfl⟩
  have hA'card : A'.card = r := by
    rw [← hsubcard, ← hA'image,
      Finset.card_image_of_injOn (hinj.mono (fun a ha => Finset.mem_coe.mpr (hA'sub ha)))]
  -- The sunflower kernel forces all pairwise gcds inside `A'` to coincide.
  refine hfree A' (Finset.mem_powersetCard.mpr ⟨hA'sub, hA'card⟩) ?_
  have hker : ∀ x ∈ A', ∀ y ∈ A', x ≠ y → layerSet N (Nat.gcd x y) = K := by
    intro x hx y hy hxy
    rw [← layerSet_inter]
    refine hpair _ (hA'image ▸ Finset.mem_image_of_mem _ hx) _
      (hA'image ▸ Finset.mem_image_of_mem _ hy) (fun h => hxy ?_)
    exact hinj (Finset.mem_coe.mpr (hA'sub hx)) (Finset.mem_coe.mpr (hA'sub hy)) h
  have hgIcc : ∀ x ∈ A', ∀ y ∈ A', Nat.gcd x y ∈ Set.Icc 1 N := by
    intro x hx y hy
    have hx0 : x ≠ 0 := hne x (hA'sub hx)
    refine ⟨Nat.one_le_iff_ne_zero.mpr fun h => hx0 (Nat.eq_zero_of_gcd_eq_zero_left h), ?_⟩
    exact (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hx0)).trans (hle x (hA'sub hx))
  intro a ha b hb c hc d hd hab hcd
  exact layerSet_injOn N (hgIcc a ha b hb) (hgIcc c hc d hd)
    ((hker a ha b hb hab).trans (hker c hc d hd hcd).symm)

/-- Joint satisfiability of every hypothesis of
`card_le_of_isAlmostPrime` at one concrete model: `r = 3`, `k = 2`,
`A = {4, 6, 9}`.  `A` is nonempty and the conclusion `3 ≤ 2 ^ 2 * 2 ! = 8`
is a genuine (non-vacuous) inequality, so the theorem is not vacuously
quantified. -/
example : ({4, 6, 9} : Finset ℕ).card ≤ (3 - 1) ^ 2 * 2 ! :=
  card_le_of_isAlmostPrime (by norm_num) isAlmostPrime_two_of_mem_four_six_nine (by decide)

-- ════════════════════════════════════════════════════════════════════
-- THE GCD-SUNFLOWER NUMBER
-- ════════════════════════════════════════════════════════════════════

/-- The set of achievable sizes of `k`-almost-prime, `r`-pattern-free
sets.  `gcdSunflowerNumber` is its supremum. -/
def gcdSunflowerSizes (k r : ℕ) : Set ℕ :=
  {m : ℕ | ∃ A : Finset ℕ,
    (∀ a ∈ A, Nat.IsAlmostPrime k a) ∧ GcdPatternFree r A ∧ A.card = m}

/-- `gcdSunflowerNumber k r`: the largest size of a set of `k`-almost
primes containing no `r` elements of equal pairwise gcd.

For `1 ≤ r` the defining set contains `0` (witnessed by `A = ∅`,
`gcdSunflowerSizes_nonempty`) and is bounded above
(`gcdSunflowerSizes_bddAbove`, needing `2 ≤ r`), so under `2 ≤ r` this is
a genuine maximum rather than the `ℕ`-valued `sSup` junk value `0`.  At
`r = 0` the defining set is empty — `GcdPatternFree 0 A` is false for
every `A` — and the definition degenerates to `0`; every theorem below
therefore carries `2 ≤ r`. -/
noncomputable def gcdSunflowerNumber (k r : ℕ) : ℕ := sSup (gcdSunflowerSizes k r)

/-- The defining set of `gcdSunflowerNumber` is nonempty for `1 ≤ r`,
witnessed by the empty family. -/
theorem gcdSunflowerSizes_nonempty (k : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (gcdSunflowerSizes k r).Nonempty := by
  refine ⟨0, ∅, by simp, ?_, Finset.card_empty⟩
  intro S hS
  rw [Finset.powersetCard_eq_empty.mpr (by simp only [Finset.card_empty]; omega)] at hS
  exact absurd hS (Finset.notMem_empty S)

/-- The defining set of `gcdSunflowerNumber` is bounded above — this is
the content of `card_le_of_isAlmostPrime`. -/
theorem gcdSunflowerSizes_bddAbove {k r : ℕ} (hr : 2 ≤ r) :
    BddAbove (gcdSunflowerSizes k r) := by
  refine ⟨(r - 1) ^ k * k !, ?_⟩
  rintro m ⟨A, hA, hfree, rfl⟩
  exact card_le_of_isAlmostPrime hr hA hfree

/-- **The gcd-sunflower number is bounded**:
`gcdSunflowerNumber k r ≤ (r - 1) ^ k * k !`. -/
theorem gcdSunflowerNumber_le {k r : ℕ} (hr : 2 ≤ r) :
    gcdSunflowerNumber k r ≤ (r - 1) ^ k * k ! := by
  refine csSup_le (gcdSunflowerSizes_nonempty k (by omega)) ?_
  rintro m ⟨A, hA, hfree, rfl⟩
  exact card_le_of_isAlmostPrime hr hA hfree

/-- There are arbitrarily large finite sets of primes.  (Used to exhibit
extremal families for `gcdSunflowerNumber 1 r`.) -/
theorem exists_finset_primes (m : ℕ) : ∃ P : Finset ℕ, P.card = m ∧ ∀ p ∈ P, p.Prime := by
  induction m with
  | zero => exact ⟨∅, Finset.card_empty, by simp⟩
  | succ m ih =>
      obtain ⟨P, hcard, hP⟩ := ih
      obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (P.sup id + 1)
      have hpnot : p ∉ P := fun h => by
        have hsup : id p ≤ P.sup id := Finset.le_sup (f := id) h
        simp only [id] at hsup
        omega
      refine ⟨insert p P, by rw [Finset.card_insert_of_notMem hpnot, hcard], fun q hq => ?_⟩
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact hp
      · exact hP q hq'

/-- **Sharpness at `k = 1`**: `gcdSunflowerNumber 1 r = r - 1`.  The upper
bound is `gcdSunflowerNumber_le`; the matching lower bound is any set of
`r - 1` distinct primes, which is pattern-free because it is too small to
contain an `r`-subset at all.  (Three or more primes DO realize the
pattern — all their pairwise gcds are `1` — so `r - 1` is exactly the
threshold.) -/
theorem gcdSunflowerNumber_one {r : ℕ} (hr : 2 ≤ r) :
    gcdSunflowerNumber 1 r = r - 1 := by
  refine le_antisymm ?_ ?_
  · simpa using gcdSunflowerNumber_le (k := 1) hr
  · obtain ⟨P, hPcard, hP⟩ := exists_finset_primes (r - 1)
    refine le_csSup (gcdSunflowerSizes_bddAbove hr) ⟨P, ?_, ?_, hPcard⟩
    · exact fun p hp => Nat.isAlmostPrime_one_iff.mpr (hP p hp)
    · intro S hS
      rw [Finset.powersetCard_eq_empty.mpr (by omega)] at hS
      exact absurd hS (Finset.notMem_empty S)

/-- The `r = 3` instance of `gcdSunflowerNumber_one`, spelled out: the
largest set of primes with no three of equal pairwise gcd has two
elements.  Both bracketing witnesses are machine-checked separately:
`¬ GcdPatternFree 3 {2, 3, 5}` in the ground-truth block above, and
`GcdPatternFree 3 {2, 3}` immediately below. -/
theorem gcdSunflowerNumber_one_three : gcdSunflowerNumber 1 3 = 2 := by
  simpa using gcdSunflowerNumber_one (r := 3) (by norm_num)

/-- The extremal family for `gcdSunflowerNumber 1 3 = 2`. -/
example : GcdPatternFree 3 ({2, 3} : Finset ℕ) := by decide

-- ════════════════════════════════════════════════════════════════════
-- THE `f_r(N)` FORM
-- ════════════════════════════════════════════════════════════════════

/-- `fgcd r N` is `f_r(N)` of [1]: the size of the largest subset of
`{1, …, N}` no `r` elements of which have the same pairwise gcd. -/
def fgcd (r N : ℕ) : ℕ :=
  {A ∈ (Finset.Icc 1 N).powerset | GcdPatternFree r A}.sup Finset.card

/-- Every pattern-free subset of `{1, …, N}` is counted by `fgcd`. -/
theorem le_fgcd {r N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hfree : GcdPatternFree r A) : A.card ≤ fgcd r N :=
  Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hfree⟩)

/- Ground truth for `fgcd`: `f_3(N)` for `N = 0, …, 10` is
`0, 1, 2, 2, 3, 3, 3, 3, 4, 5, 5` (independently reproduced by brute
force outside Lean).  `fgcd` is computable because `GcdPatternFree` is;
the first few values are checked by kernel reduction below, the whole
table is displayed by `#eval` (which is NOT proof-bearing). -/
#eval (List.range 11).map (fgcd 3)

example : fgcd 3 0 = 0 := by decide
example : fgcd 3 1 = 1 := by decide
example : fgcd 3 2 = 2 := by decide
example : fgcd 3 3 = 2 := by decide
example : fgcd 3 4 = 3 := by decide

/-- Non-vacuity of `fgcd`: it is not identically `0`.  `{4, 6, 9}` is a
`3`-pattern-free subset of `{1, …, 9}`, so `3 ≤ f_3(9)`. -/
theorem three_le_fgcd_three_nine : 3 ≤ fgcd 3 9 := by
  have hcard : ({4, 6, 9} : Finset ℕ).card = 3 := by decide
  exact hcard ▸ le_fgcd (by decide) (by decide)

/-- The trivial bound `f_r(N) ≤ N`.  Recorded so that the strength of
`fgcd_le_erdos_rado` can be judged against it. -/
theorem fgcd_le_self (r N : ℕ) : fgcd r N ≤ N := by
  refine Finset.sup_le fun A hA => ?_
  have hsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsub
    _ = N := by rw [Nat.card_Icc]; omega

/-- **The `N`-form of the reduction.**  Summing `card_le_of_isAlmostPrime`
over the `log₂ N + 1` possible values of `Ω a` for `1 ≤ a ≤ N`:

  `f_r(N) ≤ (log₂ N + 1) · (r - 1)^(log₂ N) · (log₂ N)!`.

TRUE BUT WEAKER THAN TRIVIAL — see the header and
`erdosRado_bound_weaker_than_trivial`.  The hypothesis `3 ≤ r` matches
[1]; the proof only uses `2 ≤ r`. -/
theorem fgcd_le_erdos_rado {r N : ℕ} (hr : 3 ≤ r) :
    fgcd r N ≤ (Nat.log 2 N + 1) * ((r - 1) ^ Nat.log 2 N * (Nat.log 2 N)!) := by
  classical
  refine Finset.sup_le fun A hA => ?_
  obtain ⟨hApow, hfree⟩ := Finset.mem_filter.mp hA
  have hAsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp hApow
  have hne : ∀ a ∈ A, a ≠ 0 := fun a ha => by
    have hone : 1 ≤ a := (Finset.mem_Icc.mp (hAsub ha)).1
    omega
  have hle : ∀ a ∈ A, a ≤ N := fun a ha => (Finset.mem_Icc.mp (hAsub ha)).2
  -- Split `A` into the `log₂ N + 1` fibres of `Ω`.
  have hmaps : Set.MapsTo (fun a => Ω a) (A : Set ℕ) (Finset.range (Nat.log 2 N + 1) : Set ℕ) := by
    intro a ha
    have ha' : a ∈ A := Finset.mem_coe.mp ha
    simpa using Nat.lt_succ_of_le (cardFactors_le_log (hne a ha') (hle a ha'))
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ k ∈ Finset.range (Nat.log 2 N + 1), {a ∈ A | Ω a = k}.card
      ≤ ∑ _k ∈ Finset.range (Nat.log 2 N + 1),
          ((r - 1) ^ Nat.log 2 N * (Nat.log 2 N)!) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkL : k ≤ Nat.log 2 N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hlayer : {a ∈ A | Ω a = k}.card ≤ (r - 1) ^ k * k ! := by
          refine card_le_of_isAlmostPrime (by omega) (fun a ha => ?_)
            (hfree.subset (Finset.filter_subset _ _))
          obtain ⟨ha', hΩ⟩ := Finset.mem_filter.mp ha
          exact ⟨hne a ha', hΩ⟩
        exact hlayer.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hkL)
          (Nat.factorial_le hkL))
    _ = (Nat.log 2 N + 1) * ((r - 1) ^ Nat.log 2 N * (Nat.log 2 N)!) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The bound in the exact shape of the `Proofs/Scratch/ErdosCandidates/E535.lean`
sketch, `(log₂ N + 1) · (log₂ N)! · (r-1)^(log₂ N + 1)`, which is the
above weakened by one more factor of `r - 1`. -/
theorem fgcd_le_erdos_rado_sketch_form {r N : ℕ} (hr : 3 ≤ r) :
    fgcd r N ≤ (Nat.log 2 N + 1) * (Nat.log 2 N)! * (r - 1) ^ (Nat.log 2 N + 1) := by
  refine (fgcd_le_erdos_rado hr).trans ?_
  have hcomm : (Nat.log 2 N + 1) * ((r - 1) ^ Nat.log 2 N * (Nat.log 2 N)!)
      = (Nat.log 2 N + 1) * (Nat.log 2 N)! * (r - 1) ^ Nat.log 2 N := by ring
  rw [hcomm]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))

-- ════════════════════════════════════════════════════════════════════
-- HOW WEAK THE `N`-FORM IS
-- ════════════════════════════════════════════════════════════════════

/-- At `N = 2`, `r = 3` the Erdős–Rado-derived bound is `4`, already
larger than the trivial bound `f_3(2) ≤ 2` of `fgcd_le_self` — and the
true value is `fgcd 3 2 = 2`, checked by `decide` above.  So the `N`-form
is already worse than trivial at the smallest interesting `N`. -/
theorem erdosRado_bound_weaker_than_trivial :
    (2 : ℕ) < (Nat.log 2 2 + 1) * ((3 - 1) ^ Nat.log 2 2 * (Nat.log 2 2)!) := by
  norm_num [Nat.factorial]

/-- At `N = 1024`, `r = 3` the Erdős–Rado-derived bound is
`40874803200`, against the trivial bound `f_3(1024) ≤ 1024`. -/
theorem erdosRado_bound_weaker_than_trivial_1024 :
    (1024 : ℕ) < (Nat.log 2 1024 + 1) * ((3 - 1) ^ Nat.log 2 1024 * (Nat.log 2 1024)!) := by
  norm_num [Nat.factorial]

end Erdos535

-- ════════════════════════════════════════════════════════════════════
-- SIGNATURE AUDIT
-- ════════════════════════════════════════════════════════════════════

#check @Erdos535.EqualPairwiseGcd
#check @Erdos535.equalPairwiseGcd_iff_exists
#check @Erdos535.GcdPatternFree
#check @Erdos535.GcdPatternFree.subset
#check @Erdos535.isAlmostPrime_two_of_mem_four_six_nine
#check @Erdos535.layerSet
#check @Erdos535.mem_layerSet
#check @Erdos535.layerSet_inter
#check @Erdos535.pow_dvd_of_layerSet_subset
#check @Erdos535.layerSet_injOn
#check @Erdos535.card_layerSet
#check @Erdos535.two_pow_cardFactors_le
#check @Erdos535.cardFactors_le_log
#check @Erdos535.card_le_of_isAlmostPrime
#check @Erdos535.gcdSunflowerSizes
#check @Erdos535.gcdSunflowerSizes_nonempty
#check @Erdos535.gcdSunflowerSizes_bddAbove
#check @Erdos535.gcdSunflowerNumber
#check @Erdos535.gcdSunflowerNumber_le
#check @Erdos535.exists_finset_primes
#check @Erdos535.gcdSunflowerNumber_one
#check @Erdos535.gcdSunflowerNumber_one_three
#check @Erdos535.fgcd
#check @Erdos535.le_fgcd
#check @Erdos535.three_le_fgcd_three_nine
#check @Erdos535.fgcd_le_self
#check @Erdos535.fgcd_le_erdos_rado
#check @Erdos535.fgcd_le_erdos_rado_sketch_form
#check @Erdos535.erdosRado_bound_weaker_than_trivial
#check @Erdos535.erdosRado_bound_weaker_than_trivial_1024

-- ════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms Erdos535.equalPairwiseGcd_iff_exists
#print axioms Erdos535.GcdPatternFree.subset
#print axioms Erdos535.isAlmostPrime_two_of_mem_four_six_nine
#print axioms Erdos535.mem_layerSet
#print axioms Erdos535.layerSet_inter
#print axioms Erdos535.pow_dvd_of_layerSet_subset
#print axioms Erdos535.layerSet_injOn
#print axioms Erdos535.card_layerSet
#print axioms Erdos535.two_pow_cardFactors_le
#print axioms Erdos535.cardFactors_le_log
#print axioms Erdos535.card_le_of_isAlmostPrime
#print axioms Erdos535.gcdSunflowerSizes_nonempty
#print axioms Erdos535.gcdSunflowerSizes_bddAbove
#print axioms Erdos535.exists_finset_primes
#print axioms Erdos535.gcdSunflowerNumber_le
#print axioms Erdos535.gcdSunflowerNumber_one
#print axioms Erdos535.gcdSunflowerNumber_one_three
#print axioms Erdos535.le_fgcd
#print axioms Erdos535.three_le_fgcd_three_nine
#print axioms Erdos535.fgcd_le_self
#print axioms Erdos535.fgcd_le_erdos_rado
#print axioms Erdos535.fgcd_le_erdos_rado_sketch_form
#print axioms Erdos535.erdosRado_bound_weaker_than_trivial
#print axioms Erdos535.erdosRado_bound_weaker_than_trivial_1024
