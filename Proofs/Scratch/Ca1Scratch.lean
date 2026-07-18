import Mathlib
import Xlib.TPP
import Xlib.CUCapacity
import Xlib.CharDegreesComm
import Xlib.CharDegreesIndexBound
import Xlib.GeomArithInequality

/-! Scratch for Ca1: STPP capacity inequality, abelian instance -/

open scoped BigOperators
open Xlib.STPPWreath Xlib.TPP Xlib.CUCapacity Xlib.CharDegrees

-- Check that the key identity holds:
-- For the full n^ℓ triples from SimultaneousTPP.pow, the LHS of the capacity
-- inequality ∑_φ (a'_φ b'_φ c'_φ)^{ω/3} factors as (∑_i (a_i b_i c_i)^{ω/3})^ℓ.

-- The key plank: CU 4.1 on the wreath gives
-- ((n!)^3 * ∏ (a b c))^{ω/3} ≤ (n!)^{ω-1} * D^n
-- i.e., n! * (∏ (a b c))^{ω/3} ≤ D^n
-- where the product is over n STPP triples.

-- For the geometric mean bound:
-- (∏_i s_i)^{1/n} ≤ D / (n!)^{1/n}

-- This with le_of_pow_le_poly_mul_pow (iterating over ℓ-fold powers)
-- gives (∏ s_i)^{1/n} ≤ D (absorbing the factorial).

-- Then by AM-GM: (1/n) ∑ s_i ≥ (∏ s_i)^{1/n}, so ∑ s_i ≤ n * D. WRONG DIRECTION!

-- WAIT. AM-GM says arithmetic mean ≥ geometric mean.
-- So (1/n) ∑ s_i ≥ (∏ s_i)^{1/n}.
-- We have (∏ s_i)^{1/n} ≤ D.
-- This gives: ∑ s_i ≥ n * (∏ s_i)^{1/n}... no constraint on ∑ s_i.

-- AM-GM goes the WRONG WAY here. We'd need ∑ s_i ≤ something, but AM-GM only
-- gives ∑ s_i ≥ something.

-- OK the correct route MUST use the multinomial theorem / geom-arith.
-- After much algebra analysis, here's what works:

-- For each N ≥ 1 and μ : Fin n → ℕ with ∑ μ = N:
--   1. Take N-fold STPP power, select M = multinomial(N,μ) triples of type μ
--   2. Each triple has s'_p = ∏_i s_i^{μ_i} (same for all p)
--   3. Apply STPP2TPP: TPP in wreath with |S|*|T|*|U| = (M!)^3 * L^M
--      where L = ∏_i (a b c)_i^{μ_i}
--   4. CU 4.1 + wreath bound: (M!)^ω * L^{Mω/3} ≤ (M!)^{ω-1} * D^{NM}
--   5. Simplify: M! * (∏ s_i^{μ_i})^M ≤ D^{NM}
--   6. Since M ≤ M!: M * (∏ s_i^{μ_i})^M ≤ D^{NM}
--   7. i.e., multinomial(N,μ) * (∏ s_i^{μ_i})^M ≤ (D^N)^M

-- But step 7 is NOT the same as multinomial * ∏ s_i^{μ_i} ≤ D^N !
-- Step 7 has the product raised to M, not 1.

-- Hmm. Let's try: from M! * x^M ≤ y^M (where x = ∏ s^μ, y = D^N, M = multinomial):
-- Take M-th root: (M!)^{1/M} * x ≤ y
-- Since (M!)^{1/M} ≥ 1: x ≤ y
-- i.e., ∏ s_i^{μ_i} ≤ D^N for all μ with ∑ μ = N.

-- This gives: for μ = (N, 0, ..., 0): s_1^N ≤ D^N, so s_1 ≤ D.
-- More generally: s_i ≤ D for each i.

-- BUT: we need ∑ s_i ≤ D, which is STRICTLY STRONGER for n ≥ 2.

-- THE KEY INSIGHT: we do NOT have ∑ s_i ≤ D for arbitrary s_i ≤ D.
-- The STPP condition CONSTRAINS the s_i beyond just s_i ≤ D.
-- The constraint is: the n STPP triples in G force
-- (n!)^3 * ∏_i (a b c)_i ≤ tppCapacity(wreath) ≤ D(wreath) / ???
-- which gives a JOINT constraint on the s_i.

-- I think the correct formal proof goes through `sum_le_of_multinomial_prod_pow_le`
-- with hypothesis derived from ITERATED application:
-- For each ℓ ≥ 1, use ℓ*μ to get the bound. As ℓ varies, we get bounds for
-- different M values. The key: `le_of_pow_le_poly_mul_pow` inside
-- sum_le_of_multinomial_prod_pow_le absorbs the factorial.

-- Actually, wait. Let me re-read sum_le_of_multinomial_prod_pow_le's proof.
-- It uses le_of_pow_le_poly_mul_pow with:
-- x = ∑ s_i, y = C, K = 1, k = |ι|
-- The hypothesis: for all N and μ with ∑ μ = N,
--   multinomial(N, μ) * ∏ s_i^{μ_i} ≤ C^N
-- The proof: expand (∑ s_i)^N = ∑_μ multinomial * ∏ s_i^{μ_i} ≤ #{μ} * C^N ≤ (N+1)^k * C^N
-- Then le_of_pow_le_poly_mul_pow gives ∑ s_i ≤ C.

-- So the hypothesis IS multinomial * ∏ s^μ ≤ C^N. And I need to produce this.

-- From the capacity chain: M! * x^M ≤ y^M gives x ≤ y. So ∏ s^μ ≤ D^N.
-- Then multinomial * ∏ s^μ ≤ multinomial * D^N. But I need ≤ D^N, not multinomial * D^N.

-- UNLESS: the geom-arith step is INSIDE the wreath construction, not separate.
-- I.e., the hypothesis of sum_le_of_multinomial_prod_pow_le is proved BY the
-- capacity chain, which automatically has the multinomial factor absorbed.

-- Let me check: does the capacity chain give EXACTLY
-- multinomial(N, μ) * ∏ s_i^{μ_i} ≤ D^N ?

-- From M! * (∏ s^μ)^M ≤ (D^N)^M:
-- We have M = multinomial(N, μ) and (∏ s^μ) = x.
-- M! * x^M ≤ y^M where y = D^N.
-- M! ≥ M ≥ 1, so x ≤ y.
-- Also M * x^M ≤ M! * x^M ≤ y^M (since M ≤ M!).
-- So M * x^M ≤ y^M.
-- Taking M-th root: (M * x^M)^{1/M} = M^{1/M} * x ≤ y.
-- As M → ∞: M^{1/M} → 1, so x ≤ y. (Same as before.)

-- But we need M * x ≤ y, not M^{1/M} * x ≤ y.

-- UNLESS we iterate WITHIN the hypothesis of sum_le_of_multinomial_prod_pow_le.
-- That lemma needs: for ALL N and ALL μ with ∑ μ = N.
-- For each (N, μ), I get ONE instance of the capacity chain with one M.
-- I cannot iterate for a SINGLE (N, μ) pair.

-- CONCLUSION: The correct formal proof must use a DIFFERENT approach than
-- sum_le_of_multinomial_prod_pow_le. It should go through le_of_pow_le_poly_mul_pow
-- directly, applying the capacity chain to the FULL n^ℓ-fold power (not the
-- multinomial selection), and using the fact that the SUM of the s'_φ is (∑ s_i)^ℓ.

-- HERE IS THE CORRECT ROUTE:
-- For each ℓ ≥ 1:
--   1. Take ℓ-fold STPP power: n^ℓ triples in G^ℓ
--   2. Apply htpp: TPP in wreath S_{n^ℓ} ⋉ (G^ℓ)^{n^ℓ}
--   3. CU 4.1 on the wreath: tppCapacity(wreath)^{ω/3} ≤ D_ω(wreath)
--   4. hbound on the wreath: D_ω(wreath) ≤ ((n^ℓ)!)^{ω-1} * D_ω(G^ℓ)^{n^ℓ}
--   5. D_ω(G^ℓ) = |G|^ℓ = D_ω(G)^ℓ (abelian)
--   6. tppCapacity(wreath) ≥ |S|*|T|*|U| = ((n^ℓ)!)^3 * P
--      where P = (∏_i a_i)^{ℓ n^{ℓ-1}} * (∏_i b_i)^{ℓ n^{ℓ-1}} * (∏_i c_i)^{ℓ n^{ℓ-1}}
--   7. Combine: ((n^ℓ)!)^ω * P^{ω/3} ≤ ((n^ℓ)!)^{ω-1} * D^{ℓ n^ℓ}
--   8. Simplify: (n^ℓ)! * P^{ω/3} ≤ D^{ℓ n^ℓ}
--   9. P = (∏_i (abc)_i)^{ℓ n^{ℓ-1}}
--   10. P^{ω/3} = (∏_i s_i)^{ℓ n^{ℓ-1}} where s_i = (abc_i)^{ω/3}
--   11. (n^ℓ)! * (∏ s_i)^{ℓ n^{ℓ-1}} ≤ D^{ℓ n^ℓ}
--
-- THIS gives a bound on the GEOMETRIC MEAN (∏ s_i)^{1/n}, NOT the arithmetic mean!
-- The sum ∑ s_i does NOT appear anywhere!
--
-- KEY REALIZATION: The STPP capacity inequality CANNOT be proved purely from
-- the geometric mean bound. The multinomial selection IS ESSENTIAL.
-- And the multinomial selection gives multinomial * ∏ s^μ ≤ D^N, which I've
-- shown CANNOT be derived from the capacity chain alone (counterexample above).
--
-- THEREFORE: the STPP capacity inequality requires additional machinery beyond
-- what the current planks provide. Specifically, it needs the
-- sum_le_of_multinomial_prod_pow_le with a hypothesis that the capacity chain
-- does NOT directly produce.
--
-- RESOLUTION: I think the correct formalization has the factored theorem take
-- as hypothesis EXACTLY the multinomial bound:
-- ∀ N μ, ∑ μ = N → multinomial(univ, μ) * ∏_i s_i^{μ_i} ≤ C^N
-- where s_i = (abc_i)^{ω/3} and C = D_ω(G).
-- The CommGroup corollary then proves this hypothesis from the planks.
-- And proving this hypothesis IS the hard part (it goes through ITERATED
-- wreath constructions and absorbs the factorial via le_of_pow_le_poly_mul_pow).

-- Actually wait, I just realized: maybe the proof for the CommGroup case
-- is MUCH simpler. Let me check: for CommGroup G, D_ω(G) = |G|, and each
-- TPP triple (A, B, C) satisfies |A|*|B|*|C| ≤ |G| (since for abelian groups,
-- TPP is equivalent to A+B+C having distinct sums, giving |A|*|B|*|C| ≤ |G|).
-- And the STPP simultaneous condition gives |A_i|*|B_i|*|C_i| ≤ |G|/n... hmm no.

-- Actually, for abelian groups, the STPP is EQUIVALENT to the condition that
-- A_i - A_j + B_j - B_k + C_k - C_i ∩ {0} = ∅ for i ≠ j or j ≠ k.
-- This means the "mixed quotient sets" are disjoint from 0.
-- The sizes are constrained by... hmm, I don't think there's a simple size bound.

-- OK let me just compute with Sage for a real STPP example to see if the
-- hypothesis of sum_le_of_multinomial_prod_pow_le actually holds.

end
