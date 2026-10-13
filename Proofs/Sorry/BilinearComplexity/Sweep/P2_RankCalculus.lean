/-
  Sorry/BilinearComplexity/Sweep/P2_RankCalculus — calibration conjecture sweep (pair P2,
  concrete track: exact rank decompositions of small matmul tensors over
  finite fields, especially F₂ and ⟨3,3,3⟩).

  Conjectures produced from computational data only:
    · Scratch/stabilizer_cache.json      (Strassen S₃×S₃ order 36 EXACT,
                                          orbit sizes 1+6; Smirnov-1 C₃
                                          LOWER BOUND, orbit sizes 1+8·3)
    · Scratch/burnside_n3.sage           (511³ rank-1 F₂ tensors → 211
                                          orbits under the sandwich action)
    · Scratch/residual_aut_cascade.sage  (⟨2,2,2⟩/F₂: 21 Aut-orbits of
                                          nonzero rank-1 tensors, orbit
                                          sizes 27…432; residual Lie-stab
                                          dims 3…10, T itself 11, generic 2)
    · Scratch/residual_trajectory.sage   (Laderman 23 / Smirnov-1,2 25 peel
                                          trajectories)
    · fresh probes (2026-07-19): sandwich convention g₃ = P^{-T}⊗R in the
      (i,k)-packing verified exhaustively over all 168² triples for n=2;
      Strassen-mod-2 triads fall into exactly 2 Aut-orbits, sizes 1 (the
      identity triad vec(I)⊗vec(I)⊗vec(I), orbit size 36) and 6 (orbit
      size 216, middle factor singular); Smirnov-1's C₃-fixed triad IS
      vec(I₃)⊗vec(I₃)⊗vec(I₃) with det 1 (also mod 2); for n=3 the
      sandwich action has 0-dimensional common fixed space on each mode;
      200 random rank-1 peels of ⟨3,3,3⟩/F₂ all keep residual Lie-stab
      dim ≥ 4 (> the 2-dimensional trivial space).

  The original vocabulary and p2_c1, p2_c2, p2_c4 are now provided by
  BilinearComplexity.Sandwich; InfStab, p2_c3, and p2_c9 are provided by
  BilinearComplexity.P2MovingTriad; p2_c8 is provided by
  BilinearComplexity.P2ResidualStabilizer. The four remaining conjectures
  (p2_c5, p2_c6, p2_c7, p2_c10) retain `sorry`;
  their historical computational evidence below is not a proof.
  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.ZMod.Basic
import BilinearComplexity.P2ResidualStabilizer

set_option autoImplicit false

namespace BilinearComplexity
namespace P2Sweep

open Matrix

/-! ### Remaining local vocabulary (shared sandwich vocabulary is imported) -/

/-- Unpack a mode vector of `matMulTensor k n n n` into an `n × n` matrix
(row-major, first component slow). -/
def matOf {k : Type*} {n : ℕ} (x : Fin (n * n) → k) : Matrix (Fin n) (Fin n) k :=
  fun i j => x (finProdFinEquiv (i, j))

/- Infinitesimal (Lie-algebra) stabilizer condition: `(X₁,X₂,X₃)` is a
derivation annihilating `T`. Over F₂ the triple `(α•1, β•1, (α+β)•1)`
satisfies this for every tensor — the 2-dimensional trivial space. -/
-- `InfStab` is now provided by `BilinearComplexity.P2MovingTriad`.

/-! ### Historical sweep: imported results and remaining conjectures -/

/- (a) The de-Groote-style sandwich `(P,Q,R) ↦ (P⊗⅟Qᵀ, Q⊗⅟Rᵀ, R⊗⅟Pᵀ)`
   fixes `matMulTensor` — the licensing lemma behind every orbit count in
   burnside_n3.sage and compute_stabilizers.sage; verified exhaustively for
   n=2 over F₂ (all 168² = 216 GL(2,2)³ triples, probe 2026-07-19) and
   implicitly by every verified decomposition-stabilizer computation.
   (b) [concrete]
   (c) exact-tier data only. -/
-- `p2_c1` is now provided by `BilinearComplexity.Sandwich`.

/- (a) Stabilizers multiply under Kronecker product: the mode-wise
   `matKron` of a stabilizing triple of `T` and one of `T'` stabilizes
   `kron T T'` — licenses orbit reduction for `⟨9,9,9⟩ = ⟨3,3,3⟩⊗⟨3,3,3⟩`
   searches; grounded in the pipeline's pervasive use of
   `tensor_product` to build the acting group.
   (b) [concrete]
   (c) exact-tier. -/
-- `p2_c2` is now provided by `BilinearComplexity.Sandwich`.

/- (a) No nonzero rank-1 tensor is fixed by the whole stabilizer of
   `⟨n,n,n⟩` over F₂: exhaustive for n=2 (all 3375 nonzero triads, min
   Aut-orbit size 27 in residual_aut_cascade.sage); for n=3 the sandwich
   action has trivial common fixed space on each mode (probe). So full-group
   orbit reduction via `stab_residual` necessarily degrades after one peel.
   FLAG: n ≥ 4 is extrapolation beyond the data.
   (b) [concrete]
   (c) exact-tier for n=2,3; extrapolated beyond. -/
-- `p2_c3` is now proved in `BilinearComplexity.P2MovingTriad`.

/- (a) The diagonal sandwich `(P,P,P)` fixes the residual
   `⟨n,n,n⟩ − vec(I)⊗vec(I)⊗vec(I)`: the Strassen stabilizer (order 36,
   EXACT, cache) fixes its identity triad (orbit size 1, probe: orbit of
   `vec(I)^⊗3` has size 36, stabilizer order 12 ⊇ diagonal GL(2,2));
   Smirnov-1's C₃-fixed triad is also exactly `vec(I₃)^⊗3` (probe, det 1).
   This is the concrete `stab_residual` instance at peel step 1 of an
   identity-triad-first search.
   (b) [concrete]
   (c) Smirnov-1 evidence is lower-bound-tier (C₃ only); Strassen exact. -/
-- `p2_c4` is now provided by `BilinearComplexity.Sandwich`.

/- (a) Every rank-7 decomposition of `⟨2,2,2⟩` over F₂ contains a triad
   all three of whose factor matrices are invertible: in Strassen mod 2 the
   7 triads split into Aut-orbits 1+6 (probe), and exactly the orbit-size-1
   triad `vec(I)^⊗3` has all factors invertible (the other 6 have a
   singular weight-1 middle factor). Killable by exhibiting any F₂ rank-7
   decomposition (e.g. a Hopcroft–Kerr variant) with no such triad.
   (b) [concrete]
   (c) exact-tier; single-decomposition evidence, genuinely risky. -/
theorem p2_c5 (u v w : Fin 7 → Fin (2 * 2) → ZMod 2)
    (hdec : matMulTensor (ZMod 2) 2 2 2 = fun i j l => ∑ s, u s i * v s j * w s l) :
    ∃ s, IsUnit (matOf (u s)) ∧ IsUnit (matOf (v s)) ∧ IsUnit (matOf (w s)) := sorry

/- (a) The central bet of the rank-23 search: peeling the identity triad
   from `⟨3,3,3⟩` over F₂ leaves rank ≤ 22, i.e. some rank-23 decomposition
   contains `vec(I₃)^⊗3`. Grounded in the cross-decomposition pattern that
   the symmetry-fixed triad of BOTH Strassen (rank 7 = 6+identity) and
   Smirnov-1 (rank 25 = 24+identity) is the identity triad. NOT verified
   directly (whether Laderman mod 2 is equivalent to such a decomposition
   is unknown); direct check skipped for time under the 60 s budget.
   (b) [concrete]
   (c) leans on lower-bound-tier Smirnov-1 cache data; genuinely open. -/
theorem p2_c6 :
    RankLE (matMulTensor (ZMod 2) 3 3 3 - identityTriad (ZMod 2) 3) 22 := sorry

/- (a) Companion lower bet: the identity-peel residual does NOT have rank
   ≤ 21 (else `R⟨3,3,3⟩ ≤ 22` over F₂ via re-adding the triad). A rank-22
   search that peels the identity triad first must fail at 21; killing this
   statement would be a breakthrough rank-22 algorithm over F₂.
   (b) [concrete]
   (c) open; consistent with all known decompositions (23 is the best
   verified in Scratch: Laderman trajectory reaches 0 in 23 steps). -/
theorem p2_c7 :
    ¬ RankLE (matMulTensor (ZMod 2) 3 3 3 - identityTriad (ZMod 2) 3) 21 := sorry

/- (a) Infinitesimal symmetry survives one peel for `⟨3,3,3⟩`/F₂: every
   rank-1 residual keeps a derivation outside the trivial 2-dimensional
   space `{(α•1, β•1, (α+β)•1)}`. Exhaustive for the n=2 analogue (all 21
   orbits, min residual Lie dim 3 > 2, residual_aut_cascade.sage); for
   n=3, 200 random rank-1 peels all gave Lie dim ≥ 4 > 2 (probe; full
   211-orbit sweep skipped for time under the 60 s budget).
   (b) [concrete]
   (c) sampled evidence for n=3, exhaustive only for the n=2 analogue. -/
-- `p2_c8` is now proved in `BilinearComplexity.P2ResidualStabilizer`.

/- (a) …but the infinitesimal stabilizer never survives a peel intact:
   for every nonzero rank-1 `t`, some derivation of `⟨2,2,2⟩`/F₂ fails on
   the residual. Exhaustive: residual Lie dims are 3–10 across all 21
   orbits, strictly below dim 11 of `T` itself (residual_aut_cascade.sage);
   `Lie(T) ⊆ Lie(T−t)` would force dim ≥ 11. The n=3 analogue (26 vs
   sampled ≤ 25) is unverified — n=2 stated only.
   (b) [concrete]
   (c) exact-tier, exhaustive for n=2. -/
-- `p2_c9` is now proved in `BilinearComplexity.P2MovingTriad`.

/- (a) Any cyclically symmetric rank-23 decomposition of `⟨3,3,3⟩`/F₂
   (an order-3 term permutation π intertwining the `cyc` rotation, which
   fixes `matMulTensor` on the nose) has at least TWO π-fixed triads —
   23 ≡ 2 mod 3 forces ≥ 2 diagonal terms, versus exactly 1 for Strassen
   (7 ≡ 1 mod 6-orbits, cache EXACT) and 1 for Smirnov-1 (25 ≡ 1 mod 3,
   cache) — and at least one of them has an invertible u-factor, as in
   both known cases (probe: Smirnov-1's fixed triad is `vec(I₃)^⊗3`).
   The invertibility clause is the killable content beyond counting.
   (b) [concrete]
   (c) invertibility clause extrapolates from 2 data points; Smirnov-1
   is lower-bound-tier. -/
theorem p2_c10 (u v w : Fin 23 → Fin (3 * 3) → ZMod 2) (π : Equiv.Perm (Fin 23))
    (hπ : π ^ 3 = 1)
    (hdec : matMulTensor (ZMod 2) 3 3 3 = fun i j l => ∑ s, u s i * v s j * w s l)
    (hsym : ∀ s, u (π s) = v s ∧ v (π s) = w s ∧ w (π s) = u s) :
    ∃ s t, s ≠ t ∧ π s = s ∧ π t = t ∧
      (IsUnit (matOf (u s)) ∨ IsUnit (matOf (u t))) := sorry

end P2Sweep
end BilinearComplexity
