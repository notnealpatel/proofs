/-
  Scratch/Sweep/P2_RankCalculus — calibration conjecture sweep (pair P2,
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

  Every statement is `sorry`; a later stage elaborates/attacks them.
  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.ZMod.Basic
import Proofs.BilinearComplexity.RankCalculus

namespace BilinearComplexity
namespace P2Sweep

open Matrix

/-! ### Local vocabulary (new definitions, no collisions with Proofs/Xlib) -/

/-- Kronecker product of matrices, packed row-major by `finProdFinEquiv`
(first component slow), matching the packing of `matMulTensor` and `kron`. -/
def matKron {k : Type*} [Mul k] {a b a' b' : ℕ} (M : Matrix (Fin a) (Fin b) k)
    (N : Matrix (Fin a') (Fin b') k) : Matrix (Fin (a * a')) (Fin (b * b')) k :=
  fun i j => M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    * N (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

/-- A single rank-one triad `u ⊗ v ⊗ w`. -/
def triad {k : Type*} [Mul k] {a b c : ℕ} (u : Fin a → k) (v : Fin b → k)
    (w : Fin c → k) : Tensor k a b c := fun i j l => u i * v j * w l

/-- Simultaneous contraction of all three modes — the group action whose
stabilizers `stab_residual` reasons about. -/
def sandwich {k : Type*} [CommSemiring k] {a b c : ℕ}
    (M₁ : Matrix (Fin a) (Fin a) k) (M₂ : Matrix (Fin b) (Fin b) k)
    (M₃ : Matrix (Fin c) (Fin c) k) (T : Tensor k a b c) : Tensor k a b c :=
  contract₁ M₁ (contract₂ M₂ (contract₃ M₃ T))

/-- Unpack a mode vector of `matMulTensor k n n n` into an `n × n` matrix
(row-major, first component slow). -/
def matOf {k : Type*} {n : ℕ} (x : Fin (n * n) → k) : Matrix (Fin n) (Fin n) k :=
  fun i j => x (finProdFinEquiv (i, j))

/-- The vectorized identity matrix, `vec(Iₙ)` in row-major packing. -/
def vecI (k : Type*) [Zero k] [One k] (n : ℕ) : Fin (n * n) → k :=
  fun x => if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm x).2 then 1 else 0

/-- The identity triad `vec(Iₙ) ⊗ vec(Iₙ) ⊗ vec(Iₙ)` — the distinguished
symmetry-fixed term of both the Strassen and Smirnov-1 decompositions. -/
def identityTriad (k : Type*) [CommSemiring k] (n : ℕ) :
    Tensor k (n * n) (n * n) (n * n) :=
  triad (vecI k n) (vecI k n) (vecI k n)

/-- Infinitesimal (Lie-algebra) stabilizer condition: `(X₁,X₂,X₃)` is a
derivation annihilating `T`. Over F₂ the triple `(α•1, β•1, (α+β)•1)`
satisfies this for every tensor — the 2-dimensional trivial space. -/
def InfStab {k : Type*} [CommSemiring k] {a b c : ℕ}
    (X₁ : Matrix (Fin a) (Fin a) k) (X₂ : Matrix (Fin b) (Fin b) k)
    (X₃ : Matrix (Fin c) (Fin c) k) (T : Tensor k a b c) : Prop :=
  ∀ i j l, (∑ i', X₁ i i' * T i' j l) + (∑ j', X₂ j j' * T i j' l)
    + (∑ l', X₃ l l' * T i j l') = 0

/-! ### Conjectures -/

/- (a) The de-Groote-style sandwich `(P,Q,R) ↦ (P⊗⅟Qᵀ, Q⊗⅟Rᵀ, R⊗⅟Pᵀ)`
   fixes `matMulTensor` — the licensing lemma behind every orbit count in
   burnside_n3.sage and compute_stabilizers.sage; verified exhaustively for
   n=2 over F₂ (all 168² = 216 GL(2,2)³ triples, probe 2026-07-19) and
   implicitly by every verified decomposition-stabilizer computation.
   (b) [concrete]
   (c) exact-tier data only. -/
theorem p2_c1 {k : Type*} [CommSemiring k] {a b c : ℕ}
    (P : Matrix (Fin a) (Fin a) k) (Q : Matrix (Fin b) (Fin b) k)
    (R : Matrix (Fin c) (Fin c) k) [Invertible P] [Invertible Q] [Invertible R] :
    sandwich (matKron P (⅟Q)ᵀ) (matKron Q (⅟R)ᵀ) (matKron R (⅟P)ᵀ)
      (matMulTensor k a b c) = matMulTensor k a b c := sorry

/- (a) Stabilizers multiply under Kronecker product: the mode-wise
   `matKron` of a stabilizing triple of `T` and one of `T'` stabilizes
   `kron T T'` — licenses orbit reduction for `⟨9,9,9⟩ = ⟨3,3,3⟩⊗⟨3,3,3⟩`
   searches; grounded in the pipeline's pervasive use of
   `tensor_product` to build the acting group.
   (b) [concrete]
   (c) exact-tier. -/
theorem p2_c2 {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}
    (M₁ : Matrix (Fin a) (Fin a) k) (M₂ : Matrix (Fin b) (Fin b) k)
    (M₃ : Matrix (Fin c) (Fin c) k) (N₁ : Matrix (Fin a') (Fin a') k)
    (N₂ : Matrix (Fin b') (Fin b') k) (N₃ : Matrix (Fin c') (Fin c') k)
    (T : Tensor k a b c) (T' : Tensor k a' b' c')
    (hT : sandwich M₁ M₂ M₃ T = T) (hT' : sandwich N₁ N₂ N₃ T' = T') :
    sandwich (matKron M₁ N₁) (matKron M₂ N₂) (matKron M₃ N₃) (kron T T')
      = kron T T' := sorry

/- (a) No nonzero rank-1 tensor is fixed by the whole stabilizer of
   `⟨n,n,n⟩` over F₂: exhaustive for n=2 (all 3375 nonzero triads, min
   Aut-orbit size 27 in residual_aut_cascade.sage); for n=3 the sandwich
   action has trivial common fixed space on each mode (probe). So full-group
   orbit reduction via `stab_residual` necessarily degrades after one peel.
   FLAG: n ≥ 4 is extrapolation beyond the data.
   (b) [concrete]
   (c) exact-tier for n=2,3; extrapolated beyond. -/
theorem p2_c3 (n : ℕ) (hn : 2 ≤ n) (u v w : Fin (n * n) → ZMod 2)
    (ht : triad u v w ≠ 0) :
    ∃ (M₁ M₂ M₃ : Matrix (Fin (n * n)) (Fin (n * n)) (ZMod 2)),
      IsUnit M₁ ∧ IsUnit M₂ ∧ IsUnit M₃ ∧
      sandwich M₁ M₂ M₃ (matMulTensor (ZMod 2) n n n) = matMulTensor (ZMod 2) n n n ∧
      sandwich M₁ M₂ M₃ (triad u v w) ≠ triad u v w := sorry

/- (a) The diagonal sandwich `(P,P,P)` fixes the residual
   `⟨n,n,n⟩ − vec(I)⊗vec(I)⊗vec(I)`: the Strassen stabilizer (order 36,
   EXACT, cache) fixes its identity triad (orbit size 1, probe: orbit of
   `vec(I)^⊗3` has size 36, stabilizer order 12 ⊇ diagonal GL(2,2));
   Smirnov-1's C₃-fixed triad is also exactly `vec(I₃)^⊗3` (probe, det 1).
   This is the concrete `stab_residual` instance at peel step 1 of an
   identity-triad-first search.
   (b) [concrete]
   (c) Smirnov-1 evidence is lower-bound-tier (C₃ only); Strassen exact. -/
theorem p2_c4 {k : Type*} [CommRing k] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) k) [Invertible P] :
    sandwich (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ)
        (matMulTensor k n n n - identityTriad k n)
      = matMulTensor k n n n - identityTriad k n := sorry

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
theorem p2_c8 (u v w : Fin (3 * 3) → ZMod 2) :
    ∃ (X₁ X₂ X₃ : Matrix (Fin (3 * 3)) (Fin (3 * 3)) (ZMod 2)),
      InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 3 3 3 - triad u v w) ∧
      ¬ ∃ α β : ZMod 2, X₁ = α • 1 ∧ X₂ = β • 1 ∧ X₃ = (α + β) • 1 := sorry

/- (a) …but the infinitesimal stabilizer never survives a peel intact:
   for every nonzero rank-1 `t`, some derivation of `⟨2,2,2⟩`/F₂ fails on
   the residual. Exhaustive: residual Lie dims are 3–10 across all 21
   orbits, strictly below dim 11 of `T` itself (residual_aut_cascade.sage);
   `Lie(T) ⊆ Lie(T−t)` would force dim ≥ 11. The n=3 analogue (26 vs
   sampled ≤ 25) is unverified — n=2 stated only.
   (b) [concrete]
   (c) exact-tier, exhaustive for n=2. -/
theorem p2_c9 (u v w : Fin (2 * 2) → ZMod 2) (ht : triad u v w ≠ 0) :
    ∃ (X₁ X₂ X₃ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) (ZMod 2)),
      InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 2 2 2) ∧
      ¬ InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 2 2 2 - triad u v w) := sorry

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
