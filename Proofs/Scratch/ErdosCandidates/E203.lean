/-
  Erdős Problem #203 — Sierpiński numbers coprime to 6 (two-dimensional
  Sierpiński problem).
  Status: open.  Tier UB archive target.

  Verbatim statement (`goof erdos fetch 203`, pulled 2026-08-05):

    "Is there an integer $m\geq 1$ with $(m,6)=1$ such that none of
    $2^k3^\ell m+1$ are prime, for any $k,\ell\geq 0$?"

  DB remarks: with only powers of 2 these are Sierpiński numbers (see
  #1113).  Erdős–Graham also ask about p₁^{k₁}⋯p_r^{k_r}m + 1 and about
  q₁⋯q_r m + 1 with q_i ≡ 1 (mod 4) (the latter trivially m = 1,
  noted by Dogmachine — a condition like m even is presumably meant).
  Comments: no such m up to 10¹¹ (emil467q searched 10¹⁰–10¹¹);
  AnimishSharma (Jun 2026, comment-sourced): |⟨2,3⟩ ≤ (ℤ/p)^×| =
  lcm(ord_p 2, ord_p 3) and the covering-density necessary condition
  ∑_{p∈P} 1/|H_p| ≥ 1 for any finite covering set; small-lcm coverings
  ruled out computationally.

  Audit verdict (candidates doc): archive only — the 2-generator
  subgroup structure is genuinely different from the repo's 1D covering
  lane; no decidable fragment in reach.  Worth stating as the exact 2D
  generalization of `Proofs/Erdos/Covering/Sierpinski.lean`.

  Mathlib inventory: `Nat.Coprime`, `Nat.Prime`; repo:
  `Erdos.Covering.IsSierpinskiNumber` for the 1D link.
-/
import Mathlib
import Erdos.Covering.Sierpinski

set_option autoImplicit false

namespace ErdosCandidates.E203

/-- `IsTwoDimSierpinski m`: `m ≥ 1`, coprime to 6, and `2^k·3^ℓ·m + 1`
    is never prime. -/
def IsTwoDimSierpinski (m : ℕ) : Prop :=
  1 ≤ m ∧ Nat.Coprime m 6 ∧
    ∀ k ℓ : ℕ, ¬ (2 ^ k * 3 ^ ℓ * m + 1).Prime

/-- **Erdős #203 (OPEN)**: does a 2-dimensional Sierpiński number
    coprime to 6 exist?

    Source text: "Is there an integer $m\geq 1$ with $(m,6)=1$ such
    that none of $2^k3^\ell m+1$ are prime, for any $k,\ell\geq 0$?"
    No such m up to 10¹¹ (comment-sourced search); heuristics suggest
    any example is enormous (double-digit digit-count beyond the
    classical 78557). -/
theorem erdos_203 : ∃ m : ℕ, IsTwoDimSierpinski m := by
  sorry

/-- The 1D link — sanity for the definition shape: a 2D Sierpiński
    number is in particular a classical Sierpiński number (take
    `ℓ = 0`), in the repo's `IsSierpinskiNumber` sense.
    -- PROVABLE (definition chase; check the repo def's parity/oddness
    side conditions — `IsSierpinskiNumber` requires odd `k`, and
    `Nat.Coprime m 6` gives oddness).  Non-vacuity guard: the
    hypothesis is satisfiable-in-principle only if the answer to
    #203 is yes; this implication is still contentful as a
    definitional consistency check. -/
theorem twoDim_is_sierpinski (m : ℕ) (h : IsTwoDimSierpinski m) :
    Erdos.Covering.IsSierpinskiNumber m := by
  sorry

/-- Non-degeneracy of the coprimality guard: `m = 78557` (the
    classical Sierpiński number, odd but ≡ 2 mod 3 — coprime to 6!)
    FAILS the 2D property: `2·3²·78557 + 1 = 1414027` is prime
    (AnimishSharma's comment; verify independently).  So the 2D
    problem is strictly harder than 1D and the classical witness does
    not transfer.  -- PROVABLE (norm_num primality certificate). -/
example : Nat.Coprime 78557 6 ∧ (2 ^ 1 * 3 ^ 2 * 78557 + 1).Prime := by
  sorry

/-- **Covering-density necessary condition** (comment-sourced,
    AnimishSharma Jun 2026; elementary and re-derivable): if a finite
    set `P` of primes (none dividing 6) covers the problem for `m` —
    every `2^k 3^ℓ m + 1` is divisible by some `p ∈ P` — then
    `∑_{p ∈ P} 1/|H_p| ≥ 1`, where `H_p = ⟨2, 3⟩ ≤ (ℤ/p)^×` and
    `|H_p| = lcm(ord_p 2, ord_p 3)`.  Stated with `orderOf` in
    `(ZMod p)ˣ`; the multiplicative-order machinery is in Mathlib
    (`ZMod.orderOf_units`, `orderOf`). -/
theorem covering_density_condition (m : ℕ) (hm : IsTwoDimSierpinski m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ 6)
    (hcov : ∀ k ℓ : ℕ, ∃ p ∈ P, (p : ℕ) ∣ 2 ^ k * 3 ^ ℓ * m + 1) :
    1 ≤ ∑ p ∈ P.attach,
      (1 : ℚ) / Nat.lcm (orderOf (2 : ZMod p.1)) (orderOf (3 : ZMod p.1)) := by
  sorry

end ErdosCandidates.E203

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch.
   - IsTwoDimSierpinski faithfully encodes m >= 1, (m,6)=1, and universally
     composite 2^k * 3^l * m + 1.
   - twoDim_is_sierpinski: IsSierpinskiNumber (Sierpinski.lean line 94) requires
     odd k and forall n, Composite(k*2^n+1). Setting l=0 in the 2D property gives
     the 1D statement; Nat.Coprime m 6 implies oddness; the Composite 1< guard
     holds because IsTwoDimSierpinski is vacuously false for m=1 (2 is prime),
     forcing m >= 5. Quantifier structure matches.
   - Arithmetic verified: 2*9*78557+1 = 1414027 is prime (sympy confirmed);
     gcd(78557,6) = 1.
   - covering_density_condition uses orderOf(2 : ZMod p.1) and orderOf(3 : ZMod p.1)
     which give multiplicative orders since p is prime and p does not divide 6;
     Nat.lcm of these matches AnimishSharma's |H_p| = lcm(ord_p 2, ord_p 3).
   - Dogmachine's "no such m up to 10^10", emil467q's 10^10-10^11 search, and
     AnimishSharma's density obstruction all accurately reflected.
-/
