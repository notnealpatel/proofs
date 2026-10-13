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
  Comments: emil467q (post 1912) reports a shallow search from 10¹⁰
  to 10¹¹, not a certified exclusion; Dogmachine (post 3775) explicitly
  describes the 10¹⁰ discussion as heuristic. No rigorous exclusion
  bound is certified by these comments;
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
    emil467q reports a shallow search from 10¹⁰ to 10¹¹ (post 1912);
    Dogmachine explicitly describes the 10¹⁰ discussion as heuristic
    (post 3775). These comments certify no rigorous exclusion bound.
    Heuristics suggest any example is enormous (double-digit digit-count
    beyond the classical 78557). -/
theorem erdos_203 : ∃ m : ℕ, IsTwoDimSierpinski m := by
  sorry

/-- The 1D link — sanity for the definition shape: a 2D Sierpiński
    number is in particular a classical Sierpiński number (take
    `ℓ = 0`), in the repo's `IsSierpinskiNumber` sense.
    Oddness follows from coprimality with 6; `1 ≤ m` supplies the
    strict lower bound in `Composite`. The hypothesis's satisfiability
    remains the open existence question #203. -/
theorem twoDim_is_sierpinski (m : ℕ) (h : IsTwoDimSierpinski m) :
    Erdos.Covering.IsSierpinskiNumber m := by
  have hc2 : Nat.Coprime m 2 := h.2.1.of_dvd_right (by decide)
  refine ⟨Nat.prime_two.coprime_iff_not_dvd.mp hc2.symm, ?_⟩
  intro n
  have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hprod : 1 ≤ m * 2 ^ n := Nat.mul_le_mul h.1 hp
  refine ⟨by omega, ?_⟩
  simpa only [pow_zero, mul_one, Nat.mul_comm] using h.2.2 n 0

/-- Non-degeneracy of the coprimality guard: `m = 78557` (the
    classical Sierpiński number, odd but ≡ 2 mod 3 — coprime to 6!)
    FAILS the 2D property: `2·3²·78557 + 1 = 1414027` is prime
    (AnimishSharma's comment; verify independently).  So the 2D
    problem is strictly harder than 1D and the classical witness does
    not transfer. Primality and coprimality are kernel-checked by
    `norm_num`. -/
theorem coprime_78557_prime_witness :
    Nat.Coprime 78557 6 ∧ (2 ^ 1 * 3 ^ 2 * 78557 + 1).Prime := by
  norm_num

/-- The classical witness `78557` is not a two-dimensional Sierpiński
    number: the exponents `(1, 2)` give a prime. -/
theorem not_twoDim_78557 : ¬ IsTwoDimSierpinski 78557 := by
  intro h
  exact h.2.2 1 2 coprime_78557_prime_witness.2

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
   - Dogmachine's heuristic 10^10 discussion (post 3775) and emil467q's
     shallow search from 10^10 to 10^11 (post 1912) certify no rigorous
     exclusion bound. The earlier endorsement of an unqualified bound was
     overstated; the commentary above now records the search's limitations.
     AnimishSharma's density obstruction remains comment-sourced.
-/
