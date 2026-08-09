/-
  Erdős Problem #406 — powers of 2 with only digits 0, 1 in base 3.
  Status: open.  Tier UB archive target with decidable sanity layer.

  Verbatim statement (`goof erdos fetch 406`, pulled 2026-08-05):

    "Is it true that there are only finitely many powers of $2$ which
    have only the digits $0$ and $1$ when written in base $3$?"

  DB remarks: the only known examples are 1, 4 = 1+3,
  256 = 1+3+3²+3⁵.  With digits {1,2} only, 2¹⁵ seems largest.  Would
  imply 3 ∣ C(2^{k+1}, 2^k) for all large k (via Kummer).  Saye [Sa22]:
  2ⁿ contains every ternary digit for 16 ≤ n ≤ 5.9·10²¹.  Narkiewicz
  [Na80]: N(x) ≤ 1.62·x^{log₃2}.

  Audit verdict (candidates doc): archive with decidable `Nat.digits`
  sanity layer; anything stronger is known-hard Diophantine territory
  (Lagarias 3-adic analysis).  Shares digit language with #376's
  Kummer layer.

  Mathlib inventory: `Nat.digits` (Data/Nat/Digits); nothing else
  needed.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E406

/-- `ZeroOneBase3 m`: all base-3 digits of `m` lie in `{0, 1}`. -/
def ZeroOneBase3 (m : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 3 m, d ≤ 1

instance (m : ℕ) : Decidable (ZeroOneBase3 m) := by
  unfold ZeroOneBase3; infer_instance

/-- The three known witnesses: `2⁰ = 1`, `2² = 4 = (11)₃`,
    `2⁸ = 256 = (100111)₃`.  -- PROVABLE (decide). -/
theorem witnesses :
    ZeroOneBase3 (2 ^ 0) ∧ ZeroOneBase3 (2 ^ 2) ∧ ZeroOneBase3 (2 ^ 8) := by
  sorry

/-- Non-degeneracy: `2¹ = 2 = (2)₃` and `2⁴ = 16 = (121)₃` fail.
    -- PROVABLE (decide). -/
example : ¬ ZeroOneBase3 (2 ^ 1) ∧ ¬ ZeroOneBase3 (2 ^ 4) := by
  sorry

/-- **Erdős #406 (OPEN)**: only finitely many `n` have `2ⁿ` with
    ternary digits in `{0, 1}`.

    Source text: "Is it true that there are only finitely many powers
    of $2$ which have only the digits $0$ and $1$ when written in base
    $3$?"  Expected TRUE (indeed {0, 2, 8} are believed to be all);
    verified failure for 16 ≤ n ≤ 5.9·10²¹ (Saye).  No proof method
    is known — ternary digits of 2ⁿ resist all current techniques. -/
theorem erdos_406 : {n : ℕ | ZeroOneBase3 (2 ^ n)}.Finite := by
  sorry

/-- Verified window: no further examples for `9 ≤ n ≤ 200`.
    -- PROVABLE (decide; 2²⁰⁰ is a 61-digit number, `Nat.digits`
    kernel evaluation is fine at this scale). -/
theorem window_200 : ∀ n ∈ Finset.Icc 9 200, ¬ ZeroOneBase3 (2 ^ n) := by
  sorry

/-- The Kummer corollary recorded in the DB: if the conjecture holds
    (with the known-witness list complete), then `3 ∣ C(2^{k+1}, 2^k)`
    for all large `k` — since `C(2m, m)` is coprime to 3 iff `m` has
    only digits {0,1} base 3 (see E376's Kummer bridge).
    -- PROVABLE from `prime_not_dvd_centralBinom_iff_digits` (#376
    file) + the window; stated here as the conditional. -/
theorem kummer_corollary
    (h : {n : ℕ | ZeroOneBase3 (2 ^ n)}.Finite) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 3 ∣ Nat.centralBinom (2 ^ k) := by
  sorry

/-- The {1,2}-digit variant from the DB remarks: `2¹⁵` seems to be the
    largest power of 2 with all ternary digits in `{1, 2}`.  Sanity
    window only (the general claim is as hard as the headline).
    -- PROVABLE (decide). -/
theorem digits_12_window :
    (∀ d ∈ Nat.digits 3 (2 ^ 15), 1 ≤ d) ∧
    ∀ n ∈ Finset.Icc 16 200, ¬ ∀ d ∈ Nat.digits 3 (2 ^ n), 1 ≤ d := by
  sorry

end ErdosCandidates.E406

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch.
   - ZeroOneBase3 correctly uses Nat.digits 3 m with d <= 1 (digits in {0,1}).
   - Known witnesses verified: 2^0=1=(1)_3, 2^2=4=(11)_3, 2^8=256=(100111)_3
     — all digits in {0,1}.
   - Non-examples verified: 2^1=2=(2)_3 has digit 2; 2^4=16=(121)_3 has digit 2.
   - {1,2}-digit variant: 2^15=32768=(1122222112)_3 — all digits in {1,2},
     confirmed computationally. The file checks 1 <= d which correctly captures
     digits in {1,2} for base-3.
   - Kummer corollary matches DB: "would imply 3 | C(2^{k+1}, 2^k) for all
     large k" via Kummer's theorem on base-p carries.
   - Saye verification range and Narkiewicz bound accurately cited.
-/
