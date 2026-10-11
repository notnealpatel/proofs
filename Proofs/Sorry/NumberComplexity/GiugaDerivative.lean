/- The archived open converse of Lava’s conjecture and its dependent equivalence.
These are not completed results; the converse retains its original admission. -/
import NumberComplexity.GiugaDerivative

set_option autoImplicit false

namespace GiugaDerivative

/-! ## The open half, archived -/

/-- **The open half of Lava's conjecture (A007850) — the ONE intended sorry.**

Verbatim conjecture: "Giuga numbers are the solution of the differential
equation n' = n + 1" (Paolo P. Lava, Nov 16 2009).  This direction — every
Giuga number satisfies `n' = n + 1` — is the open content.  Grau–Oller-Marcén
(arXiv:1103.2298) prove `IsGiuga n ↔ ∃ a > 0, ad n = a·n + 1`; what is open is
that the multiplier `a` is always `1`, equivalently that every Giuga number
satisfies `Σ_{p ∣ n} 1/p − 1/n = 1`.  A counterexample must have more than 59
prime factors (Grau–Oller-Marcén, citing Borwein–Wong 1997).  The statement
holds for every Giuga number with at most 8 prime factors: Schneider's
exhaustive search reports "There are no other Giuga numbers with 8 or fewer
prime factors" (A007850 comment, Jul 04 2006), and Grau–Oller-Marcén confirm
the thirteen known Giuga numbers satisfy `n' = n + 1`.  Archived, not
attempted. -/
theorem ad_eq_succ_of_isGiuga {n : ℕ} (h : IsGiuga n) : ad n = n + 1 := by
  sorry

/-- **Lava's conjecture (A007850), stated as the biconditional the OEIS
comment asserts.**  The `←` direction is the sorry-free
`isGiuga_of_ad_eq_succ`; the `→` direction is the archived open half, so this
statement's axiom report includes `sorryAx` by design — it is the conjecture,
not a result.  No `1 < n` guard is needed: for `n ∈ {0, 1}` both sides are
false (`IsGiuga` requires `1 < n`; `ad 0 = 0 ≠ 1` and `ad 1 = 0 ≠ 2`). -/
theorem lava_conjecture (n : ℕ) : IsGiuga n ↔ ad n = n + 1 :=
  ⟨ad_eq_succ_of_isGiuga, isGiuga_of_ad_eq_succ⟩

end GiugaDerivative
