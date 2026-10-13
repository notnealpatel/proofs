import Enumerative.GreedyQuasiBarrycadeData

/-!
# Stable finite certificates for the first five greedy rows

These bounded checks certify finite prefixes only. Acceptance includes a
triangular-gap certificate whose soundness excludes the entire earlier-row tail;
it is not membership testing in a truncated list of forbidden sums.
The rejection search bound 20 supplies witnesses, not an approximation to the rule.
The finite computation is isolated from the downstream infinite-tail bridge.
-/

set_option autoImplicit false

namespace GreedyQuasiBarrycade

/-- Finite certificate for a single exceptional-prefix entry: positive and
unused, avoiding the earlier finite exceptions and entire infinite tails,
with every smaller positive candidate either used or explicitly forbidden. -/
def FiniteCertificate (r n : ℕ) : Prop :=
  let a := explicitTable r n
  let x := partialSum (explicitTable r) n + a
  0 < a ∧
  (∀ m ∈ Finset.range n, explicitTable r m ≠ a) ∧
  (∀ i ∈ Finset.range r,
    (∀ k ∈ Finset.range (rowPrefix i).length, 0 < k →
      partialSum (explicitTable i) k ≠ x) ∧ TailAvoid i x) ∧
  ∀ b ∈ Finset.range a, 0 < b →
    (∃ m ∈ Finset.range n, explicitTable r m = b) ∨
    (∃ i ∈ Finset.range r, ∃ k ∈ Finset.range 20,
      0 < k ∧ partialSum (explicitTable i) k =
        partialSum (explicitTable r) n + b)

instance (r n : ℕ) : Decidable (FiniteCertificate r n) := by
  unfold FiniteCertificate
  infer_instance

example : FiniteCertificate 2 0 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-checked finite certificates for every exceptional-prefix entry
of the first five displayed rows. Every smaller positive candidate is checked. -/
theorem finite_certificates :
    ∀ r ∈ Finset.range 5, ∀ n ∈ Finset.range (rowPrefix r).length,
      FiniteCertificate r n := by
  decide

/-- A finite prefix certificate proves the exact unbounded greedy rule
at that entry, using the triangular-gap theorem for every earlier tail index. -/
theorem finiteCertificate_greedy (r n : ℕ) (hr : r < 5)
    (hc : FiniteCertificate r n) :
    Admissible explicitTable r n (explicitTable r n) ∧
    ∀ b, Admissible explicitTable r n b → explicitTable r n ≤ b := by
  rcases hc with ⟨hpos, hunused, havoid, hreject⟩
  constructor
  · refine ⟨hpos, ?_, ?_⟩
    · intro m hm
      exact hunused m (Finset.mem_range.mpr hm)
    · intro i hi k hk
      have hcert := havoid i (Finset.mem_range.mpr hi)
      by_cases hcut : (rowPrefix i).length ≤ k
      · exact tailAvoid_ne i _ k (Nat.lt_trans hi hr) hk hcut hcert.2
      · exact hcert.1 k (Finset.mem_range.mpr (by omega)) hk
  · intro b hb
    by_contra hnot
    have hsmall : b < explicitTable r n := by omega
    rcases hreject b (Finset.mem_range.mpr hsmall) hb.1 with
      ⟨m, hm, heq⟩ | ⟨i, hi, k, hk, hkpos, heq⟩
    · exact hb.2.1 m (Finset.mem_range.mp hm) heq
    · exact hb.2.2 i (Finset.mem_range.mp hi) k hkpos heq

end GreedyQuasiBarrycade
