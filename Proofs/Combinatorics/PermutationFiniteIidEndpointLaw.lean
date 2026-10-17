import Combinatorics.PermutationFiniteIidTransport
import Combinatorics.PermutationFiniteIidCollision
import Combinatorics.PermutationFiniteIidPattern

set_option autoImplicit false
noncomputable section
namespace PermutationFiniteIidEndpointLaw
open PermutationFiniteWordPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The exact iid avoidance mass equals the sum over actual avoiding patterns. -/
theorem iid_pattern_identity {m n : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n)
    (a b : Fin n) :
    let E := Finset.univ.filter (SampleAvoid (by omega : 0 < m) a b)
    (E.card : ℝ) / (n : ℝ) ^ (2 * (m - 1)) = patternSum m a b := by
  exact FiniteIidPatternRepair.iid_pattern_identity_repaired hm hn a b

/-- Restriction to free boundary labels identifies actual endpoint avoidance
with iid avoidance conditioned on the nonempty good event. -/
theorem actual_good_sample_identity {m n : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hn : 2 * m ≤ n) (q a b : Fin n)
    (hq : q.val + 1 = n) (hab : a ≠ b) :
    let E := Finset.univ.filter (SampleAvoid (by omega : 0 < m) a b)
    let G := Finset.univ.filter (Good (m := m) a b)
    G.Nonempty ∧
      PermutationEndpointProfile.shortFraction (m + 1) q a b =
        ((E ∩ G).card : ℝ) / G.card := by
  exact actual_good_sample_identity_repaired hm hn q a b hq hab

/-- The unconditional bad-sample frequency is bounded by the union of
coordinate collisions and the two anchor hits at each coordinate. -/
theorem bad_sample_bound {m n : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n)
    (a b : Fin n) (hab : a ≠ b) :
    let G := Finset.univ.filter (Good (m := m) a b)
    1 - (G.card : ℝ) / (n : ℝ) ^ (2 * (m - 1)) ≤
      ((Nat.choose (2 * m - 2) 2 : ℝ) + 2 * (2 * m - 2 : ℕ)) / n := by
  exact FiniteIidCollisionRepair.bad_sample_bound_repaired hm hn a b hab

/-- Actual finite endpoint short-avoidance differs from the iid pattern sum
by at most the unconditional coordinate-collision and anchor-hit bound. -/
theorem actual_finite_iid_endpoint_error {m n : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hn : 2 * m ≤ n) (q a b : Fin n)
    (hq : q.val + 1 = n) (hab : a ≠ b) :
    |PermutationEndpointProfile.shortFraction (m + 1) q a b -
      (1 - ∑ k ∈ Finset.Icc 2 m,
        ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k, patternWeight a b σ)| ≤
      ((Nat.choose (2 * m - 2) 2 : ℝ) + 2 * (2 * m - 2 : ℕ)) / n := by
  classical
  let E := Finset.univ.filter (SampleAvoid (by omega : 0 < m) a b)
  let G := Finset.univ.filter (Good (m := m) a b)
  obtain ⟨hg, htransport⟩ := actual_good_sample_identity hm hn q a b hq hab
  have hiid := iid_pattern_identity hm hn a b
  have hbad := bad_sample_bound hm hn a b hab
  have hcompare := finite_conditioning_comparison E G hg
  have hspace : Fintype.card (Fin (2 * (m - 1)) → Fin n) = n ^ (2 * (m - 1)) := by
    simp
  rw [hspace] at hcompare
  simp only [Nat.cast_pow] at hcompare
  change |PermutationEndpointProfile.shortFraction (m + 1) q a b - patternSum m a b| ≤ _
  rw [htransport, ← hiid]
  exact hcompare.trans hbad

example : 2 ≤ (2 : ℕ) ∧ 2 * 2 ≤ (100 : ℕ) ∧
    (99 : Fin 100).val + 1 = 100 ∧ (0 : Fin 100) ≠ 99 ∧
    Nonempty (PermutationEndpointCounting.FixedTwo (0 : Fin 100) 99 0 99) ∧
    ((Nat.choose (2 * 2 - 2) 2 : ℝ) + 2 * (2 * 2 - 2 : ℕ)) / 100 = 5 / 100 ∧
    (5 / 100 : ℝ) < 1 := by
  refine ⟨by decide, by decide, by decide, by decide,
    PermutationEndpointCounting.fixedTwo_nonempty 0 99 0 99 (by decide) (by decide),
    ?_, by norm_num⟩
  norm_num

end PermutationFiniteIidEndpointLaw
