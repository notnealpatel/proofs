import Combinatorics.PermutationEndpointProfileFinite
import Combinatorics.PermutationEndpointProfileReversal

set_option autoImplicit false

namespace Flex86E1Finite

attribute [local instance] Classical.propDecidable

open PermutationOrderCounting
open PermutationEndpointProfile (reversePositions reversePositions_involutive)

/-- The increasing-position prefix inclusion into a word of length `s+1`. -/
def prefixPos {s k : ℕ} (hk : k ≤ s + 1) (i : Fin k) : Fin (s + 1) :=
  Fin.castLE hk i

example {s k : ℕ} (hk : k ≤ s + 1) (i : Fin k) : (prefixPos hk i).val = i.val := rfl

/-- The increasing-position suffix inclusion, not a reversed suffix. -/
def suffix {s k : ℕ} (hk : k ≤ s + 1) (i : Fin k) : Fin (s + 1) :=
  (prefixPos hk i.rev).rev

/-- The suffix index is the usual offset `s+1-k+i`. -/
theorem suffix_val {s k : ℕ} (hk : k ≤ s + 1) (i : Fin k) :
    (suffix hk i).val = (s + 1 - k) + i.val := by
  simp only [suffix, prefixPos, Fin.val_rev, Fin.val_castLE]
  have hi := i.isLt
  omega

/-- Actual equality of all strict comparisons of the first `k` entries of
`alpha` and the last `k` entries of `beta`, in increasing position order. -/
def PairOverlap {s k : ℕ} (hk : k ≤ s + 1)
    (alpha beta : Equiv.Perm (Fin (s + 1))) : Prop :=
  ∀ i j : Fin k, alpha (prefixPos hk i) < alpha (prefixPos hk j) ↔
    beta (suffix hk i) < beta (suffix hk j)

example {s k : ℕ} (hk : k ≤ s + 1) :
    PairOverlap hk (Equiv.refl _) (Equiv.refl _) := by
  intro i j
  change i.val < j.val ↔ (suffix hk i).val < (suffix hk j).val
  rw [suffix_val, suffix_val]
  omega

/-- Compatibility at cutoff `s+2`: exclude exactly the lengths `2 ≤ k < s+2`.
Each of the two words has length `s+1`, and their total boundary is `2s+2`. -/
def Compatible {s : ℕ} (alpha beta : Equiv.Perm (Fin (s + 1))) : Prop :=
  ∀ k, (h₂ : 2 ≤ k) → (hk : k < s + 2) →
    ¬ PairOverlap (by omega : k ≤ s + 1) alpha beta

example : Compatible (Equiv.refl (Fin 2)) Fin.revPerm := by
  intro k h₂ hk h
  have hke : k = 2 := by omega
  subst k
  have hh := h (0 : Fin 2) (1 : Fin 2)
  norm_num [prefixPos, suffix, Fin.revPerm, Fin.rev] at hh

/-- Actual endpoint-rank fibers: first rank `r` in the left word and last
rank `t` in the right word. Permutation values already are standardized ranks. -/
abbrev EndpointPairs (s : ℕ) (r t : Fin (s + 1)) :=
  FixedFirst (0 : Fin (s + 1)) r × FixedFirst (0 : Fin (s + 1)).rev t

example (s : ℕ) (r t : Fin (s + 1)) : Nonempty (EndpointPairs s r t) :=
  let ⟨a⟩ := fixedFirst_nonempty (0 : Fin (s + 1)) r
  let ⟨b⟩ := fixedFirst_nonempty (0 : Fin (s + 1)).rev t
  ⟨(a, b)⟩

/-- Every first-rank fiber has exactly `s!` patterns. -/
theorem card_firstFiber (s : ℕ) (r : Fin (s + 1)) :
    Fintype.card (FixedFirst (0 : Fin (s + 1)) r) = s.factorial := by
  simpa using card_fixedFirst (0 : Fin (s + 1)) r

/-- Every last-rank fiber has exactly `s!` patterns, at the actual last position. -/
theorem card_lastFiber (s : ℕ) (t : Fin (s + 1)) :
    Fintype.card (FixedFirst (0 : Fin (s + 1)).rev t) = s.factorial := by
  simpa using card_fixedFirst (0 : Fin (s + 1)).rev t

/-- Each joint endpoint-rank fiber contains exactly `(s!)²` pairs. -/
theorem card_endpointPairs (s : ℕ) (r t : Fin (s + 1)) :
    Fintype.card (EndpointPairs s r t) = s.factorial ^ 2 := by
  rw [Fintype.card_prod, card_firstFiber, card_lastFiber, pow_two]

/-- The actual compatible pairs in a prescribed joint endpoint-rank fiber. -/
abbrev CompatiblePairs (s : ℕ) (r t : Fin (s + 1)) :=
  {p : EndpointPairs s r t // Compatible p.1.val p.2.val}

example : Nonempty (CompatiblePairs 1 0 0) := by
  refine ⟨⟨(⟨Equiv.refl _, rfl⟩, ⟨Fin.revPerm, rfl⟩), ?_⟩⟩
  intro k h₂ hk h
  have hke : k = 2 := by omega
  subst k
  have hh := h (0 : Fin 2) (1 : Fin 2)
  norm_num [prefixPos, suffix, Fin.revPerm, Fin.rev] at hh

/-- Reversal of the whole boundary sends `(alpha,beta)` to `(rev beta,rev alpha)`
and preserves the actual block-comparison overlap event. -/
theorem pairOverlap_reverse_iff {s k : ℕ} (hk : k ≤ s + 1)
    (alpha beta : Equiv.Perm (Fin (s + 1))) :
    PairOverlap hk (reversePositions beta) (reversePositions alpha) ↔
      PairOverlap hk alpha beta := by
  have forward (a b : Equiv.Perm (Fin (s + 1))) (h : PairOverlap hk a b) :
      PairOverlap hk (reversePositions b) (reversePositions a) := by
    intro i j
    simpa only [reversePositions, Equiv.trans_apply, Fin.revPerm_apply,
      suffix, Fin.rev_rev] using (h i.rev j.rev).symm
  constructor
  · intro h
    simpa only [reversePositions_involutive alpha, reversePositions_involutive beta] using
      forward (reversePositions beta) (reversePositions alpha) h
  · exact forward alpha beta

/-- Whole-boundary position reversal preserves compatibility, with no value complement. -/
theorem compatible_reverse_iff {s : ℕ} (alpha beta : Equiv.Perm (Fin (s + 1))) :
    Compatible (reversePositions beta) (reversePositions alpha) ↔ Compatible alpha beta := by
  unfold Compatible
  simp only [pairOverlap_reverse_iff]

/-- Reverse positions in both words and exchange the words; endpoint ranks swap. -/
def endpointReverse {s : ℕ} {r t : Fin (s + 1)}
    (p : EndpointPairs s r t) : EndpointPairs s t r :=
  (⟨reversePositions p.2.val, p.2.property⟩,
   ⟨reversePositions p.1.val, by
      change p.1.val (0 : Fin (s + 1)).rev.rev = r
      simpa only [Fin.rev_rev] using p.1.property⟩)

example {s : ℕ} {r t : Fin (s + 1)} (p : EndpointPairs s r t) :
    (endpointReverse p).1.val = reversePositions p.2.val := rfl

/-- Reversing a boundary twice recovers the original endpoint pair. -/
theorem endpointReverse_twice {s : ℕ} {r t : Fin (s + 1)}
    (p : EndpointPairs s r t) : endpointReverse (endpointReverse p) = p := by
  apply Prod.ext
  · exact Subtype.ext (reversePositions_involutive p.1.val)
  · exact Subtype.ext (reversePositions_involutive p.2.val)

/-- Position reversal bijects the actual compatible pairs with ranks `(r,t)`
with those with ranks `(t,r)`. -/
def compatibleReverseEquiv (s : ℕ) (r t : Fin (s + 1)) :
    CompatiblePairs s r t ≃ CompatiblePairs s t r where
  toFun p := ⟨endpointReverse p.val,
    (compatible_reverse_iff p.val.1.val p.val.2.val).mpr p.property⟩
  invFun p := ⟨endpointReverse p.val,
    (compatible_reverse_iff p.val.1.val p.val.2.val).mpr p.property⟩
  left_inv p := Subtype.ext (endpointReverse_twice p.val)
  right_inv p := Subtype.ext (endpointReverse_twice p.val)

example (s : ℕ) (r t : Fin (s + 1)) (p : CompatiblePairs s r t) :
    ((compatibleReverseEquiv s r t) p).val = endpointReverse p.val := rfl

/-- Actual compatible-pair count divided by the full endpoint-fiber size `(s!)²`.
The factorial denominator is strictly positive at every natural `s`. -/
noncomputable def coefficient (s : ℕ) (r t : Fin (s + 1)) : ℝ := by
  classical
  exact (Fintype.card (CompatiblePairs s r t) : ℝ) / (s.factorial : ℝ) ^ 2

example (r t : Fin 2) : coefficient 1 r t =
    (Fintype.card (CompatiblePairs 1 r t) : ℝ) := by
  classical
  simp [coefficient]

/-- The actual normalized compatible-pair counts lie between zero and one. -/
theorem coefficient_bounds (s : ℕ) (r t : Fin (s + 1)) :
    0 ≤ coefficient s r t ∧ coefficient s r t ≤ 1 := by
  classical
  have hd : 0 < (s.factorial : ℝ) ^ 2 := by positivity
  have hc : Fintype.card (CompatiblePairs s r t) ≤ s.factorial ^ 2 := by
    exact (Fintype.card_subtype_le _).trans_eq (card_endpointPairs s r t)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hd.le
  · unfold coefficient
    apply (div_le_one hd).mpr
    exact_mod_cast hc

/-- The actual coefficient matrix is symmetric by position reversal, not raw exchange. -/
theorem coefficient_symm (s : ℕ) (r t : Fin (s + 1)) :
    coefficient s r t = coefficient s t r := by
  classical
  unfold coefficient
  rw [Fintype.card_congr (compatibleReverseEquiv s r t)]

/-- The word length and total boundary specialize to `K-1` and `2K-2`. -/
theorem cutoff_dimensions (K : ℕ) (hK : 3 ≤ K) :
    (K - 2) + 1 = K - 1 ∧ 2 * ((K - 2) + 1) = 2 * K - 2 := by
  omega

example : 3 ≤ 3 ∧ (3 - 2) + 1 = 2 ∧ 2 * ((3 - 2) + 1) = 4 := by decide

/-- With `s=K-2` and `K≥3`, compatibility excludes exactly `2 ≤ k < K`
on two actual words of length `(K-2)+1 = K-1`. -/
theorem compatible_cutoff (K : ℕ) (hK : 3 ≤ K)
    (alpha beta : Equiv.Perm (Fin ((K - 2) + 1))) :
    Compatible alpha beta ↔
      ∀ k, (h₂ : 2 ≤ k) → (hk : k < K) →
        ¬ PairOverlap (by omega : k ≤ (K - 2) + 1) alpha beta := by
  constructor
  · intro h k h₂ hk
    exact h k h₂ (by omega)
  · intro h k h₂ hk
    exact h k h₂ (by omega)

/-- The usual degree-`s` Bernstein basis; the rank index ensures `r ≤ s`. -/
def bernsteinBasis (s : ℕ) (r : Fin (s + 1)) (x : ℝ) : ℝ :=
  (s.choose r.val : ℝ) * x ^ r.val * (1 - x) ^ (s - r.val)

example (x : ℝ) : bernsteinBasis 0 0 x = 1 := by simp [bernsteinBasis]
example (x : ℝ) : bernsteinBasis 1 0 x = 1 - x := by simp [bernsteinBasis]
example (x : ℝ) : bernsteinBasis 1 1 x = x := by simp [bernsteinBasis]

/-- The explicit tensor Bernstein polynomial at cutoff `K`, with `s=K-2`,
actual compatible-pair coefficients, and total boundary size `2K-2` for `K≥3`.
Its definition is a real polynomial expression on the whole plane. -/
noncomputable def BernsteinQK (K : ℕ) (x y : ℝ) : ℝ :=
  ∑ r : Fin ((K - 2) + 1), ∑ t : Fin ((K - 2) + 1),
    coefficient (K - 2) r t * bernsteinBasis (K - 2) r x * bernsteinBasis (K - 2) t y

example (K : ℕ) (x y : ℝ) : BernsteinQK K x y =
    ∑ r : Fin ((K - 2) + 1), ∑ t : Fin ((K - 2) + 1),
      coefficient (K - 2) r t *
        ((Nat.choose (K - 2) r.val : ℝ) * x ^ r.val * (1 - x) ^ (K - 2 - r.val)) *
        ((Nat.choose (K - 2) t.val : ℝ) * y ^ t.val * (1 - y) ^ (K - 2 - t.val)) := rfl

/-- The actual finite Bernstein polynomial is symmetric on the whole real plane. -/
theorem BernsteinQK_symm (K : ℕ) (x y : ℝ) : BernsteinQK K x y = BernsteinQK K y x := by
  unfold BernsteinQK
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro r hr
  rw [coefficient_symm (K - 2) r t]
  ring

end Flex86E1Finite
