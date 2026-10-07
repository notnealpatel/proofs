/-
Finite three-carry localization of reflection collision energy. No AP-free
hypothesis is needed. This is a counting identity and a lower localization
bound, not an energy upper bound or either open estimate (O)/(C).

Inspired by the finite carry partition in OAI.Erdos3's
`exists_unwrapped_family_reflected_correlation` and `tripleCarry_representative`
(CyclicMixedReflection.lean, source inspected at lines 212ff/247ff). No external
module is imported or theorem ported. Here k = 0,1,2 is the carry of THREE
nonnegative low digits, not a sign reindexing of progression residuals.
-/
import Erdos.Erdos142.ReflectionMassEnergy
import Mathlib.Combinatorics.Pigeonhole

set_option autoImplicit false

open Finset

namespace Erdos142

/-- Ordered collisions `(c,a,a')`: both centres represent the same in-range
reflection target nontrivially. The sigma index retains the exact target. -/
noncomputable def reflectionCollisions (A : Finset ℤ) (N : ℕ) : Finset (Σ _ : ℤ, ℤ × ℤ) :=
  (Ico 0 ((N : ℤ)^2)).sigma fun c =>
    (A.filter (fun a => 2*a-c ∈ A ∧ a ≠ c)) ×ˢ
      (A.filter (fun a => 2*a-c ∈ A ∧ a ≠ c))

/-- The sum of the three integer low digits in a collision. -/
def reflectionLowSum (N : ℕ) (t : Σ _ : ℤ, ℤ × ℤ) : ℤ :=
  t.2.1 % (N : ℤ) + t.2.2 % (N : ℤ) + t.1 % (N : ℤ)

/-- The exact collision slice of low digit z and carry k, with all scalar
membership and nontriviality constraints retained. -/
noncomputable def reflectionCarrySlice (A : Finset ℤ) (N : ℕ) (z : ℤ) (k : Fin 3) :
    Finset (Σ _ : ℤ, ℤ × ℤ) :=
  (reflectionCollisions A N).filter fun t =>
    reflectionLowSum N t = z + (k.val : ℤ) * (N : ℤ)

example (N : ℕ) : reflectionCollisions ∅ N = ∅ := by simp [reflectionCollisions]
example : reflectionLowSum 2 ⟨3, (2, 1)⟩ = 2 := by decide
example (N : ℕ) (z : ℤ) (k : Fin 3) : reflectionCarrySlice ∅ N z k = ∅ := by
  simp [reflectionCarrySlice, reflectionCollisions]

/-- Explicit scalar membership of a collision; the two centres need not be
 distinct from each other, but each differs from the target. -/
theorem mem_reflectionCollisions (A : Finset ℤ) (N : ℕ) (c a b : ℤ) :
    (⟨c, (a,b)⟩ : Σ _ : ℤ, ℤ × ℤ) ∈ reflectionCollisions A N ↔
      0 ≤ c ∧ c < (N : ℤ)^2 ∧
      (a ∈ A ∧ 2*a-c ∈ A ∧ a ≠ c) ∧
      (b ∈ A ∧ 2*b-c ∈ A ∧ b ≠ c) := by
  simp [reflectionCollisions, and_assoc]

/-- Fully scalar membership of a carry slice, including exact range,
nontriviality, and the sum of the three integer remainders. -/
theorem mem_reflectionCarrySlice (A : Finset ℤ) (N : ℕ)
    (z : ℤ) (k : Fin 3) (c a b : ℤ) :
    (⟨c, (a,b)⟩ : Σ _ : ℤ, ℤ × ℤ) ∈ reflectionCarrySlice A N z k ↔
      0 ≤ c ∧ c < (N : ℤ)^2 ∧
      (a ∈ A ∧ 2*a-c ∈ A ∧ a ≠ c) ∧
      (b ∈ A ∧ 2*b-c ∈ A ∧ b ≠ c) ∧
      a % (N : ℤ) + b % (N : ℤ) + c % (N : ℤ) =
        z + (k.val : ℤ)*(N : ℤ) := by
  rw [reflectionCarrySlice, Finset.mem_filter, mem_reflectionCollisions]
  simp only [reflectionLowSum, and_assoc]

/-- Collision cardinality is precisely the existing squared-multiplicity
energy (ordered collisions, including the diagonal a=a'). -/
theorem card_reflectionCollisions (A : Finset ℤ) (N : ℕ) :
    (reflectionCollisions A N).card =
      ∑ c ∈ Ico 0 ((N : ℤ)^2), reflectionMultiplicity A c ^ 2 := by
  simp only [reflectionCollisions, card_sigma, card_product,
    reflectionMultiplicity_eq_card_filter, pow_two]

/-- Three low digits have sum in [0,3N), regardless of scalar range. -/
theorem reflectionLowSum_bounds (N : ℕ) (hN : 0 < N) (t : Σ _ : ℤ, ℤ × ℤ) :
    0 ≤ reflectionLowSum N t ∧ reflectionLowSum N t < 3 * (N : ℤ) := by
  have hp : 0 < (N : ℤ) := by exact_mod_cast hN
  have h1 := Int.emod_nonneg t.2.1 (ne_of_gt hp)
  have h2 := Int.emod_nonneg t.2.2 (ne_of_gt hp)
  have h3 := Int.emod_nonneg t.1 (ne_of_gt hp)
  have h4 := Int.emod_lt_of_pos t.2.1 hp
  have h5 := Int.emod_lt_of_pos t.2.2 hp
  have h6 := Int.emod_lt_of_pos t.1 hp
  dsimp [reflectionLowSum]
  omega

private theorem carry_exists (N : ℕ) (hN : 0 < N) (s : ℤ)
    (hs : 0 ≤ s ∧ s < 3 * (N : ℤ)) :
    ∃ z ∈ Ico 0 (N : ℤ), ∃ k : Fin 3, s = z + (k.val : ℤ)*(N : ℤ) := by
  have hp : 0 < (N : ℤ) := by exact_mod_cast hN
  by_cases h0 : s < (N : ℤ)
  · exact ⟨s, mem_Ico.mpr ⟨hs.1, h0⟩, 0, by simp⟩
  · by_cases h1 : s < 2*(N : ℤ)
    · refine ⟨s-(N : ℤ), mem_Ico.mpr ⟨by omega, by omega⟩, 1, ?_⟩
      norm_num
    · refine ⟨s-2*(N : ℤ), mem_Ico.mpr ⟨by omega, by omega⟩, 2, ?_⟩
      norm_num

private theorem carry_unique (N : ℕ) (z w : ℤ) (k l : Fin 3)
    (hz : z ∈ Ico 0 (N : ℤ)) (hw : w ∈ Ico 0 (N : ℤ))
    (heq : z+(k.val : ℤ)*(N : ℤ) = w+(l.val : ℤ)*(N : ℤ)) :
    z = w ∧ k = l := by
  simp only [mem_Ico] at hz hw
  fin_cases k <;> fin_cases l <;> norm_num at heq ⊢ <;> omega

/-- Each possible three-digit sum occupies exactly one low-digit/carry cell. -/
theorem sum_carry_indicator (N : ℕ) (hN : 0 < N) (s : ℤ)
    (hs : 0 ≤ s ∧ s < 3*(N : ℤ)) :
    (∑ z ∈ Ico 0 (N : ℤ), ∑ k : Fin 3,
      if s = z+(k.val : ℤ)*(N : ℤ) then (1 : ℕ) else 0) = 1 := by
  obtain ⟨z, hz, k, hk⟩ := carry_exists N hN s hs
  rw [sum_eq_single z]
  · rw [sum_eq_single k]
    · simp [hk]
    · intro l hl hne
      have hnot : s ≠ z+(l.val : ℤ)*(N : ℤ) := by
        intro heq
        have hu := carry_unique N z z k l hz hz (hk.symm.trans heq)
        exact hne hu.2.symm
      simp [hnot]
    · simp
  · intro w hw hne
    apply sum_eq_zero
    intro l hl
    have hnot : s ≠ w+(l.val : ℤ)*(N : ℤ) := by
      intro heq
      have hu := carry_unique N z w k l hz hw (hk.symm.trans heq)
      exact hne hu.1.symm
    simp [hnot]
  · exact fun hn => False.elim (hn hz)

/-- Exact local energy partition into N low digits and three carries. No
AP-free or positive-energy assumption is used. -/
theorem reflection_energy_eq_sum_carry (A : Finset ℤ) (N : ℕ) (hN : 0 < N) :
    (∑ c ∈ Ico 0 ((N : ℤ)^2), reflectionMultiplicity A c ^ 2) =
      ∑ z ∈ Ico 0 (N : ℤ), ∑ k : Fin 3, (reflectionCarrySlice A N z k).card := by
  rw [← card_reflectionCollisions]
  simp only [reflectionCarrySlice, card_eq_sum_ones, sum_filter]
  conv_rhs =>
    arg 2
    ext z
    rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  exact (sum_carry_indicator N hN (reflectionLowSum N t)
    (reflectionLowSum_bounds N hN t)).symm

/-- Some literal collision slice carries at least a 1/(3N) fraction of the
energy. Valid for empty A and zero energy, including N=1. -/
theorem exists_reflectionCarrySlice_large (A : Finset ℤ) (N : ℕ) (hN : 0 < N) :
    ∃ z ∈ Ico 0 (N : ℤ), ∃ k : Fin 3,
      (∑ c ∈ Ico 0 ((N : ℤ)^2), reflectionMultiplicity A c ^ 2) ≤
        (3*N) * (reflectionCarrySlice A N z k).card := by
  let T := (Ico 0 (N : ℤ)) ×ˢ (univ : Finset (Fin 3))
  have hT : T.Nonempty := by
    refine ⟨(0, 0), mem_product.mpr ⟨?_, mem_univ _⟩⟩
    exact mem_Ico.mpr ⟨le_refl 0, by change 0 < (N : ℤ); exact_mod_cast hN⟩
  obtain ⟨p, hp, hmax⟩ := exists_max_image T
    (fun q => (reflectionCarrySlice A N q.1 q.2).card) hT
  have hpz := (mem_product.mp hp).1
  refine ⟨p.1, hpz, p.2, ?_⟩
  have hcard : T.card = 3*N := by simp [T, card_product, Int.card_Ico, Nat.mul_comm]
  calc
    _ = ∑ q ∈ T, (reflectionCarrySlice A N q.1 q.2).card := by
      rw [reflection_energy_eq_sum_carry A N hN]
      simp only [T, sum_product]
    _ ≤ ∑ q ∈ T, (reflectionCarrySlice A N p.1 p.2).card :=
      sum_le_sum hmax
    _ = (3*N) * (reflectionCarrySlice A N p.1 p.2).card := by
      rw [sum_const, smul_eq_mul, hcard]

/-- Zero-extended digit-centre predicate: all four digits must lie in [0,N),
and the reconstructed scalar centre and its reflection belong to A, with
centre different from target. Different upper digits i and j are allowed. -/
def reflectionDigitCenter (A : Finset ℤ) (N : ℕ) (i v x n : ℤ) : Prop :=
  x ∈ Ico 0 (N : ℤ) ∧ n ∈ Ico 0 (N : ℤ) ∧
  i ∈ Ico 0 (N : ℤ) ∧ v ∈ Ico 0 (N : ℤ) ∧
  (x+(N : ℤ)*i ∈ A ∧
    2*(x+(N : ℤ)*i)-(n+(N : ℤ)*v) ∈ A ∧
    x+(N : ℤ)*i ≠ n+(N : ℤ)*v)

example : reflectionDigitCenter {2,5} 3 1 2 2 2 := by
  norm_num [reflectionDigitCenter]
example (A : Finset ℤ) (N : ℕ) (i v x : ℤ) :
    ¬ reflectionDigitCenter A N i v x (-1) := by
  simp [reflectionDigitCenter]

private theorem digit_scalar_range (N : ℕ) (n v : ℤ)
    (hn : n ∈ Ico 0 (N : ℤ)) (hv : v ∈ Ico 0 (N : ℤ)) :
    0 ≤ n+(N : ℤ)*v ∧ n+(N : ℤ)*v < (N : ℤ)^2 := by
  simp only [mem_Ico] at hn hv
  have hN : 0 ≤ (N : ℤ) := Nat.cast_nonneg N
  constructor <;> nlinarith

/-- Digit reconstruction exposes the literal (not cyclic) equation
n=z+kN-x-y for slice membership, with all six digits in [0,N). In particular
no equality of the two upper centre digits i,j is required. -/
theorem mem_reflectionCarrySlice_digits (A : Finset ℤ) (N : ℕ)
    (z : ℤ) (k : Fin 3) (i j v x y n : ℤ)
    (hi : i ∈ Ico 0 (N : ℤ)) (hj : j ∈ Ico 0 (N : ℤ))
    (hv : v ∈ Ico 0 (N : ℤ)) (hx : x ∈ Ico 0 (N : ℤ))
    (hy : y ∈ Ico 0 (N : ℤ)) (hn : n ∈ Ico 0 (N : ℤ)) :
    (⟨n+(N : ℤ)*v, (x+(N : ℤ)*i, y+(N : ℤ)*j)⟩ : Σ _ : ℤ, ℤ × ℤ)
        ∈ reflectionCarrySlice A N z k ↔
      reflectionDigitCenter A N i v x n ∧
      reflectionDigitCenter A N j v y n ∧
      n = z+(k.val : ℤ)*(N : ℤ)-x-y := by
  have hr := digit_scalar_range N n v hn hv
  have hlow : reflectionLowSum N
      ⟨n+(N : ℤ)*v, (x+(N : ℤ)*i, y+(N : ℤ)*j)⟩ = x+y+n := by
    simp only [reflectionLowSum, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (mem_Ico.mp hx).1 (mem_Ico.mp hx).2,
      Int.emod_eq_of_lt (mem_Ico.mp hy).1 (mem_Ico.mp hy).2,
      Int.emod_eq_of_lt (mem_Ico.mp hn).1 (mem_Ico.mp hn).2]
  simp only [reflectionCarrySlice, mem_filter, mem_reflectionCollisions, hlow,
    reflectionDigitCenter, hi, hj, hv, hx, hy, hn, true_and]
  constructor
  · rintro ⟨⟨hc0, hc1, ha, hb⟩, heq⟩
    exact ⟨ha, hb, by omega⟩
  · rintro ⟨ha, hb, heq⟩
    exact ⟨⟨hr.1, hr.2, ha, hb⟩, by omega⟩

/-- Exact zero-extended digit-cell interpretation. Fix any five in-range
digits (i,j,v,x,y). A compatible target digit exists in a carry slice exactly
when both digit-centre predicates hold at n=z+kN-x-y. Their range conditions
kill an out-of-range n rather than reducing it modulo N. -/
theorem reflectionCarrySlice_digit_cell_iff (A : Finset ℤ) (N : ℕ)
    (z : ℤ) (k : Fin 3) (i j v x y : ℤ)
    (hi : i ∈ Ico 0 (N : ℤ)) (hj : j ∈ Ico 0 (N : ℤ))
    (hv : v ∈ Ico 0 (N : ℤ)) (hx : x ∈ Ico 0 (N : ℤ))
    (hy : y ∈ Ico 0 (N : ℤ)) :
    (∃ n ∈ Ico 0 (N : ℤ),
      (⟨n+(N : ℤ)*v, (x+(N : ℤ)*i, y+(N : ℤ)*j)⟩ : Σ _ : ℤ, ℤ × ℤ)
        ∈ reflectionCarrySlice A N z k) ↔
      reflectionDigitCenter A N i v x (z+(k.val : ℤ)*(N : ℤ)-x-y) ∧
      reflectionDigitCenter A N j v y (z+(k.val : ℤ)*(N : ℤ)-x-y) := by
  constructor
  · rintro ⟨n, hn, ht⟩
    obtain ⟨ha, hb, heq⟩ :=
      (mem_reflectionCarrySlice_digits A N z k i j v x y n hi hj hv hx hy hn).mp ht
    rw [heq] at ha hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    have hn := ha.2.1
    refine ⟨z+(k.val : ℤ)*(N : ℤ)-x-y, hn, ?_⟩
    exact (mem_reflectionCarrySlice_digits A N z k i j v x y _ hi hj hv hx hy hn).mpr
      ⟨ha, hb, rfl⟩

/-- The wrapped collision fiber: only the sum of low digits is reduced
modulo N; all scalar representation and target constraints remain exact. -/
noncomputable def reflectionWrappedSlice (A : Finset ℤ) (N : ℕ) (z : ℤ) :
    Finset (Σ _ : ℤ, ℤ × ℤ) :=
  (reflectionCollisions A N).filter fun t => reflectionLowSum N t % (N : ℤ) = z

example (N : ℕ) (z : ℤ) : reflectionWrappedSlice ∅ N z = ∅ := by
  simp [reflectionWrappedSlice, reflectionCollisions]

private theorem sum_carry_indicator_at (N : ℕ) (hN : 0 < N) (s z : ℤ)
    (hs : 0 ≤ s ∧ s < 3*(N : ℤ)) (hz : z ∈ Ico 0 (N : ℤ)) :
    (∑ k : Fin 3, if s = z+(k.val : ℤ)*(N : ℤ) then (1 : ℕ) else 0) =
      if s % (N : ℤ) = z then 1 else 0 := by
  obtain ⟨w, hw, l, hl⟩ := carry_exists N hN s hs
  have hmod : s % (N : ℤ) = w := by
    rw [hl, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (mem_Ico.mp hw).1 (mem_Ico.mp hw).2]
  by_cases heq : z = w
  · subst z
    simp only [hmod]
    rw [sum_eq_single l]
    · simp [hl]
    · intro k hk hne
      have hnot : s ≠ w+(k.val : ℤ)*(N : ℤ) := by
        intro heq
        have hu := carry_unique N w w l k hw hw (hl.symm.trans heq)
        exact hne hu.2.symm
      simp [hnot]
    · simp
  · simp only [hmod, if_neg (Ne.symm heq)]
    apply sum_eq_zero
    intro k hk
    have hnot : s ≠ z+(k.val : ℤ)*(N : ℤ) := by
      intro heq'
      have hu := carry_unique N w z l k hw hz (hl.symm.trans heq')
      exact heq hu.1.symm
    simp [hnot]

/-- Per-low-digit wrapped mass is exactly the sum of its three literal carry
slices. This is the positive finite partition, with no Fourier loss. -/
theorem card_reflectionWrappedSlice_eq_sum_carry (A : Finset ℤ) (N : ℕ)
    (hN : 0 < N) (z : ℤ) (hz : z ∈ Ico 0 (N : ℤ)) :
    (reflectionWrappedSlice A N z).card =
      ∑ k : Fin 3, (reflectionCarrySlice A N z k).card := by
  simp only [reflectionWrappedSlice, reflectionCarrySlice, card_eq_sum_ones, sum_filter]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  exact (sum_carry_indicator_at N hN (reflectionLowSum N t) z
    (reflectionLowSum_bounds N hN t) hz).symm

/-- Energy is also the sum of the wrapped low-digit fibers. -/
theorem reflection_energy_eq_sum_wrapped (A : Finset ℤ) (N : ℕ) (hN : 0 < N) :
    (∑ c ∈ Ico 0 ((N : ℤ)^2), reflectionMultiplicity A c ^ 2) =
      ∑ z ∈ Ico 0 (N : ℤ), (reflectionWrappedSlice A N z).card := by
  rw [reflection_energy_eq_sum_carry A N hN]
  apply sum_congr rfl
  intro z hz
  exact (card_reflectionWrappedSlice_eq_sum_carry A N hN z hz).symm

-- A nonempty third-carry model: centre 5, endpoint 2, target 8.
example : (⟨8, (5,5)⟩ : Σ _ : ℤ, ℤ × ℤ) ∈ reflectionCarrySlice {2,5} 3 0 2 := by
  simp [reflectionCarrySlice, reflectionCollisions, reflectionLowSum]

-- Jointly satisfiable six-digit boundary data for the digit bridge.
example :
    (⟨2+(3 : ℤ)*2, (2+(3 : ℤ)*1, 2+(3 : ℤ)*1)⟩ : Σ _ : ℤ, ℤ × ℤ)
      ∈ reflectionCarrySlice {2,5} 3 0 2 := by
  apply (mem_reflectionCarrySlice_digits {2,5} 3 0 2 1 1 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num [reflectionDigitCenter]

example : ∃ z ∈ Ico 0 (1 : ℤ), ∃ k : Fin 3,
    (∑ c ∈ Ico 0 ((1 : ℤ)^2), reflectionMultiplicity ∅ c ^ 2) ≤
      3 * (reflectionCarrySlice ∅ 1 z k).card := by
  exact exists_reflectionCarrySlice_large ∅ 1 (by decide)

end Erdos142
