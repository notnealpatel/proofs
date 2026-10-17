import Combinatorics.NoncommutingFiber
import Mathlib.Data.Int.Interval

set_option autoImplicit false

noncomputable section

namespace NoncommutingBoxAspectNecessity

open NoncommutingFiber
open scoped Pointwise

/-- The integer side interval of length `N`. -/
def interval (N : ℕ) : Finset ℤ := Finset.Icc 0 ((N : ℤ) - 1)

/-- The thin box with side lengths `1, N, N`. -/
def box (N : ℕ) : Finset (ℤ × ℤ × ℤ) := {0} ×ˢ (interval N ×ˢ interval N)

/-- The thin box with its origin deleted. -/
def punctured (N : ℕ) : Finset (ℤ × ℤ × ℤ) := (box N).erase (0, 0, 0)

example : interval 2 = Finset.Icc 0 1 := rfl
example : box 2 = {0} ×ˢ (Finset.Icc 0 1 ×ˢ Finset.Icc 0 1) := rfl
example : punctured 2 = (box 2).erase (0, 0, 0) := rfl
example : 2 ≤ (2 : ℕ) := by decide

private theorem interval_mem (N : ℕ) (a : ℤ) :
    a ∈ interval N ↔ 0 ≤ a ∧ a ≤ (N : ℤ) - 1 := by
  simp only [interval, Finset.mem_Icc]

private theorem box_mem (N : ℕ) (p a b : ℤ) :
    (p, a, b) ∈ box N ↔ p = 0 ∧ a ∈ interval N ∧ b ∈ interval N := by
  simp only [box, Finset.mem_product, Finset.mem_singleton]

private theorem origin_mem (N : ℕ) (hN : 2 ≤ N) :
    (0, 0, 0) ∈ box N := by
  rw [box_mem, interval_mem]
  omega

private theorem samples (N : ℕ) (hN : 2 ≤ N)
    (a : ℤ) (ha : a ∈ interval N) :
    (0, a, 1) ∈ punctured N ∧ (0, 1, a) ∈ punctured N := by
  have h1 : (1 : ℤ) ∈ interval N := by
    rw [interval_mem]
    omega
  constructor
  · apply Finset.mem_erase.mpr
    constructor
    · intro h
      have h' := congrArg (fun x : ℤ × ℤ × ℤ => x.2.2) h
      norm_num at h'
    · exact (box_mem N 0 a 1).mpr ⟨rfl, ha, h1⟩
  · apply Finset.mem_erase.mpr
    constructor
    · intro h
      have h' := congrArg (fun x : ℤ × ℤ × ℤ => x.2.1) h
      norm_num at h'
    · exact (box_mem N 0 1 a).mpr ⟨rfl, h1, ha⟩

private theorem witness
    (S : Finset (ℤ × ℤ × ℤ)) (a b c d : ℤ)
    (ha : (0, a, 1) ∈ S) (hb : (0, 1, b) ∈ S)
    (hr : (0, d, c) ∈ S) :
    (a + b, c, -d) ∈ mixedSum S := by
  change (a + b, c, -d) ∈ S.image L0 + S.image L1 + S.image L2
  apply Finset.mem_add.mpr
  refine ⟨L0 (0, a, 1) + L1 (0, 1, b), ?_,
    L2 (0, d, c), Finset.mem_image.mpr ⟨_, hr, rfl⟩, ?_⟩
  · exact Finset.mem_add.mpr
      ⟨_, Finset.mem_image.mpr ⟨_, ha, rfl⟩,
        _, Finset.mem_image.mpr ⟨_, hb, rfl⟩, rfl⟩
  · simp only [L0, L1, L2, Prod.mk_add_mk, neg_zero, add_zero, zero_add]

private theorem extract
    (N : ℕ) (S : Finset (ℤ × ℤ × ℤ)) (hS : S ⊆ box N)
    (t y z : ℤ) (hx : (t, y, z) ∈ mixedSum S) :
    ∃ a b : ℤ, a ∈ interval N ∧ b ∈ interval N ∧
      t = a + b ∧ (0, -z, y) ∈ S := by
  change (t, y, z) ∈ S.image L0 + S.image L1 + S.image L2 at hx
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
  obtain ⟨u₀, hu₀, u₁, hu₁, he⟩ := Finset.mem_add.mp hu
  obtain ⟨⟨p, a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hu₀
  obtain ⟨⟨q, d, e⟩, hq, rfl⟩ := Finset.mem_image.mp hu₁
  obtain ⟨⟨r, c, f⟩, hr, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp0, ha, _⟩ := (box_mem N p a b).mp (hS hp)
  obtain ⟨hq0, _, heN⟩ := (box_mem N q d e).mp (hS hq)
  obtain ⟨hr0, _, _⟩ := (box_mem N r c f).mp (hS hr)
  subst p
  subst q
  subst r
  have hsum : L0 (0, a, b) + L1 (0, d, e) + L2 (0, c, f) = (t, y, z) := by
    rw [he]
    exact huv
  have hcoords : (a + e, f, -c) = (t, y, z) := by
    simpa only [L0, L1, L2, Prod.mk_add_mk, neg_zero, add_zero, zero_add] using hsum
  have ht : a + e = t := congrArg Prod.fst hcoords
  have hy : f = y := congrArg (fun x : ℤ × ℤ × ℤ => x.2.1) hcoords
  have hz : -c = z := congrArg (fun x : ℤ × ℤ × ℤ => x.2.2) hcoords
  refine ⟨a, e, ha, heN, ht.symm, ?_⟩
  have hc : -z = c := by omega
  rw [hc, ← hy]
  exact hr

private theorem decompose (N : ℕ) (hN : 2 ≤ N) (t : ℤ)
    (ht : t ∈ Finset.Icc (0 : ℤ) (2 * (N : ℤ) - 2)) :
    ∃ a b : ℤ, a ∈ interval N ∧ b ∈ interval N ∧ t = a + b := by
  obtain ⟨ht0, ht1⟩ := Finset.mem_Icc.mp ht
  refine ⟨min t ((N : ℤ) - 1), t - min t ((N : ℤ) - 1), ?_, ?_, ?_⟩
  · rw [interval_mem]
    omega
  · rw [interval_mem]
    omega
  · omega

/-- Puncturing the box removes exactly the origin from the input. -/
theorem input_holes (N : ℕ) (hN : 2 ≤ N) :
    box N \ punctured N = {(0, 0, 0)} := by
  exact Finset.sdiff_erase_self (origin_mem N hN)

/-- The input defect has cardinality one. -/
theorem input_holes_card (N : ℕ) (hN : 2 ≤ N) :
    (box N \ punctured N).card = 1 := by
  rw [input_holes N hN]
  exact Finset.card_singleton _

/-- The output defect is precisely the horizontal interval of length `2 * N - 1`. -/
theorem output_holes (N : ℕ) (hN : 2 ≤ N) :
    mixedSum (box N) \ mixedSum (punctured N) =
      (Finset.Icc (0 : ℤ) (2 * (N : ℤ) - 2)).image (fun t => (t, 0, 0)) := by
  ext ⟨t, y, z⟩
  constructor
  · intro hx
    obtain ⟨hx, hnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨a, b, ha, hb, ht, hr⟩ := extract N (box N) (fun _ h => h) t y z hx
    have haxis : y = 0 ∧ z = 0 := by
      by_contra hn
      have hr' : (0, -z, y) ∈ punctured N := by
        apply Finset.mem_erase.mpr
        refine ⟨?_, hr⟩
        intro he
        have hz := congrArg (fun x : ℤ × ℤ × ℤ => x.2.1) he
        have hy := congrArg (fun x : ℤ × ℤ × ℤ => x.2.2) he
        change -z = 0 at hz
        change y = 0 at hy
        apply hn
        omega
      have hw := witness (punctured N) a b y (-z)
        (samples N hN a ha).1 (samples N hN b hb).2 hr'
      apply hnot
      simpa only [neg_neg, ← ht] using hw
    obtain ⟨rfl, rfl⟩ := haxis
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_Icc.mpr ?_, rfl⟩
    rw [interval_mem] at ha hb
    omega
  · intro hx
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hx
    have ht : s = t := congrArg Prod.fst he
    have hy : (0 : ℤ) = y := congrArg (fun x : ℤ × ℤ × ℤ => x.2.1) he
    have hz : (0 : ℤ) = z := congrArg (fun x : ℤ × ℤ × ℤ => x.2.2) he
    subst t
    subst y
    subst z
    obtain ⟨a, b, ha, hb, hab⟩ := decompose N hN s hs
    apply Finset.mem_sdiff.mpr
    constructor
    · have hpa := Finset.mem_of_mem_erase (samples N hN a ha).1
      have hpb := Finset.mem_of_mem_erase (samples N hN b hb).2
      have hw := witness (box N) a b 0 0 hpa hpb (origin_mem N hN)
      simpa only [neg_zero, ← hab] using hw
    · intro hm
      obtain ⟨a', b', ha', hb', ht', hr⟩ :=
        extract N (punctured N) (Finset.erase_subset _ _) s 0 0 hm
      have hr' : (0, 0, 0) ∈ punctured N := by simpa only [neg_zero] using hr
      exact (Finset.mem_erase.mp hr').1 rfl

/-- The output defect has cardinality `2 * N - 1`. -/
theorem output_holes_card (N : ℕ) (hN : 2 ≤ N) :
    (mixedSum (box N) \ mixedSum (punctured N)).card = 2 * N - 1 := by
  rw [output_holes N hN]
  have hinj : Function.Injective (fun t : ℤ => (t, (0 : ℤ), (0 : ℤ))) := by
    intro a b h
    exact congrArg Prod.fst h
  rw [Finset.card_image_of_injective _ hinj, Int.card_Icc]
  omega

/-- No uniform real multiple of the input defect bounds these output defects. -/
theorem necessity :
    ∀ C : ℝ, ∃ N : ℕ, 2 ≤ N ∧
      C * ((box N \ punctured N).card : ℝ) <
        ((mixedSum (box N) \ mixedSum (punctured N)).card : ℝ) := by
  intro C
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 : ℝ) (C + 1))
  have htwo : (2 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hC : C + 1 < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNat : 2 ≤ N := by
    by_contra h
    have hn : N ≤ 1 := by omega
    have hn' : (N : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
  refine ⟨N, hNat, ?_⟩
  rw [input_holes_card N hNat, output_holes_card N hNat]
  have hsub : 1 ≤ 2 * N := by omega
  rw [Nat.cast_sub hsub, Nat.cast_mul]
  push_cast
  linarith

end NoncommutingBoxAspectNecessity
