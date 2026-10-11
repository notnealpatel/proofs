import Combinatorics.NoncommutingFiber

/-!
# x-fiber compression can increase the noncommuting mixed sum

For integer points, `xCompress` replaces each fiber over `(y,z)` of size `k`
by the x-coordinates `0,…,k-1`. The four-point witness below moves only the
singleton `(1,1,0)` to `(0,1,0)`. For the three independently chosen images,
`L0(p0) + L1(p1) + L2(p2) = (y0+z1, -x0+z2, -x1-y2)`.
Its mixed-sum cardinality increases from 17 to 18.

Structurally, the `L1` and `L2` images stay fixed. If `B = L1(A) + L2(A)`
and `U = B ∪ (B-e_y)`, the changing `L0` image replaces the translate
`B+e_x-e_y` by `B+e_x`. The fixed sets have sizes 8 and 13, respectively;
the old translate overlaps `U` in four points, the new one in three.
Compression can thus reduce collisions between independent summands.

The one-x-level boundary case is also proved below: compression zeroes the
x-coordinate, and the original mixed sum is a translate of the compressed one,
so cardinality is preserved, including for empty sets and negative levels.

Source consolidation: `Plans/NoncommutingXCompression.md` at revision
`8541812f37e99d0dae8f6bc3490d43aa56d7cc1c`.
`Programs/NoncommutingXCompression.sage` remains an auxiliary reproduction: it
checks output sets and overlaps and stops at the first mask witness among at
most 255 nonempty subsets of `{0,1}³`. This is not an exhaustive classification
or a minimality claim, and Lean has no execution dependency on that script.

This is only a counterexample to unconditional nonincrease for this specified
x-compression. It asserts no novelty, minimality, other compression direction,
inverse operation, or restricted-class result beyond the one-x-level boundary
case. In particular, it gives no
bridge from comparable-box density estimates to an arbitrary dense-box theorem.
-/

set_option autoImplicit false

namespace NoncommutingFiber

/-- Replace every x-fiber by its initial segment of nonnegative integers,
retaining its `(y,z)` coordinate and its number of points. -/
def xCompress (A : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  (A.image Prod.snd).biUnion fun yz =>
    (Finset.range (A.filter (fun p => p.2 = yz)).card).image
      (fun x : ℕ => ((x : ℤ), yz))

example : xCompress ∅ = ∅ := by decide
example : xCompress {(7, 2, 3)} = {(0, 2, 3)} := by decide

/-- Four integer points whose mixed sum grows under x-fiber compression. -/
def xCompressionWitness : Finset (ℤ × ℤ × ℤ) :=
  {(0, 0, 0), (0, 0, 1), (1, 0, 0), (1, 1, 0)}

example : xCompressionWitness.card = 4 := by decide

/-- The compressed four-point witness: only the singleton fiber at `(1,0)` moves. -/
def xCompressionWitnessCompressed : Finset (ℤ × ℤ × ℤ) :=
  {(0, 0, 0), (1, 0, 0), (0, 0, 1), (0, 1, 0)}

example : xCompressionWitnessCompressed.card = 4 := by decide

/-- Executable x-fiber compression gives precisely the displayed compressed witness. -/
theorem xCompress_witness :
    xCompress xCompressionWitness = xCompressionWitnessCompressed := by
  decide

/-- The original witness has exactly seventeen independently chosen mixed sums. -/
theorem mixedSum_witness_card : (mixedSum xCompressionWitness).card = 17 := by
  decide

/-- The compressed witness has exactly eighteen independently chosen mixed sums. -/
theorem mixedSum_compressed_witness_card :
    (mixedSum xCompressionWitnessCompressed).card = 18 := by
  decide

/-- Genuine x-fiber compression strictly increases the mixed-sum size of this witness. -/
theorem mixedSum_card_lt_xCompress_witness :
    (mixedSum xCompressionWitness).card <
      (mixedSum (xCompress xCompressionWitness)).card := by
  rw [xCompress_witness, mixedSum_witness_card, mixedSum_compressed_witness_card]
  decide

/-- There exists a finite integer set for which x-fiber compression increases the mixed sum. -/
theorem exists_mixedSum_card_lt_xCompress :
    ∃ A : Finset (ℤ × ℤ × ℤ), (mixedSum A).card < (mixedSum (xCompress A)).card := by
  exact ⟨xCompressionWitness, mixedSum_card_lt_xCompress_witness⟩

/-- x-fiber compression is not universally mixed-sum-cardinality nonincreasing. -/
theorem not_mixedSum_xCompress_card_le :
    ¬ ∀ A : Finset (ℤ × ℤ × ℤ), (mixedSum (xCompress A)).card ≤ (mixedSum A).card := by
  intro h
  exact Nat.not_le_of_lt mixedSum_card_lt_xCompress_witness (h xCompressionWitness)

open scoped Pointwise

/-- On a single x-level, compression simply zeroes every x-coordinate.
The empty set is allowed, and the level can be any integer. -/
theorem xCompress_eq_image_of_one_x_level (A : Finset (ℤ × ℤ × ℤ)) (c : ℤ)
    (hA : ∀ p ∈ A, p.1 = c) :
    xCompress A = A.image (fun p => (0, p.2)) := by
  have hf (p : ℤ × ℤ × ℤ) (hp : p ∈ A) :
      A.filter (fun q => q.2 = p.2) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hq
      exact Prod.ext ((hA q hq.1).trans (hA p hp).symm) hq.2
    · intro hq
      subst q
      exact ⟨hp, rfl⟩
  ext q
  constructor
  · intro hq
    obtain ⟨yz, hyz, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hyz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    rw [hf p hp, Finset.card_singleton] at hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact Finset.mem_image_of_mem (fun p => ((0 : ℤ), p.2)) hp
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_biUnion.mpr
    refine ⟨p.2, Finset.mem_image_of_mem Prod.snd hp, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨0, ?_, rfl⟩
    rw [hf p hp, Finset.card_singleton]
    decide

example : ∀ p ∈ ({(-2, 3, 4)} : Finset (ℤ × ℤ × ℤ)), p.1 = (-2 : ℤ) := by
  simp

private theorem add_singleton_eq_image (S : Finset (ℤ × ℤ × ℤ))
    (t : ℤ × ℤ × ℤ) : S + {t} = S.image (fun p => p + t) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hp, u, hu, he⟩ := Finset.mem_add.mp hq
    have hu_eq : u = t := Finset.mem_singleton.mp hu
    subst u
    exact Finset.mem_image.mpr ⟨p, hp, he⟩
  · intro hq
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hq
    exact Finset.mem_add.mpr ⟨p, hp, t, Finset.mem_singleton_self t, he⟩

/-- On one x-level, the original mixed sum is the compressed mixed sum translated
by `(0,-c,-c)`. This includes empty sets and negative x-levels. -/
theorem mixedSum_eq_xCompress_add_singleton_of_one_x_level
    (A : Finset (ℤ × ℤ × ℤ)) (c : ℤ) (hA : ∀ p ∈ A, p.1 = c) :
    mixedSum A = mixedSum (xCompress A) + {(0, -c, -c)} := by
  have h0 : A.image L0 = (xCompress A).image L0 + {(0, -c, 0)} := by
    rw [add_singleton_eq_image, xCompress_eq_image_of_one_x_level A c hA]
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro p hp
    simp [Function.comp_def, L0, hA p hp]
  have h1 : A.image L1 = (xCompress A).image L1 + {(0, 0, -c)} := by
    rw [add_singleton_eq_image, xCompress_eq_image_of_one_x_level A c hA]
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro p hp
    simp [Function.comp_def, L1, hA p hp]
  have h2 : A.image L2 = (xCompress A).image L2 := by
    rw [xCompress_eq_image_of_one_x_level A c hA]
    simp only [Finset.image_image]
    rfl
  unfold mixedSum
  rw [h0, h1, h2]
  calc
    _ = ((xCompress A).image L0 + (xCompress A).image L1 +
        (xCompress A).image L2) + ({(0, -c, 0)} + {(0, 0, -c)}) := by ac_rfl
    _ = _ := by rw [Finset.singleton_add_singleton]; simp

/-- Compression preserves mixed-sum cardinality for any finite set on one x-level. -/
theorem mixedSum_xCompress_card_eq_of_one_x_level
    (A : Finset (ℤ × ℤ × ℤ)) (c : ℤ) (hA : ∀ p ∈ A, p.1 = c) :
    (mixedSum (xCompress A)).card = (mixedSum A).card := by
  rw [mixedSum_eq_xCompress_add_singleton_of_one_x_level A c hA,
    Finset.card_add_singleton]

end NoncommutingFiber
