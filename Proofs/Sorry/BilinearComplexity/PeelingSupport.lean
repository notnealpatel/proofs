import Sorry.Quarantine.BilinearComplexity.PeelingSupport

/-!
Quarantined admissions and their dependent consequences. Production supplies the
independent infrastructure; the declarations below retain their original statements
and proofs. The original source and disclosure documentation is retained below.
No mathematical proof closure is claimed.
-/

/-!
# Support-geometry foundation for the peeling-peak invariant

Formalization of five lemmas (L0–L5) about the combinatorial geometry
of the matrix-multiplication support `T n` and its F₂-decompositions
into indicator boxes.

## Setting

Over F₂, a rank-1 tensor is an indicator box: for nonempty
`U V W : Finset (Fin n × Fin n)`, its support is the product set
`U ×ˢ V ×ˢ W`, of size `|U|·|V|·|W|`. The matmul support is

  `T n = {((i,j), (j,k), (i,k)) : i j k : Fin n}`

with `|T n| = n³`. A decomposition of length `r` is a list of `r`
boxes whose iterated symmetric difference equals `T n` — equivalently,
every cell of `T n` lies in an odd number of the boxes and every other
cell in an even number.

## Main results

* `matmulSupport_card` — `|T n| = n³`.
* `line_property_12`, `line_property_23`, `line_property_13` (L1) —
  each axis line meets `T n` at most once.
* `shadow_bound_12`, `shadow_bound_23`, `shadow_bound_13` (L2) —
  `|supp τ ∩ T n| ≤ |U|·|V|` (and cyclic variants);
  `shadow_cube_bound` — `m³ ≤ |τ|²`.
* `cover_sum_ge` (L3) — `Σ mᵢ ≥ n³`; `cover_outmass_even` — total
  out-mass is even.
* `slack0_size_bound` (L4) — `|τ| ≤ 2m`; `slack0_m_le` — `m ≤ 4`;
  `slack0_tau_le` — `|τ| ≤ 8`.
* `outmass_ge_two` (L5) — any decomposition with `r < n³` has
  out-mass ≥ 2.
-/



set_option autoImplicit false

namespace BilinearComplexity.PeelingSupport

open Finset
open scoped symmDiff

/-- The out-mass of a box counts the cells of its support outside `T n`:
`τ.outMass = Σ_{t ∉ T n} [t ∈ supp τ]`. -/
private lemma outMass_eq_sum_indicator {n : ℕ} (τ : Box n) :
    τ.outMass = ∑ t ∈ (matmulSupport n)ᶜ, if t ∈ τ.support then 1 else 0 := by
  rw [Finset.sum_boole, Nat.cast_id, Box.outMass, Box.mass]
  have hsd := card_sdiff_add_card_inter τ.support (matmulSupport n)
  have hfilt : ({t ∈ (matmulSupport n)ᶜ | t ∈ τ.support} : Finset (Triple n)) =
      τ.support \ matmulSupport n := by
    ext t
    simp [and_comm]
  rw [hfilt]
  omega

/-- Cover counts split off the head box:
`coverCount t (τ :: L) = [t ∈ supp τ] + coverCount t L`. -/
private lemma coverCount_cons {n : ℕ} (t : Triple n) (τ : Box n) (L : List (Box n)) :
    coverCount t (τ :: L) = (if t ∈ τ.support then 1 else 0) + coverCount t L := by
  unfold coverCount
  by_cases h : t ∈ τ.support
  · simp [h, Nat.add_comm]
  · simp [h]

/-- Double counting: the total out-mass equals the sum of cover counts over the
cells outside `T n`. -/
private lemma totalOutMass_eq_sum_coverCount {n : ℕ} (L : List (Box n)) :
    totalOutMass n L = ∑ t ∈ (matmulSupport n)ᶜ, coverCount t L := by
  induction L with
  | nil => simp [totalOutMass, coverCount]
  | cons τ L ih =>
    have hcons : totalOutMass n (τ :: L) = τ.outMass + totalOutMass n L := by
      simp only [totalOutMass, List.map_cons, List.sum_cons]
    simp_rw [hcons, coverCount_cons, Finset.sum_add_distrib, ih, outMass_eq_sum_indicator]

/-- **L3b.** The total out-mass is even. -/
theorem cover_outmass_even {n : ℕ} {L : List (Box n)} (hd : IsDecomp n L) :
    Even (totalOutMass n L) := by
  rw [totalOutMass_eq_sum_coverCount]
  apply Finset.even_sum
  intro t ht
  exact (isDecomp_iff_parity.mp hd).2 t (Finset.mem_compl.mp ht)

/-! The two private, independently proved helpers are copied verbatim so that
the archived consumer retains its proof without exposing production-private names.
The originals remain in production. -/

/-- If m ≥ 2 then |τ| > m (equivalently, outMass ≥ 1). -/
private lemma outMass_pos_of_mass_ge_two {n : ℕ} (τ : Box n) (hm : 2 ≤ τ.mass) :
    0 < τ.outMass := by
  unfold Box.outMass
  -- If |τ| ≤ m then m³ ≤ |τ|² ≤ m², so m ≤ 1, contradicting m ≥ 2
  by_contra h
  simp only [not_lt, Nat.le_zero] at h
  -- h : τ.support.card - τ.mass = 0, so |τ| ≤ m
  have hle : τ.support.card ≤ τ.mass := by omega
  have hcube := shadow_cube_bound τ
  -- m³ ≤ |τ|² ≤ m²
  have : τ.mass ^ 3 ≤ τ.mass ^ 2 :=
    le_trans hcube (Nat.pow_le_pow_left hle 2)
  -- m * m² ≤ m², so m ≤ 1 (for m > 0, cancel m²)
  have hm_pos : 0 < τ.mass := by omega
  have : τ.mass ≤ 1 := by nlinarith [sq_nonneg τ.mass]
  omega

/-- Pigeonhole: if sum of a list ≥ k and length < k, some element ≥ 2. -/
private lemma exists_ge_two_of_sum_gt_length {L : List ℕ}
    (hsum : L.length < L.sum) :
    ∃ x ∈ L, 2 ≤ x := by
  by_contra hall
  simp only [not_exists, not_and, not_le] at hall
  -- Every element is ≤ 1, so sum ≤ length
  have : L.sum ≤ L.length := by
    induction L with
    | nil => simp
    | cons x L' ih =>
      simp only [List.sum_cons, List.length_cons]
      have hx : x < 2 := hall x (List.Mem.head _)
      have hall' : ∀ y ∈ L', y < 2 := fun y hy => hall y (List.Mem.tail _ hy)
      suffices L'.sum ≤ L'.length by omega
      clear ih hsum hall
      induction L' with
      | nil => simp
      | cons y L'' ihy =>
        simp only [List.sum_cons, List.length_cons]
        have hy2 : y < 2 := hall' y (List.Mem.head _)
        have := ihy (fun z hz => hall' z (List.Mem.tail _ hz))
        omega
  omega

/-- **L5.** Any decomposition with fewer than `n³` boxes has
out-mass ≥ 2. -/
theorem outmass_ge_two {n : ℕ} {L : List (Box n)}
    (hd : IsDecomp n L) (hr : L.length < n ^ 3) :
    2 ≤ totalOutMass n L := by
  -- Step 1: totalMass ≥ n³ > r, so some box has mass ≥ 2
  have hmass := cover_sum_ge hd
  have hlen : L.length < (L.map (fun τ => τ.mass)).sum := by
    calc L.length < n ^ 3 := hr
      _ ≤ totalMass n L := hmass
      _ = _ := rfl
  have hlen' : (L.map (fun τ => τ.mass)).length < (L.map (fun τ => τ.mass)).sum := by
    simp only [List.length_map]; exact hlen
  obtain ⟨m, hm_mem, hm_ge⟩ := exists_ge_two_of_sum_gt_length hlen'
  rw [List.mem_map] at hm_mem
  obtain ⟨τ, hτ_mem, rfl⟩ := hm_mem
  -- Step 2: that box has outMass ≥ 1
  have hout := outMass_pos_of_mass_ge_two τ hm_ge
  -- Step 3: totalOutMass ≥ 1
  have hout1 : 1 ≤ totalOutMass n L := by
    unfold totalOutMass
    calc 1 ≤ τ.outMass := hout
      _ ≤ (L.map (fun τ => τ.outMass)).sum :=
          List.le_sum_of_mem (List.mem_map_of_mem (f := fun τ : Box n => τ.outMass) hτ_mem)
  -- Step 4: totalOutMass is even, so ≥ 2
  have heven := cover_outmass_even hd
  obtain ⟨k, hk⟩ := heven
  omega

end BilinearComplexity.PeelingSupport
