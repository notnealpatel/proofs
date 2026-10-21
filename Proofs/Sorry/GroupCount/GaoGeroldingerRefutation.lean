/-
# Gao–Geroldinger refuted: explicit zero-sum-free sequences with excess `m`

## Source

Guoqing Wang, "Disproof of a Conjectured Upper Bound for the Davenport
Constant", arXiv:2609.29878v4.  Section 3.1 ("An explicit family with
unbounded excess"): Lemma 3.2 (`lem:binary`) and Theorem 3.1 (`thm:main`),
specifically the core group `B_m` in the proof of Theorem 3.1.
Retrieved 2026-10-21.

## Verbatim informal claims

Conjecture (Gao–Geroldinger, [GG06, Conjecture 3.7]): "Every nontrivial finite
abelian group `G` satisfies `δ(G) ≤ r(G) - 1`", where `δ(G) = D(G) - D*(G)`,
`D*(G) = 1 + ∑ (n_i - 1)` for `G = C_{n_1} ⊕ ⋯ ⊕ C_{n_r}`, `1 < n_1 ∣ ⋯ ∣ n_r`.

Theorem 3.1 (core case `r = 8`, proof of the theorem): over
`B_m = C_m^3 ⊕ C_{2m}^4 ⊕ C_{6m}` with generators `z_1,z_2,z_3` (order `m`),
`y_1,…,y_4` (order `2m`), `e` (order `6m`), put
  `q_j = y_j + 2e` (`1 ≤ j ≤ 4`),
  `q_{4+i} = z_i + ∑_{1 ≤ j ≤ 4, j ≠ i} y_j + 2e` (`1 ≤ i ≤ 3`),
  `S_m = e^{4m-1} ∏_{j=1}^7 q_j^{2m-1}`.
"We have `|S_m| = 18m - 8`. Moreover, `supp(S_m)` generates `B_m` … `S_m` is
zero-sum free."  With `d*(B_m) = 17m - 8` this gives `δ(B_m) ≥ m`, and for
`m ≥ 8 = r(B_m)` it contradicts the Gao–Geroldinger conjecture.

## Status

Proved in the paper (Section 3.1).  This module formalizes the core case
`B_m` (the padding by `C_m^{r-8}` is not formalized) and the resulting
refutation at every `m ≥ 8`, in particular at `G = C_8^3 ⊕ C_16^4 ⊕ C_48`.
Mathlib has no Davenport constant; `D(G) ≤ ℓ` is expressed by
`HasDavenportBound G ℓ` ("every sequence of length at least `ℓ` has a nonempty
zero-sum subsequence"), and a sequence is a `Multiset`.
-/
import Mathlib

set_option autoImplicit false

namespace GaoGeroldinger

/-! ## Zero-sum vocabulary -/

/-- A sequence (multiset) over an additive monoid is *zero-sum free* when no
nonempty subsequence has sum zero (`0 ∉ Σ(S)` in the paper's notation). -/
def ZeroSumFree {G : Type*} [AddCommMonoid G] (s : Multiset G) : Prop :=
  ∀ t ≤ s, t ≠ 0 → t.sum ≠ 0

/-- `HasDavenportBound G ℓ` says `D(G) ≤ ℓ`: every sequence over `G` of length at
least `ℓ` has a nonempty zero-sum subsequence.  The Davenport constant `D(G)` is
the least `ℓ` with this property. -/
def HasDavenportBound (G : Type*) [AddCommMonoid G] (ℓ : ℕ) : Prop :=
  ∀ s : Multiset G, ℓ ≤ s.card → ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0

/-- `dStar [n_1, …, n_r] = ∑ (n_i - 1)`, the paper's `d*(G)` for
`G = C_{n_1} ⊕ ⋯ ⊕ C_{n_r}`; the paper's `D*(G)` is `dStar + 1`.  All `n_i` are
positive cyclic orders, so the truncated subtraction is exact. -/
def dStar (ns : List ℕ) : ℕ := (ns.map fun n => n - 1).sum

/-- `ZeroSumFree` unfolds to a check over the (finite) powerset. -/
theorem zeroSumFree_iff_powerset {G : Type*} [AddCommMonoid G] (s : Multiset G) :
    ZeroSumFree s ↔ ∀ t ∈ s.powerset, t ≠ 0 → t.sum ≠ 0 := by
  simp only [ZeroSumFree, Multiset.mem_powerset]

/-- A zero-sum-free sequence of length `ℓ` witnesses the failure of `D(G) ≤ ℓ`. -/
theorem not_hasDavenportBound_of_zeroSumFree {G : Type*} [AddCommMonoid G]
    {s : Multiset G} (hs : ZeroSumFree s) : ¬ HasDavenportBound G s.card := by
  intro hD
  obtain ⟨t, hts, hne, hsum⟩ := hD s le_rfl
  exact hs t hts hne hsum

/-- Ground truth: in `C_3`, the sequence `1·1` is zero-sum free. -/
example : ZeroSumFree ({1, 1} : Multiset (ZMod 3)) := by
  rw [zeroSumFree_iff_powerset]
  decide

/-- Ground truth: in `C_3`, the sequence `1·2` is not zero-sum free. -/
example : ¬ ZeroSumFree ({1, 2} : Multiset (ZMod 3)) := by
  rw [zeroSumFree_iff_powerset]
  decide

/-- Ground truth: Baayen's group `C_2^4 ⊕ C_6` has `d* = 9`. -/
example : dStar [2, 2, 2, 2, 6] = 9 := rfl

/-! ## The group `B_m` and the sequence `S_m` -/

/-- `B_m = C_m^3 ⊕ C_{2m}^4 ⊕ C_{6m}`, coordinates `(z, y, e)`. -/
abbrev B (m : ℕ) : Type := (Fin 3 → ZMod m) × (Fin 4 → ZMod (2 * m)) × ZMod (6 * m)

/-- The generator `e` of the summand `C_{6m}`. -/
def e (m : ℕ) : B m := (0, 0, 1)

/-- The generators `y_1, …, y_4` of the summands `C_{2m}` (0-indexed). -/
def y (m : ℕ) (j : Fin 4) : B m := (0, Pi.single j 1, 0)

/-- The generators `z_1, z_2, z_3` of the summands `C_m` (0-indexed). -/
def z (m : ℕ) (i : Fin 3) : B m := (Pi.single i 1, 0, 0)

/-- `q_j = y_j + 2e` for `1 ≤ j ≤ 4` (paper eq. `q-first`, 0-indexed). -/
def qy (m : ℕ) (j : Fin 4) : B m := y m j + 2 • e m

/-- `q_{4+i} = z_i + ∑_{j ≠ i} y_j + 2e` for `1 ≤ i ≤ 3` (paper eq. `q-last`,
0-indexed; `j` ranges over the four `y`-indices). -/
def qz (m : ℕ) (i : Fin 3) : B m :=
  z m i + (∑ j ∈ Finset.univ.filter (fun j : Fin 4 => j ≠ Fin.castSucc i), y m j) + 2 • e m

/-- The seven elements `q_1, …, q_7`. -/
def q (m : ℕ) : Fin 7 → B m := ![qy m 0, qy m 1, qy m 2, qy m 3, qz m 0, qz m 1, qz m 2]

/-- The paper's sequence `S_m = e^{4m-1} ∏_{j=1}^7 q_j^{2m-1}` over `B_m`
(used for `m ≥ 1`). -/
def S (m : ℕ) : Multiset (B m) :=
  Multiset.replicate (4 * m - 1) (e m) + ∑ j : Fin 7, Multiset.replicate (2 * m - 1) (q m j)

/-- Ground truth: `q_5 = z_1 + y_2 + y_3 + y_4 + 2e` in `B_2`. -/
example : q 2 4 = (![1, 0, 0], ![0, 1, 1, 1], 2) := by decide

/-- Ground truth: `q_2 = y_2 + 2e` in `B_2`. -/
example : q 2 1 = (0, ![0, 1, 0, 0], 2) := by decide

/-! ## Coordinates of the support -/

/-- The eight support elements `e, q_1, …, q_7`. -/
def gen (m : ℕ) : Fin 8 → B m := Fin.cons (e m) (q m)

/-- Their multiplicities `4m-1, 2m-1, …, 2m-1` in `S_m`. -/
def mult (m : ℕ) : Fin 8 → ℕ :=
  ![4 * m - 1, 2 * m - 1, 2 * m - 1, 2 * m - 1, 2 * m - 1, 2 * m - 1, 2 * m - 1, 2 * m - 1]

/-- `z`-coordinates of `gen k` as natural numbers. -/
def zCoeff : Fin 8 → Fin 3 → ℕ :=
  ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, 0], ![0, 1, 0],
    ![0, 0, 1]]

/-- `y`-coordinates of `gen k` as natural numbers. -/
def yCoeff : Fin 8 → Fin 4 → ℕ :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 1, 1, 1],
    ![1, 0, 1, 1], ![1, 1, 0, 1]]

/-- `e`-coordinates of `gen k` as natural numbers. -/
def eCoeff : Fin 8 → ℕ := ![1, 2, 2, 2, 2, 2, 2, 2]

/-- `S_m` is the sum of the eight replicate blocks. -/
theorem S_eq (m : ℕ) : S m = ∑ k : Fin 8, Multiset.replicate (mult m k) (gen m k) := by
  rw [Fin.sum_univ_succ]
  rfl

/-- The support elements in coordinates. -/
theorem gen_eq (m : ℕ) (k : Fin 8) :
    gen m k = ((fun i => (zCoeff k i : ZMod m)), (fun j => (yCoeff k j : ZMod (2 * m))),
      (eCoeff k : ZMod (6 * m))) := by
  fin_cases k <;>
  · simp only [gen, q]
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
    all_goals
      first
      | (fin_cases i <;> simp [qy, qz, e, y, z, zCoeff, Finset.sum_filter, Fin.sum_univ_four])
      | (fin_cases j <;> simp [qy, qz, e, y, z, yCoeff, Finset.sum_filter, Fin.sum_univ_four])
      | simp [qy, qz, e, y, z, eCoeff, Finset.sum_filter, Fin.sum_univ_four]

/-- A nonnegative combination `∑ f k • gen k`, coordinatewise. -/
theorem sum_nsmul_gen (m : ℕ) (f : Fin 8 → ℕ) :
    ∑ k, f k • gen m k = ((fun i => ((∑ k, f k * zCoeff k i : ℕ) : ZMod m)),
      (fun j => ((∑ k, f k * yCoeff k j : ℕ) : ZMod (2 * m))),
      ((∑ k, f k * eCoeff k : ℕ) : ZMod (6 * m))) := by
  simp_rw [gen_eq]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
  · simp [Prod.fst_sum, Finset.sum_apply]
  · simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
  · simp [Prod.snd_sum]

/-- The `y`-coordinate patterns of the eight support elements are distinct. -/
theorem yCoeff_injective : Function.Injective yCoeff := by decide

/-- For `m ≥ 1` the eight support elements `e, q_1, …, q_7` are distinct. -/
theorem gen_injective (m : ℕ) (hm : 1 ≤ m) : Function.Injective (gen m) := by
  intro k l hkl
  apply yCoeff_injective
  funext j
  have h := congrArg (fun g : B m => g.2.1 j) hkl
  simp only [gen_eq] at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have hk : yCoeff k j < 2 := by fin_cases k <;> fin_cases j <;> decide
  have hl : yCoeff l j < 2 := by fin_cases l <;> fin_cases j <;> decide
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

/-- The multiplicity of `gen k` in `S_m` is `mult k`. -/
theorem count_S (m : ℕ) (hm : 1 ≤ m) (k : Fin 8) : (S m).count (gen m k) = mult m k := by
  rw [S_eq, Multiset.count_sum']
  simp_rw [Multiset.count_replicate, (gen_injective m hm).eq_iff]
  simp

/-- Every term of `S_m` is one of `e, q_1, …, q_7`. -/
theorem exists_eq_gen_of_mem_S (m : ℕ) {x : B m} (hx : x ∈ S m) : ∃ k, x = gen m k := by
  rw [S_eq, Multiset.mem_sum] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact ⟨k, Multiset.eq_of_mem_replicate hk⟩

/-- The sum of a subsequence `T ∣ S_m` is `∑ v_{gen k}(T) • gen k`. -/
theorem sum_eq_of_le_S (m : ℕ) (hm : 1 ≤ m) (t : Multiset (B m)) (ht : t ≤ S m) :
    t.sum = ∑ k, t.count (gen m k) • gen m k := by
  rw [Finset.sum_multiset_count]
  have hsub : t.toFinset ⊆ Finset.univ.image (gen m) := by
    intro x hx
    obtain ⟨k, rfl⟩ := exists_eq_gen_of_mem_S m (Multiset.mem_of_le ht (Multiset.mem_toFinset.mp hx))
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  rw [Finset.sum_subset hsub (fun x _ hx => by
    rw [Multiset.count_eq_zero.mpr (by simpa using hx), zero_smul])]
  rw [Finset.sum_image (fun a _ b _ h => gen_injective m hm h)]

/-! ## The arithmetic core (Lemma 3.2 and the congruence argument) -/

/-- The reduced system (paper eqs. `a'j+=0mod2` and `c' + 2h ≡ 0 mod 6`) with
`c' ≤ 3` and `a'_j, b'_i ∈ {0, 1}` has only the zero solution; this is the
content of Lemma 3.2 (`lem:binary`) combined with the final step of the proof. -/
theorem reduced_eq_zero (c a1 a2 a3 a4 b1 b2 b3 : ℕ) (hc : c < 4) (ha1 : a1 < 2)
    (ha2 : a2 < 2) (ha3 : a3 < 2) (ha4 : a4 < 2) (hb1 : b1 < 2) (hb2 : b2 < 2) (hb3 : b3 < 2)
    (hy1 : 2 ∣ a1 + b2 + b3) (hy2 : 2 ∣ a2 + b1 + b3) (hy3 : 2 ∣ a3 + b1 + b2)
    (hy4 : 2 ∣ a4 + b1 + b2 + b3) (he : 6 ∣ c + 2 * (a1 + a2 + a3 + a4 + b1 + b2 + b3)) :
    c = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  interval_cases b1 <;> interval_cases b2 <;> interval_cases b3 <;> omega

/-- The coordinate congruences of a zero-sum subsequence `e^c ∏ q_j^{a_j} ∏ q_{4+i}^{b_i}`
of `S_m` (paper eqs. `y-coordinate`, `e-coordinate` and `m ∣ b_i`) force all
multiplicities to vanish. -/
theorem multiplicities_eq_zero (m c a1 a2 a3 a4 b1 b2 b3 : ℕ) (hm : 0 < m) (hc : c < 4 * m)
    (ha1 : a1 < 2 * m) (ha2 : a2 < 2 * m) (ha3 : a3 < 2 * m) (ha4 : a4 < 2 * m)
    (hb1 : b1 < 2 * m) (hb2 : b2 < 2 * m) (hb3 : b3 < 2 * m)
    (hz1 : m ∣ b1) (hz2 : m ∣ b2) (hz3 : m ∣ b3)
    (hy1 : 2 * m ∣ a1 + b2 + b3) (hy2 : 2 * m ∣ a2 + b1 + b3) (hy3 : 2 * m ∣ a3 + b1 + b2)
    (hy4 : 2 * m ∣ a4 + b1 + b2 + b3)
    (he : 6 * m ∣ c + 2 * (a1 + a2 + a3 + a4 + b1 + b2 + b3)) :
    c = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  have hm2 : m ∣ 2 * m := Dvd.intro_left 2 rfl
  have hm6 : m ∣ 6 * m := Dvd.intro_left 6 rfl
  obtain ⟨b1', rfl⟩ := hz1
  obtain ⟨b2', rfl⟩ := hz2
  obtain ⟨b3', rfl⟩ := hz3
  have ha1m : m ∣ a1 := (Nat.dvd_add_right (dvd_mul_right m (b2' + b3'))).mp
    (by rw [show m * (b2' + b3') + a1 = a1 + m * b2' + m * b3' by ring]; exact hm2.trans hy1)
  have ha2m : m ∣ a2 := (Nat.dvd_add_right (dvd_mul_right m (b1' + b3'))).mp
    (by rw [show m * (b1' + b3') + a2 = a2 + m * b1' + m * b3' by ring]; exact hm2.trans hy2)
  have ha3m : m ∣ a3 := (Nat.dvd_add_right (dvd_mul_right m (b1' + b2'))).mp
    (by rw [show m * (b1' + b2') + a3 = a3 + m * b1' + m * b2' by ring]; exact hm2.trans hy3)
  have ha4m : m ∣ a4 := (Nat.dvd_add_right (dvd_mul_right m (b1' + b2' + b3'))).mp
    (by rw [show m * (b1' + b2' + b3') + a4 = a4 + m * b1' + m * b2' + m * b3' by ring]
        exact hm2.trans hy4)
  obtain ⟨a1', rfl⟩ := ha1m
  obtain ⟨a2', rfl⟩ := ha2m
  obtain ⟨a3', rfl⟩ := ha3m
  obtain ⟨a4', rfl⟩ := ha4m
  have hcm : m ∣ c := (Nat.dvd_add_left
    (dvd_mul_of_dvd_right (dvd_mul_right m (a1' + a2' + a3' + a4' + b1' + b2' + b3')) 2)).mp
    (by
      rw [show c + 2 * (m * (a1' + a2' + a3' + a4' + b1' + b2' + b3')) =
        c + 2 * (m * a1' + m * a2' + m * a3' + m * a4' + m * b1' + m * b2' + m * b3') by ring]
      exact hm6.trans he)
  obtain ⟨c', rfl⟩ := hcm
  have lt2 : ∀ x : ℕ, m * x < 2 * m → x < 2 := fun x hx =>
    Nat.lt_of_mul_lt_mul_left (a := m) (by rw [mul_comm m 2]; exact hx)
  have lt4 : ∀ x : ℕ, m * x < 4 * m → x < 4 := fun x hx =>
    Nat.lt_of_mul_lt_mul_left (a := m) (by rw [mul_comm m 4]; exact hx)
  have d2 : ∀ x : ℕ, 2 * m ∣ m * x → 2 ∣ x := fun x hx =>
    (Nat.mul_dvd_mul_iff_left hm).mp (by rw [mul_comm m 2]; exact hx)
  have d6 : ∀ x : ℕ, 6 * m ∣ m * x → 6 ∣ x := fun x hx =>
    (Nat.mul_dvd_mul_iff_left hm).mp (by rw [mul_comm m 6]; exact hx)
  have key := reduced_eq_zero c' a1' a2' a3' a4' b1' b2' b3' (lt4 _ hc) (lt2 _ ha1) (lt2 _ ha2)
    (lt2 _ ha3) (lt2 _ ha4) (lt2 _ hb1) (lt2 _ hb2) (lt2 _ hb3)
    (d2 _ (by rw [show m * (a1' + b2' + b3') = m * a1' + m * b2' + m * b3' by ring]; exact hy1))
    (d2 _ (by rw [show m * (a2' + b1' + b3') = m * a2' + m * b1' + m * b3' by ring]; exact hy2))
    (d2 _ (by rw [show m * (a3' + b1' + b2') = m * a3' + m * b1' + m * b2' by ring]; exact hy3))
    (d2 _ (by
      rw [show m * (a4' + b1' + b2' + b3') = m * a4' + m * b1' + m * b2' + m * b3' by ring]
      exact hy4))
    (d6 _ (by
      rw [show m * (c' + 2 * (a1' + a2' + a3' + a4' + b1' + b2' + b3')) =
        m * c' + 2 * (m * a1' + m * a2' + m * a3' + m * a4' + m * b1' + m * b2' + m * b3') by
          ring]
      exact he))
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := key
  subst h0 h1 h2 h3 h4 h5 h6 h7
  simp

/-! ## Theorem 3.1, core case -/

/-- **Theorem 3.1 (core case, arXiv:2609.29878).** For every `m ≥ 1` the sequence
`S_m = e^{4m-1} ∏_{j=1}^7 q_j^{2m-1}` over `B_m = C_m^3 ⊕ C_{2m}^4 ⊕ C_{6m}` is
zero-sum free. -/
theorem zeroSumFree_S (m : ℕ) (hm : 1 ≤ m) : ZeroSumFree (S m) := by
  intro t ht hne hsum
  set n : Fin 8 → ℕ := fun k => t.count (gen m k)
  have hbound : ∀ k, n k ≤ mult m k := fun k =>
    (count_S m hm k) ▸ Multiset.count_le_of_le _ ht
  have hpos : ∃ k, 0 < n k := by
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨k, rfl⟩ := exists_eq_gen_of_mem_S m (Multiset.mem_of_le ht hx)
    exact ⟨k, Multiset.count_pos.mpr hx⟩
  rw [sum_eq_of_le_S m hm t ht, sum_nsmul_gen] at hsum
  have hz : ∀ i, m ∣ ∑ k, n k * zCoeff k i := fun i => by
    have h := congrArg (fun g : B m => g.1 i) hsum
    simp only [Prod.fst_zero, Pi.zero_apply] at h
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  have hy : ∀ j, 2 * m ∣ ∑ k, n k * yCoeff k j := fun j => by
    have h := congrArg (fun g : B m => g.2.1 j) hsum
    simp only [Prod.snd_zero, Prod.fst_zero, Pi.zero_apply] at h
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  have he : 6 * m ∣ ∑ k, n k * eCoeff k := by
    have h := congrArg (fun g : B m => g.2.2) hsum
    simp only [Prod.snd_zero] at h
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hy0 := hy 0
  have hy1 := hy 1
  have hy2 := hy 2
  have hy3 := hy 3
  simp only [zCoeff, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Fin.sum_univ_eight, mul_zero, Matrix.cons_val_one, add_zero,
    Matrix.cons_val, mul_one, zero_add, yCoeff, eCoeff] at hz0 hz1 hz2 hy0 hy1 hy2 hy3 he
  have hb0 := hbound 0
  have hb1 := hbound 1
  have hb2 := hbound 2
  have hb3 := hbound 3
  have hb4 := hbound 4
  have hb5 := hbound 5
  have hb6 := hbound 6
  have hb7 := hbound 7
  simp only [Fin.isValue, mult, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hzero := multiplicities_eq_zero m (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hz0 hz1 hz2 hy0 hy1 hy2 hy3 (by convert he using 1; ring)
  obtain ⟨k, hk⟩ := hpos
  fin_cases k <;> simp_all

/-- `|S_m| = 18m - 8` (stated without truncated subtraction). -/
theorem card_S_add_eight (m : ℕ) (hm : 1 ≤ m) : (S m).card + 8 = 18 * m := by
  simp only [S, Multiset.card_add, Multiset.card_replicate, Multiset.card_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- The invariant factors of `B_m`: `m ∣ m ∣ m ∣ 2m ∣ 2m ∣ 2m ∣ 2m ∣ 6m`. -/
def invariants (m : ℕ) : List ℕ := [m, m, m, 2 * m, 2 * m, 2 * m, 2 * m, 6 * m]

/-- Ground truth: the factors of `B_8 = C_8^3 ⊕ C_16^4 ⊕ C_48` form a divisor chain
starting above `1`, so they are its invariant factors and `r(B_8) = 8`. -/
example : (invariants 8).IsChain (· ∣ ·) ∧ 1 < (invariants 8).head! ∧
    (invariants 8).length = 8 := by
  refine ⟨?_, by decide, rfl⟩
  simp [invariants]

/-- Ground truth: `d*(B_8) = 7·3 + 15·4 + 47 = 128`. -/
example : dStar (invariants 8) = 128 := by decide

/-- `d*(B_m) = 17m - 8`, stated as `d*(B_m) + 8 = 17m`. -/
theorem dStar_invariants_add_eight (m : ℕ) (hm : 1 ≤ m) : dStar (invariants m) + 8 = 17 * m := by
  simp only [dStar, invariants, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  omega

/-- `|S_m| = d*(B_m) + m`. -/
theorem card_S (m : ℕ) (hm : 1 ≤ m) : (S m).card = dStar (invariants m) + m := by
  have h1 := card_S_add_eight m hm
  have h2 := dStar_invariants_add_eight m hm
  omega

/-- **Theorem 3.1, core case (arXiv:2609.29878).** For every `m ≥ 1`, the group
`B_m = C_m^3 ⊕ C_{2m}^4 ⊕ C_{6m}` carries a zero-sum-free sequence of length
`d*(B_m) + m`; hence `δ(B_m) = d(B_m) - d*(B_m) ≥ m`. -/
theorem exists_zeroSumFree_card_eq (m : ℕ) (hm : 1 ≤ m) :
    ∃ s : Multiset (B m), ZeroSumFree s ∧ s.card = dStar (invariants m) + m :=
  ⟨S m, zeroSumFree_S m hm, card_S m hm⟩

/-- Every element of `B_m` is a nonnegative combination of `z_1, z_2, z_3`,
`y_1, …, y_4` and `e`. -/
theorem eq_sum_nsmul_basis (m : ℕ) [NeZero m] (g : B m) :
    g = ∑ i, (g.1 i).val • z m i + ∑ j, (g.2.1 j).val • y m j + (g.2.2).val • e m := by
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
  · simp [z, y, e, Prod.fst_sum, Finset.sum_apply, Pi.single_apply, -ZMod.natCast_val,
      ZMod.natCast_zmod_val]
  · simp [z, y, e, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply,
      -ZMod.natCast_val, ZMod.natCast_zmod_val]
  · simp [z, y, e, Prod.snd_sum]

/-- Each support element `gen k` occurs in `S_m` when `m ≥ 1`. -/
theorem gen_mem_S (m : ℕ) (hm : 1 ≤ m) (k : Fin 8) : gen m k ∈ S m := by
  rw [← Multiset.count_pos, count_S m hm k]
  fin_cases k <;>
  · simp only [mult, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, tsub_pos_iff_lt]
    omega

/-- **Theorem 3.1, generation clause (core case).** For `m ≥ 1`, `supp(S_m)`
generates `B_m`. -/
theorem closure_S_eq_top (m : ℕ) (hm : 1 ≤ m) :
    AddSubgroup.closure {x | x ∈ S m} = ⊤ := by
  haveI : NeZero m := ⟨by omega⟩
  set H := AddSubgroup.closure {x | x ∈ S m} with hH
  have hgen : ∀ k, gen m k ∈ H := fun k => AddSubgroup.subset_closure (gen_mem_S m hm k)
  have he : e m ∈ H := hgen 0
  have hqy : ∀ j, qy m j ∈ H := by
    intro j
    fin_cases j
    exacts [hgen 1, hgen 2, hgen 3, hgen 4]
  have hqz : ∀ i, qz m i ∈ H := by
    intro i
    fin_cases i
    exacts [hgen 5, hgen 6, hgen 7]
  have hy : ∀ j, y m j ∈ H := fun j => by
    have hyj : y m j = qy m j - 2 • e m := by simp [qy]
    rw [hyj]
    exact H.sub_mem (hqy j) (H.nsmul_mem he 2)
  have hz : ∀ i, z m i ∈ H := fun i => by
    have hzi : z m i = qz m i -
        (∑ j ∈ Finset.univ.filter (fun j : Fin 4 => j ≠ Fin.castSucc i), y m j) - 2 • e m := by
      rw [qz]
      abel
    rw [hzi]
    exact H.sub_mem (H.sub_mem (hqz i) (H.sum_mem fun j _ => hy j)) (H.nsmul_mem he 2)
  rw [eq_top_iff]
  intro g _
  rw [eq_sum_nsmul_basis m g]
  exact H.add_mem (H.add_mem (H.sum_mem fun i _ => H.nsmul_mem (hz i) _)
    (H.sum_mem fun j _ => H.nsmul_mem (hy j) _)) (H.nsmul_mem he _)

/-- **Theorem 3.1 (`thm:main`), core case `B_m`, arXiv:2609.29878.** For every
`m ≥ 1`, `S_m = e^{4m-1} ∏_{j=1}^7 q_j^{2m-1}` is a zero-sum-free sequence over
`B_m = C_m^3 ⊕ C_{2m}^4 ⊕ C_{6m}` of length `|S_m| = d*(B_m) + m = 18m - 8` whose
support generates `B_m`. -/
theorem thm_3_1_core (m : ℕ) (hm : 1 ≤ m) :
    ZeroSumFree (S m) ∧ (S m).card = dStar (invariants m) + m ∧ (S m).card + 8 = 18 * m ∧
      AddSubgroup.closure {x | x ∈ S m} = ⊤ :=
  ⟨zeroSumFree_S m hm, card_S m hm, card_S_add_eight m hm, closure_S_eq_top m hm⟩

/-- Non-vacuity: the hypotheses of `thm_3_1_core` hold at `m = 1`, where `S_1` is a
nonempty sequence of length `10` over `C_2^4 ⊕ C_6`. -/
example : ZeroSumFree (S 1) ∧ (S 1).card = 10 :=
  ⟨(thm_3_1_core 1 le_rfl).1, by have h := (thm_3_1_core 1 le_rfl).2.2.1; omega⟩

/-- `HasDavenportBound` is upward closed in the length. -/
theorem HasDavenportBound.mono {G : Type*} [AddCommMonoid G] {ℓ ℓ' : ℕ}
    (h : HasDavenportBound G ℓ) (hle : ℓ ≤ ℓ') : HasDavenportBound G ℓ' :=
  fun s hs => h s (hle.trans hs)

/-- **Refutation of the Gao–Geroldinger conjecture** ([GG06, Conj. 3.7]; arXiv:2609.29878,
remark after Theorem 3.1).  For `m ≥ 8`, `G = B_m` has rank `8` and
`D(G) ≤ D*(G) + r(G) - 1` fails, where `D*(G) = d*(G) + 1` and `r(G) = 8` is the
length of the invariant-factor list. -/
theorem not_hasDavenportBound_of_eight_le (m : ℕ) (hm : 8 ≤ m) :
    ¬ HasDavenportBound (B m) (dStar (invariants m) + 1 + (invariants m).length - 1) := by
  intro hD
  have hlen : (invariants m).length = 8 := rfl
  have hcard := card_S m (by omega)
  exact not_hasDavenportBound_of_zeroSumFree (zeroSumFree_S m (by omega))
    (hD.mono (by omega))

/-- **The explicit counterexample `C_8^3 ⊕ C_16^4 ⊕ C_48`.**  Here `D*(G) = 129`,
`r(G) = 8`, and `S_8` is a zero-sum-free sequence of length `136 = D*(G) + r(G) - 1`,
so `D(G) ≥ 137 > D*(G) + r(G) - 1`, contradicting Gao–Geroldinger. -/
theorem gao_geroldinger_fails_at_eight :
    ¬ HasDavenportBound (B 8) (dStar (invariants 8) + 1 + (invariants 8).length - 1) :=
  not_hasDavenportBound_of_eight_le 8 le_rfl

end GaoGeroldinger
