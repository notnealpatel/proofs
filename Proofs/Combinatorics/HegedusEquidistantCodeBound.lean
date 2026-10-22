/-
# Hegedüs's equidistant-code bound via the equal-Gram lemma

Scott Duke Kominers, *An eigenvalue proof of Hegedüs's bound for codes
with a single Hamming distance*, arXiv:2606.24624, Lemma 1, Theorems 1–2,
and Remarks (b), (c), (e). The binary bound is Hegedüs, Australas. J.
Combin. 94 (2026), Theorem 1.3; the q-ary bound is Hu–Huang–Yu,
arXiv:2504.07036, Theorem 6.

The equal-Gram lemma bounds the number of vectors by dimension plus one.
It yields `m ≤ n` for positive-length binary equidistant codes except at
distance `(n+1)/2`, and `m ≤ n(q-1)` for q-ary codes except at
distance `((q-1)n+1)/q`.

## Formalization notes

* The Gram lemma is proved for an arbitrary finite-dimensional real inner
  product space `E` with `d = finrank ℝ E`, in the division-free form
  `s + d * t = 0`; `gram_lemma` is the paper's `ℝ^d`, `1 ≤ d`, `t = -s/d`
  form.  The proof avoids eigenvalues: equal Gram data with
  `s + (k - 1) t ≠ 0` forces linear independence (`linearIndependent_of_gram`);
  either all `m` vectors or the last `m - 1` of them satisfy this.
* `n` positive is a load-bearing hypothesis of Theorems 1 and 2: for `n = 0`
  a single word (`m = 1`) violates `m ≤ n`.
* Theorem 2 uses the simplex embedding scaled by `√q`, i.e.
  `φ(x)(i, a) = q·[x_i = a] - 1`, inside the subspace of
  `EuclideanSpace ℝ (Fin n × Fin q)` with zero row sums (dimension `n(q-1)`).
* Distances: `symmDiff`-cardinality for sets (the paper's \(|F\triangle G|\))
  and Mathlib's `hammingDist` for words.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.HegedusEquidistantCodeBound

open Module Finset

/-! ## The Gram lemma -/

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Vectors with common squared norm `s`, common pairwise inner product
`t < s`, and `s + (k - 1) t ≠ 0` (where `k` is their number) are linearly
independent.  Pairing a relation `∑ cᵢ wᵢ = 0` with `w_j` gives
`(s - t) c_j + t ∑ cᵢ = 0`; summing over `j` kills `∑ cᵢ`. -/
theorem linearIndependent_of_gram {ι : Type*} [Fintype ι] (w : ι → E) (s t : ℝ)
    (hst : t < s) (hn : ∀ i, inner ℝ (w i) (w i) = s)
    (hi : ∀ i j, i ≠ j → inner ℝ (w i) (w j) = t)
    (hsum : s + ((Fintype.card ι : ℝ) - 1) * t ≠ 0) : LinearIndependent ℝ w := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set S := ∑ i, g i with hS
  have hj : ∀ j, (s - t) * g j + t * S = 0 := by
    intro j
    have h0 : inner ℝ (∑ i, g i • w i) (w j) = 0 := by rw [hg, inner_zero_left]
    rw [sum_inner, ← Finset.add_sum_erase _ _ (mem_univ j)] at h0
    have hrest : ∑ i ∈ univ.erase j, inner ℝ (g i • w i) (w j) = t * (S - g j) := by
      rw [hS, ← Finset.add_sum_erase _ _ (mem_univ j), add_sub_cancel_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi' => ?_
      rw [real_inner_smul_left, hi i j (Finset.ne_of_mem_erase hi'), mul_comm]
    rw [hrest, real_inner_smul_left, hn] at h0
    linarith
  have hS0 : S * (s + ((Fintype.card ι : ℝ) - 1) * t) = 0 := by
    have htot : ∑ j, ((s - t) * g j + t * S) = 0 := Finset.sum_eq_zero fun j _ => hj j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hS] at htot
    linarith
  have hSz : S = 0 := (mul_eq_zero.mp hS0).resolve_right hsum
  intro i
  have hgi := hj i
  rw [hSz, mul_zero, add_zero] at hgi
  exact (mul_eq_zero.mp hgi).resolve_left (sub_ne_zero.mpr hst.ne')

/-- **Gram lemma (arXiv:2606.24624, Lemma 1), division-free form.**
If `w₁, …, w_m` in a finite-dimensional real inner product space of dimension
`d` have equal squared norms `s` and a common pairwise inner product `t < s`,
then `m ≤ d + 1`, and `m = d + 1` forces `s + d t = 0`. -/
theorem gram_simplex_bound [FiniteDimensional ℝ E] {m : ℕ} (w : Fin m → E) (s t : ℝ)
    (hst : t < s) (hn : ∀ i, inner ℝ (w i) (w i) = s)
    (hi : ∀ i j, i ≠ j → inner ℝ (w i) (w j) = t) :
    m ≤ finrank ℝ E + 1 ∧ (m = finrank ℝ E + 1 → s + (finrank ℝ E : ℝ) * t = 0) := by
  by_cases h : s + ((m : ℝ) - 1) * t = 0
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
      rcases m with _ | k
      · exfalso
        push_cast at h
        linarith
      · exact ⟨k, rfl⟩
    have hk : s + (k : ℝ) * t = 0 := by
      push_cast at h
      linarith
    have ht : t ≠ 0 := by
      rintro rfl
      rw [mul_zero, add_zero] at hk
      linarith
    have hsum : s + ((Fintype.card (Fin k) : ℝ) - 1) * t ≠ 0 := by
      rw [Fintype.card_fin]
      intro h'
      apply ht
      linarith
    have hli : LinearIndependent ℝ (w ∘ Fin.succ) :=
      linearIndependent_of_gram (w ∘ Fin.succ) s t hst (fun i => hn i.succ)
        (fun i j hij => hi i.succ j.succ (Fin.succ_injective _ |>.ne hij)) hsum
    have hle : k ≤ finrank ℝ E := by
      simpa using hli.fintype_card_le_finrank
    refine ⟨by omega, fun hm => ?_⟩
    have hkd : k = finrank ℝ E := by omega
    rw [← hkd]
    exact hk
  · have hli : LinearIndependent ℝ w :=
      linearIndependent_of_gram w s t hst hn hi (by rwa [Fintype.card_fin])
    have hle : m ≤ finrank ℝ E := by
      simpa using hli.fintype_card_le_finrank
    exact ⟨by omega, fun hm => by omega⟩

/-- The Gram lemma for vectors lying in a subspace `K`: the dimension is that
of `K`. -/
theorem gram_simplex_bound_submodule [FiniteDimensional ℝ E] (K : Submodule ℝ E) {m : ℕ}
    (w : Fin m → E) (hw : ∀ i, w i ∈ K) (s t : ℝ) (hst : t < s)
    (hn : ∀ i, inner ℝ (w i) (w i) = s) (hi : ∀ i j, i ≠ j → inner ℝ (w i) (w j) = t) :
    m ≤ finrank ℝ K + 1 ∧ (m = finrank ℝ K + 1 → s + (finrank ℝ K : ℝ) * t = 0) :=
  gram_simplex_bound (fun i => (⟨w i, hw i⟩ : K)) s t hst
    (fun i => by rw [Submodule.coe_inner]; exact hn i)
    (fun i j hij => by rw [Submodule.coe_inner]; exact hi i j hij)

end Gram

/-- **Lemma 1 of arXiv:2606.24624, as stated.**  For `d ≥ 1` and
`w₁, …, w_m ∈ ℝ^d` with `⟨wᵢ, wᵢ⟩ = s`, `⟨wᵢ, wⱼ⟩ = t` (`i ≠ j`) and `t < s`:
`m ≤ d + 1`, and if `m = d + 1` then `t = -s/d`. -/
theorem gram_lemma {d m : ℕ} (hd : 1 ≤ d) (w : Fin m → EuclideanSpace ℝ (Fin d)) (s t : ℝ)
    (hst : t < s) (hn : ∀ i, inner ℝ (w i) (w i) = s)
    (hi : ∀ i j, i ≠ j → inner ℝ (w i) (w j) = t) :
    m ≤ d + 1 ∧ (m = d + 1 → t = -s / d) := by
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  obtain ⟨hle, heq⟩ := gram_simplex_bound w s t hst hn hi
  rw [hfin] at hle heq
  refine ⟨hle, fun hm => ?_⟩
  have hd0 : (d : ℝ) ≠ 0 := by
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [eq_div_iff hd0]
  linarith [heq hm]

/-! ## The binary theorem (Hegedüs) -/

/-- The signed characteristic vector of `F ⊆ [n]`: `+1` on `F`, `-1` off `F`. -/
noncomputable def signVec {n : ℕ} (F : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if j ∈ F then 1 else -1)

/-- `⟨v_F, v_G⟩ = n - 2 |F △ G|` for signed characteristic vectors. -/
theorem inner_signVec {n : ℕ} (F G : Finset (Fin n)) :
    inner ℝ (signVec F) (signVec G) = (n : ℝ) - 2 * ((symmDiff F G).card : ℝ) := by
  classical
  have hpt : ∀ j : Fin n, inner ℝ ((signVec F) j) ((signVec G) j)
      = 1 - 2 * (if j ∈ symmDiff F G then (1 : ℝ) else 0) := by
    intro j
    by_cases hF : j ∈ F <;> by_cases hG : j ∈ G <;>
      norm_num [signVec, Finset.mem_symmDiff, hF, hG]
  rw [PiLp.inner_apply]
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp

/-- The paper's Remark (b) tetrahedron vectors `(+,+,+)` and
`(+,-,-)` have inner product `-1`. -/
example : inner ℝ (signVec ({0, 1, 2} : Finset (Fin 3))) (signVec {0}) = -1 := by
  rw [inner_signVec]
  have hcard : (symmDiff ({0, 1, 2} : Finset (Fin 3)) {0}).card = 2 := by decide
  rw [hcard]
  norm_num

/-- **Hegedüs's bound (arXiv:2606.24624, Theorem 1; Hegedüs 2026, Thm 1.3).**
If `F₁, …, F_m ⊆ [n]` (`n ≥ 1`) are pairwise at Hamming distance
`|Fᵢ △ Fⱼ| = ℓ` for a positive integer `ℓ` with `ℓ ≠ (n + 1)/2`, then
`m ≤ n`. -/
theorem hegedus_equidistant {n m ℓ : ℕ} (hn : 0 < n) (F : Fin m → Finset (Fin n))
    (hℓ : 1 ≤ ℓ) (hd : ∀ i j, i ≠ j → (symmDiff (F i) (F j)).card = ℓ)
    (hne : (ℓ : ℚ) ≠ ((n : ℚ) + 1) / 2) : m ≤ n := by
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  obtain ⟨hle, heq⟩ := gram_simplex_bound (fun i => signVec (F i)) (n : ℝ) ((n : ℝ) - 2 * ℓ)
    (by linarith)
    (fun i => by rw [inner_signVec, symmDiff_self, Finset.bot_eq_empty, Finset.card_empty]; simp)
    (fun i j hij => by rw [inner_signVec, hd i j hij])
  rw [hfin] at hle heq
  by_contra hlt
  have hm : m = n + 1 := by omega
  have h0 := heq hm
  apply hne
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (2 * ℓ : ℝ) = n + 1 := by
    have hfac : (n : ℝ) * (1 + n - 2 * ℓ) = 0 := by linear_combination h0
    have hlin := (mul_eq_zero.mp hfac).resolve_left hnr.ne'
    linarith
  have h2' : (2 * ℓ : ℚ) = n + 1 := by exact_mod_cast h2
  linarith

/-- The four sets `{1,2,3}, {1}, {2}, {3}` of Remark (b) (0-indexed). -/
def tetrahedronFamily : Fin 4 → Finset (Fin 3) := ![{0, 1, 2}, {0}, {1}, {2}]

/-- **Remark (b) of arXiv:2606.24624: the excluded distance is necessary.**
For `n = 3`, `ℓ = 2 = (n + 1)/2`, the four sets `{1,2,3}, {1}, {2}, {3}` are
pairwise at distance `2`, yet `4 > 3`; every other hypothesis of
`hegedus_equidistant` holds. -/
theorem tetrahedron_necessary :
    (∀ i j, i ≠ j → (symmDiff (tetrahedronFamily i) (tetrahedronFamily j)).card = 2) ∧
      ((2 : ℕ) : ℚ) = (((3 : ℕ) : ℚ) + 1) / 2 ∧ ¬ (4 ≤ 3) := by
  refine ⟨by decide, by norm_num, by decide⟩

/-- The rows of the Sylvester Hadamard matrix of order 4 as subsets of `[4]`
(0-indexed): `++++`, `+-+-`, `++--`, `+--+`. -/
def hadamardFamily : Fin 4 → Finset (Fin 4) := ![{0, 1, 2, 3}, {0, 2}, {0, 1}, {0, 3}]

/-- **Remark (c) of arXiv:2606.24624 at `n = 4`: sharpness and non-vacuity.**
The Hadamard family satisfies every hypothesis of `hegedus_equidistant`
(`ℓ = 2 ≠ 5/2`) with `m = n = 4`. -/
theorem hadamard_sharp :
    (∀ i j, i ≠ j → (symmDiff (hadamardFamily i) (hadamardFamily j)).card = 2) ∧
      ((2 : ℕ) : ℚ) ≠ (((4 : ℕ) : ℚ) + 1) / 2 := by
  refine ⟨by decide, by norm_num⟩

example : 4 ≤ 4 :=
  hegedus_equidistant (by norm_num) hadamardFamily (by norm_num) hadamard_sharp.1
    hadamard_sharp.2

/-! ## The q-ary theorem (Hu--Huang--Yu) -/

/-- The simplex embedding scaled by `√q`: the word `x ∈ [q]^n` goes to
`φ(x)(i, a) = q·[xᵢ = a] - 1`, i.e. `√q · f_{xᵢ}` in block `i` with
`f_a = √q (e_a - 𝟙/q)`. -/
noncomputable def simplexVec {n q : ℕ} (x : Fin n → Fin q) :
    EuclideanSpace ℝ (Fin n × Fin q) :=
  WithLp.toLp 2 (fun p => (q : ℝ) * (if x p.1 = p.2 then 1 else 0) - 1)

/-- `⟨φ(x), φ(y)⟩ = n (q² - q) - q² d_H(x, y)`. -/
theorem inner_simplexVec {n q : ℕ} (x y : Fin n → Fin q) :
    inner ℝ (simplexVec x) (simplexVec y)
      = (n : ℝ) * ((q : ℝ) * q - q) - (q : ℝ) * q * (hammingDist x y : ℝ) := by
  classical
  have hcoord : ∀ i : Fin n, ∑ a : Fin q, inner ℝ ((simplexVec x) (i, a)) ((simplexVec y) (i, a))
      = ((q : ℝ) * q - q) - (q : ℝ) * q * (if x i ≠ y i then 1 else 0) := by
    intro i
    have hterm : ∀ a : Fin q, inner ℝ ((simplexVec x) (i, a)) ((simplexVec y) (i, a))
        = (q : ℝ) * q * (if x i = a then (if y i = a then 1 else 0) else 0)
          - q * (if x i = a then 1 else 0) - q * (if y i = a then 1 else 0) + 1 := by
      intro a
      by_cases hx : x i = a <;> by_cases hy : y i = a <;> simp only [simplexVec, hx, hy, ↓reduceIte, RCLike.inner_apply, conj_trivial] <;> ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq,
      Finset.sum_ite_eq]
    by_cases hxy : x i = y i
    · simp [hxy]
    · have hyx : y i ≠ x i := fun h => hxy h.symm
      simp [hxy, hyx]
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp_rw [hcoord]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hammingDist]

/-- The row-sum map `v ↦ (i ↦ ∑ₐ v(i, a))`; its kernel is `U^n` with
`U = 𝟙^⊥ ⊆ ℝ^q`. -/
noncomputable def rowSum (n q : ℕ) : EuclideanSpace ℝ (Fin n × Fin q) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v i := ∑ a, v (i, a)
  map_add' v w := by
    funext i
    simp [Finset.sum_add_distrib]
  map_smul' c v := by
    funext i
    simp [Finset.mul_sum]

/-- Every embedded word lies in `U^n`. -/
theorem simplexVec_mem_ker {n q : ℕ} (x : Fin n → Fin q) :
    simplexVec x ∈ LinearMap.ker (rowSum n q) := by
  classical
  rw [LinearMap.mem_ker]
  funext i
  simp [rowSum, simplexVec, Finset.sum_sub_distrib]

/-- The row-sum map is surjective when `q ≥ 1`. -/
theorem rowSum_surjective {n q : ℕ} (hq : 0 < q) : Function.Surjective (rowSum n q) := by
  classical
  intro y
  refine ⟨WithLp.toLp 2 (fun p => if p.2 = ⟨0, hq⟩ then y p.1 else 0), ?_⟩
  funext i
  simp [rowSum]

/-- `dim U^n = n (q - 1)`. -/
theorem finrank_ker_rowSum {n q : ℕ} (hq : 0 < q) :
    finrank ℝ (LinearMap.ker (rowSum n q)) = n * (q - 1) := by
  have h := LinearMap.finrank_range_add_finrank_ker (rowSum n q)
  rw [LinearMap.range_eq_top.mpr (rowSum_surjective hq), finrank_top, Module.finrank_fin_fun,
    finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  rw [Nat.mul_sub, mul_one]
  omega

/-- **Hu--Huang--Yu (arXiv:2606.24624, Theorem 2; arXiv:2504.07036, Thm 6).**
For `n ≥ 1`, `q ≥ 2`, if words `x₁, …, x_m ∈ {0, …, q-1}^n` are pairwise at
Hamming distance `ℓ` for a positive integer `ℓ ≠ ((q - 1) n + 1)/q`, then
`m ≤ n (q - 1)`. -/
theorem huHuangYu_equidistant {n q m ℓ : ℕ} (hn : 0 < n) (hq : 2 ≤ q)
    (x : Fin m → (Fin n → Fin q)) (hℓ : 1 ≤ ℓ)
    (hd : ∀ i j, i ≠ j → hammingDist (x i) (x j) = ℓ)
    (hne : (ℓ : ℚ) ≠ (((q : ℚ) - 1) * n + 1) / q) : m ≤ n * (q - 1) := by
  have hq0 : 0 < q := by omega
  have hfin := finrank_ker_rowSum (n := n) hq0
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  obtain ⟨hle, heq⟩ := gram_simplex_bound_submodule (LinearMap.ker (rowSum n q))
    (fun i => simplexVec (x i)) (fun i => simplexVec_mem_ker (x i))
    ((n : ℝ) * ((q : ℝ) * q - q)) ((n : ℝ) * ((q : ℝ) * q - q) - (q : ℝ) * q * ℓ)
    (by nlinarith)
    (fun i => by rw [inner_simplexVec, hammingDist_self]; simp)
    (fun i j hij => by rw [inner_simplexVec, hd i j hij])
  rw [hfin] at hle heq
  by_contra hlt
  have hm : m = n * (q - 1) + 1 := by omega
  have h0 := heq hm
  apply hne
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : ((n * (q - 1) : ℕ) : ℝ) = (n : ℝ) * ((q : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at h0
  have hfac : (n : ℝ) * (q : ℝ) * ((q : ℝ) - 1) * (1 + ((q : ℝ) - 1) * n - q * ℓ) = 0 := by
    linear_combination h0
  have hpos : (n : ℝ) * (q : ℝ) * ((q : ℝ) - 1) ≠ 0 := by
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    have hqpos : (0 : ℝ) < q := by linarith
    exact (mul_pos (mul_pos hnr hqpos) hq1).ne'
  have h2 : (q : ℝ) * ℓ = ((q : ℝ) - 1) * n + 1 := by
    have hlin := (mul_eq_zero.mp hfac).resolve_left hpos
    linarith
  have h2' : (q : ℚ) * ℓ = ((q : ℚ) - 1) * n + 1 := by exact_mod_cast h2
  have hqQ : (q : ℚ) ≠ 0 := by
    have hqQpos : (0 : ℚ) < q := by exact_mod_cast hq0
    exact hqQpos.ne'
  rw [eq_div_iff hqQ, ← h2', mul_comm]

/-- **Remark (e) of arXiv:2606.24624 at `q = 3`, `n = 1`:** the three words of
length `1` are pairwise at distance `1 = ((q - 1)·1 + 1)/q`, and `3 > 2 = n (q - 1)`;
so the excluded distance is necessary in the q-ary theorem too. -/
theorem qary_excluded_necessary :
    (∀ i j : Fin 3, i ≠ j →
        hammingDist (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) = 1) ∧
      ((1 : ℕ) : ℚ) = ((((3 : ℕ) : ℚ) - 1) * ((1 : ℕ) : ℚ) + 1) / ((3 : ℕ) : ℚ) ∧
      ¬ (3 ≤ 1 * (3 - 1)) := by
  refine ⟨by decide, by norm_num, by decide⟩

/-- Non-vacuity of `huHuangYu_equidistant`: the words `00, 11, 22` over `[3]`
are pairwise at distance `2 ≠ 5/3`, and the theorem gives `3 ≤ 4`. -/
example : 3 ≤ 2 * (3 - 1) :=
  huHuangYu_equidistant (n := 2) (q := 3) (ℓ := 2) (by norm_num) (by norm_num)
    ![fun _ => 0, fun _ => 1, fun _ => 2] (by norm_num) (by decide) (by norm_num)

end Candidates.HegedusEquidistantCodeBound
