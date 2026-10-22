/-
# Cameron–Ellis–Raynaud: unipotent maps admit no proper cover

Peter J. Cameron, David Ellis and William Raynaud, *Smallest cyclically
covering subspaces of F_q^n, and lower bounds in Isbell's conjecture*,
arXiv:1810.03485: Theorem `thm:prime-power` (k = 1), Lemmas `lemma:peter`
and `lemma:peterII`, and the following corollary.

A subspace is cyclically covering if its cyclic shifts cover the space.
The results below are:
(A) If `T - 1` is nilpotent and every vector has a power of `T` in a
submodule `U`, then `U = ⊤`; this holds over any ring, without finite dimension.
(B) In characteristic `p` prime, every cyclically covering subspace of
`K^(p^d)` is the whole space.
(C) For `n ≥ 1`, this holds over `ZMod 2` iff `n` is a power of 2.

The proof of (A) descends along the images of `(T - 1)^j`. The other half
of the paper's corollary, `h_2(n) = 1 ↔ n = 3`, is not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace CameronEllisRaynaudCyclicCover

open Finset

section General

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- For an endomorphism `T`, `(T^k - 1)(T - 1)^j = (T - 1)^(j+1) (∑_{i<k} T^i)`. -/
theorem pow_sub_one_mul_pow_eq (T : Module.End R V) (k j : ℕ) :
    (T ^ k - 1) * (T - 1) ^ j = (T - 1) ^ (j + 1) * ∑ i ∈ range k, T ^ i := by
  have hc : Commute ((T - 1) ^ j) (T ^ k - 1) :=
    ((((Commute.refl T).sub_left (Commute.one_left T)).pow_left j).pow_right k).sub_right
      (Commute.one_right _)
  rw [← hc.eq, pow_succ, mul_assoc, mul_geom_sum]

/-- Descending step: if every `v` has a power `T^k v` in `U` and `U` contains the
image of `(T - 1)^(j+1)`, then `U` contains the image of `(T - 1)^j`. -/
theorem range_pow_le_of_range_pow_succ_le (T : Module.End R V) (U : Submodule R V)
    (hU : ∀ v, ∃ k : ℕ, (T ^ k) v ∈ U) (j : ℕ)
    (hj : LinearMap.range ((T - 1) ^ (j + 1)) ≤ U) :
    LinearMap.range ((T - 1) ^ j) ≤ U := by
  rintro v ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := hU (((T - 1) ^ j) x)
  have hid : (T ^ k) (((T - 1) ^ j) x) - ((T - 1) ^ j) x =
      ((T - 1) ^ (j + 1)) ((∑ i ∈ range k, T ^ i) x) := by
    have h := LinearMap.congr_fun (pow_sub_one_mul_pow_eq T k j) x
    simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] using h
  have hdiff : (T ^ k) (((T - 1) ^ j) x) - ((T - 1) ^ j) x ∈ U := by
    rw [hid]
    exact hj ⟨_, rfl⟩
  simpa using U.sub_mem hk hdiff

/-- General form of (A): over any ring, if `T - 1` is nilpotent and every vector has
some power `T^k v` inside the submodule `U`, then `U` is everything. -/
theorem eq_top_of_isNilpotent_sub_one (T : Module.End R V) (hT : IsNilpotent (T - 1))
    (U : Submodule R V) (hU : ∀ v, ∃ k : ℕ, (T ^ k) v ∈ U) : U = ⊤ := by
  obtain ⟨m, hm⟩ := hT
  have key : ∀ i, LinearMap.range ((T - 1) ^ (m - i)) ≤ U := by
    intro i
    induction i with
    | zero => simp [hm]
    | succ i ih =>
      rcases Nat.lt_or_ge i m with hi | hi
      · apply range_pow_le_of_range_pow_succ_le T U hU
        rwa [show m - (i + 1) + 1 = m - i by omega]
      · rwa [show m - (i + 1) = m - i by omega]
  have htop := key m
  rw [Nat.sub_self, pow_zero, Module.End.one_eq_id, LinearMap.range_id] at htop
  exact top_le_iff.mp htop

end General

/-- Part (A), Cameron–Ellis–Raynaud (arXiv:1810.03485, the `k = 1`, cyclic case of
Lemmas `lemma:peter`/`lemma:peterII`): for a finite-dimensional vector space `V` over a
field `K`, a linear map `T` with `T - 1` nilpotent, and a subspace `U` such that every
`v` has some `k` with `T^k v ∈ U`, we have `U = V`. -/
theorem unipotent_no_proper_cover {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V) (hT : IsNilpotent (T - 1)) (U : Submodule K V)
    (hU : ∀ v, ∃ k : ℕ, (T ^ k) v ∈ U) : U = ⊤ :=
  eq_top_of_isNilpotent_sub_one T hT U hU

/-- Non-vacuity of (A)'s hypotheses: `T = 1` with `U = ⊤` satisfies them. -/
example : IsNilpotent ((1 : Module.End ℚ (Fin 2 → ℚ)) - 1) ∧
    ∀ v : Fin 2 → ℚ, ∃ k : ℕ, ((1 : Module.End ℚ (Fin 2 → ℚ)) ^ k) v ∈ (⊤ : Submodule ℚ _) :=
  ⟨⟨1, by simp⟩, fun _ => ⟨0, Submodule.mem_top⟩⟩

/-! ## Cyclic shifts and cyclically covering subspaces -/

section Cyclic

/-- The cyclic shift `σ` on `K^n`, indexed by `ZMod n`: `(σ x) i = x (i - 1)`. -/
def shift (K : Type*) [Field K] (n : ℕ) [NeZero n] : Module.End K (ZMod n → K) :=
  LinearMap.funLeft K K (fun i : ZMod n => i - 1)

/-- Shifting the indicator of `0` in `(ZMod 2)^3` moves the `1` to index `1`. -/
example : shift (ZMod 2) 3 (fun i => if i = 0 then 1 else 0) 1 = 1 := by decide

/-- The shifted indicator vanishes at index `0`. -/
example : shift (ZMod 2) 3 (fun i => if i = 0 then 1 else 0) 0 = 0 := by decide

/-- Iterated shift: `(σ^k x) i = x (i - k)`. -/
theorem shift_pow_apply (K : Type*) [Field K] (n : ℕ) [NeZero n] (k : ℕ) (x : ZMod n → K)
    (i : ZMod n) : (shift K n ^ k) x i = x (i - k) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (shift K n ^ k) x (i - 1) = _
    rw [ih, Nat.cast_succ, sub_sub, add_comm (1 : ZMod n)]

/-- The shift has order dividing `n`: `σ^n = 1`. -/
theorem shift_pow_self (K : Type*) [Field K] (n : ℕ) [NeZero n] : shift K n ^ n = 1 := by
  ext x i
  simp [shift_pow_apply]

/-- `σ^{(-k).val}` inverts `σ^k` on both sides. -/
theorem shift_pow_neg_val_comp (K : Type*) [Field K] (n : ℕ) [NeZero n] (k : ℕ)
    (y : ZMod n → K) :
    (shift K n ^ (-(k : ZMod n)).val) ((shift K n ^ k) y) = y ∧
    (shift K n ^ k) ((shift K n ^ (-(k : ZMod n)).val) y) = y := by
  constructor <;> (ext i; simp [shift_pow_apply])

/-- A subspace `U ≤ K^n` is *cyclically covering* if every vector is moved into `U` by
some power of the cyclic shift (equivalently, by `cyclicallyCovering_iff`, the shifts
`σ^k(U)`, `0 ≤ k < n`, cover `K^n`, which is the paper's definition). -/
def CyclicallyCovering (K : Type*) [Field K] (n : ℕ) [NeZero n]
    (U : Submodule K (ZMod n → K)) : Prop :=
  ∀ x, ∃ k : ℕ, (shift K n ^ k) x ∈ U

/-- Equivalence with the paper's definition `⋃_{k<n} σ^k(U) = K^n`. -/
theorem cyclicallyCovering_iff (K : Type*) [Field K] (n : ℕ) [NeZero n]
    (U : Submodule K (ZMod n → K)) :
    CyclicallyCovering K n U ↔ ∀ x, ∃ k < n, x ∈ U.map (shift K n ^ k) := by
  constructor
  · intro h x
    obtain ⟨k, hk⟩ := h x
    exact ⟨(-(k : ZMod n)).val, ZMod.val_lt _, _, hk, (shift_pow_neg_val_comp K n k x).1⟩
  · intro h x
    obtain ⟨k, -, u, hu, rfl⟩ := h x
    exact ⟨(-(k : ZMod n)).val, by rwa [(shift_pow_neg_val_comp K n k u).1]⟩

/-- Non-vacuity: the whole space is cyclically covering. -/
example (K : Type*) [Field K] (n : ℕ) [NeZero n] : CyclicallyCovering K n ⊤ :=
  fun _ => ⟨0, Submodule.mem_top⟩

/-- In characteristic `p`, the shift on `K^(p^d)` is unipotent: `(σ - 1)^(p^d) = 0`. -/
theorem isNilpotent_shift_sub_one (p d : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] : IsNilpotent (shift K (p ^ d) - 1) := by
  refine ⟨p ^ d, ?_⟩
  have h := congrArg (Polynomial.aeval (shift K (p ^ d)))
    (sub_pow_char_pow (R := Polynomial K) (p := p) (n := d) Polynomial.X 1)
  simpa [shift_pow_self] using h

/-- Part (B), Cameron–Ellis–Raynaud Theorem `thm:prime-power` with `k = 1`
(arXiv:1810.03485): for a prime `p` and a field `K` of characteristic `p`, every
cyclically covering subspace of `K^(p^d)` is the whole space, i.e. `h_q(p^d) = 0`. -/
theorem charP_pow_no_proper_cover (p d : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (U : Submodule K (ZMod (p ^ d) → K)) (h : CyclicallyCovering K (p ^ d) U) : U = ⊤ :=
  eq_top_of_isNilpotent_sub_one _ (isNilpotent_shift_sub_one p d K) U h

end Cyclic

/-! ## The binary case: zeros of `h_2` -/

section Binary

/-- The hyperplane `{x : x 0 = x c}` of `(ZMod 2)^n`. -/
def pairHyperplane (n : ℕ) (c : ZMod n) : Submodule (ZMod 2) (ZMod n → ZMod 2) :=
  LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : ZMod n => ZMod 2) 0 -
    LinearMap.proj (R := ZMod 2) (φ := fun _ : ZMod n => ZMod 2) c)

/-- Membership in `pairHyperplane n c` means `x 0 = x c`. -/
theorem mem_pairHyperplane (n : ℕ) (c : ZMod n) (x : ZMod n → ZMod 2) :
    x ∈ pairHyperplane n c ↔ x 0 = x c := by
  simp [pairHyperplane, sub_eq_zero]

/-- Odd-cycle argument: if `n = 2^a m` with `m` odd, every `x : ZMod n → ZMod 2` has two
equal values at some `i` and `i + 2^a` (an odd cycle has no proper 2-colouring). -/
theorem exists_eq_add_of_odd (n a m : ℕ) (hn : n = 2 ^ a * m) (hm : Odd m)
    (x : ZMod n → ZMod 2) : ∃ i : ZMod n, x i = x (i + ((2 ^ a : ℕ) : ZMod n)) := by
  set c : ZMod n := ((2 ^ a : ℕ) : ZMod n) with hc
  by_contra h
  simp only [not_exists] at h
  have hstep : ∀ i, x (i + c) = x i + 1 := by
    intro i
    have hne := h i
    generalize x i = u at hne ⊢
    generalize x (i + c) = w at hne ⊢
    revert u w
    decide
  have hiter : ∀ j : ℕ, x ((j : ZMod n) * c) = x 0 + j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.cast_succ, add_mul, one_mul, hstep, ih]; push_cast; ring
  have hm0 : (m : ZMod n) * c = 0 := by
    rw [hc, ← Nat.cast_mul, mul_comm, ← hn, ZMod.natCast_self]
  have hm1 : (m : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp hm, Nat.cast_one]
  have hcontra := hiter m
  rw [hm0, hm1] at hcontra
  revert hcontra
  generalize x 0 = u
  revert u
  decide

/-- CER Lemma `lemma:simple`-type construction: for `n = 2^a m` with `m` odd, the
hyperplane `x 0 = x (2^a)` is cyclically covering. -/
theorem pairHyperplane_cyclicallyCovering (n a m : ℕ) [NeZero n] (hn : n = 2 ^ a * m)
    (hm : Odd m) : CyclicallyCovering (ZMod 2) n (pairHyperplane n ((2 ^ a : ℕ) : ZMod n)) := by
  intro x
  obtain ⟨i, hi⟩ := exists_eq_add_of_odd n a m hn hm x
  refine ⟨(-i).val, ?_⟩
  rw [mem_pairHyperplane, shift_pow_apply, shift_pow_apply, ZMod.natCast_zmod_val]
  simpa [add_comm] using hi

/-- The hyperplane `x 0 = x (2^a)` is proper when `2^a < n`. -/
theorem pairHyperplane_ne_top (n a : ℕ) [NeZero n] (ha : 2 ^ a < n) :
    pairHyperplane n ((2 ^ a : ℕ) : ZMod n) ≠ ⊤ := by
  intro htop
  have hmem : (Pi.single 0 1 : ZMod n → ZMod 2) ∈ pairHyperplane n ((2 ^ a : ℕ) : ZMod n) := by
    rw [htop]; exact Submodule.mem_top
  rw [mem_pairHyperplane] at hmem
  have hc : ((2 ^ a : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by positivity) ha
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hc] at hmem
  exact one_ne_zero hmem

/-- Example `h_2(3) ≥ 1`: in `(ZMod 2)^3` the hyperplane `x 0 = x 1` is cyclically
covering and proper. -/
example : CyclicallyCovering (ZMod 2) 3 (pairHyperplane 3 ((2 ^ 0 : ℕ) : ZMod 3)) ∧
    pairHyperplane 3 ((2 ^ 0 : ℕ) : ZMod 3) ≠ ⊤ :=
  ⟨pairHyperplane_cyclicallyCovering 3 0 3 rfl (by decide),
    pairHyperplane_ne_top 3 0 (by decide)⟩

/-- Part (C), the `h_2(n) = 0` half of the Corollary after Theorem `thm:prime-power` in
Cameron–Ellis–Raynaud (arXiv:1810.03485): for `n ≥ 1`, the only cyclically covering subspace
of `(ZMod 2)^n` is the whole space if and only if `n` is a power of `2`. -/
theorem forall_cyclicallyCovering_eq_top_iff (n : ℕ) [NeZero n] :
    (∀ U, CyclicallyCovering (ZMod 2) n U → U = ⊤) ↔ ∃ d, n = 2 ^ d := by
  constructor
  · intro h
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne n)
    by_cases hm1 : m = 1
    · exact ⟨a, by rw [hn, hm1, mul_one]⟩
    · exfalso
      have hm3 : 3 ≤ m := by obtain ⟨r, rfl⟩ := hm; omega
      have ha : 2 ^ a < n := by
        rw [hn]
        have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        nlinarith
      exact pairHyperplane_ne_top n a ha (h _ (pairHyperplane_cyclicallyCovering n a m hn hm))
  · rintro ⟨d, rfl⟩ U hU
    exact charP_pow_no_proper_cover 2 d (ZMod 2) U hU

end Binary

end CameronEllisRaynaudCyclicCover
