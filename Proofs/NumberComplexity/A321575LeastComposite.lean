/-
# A321575 — Israel: the non-squarefree least composite pretenders are 4, 9, 49

Robert Israel's conjecture in OEIS A321575 (2018): the only non-squarefree
least composite pretenders are `4,9,49`.

A finite certificate proves the result:

* `a n ≤ 561` because `561` satisfies the congruence for every residue
  (`cong_561`);
* for every non-squarefree `k ≤ 561` other than `4, 9, 49` and every residue
  `r` mod `k` satisfying the congruence, some composite `j < k` from a fixed
  list of twenty witnesses satisfies the congruence at every lift of `r`
  modulo `k * j` (`certificate`), so `k` is never the *least* composite.

## Definitional fidelity

* `n` ranges over `ℕ` (OEIS offset `0`); the congruence is evaluated in `ℤ`,
  so `n - 1 = -1` at `n = 0` (the entry's `a(0) = 9` uses `(-1)^9 = -1`).
* "composite" is `1 < k ∧ ¬ k.Prime`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A321575LeastComposite

/-! ## Definitions -/

/-- The defining congruence of A321575: `n^k - (n-1)^k ≡ 1 (mod k)`, computed
in `ℤ` (so that `n - 1` is a genuine integer at `n = 0`). -/
def Cong (k : ℕ) (n : ℤ) : Prop := n ^ k - (n - 1) ^ k ≡ 1 [ZMOD k]

/-- `k` is composite: `1 < k` and `k` is not prime. -/
def IsComposite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime

/-- The congruence is decidable (via `Int.ModEq`). -/
instance (k : ℕ) (n : ℤ) : Decidable (Cong k n) :=
  inferInstanceAs (Decidable (Int.ModEq _ _ _))

/-- Compositeness is decidable. -/
instance (k : ℕ) : Decidable (IsComposite k) :=
  inferInstanceAs (Decidable (1 < k ∧ ¬ k.Prime))

/-! ## Computable mirrors used by the certificate -/

/-- Boolean mirror of the congruence on a natural residue `r`, avoiding
subtraction: `r^k ≡ (r + k - 1)^k + 1 (mod k)`. -/
def cb (k r : ℕ) : Bool := r ^ k % k == ((r + k - 1) ^ k + 1) % k

/-- Boolean compositeness test by trial division. -/
def compB (k : ℕ) : Bool := 1 < k && (List.range k).any fun d => 2 ≤ d && k % d == 0

/-- Boolean test for a square factor `d * d` with `2 ≤ d < k`. -/
def hasSq (k : ℕ) : Bool := (List.range k).any fun d => 2 ≤ d && k % (d * d) == 0

/-- The twenty witness composites used by the certificate. -/
def witnesses : List ℕ := [4, 6, 9, 10, 14, 15, 21, 22, 26, 33, 34, 38, 39, 46, 49, 51, 57,
  65, 69, 133]

/-- The certificate condition for one modulus `k`: either `k` is squarefree, or
`k ∈ {4, 9, 49}`, or every residue `r` with the congruence has a smaller
witness `j` satisfying the congruence at every lift `r + k t` (`t < j`). -/
def certK (k : ℕ) : Bool :=
  !(hasSq k) || k == 4 || k == 9 || k == 49 ||
    (List.range k).all fun r => !(cb k r) ||
      witnesses.any fun j => j < k && (List.range j).all fun t => cb j ((r + k * t) % j)

/-! ## Bridges between the Boolean mirrors and the definitions -/

/-- The congruence for a natural `n` is decided by the Boolean mirror at the
residue `n % k`. -/
theorem cong_iff_cb (k n : ℕ) (hk : 0 < k) : Cong k n ↔ cb k (n % k) = true := by
  have hsub : ((n % k + k - 1 : ℕ) : ZMod k) = (n : ZMod k) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_mod,
      Nat.cast_one]
  unfold Cong cb
  rw [beq_iff_eq, ← ZMod.natCast_eq_natCast_iff', ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [hsub, ZMod.natCast_mod, sub_eq_iff_eq_add, add_comm]


/-- Compositeness agrees with the trial-division test `compB`. -/
theorem isComposite_iff_compB (k : ℕ) : IsComposite k ↔ compB k = true := by
  unfold IsComposite compB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨h1, hp⟩
    refine ⟨h1, ?_⟩
    rw [Nat.prime_def_lt] at hp
    push Not at hp
    obtain ⟨m, hmk, hdvd, hm1⟩ := hp (by omega)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hdvd
      omega
    exact ⟨m, hmk, by omega, Nat.mod_eq_zero_of_dvd hdvd⟩
  · rintro ⟨h1, d, hdk, h2d, hmod⟩
    refine ⟨h1, fun hp => ?_⟩
    have hd1 := (Nat.prime_def_lt.1 hp).2 d hdk (Nat.dvd_of_mod_eq_zero hmod)
    omega

/-- A positive non-squarefree number has a square factor `d * d` with
`2 ≤ d < k`, so the test `hasSq` succeeds. -/
theorem hasSq_of_not_squarefree (k : ℕ) (hk : 0 < k) (h : ¬ Squarefree k) :
    hasSq k = true := by
  unfold Squarefree at h
  push Not at h
  obtain ⟨x, hx, hxu⟩ := h
  rw [Nat.isUnit_iff] at hxu
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [mul_zero, zero_dvd_iff] at hx
    omega
  have hle : x * x ≤ k := Nat.le_of_dvd hk hx
  have hx2 : 2 ≤ x := by omega
  have hxk : x < k := by nlinarith
  unfold hasSq
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨x, hxk, hx2, Nat.mod_eq_zero_of_dvd hx⟩

/-! ## The Carmichael bound `a(n) ≤ 561` -/

/-- `561` (the smallest Carmichael number) satisfies the congruence for every
`n`; checked over all residues mod `561`. -/
theorem cong_561 (n : ℕ) : Cong 561 n := by
  rw [cong_iff_cb 561 n (by norm_num)]
  have h : (List.range 561).all (cb 561) = true := by decide +kernel
  rw [List.all_eq_true] at h
  exact h _ (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))

/-- `561 = 3 · 11 · 17` is composite. -/
theorem isComposite_561 : IsComposite 561 := (isComposite_iff_compB 561).2 (by decide +kernel)

/-- For every `n` some composite `k` satisfies the congruence (namely `561`). -/
theorem exists_composite_cong (n : ℕ) : ∃ k, IsComposite k ∧ Cong k n :=
  ⟨561, isComposite_561, cong_561 n⟩

/-- **A321575.** `a n` is the least composite `k` with
`n^k - (n-1)^k ≡ 1 (mod k)` (offset `0`, congruence evaluated in `ℤ`). -/
def a (n : ℕ) : ℕ := Nat.find (exists_composite_cong n)

/-- `a n` is composite and satisfies the congruence. -/
theorem a_spec (n : ℕ) : IsComposite (a n) ∧ Cong (a n) n :=
  Nat.find_spec (exists_composite_cong n)

/-- No composite below `a n` satisfies the congruence. -/
theorem a_min (n j : ℕ) (hj : j < a n) : ¬ (IsComposite j ∧ Cong j n) :=
  Nat.find_min (exists_composite_cong n) hj

/-- The Carmichael bound from the entry: `a n ≤ 561`. -/
theorem a_le_561 (n : ℕ) : a n ≤ 561 :=
  Nat.find_min' _ ⟨isComposite_561, cong_561 n⟩

/-! ## Examples -/

/-- Boolean check that `m` is the least composite satisfying the congruence
at `n`. -/
def isLeast (n m : ℕ) : Bool :=
  (compB m && cb m (n % m)) && (List.range m).all fun j => !(compB j && cb j (n % j))

/-- A successful `isLeast n m` check determines `a n = m`. -/
theorem a_eq_of_isLeast (n m : ℕ) (h : isLeast n m = true) : a n = m := by
  unfold isLeast at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    Bool.and_eq_false_iff] at h
  obtain ⟨⟨hcm, hcb⟩, hlt⟩ := h
  have hm := (isComposite_iff_compB m).2 hcm
  have hm0 : 0 < m := by have := hm.1; omega
  rw [a, Nat.find_eq_iff]
  refine ⟨⟨hm, (cong_iff_cb m n hm0).2 hcb⟩, fun j hj ⟨hjc, hjcong⟩ => ?_⟩
  have hj0 : 0 < j := by have := hjc.1; omega
  rcases hlt j hj with hf | hf
  · rw [(isComposite_iff_compB j).1 hjc] at hf
    exact Bool.false_ne_true hf.symm
  · rw [(cong_iff_cb j n hj0).1 hjcong] at hf
    exact Bool.false_ne_true hf.symm

/-- The first 81 terms listed in the entry (`a(0), …, a(80)`). -/
def listedTerms : List ℕ := [9, 4, 341, 4, 6, 4, 9, 4, 14, 4, 6, 4, 9, 4, 21, 4, 6, 4, 9, 4, 15,
  4, 6, 4, 9, 4, 10, 4, 6, 4, 9, 4, 62, 4, 6, 4, 9, 4, 49, 4, 6, 4, 9, 4, 33, 4, 6, 4, 9, 4, 14,
  4, 6, 4, 9, 4, 10, 4, 6, 4, 9, 4, 65, 4, 6, 4, 9, 4, 49, 4, 6, 4, 9, 4, 111, 4, 6, 4, 9, 4, 15]

/-- `a` agrees with every term listed in the entry. -/
theorem a_eq_listedTerms (n : ℕ) (hn : n < 81) : a n = listedTerms.getD n 0 := by
  have h : (List.range 81).all (fun i => isLeast i (listedTerms.getD i 0)) = true := by
    decide +kernel
  rw [List.all_eq_true] at h
  exact a_eq_of_isLeast _ _ (h n (List.mem_range.2 hn))

example : a 0 = 9 := a_eq_listedTerms 0 (by norm_num)
example : a 2 = 341 := a_eq_listedTerms 2 (by norm_num)
example : a 38 = 49 := a_eq_listedTerms 38 (by norm_num)

/-- The entry's comment: `a(422) = 561`, so the Carmichael bound is attained. -/
theorem a_422 : a 422 = 561 := a_eq_of_isLeast _ _ (by decide +kernel)


/-! ## The certificate -/

/-- The finite certificate: `certK k` holds for every `k ≤ 561`. -/
theorem certificate : (List.range 562).all certK = true := by
  decide +kernel

/-- Every witness in the certificate list is composite. -/
theorem witnesses_composite (j : ℕ) (hj : j ∈ witnesses) : IsComposite j := by
  have h : witnesses.all compB = true := by decide +kernel
  rw [List.all_eq_true] at h
  exact (isComposite_iff_compB j).2 (h j hj)

/-- Unpacked certificate: a non-squarefree `k ≤ 561` other than `4, 9, 49`
and a residue `r < k` satisfying the congruence admit a witness composite
`j < k` satisfying the congruence at every lift `r + k t`, `t < j`. -/
theorem exists_witness (k r : ℕ) (hk : k ≤ 561) (hsq : hasSq k = true) (h4 : k ≠ 4)
    (h9 : k ≠ 9) (h49 : k ≠ 49) (hr : r < k) (hc : cb k r = true) :
    ∃ j ∈ witnesses, j < k ∧ ∀ t < j, cb j ((r + k * t) % j) = true := by
  have h := certificate
  rw [List.all_eq_true] at h
  have hK := h k (List.mem_range.2 (by omega))
  simp only [certK, hsq, h4, h9, h49, Bool.not_true, Bool.false_or, beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_self, false_or,
    Bool.not_eq_true'] at hK
  rcases hK r hr with hf | hw
  · rw [hc] at hf
    exact absurd hf.symm Bool.false_ne_true
  · exact hw

/-- If the congruence for `j` holds at every lift `n % k + k t` (`t < j`), then
it holds at `n`. -/
theorem cong_of_lifts (k j n : ℕ) (hj : 0 < j)
    (h : ∀ t < j, cb j ((n % k + k * t) % j) = true) : Cong j n := by
  rw [cong_iff_cb j n hj]
  have ht := h ((n / k) % j) (Nat.mod_lt _ hj)
  have h1 : n % k + k * ((n / k) % j) ≡ n % k + k * (n / k) [MOD j] :=
    Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _))
  rw [Nat.mod_add_div n k] at h1
  rwa [h1] at ht

/-! ## The conjecture -/

/-- **Israel's conjecture (A321575, Robert Israel, 2018).**

This is the universal half: every term `a n` (`n ≥ 0`) is squarefree or lies
in `{4, 9, 49}`.  Proved by the finite certificate `certificate`. -/
theorem squarefree_or_mem (n : ℕ) : Squarefree (a n) ∨ a n ∈ ({4, 9, 49} : Finset ℕ) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hsqf, hmem⟩ := hcon
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
  obtain ⟨h4, h9, h49⟩ := hmem
  obtain ⟨hcomp, hcong⟩ := a_spec n
  have hpos : 0 < a n := by have := hcomp.1; omega
  have hsq := hasSq_of_not_squarefree _ hpos hsqf
  have hcb := (cong_iff_cb _ _ hpos).1 hcong
  obtain ⟨j, hjW, hjk, hall⟩ :=
    exists_witness (a n) (n % a n) (a_le_561 n) hsq h4 h9 h49 (Nat.mod_lt _ hpos) hcb
  have hjc := witnesses_composite j hjW
  have hj0 : 0 < j := by have := hjc.1; omega
  exact a_min n j hjk ⟨hjc, cong_of_lifts (a n) j n hj0 hall⟩

/-- **Israel's conjecture, exact form (A321575).** The set of non-squarefree
terms of the sequence is exactly `{4, 9, 49}`: the universal half is
`squarefree_or_mem`, and `a 1 = 4`, `a 0 = 9`, `a 38 = 49` show each value
occurs. -/
theorem nonsquarefree_terms :
    {m : ℕ | ∃ n, a n = m ∧ ¬ Squarefree m} = ({4, 9, 49} : Set ℕ) := by
  have hns : ∀ d : ℕ, d ≠ 1 → ¬ Squarefree (d * d) := fun d hd hsq =>
    hd (Nat.isUnit_iff.1 (hsq d dvd_rfl))
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, rfl, hsq⟩
    rcases squarefree_or_mem n with h | h
    · exact absurd h hsq
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, a_eq_listedTerms 1 (by norm_num), hns 2 (by norm_num)⟩
    · exact ⟨0, a_eq_listedTerms 0 (by norm_num), hns 3 (by norm_num)⟩
    · exact ⟨38, a_eq_listedTerms 38 (by norm_num), hns 7 (by norm_num)⟩

end Candidates.A321575LeastComposite

