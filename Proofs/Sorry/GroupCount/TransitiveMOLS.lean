/-
# Transitive MOLS: the MacNeish bound for disjoint group packets

## Source

Amadou Keita, Ilya Shapiro, *Transitive Sets of Mutually Orthogonal Latin Squares*,
arXiv:2601.22205, Section 4 ("MacNeish's conjecture"): Lemma `lem:conj`,
Theorem `thm:m2`, Remark `rem:dir` (direct counting proof) and Theorem `thm:stransconj`.
Formalized 2026-10-21.

A group packet `(G, H_i)_{i=1}^{q+2}` (paper, Definition `def:group-packet`) consists of
subgroups `H_i ≤ G` with a common pairwise intersection `H_i ∩ H_j = K` and indices
`[G : H_i] = [H_i : K] = n`; it is *disjoint* when `K = {e}`.  Simply transitive elements of
`q-MOLS(n)` correspond to disjoint group packets (Corollary `cor:strans`).

Verbatim claims:

* Theorem `thm:m2`: "Consider a transitive element of q-MOLS(n) and let (G,H_i)_{i=1}^{q+2}
  be a group packet in the equivalence class that corresponds to this element. ... For a
  prime p suppose that p^a | n and p^{a+1} ∤ n, if p ∤ |K|, then q ≤ p^a - 1."
* Remark `rem:dir`: "... 1+(q+2)(p^a-1) ≤ p^{2a} so (q+2)(p^a-1) ≤ p^{2a}-1=(p^a+1)(p^a-1)
  so q+2 ≤ p^a+1 so q ≤ p^a-1."
* Theorem `thm:stransconj`: "MacNeish's conjecture holds for simply transitive sets of MOLS."

## Status

Proved in the paper.  This module formalizes the group-theoretic upper bound for disjoint
group packets (`K = ⊥`, so `p ∤ |K|` holds for every `p`), i.e. the upper half of
Theorem `thm:stransconj` in its group-packet form, by the paper's own route: Lemma `lem:conj`
(conjugates of two packet members still meet trivially), Sylow conjugation of a subgroup of
order `p ^ a` of each `H_i` into one Sylow subgroup `P` of order `p ^ (2a)`, and the counting
of Remark `rem:dir`.  The MOLS ↔ group-packet correspondence (Theorem `thm:m1`,
Corollary `cor:strans`) and the MacNeish–Mann lower bound are not formalized here.
-/
import Mathlib

set_option autoImplicit false

open Pointwise

namespace TransitiveMOLS

variable {G : Type*} [Group G]

/-- A *disjoint group packet* of order `n` (arXiv:2601.22205, Definition `def:group-packet`
with `K = ⊥`): subgroups `H i ≤ G` with `[G : H i] = n`, `[H i : ⊥] = |H i| = n`, and
`H i ∩ H j = {e}` for `i ≠ j`.  With `ι = Fin (q + 2)` this is an element of `(q+2)-GP(n)`
with trivial `K`. -/
structure IsDisjointGroupPacket {ι : Type*} (H : ι → Subgroup G) (n : ℕ) : Prop where
  /-- `[G : H_i] = n`. -/
  index_eq : ∀ i, (H i).index = n
  /-- `[H_i : K] = |H_i| = n` since `K = ⊥`. -/
  card_eq : ∀ i, Nat.card (H i) = n
  /-- `H_i ∩ H_j = K = ⊥` for `i ≠ j`. -/
  inf_eq_bot : Pairwise fun i j => H i ⊓ H j = ⊥

/-- If `A ⊓ B = ⊥` and `|A| |B| = |G|` in a finite group, every `g : G` factors as
`g = a * b` with `a ∈ A`, `b ∈ B` (the product map `A × B → G` is a bijection). -/
theorem exists_mul_eq_of_inf_eq_bot [Finite G] {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    (hcard : Nat.card A * Nat.card B = Nat.card G) (g : G) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let f : A × B → G := fun x => (x.1 : G) * x.2
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : G) * b = a' * b' := hab
    have hmemA : (a' : G)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem a'.2) a.2
    have heq : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hab', mul_inv_cancel_right]
    have hmemB : (a' : G)⁻¹ * a ∈ B := heq ▸ B.mul_mem b'.2 (B.inv_mem b.2)
    have hone : (a' : G)⁻¹ * a = 1 := by
      have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B := ⟨hmemA, hmemB⟩
      rwa [hAB, Subgroup.mem_bot] at hmem
    have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp hone).symm
    have hb : b = b' := by
      subst ha
      exact Subtype.ext (mul_left_cancel hab')
    rw [ha, hb]
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  obtain ⟨⟨a, b⟩, hx⟩ := hbij.2 g
  exact ⟨a, a.2, b, b.2, hx⟩

/-- Paper's Lemma `lem:conj` for a disjoint packet (`K = ⊥`): if `A ⊓ B = ⊥` and
`|A| |B| = |G|`, then every pair of conjugates `x A x⁻¹`, `y B y⁻¹` still meets trivially. -/
theorem conj_smul_inf_conj_smul_eq_bot [Finite G] {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    (hcard : Nat.card A * Nat.card B = Nat.card G) (x y : G) :
    MulAut.conj x • A ⊓ MulAut.conj y • B = ⊥ := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hxy⟩ := exists_mul_eq_of_inf_eq_bot hAB hcard (x⁻¹ * y)
  have hA : MulAut.conj x • A = MulAut.conj (x * a₀) • A := by
    rw [map_mul, mul_smul, Subgroup.conj_smul_eq_self_of_mem ha₀]
  have hB : MulAut.conj y • B = MulAut.conj (x * a₀) • B := by
    have hy : y = x * a₀ * b₀ := by rw [mul_assoc, hxy, mul_inv_cancel_left]
    rw [hy, map_mul, mul_smul, Subgroup.conj_smul_eq_self_of_mem hb₀]
  rw [hA, hB, ← Subgroup.smul_inf, hAB, Subgroup.smul_bot]

/-- Counting step of the paper's Remark `rem:dir`: if `m` subgroups `A i ≤ B`, each of order
`c`, meet pairwise trivially, then their nonidentity elements are disjoint inside `B \ {1}`,
so `m (c - 1) + 1 ≤ |B|` (stated without truncated subtraction). -/
theorem card_mul_add_one_le {ι : Type*} [Finite ι] [Finite G] {A : ι → Subgroup G}
    {B : Subgroup G} {c : ℕ} (hle : ∀ i, A i ≤ B) (hcard : ∀ i, Nat.card (A i) = c)
    (hdisj : Pairwise fun i j => A i ⊓ A j = ⊥) :
    Nat.card ι * c + 1 ≤ Nat.card B + Nat.card ι := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ι := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card (α := ι)]
  let s : ι → Finset G := fun i => (A i : Set G).toFinset.erase 1
  have hs : ∀ i, (s i).card + 1 = c := by
    intro i
    rw [Finset.card_erase_add_one (by simp), ← hcard i]
    exact (Nat.card_eq_card_toFinset (A i : Set G)).symm
  have hpd : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint s := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    have hx : x ∈ A i ⊓ A j := by
      simp only [s, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hxi hxj
      exact ⟨hxi.2, hxj.2⟩
    rw [hdisj hij, Subgroup.mem_bot] at hx
    simp [s, hx] at hxi
  have hsub : (Finset.univ.biUnion s) ⊆ (B : Set G).toFinset.erase 1 := by
    intro x hx
    simp only [s, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase,
      Set.mem_toFinset, SetLike.mem_coe] at hx
    obtain ⟨i, hx1, hxi⟩ := hx
    simp only [Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe]
    exact ⟨hx1, hle i hxi⟩
  have hB : ((B : Set G).toFinset.erase 1).card + 1 = Nat.card B := by
    rw [Finset.card_erase_add_one (by simp)]
    exact (Nat.card_eq_card_toFinset (B : Set G)).symm
  have hsum := Finset.card_le_card hsub
  rw [Finset.card_biUnion hpd] at hsum
  have hsum' : ∑ i : ι, ((s i).card + 1) = Fintype.card ι * c := by
    simp [hs]
  rw [Finset.sum_add_distrib] at hsum'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum'
  omega

/-- If `p ^ a ∣ n` and `p ^ (a + 1) ∤ n` with `n ≠ 0`, then `a` is the `p`-adic valuation. -/
theorem factorization_eq_of_pow_dvd_of_not_pow_succ_dvd {n p a : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hpa : p ^ a ∣ n) (hpa' : ¬ p ^ (a + 1) ∣ n) : n.factorization p = a := by
  have hle : a ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).1 hpa
  have hlt : ¬ a + 1 ≤ n.factorization p := fun h => hpa' ((hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

/-- Arithmetic close of Remark `rem:dir`: with `q = p ^ a ≥ 2`, the inequality
`k q + 1 ≤ q ^ 2 + k` (i.e. `k (q - 1) ≤ (q - 1)(q + 1)`) forces `k ≤ q + 1`. -/
theorem le_add_one_of_mul_add_one_le {k q : ℕ} (hq : 2 ≤ q) (h : k * q + 1 ≤ q ^ 2 + k) :
    k ≤ q + 1 := by
  by_contra hk
  have hk' : q + 1 < k := Nat.lt_of_not_le hk
  nlinarith

/-- **Upper half of Theorem `thm:stransconj` (via Theorem `thm:m2` with `K = 1` and the
counting of Remark `rem:dir`), arXiv:2601.22205.** Let `G` be a finite group of order `n²` and
`H i` (`i : ι`) subgroups of order `n` meeting pairwise trivially (a disjoint group packet).
If `p` is a prime with `p ^ a ∣ n`, `p ^ (a + 1) ∤ n` and `0 < a`, then the number of
subgroups is at most `p ^ a + 1`. -/
theorem card_le_prime_pow_add_one [Finite G] {ι : Type*} [Finite ι] {n p a : ℕ}
    (hp : p.Prime) (hG : Nat.card G = n ^ 2) (H : ι → Subgroup G)
    (hH : ∀ i, Nat.card (H i) = n) (hdisj : Pairwise fun i j => H i ⊓ H j = ⊥)
    (ha : 0 < a) (hpa : p ^ a ∣ n) (hpa' : ¬ p ^ (a + 1) ∣ n) :
    Nat.card ι ≤ p ^ a + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : n ≠ 0 := by
    rintro rfl
    have hpos : 0 < Nat.card G := Nat.card_pos
    rw [hG] at hpos
    simp at hpos
  have hfac : n.factorization p = a :=
    factorization_eq_of_pow_dvd_of_not_pow_succ_dvd hp hn hpa hpa'
  -- A Sylow `p`-subgroup `P` of `G` has order `p ^ (2a)`.
  let P : Sylow p G := default
  have hP : Nat.card P = (p ^ a) ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_pow, Finsupp.smul_apply, hfac,
      smul_eq_mul, ← pow_mul, mul_comm]
  -- Each `H i` contains a subgroup `Q` of order `p ^ a`, which conjugates into `P`.
  have hQ : ∀ i, ∃ (g : G) (Q : Subgroup G),
      Q ≤ H i ∧ Nat.card Q = p ^ a ∧ MulAut.conj g • Q ≤ (P : Subgroup G) := by
    intro i
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H i) p
      (n := a) (by rw [hH i]; exact hpa)
    let Q : Subgroup G := K.map (H i).subtype
    have hQcard : Nat.card Q = p ^ a := by
      rw [Subgroup.card_map_of_injective (H i).subtype_injective, hK]
    obtain ⟨R, hR⟩ := (IsPGroup.of_card hQcard).exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
    refine ⟨g, Q, Subgroup.map_subtype_le K, hQcard, ?_⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hR
  choose g Q hQH hQcard hQP using hQ
  let A : ι → Subgroup G := fun i => MulAut.conj (g i) • Q i
  have hAcard : ∀ i, Nat.card (A i) = p ^ a := fun i =>
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj (g i)) (Q i)).toEquiv).symm.trans
      (hQcard i)
  have hAdisj : Pairwise fun i j => A i ⊓ A j = ⊥ := by
    intro i j hij
    have hbot := conj_smul_inf_conj_smul_eq_bot (hdisj hij)
      (by rw [hH i, hH j, hG, sq]) (g i) (g j)
    refine eq_bot_iff.2 (le_trans (inf_le_inf ?_ ?_) hbot.le)
    · exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 (hQH i)
    · exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 (hQH j)
  have hcount := card_mul_add_one_le (A := A) (B := (P : Subgroup G)) hQP hAcard hAdisj
  rw [hP] at hcount
  have hq : 2 ≤ p ^ a := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  exact le_add_one_of_mul_add_one_le hq hcount

/-- In a finite group carrying a disjoint group packet of order `n` with at least one member,
`|G| = n ^ 2` (from `|G| = |H_i| [G : H_i]`). -/
theorem IsDisjointGroupPacket.card_eq_sq [Finite G] {ι : Type*} [Nonempty ι]
    {H : ι → Subgroup G} {n : ℕ} (hpk : IsDisjointGroupPacket H n) : Nat.card G = n ^ 2 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [← (H i).card_mul_index, hpk.card_eq i, hpk.index_eq i, sq]

/-- **Theorem `thm:m2` for disjoint packets (`K = 1`), arXiv:2601.22205.** If
`(G, H_i)_{i=1}^{q+2}` is a disjoint group packet of order `n` in a finite group and `p` is a
prime with `p ^ a ∣ n`, `p ^ (a + 1) ∤ n`, `0 < a`, then `q ≤ p ^ a - 1`, stated as
`q < p ^ a`. -/
theorem thm_m2 [Finite G] {q n p a : ℕ} {H : Fin (q + 2) → Subgroup G}
    (hpk : IsDisjointGroupPacket H n) (hp : p.Prime) (ha : 0 < a) (hpa : p ^ a ∣ n)
    (hpa' : ¬ p ^ (a + 1) ∣ n) : q < p ^ a := by
  have hle := card_le_prime_pow_add_one hp hpk.card_eq_sq H hpk.card_eq hpk.inf_eq_bot ha
    hpa hpa'
  rw [Nat.card_fin] at hle
  omega

/-- **Upper half of Theorem `thm:stransconj` (MacNeish's bound for simply transitive MOLS,
group-packet form), arXiv:2601.22205.** If `(G, H_i)_{i=1}^{q+2}` is a disjoint group packet
of order `n` in a finite group, then for every prime `p ∣ n`, `q ≤ p ^ v_p(n) - 1`, stated as
`q < p ^ n.factorization p`; hence `q + 1` is at most the smallest prime-power part of `n`. -/
theorem thm_stransconj_upper [Finite G] {q n : ℕ} {H : Fin (q + 2) → Subgroup G}
    (hpk : IsDisjointGroupPacket H n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    q < p ^ n.factorization p := by
  have hn : n ≠ 0 := by
    have hpos : 0 < Nat.card (H 0) := Nat.card_pos
    rw [hpk.card_eq 0] at hpos
    exact hpos.ne'
  exact thm_m2 hpk hp (hp.factorization_pos_of_dvd hn hpn) (Nat.ordProj_dvd n p)
    (Nat.pow_succ_factorization_not_dvd hn hp)

/-! ### Ground truth: the Klein four-group packet `(F₂², three lines)` -/

/-- The Klein four-group `F₂ ⊕ F₂`, written multiplicatively. -/
abbrev Klein : Type := Multiplicative (ZMod 2 × ZMod 2)

/-- Generators of the three lines `ℓ_i` of `F₂ ⊕ F₂` (paper, packet `eq:maxmol` at `q = 2`). -/
def kleinGen : Fin 3 → Klein :=
  ![Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (1, 1)]

/-- The three lines of `F₂ ⊕ F₂` as subgroups. -/
def kleinLine (i : Fin 3) : Subgroup Klein := Subgroup.zpowers (kleinGen i)

/-- Each generator has order `2`. -/
theorem orderOf_kleinGen (i : Fin 3) : orderOf (kleinGen i) = 2 :=
  orderOf_eq_prime (by revert i; decide) (by revert i; decide)

/-- The line `ℓ_i` is exactly `{1, kleinGen i}`. -/
theorem mem_kleinLine (i : Fin 3) (y : Klein) : y ∈ kleinLine i ↔ y = 1 ∨ y = kleinGen i := by
  classical
  rw [kleinLine, mem_zpowers_iff_mem_range_orderOf, orderOf_kleinGen]
  revert i y
  decide

example : Nat.card Klein = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

/-- The three lines of `F₂ ⊕ F₂` form a disjoint group packet of order `2` (`q = 1`). -/
theorem kleinLine_isDisjointGroupPacket : IsDisjointGroupPacket kleinLine 2 := by
  have hcard : ∀ i, Nat.card (kleinLine i) = 2 := fun i => by
    rw [kleinLine, Nat.card_zpowers, orderOf_kleinGen]
  refine ⟨fun i => ?_, hcard, ?_⟩
  · have hG : Nat.card Klein = 4 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    have hmul := (kleinLine i).card_mul_index
    rw [hcard i, hG] at hmul
    omega
  · intro i j hij
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf, mem_kleinLine, mem_kleinLine] at hy
    rw [Subgroup.mem_bot]
    revert i j y
    decide

/-- Repeating a line does not give a disjoint packet: the intersection condition fails. -/
example : ¬ IsDisjointGroupPacket (fun _ : Fin 2 => kleinLine 0) 2 := by
  intro hpk
  have hbot := hpk.inf_eq_bot (show (0 : Fin 2) ≠ 1 by decide)
  have hmem : kleinGen 0 ∈ kleinLine 0 ⊓ kleinLine 0 :=
    ⟨(mem_kleinLine 0 _).2 (Or.inr rfl), (mem_kleinLine 0 _).2 (Or.inr rfl)⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact absurd hmem (by decide)

/-- Non-vacuity and sharpness: all hypotheses of `card_le_prime_pow_add_one` hold jointly for
the Klein packet (`n = 2`, `p = 2`, `a = 1`), where the bound `3 ≤ 2 ^ 1 + 1` is attained. -/
example : Nat.card (Fin 3) ≤ 2 ^ 1 + 1 :=
  card_le_prime_pow_add_one Nat.prime_two kleinLine_isDisjointGroupPacket.card_eq_sq kleinLine
    kleinLine_isDisjointGroupPacket.card_eq kleinLine_isDisjointGroupPacket.inf_eq_bot
    one_pos (by norm_num) (by norm_num)

/-- `thm_m2` instantiated on the Klein packet: `q = 1 < 2 = 2 ^ 1`. -/
example : 1 < 2 ^ 1 :=
  thm_m2 (q := 1) kleinLine_isDisjointGroupPacket Nat.prime_two one_pos (by norm_num)
    (by norm_num)

end TransitiveMOLS
