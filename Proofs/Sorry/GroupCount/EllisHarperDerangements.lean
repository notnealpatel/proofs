/-
# Ellis–Harper two-orbit derangements: the CFSG-free cases `n = p^k` and `n = b·p` with `2b ≤ p`

## Source

* M. Lee, T. Popiel, G. Verret, *Derangements in permutation groups with two
  orbits*, arXiv:2506.11396 (retrieved with `fetch 2506.11396`, 2026-10-21).
* The conjecture is D. Ellis and S. Harper, arXiv:2408.16064, Conjecture 2.

Verbatim (arXiv:2506.11396, Section 1):

> A classical theorem of Jordan asserts that if $G$ acts transitively on
> $\Omega$ and $|\Omega|\geq 2$, then $G$ contains a derangement. [...]
> Ellis and Harper have conjectured that this cannot happen if the two orbits
> have equal length $n \geq 2$ [...]. They have proved this conjecture in
> various cases, including [...] (iii) when $n$ is a prime power.

Verbatim (arXiv:2506.11396, Lemma 3.3 `NewBounds`, last clause):

> Let $p$ be a prime, let $P$ be a Sylow $p$-subgroup of $G$, let $|P|=p^d$
> and let $n=bp$ with $b<p$. [...] In particular, if $b<(p+1)/2$, then $P$
> contains a derangement.

Here `G` acts on `Ω` with exactly two orbits, both of length `n`; the paper
assumes a faithful action but the argument below does not need it.  The
condition `b < (p+1)/2` is `2b ≤ p` for integers.

## Status

Proved in the literature (Jordan 1872; Ellis–Harper for prime powers;
Lee–Popiel–Verret Lemma 3.3).  The full conjecture is claimed in
arXiv:2607.11543 (Anzanello–Eberhard) via CFSG; that is not formalized here.

## Proof route formalized (CFSG-free)

1. `iUnion_ne_univ_of_card_le_minFac`: at most `minFac |G|` proper subgroups
   never cover `G` (counting).
2. `pow_dvd_card_orbit_sylow` (the paper's Lemma 2.1, ref. [friends]): if
   `p^e` divides `|G·a|` then it divides `|P·a|` for a Sylow `p`-subgroup `P`.
3. `exists_derangement_of_isPGroup`: a `p`-group with no fixed points and at
   most `p` orbits has a derangement (each stabilizer lies in a maximal, hence
   normal, subgroup; normality makes one subgroup per orbit suffice).
4. `exists_derangement_of_pow_dvd_card_orbit`: if `p^e` (`e ≥ 1`) divides
   every orbit length and `|Ω| ≤ p^(e+1)` then a derangement exists; the two
   target cases are instances.
-/
import Mathlib

set_option autoImplicit false

namespace EllisHarperDerangements

open MulAction

/-- An element `g` of a group acting on `α` is a *derangement* if it fixes no
point of `α`. -/
def IsDerangement {G α : Type*} [Group G] [MulAction G α] (g : G) : Prop :=
  ∀ a : α, g • a ≠ a

/-- Ground truth: for the natural action of `Equiv.Perm α`, `IsDerangement`
is Mathlib's `derangements`. -/
theorem isDerangement_perm_iff {α : Type*} (σ : Equiv.Perm α) :
    IsDerangement (α := α) σ ↔ σ ∈ derangements α := Iff.rfl

/-- Ground truth: the 3-cycle `finRotate 3` is a derangement of `Fin 3`. -/
example : IsDerangement (α := Fin 3) (finRotate 3) := by
  unfold IsDerangement; decide

/-- Ground truth: the transposition `swap 0 1` fixes `2`, so it is not a
derangement of `Fin 3`. -/
example : ¬ IsDerangement (α := Fin 3) (Equiv.swap (0 : Fin 3) 1) := by
  unfold IsDerangement; decide

/-! ## Covering lemma -/

/-- At most `minFac |G|` proper subgroups of a finite group `G` never cover
`G`. -/
theorem iUnion_ne_univ_of_card_le_minFac {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Finite ι] (H : ι → Subgroup G) (hH : ∀ i, H i ≠ ⊤)
    (hk : Nat.card ι ≤ (Nat.card G).minFac) :
    (⋃ i, (H i : Set G)) ≠ Set.univ := by
  classical
  intro hU
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite ι
  -- `1` lies in some `H i₀`, so `ι` is nonempty.
  have h1 : (1 : G) ∈ ⋃ i, (H i : Set G) := hU ▸ Set.mem_univ _
  obtain ⟨i₀, -⟩ := Set.mem_iUnion.mp h1
  set N := Nat.card G with hN
  set m := N.minFac with hm
  have hNpos : 0 < N := Nat.card_pos
  -- each proper subgroup has index at least `m`
  have hidx : ∀ i, m ≤ (H i).index := by
    intro i
    have hne1 : (H i).index ≠ 1 := fun h => hH i (Subgroup.index_eq_one.mp h)
    have hne0 : (H i).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Nat.minFac_le_of_dvd (by omega) (Subgroup.index_dvd_card _)
  have hcard : ∀ i, Nat.card (H i) * m ≤ N := by
    intro i
    calc Nat.card (H i) * m ≤ Nat.card (H i) * (H i).index :=
          Nat.mul_le_mul_left _ (hidx i)
      _ = N := Subgroup.card_mul_index _
  have hm2 : 2 ≤ m := by
    have hidx0 := hidx i₀
    have hne1 : (H i₀).index ≠ 1 := fun h => hH i₀ (Subgroup.index_eq_one.mp h)
    have hle : (H i₀).index ≤ N := Nat.le_of_dvd hNpos (Subgroup.index_dvd_card _)
    have hN1 : N ≠ 1 := by
      have hne0 : (H i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    exact (Nat.minFac_prime hN1).two_le
  have hmN : m ≤ N := Nat.minFac_le hNpos
  -- the non-identity elements are covered by the sets `H i \ {1}`
  let c : ι → ℕ := fun i => Nat.card (H i)
  have hc : ∀ i, c i = (Finset.univ.filter (· ∈ H i)).card := by
    intro i
    simp only [c, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (Finset.univ : Finset G).erase 1 ⊆
      Finset.univ.biUnion (fun i => (Finset.univ.filter (· ∈ H i)).erase 1) := by
    intro g hg
    have hg1 : g ≠ 1 := Finset.ne_of_mem_erase hg
    have hgU : g ∈ ⋃ i, (H i : Set G) := hU ▸ Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hgU
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase,
      Finset.mem_filter]
    exact ⟨i, hg1, hi⟩
  set S := ∑ i, (c i - 1) with hS
  have hNS : N - 1 ≤ S := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card] at h
    refine h.trans (Finset.card_biUnion_le.trans (le_of_eq ?_))
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_erase_of_mem (by simp), ← hc]
  have hmS : m * S ≤ m * (N - m) := by
    calc m * S = ∑ i, m * (c i - 1) := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : ι, (N - m) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hci : c i * m ≤ N := hcard i
          rw [Nat.mul_sub_one, Nat.mul_comm]
          omega
      _ = Nat.card ι * (N - m) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
      _ ≤ m * (N - m) := Nat.mul_le_mul_right _ hk
  have hmS' : S ≤ N - m := Nat.le_of_mul_le_mul_left hmS (by omega)
  omega

/-! ## Derangements in `p`-groups -/

/-- Every proper subgroup of a finite `p`-group lies in a proper normal
subgroup (a maximal subgroup, normal by the normalizer condition). -/
theorem exists_normal_ne_top_le_of_isPGroup {p : ℕ} [Fact p.Prime] {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P) (H : Subgroup P) (hH : H ≠ ⊤) :
    ∃ M : Subgroup P, M.Normal ∧ M ≠ ⊤ ∧ H ≤ M := by
  have _ : Group.IsNilpotent P := hP.isNilpotent
  obtain hHtop | ⟨M, hMc, hHM⟩ := IsCoatomic.eq_top_or_exists_le_coatom H
  · exact absurd hHtop hH
  · exact ⟨M, Subgroup.NormalizerCondition.normal_of_coatom M
    Group.normalizerCondition_of_isNilpotent hMc, hMc.1, hHM⟩

/-- A finite `p`-group acting on a finite set with no fixed point and at most
`p` orbits contains a derangement. -/
theorem exists_derangement_of_isPGroup {p : ℕ} [hp : Fact p.Prime] {P α : Type*}
    [Group P] [Finite P] [MulAction P α] [Finite α] (hP : IsPGroup p P)
    (hfix : ∀ a : α, 1 < Nat.card (orbit P a))
    (horb : Nat.card (orbitRel.Quotient P α) ≤ p) :
    ∃ g : P, IsDerangement (α := α) g := by
  classical
  by_contra hno
  simp only [IsDerangement, not_exists, not_forall, not_not] at hno
  obtain ⟨a₀, -⟩ := hno 1
  -- stabilizers are proper
  have hstab : ∀ a : α, stabilizer P a ≠ ⊤ := by
    intro a htop
    have hsub : orbit P a ⊆ {a} := by
      rintro _ ⟨g, rfl⟩
      exact (mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top g))
    have hle : Nat.card (orbit P a) ≤ 1 := by
      have := Set.ncard_le_ncard hsub (Set.finite_singleton a)
      rw [Set.ncard_singleton] at this
      rwa [Nat.card_coe_set_eq]
    exact absurd (hfix a) (not_lt.mpr hle)
  -- one proper normal subgroup per orbit
  have hM : ∀ q : orbitRel.Quotient P α, ∃ M : Subgroup P,
      M.Normal ∧ M ≠ ⊤ ∧ stabilizer P q.out ≤ M := fun q =>
    exists_normal_ne_top_le_of_isPGroup hP _ (hstab q.out)
  choose M hMn hMtop hMle using hM
  -- these subgroups cover `P`
  have hcover : (⋃ q, (M q : Set P)) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨a, ha⟩ := hno g
    let q : orbitRel.Quotient P α := Quotient.mk (orbitRel P α) a
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    obtain ⟨h, hh⟩ : q.out ∈ orbit P a := Quotient.mk_out (s := orbitRel P α) a
    have hconj : h * g * h⁻¹ ∈ stabilizer P q.out := by
      rw [mem_stabilizer_iff, ← hh, mul_smul, mul_smul, inv_smul_smul, ha]
    have hmem := (hMn q).conj_mem _ (hMle q hconj) h⁻¹
    simpa [mul_assoc] using hmem
  -- `P` is nontrivial, so `minFac |P| = p`
  have hmin : (Nat.card P).minFac = p := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hsub : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact hstab a₀ (Subsingleton.elim _ _)
    rw [hk, hp.out.pow_minFac hk0]
  exact iUnion_ne_univ_of_card_le_minFac M hMtop (hmin ▸ horb) hcover

/-! ## Sylow orbit lengths -/

/-- Orbit–stabilizer in `Nat.card` form: `|G·a| · |G_a| = |G|`. -/
theorem card_orbit_mul_card_stabilizer {G α : Type*} [Group G] [MulAction G α] (a : α) :
    Nat.card (orbit G a) * Nat.card (stabilizer G a) = Nat.card G := by
  rw [Nat.card_coe_set_eq, ← index_stabilizer, Nat.mul_comm, Subgroup.card_mul_index]

/-- The paper's Lemma 2.1 (from its reference [friends]), divisibility form:
if `p^e` divides the length of the `G`-orbit of `a`, then it divides the length
of the orbit of `a` under a Sylow `p`-subgroup `P` of `G`. -/
theorem pow_dvd_card_orbit_sylow {p : ℕ} [hp : Fact p.Prime] {G α : Type*} [Group G]
    [Finite G] [MulAction G α] (P : Sylow p G) (a : α) {e : ℕ}
    (he : p ^ e ∣ Nat.card (orbit G a)) :
    p ^ e ∣ Nat.card (orbit (P : Subgroup G) a) := by
  have hpr := hp.out
  set N := (Nat.card G).factorization p with hN
  have hG := card_orbit_mul_card_stabilizer (G := G) a
  have hPc := card_orbit_mul_card_stabilizer (G := (P : Subgroup G)) a
  rw [P.card_eq_multiplicity, ← hN] at hPc
  -- `|P_a|` divides `|G_a|`
  have hstab : Nat.card (stabilizer (P : Subgroup G) a) ∣ Nat.card (stabilizer G a) := by
    have hle : (stabilizer (P : Subgroup G) a).map (P : Subgroup G).subtype ≤
        stabilizer G a := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at this
  -- both factors of `|P|` are powers of `p`
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hpr).mp (Dvd.intro _ hPc)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpr).mp (Dvd.intro_left _ hPc)
  have hij : i + j = N := by
    rw [hi, hj, ← pow_add] at hPc
    exact Nat.pow_right_injective hpr.two_le hPc
  have hGa0 : Nat.card (stabilizer G a) ≠ 0 := Nat.card_pos.ne'
  have hGo0 : Nat.card (orbit G a) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hG
    exact Nat.card_pos.ne' hG.symm
  have hjle : j ≤ (Nat.card (stabilizer G a)).factorization p :=
    (hpr.pow_dvd_iff_le_factorization hGa0).mp (hj ▸ hstab)
  have hele : e ≤ (Nat.card (orbit G a)).factorization p :=
    (hpr.pow_dvd_iff_le_factorization hGo0).mp he
  have hNsum : N = (Nat.card (orbit G a)).factorization p +
      (Nat.card (stabilizer G a)).factorization p := by
    rw [hN, ← hG, Nat.factorization_mul hGo0 hGa0, Finsupp.add_apply]
  rw [hi]
  exact Nat.pow_dvd_pow p (by omega)

/-! ## The general orbit-length criterion -/

/-- If `p^e` with `e ≥ 1` divides the length of every orbit of a finite group
`G` acting on a finite set `α`, and `|α| ≤ p^(e+1)`, then `G` contains a
derangement.  (A Sylow `p`-subgroup has at most `p` orbits, none trivial.) -/
theorem exists_derangement_of_pow_dvd_card_orbit {p e : ℕ} [hp : Fact p.Prime]
    {G α : Type*} [Group G] [Finite G] [MulAction G α] [Finite α] (he : 1 ≤ e)
    (hdvd : ∀ a : α, p ^ e ∣ Nat.card (orbit G a)) (hcard : Nat.card α ≤ p ^ (e + 1)) :
    ∃ g : G, IsDerangement (α := α) g := by
  classical
  have hpr := hp.out
  let P : Sylow p G := default
  have hPdvd : ∀ a : α, p ^ e ∣ Nat.card (orbit (P : Subgroup G) a) := fun a =>
    pow_dvd_card_orbit_sylow P a (hdvd a)
  have hPle : ∀ a : α, p ^ e ≤ Nat.card (orbit (P : Subgroup G) a) := by
    intro a
    have _ : Nonempty (orbit (P : Subgroup G) a) := ⟨⟨a, mem_orbit_self a⟩⟩
    exact Nat.le_of_dvd Nat.card_pos (hPdvd a)
  have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  have hfix : ∀ a : α, 1 < Nat.card (orbit (P : Subgroup G) a) := fun a =>
    lt_of_lt_of_le hpr.one_lt (hpe.trans (hPle a))
  let _ := Fintype.ofFinite (orbitRel.Quotient (P : Subgroup G) α)
  have horb : Nat.card (orbitRel.Quotient (P : Subgroup G) α) ≤ p := by
    have hsum : Nat.card α = ∑ q : orbitRel.Quotient (P : Subgroup G) α,
        Nat.card (orbit (P : Subgroup G) q.out) := by
      rw [Nat.card_congr (selfEquivSigmaOrbits (P : Subgroup G) α), Nat.card_sigma]
    have hlow : Nat.card (orbitRel.Quotient (P : Subgroup G) α) * p ^ e ≤ Nat.card α := by
      rw [hsum, Nat.card_eq_fintype_card, ← smul_eq_mul, ← Finset.card_univ,
        ← Finset.sum_const]
      exact Finset.sum_le_sum fun q _ => hPle q.out
    have hpe0 : 0 < p ^ e := pow_pos hpr.pos e
    rw [pow_succ'] at hcard
    exact Nat.le_of_mul_le_mul_right (hlow.trans hcard) hpe0
  obtain ⟨g, hg⟩ := exists_derangement_of_isPGroup P.isPGroup' hfix horb
  exact ⟨g, hg⟩

/-! ## The Ellis–Harper cases -/

/-- Ellis–Harper, prime-power case: if a finite group acts on a finite set
with exactly two orbits, both of length `n = p^k` (`p` prime, `k ≥ 1`), then it
contains a derangement. -/
theorem exists_derangement_of_two_orbits_prime_pow {p k : ℕ} [hp : Fact p.Prime]
    {G α : Type*} [Group G] [Finite G] [MulAction G α] [Finite α] (hk : 1 ≤ k)
    (hα : Nat.card α = 2 * p ^ k) (horb : ∀ a : α, Nat.card (orbit G a) = p ^ k) :
    ∃ g : G, IsDerangement (α := α) g := by
  refine exists_derangement_of_pow_dvd_card_orbit (p := p) (e := k) hk (fun a => by rw [horb a]) ?_
  rw [hα, pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ hp.out.two_le

/-- Lee–Popiel–Verret, Lemma 3.3 (last clause): if a finite group acts on a
finite set with exactly two orbits, both of length `n = b·p` with `p` prime,
`b ≥ 1` and `2b ≤ p` (i.e. `b < (p+1)/2`), then it contains a derangement. -/
theorem exists_derangement_of_two_orbits_mul_prime {p b : ℕ} [hp : Fact p.Prime]
    {G α : Type*} [Group G] [Finite G] [MulAction G α] [Finite α] (hb : 2 * b ≤ p)
    (hα : Nat.card α = 2 * (b * p)) (horb : ∀ a : α, Nat.card (orbit G a) = b * p) :
    ∃ g : G, IsDerangement (α := α) g := by
  refine exists_derangement_of_pow_dvd_card_orbit (p := p) (e := 1) le_rfl
    (fun a => by rw [horb a, pow_one]; exact dvd_mul_left p b) ?_
  rw [hα, ← Nat.mul_assoc, pow_two]
  exact Nat.mul_le_mul_right _ hb

/-- **Ellis–Harper two-orbit theorem, CFSG-free cases.**  Let a finite group
`G` act on a finite set `α` with exactly two orbits, both of length `n`
(`|α| = 2n` and every orbit has length `n`).  If `n = p^k` with `p` prime and
`k ≥ 1`, or `n = b·p` with `b ≥ 1` and `2b ≤ p`, then some `g ∈ G` fixes no
point.  (Ellis–Harper case (iii); Lee–Popiel–Verret, arXiv:2506.11396,
Lemma 3.3.) -/
theorem exists_derangement_of_two_orbits {p n : ℕ} [Fact p.Prime] {G α : Type*}
    [Group G] [Finite G] [MulAction G α] [Finite α] (hα : Nat.card α = 2 * n)
    (horb : ∀ a : α, Nat.card (orbit G a) = n)
    (hn : (∃ k, 1 ≤ k ∧ n = p ^ k) ∨ (∃ b, 1 ≤ b ∧ n = b * p ∧ 2 * b ≤ p)) :
    ∃ g : G, IsDerangement (α := α) g := by
  rcases hn with ⟨k, hk, rfl⟩ | ⟨b, -, rfl, hb⟩
  · exact exists_derangement_of_two_orbits_prime_pow hk hα horb
  · exact exists_derangement_of_two_orbits_mul_prime hb hα horb

/-! ## Jordan's theorem -/

/-- **Jordan's theorem.**  A finite group acting transitively on a finite set
with at least two points contains a derangement.  (Proof by Burnside's
lemma: the fixed-point counts sum to `|G|`, the identity alone contributes
`|α| ≥ 2`.) -/
theorem exists_derangement_of_isPretransitive {G α : Type*} [Group G] [Finite G]
    [MulAction G α] [Finite α] [IsPretransitive G α] (h : 2 ≤ Nat.card α) :
    ∃ g : G, IsDerangement (α := α) g := by
  classical
  by_contra hno
  simp only [IsDerangement, not_exists, not_forall, not_not] at hno
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite α
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group G α
  have hone : Fintype.card (Quotient (orbitRel G α)) = 1 := by
    obtain ⟨a₀, -⟩ := hno 1
    refine Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ a₀, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h a =>
      obtain ⟨g, hg⟩ := exists_smul_eq G a₀ a
      exact Quotient.sound ⟨g, hg⟩
  have hpos : ∀ g : G, 1 ≤ Fintype.card (fixedBy α g) := by
    intro g
    obtain ⟨a, ha⟩ := hno g
    exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
  have h1 : Fintype.card (fixedBy α (1 : G)) = Fintype.card α := by
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun a => one_smul G a)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset G)
    (fun g => Fintype.card (fixedBy α g)) (Finset.mem_univ 1)
  have hrest : (Finset.univ.erase (1 : G)).card ≤
      ∑ g ∈ Finset.univ.erase (1 : G), Fintype.card (fixedBy α g) := by
    have hle := Finset.card_nsmul_le_sum (Finset.univ.erase (1 : G))
      (fun g => Fintype.card (fixedBy α g)) 1 fun g _ => hpos g
    rwa [smul_eq_mul, mul_one] at hle
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hrest
  rw [hone, one_mul] at hburn
  rw [Nat.card_eq_fintype_card] at h
  have hG : 1 ≤ Fintype.card G := Fintype.card_pos
  omega

/-! ## Non-vacuity: a concrete two-orbit model

`Equiv.Perm (Fin 2)` acting on `Fin 2 ⊕ Fin 2` has exactly two orbits, both
of length `2`; this satisfies the hypotheses of every main theorem above. -/

/-- In the model `Equiv.Perm (Fin 2)` acting on `Fin 2 ⊕ Fin 2`, every orbit
has length `2`. -/
theorem card_orbit_perm_fin_two_sum (a : Fin 2 ⊕ Fin 2) :
    Nat.card (orbit (Equiv.Perm (Fin 2)) a) = 2 := by
  have key : ∀ (f : Fin 2 → Fin 2 ⊕ Fin 2), Function.Injective f →
      (∀ g : Equiv.Perm (Fin 2), ∀ x, g • f x = f (g x)) →
      ∀ x, Nat.card (orbit (Equiv.Perm (Fin 2)) (f x)) = 2 := by
    intro f hf hsmul x
    have horb : orbit (Equiv.Perm (Fin 2)) (f x) = Set.range f := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g x, (hsmul g x).symm⟩
      · rintro ⟨z, rfl⟩
        obtain ⟨g, hg⟩ := exists_smul_eq (Equiv.Perm (Fin 2)) x z
        exact ⟨g, (hsmul g x).trans (congrArg f hg)⟩
    rw [horb, Nat.card_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases a with x | x
  · exact key Sum.inl Sum.inl_injective (fun _ _ => rfl) x
  · exact key Sum.inr Sum.inr_injective (fun _ _ => rfl) x

/-- Non-vacuity of `exists_derangement_of_two_orbits`, prime-power branch
(`p = 2`, `k = 1`, `n = 2`). -/
example : ∃ g : Equiv.Perm (Fin 2), IsDerangement (α := Fin 2 ⊕ Fin 2) g :=
  exists_derangement_of_two_orbits (p := 2) (n := 2) (by simp)
    card_orbit_perm_fin_two_sum (Or.inl ⟨1, le_rfl, rfl⟩)

/-- Non-vacuity of `exists_derangement_of_two_orbits`, `b·p` branch
(`p = 2`, `b = 1`, `n = 2`). -/
example : ∃ g : Equiv.Perm (Fin 2), IsDerangement (α := Fin 2 ⊕ Fin 2) g :=
  exists_derangement_of_two_orbits (p := 2) (n := 2) (by simp)
    card_orbit_perm_fin_two_sum (Or.inr ⟨1, le_rfl, rfl, le_rfl⟩)

/-- Non-vacuity of `exists_derangement_of_pow_dvd_card_orbit` (`p = 2`,
`e = 1`). -/
example : ∃ g : Equiv.Perm (Fin 2), IsDerangement (α := Fin 2 ⊕ Fin 2) g :=
  exists_derangement_of_pow_dvd_card_orbit (p := 2) (e := 1) le_rfl
    (fun a => by rw [card_orbit_perm_fin_two_sum, pow_one]) (by simp)

/-- Non-vacuity of Jordan's theorem: `Equiv.Perm (Fin 2)` on `Fin 2`. -/
example : ∃ g : Equiv.Perm (Fin 2), IsDerangement (α := Fin 2) g :=
  exists_derangement_of_isPretransitive (by simp)

/-- The conclusion is not trivially witnessed by `1`: the identity is not a
derangement of the nonempty model set. -/
example : ¬ IsDerangement (α := Fin 2 ⊕ Fin 2) (1 : Equiv.Perm (Fin 2)) :=
  fun h => h (Sum.inl 0) (one_smul _ _)

end EllisHarperDerangements
