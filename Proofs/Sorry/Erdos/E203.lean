/-
  Erdős Problem #203 — Sierpiński numbers coprime to 6 (two-dimensional
  Sierpiński problem).
  Status: open.  Tier UB archive target.

  Verbatim statement (`goof erdos fetch 203`, pulled 2026-08-05):

    "Is there an integer $m\geq 1$ with $(m,6)=1$ such that none of
    $2^k3^\ell m+1$ are prime, for any $k,\ell\geq 0$?"

  DB remarks: with only powers of 2 these are Sierpiński numbers (see
  #1113).  Erdős–Graham also ask about p₁^{k₁}⋯p_r^{k_r}m + 1 and about
  q₁⋯q_r m + 1 with q_i ≡ 1 (mod 4) (the latter trivially m = 1,
  noted by Dogmachine — a condition like m even is presumably meant).
  Comments: emil467q (post 1912) reports a shallow search from 10¹⁰
  to 10¹¹, not a certified exclusion; Dogmachine (post 3775) explicitly
  describes the 10¹⁰ discussion as heuristic. No rigorous exclusion
  bound is certified by these comments;
  AnimishSharma (Jun 2026, comment-sourced): |⟨2,3⟩ ≤ (ℤ/p)^×| =
  lcm(ord_p 2, ord_p 3) and the covering-density necessary condition
  ∑_{p∈P} 1/|H_p| ≥ 1 for any finite covering set; small-lcm coverings
  ruled out computationally.

  Audit verdict (candidates doc): archive only — the 2-generator
  subgroup structure is genuinely different from the repo's 1D covering
  lane; no decidable fragment in reach.  Worth stating as the exact 2D
  generalization of `Proofs/Erdos/Covering/Sierpinski.lean`.

  Mathlib inventory: `Nat.Coprime`, `Nat.Prime`; repo:
  `Erdos.Covering.IsSierpinskiNumber` for the 1D link.
-/
import Mathlib
import Erdos.Covering.Sierpinski

set_option autoImplicit false

namespace ErdosCandidates.E203

/-- `IsTwoDimSierpinski m`: `m ≥ 1`, coprime to 6, and `2^k·3^ℓ·m + 1`
    is never prime. -/
def IsTwoDimSierpinski (m : ℕ) : Prop :=
  1 ≤ m ∧ Nat.Coprime m 6 ∧
    ∀ k ℓ : ℕ, ¬ (2 ^ k * 3 ^ ℓ * m + 1).Prime

/-- **Erdős #203 (OPEN)**: does a 2-dimensional Sierpiński number
    coprime to 6 exist?

    Source text: "Is there an integer $m\geq 1$ with $(m,6)=1$ such
    that none of $2^k3^\ell m+1$ are prime, for any $k,\ell\geq 0$?"
    emil467q reports a shallow search from 10¹⁰ to 10¹¹ (post 1912);
    Dogmachine explicitly describes the 10¹⁰ discussion as heuristic
    (post 3775). These comments certify no rigorous exclusion bound.
    Heuristics suggest any example is enormous (double-digit digit-count
    beyond the classical 78557). -/
theorem erdos_203 : ∃ m : ℕ, IsTwoDimSierpinski m := by
  sorry

/-- The 1D link — sanity for the definition shape: a 2D Sierpiński
    number is in particular a classical Sierpiński number (take
    `ℓ = 0`), in the repo's `IsSierpinskiNumber` sense.
    Oddness follows from coprimality with 6; `1 ≤ m` supplies the
    strict lower bound in `Composite`. The hypothesis's satisfiability
    remains the open existence question #203. -/
theorem twoDim_is_sierpinski (m : ℕ) (h : IsTwoDimSierpinski m) :
    Erdos.Covering.IsSierpinskiNumber m := by
  have hc2 : Nat.Coprime m 2 := h.2.1.of_dvd_right (by decide)
  refine ⟨Nat.prime_two.coprime_iff_not_dvd.mp hc2.symm, ?_⟩
  intro n
  have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hprod : 1 ≤ m * 2 ^ n := Nat.mul_le_mul h.1 hp
  refine ⟨by omega, ?_⟩
  simpa only [pow_zero, mul_one, Nat.mul_comm] using h.2.2 n 0

/-- Non-degeneracy of the coprimality guard: `m = 78557` (the
    classical Sierpiński number, odd but ≡ 2 mod 3 — coprime to 6!)
    FAILS the 2D property: `2·3²·78557 + 1 = 1414027` is prime
    (AnimishSharma's comment; verify independently).  So the 2D
    problem is strictly harder than 1D and the classical witness does
    not transfer. Primality and coprimality are kernel-checked by
    `norm_num`. -/
theorem coprime_78557_prime_witness :
    Nat.Coprime 78557 6 ∧ (2 ^ 1 * 3 ^ 2 * 78557 + 1).Prime := by
  norm_num

/-- The classical witness `78557` is not a two-dimensional Sierpiński
    number: the exponents `(1, 2)` give a prime. -/
theorem not_twoDim_78557 : ¬ IsTwoDimSierpinski 78557 := by
  intro h
  exact h.2.2 1 2 coprime_78557_prime_witness.2

/-- If `u ^ L = 1` then `u ^ (n % L) = u ^ n`. -/
private lemma pow_mod_of_pow_eq_one {G : Type*} [Monoid G] {u : G} {L : ℕ} (hu : u ^ L = 1)
    (n : ℕ) : u ^ (n % L) = u ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n L, pow_add, pow_mul, hu, one_pow, mul_one]

/-- The homomorphism `(k, ℓ) ↦ u ^ k * v ^ ℓ` on `ℤ/L × ℤ/L`. -/
private def twoGenHom {G : Type*} [CommGroup G] (L : ℕ) [NeZero L] (u v : G)
    (hu : u ^ L = 1) (hv : v ^ L = 1) : Multiplicative (ZMod L × ZMod L) →* G :=
  MonoidHom.mk' (fun x => u ^ (Multiplicative.toAdd x).1.val * v ^ (Multiplicative.toAdd x).2.val)
    (by
      intro a b
      simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add,
        pow_mod_of_pow_eq_one hu, pow_mod_of_pow_eq_one hv, pow_add]
      exact mul_mul_mul_comm _ _ _ _)

/-- Evaluation formula for `twoGenHom`. -/
private lemma twoGenHom_apply {G : Type*} [CommGroup G] (L : ℕ) [NeZero L] (u v : G)
    (hu : u ^ L = 1) (hv : v ^ L = 1) (x : ZMod L × ZMod L) :
    twoGenHom L u v hu hv (Multiplicative.ofAdd x) = u ^ x.1.val * v ^ x.2.val := rfl


/-- For a prime `p ∤ 6` and `L` a common multiple of `ord_p 2`, `ord_p 3`, the number of
`(k, ℓ) ∈ (ℤ/L)²` with `p ∣ 2^k 3^ℓ m + 1` times `lcm(ord_p 2, ord_p 3)` is at most `L²`. -/
private lemma card_filter_mul_lcm_le (p L m : ℕ) (hp : p.Prime) (hp6 : ¬ p ∣ 6) [NeZero L]
    (h2 : orderOf (2 : ZMod p) ∣ L) (h3 : orderOf (3 : ZMod p) ∣ L) :
    (Finset.univ.filter
        (fun x : ZMod L × ZMod L => p ∣ 2 ^ x.1.val * 3 ^ x.2.val * m + 1)).card *
      Nat.lcm (orderOf (2 : ZMod p)) (orderOf (3 : ZMod p)) ≤ L ^ 2 := by
  haveI := Fact.mk hp
  have hc2 : Nat.Coprime 2 p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp6 (h.trans (by norm_num))).symm
  have hc3 : Nat.Coprime 3 p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp6 (h.trans (by norm_num))).symm
  set u : (ZMod p)ˣ := ZMod.unitOfCoprime 2 hc2 with hu_def
  set v : (ZMod p)ˣ := ZMod.unitOfCoprime 3 hc3 with hv_def
  have hu_coe : ((u : (ZMod p)ˣ) : ZMod p) = 2 := by simp [hu_def]
  have hv_coe : ((v : (ZMod p)ˣ) : ZMod p) = 3 := by simp [hv_def]
  have hou : orderOf u = orderOf (2 : ZMod p) := by rw [← orderOf_units, hu_coe]
  have hov : orderOf v = orderOf (3 : ZMod p) := by rw [← orderOf_units, hv_coe]
  have huL : u ^ L = 1 := orderOf_dvd_iff_pow_eq_one.1 (hou ▸ h2)
  have hvL : v ^ L = 1 := orderOf_dvd_iff_pow_eq_one.1 (hov ▸ h3)
  set φ := twoGenHom L u v huL hvL with hφ
  set S := Finset.univ.filter
    (fun x : ZMod L × ZMod L => p ∣ 2 ^ x.1.val * 3 ^ x.2.val * m + 1) with hS
  -- the image of `φ` in `ZMod p`
  have hφ_coe : ∀ x : ZMod L × ZMod L,
      ((φ (Multiplicative.ofAdd x) : (ZMod p)ˣ) : ZMod p) = 2 ^ x.1.val * 3 ^ x.2.val := by
    intro x
    rw [hφ, twoGenHom_apply, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      hu_coe, hv_coe]
  -- step 1: `|S| ≤ |ker φ|`
  have hkey : ∀ x ∈ S, ∀ y ∈ S, φ (Multiplicative.ofAdd x) = φ (Multiplicative.ofAdd y) := by
    have hcast : ∀ x ∈ S, (2 : ZMod p) ^ x.1.val * 3 ^ x.2.val * (m : ZMod p) = -1 := by
      intro x hx
      have hdvd : p ∣ 2 ^ x.1.val * 3 ^ x.2.val * m + 1 := (Finset.mem_filter.1 hx).2
      have h0 : ((2 ^ x.1.val * 3 ^ x.2.val * m + 1 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    intro x hx y hy
    have hm0 : (m : ZMod p) ≠ 0 := by
      intro hm
      have h := hcast x hx
      rw [hm, mul_zero] at h
      exact zero_ne_one (neg_eq_zero.1 h.symm).symm
    apply Units.ext
    rw [hφ_coe, hφ_coe]
    exact mul_right_cancel₀ hm0 ((hcast x hx).trans (hcast y hy).symm)
  have hS_le : S.card ≤ Nat.card φ.ker := by
    rcases S.eq_empty_or_nonempty with hSe | ⟨x0, hx0⟩
    · simp [hSe]
    have hinj : S.card ≤ (Finset.univ.filter
        (fun g : Multiplicative (ZMod L × ZMod L) => φ g = φ (Multiplicative.ofAdd x0))).card :=
      Finset.card_le_card_of_injOn Multiplicative.ofAdd
        (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hkey x hx x0 hx0⟩)
        (fun x _ y _ hxy => Multiplicative.ofAdd.injective hxy)
    have hfib : (Finset.univ.filter
        (fun g : Multiplicative (ZMod L × ZMod L) => φ g = φ (Multiplicative.ofAdd x0))).card =
        (Finset.univ.filter (fun g : Multiplicative (ZMod L × ZMod L) => φ g = 1)).card :=
      MonoidHom.card_fiber_eq_of_mem_range φ ⟨_, rfl⟩ ⟨1, map_one φ⟩
    have hker : Nat.card φ.ker =
        (Finset.univ.filter (fun g : Multiplicative (ZMod L × ZMod L) => φ g = 1)).card := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => MonoidHom.mem_ker (f := φ) (x := x)),
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hker, ← hfib]
    exact hinj
  -- step 2: `|ker φ| * |range φ| = L ^ 2`
  have hker_range : Nat.card φ.ker * Nat.card φ.range = L ^ 2 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
    simp [Fintype.card_multiplicative, Fintype.card_prod, ZMod.card, sq]
  -- step 3: `lcm ∣ |range φ|`
  have hφu : φ (Multiplicative.ofAdd ((1, 0) : ZMod L × ZMod L)) = u := by
    rw [hφ, twoGenHom_apply, ZMod.val_one_eq_one_mod, pow_mod_of_pow_eq_one huL, ZMod.val_zero,
      pow_one, pow_zero, mul_one]
  have hφv : φ (Multiplicative.ofAdd ((0, 1) : ZMod L × ZMod L)) = v := by
    rw [hφ, twoGenHom_apply, ZMod.val_one_eq_one_mod, pow_mod_of_pow_eq_one hvL, ZMod.val_zero,
      pow_one, pow_zero, one_mul]
  have hlcm : Nat.lcm (orderOf (2 : ZMod p)) (orderOf (3 : ZMod p)) ∣ Nat.card φ.range := by
    apply Nat.lcm_dvd
    · calc orderOf (2 : ZMod p) = orderOf (⟨u, ⟨_, hφu⟩⟩ : φ.range) := by
            rw [← hou]; exact (Subgroup.orderOf_mk (H := φ.range) u ⟨_, hφu⟩).symm
        _ ∣ Nat.card φ.range := orderOf_dvd_natCard _
    · calc orderOf (3 : ZMod p) = orderOf (⟨v, ⟨_, hφv⟩⟩ : φ.range) := by
            rw [← hov]; exact (Subgroup.orderOf_mk (H := φ.range) v ⟨_, hφv⟩).symm
        _ ∣ Nat.card φ.range := orderOf_dvd_natCard _
  have hrange_pos : 0 < Nat.card φ.range := Nat.card_pos
  calc S.card * Nat.lcm (orderOf (2 : ZMod p)) (orderOf (3 : ZMod p))
      ≤ Nat.card φ.ker * Nat.card φ.range :=
        Nat.mul_le_mul hS_le (Nat.le_of_dvd hrange_pos hlcm)
    _ = L ^ 2 := hker_range


/-- For a prime `p` not dividing `a`, the multiplicative order of `a` mod `p` divides `p - 1`. -/
private lemma orderOf_natCast_dvd_sub_one (p a : ℕ) (hp : p.Prime) (ha : ¬ p ∣ a) :
    orderOf (a : ZMod p) ∣ p - 1 := by
  haveI := Fact.mk hp
  exact ZMod.orderOf_dvd_card_sub_one fun h => ha ((ZMod.natCast_eq_zero_iff a p).1 h)

/-- **Covering-density necessary condition** (comment-sourced,
    AnimishSharma Jun 2026; elementary and re-derivable): if a finite
    set `P` of primes (none dividing 6) covers the problem for `m` —
    every `2^k 3^ℓ m + 1` is divisible by some `p ∈ P` — then
    `∑_{p ∈ P} 1/|H_p| ≥ 1`, where `H_p = ⟨2, 3⟩ ≤ (ℤ/p)^×` and
    `|H_p| = lcm(ord_p 2, ord_p 3)`.  Stated with `orderOf` in
    `(ZMod p)ˣ`; the multiplicative-order machinery is in Mathlib
    (`ZMod.orderOf_units`, `orderOf`). -/
theorem covering_density_condition (m : ℕ) (hm : IsTwoDimSierpinski m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ 6)
    (hcov : ∀ k ℓ : ℕ, ∃ p ∈ P, (p : ℕ) ∣ 2 ^ k * 3 ^ ℓ * m + 1) :
    1 ≤ ∑ p ∈ P.attach,
      (1 : ℚ) / Nat.lcm (orderOf (2 : ZMod p.1)) (orderOf (3 : ZMod p.1)) := by
  set L : ℕ := ∏ p ∈ P, (p - 1) with hL_def
  have hL : L ≠ 0 := by
    rw [hL_def, Finset.prod_ne_zero_iff]
    intro p hp
    have := (hP p hp).1.two_le
    omega
  haveI : NeZero L := ⟨hL⟩
  -- the orders of 2 and 3 modulo each `p ∈ P` divide `L`
  have hord : ∀ p ∈ P, ∀ a : ℕ, a ∣ 6 → orderOf (a : ZMod p) ∣ L := by
    intro p hp a ha
    have hpa : ¬ p ∣ a := fun h => (hP p hp).2 (h.trans ha)
    exact (orderOf_natCast_dvd_sub_one p a (hP p hp).1 hpa).trans
      (Finset.dvd_prod_of_mem _ hp)
  set ℓcm : P → ℕ := fun p => Nat.lcm (orderOf (2 : ZMod p.1)) (orderOf (3 : ZMod p.1))
    with hℓcm
  set F : P → Finset (ZMod L × ZMod L) := fun p => Finset.univ.filter
    (fun x : ZMod L × ZMod L => p.1 ∣ 2 ^ x.1.val * 3 ^ x.2.val * m + 1) with hF
  -- per-prime bound
  have hFp : ∀ p : P, (F p).card * ℓcm p ≤ L ^ 2 := by
    intro p
    have h2 := hord p.1 p.2 2 (by norm_num)
    have h3 := hord p.1 p.2 3 (by norm_num)
    rw [Nat.cast_ofNat] at h2 h3
    exact card_filter_mul_lcm_le p.1 L m (hP p.1 p.2).1 (hP p.1 p.2).2 h2 h3
  have hℓcm_pos : ∀ p : P, 0 < ℓcm p := by
    intro p
    have h2 := hord p.1 p.2 2 (by norm_num)
    have h3 := hord p.1 p.2 3 (by norm_num)
    rw [Nat.cast_ofNat] at h2 h3
    exact Nat.lcm_pos (Nat.pos_of_dvd_of_pos h2 (Nat.pos_of_ne_zero hL))
      (Nat.pos_of_dvd_of_pos h3 (Nat.pos_of_ne_zero hL))
  -- covering: every pair is counted at least once
  have hcount : L ^ 2 ≤ ∑ p ∈ P.attach, (F p).card := by
    have hsub : (Finset.univ : Finset (ZMod L × ZMod L)) ⊆ P.attach.biUnion F := by
      intro x _
      obtain ⟨p, hp, hdvd⟩ := hcov x.1.val x.2.val
      exact Finset.mem_biUnion.2 ⟨⟨p, hp⟩, Finset.mem_attach _ _,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hdvd⟩⟩
    calc L ^ 2 = (Finset.univ : Finset (ZMod L × ZMod L)).card := by
          simp [Finset.card_univ, Fintype.card_prod, ZMod.card, sq]
      _ ≤ (P.attach.biUnion F).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
  have hLq : (0 : ℚ) < (L : ℚ) ^ 2 := by positivity
  have hle : ∀ p ∈ P.attach, ((F p).card : ℚ) ≤ (L : ℚ) ^ 2 * (1 / ℓcm p) := by
    intro p _
    have hpos : (0 : ℚ) < ℓcm p := by exact_mod_cast hℓcm_pos p
    rw [mul_one_div, le_div_iff₀ hpos]
    exact_mod_cast hFp p
  have hsum : (L : ℚ) ^ 2 ≤ (L : ℚ) ^ 2 * ∑ p ∈ P.attach, (1 : ℚ) / ℓcm p := by
    rw [Finset.mul_sum]
    calc (L : ℚ) ^ 2 ≤ ∑ p ∈ P.attach, ((F p).card : ℚ) := by exact_mod_cast hcount
      _ ≤ _ := Finset.sum_le_sum hle
  have hsum' : (L : ℚ) ^ 2 * 1 ≤ (L : ℚ) ^ 2 * ∑ p ∈ P.attach, (1 : ℚ) / ℓcm p := by
    rw [mul_one]
    exact hsum
  exact le_of_mul_le_mul_left hsum' hLq

end ErdosCandidates.E203

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch.
   - IsTwoDimSierpinski faithfully encodes m >= 1, (m,6)=1, and universally
     composite 2^k * 3^l * m + 1.
   - twoDim_is_sierpinski: IsSierpinskiNumber (Sierpinski.lean line 94) requires
     odd k and forall n, Composite(k*2^n+1). Setting l=0 in the 2D property gives
     the 1D statement; Nat.Coprime m 6 implies oddness; the Composite 1< guard
     holds because IsTwoDimSierpinski is vacuously false for m=1 (2 is prime),
     forcing m >= 5. Quantifier structure matches.
   - Arithmetic verified: 2*9*78557+1 = 1414027 is prime (sympy confirmed);
     gcd(78557,6) = 1.
   - covering_density_condition uses orderOf(2 : ZMod p.1) and orderOf(3 : ZMod p.1)
     which give multiplicative orders since p is prime and p does not divide 6;
     Nat.lcm of these matches AnimishSharma's |H_p| = lcm(ord_p 2, ord_p 3).
   - Dogmachine's heuristic 10^10 discussion (post 3775) and emil467q's
     shallow search from 10^10 to 10^11 (post 1912) certify no rigorous
     exclusion bound. The earlier endorsement of an unqualified bound was
     overstated; the commentary above now records the search's limitations.
     AnimishSharma's density obstruction remains comment-sourced.
-/
