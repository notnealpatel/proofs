/-
# Szele's theorem: every group of order `n` is cyclic iff `gcd(n, φ(n)) = 1`

## Classical source (recorded 2026-10-21)

* T. Szele, *Über die endlichen Ordnungszahlen, zu denen nur eine Gruppe gehört*,
  Comment. Math. Helv. 20 (1947) 265–267 — the criterion is the main theorem.
* Earlier implicit in L. E. Dickson (1905); restated in J. Pakianathan and K. Shankar,
  *Nilpotent numbers*, Amer. Math. Monthly 107 (2000).  The numbers in question are the
  *cyclic numbers*, OEIS A003277.

## Informal statement (verbatim from the target spec)

```
For n >= 1, gnu n = 1 (every group of order n is cyclic) if and only if
Nat.Coprime n (Nat.totient n). (Cyclic numbers, OEIS A003277.)
```

## Mathlib absence check

`leandoc` (phrasings "cyclic totient coprime", "every group of order n is cyclic",
"IsCyclic coprime card totient") and a grep for `totient` under
`Mathlib/GroupTheory/` find only `IsCyclic.card_mulAut`, `IsZGroup.of_squarefree`,
`isZGroup_iff_exists_mulEquiv` and `Nat.totient_coprime_totient_iff`; none states the
criterion.

## Proof outline

* (`⇐`) `gcd(n, φ n) = 1` forces `n` squarefree, so every group of order `n` is a
  Z-group (`IsZGroup.of_squarefree`), hence `G ≃* N ⋊[φ] H` with `N`, `H` cyclic of
  coprime orders.  The image of `φ : H →* MulAut N` has exponent dividing both `|H| ∣ n`
  and `|MulAut N| = φ |N| ∣ φ n`, so `φ = 1`, `G ≃* N × H`, and `N × H` is cyclic.
* (`⇒`) a prime `p ∣ gcd(n, φ n)` gives `p² ∣ n` or a prime `q ∣ n` with `p ∣ q - 1`.
  In the first case `C_p × C_{n/p}` is not cyclic; in the second the repo's nonabelian
  `C_q ⋊ C_p` (`GroupCount.exists_semidirectProduct_card_mul_primes_noncommutative`)
  times `C_{n/(pq)}` is not cyclic.

## Main results

* `GroupCount.isCyclic_of_coprime_card_totient` — group-level `⇐`.
* `GroupCount.exists_not_isCyclic_of_not_coprime_totient` — group-level `⇒`.
* `GroupCount.forall_isCyclic_iff_coprime_totient` — Szele's criterion, group form.
* `GroupCount.gnu_eq_one_iff_coprime_totient` — Szele's criterion, `gnu` form.  The
  spec's guard `1 ≤ n` is not needed: at `n = 0` both sides are false
  (`gnu 0 = 0`, and `gcd(0, φ 0) = gcd(0, 0) = 0`), so the statement is proved for all `n`.
-/
import Mathlib
import Sorry.GroupCount.Gnu
import Sorry.GroupCount.HolderPQ

set_option autoImplicit false

namespace GroupCount

/-! ## Arithmetic of `gcd(n, φ n) = 1` -/

/-- If `n` is coprime to `φ n` then `n` is squarefree: `p² ∣ n` would give
`p ∣ p (p - 1) = φ (p²) ∣ φ n`. -/
theorem squarefree_of_coprime_totient {n : ℕ} (h : n.Coprime n.totient) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hdvd : (p ^ 2).totient ∣ n.totient := Nat.totient_dvd_of_dvd (by rwa [sq])
  rw [Nat.totient_prime_pow hp (by norm_num)] at hdvd
  have hpn : p ∣ n := (Dvd.intro p rfl).trans hpp
  have hpt : p ∣ n.totient := (Dvd.intro (p - 1) (by simp)).trans hdvd
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes h hpn hpt)

/-- `n` coprime to `φ n` forces `n ≠ 0` (`gcd(0, φ 0) = gcd(0, 0) = 0`). -/
theorem ne_zero_of_coprime_totient {n : ℕ} (h : n.Coprime n.totient) : n ≠ 0 := by
  rintro rfl
  simp at h

/-- A prime `p` dividing both `n ≠ 0` and `φ n` either has `p * p ∣ n`, or divides
`q - 1` for some prime `q ∣ n` (read off from `φ n = ∏ q ^ (k - 1) * (q - 1)`). -/
theorem exists_prime_of_not_coprime_totient {n : ℕ} (hn : n ≠ 0)
    (h : ¬ n.Coprime n.totient) :
    ∃ p, p.Prime ∧ (p * p ∣ n ∨ ∃ q, q.Prime ∧ p ∣ n ∧ q ∣ n ∧ p ∣ q - 1) := by
  obtain ⟨p, hp, hpn, hpt⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  rw [Nat.totient_eq_prod_factorization hn] at hpt
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsuppProd_iff.mp hpt
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq
  refine ⟨p, hp, ?_⟩
  rcases (Nat.Prime.prime hp).dvd_or_dvd hpq with hpow | hsub
  · left
    have hk : n.factorization q - 1 ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hpow
      exact hp.ne_one (Nat.dvd_one.mp hpow)
    have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (hp.dvd_of_dvd_pow hpow)
    subst hpeq
    have h2 : 2 ≤ n.factorization p := by omega
    have hpp : p ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr h2
    simpa [sq] using hpp
  · right
    exact ⟨q, hqp, hpn, hqn, hsub⟩

/-! ## `⇐`: coprime orders give cyclic groups -/

/-- **Szele, `⇐`.**  A finite group `G` whose order `n` is coprime to `φ n` is cyclic. -/
theorem isCyclic_of_coprime_card_totient {G : Type*} [Group G] [Finite G]
    (h : (Nat.card G).Coprime (Nat.card G).totient) : IsCyclic G := by
  have hZ : IsZGroup G := IsZGroup.of_squarefree (squarefree_of_coprime_totient h)
  obtain ⟨N, H, φ, e, hH, hN, hNH⟩ := isZGroup_iff_exists_mulEquiv.mp hZ
  have hφ : φ = 1 := by
    ext1 x
    have h1 : orderOf (φ x) ∣ (Nat.card G).totient := by
      refine (orderOf_dvd_natCard (φ x)).trans ?_
      rw [IsCyclic.card_mulAut]
      exact Nat.totient_dvd_of_dvd (Subgroup.card_subgroup_dvd_card N)
    have h2 : orderOf (φ x) ∣ Nat.card G :=
      (orderOf_map_dvd φ x).trans ((orderOf_dvd_natCard x).trans
        (Subgroup.card_subgroup_dvd_card H))
    have h3 : orderOf (φ x) = 1 := Nat.eq_one_of_dvd_coprimes h h2 h1
    simpa using h3
  subst hφ
  have hprod : IsCyclic (N × H) := Group.isCyclic_prod_iff.mpr ⟨hN, hH, hNH⟩
  let e' : G ≃* N × H := e.trans SemidirectProduct.mulEquivProd
  exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

/-! ## `⇒`: explicit noncyclic groups -/

/-- If `p * p ∣ n ≠ 0` for a prime `p`, then `C_p × C_{n/p}` is a noncyclic group of
order `n`. -/
theorem exists_not_isCyclic_of_mul_self_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hpp : p * p ∣ n) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Nat.card G = n ∧ ¬ IsCyclic G := by
  obtain ⟨m, rfl⟩ := hpp
  have hm : m ≠ 0 := by rintro rfl; simp at hn
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p * m) := ⟨Nat.mul_ne_zero hp.ne_zero hm⟩
  refine ⟨Multiplicative (ZMod p) × Multiplicative (ZMod (p * m)), inferInstance,
    inferInstance, ?_, ?_⟩
  · simp [mul_assoc]
  · intro hcyc
    have hcop := (Group.isCyclic_prod_iff.mp hcyc).2.2
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hcop
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (Dvd.intro m rfl))

/-- If primes `p, q` divide `n ≠ 0` and `p ∣ q - 1`, then the nonabelian `C_q ⋊ C_p`
times `C_{n/(pq)}` is a noncyclic group of order `n`. -/
theorem exists_not_isCyclic_of_dvd_sub_one {n p q : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n) (hpq : p ∣ q - 1) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Nat.card G = n ∧ ¬ IsCyclic G := by
  have hlt : p < q := by
    have hq2 := hq.two_le
    have hle := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨σ, -, -, hcard, x, y, hxy⟩ :=
    exists_semidirectProduct_card_mul_primes_noncommutative hp hq hlt hpq
  let K := Multiplicative (ZMod q) ⋊[(Subgroup.zpowers σ).subtype] (Subgroup.zpowers σ)
  have hpqn : p * q ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr hlt.ne) hpn hqn
  obtain ⟨m, hm⟩ := hpqn
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hm)
  haveI : NeZero m := ⟨hm0⟩
  haveI : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.mul_ne_zero hp.ne_zero hq.ne_zero)
  refine ⟨K × Multiplicative (ZMod m), inferInstance, inferInstance, ?_, ?_⟩
  · rw [Nat.card_prod, hcard, hm]
    simp
  · intro hcyc
    haveI : IsCyclic K := isCyclic_left_of_prod K (Multiplicative (ZMod m))
    exact hxy ((IsCyclic.isMulCommutative (α := K)).is_comm.comm _ _)

/-- **Szele, `⇒`.**  If `n ≠ 0` is not coprime to `φ n`, some group of order `n` is not
cyclic. -/
theorem exists_not_isCyclic_of_not_coprime_totient {n : ℕ} (hn : n ≠ 0)
    (h : ¬ n.Coprime n.totient) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Nat.card G = n ∧ ¬ IsCyclic G := by
  obtain ⟨p, hp, hpp | ⟨q, hq, hpn, hqn, hpq⟩⟩ := exists_prime_of_not_coprime_totient hn h
  · exact exists_not_isCyclic_of_mul_self_dvd hn hp hpp
  · exact exists_not_isCyclic_of_dvd_sub_one hn hp hq hpn hqn hpq

/-! ## Szele's theorem -/

/-- **Szele's theorem (1947), group form.**  For `n ≠ 0`, every finite group of order `n`
is cyclic if and only if `gcd(n, φ(n)) = 1`. -/
theorem forall_isCyclic_iff_coprime_totient {n : ℕ} (hn : n ≠ 0) :
    (∀ (G : Type) [Group G] [Finite G], Nat.card G = n → IsCyclic G) ↔
      n.Coprime n.totient := by
  constructor
  · intro hall
    by_contra hcop
    obtain ⟨G, _, _, hG, hncyc⟩ := exists_not_isCyclic_of_not_coprime_totient hn hcop
    exact hncyc (hall G hG)
  · intro hcop G _ _ hG
    exact isCyclic_of_coprime_card_totient (hG ▸ hcop)

/-- A noncyclic finite group of order `n` gives `2 ≤ gnu n` (compare it with the cyclic
group `C_n`). -/
theorem two_le_gnu_of_not_isCyclic {n : ℕ} {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = n) (h : ¬ IsCyclic G) : 2 ≤ gnu n := by
  have hn : n ≠ 0 := hG ▸ Nat.card_pos.ne'
  haveI : NeZero n := ⟨hn⟩
  letI : Fintype G := Fintype.ofFinite G
  have hG' : Fintype.card G = n := by rw [← Nat.card_eq_fintype_card, hG]
  have hC : Fintype.card (Multiplicative (ZMod n)) = n := by simp
  refine two_le_gnu_of_isEmpty_mulEquiv hG' hC ⟨fun e => h ?_⟩
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- **Szele's theorem (1947), `gnu` form.**  There is exactly one group of order `n` up
to isomorphism (`gnu n = 1`, OEIS A000001) if and only if `gcd(n, φ(n)) = 1` (the cyclic
numbers, OEIS A003277).  No guard on `n` is needed: at `n = 0` both sides are false. -/
theorem gnu_eq_one_iff_coprime_totient (n : ℕ) : gnu n = 1 ↔ n.Coprime n.totient := by
  constructor
  · intro hgnu
    have hn : n ≠ 0 := by
      rintro rfl
      rw [gnu_zero] at hgnu
      exact zero_ne_one hgnu
    by_contra hcop
    obtain ⟨G, _, _, hG, hncyc⟩ := exists_not_isCyclic_of_not_coprime_totient hn hcop
    have h2 := two_le_gnu_of_not_isCyclic hG hncyc
    omega
  · intro hcop
    have hn : n ≠ 0 := ne_zero_of_coprime_totient hcop
    refine gnu_eq_one_of_forall_mulEquiv (Nat.one_le_iff_ne_zero.mpr hn) ?_
    intro G H _ _ _ _ hG hH
    have hG' : Nat.card G = n := by rw [Nat.card_eq_fintype_card, hG]
    have hH' : Nat.card H = n := by rw [Nat.card_eq_fintype_card, hH]
    haveI : IsCyclic G := isCyclic_of_coprime_card_totient (hG' ▸ hcop)
    haveI : IsCyclic H := isCyclic_of_coprime_card_totient (hH' ▸ hcop)
    exact ⟨mulEquivOfCyclicCardEq (hG'.trans hH'.symm)⟩

section GroundTruth

/-- Ground truth: `15` is a cyclic number (`gcd(15, φ 15) = gcd(15, 8) = 1`), so the
hypothesis side of `⇐` is satisfiable at a composite order. -/
example : (15 : ℕ).Coprime (Nat.totient 15) := by decide

/-- Ground truth: `6` is not a cyclic number (`gcd(6, φ 6) = gcd(6, 2) = 2`). -/
example : ¬ (6 : ℕ).Coprime (Nat.totient 6) := by decide

/-- Szele at `n = 15`: there is exactly one group of order `15`. -/
example : gnu 15 = 1 := (gnu_eq_one_iff_coprime_totient 15).mpr (by decide)

/-- Szele at `n = 6`: `gnu 6 ≠ 1` (the symmetric group `S_3`). -/
example : gnu 6 ≠ 1 := fun h => by
  have := (gnu_eq_one_iff_coprime_totient 6).mp h
  revert this
  decide

/-- Szele at `n = 9 = 3 * 3`: `gnu 9 ≠ 1` (the square-divisor branch). -/
example : gnu 9 ≠ 1 := fun h => by
  have := (gnu_eq_one_iff_coprime_totient 9).mp h
  revert this
  decide

end GroundTruth

end GroupCount
