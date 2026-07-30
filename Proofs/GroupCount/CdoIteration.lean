import GroupCount.Gnu

/-!
# The Conway–Dietrich–O'Brien `gnu`-iteration conjecture (OEIS A000001)

Iterating the group-counting function `GroupCount.gnu` (number of groups of order `n`
up to isomorphism, OEIS A000001) is conjectured to reach `1` from every start `1 ≤ n`.
The A000001 comment recording it (pulled live with `oeis show A000001`, 2026-07-30):

> "It is conjectured in (J. H. Conway, Heiko Dietrich and E. A. O'Brien, 2008) that the
> sequence n -> a(n) -> a(a(n)) = a^2(n) -> a(a(a(n))) = a^3(n) -> ... -> consists
> ultimately of 1s, where a(n), denoted by gnu(n), is called the 'group number of n'."
> — recorded by _Muniru A Asiru_, Nov 19 2017.

Source: J. H. Conway, H. Dietrich, E. A. O'Brien, *Counting groups: gnus, moas and
other exotica*, Math. Intelligencer 30 (2008).  Task card:
`Formalize/A000001-cdo-iteration.md` (claim `cdo-gnu-iteration`).

## The archived conjecture — the file's single intended `sorry`

* `GroupCount.cdo_gnu_iteration` — for `1 ≤ n` there is a `k` with `gnu^[k] n = 1`.
  OPEN; see the theorem docstring for status and fidelity notes.

## Proved sanity layer (`sorry`-free)

Absorption and reformulation:

* `GroupCount.gnu_iterate_one_eq_one` — `1` is a fixed point: `gnu^[k] 1 = 1`.
* `GroupCount.gnu_iterate_zero_eq_zero` — so is the junk stratum: `gnu^[k] 0 = 0`;
  hence `GroupCount.not_exists_gnu_iterate_zero_eq_one`: the guard `1 ≤ n` in the
  conjecture is necessary, not decorative.
* `GroupCount.gnu_iterate_eq_one_of_le` — once the iteration hits `1` it stays.
* `GroupCount.exists_gnu_iterate_eq_one_iff_forall_le` — "reaches `1`" is therefore
  faithfully the entry's "consists ultimately of 1s" (all late iterates are `1`).
* `GroupCount.exists_gnu_iterate_eq_one_gnu_iff` — the conjecture at `n` and at
  `gnu n` are equivalent (the iteration may be started one step in).

The conjecture proved on the strata reachable from the certified `gnu` values:

* `GroupCount.cdo_gnu_iteration_one` (`k = 0`),
* `GroupCount.cdo_gnu_iteration_prime` — every prime, via `gnu p = 1` (`k = 1`);
  includes `n = 2, 3, 5, 7, …`,
* `GroupCount.exists_gnu_iterate_eq_one_of_gnu_eq_one` — the generic `k = 1` stratum
  (A003277, the cyclic numbers),
* `GroupCount.cdo_gnu_iteration_four` — `n = 4`, via `gnu 4 = 2`, `gnu 2 = 1`
  (`k = 2`, and `k ≤ 1` provably does not suffice: see the ground-truth section),
* `GroupCount.cdo_gnu_iteration_prime_sq` — `n = p²` for every prime `p`, via the
  stretch value `GroupCount.gnu_prime_sq : gnu (p ^ 2) = 2` proved below by
  classification (`p²`-groups are abelian, hence `C_{p²}` or `C_p × C_p`).

## `gnu (p ^ 2) = 2` (the stretch layer)

* `GroupCount.multiplicative_zmod_prod_pow_eq_one` — every element of
  `Multiplicative (ZMod n) × Multiplicative (ZMod n)` has `n`-th power `1`.
* `GroupCount.not_isCyclic_multiplicative_zmod_prod` — that group is not cyclic at
  prime `p` (order `p²` beats every element order).
* `GroupCount.nonempty_mulEquiv_multiplicative_zmod_prod` — a *non-cyclic* group of
  order `p ^ 2` is isomorphic to it (commutative by
  `IsPGroup.commGroupOfCardEqPrimeSq`, exponent `p`, hence a rank-2 `ZMod p`-vector
  space).
* `GroupCount.gnu_prime_sq` — `gnu (p ^ 2) = 2`, by
  `GroupCount.card_eq_gnu_of_classification` on the two-member family; agrees with
  A000001 at `4, 9, 25, 49` and with the Mitch Harris formula `a(p^2) = 2` in the
  entry's formula section.

## Trust policy (USER decision, binding for this file)

**Zero `native_decide` anywhere in this module.**  Kernel `decide` only where kernel
evaluation is feasible — per the measured wall in `GroupCount/Gnu.lean`, exact `gnu`
values reduce in-kernel only for `n ≤ 2`, and the `decide` ground checks below stay
inside it.  The axiom sweep at the end confirms every declaration rests on
`{propext, Classical.choice, Quot.sound}` — plus `sorryAx` on `cdo_gnu_iteration`
alone, its single intended `sorry`.
-/

set_option autoImplicit false

namespace GroupCount

/-! ## Absorption: `1` (and the junk value `0`) are fixed points -/

/-- `1` is a fixed point of the iteration: `gnu^[k] 1 = 1` for every `k`.  This is the
"stays there" half of the entry's "consists ultimately of 1s". -/
theorem gnu_iterate_one_eq_one (k : ℕ) : gnu^[k] 1 = 1 :=
  Function.iterate_fixed gnu_one k

/-- The junk stratum is also a fixed point: `gnu^[k] 0 = 0` for every `k` (there is no
group of order `0`, and `gnu 0 = 0`).  This is why the conjecture needs its `1 ≤ n`
guard: see `GroupCount.not_exists_gnu_iterate_zero_eq_one`. -/
theorem gnu_iterate_zero_eq_zero (k : ℕ) : gnu^[k] 0 = 0 :=
  Function.iterate_fixed gnu_zero k

/-- **Absorption.**  Once the iteration hits `1` it stays: if `gnu^[k] n = 1` and
`k ≤ m` then `gnu^[m] n = 1`. -/
theorem gnu_iterate_eq_one_of_le {n k m : ℕ} (hk : gnu^[k] n = 1) (hkm : k ≤ m) :
    gnu^[m] n = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [Nat.add_comm k j, Function.iterate_add_apply, hk, gnu_iterate_one_eq_one]

/-- Reaching `1` once is the same as being `1` from some point on — the faithful
rendering of the entry's "the sequence … consists ultimately of 1s". -/
theorem exists_gnu_iterate_eq_one_iff_forall_le (n : ℕ) :
    (∃ k, gnu^[k] n = 1) ↔ ∃ k, ∀ m, k ≤ m → gnu^[m] n = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, fun m hm => gnu_iterate_eq_one_of_le hk hm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk k (Nat.le_refl k)⟩

/-- The conjecture at `gnu n` and at `n` are equivalent: the iteration may be entered
one step in.  (No `1 ≤ n` guard is needed: for `n = 0` both sides are false, `gnu 0`
being `0`.) -/
theorem exists_gnu_iterate_eq_one_gnu_iff (n : ℕ) :
    (∃ k, gnu^[k] (gnu n) = 1) ↔ ∃ k, gnu^[k] n = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply]
    exact hk
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      simp only [Function.iterate_zero_apply] at hk
      subst hk
      exact ⟨0, by rw [Function.iterate_zero_apply, gnu_one]⟩
    | succ j =>
      rw [Function.iterate_succ_apply] at hk
      exact ⟨j, hk⟩

/-! ## The archived conjecture (OPEN, intended `sorry`) -/

/-- **The Conway–Dietrich–O'Brien `gnu`-iteration conjecture** (OEIS A000001 comment,
recorded by Muniru A Asiru, Nov 19 2017; conjectured in J. H. Conway, H. Dietrich,
E. A. O'Brien, *Counting groups: gnus, moas and other exotica*, 2008): from every
`1 ≤ n`, the iteration `n → gnu n → gnu (gnu n) → ⋯` eventually reaches `1`.  OPEN,
the file's single intended `sorry`.

Fidelity of the statement:

* "consists ultimately of 1s" is `∃ k, gnu^[k] n = 1` *together with* the proved
  absorption `GroupCount.gnu_iterate_eq_one_of_le`; the two phrasings are exchanged by
  `GroupCount.exists_gnu_iterate_eq_one_iff_forall_le`.
* The guard `1 ≤ n` is necessary, not decorative: `gnu 0 = 0` is a fixed point, so the
  `n = 0` instance is *false* (`GroupCount.not_exists_gnu_iterate_zero_eq_one`).
  A000001 itself starts its group-theoretic content at `n = 1`.

Status: open.  The iteration decreases dramatically in known ranges (external
evidence: it terminates for all `n` within GAP SmallGroups coverage), but a proof
would need control of `gnu` at prime powers, where the value explodes
(`gnu (p^e) ~ p^{(2/27)e³ + O(e^{8/3})}`, entry formula section) — no route is known.
Proved strata in this file: `n = 1`, every prime, `n = 4`, and every `p²`
(`GroupCount.cdo_gnu_iteration_one` / `_prime` / `_four` / `_prime_sq`). -/
theorem cdo_gnu_iteration {n : ℕ} (hn : 1 ≤ n) : ∃ k, gnu^[k] n = 1 := by
  -- intended sorry: open conjecture (card Formalize/A000001-cdo-iteration.md,
  -- claim cdo-gnu-iteration; ROUTE: none known — see the docstring).
  sorry

/-- The `1 ≤ n` guard of `GroupCount.cdo_gnu_iteration` excludes a genuine
counterexample, not a junk case we could not handle: at `n = 0` the iteration is
constantly `0` and never reaches `1`. -/
theorem not_exists_gnu_iterate_zero_eq_one : ¬ ∃ k, gnu^[k] 0 = 1 := by
  rintro ⟨k, hk⟩
  rw [gnu_iterate_zero_eq_zero] at hk
  exact Nat.zero_ne_one hk

/-! ## Proved strata of the conjecture -/

/-- The generic `k = 1` stratum: the conjecture holds at every `n` with `gnu n = 1`
(the "cyclic numbers", A003277 — in particular every prime). -/
theorem exists_gnu_iterate_eq_one_of_gnu_eq_one {n : ℕ} (h : gnu n = 1) :
    ∃ k, gnu^[k] n = 1 :=
  ⟨1, by rw [Function.iterate_one]; exact h⟩

/-- The conjecture holds at `n = 1`, with `k = 0`. -/
theorem cdo_gnu_iteration_one : ∃ k, gnu^[k] 1 = 1 :=
  ⟨0, rfl⟩

/-- The conjecture holds at every prime, with `k = 1`: `gnu p = 1`
(`GroupCount.gnu_prime`, every group of prime order is cyclic). -/
theorem cdo_gnu_iteration_prime {p : ℕ} (hp : p.Prime) : ∃ k, gnu^[k] p = 1 :=
  exists_gnu_iterate_eq_one_of_gnu_eq_one (gnu_prime hp)

/-- Unfolding the two-step iterate by rewriting.  (Unfolding it by `show`/`rfl` would
send the elaborator into the astronomically large definitional reduction of `gnu`.) -/
theorem gnu_iterate_two (n : ℕ) : gnu^[2] n = gnu (gnu n) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]

/-- The explicit two-step run at `n = 4`: `4 → gnu 4 = 2 → gnu 2 = 1`. -/
theorem gnu_iterate_two_four : gnu^[2] 4 = 1 := by
  rw [gnu_iterate_two, gnu_four, gnu_two]

/-- The conjecture holds at `n = 4`, with `k = 2` (and provably not with `k ≤ 1`;
see the ground-truth section). -/
theorem cdo_gnu_iteration_four : ∃ k, gnu^[k] 4 = 1 :=
  ⟨2, gnu_iterate_two_four⟩

/-! ## `gnu (p ^ 2) = 2`: the classification of groups of order `p²`

Groups of order `p²` are commutative (`IsPGroup.commGroupOfCardEqPrimeSq`), and a
commutative group of order `p²` is cyclic or elementary abelian of rank `2`.  The
two classes are distinguished by cyclicity, so
`GroupCount.card_eq_gnu_of_classification` counts them: `gnu (p ^ 2) = 2`. -/

/-- Every element of `Multiplicative (ZMod n) × Multiplicative (ZMod n)` has `n`-th
power `1` (componentwise, `n • a = n * a = 0` in the ring `ZMod n`). -/
theorem multiplicative_zmod_prod_pow_eq_one (n : ℕ)
    (y : Multiplicative (ZMod n) × Multiplicative (ZMod n)) : y ^ n = 1 := by
  have hcomp : ∀ x : Multiplicative (ZMod n), x ^ n = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨a, b⟩ := y
  calc (a, b) ^ n = (a ^ n, b ^ n) := rfl
    _ = ((1 : Multiplicative (ZMod n)), (1 : Multiplicative (ZMod n))) := by
        rw [hcomp a, hcomp b]
    _ = 1 := rfl

/-- `Multiplicative (ZMod p) × Multiplicative (ZMod p)` is not cyclic at a prime `p`:
its order `p * p` exceeds every element order, which divides `p`. -/
theorem not_isCyclic_multiplicative_zmod_prod {p : ℕ} (hp : p.Prime) :
    ¬ IsCyclic (Multiplicative (ZMod p) × Multiplicative (ZMod p)) := by
  intro hcyc
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcard : Nat.card (Multiplicative (ZMod p) × Multiplicative (ZMod p)) = p * p := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have horder : orderOf g = p * p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hdvd : orderOf g ∣ p :=
    orderOf_dvd_of_pow_eq_one (multiplicative_zmod_prod_pow_eq_one p g)
  rw [horder] at hdvd
  have hle : p * p ≤ p := Nat.le_of_dvd hp.pos hdvd
  have htwo : 2 * p ≤ p * p := Nat.mul_le_mul hp.two_le (Nat.le_refl p)
  have h2 : 2 ≤ p := hp.two_le
  omega

/-- **The non-cyclic half of the `p²` classification.**  A non-cyclic group of order
`p ^ 2` is elementary abelian of rank `2`: commutative by
`IsPGroup.commGroupOfCardEqPrimeSq`, of exponent `p` (an element of order `p²` would
generate), hence a `ZMod p`-vector space of dimension `2`. -/
theorem nonempty_mulEquiv_multiplicative_zmod_prod {G : Type*} [Group G] [Fintype G]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    Nonempty (G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  letI : CommGroup G := IsPGroup.commGroupOfCardEqPrimeSq
    (by rw [Nat.card_eq_fintype_card, hcard])
  -- exponent `p`: an element of order `p²` would make `G` cyclic
  have hpow : ∀ g : G, g ^ p = 1 := by
    intro g
    have hdvd : orderOf g ∣ p ^ 2 := by
      rw [← hcard]
      exact orderOf_dvd_card
    obtain ⟨m, hm2, hgm⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hmne : m ≠ 2 := by
      rintro rfl
      exact hnc (isCyclic_of_orderOf_eq_card g
        (by rw [Nat.card_eq_fintype_card, hcard]; exact hgm))
    have hdvdp : orderOf g ∣ p := by
      have hpm : p ^ m ∣ p ^ 1 := pow_dvd_pow p (by omega)
      rw [pow_one] at hpm
      rw [hgm]
      exact hpm
    exact orderOf_dvd_iff_pow_eq_one.mp hdvdp
  -- hence `Additive G` is a `ZMod p`-vector space, of dimension `2` by cardinality
  have hsmul : ∀ a : Additive G, p • a = 0 := by
    intro a
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hpow a.toMul
  letI hMod : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule hsmul
  have hfinrank : Module.finrank (ZMod p) (Additive G) = 2 := by
    have hc : Fintype.card (Additive G)
        = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (Additive G) :=
      Module.card_eq_pow_finrank
    rw [Fintype.card_additive, hcard, ZMod.card] at hc
    exact (Nat.pow_right_injective hp.two_le hc).symm
  haveI hMF : Module.Finite (ZMod p) (Additive G) := Module.Finite.of_finite
  haveI hFree : Module.Free (ZMod p) (Additive G) := by infer_instance
  haveI hSRC : StrongRankCondition (ZMod p) := by infer_instance
  -- (the instance arguments are passed explicitly: with a `letI` module structure the
  -- elaborator's instance search for them gets stuck on metavariables)
  let b : Module.Basis (Fin 2) (ZMod p) (Additive G) :=
    @Module.finBasisOfFinrankEq (ZMod p) (Additive G) _ _ hMod hFree hSRC hMF 2 hfinrank
  let e : Additive G ≃+ ZMod p × ZMod p :=
    (b.equivFun.trans (LinearEquiv.finTwoArrow (ZMod p) (ZMod p))).toAddEquiv
  exact ⟨((MulEquiv.multiplicativeAdditive G).symm.trans
    (AddEquiv.toMultiplicative e)).trans (MulEquiv.prodMultiplicative (ZMod p) (ZMod p))⟩

/-- **`gnu (p ^ 2) = 2` for every prime `p`** — A000001 at every squared prime at
once (`4, 9, 25, 49, …` all have value `2`; entry formula `a(p^2) = 2`, Mitch
Harris).  The classification: every group of order `p²` is cyclic or isomorphic to
`Multiplicative (ZMod p) × Multiplicative (ZMod p)`, and the two are non-isomorphic. -/
theorem gnu_prime_sq {p : ℕ} (hp : p.Prime) : gnu (p ^ 2) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p * p) := ⟨Nat.mul_ne_zero hp.pos.ne' hp.pos.ne'⟩
  rw [pow_two]
  -- the non-cyclic witness structure, transported onto `Fin (p * p)`
  have hcardM : Fintype.card (Multiplicative (ZMod p) × Multiplicative (ZMod p)) = p * p := by
    simp [ZMod.card]
  obtain ⟨T, ⟨g⟩⟩ := GroupStructure.exists_carrier_mulEquiv hcardM
  have hTnc : ¬ IsCyclic T.Carrier := by
    intro h
    haveI := h
    exact not_isCyclic_multiplicative_zmod_prod hp
      (isCyclic_of_surjective g.symm.toMonoidHom g.symm.surjective)
  -- irredundancy: cyclic vs non-cyclic
  have hne : ¬ (GroupStructure.cyclic (p * p)).Iso T := by
    intro hiso
    obtain ⟨f⟩ := (GroupStructure.iso_iff_nonempty_mulEquiv _ _).mp hiso
    exact hTnc (isCyclic_of_surjective f.toMonoidHom f.surjective)
  -- exhaustiveness: cyclic or (by the classification) isomorphic to `T`
  have key : Fintype.card Bool = gnu (p * p) := by
    refine card_eq_gnu_of_classification
      (fun b => cond b T (GroupStructure.cyclic (p * p))) ?_ ?_
    · intro S
      by_cases hc : IsCyclic S.Carrier
      · refine ⟨false, ?_⟩
        show (GroupStructure.cyclic (p * p)).Iso S
        haveI := hc
        exact (GroupStructure.iso_iff_nonempty_mulEquiv _ S).mpr
          ⟨mulEquivOfCyclicCardEq (by simp)⟩
      · refine ⟨true, ?_⟩
        show T.Iso S
        obtain ⟨u⟩ := nonempty_mulEquiv_multiplicative_zmod_prod hp
          (by rw [pow_two]; exact S.card_carrier) hc
        exact (GroupStructure.iso_iff_nonempty_mulEquiv T S).mpr ⟨g.symm.trans u.symm⟩
    · intro i j hij
      cases i <;> cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
  rw [← key, Fintype.card_bool]

/-- The explicit two-step run at `n = p²`: `p² → gnu (p²) = 2 → gnu 2 = 1`. -/
theorem gnu_iterate_two_prime_sq {p : ℕ} (hp : p.Prime) : gnu^[2] (p ^ 2) = 1 := by
  rw [gnu_iterate_two, gnu_prime_sq hp, gnu_two]

/-- The conjecture holds at every squared prime, with `k = 2`. -/
theorem cdo_gnu_iteration_prime_sq {p : ℕ} (hp : p.Prime) : ∃ k, gnu^[k] (p ^ 2) = 1 :=
  ⟨2, gnu_iterate_two_prime_sq hp⟩

/-! ## Ground truth and satisfiability

Cross-checked against `oeis show A000001` (pulled 2026-07-30): the terms at
`n = 0, …, 9` are `0, 1, 1, 1, 2, 1, 2, 1, 5, 2`, and `a(25) = a(49) = 2`.  Every
hypothesis-bearing proved theorem above is instantiated at a concrete model here, and
the kernel `decide` probes stay inside the measured `n ≤ 2` evaluation wall recorded
in `GroupCount/Gnu.lean`. -/

section GroundTruth

-- The archived statement is satisfiable with content: hypothesis and conclusion
-- jointly at `n = 4`, with no appeal to the intended `sorry`.
example : 1 ≤ 4 ∧ ∃ k, gnu^[k] 4 = 1 := ⟨by omega, cdo_gnu_iteration_four⟩

-- Kernel ground check of the iteration machinery itself, inside the `n ≤ 2` wall:
-- the two-step orbit of `2` reaches `1` *in the kernel* …
example : gnu^[2] 2 = 1 := by decide

-- … while `k = 0` genuinely fails there: the `∃ k` is never degenerately witnessed.
example : ¬ gnu^[0] 2 = 1 := by decide

-- The witness `k = 2` at `n = 4` is sharp: `k = 0` and `k = 1` provably fail.
example : gnu^[0] 4 ≠ 1 := by rw [Function.iterate_zero_apply]; omega

example : gnu^[1] 4 ≠ 1 := by rw [Function.iterate_one, gnu_four]; omega

-- Absorption instantiated strictly beyond the entry point `k = 2`.
example : gnu^[37] 4 = 1 := gnu_iterate_eq_one_of_le gnu_iterate_two_four (by omega)

-- The junk stratum really is stuck at `0` (the guard of the conjecture is
-- load-bearing; see also `not_exists_gnu_iterate_zero_eq_one`).
example : gnu^[5] 0 = 0 := gnu_iterate_zero_eq_zero 5

-- The prime stratum at the concrete certified primes.
example : ∃ k, gnu^[k] 2 = 1 := cdo_gnu_iteration_prime Nat.prime_two

example : ∃ k, gnu^[k] 3 = 1 := cdo_gnu_iteration_prime Nat.prime_three

example : ∃ k, gnu^[k] 5 = 1 := exists_gnu_iterate_eq_one_of_gnu_eq_one gnu_five

example : ∃ k, gnu^[k] 7 = 1 := exists_gnu_iterate_eq_one_of_gnu_eq_one gnu_seven

-- The step-equivalence instantiated in both directions at `n = 4`.
example : ∃ k, gnu^[k] (gnu 4) = 1 :=
  (exists_gnu_iterate_eq_one_gnu_iff 4).mpr cdo_gnu_iteration_four

example : ∃ k, gnu^[k] 4 = 1 :=
  (exists_gnu_iterate_eq_one_gnu_iff 4).mp
    (by rw [gnu_four]; exact exists_gnu_iterate_eq_one_of_gnu_eq_one gnu_two)

-- The "consists ultimately of 1s" reformulation instantiated at `n = 4`.
example : ∃ k, ∀ m, k ≤ m → gnu^[m] 4 = 1 :=
  (exists_gnu_iterate_eq_one_iff_forall_le 4).mp cdo_gnu_iteration_four

-- `gnu_prime_sq` at numeric squares: agrees with A000001's `a(4) = a(9) = a(25) = 2`
-- — and at `p = 2` it independently *reproves* `gnu_four` by the vector-space
-- classification route, cross-checking the `isCyclic_or_isKleinFour` route of
-- `Gnu.lean`.
example : gnu 4 = 2 := by
  have h := gnu_prime_sq Nat.prime_two
  norm_num at h
  exact h

example : gnu 9 = 2 := by
  have h := gnu_prime_sq Nat.prime_three
  norm_num at h
  exact h

example : gnu 25 = 2 := by
  have h := gnu_prime_sq (p := 5) (by norm_num)
  norm_num at h
  exact h

-- …and the conjecture's `p²` stratum at the numerals `9` and `49`.
example : ∃ k, gnu^[k] 9 = 1 := by
  have h := cdo_gnu_iteration_prime_sq Nat.prime_three
  norm_num at h
  exact h

example : ∃ k, gnu^[k] 49 = 1 := by
  have h := cdo_gnu_iteration_prime_sq (p := 7) (by norm_num)
  norm_num at h
  exact h

-- The classification lemma's hypotheses are jointly satisfiable at a concrete
-- non-cyclic model: the Klein structure of `Gnu.lean`, at `p = 2`.
example : Nonempty (GroupStructure.klein.Carrier
    ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  nonempty_mulEquiv_multiplicative_zmod_prod Nat.prime_two
    (by norm_num [GroupStructure.card_carrier]) IsKleinFour.not_isCyclic

-- The primality hypothesis of `not_isCyclic_multiplicative_zmod_prod` instantiated
-- at a concrete prime.
example : ¬ IsCyclic (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  not_isCyclic_multiplicative_zmod_prod Nat.prime_two

-- Primality is load-bearing in `gnu_prime_sq`: at the non-prime `p = 1` the value
-- is `1`, not `2`.
example : gnu (1 ^ 2) = 1 := by rw [one_pow]; exact gnu_one

-- The exponent in `multiplicative_zmod_prod_pow_eq_one` matters: the group is not
-- trivial, and the first power of a non-identity element is not `1`.
example : ((Multiplicative.ofAdd (1 : ZMod 2), 1)
    : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ^ 1 ≠ 1 := by decide

end GroundTruth

/-! ## Axiom audit

`cdo_gnu_iteration` carries the file's single intended `sorry` and reports `sorryAx`
by construction — it is listed first and is the *only* declaration allowed to.  Every
other declaration must report a subset of `{propext, Classical.choice, Quot.sound}`.
The subset is the sound `native_decide` detector: a use would appear as a
per-declaration `*._native.native_decide.ax_*` axiom on this toolchain
(`Lean.ofReduceBool` is never emitted, so grepping for it detects nothing).  This
file contains no `native_decide`. -/

#print axioms cdo_gnu_iteration

#print axioms gnu_iterate_one_eq_one
#print axioms gnu_iterate_zero_eq_zero
#print axioms gnu_iterate_eq_one_of_le
#print axioms exists_gnu_iterate_eq_one_iff_forall_le
#print axioms exists_gnu_iterate_eq_one_gnu_iff
#print axioms not_exists_gnu_iterate_zero_eq_one
#print axioms exists_gnu_iterate_eq_one_of_gnu_eq_one
#print axioms cdo_gnu_iteration_one
#print axioms cdo_gnu_iteration_prime
#print axioms gnu_iterate_two
#print axioms gnu_iterate_two_four
#print axioms cdo_gnu_iteration_four
#print axioms multiplicative_zmod_prod_pow_eq_one
#print axioms not_isCyclic_multiplicative_zmod_prod
#print axioms nonempty_mulEquiv_multiplicative_zmod_prod
#print axioms gnu_prime_sq
#print axioms gnu_iterate_two_prime_sq
#print axioms cdo_gnu_iteration_prime_sq

end GroupCount
