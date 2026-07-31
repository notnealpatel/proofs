/-
  The general fixed-divisor theorem for affine-exponential families
  `n ↦ A · 2 ^ n + B` over ℤ.  THE DELIVERABLE of this lane.

  ── What this file is ───────────────────────────────────────────────
  A covering system `{a_i (mod d_i)}` together with, for each class, a
  divisor `p_i > 1` satisfying

      `2 ^ d_i ≡ 1 (mod p_i)`   and   `p_i ∣ A · 2 ^ a_i + B`

  forces `A · 2 ^ n + B` to have a divisor in `{p_i}` for *every*
  `n : ℕ`.  That is the entire mathematical content of the Sierpiński,
  Riesel and Erdős-1950 constructions, and it is stated here once, for
  arbitrary `A B : ℤ`, arbitrary covering data, and arbitrary divisors.

  The three classical applications are the three instantiations:

    | family              | `A`  | `B` | file                              |
    | ------------------- | ---- | --- | --------------------------------- |
    | `k · 2 ^ n + 1`     | `k`  | `1` | `Erdos.Covering.Sierpinski`       |
    | `k · 2 ^ n - 1`     | `k`  | `-1`| `Erdos.Covering.Riesel`           |
    | `m - 2 ^ n`         | `-1` | `m` | `Erdos.Covering.Erdos1950Instance`|

  ── This file imports none of them ──────────────────────────────────
  The framework stands on `Erdos.Covering.Basic` and Mathlib alone.
  In particular it does **not** import
  `Erdos.Covering.NotTwoPowerPlusPrime`: the retrofit showing that
  file's bespoke fixed-divisor argument to be the `A = -1`, `B = m`
  instance lives in the leaf module `Erdos.Covering.Erdos1950Instance`,
  which imports both.  The dependency graph is

      Basic ──▸ FixedDivisor ──▸ { Sierpinski, Riesel }
        │             │
        │             └──────────▸ Erdos1950Instance ◂── NotTwoPowerPlusPrime
        └──────────────────────────────────────────────┘

  so the general theorem is not an after-the-fact generalization of any
  single proof.

  ── Prior art ───────────────────────────────────────────────────────
  Cowles and Gamboa, "Verifying Sierpiński and Riesel Numbers in ACL2",
  EPTCS 70 (2011), 31–39, arXiv:1110.4671, machine-verified in ACL2
  that `78557` is a Sierpiński number and `509203` is a Riesel number
  (`books/workshops/2011/cowles-gamboa-sierpinski/support/`
  `verifying-macros.lisp`, lines 771 and 813).  Their abstract is
  explicit that the artefact is per-number: "Given a k and its cover,
  ACL2 is used to systematically verify that each integer of the given
  form has a non-trivial factor in the cover"; the macro that generates
  the per-number proof obligations is itself unverified.  The general
  criterion — covering system plus paired divisors implies fixed
  divisor — is what is formalized here.  A survey on 2026-07-31 of
  Mathlib, google-deepmind/formal-conjectures, plby/lean-proofs and the
  Isabelle AFP found no statement of it in any proof assistant.
  Priority on the two concrete numbers belongs to Cowles–Gamboa, and
  `78557` additionally has a bespoke `native_decide` proof in
  formal-conjectures; see the application files, which say so.

  ── Encoding ────────────────────────────────────────────────────────
  The certificate is a `Finset (ℕ × ℕ × ℕ)` of triples `(a, d, p)`:
  residue, modulus, divisor.  Carrying the divisor inside the Finset —
  rather than a `Finset (ℕ × ℕ)` plus a partner function `ℕ × ℕ → ℕ` —
  makes every concrete certificate a single Finset literal and every
  hypothesis a bounded `∀ t ∈ T`, hence `decide`-able with no function
  definition to elaborate.  The projection `residueClasses` recovers
  the `Finset (ℕ × ℕ)` that `Erdos.Covering.Basic` consumes, so the
  coverage check still routes through the proved equivalence
  `covers_iff_forall_range`.

  ── Contents ────────────────────────────────────────────────────────
  * `residueClasses`, `fixedDivisors` — the two projections of a
    certificate, with ground checks.
  * `Composite` — `1 < n ∧ ¬ n.Prime`, matching `Nat.Composite` of
    google-deepmind/formal-conjectures.
  * `IsFixedDivisorSystem A B T` — the certificate predicate.
  * `covers_residueClasses_iff_forall_range`,
    `isFixedDivisorSystem_iff` — the `decide`-able characterizations.
  * `two_pow_intModEq_pow_mod`, `two_pow_intModEq_of_mod_eq` — the
    order bridge: `2 ^ n (mod p)` depends only on `n mod d`.
  * `dvd_affine_two_pow_of_mod_eq` — the per-class step, for a single
    triple `(a, d, p)`.
  * `IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd` — **the general
    theorem**.
  * `IsFixedDivisorSystem.composite`,
    `IsFixedDivisorSystem.not_prime` — the compositeness corollary.
  * `IsFixedDivisorSystem.of_dvd_sub_const`, `.of_dvd_sub_coeff`,
    `intCast_dvd_sub_of_mod_eq` — translation: one certificate serves
    a whole arithmetic progression in `A` or in `B`.
  * §5 — drop-one negative controls. Fields (b) `covers`,
    (c) `two_pow_modEq_one` and (d) `divisor_dvd` are each shown
    necessary for the general theorem by a certificate satisfying the
    other three at which its conclusion FAILS. Field (a)
    `one_lt_divisor` is different and is documented as such at the
    control: it is NOT in the proof cone of
    `exists_mem_fixedDivisors_dvd`, which stays true without it. It is
    load-bearing for `.composite`/`.not_prime`, and for the predicate
    being a non-trivial certificate at all.
  * §6 — satisfiability: two concrete models with opposite sign
    patterns, at which all four fields hold jointly.

  Axiom audit: see the `#print axioms` block at the end.  Every
  declaration is sorry-free.  No `native_decide`, no custom axioms.
-/

import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 CERTIFICATES: DEFINITIONS
-- ════════════════════════════════════════════════════════════════════

/-- The residue classes of a certificate `T : Finset (ℕ × ℕ × ℕ)` of
    triples `(a, d, p)`: forget the divisor, keeping the pair
    `(a, d)` that `Erdos.Covering.Basic` consumes. -/
def residueClasses (T : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.image fun t => (t.1, t.2.1)

/-- The divisors of a certificate `T : Finset (ℕ × ℕ × ℕ)` of triples
    `(a, d, p)`: forget the class, keeping `p`.  In the classical
    applications these are the primes of the *covering set*. -/
def fixedDivisors (T : Finset (ℕ × ℕ × ℕ)) : Finset ℕ :=
  T.image fun t => t.2.2

/-- `n` is composite: `1 < n` and `n` is not prime.  This is the shape
    of `Nat.Composite` in google-deepmind/formal-conjectures
    (`FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean`,
    `abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime`), which
    current Mathlib does not provide. -/
def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- Membership in `residueClasses`. -/
theorem mem_residueClasses {T : Finset (ℕ × ℕ × ℕ)} {q : ℕ × ℕ} :
    q ∈ residueClasses T ↔ ∃ t ∈ T, (t.1, t.2.1) = q :=
  Finset.mem_image

/-- Membership in `fixedDivisors`. -/
theorem mem_fixedDivisors {T : Finset (ℕ × ℕ × ℕ)} {p : ℕ} :
    p ∈ fixedDivisors T ↔ ∃ t ∈ T, t.2.2 = p :=
  Finset.mem_image

-- Ground checks for the two projections and for `Composite`, on the
-- Sierpiński certificate of `Erdos.Covering.Sierpinski`.
example :
    residueClasses {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19),
      (27, 36, 37), (3, 9, 73)} =
      {(0, 2), (1, 4), (1, 3), (11, 12), (15, 18), (27, 36), (3, 9)} := by decide

example :
    fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19),
      (27, 36, 37), (3, 9, 73)} = {3, 5, 7, 13, 19, 37, 73} := by decide

-- The projections collapse repeats, as images do: two classes sharing
-- a divisor contribute one divisor.
example : fixedDivisors {(0, 2, 3), (1, 2, 3)} = {3} := by decide
example : residueClasses {(0, 2, 3), (0, 2, 5)} = {(0, 2)} := by decide

-- `Composite` at the boundary: `0`, `1`, and the primes are excluded.
example : Composite 4 := ⟨by norm_num, by norm_num⟩
example : Composite 9 := ⟨by norm_num, by norm_num⟩
example : ¬ Composite 0 := fun h => absurd h.1 (by norm_num)
example : ¬ Composite 1 := fun h => absurd h.1 (by norm_num)
example : ¬ Composite 2 := fun h => h.2 (by norm_num)
example : ¬ Composite 7 := fun h => h.2 (by norm_num)

/-- **Fixed-divisor certificate** for the family `n ↦ A · 2 ^ n + B`.

    `T` is a finite set of triples `(a, d, p)` — residue, modulus,
    divisor — such that

    * every divisor exceeds `1` (without this the certificate `{(0,1,1)}`
      would satisfy the remaining fields for *every* `A` and `B`,
      making the certificate vacuous as a certificate even though
      `exists_mem_fixedDivisors_dvd` itself survives its removal;
      see the negative control (a) in §5);
    * the classes `a (mod d)` cover ℤ;
    * `2 ^ d ≡ 1 (mod p)`, i.e. `d` is a multiple of the multiplicative
      order of `2` mod `p` — minimality is never needed;
    * `p ∣ A · 2 ^ a + B`, the base case of the class.

    `IsFixedDivisorSystem A B T` says exactly that `T` certifies a fixed
    divisor for `A · 2 ^ n + B`; the theorem is
    `IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd`. -/
structure IsFixedDivisorSystem (A B : ℤ) (T : Finset (ℕ × ℕ × ℕ)) : Prop where
  /-- Every divisor is strictly greater than `1`. -/
  one_lt_divisor : ∀ t ∈ T, 1 < t.2.2
  /-- The residue classes `a (mod d)` cover every integer. -/
  covers : Covers (residueClasses T)
  /-- `d` annihilates `2` mod `p`: `2 ^ d ≡ 1 (mod p)`. -/
  two_pow_modEq_one : ∀ t ∈ T, 2 ^ t.2.1 ≡ 1 [MOD t.2.2]
  /-- `p` divides the family at the base exponent `a` of its class. -/
  divisor_dvd : ∀ t ∈ T, (t.2.2 : ℤ) ∣ A * 2 ^ t.1 + B

-- ════════════════════════════════════════════════════════════════════
-- §2 DECIDABLE CHARACTERIZATION
-- ════════════════════════════════════════════════════════════════════

/-- Coverage by the classes of a certificate, reduced to the finite
    check on `0, …, L - 1` for any positive common multiple `L` of the
    moduli.  This is `Erdos.Covering.covers_iff_forall_range` composed
    with the image projection, restated over the triples so that no
    `Finset.image` appears in the `decide`-able side. -/
theorem covers_residueClasses_iff_forall_range {T : Finset (ℕ × ℕ × ℕ)}
    (L : ℕ) (hL : 0 < L) (hdvd : ∀ t ∈ T, t.2.1 ∣ L) :
    Covers (residueClasses T) ↔
      ∀ r ∈ Finset.range L, ∃ t ∈ T, r % t.2.1 = t.1 % t.2.1 := by
  have hdvd' : ∀ q ∈ residueClasses T, q.2 ∣ L := by
    intro q hq
    obtain ⟨t, htT, rfl⟩ := mem_residueClasses.mp hq
    exact hdvd t htT
  rw [covers_iff_forall_range L hL hdvd']
  constructor
  · intro hf r hr
    obtain ⟨q, hqC, hq⟩ := hf r hr
    obtain ⟨t, htT, rfl⟩ := mem_residueClasses.mp hqC
    exact ⟨t, htT, hq⟩
  · intro hf r hr
    obtain ⟨t, htT, ht⟩ := hf r hr
    exact ⟨(t.1, t.2.1), mem_residueClasses.mpr ⟨t, htT, rfl⟩, ht⟩

/-- Decidable characterization of `IsFixedDivisorSystem`, for any
    positive common multiple `L` of the moduli: all four fields become
    bounded quantifications over `T` and `Finset.range L`, hence
    checkable by kernel `decide`. -/
theorem isFixedDivisorSystem_iff (A B : ℤ) (T : Finset (ℕ × ℕ × ℕ)) (L : ℕ)
    (hL : 0 < L) (hdvd : ∀ t ∈ T, t.2.1 ∣ L) :
    IsFixedDivisorSystem A B T ↔
      (∀ t ∈ T, 1 < t.2.2) ∧
        (∀ r ∈ Finset.range L, ∃ t ∈ T, r % t.2.1 = t.1 % t.2.1) ∧
          (∀ t ∈ T, 2 ^ t.2.1 % t.2.2 = 1 % t.2.2) ∧
            ∀ t ∈ T, (t.2.2 : ℤ) ∣ A * 2 ^ t.1 + B := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (covers_residueClasses_iff_forall_range L hL hdvd).mp h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (covers_residueClasses_iff_forall_range L hL hdvd).mpr h2, h3, h4⟩

-- ════════════════════════════════════════════════════════════════════
-- §3 THE GENERAL THEOREM
-- ════════════════════════════════════════════════════════════════════

/-- If `2 ^ d ≡ 1 (mod p)` then `2 ^ m (mod p)` depends only on
    `m mod d`.  No positivity hypothesis on `d` is needed: for `d = 0`
    the statement is `2 ^ m ≡ 2 ^ m`. -/
theorem two_pow_intModEq_pow_mod {p d : ℕ} (hpow : 2 ^ d ≡ 1 [MOD p]) (m : ℕ) :
    (2 : ℤ) ^ m ≡ 2 ^ (m % d) [ZMOD (p : ℤ)] := by
  have hpowZ : (2 : ℤ) ^ d ≡ 1 [ZMOD (p : ℤ)] := by
    have hcast := Int.natCast_modEq_iff.mpr hpow
    push_cast at hcast
    exact hcast
  conv_lhs => rw [← Nat.div_add_mod m d, pow_add, pow_mul]
  calc ((2 : ℤ) ^ d) ^ (m / d) * 2 ^ (m % d)
      ≡ 1 ^ (m / d) * 2 ^ (m % d) [ZMOD (p : ℤ)] :=
        Int.ModEq.mul (hpowZ.pow _) (Int.ModEq.refl _)
    _ = 2 ^ (m % d) := by rw [one_pow, one_mul]

/-- Two exponents in the same class mod `d` give congruent powers of
    `2` mod `p`, whenever `2 ^ d ≡ 1 (mod p)`.  The residue `a` need
    not be reduced mod `d`. -/
theorem two_pow_intModEq_of_mod_eq {p d a n : ℕ} (hpow : 2 ^ d ≡ 1 [MOD p])
    (h : n % d = a % d) : (2 : ℤ) ^ n ≡ 2 ^ a [ZMOD (p : ℤ)] := by
  calc (2 : ℤ) ^ n ≡ 2 ^ (n % d) [ZMOD (p : ℤ)] := two_pow_intModEq_pow_mod hpow n
    _ = 2 ^ (a % d) := by rw [h]
    _ ≡ 2 ^ a [ZMOD (p : ℤ)] := (two_pow_intModEq_pow_mod hpow a).symm

/-- **One class, one divisor** — the per-class step, stated for a
    single triple `(a, d, p)` and arbitrary `A B : ℤ`.  If
    `2 ^ d ≡ 1 (mod p)` and `p` divides the family at the base exponent
    `a`, then `p` divides it at every exponent `n ≡ a (mod d)`.

    This generalizes `Erdos.Covering.dvd_sub_two_pow_of_modEq` of
    `NotTwoPowerPlusPrime.lean`, which is the case `A = -1`, `B = m`;
    the re-derivation is `dvd_sub_two_pow_of_modEq_of_general` in
    `Erdos.Covering.Erdos1950Instance`. -/
theorem dvd_affine_two_pow_of_mod_eq {A B : ℤ} {p d a n : ℕ}
    (hpow : 2 ^ d ≡ 1 [MOD p]) (hbase : (p : ℤ) ∣ A * 2 ^ a + B)
    (hn : n % d = a % d) : (p : ℤ) ∣ A * 2 ^ n + B := by
  have hfam : A * 2 ^ n + B ≡ A * 2 ^ a + B [ZMOD (p : ℤ)] :=
    ((two_pow_intModEq_of_mod_eq hpow hn).mul_left A).add_right B
  exact Int.modEq_zero_iff_dvd.mp (hfam.trans (Int.modEq_zero_iff_dvd.mpr hbase))

/-- **The general fixed-divisor theorem.**  If `T` certifies a fixed
    divisor for the family `n ↦ A · 2 ^ n + B` — its classes cover ℤ,
    each modulus `d` satisfies `2 ^ d ≡ 1 (mod p)` for its partner
    divisor `p`, and `p ∣ A · 2 ^ a + B` at the base exponent — then
    for *every* exponent `n` some `p ∈ fixedDivisors T` divides
    `A · 2 ^ n + B`.

    Stated over ℤ so that `B = -1` (Riesel) and `A = -1` (Erdős 1950)
    are literal instances with no ℕ-subtraction guard. -/
theorem IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystem A B T) (n : ℕ) :
    ∃ p ∈ fixedDivisors T, (p : ℤ) ∣ A * 2 ^ n + B := by
  -- Pick the class of the certificate containing the exponent `n`.
  obtain ⟨q, hqC, hcong⟩ := h.covers (n : ℤ)
  obtain ⟨t, htT, rfl⟩ := mem_residueClasses.mp hqC
  have hmod : n % t.2.1 = t.1 % t.2.1 := Int.natCast_modEq_iff.mp hcong
  exact ⟨t.2.2, mem_fixedDivisors.mpr ⟨t, htT, rfl⟩,
    dvd_affine_two_pow_of_mod_eq (h.two_pow_modEq_one t htT) (h.divisor_dvd t htT) hmod⟩

/-- A certificate is nonempty: some class must contain the exponent
    `0`. -/
theorem IsFixedDivisorSystem.nonempty {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)}
    (h : IsFixedDivisorSystem A B T) : T.Nonempty := by
  obtain ⟨q, hqC, -⟩ := h.covers 0
  obtain ⟨t, htT, -⟩ := mem_residueClasses.mp hqC
  exact ⟨t, htT⟩

/-- **Compositeness corollary.**  If `N : ℕ` is a value of the
    certified family, `(N : ℤ) = A · 2 ^ n + B`, and `N` exceeds a
    bound `M` on the divisors of the certificate, then `N` is
    composite: it is a multiple of some `p` with `1 < p ≤ M < N`.

    The bound is passed as an explicit `M` rather than
    `(fixedDivisors T).max'` so that no nonemptiness side condition
    leaks into the statement. -/
theorem IsFixedDivisorSystem.composite {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)}
    (h : IsFixedDivisorSystem A B T) {M N n : ℕ}
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hN : (N : ℤ) = A * 2 ^ n + B)
    (hMN : M < N) : Composite N := by
  obtain ⟨p, hp, hdvd⟩ := h.exists_mem_fixedDivisors_dvd n
  obtain ⟨t, htT, rfl⟩ := mem_fixedDivisors.mp hp
  have hp1 : 1 < t.2.2 := h.one_lt_divisor t htT
  have hpM : t.2.2 ≤ M := hM t.2.2 hp
  have hpN : t.2.2 ∣ N := by
    have hZ : ((t.2.2 : ℕ) : ℤ) ∣ (N : ℤ) := by rw [hN]; exact hdvd
    exact_mod_cast hZ
  refine ⟨by omega, fun hprime => ?_⟩
  rcases hprime.eq_one_or_self_of_dvd t.2.2 hpN with h1 | h2 <;> omega

/-- **Compositeness corollary, primality phrasing.**  Under the
    hypotheses of `IsFixedDivisorSystem.composite`, `N` is not
    prime. -/
theorem IsFixedDivisorSystem.not_prime {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)}
    (h : IsFixedDivisorSystem A B T) {M N n : ℕ}
    (hM : ∀ p ∈ fixedDivisors T, p ≤ M) (hN : (N : ℤ) = A * 2 ^ n + B)
    (hMN : M < N) : ¬ N.Prime :=
  (h.composite hM hN hMN).2

-- ════════════════════════════════════════════════════════════════════
-- §4 TRANSLATION: THE SAME CERTIFICATE SERVES A WHOLE PROGRESSION
-- ════════════════════════════════════════════════════════════════════

/-- Moving the constant term `B` by a multiple of every divisor keeps
    the certificate valid.  This is what makes Erdős's 1950 theorem an
    instance: there `B` is the variable `m`, ranging over an arithmetic
    progression modulo the product of the divisors (see
    `Erdos.Covering.Erdos1950Instance`). -/
theorem IsFixedDivisorSystem.of_dvd_sub_const {A B B' : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystem A B T)
    (hBB : ∀ p ∈ fixedDivisors T, (p : ℤ) ∣ B' - B) :
    IsFixedDivisorSystem A B' T where
  one_lt_divisor := h.one_lt_divisor
  covers := h.covers
  two_pow_modEq_one := h.two_pow_modEq_one
  divisor_dvd := by
    intro t ht
    have hbase := h.divisor_dvd t ht
    have hshift := hBB t.2.2 (mem_fixedDivisors.mpr ⟨t, ht, rfl⟩)
    have hsum := dvd_add hbase hshift
    have heq : A * 2 ^ t.1 + B + (B' - B) = A * 2 ^ t.1 + B' := by ring
    rwa [heq] at hsum

/-- Moving the coefficient `A` by a multiple of every divisor keeps the
    certificate valid.  This is what makes Sierpiński and Riesel
    numbers come in arithmetic progressions — hence Sierpiński's 1960
    theorem that infinitely many exist. -/
theorem IsFixedDivisorSystem.of_dvd_sub_coeff {A A' B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystem A B T)
    (hAA : ∀ p ∈ fixedDivisors T, (p : ℤ) ∣ A' - A) :
    IsFixedDivisorSystem A' B T where
  one_lt_divisor := h.one_lt_divisor
  covers := h.covers
  two_pow_modEq_one := h.two_pow_modEq_one
  divisor_dvd := by
    intro t ht
    have hbase := h.divisor_dvd t ht
    have hshift := (hAA t.2.2 (mem_fixedDivisors.mpr ⟨t, ht, rfl⟩)).mul_right ((2 : ℤ) ^ t.1)
    have hsum := dvd_add hbase hshift
    have heq : A * 2 ^ t.1 + B + (A' - A) * 2 ^ t.1 = A' * 2 ^ t.1 + B := by ring
    rwa [heq] at hsum

/-- A ℕ-level congruence `m % P = M` as an integer divisibility.  Cast
    before subtracting, per STYLE.md: `(M : ℤ)` may exceed `(m : ℤ)`
    only when `m < M`, which `m % P = M` excludes, but the ℤ statement
    needs no such argument. -/
theorem intCast_dvd_sub_of_mod_eq {P M m : ℕ} (hm : m % P = M) :
    (P : ℤ) ∣ (m : ℤ) - (M : ℤ) := by
  refine ⟨((m / P : ℕ) : ℤ), ?_⟩
  have hdm : P * (m / P) + m % P = m := Nat.div_add_mod m P
  rw [hm] at hdm
  have hcast : ((P * (m / P) + M : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast hdm
  -- `Nat.cast_add`/`Nat.cast_mul` only: `push_cast` would rewrite
  -- `((m / P : ℕ) : ℤ)` to the truncating `(m : ℤ) / (P : ℤ)` and
  -- strand the witness supplied to `Dvd.intro`.
  rw [Nat.cast_add, Nat.cast_mul] at hcast
  linarith

-- ════════════════════════════════════════════════════════════════════
-- §5 DROP-ONE NEGATIVE CONTROLS: EVERY FIELD IS LOAD-BEARING
-- ════════════════════════════════════════════════════════════════════

/-! Fields (b), (c) and (d) are each shown necessary for the general
theorem by a certificate satisfying the other three at which its
conclusion FAILS.

Field (a) `one_lt_divisor` is NOT of that form, and saying otherwise
would overstate it: `exists_mem_fixedDivisors_dvd` does not mention
`one_lt_divisor` in its proof cone and remains true without it. What
control (a) exhibits is that dropping the field makes the certificate
worthless rather than the theorem false — `{(0, 1, 1)}` satisfies the
other three for every `A` and `B`, and its conclusion, while true, says
only that `1` divides something. The field is genuinely load-bearing
for `.composite`/`.not_prime`, which do consume it.

Together with the satisfiability witness of §6 these pin the predicate
from both sides. -/

-- ── (a) `one_lt_divisor` ────────────────────────────────────────────
-- Without it the certificate `{(0, 1, 1)}` satisfies the other three
-- fields for *every* `A` and `B` — modulus `1` covers ℤ, `2 ^ 1 ≡ 1`
-- mod `1`, and `1` divides everything — so `IsFixedDivisorSystem`
-- would be a tautology and certify nothing.
example (A B : ℤ) :
    Covers (residueClasses {(0, 1, 1)}) ∧
      (∀ t ∈ ({(0, 1, 1)} : Finset (ℕ × ℕ × ℕ)), 2 ^ t.2.1 ≡ 1 [MOD t.2.2]) ∧
        ∀ t ∈ ({(0, 1, 1)} : Finset (ℕ × ℕ × ℕ)), (t.2.2 : ℤ) ∣ A * 2 ^ t.1 + B := by
  refine ⟨(covers_residueClasses_iff_forall_range 1 (by decide) (by decide)).mpr (by decide),
    by decide, ?_⟩
  intro t ht
  fin_cases ht
  simp

-- The field really is violated by that certificate …
example : ¬ IsFixedDivisorSystem 1 1 {(0, 1, 1)} := fun h =>
  absurd (h.one_lt_divisor (0, 1, 1) (by decide)) (by decide)

-- … and its conclusion would be worthless: `1 * 2 ^ 1 + 1 = 3` is
-- prime, so no compositeness can follow from a divisor equal to `1`.
example : ¬ Composite 3 := fun h => h.2 (by norm_num)

-- ── (b) `covers` ────────────────────────────────────────────────────
-- The single class `0 (mod 2)` with divisor `3` satisfies the other
-- three fields for `A = 78557`, `B = 1` (`3 ∣ 78557 + 1 = 78558`),
-- but its classes miss the odd exponents.
example : (∀ t ∈ ({(0, 2, 3)} : Finset (ℕ × ℕ × ℕ)), 1 < t.2.2) ∧
    (∀ t ∈ ({(0, 2, 3)} : Finset (ℕ × ℕ × ℕ)), 2 ^ t.2.1 ≡ 1 [MOD t.2.2]) ∧
      ∀ t ∈ ({(0, 2, 3)} : Finset (ℕ × ℕ × ℕ)),
        (t.2.2 : ℤ) ∣ (78557 : ℤ) * 2 ^ t.1 + 1 := by decide

example : ¬ Covers (residueClasses {(0, 2, 3)}) := fun h =>
  absurd ((covers_residueClasses_iff_forall_range 2 (by decide) (by decide)).mp h)
    (by decide)

-- The conclusion of the general theorem fails at `n = 1`:
-- `78557 · 2 + 1 = 157115 = 5 · 7 · 67 · 67` is not divisible by `3`.
example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 1 + 1 := by
  decide

-- ── (c) `two_pow_modEq_one` ─────────────────────────────────────────
-- The certificate `{(0, 1, 2)}` for `A = B = 1` covers ℤ (modulus `1`),
-- has `1 < 2`, and `2 ∣ 2 ^ 0 + 1 = 2`; only `2 ^ 1 ≡ 1 (mod 2)` fails.
example : (∀ t ∈ ({(0, 1, 2)} : Finset (ℕ × ℕ × ℕ)), 1 < t.2.2) ∧
    Covers (residueClasses {(0, 1, 2)}) ∧
      ∀ t ∈ ({(0, 1, 2)} : Finset (ℕ × ℕ × ℕ)),
        (t.2.2 : ℤ) ∣ (1 : ℤ) * 2 ^ t.1 + 1 :=
  ⟨by decide,
    (covers_residueClasses_iff_forall_range 1 (by decide) (by decide)).mpr (by decide),
    by decide⟩

example : ¬ ∀ t ∈ ({(0, 1, 2)} : Finset (ℕ × ℕ × ℕ)), 2 ^ t.2.1 ≡ 1 [MOD t.2.2] := by
  decide

-- The conclusion fails at `n = 1`: `2 ^ 1 + 1 = 3` is odd.
example : ¬ ∃ p ∈ fixedDivisors {(0, 1, 2)}, (p : ℤ) ∣ (1 : ℤ) * 2 ^ 1 + 1 := by decide

-- ── (d) `divisor_dvd` ───────────────────────────────────────────────
-- `{0 (mod 2), 1 (mod 2)}` with divisor `3` covers ℤ, has `1 < 3` and
-- `2 ^ 2 ≡ 1 (mod 3)`; it simply is not attached to the family
-- `2 ^ n + 1`, and the base divisibility is what detects that.
example : (∀ t ∈ ({(0, 2, 3), (1, 2, 3)} : Finset (ℕ × ℕ × ℕ)), 1 < t.2.2) ∧
    Covers (residueClasses {(0, 2, 3), (1, 2, 3)}) ∧
      ∀ t ∈ ({(0, 2, 3), (1, 2, 3)} : Finset (ℕ × ℕ × ℕ)),
        2 ^ t.2.1 ≡ 1 [MOD t.2.2] :=
  ⟨by decide,
    (covers_residueClasses_iff_forall_range 2 (by decide) (by decide)).mpr (by decide),
    by decide⟩

example : ¬ ∀ t ∈ ({(0, 2, 3), (1, 2, 3)} : Finset (ℕ × ℕ × ℕ)),
    (t.2.2 : ℤ) ∣ (1 : ℤ) * 2 ^ t.1 + 1 := by decide

-- The conclusion fails at `n = 0`: `2 ^ 0 + 1 = 2` is not divisible
-- by `3`.
example : ¬ ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 2, 3)}, (p : ℤ) ∣ (1 : ℤ) * 2 ^ 0 + 1 := by
  decide

-- ════════════════════════════════════════════════════════════════════
-- §6 SATISFIABILITY WITNESS
-- ════════════════════════════════════════════════════════════════════

/-! The negative controls of §5 pin `IsFixedDivisorSystem` from one
side; STYLE.md requires the other — a single concrete model at which
all four fields hold *jointly*, so that the predicate is not
contradictory and the general theorem is not vacuous.

Selfridge's seven-class certificate for `78557 · 2 ^ n + 1` is that
model, spelled here with literal numerals so that this file depends on
none of its applications.  `Erdos.Covering.Sierpinski` develops it into
`isSierpinskiNumber_78557`; `Erdos.Covering.Riesel` and
`Erdos.Covering.Erdos1950Instance` supply two more models, at
`(A, B) = (509203, -1)` and `(-1, m)` respectively. -/

example : IsFixedDivisorSystem 78557 1
    {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19), (27, 36, 37),
      (3, 9, 73)} :=
  (isFixedDivisorSystem_iff 78557 1 _ 36 (by decide) (by decide)).mpr (by decide)

-- The conclusion at that model is not trivially true: the divisors are
-- seven distinct primes, all far below the values of the family, and
-- the exponent `n = 27` really does need the class `27 (mod 36)`.
example : fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19),
    (27, 36, 37), (3, 9, 73)} = {3, 5, 7, 13, 19, 37, 73} := by decide
example : ∃ p ∈ fixedDivisors {(0, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13),
    (15, 18, 19), (27, 36, 37), (3, 9, 73)}, (p : ℤ) ∣ (78557 : ℤ) * 2 ^ 27 + 1 := by
  decide

-- A second model with a different sign pattern, so that neither
-- `B = 1` nor a positive `A` is doing hidden work: Riesel's
-- certificate at `(A, B) = (509203, -1)`.
example : IsFixedDivisorSystem 509203 (-1)
    {(0, 2, 3), (1, 4, 5), (2, 3, 7), (7, 12, 13), (7, 8, 17), (3, 24, 241)} :=
  (isFixedDivisorSystem_iff 509203 (-1) _ 24 (by decide) (by decide)).mpr (by decide)

-- ════════════════════════════════════════════════════════════════════
-- §7 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms residueClasses
#print axioms fixedDivisors
#print axioms Composite
#print axioms mem_residueClasses
#print axioms mem_fixedDivisors
#print axioms IsFixedDivisorSystem
#print axioms covers_residueClasses_iff_forall_range
#print axioms isFixedDivisorSystem_iff
#print axioms two_pow_intModEq_pow_mod
#print axioms two_pow_intModEq_of_mod_eq
#print axioms dvd_affine_two_pow_of_mod_eq
#print axioms IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd
#print axioms IsFixedDivisorSystem.nonempty
#print axioms IsFixedDivisorSystem.composite
#print axioms IsFixedDivisorSystem.not_prime
#print axioms IsFixedDivisorSystem.of_dvd_sub_const
#print axioms IsFixedDivisorSystem.of_dvd_sub_coeff
#print axioms intCast_dvd_sub_of_mod_eq

end Erdos.Covering

