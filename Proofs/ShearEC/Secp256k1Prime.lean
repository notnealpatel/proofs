import Mathlib

/-!
# The secp256k1 base-field prime, kernel-checked

A Pratt-style primality certificate for `p = 2^256 - 2^32 - 977`, the base
field of the secp256k1 elliptic curve, discharging the
`Fact (Nat.Prime secp256k1P)` hypothesis of
`ShearEC.ShearInversionLB.secp256k1_inversion_needs_256_shears` and
`ShearEC.ShearAdditionEC.secp256k1_some_add_some`.

## Route

Trial division (`norm_num`'s `Nat.Prime` extension) cannot reach 256 bits, so
we use Mathlib's `lucas_primality`: `p` is prime if some `a : ZMod p`
satisfies `a ^ (p - 1) = 1` and `a ^ ((p - 1) / q) ≠ 1` for every prime
`q ∣ p - 1`. Certifying the *prime* divisors of `p - 1` recurses into the
same test — the classical Pratt certificate tree. For this `p` the tree
(factorizations and witnesses computed and verified with SageMath) is

```
p    (256 bits), witness  3 : p - 1  = 2 · 3 · 7 · 13441 · q₁
q₁   (237 bits), witness 10 : q₁ - 1 = 2 · 3 · 5 · 29² · 31 · 7723 · q₂ · q₃
q₂   ( 77 bits), witness  6 : q₂ - 1 = 2 · 3 · q₄
q₄   ( 75 bits), witness  5 : q₄ - 1 = 2³ · 3 · 5323 · q₅
q₅   ( 58 bits), witness  6 : q₅ - 1 = 2³ · 5² · 2621 · 24809 · 13331831
q₃   (128 bits), witness  3 : q₃ - 1 = 2³ · 7² · 11 · 1627 · 2657 · 4423
                                        · 41201 · 96557 · 7240687 · 107590001
```

with every remaining factor `≤ 107590001` handled by `norm_num` trial
division.

## Trust story

The recurring computational obligation `a ^ e % q = r` (256-bit numbers,
256-bit exponents) is discharged **in the kernel** by `decide` on the
fuel-based binary modular exponentiation `powMod` below: structural recursion
that the kernel reduces step by step, with each step a `Nat`
multiply/mod/div on literals — GMP-accelerated primitives of the Lean 4
kernel itself. `powMod_correct` (`powMod p a e = a ^ e % p`) converts each
checked value into the `ZMod` power facts `lucas_primality` consumes.

**No `native_decide` and no axioms** beyond `propext`/`Quot.sound`/`Classical.choice`:
the entire certificate is kernel-checked (`#print axioms secp256k1P_prime`
confirms). The SageMath computation only *found* the tree; Lean re-verifies
all of it.
-/

namespace ShearEC.Secp256k1Prime

/-! ## Kernel-reducible modular exponentiation -/

/-- Fuel-based binary modular exponentiation, `acc · a ^ e (mod p)`.
Structural recursion on `fuel` (never well-founded recursion) so that the
kernel can reduce applications on `Nat` literals; each step uses only the
kernel's GMP-accelerated `Nat` primitives. -/
def powModAux (p : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, a, e, acc =>
    if e = 0 then acc
    else powModAux p fuel (a * a % p) (e / 2)
      (if e % 2 = 1 then acc * a % p else acc)

lemma powModAux_correct (p : ℕ) : ∀ fuel e a acc, e < 2 ^ fuel →
    acc % p = acc → powModAux p fuel a e acc = acc * a ^ e % p := by
  intro fuel
  induction fuel with
  | zero =>
      intro e a acc he hacc
      interval_cases e
      simpa [powModAux] using hacc.symm
  | succ fuel ih =>
      intro e a acc he hacc
      rcases eq_or_ne e 0 with rfl | he0
      · simpa [powModAux] using hacc.symm
      · rw [powModAux, if_neg he0]
        rw [ih (e / 2) (a * a % p) _
          (Nat.div_lt_of_lt_mul (by rw [pow_succ] at he; omega))
          (by split
              · exact Nat.mod_mod_of_dvd _ dvd_rfl
              · exact hacc)]
        have h2 : (a * a % p) ^ (e / 2) ≡ (a * a) ^ (e / 2) [MOD p] :=
          (Nat.mod_modEq _ _).pow _
        have hacc' : (if e % 2 = 1 then acc * a % p else acc)
            ≡ acc * a ^ (e % 2) [MOD p] := by
          split
          · next h => rw [h, pow_one]; exact Nat.mod_modEq _ _
          · next h =>
              have h0 : e % 2 = 0 := by omega
              rw [h0, pow_zero, mul_one]
        calc (if e % 2 = 1 then acc * a % p else acc) * (a * a % p) ^ (e / 2) % p
            = acc * a ^ (e % 2) * (a * a) ^ (e / 2) % p := hacc'.mul h2
          _ = acc * a ^ e % p := by
              rw [← pow_two, ← pow_mul, mul_assoc, ← pow_add]
              congr 3
              omega

/-- Binary modular exponentiation: `powMod p a e = a ^ e % p`, computable by
kernel reduction in `O(log e)` GMP steps. -/
def powMod (p a e : ℕ) : ℕ := powModAux p e (a % p) e (1 % p)

theorem powMod_correct (p a e : ℕ) : powMod p a e = a ^ e % p := by
  rw [powMod, powModAux_correct p e e (a % p) (1 % p) Nat.lt_two_pow_self
    (Nat.mod_mod_of_dvd _ dvd_rfl)]
  calc 1 % p * (a % p) ^ e % p = 1 * a ^ e % p :=
        (Nat.mod_modEq 1 p).mul ((Nat.mod_modEq a p).pow e)
    _ = a ^ e % p := by rw [one_mul]

/-- Bridge a kernel-checked `powMod` value into the `ZMod` equation that
`lucas_primality` consumes. -/
theorem zmod_pow_eq_one {q g e : ℕ} (hq : 1 < q) (h : powMod q g e = 1) :
    ((g : ℕ) : ZMod q) ^ e = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt hq]
  exact (powMod_correct q g e).symm.trans h

/-- Bridge a kernel-checked `powMod ≠ 1` into the `ZMod` disequation that
`lucas_primality` consumes. -/
theorem zmod_pow_ne_one {q g e : ℕ} (hq : 1 < q) (h : powMod q g e ≠ 1) :
    ((g : ℕ) : ZMod q) ^ e ≠ 1 := by
  intro hcontra
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt hq] at hcontra
  exact h ((powMod_correct q g e).trans hcontra)

/-! ## The certificate tree, leaves upward

Each `decide` below is a kernel-checked modular exponentiation; each
`norm_num` primality leaf is kernel-checked trial division. Generated from
the SageMath-verified Pratt tree (see the module docstring). -/

set_option maxRecDepth 20000

/-- `173378833005251801` is prime: Lucas certificate with witness `6`;
the totient factors as `2^3 * 5^2 * 2621 * 24809 * 13331831`. -/
theorem prime_q5 : Nat.Prime 173378833005251801 := by
  refine lucas_primality _ ((6 : ℕ) : ZMod 173378833005251801) ?_ ?_
  · rw [show (173378833005251801 : ℕ) - 1 = 173378833005251800 from by norm_num]
    exact zmod_pow_eq_one (by norm_num) (by decide)
  · intro f hf hdvd
    rw [show (173378833005251801 : ℕ) - 1 = 2 ^ 3 * (5 ^ 2 * (2621 ^ 1 * (24809 ^ 1 * (13331831 ^ 1)))) from by norm_num] at hdvd
    rcases hf.dvd_mul.mp hdvd with h | hdvd
    · obtain rfl : f = 2 :=
        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
      rw [show ((173378833005251801 : ℕ) - 1) / 2 = 86689416502625900 from by norm_num]
      exact zmod_pow_ne_one (by norm_num) (by decide)
    · rcases hf.dvd_mul.mp hdvd with h | hdvd
      · obtain rfl : f = 5 :=
          (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
        rw [show ((173378833005251801 : ℕ) - 1) / 5 = 34675766601050360 from by norm_num]
        exact zmod_pow_ne_one (by norm_num) (by decide)
      · rcases hf.dvd_mul.mp hdvd with h | hdvd
        · obtain rfl : f = 2621 :=
            (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
          rw [show ((173378833005251801 : ℕ) - 1) / 2621 = 66149879055800 from by norm_num]
          exact zmod_pow_ne_one (by norm_num) (by decide)
        · rcases hf.dvd_mul.mp hdvd with h | hdvd
          · obtain rfl : f = 24809 :=
              (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
            rw [show ((173378833005251801 : ℕ) - 1) / 24809 = 6988545810200 from by norm_num]
            exact zmod_pow_ne_one (by norm_num) (by decide)
          · obtain rfl : f = 13331831 :=
              (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow hdvd)
            rw [show ((173378833005251801 : ℕ) - 1) / 13331831 = 13004877800 from by norm_num]
            exact zmod_pow_ne_one (by norm_num) (by decide)

/-- `22149492674086928081353` is prime: Lucas certificate with witness `5`;
the totient factors as `2^3 * 3 * 5323 * 173378833005251801`. -/
theorem prime_q4 : Nat.Prime 22149492674086928081353 := by
  refine lucas_primality _ ((5 : ℕ) : ZMod 22149492674086928081353) ?_ ?_
  · rw [show (22149492674086928081353 : ℕ) - 1 = 22149492674086928081352 from by norm_num]
    exact zmod_pow_eq_one (by norm_num) (by decide)
  · intro f hf hdvd
    rw [show (22149492674086928081353 : ℕ) - 1 = 2 ^ 3 * (3 ^ 1 * (5323 ^ 1 * (173378833005251801 ^ 1))) from by norm_num] at hdvd
    rcases hf.dvd_mul.mp hdvd with h | hdvd
    · obtain rfl : f = 2 :=
        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
      rw [show ((22149492674086928081353 : ℕ) - 1) / 2 = 11074746337043464040676 from by norm_num]
      exact zmod_pow_ne_one (by norm_num) (by decide)
    · rcases hf.dvd_mul.mp hdvd with h | hdvd
      · obtain rfl : f = 3 :=
          (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
        rw [show ((22149492674086928081353 : ℕ) - 1) / 3 = 7383164224695642693784 from by norm_num]
        exact zmod_pow_ne_one (by norm_num) (by decide)
      · rcases hf.dvd_mul.mp hdvd with h | hdvd
        · obtain rfl : f = 5323 :=
            (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
          rw [show ((22149492674086928081353 : ℕ) - 1) / 5323 = 4161091992126043224 from by norm_num]
          exact zmod_pow_ne_one (by norm_num) (by decide)
        · obtain rfl : f = 173378833005251801 :=
            (Nat.prime_dvd_prime_iff_eq hf (prime_q5)).mp (hf.dvd_of_dvd_pow hdvd)
          rw [show ((22149492674086928081353 : ℕ) - 1) / 173378833005251801 = 127752 from by norm_num]
          exact zmod_pow_ne_one (by norm_num) (by decide)

/-- `132896956044521568488119` is prime: Lucas certificate with witness `6`;
the totient factors as `2 * 3 * 22149492674086928081353`. -/
theorem prime_q2 : Nat.Prime 132896956044521568488119 := by
  refine lucas_primality _ ((6 : ℕ) : ZMod 132896956044521568488119) ?_ ?_
  · rw [show (132896956044521568488119 : ℕ) - 1 = 132896956044521568488118 from by norm_num]
    exact zmod_pow_eq_one (by norm_num) (by decide)
  · intro f hf hdvd
    rw [show (132896956044521568488119 : ℕ) - 1 = 2 ^ 1 * (3 ^ 1 * (22149492674086928081353 ^ 1)) from by norm_num] at hdvd
    rcases hf.dvd_mul.mp hdvd with h | hdvd
    · obtain rfl : f = 2 :=
        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
      rw [show ((132896956044521568488119 : ℕ) - 1) / 2 = 66448478022260784244059 from by norm_num]
      exact zmod_pow_ne_one (by norm_num) (by decide)
    · rcases hf.dvd_mul.mp hdvd with h | hdvd
      · obtain rfl : f = 3 :=
          (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
        rw [show ((132896956044521568488119 : ℕ) - 1) / 3 = 44298985348173856162706 from by norm_num]
        exact zmod_pow_ne_one (by norm_num) (by decide)
      · obtain rfl : f = 22149492674086928081353 :=
          (Nat.prime_dvd_prime_iff_eq hf (prime_q4)).mp (hf.dvd_of_dvd_pow hdvd)
        rw [show ((132896956044521568488119 : ℕ) - 1) / 22149492674086928081353 = 6 from by norm_num]
        exact zmod_pow_ne_one (by norm_num) (by decide)

/-- `255515944373312847190720520512484175977` is prime: Lucas certificate with witness `3`;
the totient factors as `2^3 * 7^2 * 11 * 1627 * 2657 * 4423 * 41201 * 96557 * 7240687 * 107590001`. -/
theorem prime_q3 : Nat.Prime 255515944373312847190720520512484175977 := by
  refine lucas_primality _ ((3 : ℕ) : ZMod 255515944373312847190720520512484175977) ?_ ?_
  · rw [show (255515944373312847190720520512484175977 : ℕ) - 1 = 255515944373312847190720520512484175976 from by norm_num]
    exact zmod_pow_eq_one (by norm_num) (by decide)
  · intro f hf hdvd
    rw [show (255515944373312847190720520512484175977 : ℕ) - 1 = 2 ^ 3 * (7 ^ 2 * (11 ^ 1 * (1627 ^ 1 * (2657 ^ 1 * (4423 ^ 1 * (41201 ^ 1 * (96557 ^ 1 * (7240687 ^ 1 * (107590001 ^ 1))))))))) from by norm_num] at hdvd
    rcases hf.dvd_mul.mp hdvd with h | hdvd
    · obtain rfl : f = 2 :=
        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
      rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 2 = 127757972186656423595360260256242087988 from by norm_num]
      exact zmod_pow_ne_one (by norm_num) (by decide)
    · rcases hf.dvd_mul.mp hdvd with h | hdvd
      · obtain rfl : f = 7 :=
          (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
        rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 7 = 36502277767616121027245788644640596568 from by norm_num]
        exact zmod_pow_ne_one (by norm_num) (by decide)
      · rcases hf.dvd_mul.mp hdvd with h | hdvd
        · obtain rfl : f = 11 :=
            (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
          rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 11 = 23228722215755713380974592773862197816 from by norm_num]
          exact zmod_pow_ne_one (by norm_num) (by decide)
        · rcases hf.dvd_mul.mp hdvd with h | hdvd
          · obtain rfl : f = 1627 :=
              (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
            rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 1627 = 157047292177819820031174259688066488 from by norm_num]
            exact zmod_pow_ne_one (by norm_num) (by decide)
          · rcases hf.dvd_mul.mp hdvd with h | hdvd
            · obtain rfl : f = 2657 :=
                (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
              rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 2657 = 96167084822473785167753300907972968 from by norm_num]
              exact zmod_pow_ne_one (by norm_num) (by decide)
            · rcases hf.dvd_mul.mp hdvd with h | hdvd
              · obtain rfl : f = 4423 :=
                  (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
                rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 4423 = 57769826898782013834664372713652312 from by norm_num]
                exact zmod_pow_ne_one (by norm_num) (by decide)
              · rcases hf.dvd_mul.mp hdvd with h | hdvd
                · obtain rfl : f = 41201 :=
                    (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
                  rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 41201 = 6201692783507993669831327407404776 from by norm_num]
                  exact zmod_pow_ne_one (by norm_num) (by decide)
                · rcases hf.dvd_mul.mp hdvd with h | hdvd
                  · obtain rfl : f = 96557 :=
                      (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
                    rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 96557 = 2646270538369179315748423423599368 from by norm_num]
                    exact zmod_pow_ne_one (by norm_num) (by decide)
                  · rcases hf.dvd_mul.mp hdvd with h | hdvd
                    · obtain rfl : f = 7240687 :=
                        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
                      rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 7240687 = 35288908963101546467996824129048 from by norm_num]
                      exact zmod_pow_ne_one (by norm_num) (by decide)
                    · obtain rfl : f = 107590001 :=
                        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow hdvd)
                      rw [show ((255515944373312847190720520512484175977 : ℕ) - 1) / 107590001 = 2374904191824599455024826335976 from by norm_num]
                      exact zmod_pow_ne_one (by norm_num) (by decide)

/-- `205115282021455665897114700593932402728804164701536103180137503955397371` is prime: Lucas certificate with witness `10`;
the totient factors as `2 * 3 * 5 * 29^2 * 31 * 7723 * 132896956044521568488119 * 255515944373312847190720520512484175977`. -/
theorem prime_q1 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  refine lucas_primality _ ((10 : ℕ) : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ?_ ?_
  · rw [show (205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1 = 205115282021455665897114700593932402728804164701536103180137503955397370 from by norm_num]
    exact zmod_pow_eq_one (by norm_num) (by decide)
  · intro f hf hdvd
    rw [show (205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1 = 2 ^ 1 * (3 ^ 1 * (5 ^ 1 * (29 ^ 2 * (31 ^ 1 * (7723 ^ 1 * (132896956044521568488119 ^ 1 * (255515944373312847190720520512484175977 ^ 1))))))) from by norm_num] at hdvd
    rcases hf.dvd_mul.mp hdvd with h | hdvd
    · obtain rfl : f = 2 :=
        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
      rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 2 = 102557641010727832948557350296966201364402082350768051590068751977698685 from by norm_num]
      exact zmod_pow_ne_one (by norm_num) (by decide)
    · rcases hf.dvd_mul.mp hdvd with h | hdvd
      · obtain rfl : f = 3 :=
          (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
        rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 3 = 68371760673818555299038233531310800909601388233845367726712501318465790 from by norm_num]
        exact zmod_pow_ne_one (by norm_num) (by decide)
      · rcases hf.dvd_mul.mp hdvd with h | hdvd
        · obtain rfl : f = 5 :=
            (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
          rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 5 = 41023056404291133179422940118786480545760832940307220636027500791079474 from by norm_num]
          exact zmod_pow_ne_one (by norm_num) (by decide)
        · rcases hf.dvd_mul.mp hdvd with h | hdvd
          · obtain rfl : f = 29 :=
              (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
            rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 29 = 7072940759360540203348782779101117335476005679363313902763362205358530 from by norm_num]
            exact zmod_pow_ne_one (by norm_num) (by decide)
          · rcases hf.dvd_mul.mp hdvd with h | hdvd
            · obtain rfl : f = 31 :=
                (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
              rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 31 = 6616622000692118254745635503030077507380779506501164618714113030819270 from by norm_num]
              exact zmod_pow_ne_one (by norm_num) (by decide)
            · rcases hf.dvd_mul.mp hdvd with h | hdvd
              · obtain rfl : f = 7723 :=
                  (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
                rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 7723 = 26559016188198325248881872406310035313842310591937861346644762910190 from by norm_num]
                exact zmod_pow_ne_one (by norm_num) (by decide)
              · rcases hf.dvd_mul.mp hdvd with h | hdvd
                · obtain rfl : f = 132896956044521568488119 :=
                    (Nat.prime_dvd_prime_iff_eq hf (prime_q2)).mp (hf.dvd_of_dvd_pow h)
                  rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 132896956044521568488119 = 1543415952677955745309227852991199086604869270230 from by norm_num]
                  exact zmod_pow_ne_one (by norm_num) (by decide)
                · obtain rfl : f = 255515944373312847190720520512484175977 :=
                    (Nat.prime_dvd_prime_iff_eq hf (prime_q3)).mp (hf.dvd_of_dvd_pow hdvd)
                  rw [show ((205115282021455665897114700593932402728804164701536103180137503955397371 : ℕ) - 1) / 255515944373312847190720520512484175977 = 802749442992798076634733441528810 from by norm_num]
                  exact zmod_pow_ne_one (by norm_num) (by decide)

/-- `115792089237316195423570985008687907853269984665640564039457584007908834671663` is prime: Lucas certificate with witness `3`;
the totient factors as `2 * 3 * 7 * 13441 * 205115282021455665897114700593932402728804164701536103180137503955397371`. -/
theorem secp256k1P_prime : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  refine lucas_primality _ ((3 : ℕ) : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ?_ ?_
  · rw [show (115792089237316195423570985008687907853269984665640564039457584007908834671663 : ℕ) - 1 = 115792089237316195423570985008687907853269984665640564039457584007908834671662 from by norm_num]
    exact zmod_pow_eq_one (by norm_num) (by decide)
  · intro f hf hdvd
    rw [show (115792089237316195423570985008687907853269984665640564039457584007908834671663 : ℕ) - 1 = 2 ^ 1 * (3 ^ 1 * (7 ^ 1 * (13441 ^ 1 * (205115282021455665897114700593932402728804164701536103180137503955397371 ^ 1)))) from by norm_num] at hdvd
    rcases hf.dvd_mul.mp hdvd with h | hdvd
    · obtain rfl : f = 2 :=
        (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
      rw [show ((115792089237316195423570985008687907853269984665640564039457584007908834671663 : ℕ) - 1) / 2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 from by norm_num]
      exact zmod_pow_ne_one (by norm_num) (by decide)
    · rcases hf.dvd_mul.mp hdvd with h | hdvd
      · obtain rfl : f = 3 :=
          (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
        rw [show ((115792089237316195423570985008687907853269984665640564039457584007908834671663 : ℕ) - 1) / 3 = 38597363079105398474523661669562635951089994888546854679819194669302944890554 from by norm_num]
        exact zmod_pow_ne_one (by norm_num) (by decide)
      · rcases hf.dvd_mul.mp hdvd with h | hdvd
        · obtain rfl : f = 7 :=
            (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
          rw [show ((115792089237316195423570985008687907853269984665640564039457584007908834671663 : ℕ) - 1) / 7 = 16541727033902313631938712144098272550467140666520080577065369143986976381666 from by norm_num]
          exact zmod_pow_ne_one (by norm_num) (by decide)
        · rcases hf.dvd_mul.mp hdvd with h | hdvd
          · obtain rfl : f = 13441 :=
              (Nat.prime_dvd_prime_iff_eq hf (by norm_num)).mp (hf.dvd_of_dvd_pow h)
            rw [show ((115792089237316195423570985008687907853269984665640564039457584007908834671663 : ℕ) - 1) / 13441 = 8614841844901137967678817424945160914609774917464516333565775166126689582 from by norm_num]
            exact zmod_pow_ne_one (by norm_num) (by decide)
          · obtain rfl : f = 205115282021455665897114700593932402728804164701536103180137503955397371 :=
              (Nat.prime_dvd_prime_iff_eq hf (prime_q1)).mp (hf.dvd_of_dvd_pow hdvd)
            rw [show ((115792089237316195423570985008687907853269984665640564039457584007908834671663 : ℕ) - 1) / 205115282021455665897114700593932402728804164701536103180137503955397371 = 564522 from by norm_num]
            exact zmod_pow_ne_one (by norm_num) (by decide)
end ShearEC.Secp256k1Prime
