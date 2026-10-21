/-
# Counterexamples to Dujella's conjecture on integral points on `E_{a,b,c}`

## Source

Ana Jurašić and Matej Jurašić, "Counterexamples to Dujella's conjecture on
integral points on the elliptic curve attached to a Diophantine triple",
arXiv:2608.22635.  Statement in Section 1 (Dujella, *Diophantine m-tuples and
Elliptic Curves*, 2024, Conjecture 1.4.5, and Dujella's open-problem list,
Problem 4.8); the construction is Proposition 2.1, Lemma 2.3, Theorem 3.1,
Corollary 3.2, and the explicit `k = 15` witness of Section 4.

Verbatim (abstract): "Dujella formulated the conjecture that the only integral
x-coordinates on the attached elliptic curve y^2=(ax+1)(bx+1)(cx+1) are
0, d_-, d_+, together with -1 when the triple contains 1, where
d_{\pm}=a+b+c+2abc \pm 2\sqrt{(ab+1)(ac+1)(bc+1)}.  The weaker question was
stated as Problem 4.8 in Dujella's list of open problems: must every integral
point with x\ne-1 make ax+1, bx+1, and cx+1 all perfect squares?  We construct
infinitely many triples {5,115,c} admitting an integral point with x\ne-1 for
which all three factors are nonsquares."

Verbatim (Theorem 3.1): "For every k in A = {k ≥ 0 : k ≡ 15 or 440 (mod 575)},
... c_k, x_k, y_k are positive integers and {5,115,c_k} is a Diophantine
triple; (x_k, ±y_k) is an integral point on y^2=(5x+1)(115x+1)(c_kx+1); each
of 5x_k+1, 115x_k+1, and c_kx_k+1 is a nonsquare in Z."

Date recorded: 2026-10-21.

## Status

Proved in the paper (the negative answers to Problem 4.8 and to
Conjecture 1.4.5 are the paper's Corollary 3.2).  This module formalizes the
whole family of Theorem 3.1 (with the Pell orbit given by the recurrence of
the paper, bridged to `(1 + √23)(24 + 5√23)^k` in `ℤ√23`), Corollary 3.2,
and the two refutations.

## Proof route

The Pell orbit `(T_k, S_k)` is reduced modulo `N = 2875 · 11 · 2851`.  The
reduced orbit has period `1150` (a single kernel computation), so for
`k ≡ 15, 440 (mod 575)` the residue of `S_k` mod `N` is one of four explicit
values, all with `S_k^2 ≡ 54596851 (mod N)`.  This pins down
`x_k ≡ 4 (mod 11)` and `x_k ≡ 1884 (mod 2851)`, whence
`5x_k + 1 ≡ 115x_k + 1 ≡ 10 (mod 11)` and `c_k x_k + 1 ≡ 1235 (mod 2851)`,
both quadratic nonresidues (the second by Euler's criterion).
-/
import Mathlib

set_option autoImplicit false

namespace DujellaIntegralPoints

/-! ## Definitions mirroring the source -/

/-- A **Diophantine triple** `{a, b, c}`: distinct positive integers such that
`ab + 1`, `ac + 1` and `bc + 1` are perfect squares. -/
def IsDiophantineTriple (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    IsSquare (a * b + 1) ∧ IsSquare (a * c + 1) ∧ IsSquare (b * c + 1)

/-- `(x, y)` is an integral point on `E_{a,b,c} : y^2 = (ax+1)(bx+1)(cx+1)`. -/
def IsIntegralPoint (a b c : ℕ) (x y : ℤ) : Prop :=
  y ^ 2 = ((a : ℤ) * x + 1) * ((b : ℤ) * x + 1) * ((c : ℤ) * x + 1)

/-- `√((ab+1)(ac+1)(bc+1))`, computed as `Nat.sqrt`; for a Diophantine triple the
radicand is a perfect square, so this is the exact square root. -/
def sqrtProd (a b c : ℕ) : ℕ := Nat.sqrt ((a * b + 1) * (a * c + 1) * (b * c + 1))

/-- The regular extension `d_+ = a + b + c + 2abc + 2√((ab+1)(ac+1)(bc+1))`. -/
def dPlus (a b c : ℕ) : ℤ :=
  ((a + b + c + 2 * a * b * c : ℕ) : ℤ) + 2 * (sqrtProd a b c : ℤ)

/-- The regular extension `d_- = a + b + c + 2abc - 2√((ab+1)(ac+1)(bc+1))`
(an integer, computed in `ℤ`). -/
def dMinus (a b c : ℕ) : ℤ :=
  ((a + b + c + 2 * a * b * c : ℕ) : ℤ) - 2 * (sqrtProd a b c : ℤ)

/-- **Dujella's Problem 4.8** (open-problem list), as a proposition: for every
Diophantine triple `{a, b, c}`, every integral point `(x, y)` on `E_{a,b,c}` with
`x ≠ -1` makes `ax + 1`, `bx + 1` and `cx + 1` all perfect squares. -/
def Problem48 : Prop :=
  ∀ a b c : ℕ, IsDiophantineTriple a b c → ∀ x y : ℤ, IsIntegralPoint a b c x y → x ≠ -1 →
    IsSquare ((a : ℤ) * x + 1) ∧ IsSquare ((b : ℤ) * x + 1) ∧ IsSquare ((c : ℤ) * x + 1)

/-- **Dujella's Conjecture 1.4.5** (*Diophantine m-tuples and Elliptic Curves*):
for every Diophantine triple `{a, b, c}`, the only integral `x`-coordinates on
`E_{a,b,c}` are `0`, `d_-`, `d_+`, together with `-1` when `1 ∈ {a, b, c}`. -/
def Conjecture145 : Prop :=
  ∀ a b c : ℕ, IsDiophantineTriple a b c → ∀ x y : ℤ, IsIntegralPoint a b c x y →
    x = 0 ∨ x = dMinus a b c ∨ x = dPlus a b c ∨ (x = -1 ∧ (a = 1 ∨ b = 1 ∨ c = 1))

/-- The first Pell orbit of `T^2 - 23 S^2 = -22`, via the paper's recurrence
`T_{k+1} = 24 T_k + 115 S_k`, `S_{k+1} = 5 T_k + 24 S_k`, `T_0 = S_0 = 1`. -/
def pellTS : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 => (24 * (pellTS k).1 + 115 * (pellTS k).2, 5 * (pellTS k).1 + 24 * (pellTS k).2)

/-- `T_k`, the rational coefficient of `(1 + √23)(24 + 5√23)^k`. -/
def pellT (k : ℕ) : ℕ := (pellTS k).1

/-- `S_k`, the `√23`-coefficient of `(1 + √23)(24 + 5√23)^k`. -/
def pellS (k : ℕ) : ℕ := (pellTS k).2

/-- `c_k = (S_k^2 - 1)/5`.  The theorems below certify `5 c_k + 1 = S_k^2`, so the
truncated subtraction and division are exact where used. -/
def cK (k : ℕ) : ℕ := (pellS k ^ 2 - 1) / 5

/-- `x_k = (c_k - 120)/575 = (S_k^2 - 601)/2875`.  The theorems below certify
`2875 x_k + 601 = S_k^2` for `k ≡ 15, 440 (mod 575)`, so the truncated
subtraction and division are exact there. -/
def xK (k : ℕ) : ℕ := (pellS k ^ 2 - 601) / 2875

/-! ## Ground truth -/

example : IsDiophantineTriple 1 3 8 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨5, by norm_num⟩⟩

example : dMinus 1 3 8 = 0 ∧ dPlus 1 3 8 = 120 := by
  have h : sqrtProd 1 3 8 = 30 := by
    unfold sqrtProd
    norm_num [show (900 : ℕ) = 30 * 30 by norm_num, Nat.sqrt_eq]
  simp [dMinus, dPlus, h]

example : pellTS 1 = (139, 29) := rfl

example : pellT 15 = 47629391928872028421837349 := by decide

example : pellS 15 = 9931414749943516928215699 := by decide

example : cK 15 = 19726599787079129775103071759543738099950374011720 := by decide

example : xK 15 = 34307130064485443087135776973119544521652824368 := by decide

/-! ## The Pell orbit -/

/-- Bridge to the paper's definition: `T_k + S_k √23 = (1 + √23)(24 + 5√23)^k`
in `ℤ√23`. -/
theorem pellTS_zsqrtd (k : ℕ) :
    (⟨pellT k, pellS k⟩ : ℤ√23) = ⟨1, 1⟩ * ⟨24, 5⟩ ^ k := by
  induction k with
  | zero => ext <;> simp [pellT, pellS, pellTS]
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ← ih]
    ext <;> simp only [pellT, pellS, pellTS, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-- The norm equation `T_k^2 - 23 S_k^2 = -22`, written without subtraction. -/
theorem pell_norm (k : ℕ) : pellT k ^ 2 + 22 = 23 * pellS k ^ 2 := by
  induction k with
  | zero => simp [pellT, pellS, pellTS]
  | succ k ih =>
    simp only [pellT, pellS, pellTS] at ih ⊢
    nlinarith [ih]

/-- The modulus `N = 2875 · 11 · 2851` carrying all congruences of the proof. -/
def bigN : ℕ := 90162875

/-- One step of the Pell recurrence modulo `m`. -/
def stepMod (m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  ((24 * p.1 + 115 * p.2) % m, (5 * p.1 + 24 * p.2) % m)

/-- The reduced orbit is the reduction of the orbit. -/
theorem iterate_stepMod (k : ℕ) :
    (stepMod bigN)^[k] (1, 1) = (pellT k % bigN, pellS k % bigN) := by
  induction k with
  | zero => simp [pellT, pellS, pellTS, bigN]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [stepMod, pellT, pellS, pellTS, bigN, Prod.mk.injEq]
    constructor <;> omega

set_option maxRecDepth 100000 in
/-- The reduced orbit returns to `(1, 1)` after `1150` steps (kernel computation). -/
theorem stepMod_period : (stepMod bigN)^[1150] (1, 1) = (1, 1) := by
  decide

/-- Periodicity of the orbit modulo `N` with period `1150`. -/
theorem pellS_mod_bigN (k : ℕ) : pellS k % bigN = pellS (k % 1150) % bigN := by
  have h := congrArg Prod.snd (iterate_stepMod k)
  have h' := congrArg Prod.snd (iterate_stepMod (k % 1150))
  simp only at h h'
  rw [← h, ← h']
  conv_lhs => rw [← Nat.mod_add_div k 1150, Function.iterate_add_apply,
    Function.iterate_mul, Function.iterate_fixed stepMod_period]

set_option maxRecDepth 100000 in
/-- For `k ≡ 15, 440 (mod 575)`, `S_k^2 ≡ 54596851 (mod N)`. -/
theorem pellS_sq_mod (k : ℕ) (hk : k % 575 = 15 ∨ k % 575 = 440) :
    pellS k ^ 2 % bigN = 54596851 := by
  have hr : k % 1150 = 15 ∨ k % 1150 = 440 ∨ k % 1150 = 590 ∨ k % 1150 = 1015 := by omega
  have hs : pellS k % bigN = ((stepMod bigN)^[k % 1150] (1, 1)).2 := by
    rw [pellS_mod_bigN k, iterate_stepMod]
  rw [Nat.pow_mod, hs]
  rcases hr with h | h | h | h <;> rw [h] <;> decide

/-- Arithmetic consequences of `S_k^2 ≡ 54596851 (mod N)`: the divisions defining
`c_k` and `x_k` are exact, `c_k = 575 x_k + 120`, and the residues
`x_k ≡ 4 (mod 11)`, `x_k ≡ 1884 (mod 2851)` hold. -/
theorem cK_xK_facts (k : ℕ) (hk : k % 575 = 15 ∨ k % 575 = 440) :
    5 * cK k + 1 = pellS k ^ 2 ∧ 2875 * xK k + 601 = pellS k ^ 2 ∧
      575 * xK k + 120 = cK k ∧ xK k % 11 = 4 ∧ xK k % 2851 = 1884 := by
  have hQ := pellS_sq_mod k hk
  unfold cK xK
  unfold bigN at hQ
  generalize pellS k ^ 2 = Q at hQ ⊢
  omega

/-- If `n ≡ r (mod p)` and `r` is not a square in `ZMod p`, then `n` is not a
square in `ℤ`. -/
theorem not_isSquare_of_mod {p : ℕ} (n r : ℕ) (hn : n % p = r)
    (hr : ¬ IsSquare (r : ZMod p)) : ¬ IsSquare (n : ℤ) := by
  rintro ⟨z, hz⟩
  apply hr
  refine ⟨(z : ZMod p), ?_⟩
  have h1 : ((n : ℤ) : ZMod p) = ((z * z : ℤ) : ZMod p) := by rw [hz]
  rw [← hn, ZMod.natCast_mod]
  push_cast at h1
  exact h1

/-- `10` is a quadratic nonresidue modulo `11`. -/
theorem not_isSquare_ten_zmod11 : ¬ IsSquare ((10 : ℕ) : ZMod 11) := by
  rintro ⟨r, hr⟩
  revert r
  decide

/-- `1235` is a quadratic nonresidue modulo the prime `2851` (Euler's criterion:
`1235^1425 ≡ -1 (mod 2851)`). -/
theorem not_isSquare_1235_zmod2851 : ¬ IsSquare ((1235 : ℕ) : ZMod 2851) := by
  have hne : ((1235 : ℕ) : ZMod 2851) ≠ 0 := by decide
  have hnat : 1235 ^ 1425 % 2851 = 2850 := by decide +kernel
  have hpow : ((1235 : ℕ) : ZMod 2851) ^ (2851 / 2) ≠ 1 := by
    have h1 : ((1235 ^ 1425 : ℕ) : ZMod 2851) = ((2850 : ℕ) : ZMod 2851) := by
      rw [← ZMod.natCast_mod, hnat]
    have h2 : (2851 / 2 : ℕ) = 1425 := by norm_num
    rw [h2, ← Nat.cast_pow, h1]
    decide
  haveI : Fact (Nat.Prime 2851) := ⟨by norm_num⟩
  rw [ZMod.euler_criterion 2851 hne]
  exact hpow

set_option maxRecDepth 100000 in
/-- Finite check over one period of the reduced orbit (kernel computation,
about 20 seconds): `S_r^2 ≡ 601 (mod 2875)` exactly for `r ≡ 15, 440 (mod 575)`. -/
theorem orbit_check : ∀ r < 1150, (((stepMod bigN)^[r] (1, 1)).2 ^ 2 % 2875 = 601 ↔
    (r % 575 = 15 ∨ r % 575 = 440)) := by
  decide +kernel

/-- **Lemma 2.3 (Jurašić–Jurašić).**  For every `k ≥ 0`,
`x_k = (S_k^2 - 601)/2875` is an integer, i.e. `2875 ∣ S_k^2 - 601` in `ℤ`, if
and only if `k ≡ 15` or `440 (mod 575)`. -/
theorem lem_2_3 (k : ℕ) :
    (2875 : ℤ) ∣ (pellS k : ℤ) ^ 2 - 601 ↔ k % 575 = 15 ∨ k % 575 = 440 := by
  have hs : pellS k % bigN = ((stepMod bigN)^[k % 1150] (1, 1)).2 := by
    rw [pellS_mod_bigN k, iterate_stepMod]
  have hmod : pellS k ^ 2 % 2875 = ((stepMod bigN)^[k % 1150] (1, 1)).2 ^ 2 % 2875 := by
    have hdvd : 2875 ∣ bigN := by norm_num [bigN]
    rw [← hs, Nat.pow_mod]
    conv_rhs => rw [Nat.pow_mod, Nat.mod_mod_of_dvd _ hdvd]
  have hchk := orbit_check (k % 1150) (Nat.mod_lt _ (by norm_num))
  rw [← hmod] at hchk
  have hk : (k % 1150) % 575 = k % 575 := Nat.mod_mod_of_dvd _ (by norm_num)
  rw [hk] at hchk
  rw [← hchk]
  have hcast : ((pellS k : ℤ) ^ 2) = ((pellS k ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [hcast]
  generalize pellS k ^ 2 = Q
  omega

/-! ## Theorem 3.1 -/

/-- **Theorem 3.1 (Jurašić–Jurašić, arXiv:2608.22635).**  For every
`k ≡ 15` or `440 (mod 575)`, with `c_k = (S_k^2 - 1)/5`, `x_k = (S_k^2 - 601)/2875`
and `y_k = c_k x_k + 1`: the divisions are exact (`5 c_k + 1 = S_k^2`,
`115 c_k + 1 = T_k^2`, `c_k = 575 x_k + 120`), `x_k` is positive, `{5, 115, c_k}`
is a Diophantine triple, `(x_k, y_k)` is an integral point on
`y^2 = (5x+1)(115x+1)(c_k x+1)`, and none of `5x_k+1`, `115x_k+1`, `c_k x_k+1`
is a perfect square in `ℤ`. -/
theorem thm_3_1 (k : ℕ) (hk : k % 575 = 15 ∨ k % 575 = 440) :
    5 * cK k + 1 = pellS k ^ 2 ∧ 115 * cK k + 1 = pellT k ^ 2 ∧
      575 * xK k + 120 = cK k ∧ 0 < xK k ∧
      IsDiophantineTriple 5 115 (cK k) ∧
      IsIntegralPoint 5 115 (cK k) (xK k) ((cK k : ℤ) * xK k + 1) ∧
      ¬ IsSquare (5 * (xK k : ℤ) + 1) ∧ ¬ IsSquare (115 * (xK k : ℤ) + 1) ∧
      ¬ IsSquare ((cK k : ℤ) * xK k + 1) := by
  obtain ⟨hS, -, hcx, hx11, hx2851⟩ := cK_xK_facts k hk
  have hnorm := pell_norm k
  have hT : 115 * cK k + 1 = pellT k ^ 2 := by omega
  have hxpos : 0 < xK k := by omega
  refine ⟨hS, hT, hcx, hxpos, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, by omega, by norm_num, by omega, by omega,
      ⟨24, by norm_num⟩, ⟨pellS k, by rw [hS, sq]⟩, ⟨pellT k, by rw [hT, sq]⟩⟩
  · unfold IsIntegralPoint
    have hcxZ : (cK k : ℤ) = 575 * xK k + 120 := by exact_mod_cast hcx.symm
    rw [hcxZ]
    push_cast
    ring
  · have h := not_isSquare_of_mod (p := 11) (5 * xK k + 1) 10 (by omega)
      not_isSquare_ten_zmod11
    push_cast at h
    exact h
  · have h := not_isSquare_of_mod (p := 11) (115 * xK k + 1) 10 (by omega)
      not_isSquare_ten_zmod11
    push_cast at h
    exact h
  · have hc : cK k % 2851 = 40 := by omega
    have hmod : (cK k * xK k + 1) % 2851 = 1235 := by
      rw [Nat.add_mod, Nat.mul_mod, hc, hx2851]
    have h := not_isSquare_of_mod (p := 2851) (cK k * xK k + 1) 1235 hmod
      not_isSquare_1235_zmod2851
    push_cast at h
    exact h

/-- `T_k` is positive. -/
theorem pellT_pos (k : ℕ) : 0 < pellT k := by
  induction k with
  | zero => simp [pellT, pellTS]
  | succ k ih =>
    simp only [pellT, pellTS] at ih ⊢
    omega

/-- `S_k` is strictly increasing, since `S_{k+1} = 5 T_k + 24 S_k > S_k`. -/
theorem pellS_strictMono : StrictMono pellS := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have hT := pellT_pos k
  simp only [pellS, pellT, pellTS] at hT ⊢
  omega

/-- **Distinctness and minimality in Theorem 3.1.**  The triples `{5, 115, c_k}`
for `k ≡ 15, 440 (mod 575)` are pairwise distinct, and the least `c_k` in the
family is `c_15`. -/
theorem cK_injective_and_min (j k : ℕ) (hj : j % 575 = 15 ∨ j % 575 = 440)
    (hk : k % 575 = 15 ∨ k % 575 = 440) :
    (cK j = cK k → j = k) ∧ cK 15 ≤ cK k := by
  obtain ⟨hSj, -⟩ := thm_3_1 j hj
  obtain ⟨hSk, -⟩ := thm_3_1 k hk
  obtain ⟨hS15, -⟩ := thm_3_1 15 (Or.inl rfl)
  constructor
  · intro hc
    have hsq : pellS j ^ 2 = pellS k ^ 2 := by rw [← hSj, ← hSk, hc]
    have hS : pellS j = pellS k := by
      exact Nat.pow_left_injective (n := 2) (by norm_num) hsq
    exact pellS_strictMono.injective hS
  · have h15 : 15 ≤ k := by omega
    have hle : pellS 15 ≤ pellS k := pellS_strictMono.monotone h15
    have hsq : pellS 15 ^ 2 ≤ pellS k ^ 2 := Nat.pow_le_pow_left hle 2
    omega

/-! ## Corollary 3.2 and the refutations -/

/-- For the triple `{5, 115, c_k}`, `√((ab+1)(ac+1)(bc+1)) = 24 S_k T_k`. -/
theorem sqrtProd_eq (k : ℕ) (hk : k % 575 = 15 ∨ k % 575 = 440) :
    sqrtProd 5 115 (cK k) = 24 * pellS k * pellT k := by
  obtain ⟨hS, hT, -⟩ := thm_3_1 k hk
  unfold sqrtProd
  rw [hS, hT]
  rw [show (5 * 115 + 1) * pellS k ^ 2 * pellT k ^ 2
      = (24 * pellS k * pellT k) * (24 * pellS k * pellT k) by ring]
  exact Nat.sqrt_eq _

/-- At the regular extensions of `{5, 115, c_k}`, `5 d_± + 1 = (5 T_k ± 24 S_k)^2`
is a perfect square. -/
theorem isSquare_five_mul_d_add_one (k : ℕ) (hk : k % 575 = 15 ∨ k % 575 = 440) :
    IsSquare (5 * dMinus 5 115 (cK k) + 1) ∧ IsSquare (5 * dPlus 5 115 (cK k) + 1) := by
  obtain ⟨hS, hT, -⟩ := thm_3_1 k hk
  have hSZ : (5 * (cK k : ℤ) + 1) = (pellS k : ℤ) ^ 2 := by exact_mod_cast hS
  have hTZ : (115 * (cK k : ℤ) + 1) = (pellT k : ℤ) ^ 2 := by exact_mod_cast hT
  have hsq := sqrtProd_eq k hk
  unfold dMinus dPlus
  rw [hsq]
  push_cast
  constructor
  · refine ⟨5 * (pellT k : ℤ) - 24 * pellS k, ?_⟩
    linear_combination (25 : ℤ) * hTZ + 576 * hSZ
  · refine ⟨5 * (pellT k : ℤ) + 24 * pellS k, ?_⟩
    linear_combination (25 : ℤ) * hTZ + 576 * hSZ

/-- **Corollary 3.2 (Jurašić–Jurašić).**  For every `k ≡ 15` or `440 (mod 575)`,
`x_k ∉ {-1, 0, d_-, d_+}` for the Diophantine triple `{5, 115, c_k}`. -/
theorem cor_3_2 (k : ℕ) (hk : k % 575 = 15 ∨ k % 575 = 440) :
    (xK k : ℤ) ≠ -1 ∧ (xK k : ℤ) ≠ 0 ∧ (xK k : ℤ) ≠ dMinus 5 115 (cK k) ∧
      (xK k : ℤ) ≠ dPlus 5 115 (cK k) := by
  obtain ⟨-, -, -, hxpos, -, -, hns, -⟩ := thm_3_1 k hk
  obtain ⟨hdm, hdp⟩ := isSquare_five_mul_d_add_one k hk
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h
    exact hns (h ▸ hdm)
  · intro h
    exact hns (h ▸ hdp)

/-- **Negative answer to Dujella's Problem 4.8** (Jurašić–Jurašić,
arXiv:2608.22635, Corollary 3.2): there is a Diophantine triple (`{5, 115, c_15}`)
and an integral point with `x ≠ -1` on its elliptic curve for which `ax + 1`,
`bx + 1`, `cx + 1` are not all perfect squares (in fact none is). -/
theorem problem48_false : ¬ Problem48 := by
  intro h
  have hk : (15 : ℕ) % 575 = 15 ∨ (15 : ℕ) % 575 = 440 := Or.inl rfl
  obtain ⟨-, -, -, -, htriple, hpt, hns, -⟩ := thm_3_1 15 hk
  have hne : (xK 15 : ℤ) ≠ -1 := (cor_3_2 15 hk).1
  exact hns (h 5 115 (cK 15) htriple _ _ hpt hne).1

/-- **Dujella's Conjecture 1.4.5 is false** (Jurašić–Jurašić, arXiv:2608.22635,
Corollary 3.2): for the Diophantine triple `{5, 115, c_15}`, the integral point
with `x = x_15` has `x ∉ {0, d_-, d_+}` and `x ≠ -1`. -/
theorem conjecture145_false : ¬ Conjecture145 := by
  intro h
  have hk : (15 : ℕ) % 575 = 15 ∨ (15 : ℕ) % 575 = 440 := Or.inl rfl
  obtain ⟨-, -, -, -, htriple, hpt, -⟩ := thm_3_1 15 hk
  obtain ⟨hne1, hne0, hnem, hnep⟩ := cor_3_2 15 hk
  rcases h 5 115 (cK 15) htriple _ _ hpt with h0 | hm | hp | ⟨h1, -⟩
  · exact hne0 h0
  · exact hnem hm
  · exact hnep hp
  · exact hne1 h1

/-- **The explicit least counterexample** (Section 4 of arXiv:2608.22635):
`c_15 = 19726599787079129775103071759543738099950374011720` and
`x_15 = 34307130064485443087135776973119544521652824368`; `{5, 115, c_15}` is a
Diophantine triple, `(x_15, c_15 x_15 + 1)` lies on `y^2 = (5x+1)(115x+1)(c_15 x+1)`,
and none of the three factors is a perfect square. -/
theorem explicit_counterexample :
    IsDiophantineTriple 5 115 19726599787079129775103071759543738099950374011720 ∧
      IsIntegralPoint 5 115 19726599787079129775103071759543738099950374011720
        34307130064485443087135776973119544521652824368
        (19726599787079129775103071759543738099950374011720 *
          34307130064485443087135776973119544521652824368 + 1) ∧
      ¬ IsSquare (5 * (34307130064485443087135776973119544521652824368 : ℤ) + 1) ∧
      ¬ IsSquare (115 * (34307130064485443087135776973119544521652824368 : ℤ) + 1) ∧
      ¬ IsSquare ((19726599787079129775103071759543738099950374011720 : ℤ) *
          34307130064485443087135776973119544521652824368 + 1) := by
  have hc : cK 15 = 19726599787079129775103071759543738099950374011720 := by decide
  have hx : xK 15 = 34307130064485443087135776973119544521652824368 := by decide
  obtain ⟨-, -, -, -, htriple, hpt, h5, h115, hc'⟩ := thm_3_1 15 (Or.inl rfl)
  rw [hc] at htriple hpt hc'
  rw [hx] at hpt h5 h115 hc'
  exact ⟨htriple, by exact_mod_cast hpt, by exact_mod_cast h5, by exact_mod_cast h115,
    by exact_mod_cast hc'⟩


end DujellaIntegralPoints
