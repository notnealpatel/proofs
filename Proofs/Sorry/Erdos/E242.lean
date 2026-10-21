/-
  Erdős Problem #242 — the Erdős–Straus conjecture.
  Status: falsifiable (open).  Tier UB archive target (Mordell residue
  classes + witness layer).

  Verbatim statement (`goof erdos fetch 242`, pulled 2026-08-05):

    "For every $n>2$ there exist distinct integers $1\leq x<y<z$ such
    that \[\frac{4}{n} = \frac{1}{x}+\frac{1}{y}+\frac{1}{z}.\]"

  DB remarks: first in print Obláth 1950 (submitted 1948), as a
  conjecture of Erdős.  Verified for n ≤ 10¹⁸ [MiDu25].  Suffices for
  prime n.  Mordell: true except possibly n ≡ 1², 11², 13², 17², 19²,
  23² (mod 840) — i.e. {1, 121, 169, 289, 361, 529} (mod 840).  Terzi:
  198 bad classes mod 120120.  Vaughan: exceptions in [1,x] ≤
  x·exp(−c(log x)^{2/3}).  Bloom–Elsholtz [BlEl22, Thm 1]: equivalent
  congruence-existence form.  Comment thread (Jan 2026): a partial
  Lean repo (leochlon) exists with parametric-identity fragments, but
  its "CRT coverage" file was shown by Alexeev/Bloom to prove nothing
  beyond small-n checks — do NOT build on it; Bloom recommends
  formalizing the [BlEl22] equivalence instead.

  Mathlib inventory: ℚ arithmetic; nothing bespoke.  OEIS anchors:
  A073101 (solution counts), A075245–A075248 (x,y,z tables).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E242

/-- `ES n`: `4/n` is a sum of three distinct unit fractions
    `1/x + 1/y + 1/z` with `1 ≤ x < y < z` — the Erdős–Straus property,
    stated over ℚ (the `1 ≤ x` guard plus strict ordering keeps all
    denominators positive and distinct). -/
def ES (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- Witness layer: explicit decompositions for the first cases.
    4/3 = 1/1 + 1/4 + 1/12;  4/5 = 1/2 + 1/4 + 1/20;
    4/7 = 1/2 + 1/15 + 1/210.  -- PROVABLE (norm_num). -/
theorem es_3 : ES 3 := by
  exact ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The explicit decomposition `4/5 = 1/2 + 1/4 + 1/20`. -/
theorem es_5 : ES 5 := by
  exact ⟨2, 4, 20, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The explicit decomposition `4/7 = 1/2 + 1/15 + 1/210`. -/
theorem es_7 : ES 7 := by
  exact ⟨2, 15, 210, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The explicit decomposition of `4/4` with denominators `2, 3, 6`. -/
private theorem es_4 : ES 4 := by
  exact ⟨2, 3, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Multiplying all three denominators by a positive cofactor preserves `ES`. -/
private theorem es_mul (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : ES p) : ES (p * q) := by
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := h
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hzpos : 0 < z := by omega
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hxpos)
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hypos)
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hzpos)
  refine ⟨x * q, y * q, z * q, ?_,
    Nat.mul_lt_mul_of_pos_right hxy hq,
    Nat.mul_lt_mul_of_pos_right hyz hq, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hxpos hq))
  · push_cast
    calc
      (4 : ℚ) / ((p : ℚ) * q) = (4 / p) / q := by
        field_simp
      _ = (1 / x + 1 / y + 1 / z) / q := by rw [heq]
      _ = 1 / ((x : ℚ) * q) + 1 / ((y : ℚ) * q) +
          1 / ((z : ℚ) * q) := by
        field_simp [hpQ, hqQ, hxQ, hyQ, hzQ]

/-- **Erdős #242, the Erdős–Straus conjecture (OPEN)**: every `n > 2`
    admits a decomposition.  Verified to 10¹⁸; falsifiable status in
    the DB.  Note this famous statement is also carried by upstream
    formal-conjectures projects — the repo's value-add is the Mordell
    layer below, not the headline. -/
theorem erdos_straus (n : ℕ) (hn : 2 < n) : ES n := by
  sorry

/-- Reduction to primes — classical and elementary: if `ES p` holds
    for every prime `p > 2`, then `ES n` holds for every `n > 2`
    (multiply a decomposition of `4/p` through by the cofactor;
    `4/(pm) = 1/(xm) + 1/(ym) + 1/(zm)` and the ordering is
    preserved... note n = 4k needs its own two-line identity — the
    composite case splits on the least prime factor; n = 4: 4/4 = 1 =
    1/2 + 1/3 + 1/6).  -- PROVABLE (target; effort S). -/
theorem es_of_es_primes (h : ∀ p : ℕ, p.Prime → 2 < p → ES p) :
    ∀ n : ℕ, 2 < n → ES n := by
  intro n hn
  have scale_divisor : ∀ p : ℕ, 0 < p → p ∣ n → ES p → ES n := by
    intro p hp hpn hep
    obtain ⟨q, hnq⟩ := hpn
    have hq : 0 < q := by
      by_contra hq
      have hqzero : q = 0 := by omega
      simp only [hqzero, Nat.mul_zero] at hnq
      omega
    rw [hnq]
    exact es_mul p q hp hq hep
  by_cases hfour : 4 ∣ n
  · exact scale_divisor 4 (by norm_num) hfour es_4
  · by_cases htwo : 2 ∣ n
    · obtain ⟨m, hnm⟩ := htwo
      have hm : m ≠ 1 := by omega
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm
      have hpne : p ≠ 2 := by
        intro hpeq
        obtain ⟨k, hmk⟩ := hpm
        apply hfour
        refine ⟨k, ?_⟩
        rw [hnm, hmk, hpeq]
        omega
      have hplt : 2 < p := by have hpge := hp.two_le; omega
      have hmn : m ∣ n := ⟨2, by omega⟩
      exact scale_divisor p (by omega) (Nat.dvd_trans hpm hmn) (h p hp hplt)
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      have hpne : p ≠ 2 := by
        intro hpeq
        exact htwo (hpeq ▸ hpn)
      have hplt : 2 < p := by have hpge := hp.two_le; omega
      exact scale_divisor p (by omega) hpn (h p hp hplt)

/-- A natural-number identity `4xyz = n(yz + xz + xy)` with `1 ≤ x < y < z`
    witnesses `ES n` (clear denominators in `4/n = 1/x + 1/y + 1/z`). -/
private theorem es_of_nat_identity (n x y z : ℕ) (hn : 0 < n) (hx : 1 ≤ x)
    (hxy : x < y) (hyz : y < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) : ES n := by
  refine ⟨x, y, z, hx, hxy, hyz, ?_⟩
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  have hQ : (4 : ℚ) * (x * y * z) = n * (y * z + x * z + x * y) := by exact_mod_cast h
  field_simp
  linear_combination hQ

/-- `n = 4k + 2` (`k ≥ 1`): `4/n = 1/(k+1) + 1/(c+1) + 1/(c(c+1))`
    with `c = (2k+1)(k+1)`. -/
private theorem es_four_mul_add_two (k : ℕ) (hk : 1 ≤ k) : ES (4 * k + 2) := by
  have hc : 6 ≤ (2 * k + 1) * (k + 1) := by nlinarith
  apply es_of_nat_identity _ (k + 1) ((2 * k + 1) * (k + 1) + 1)
    (((2 * k + 1) * (k + 1)) * ((2 * k + 1) * (k + 1) + 1))
  · omega
  · omega
  · nlinarith
  · nlinarith
  · ring

/-- `n = 4k + 3`: `4/n = 1/(k+1) + 1/(c+1) + 1/(c(c+1))` with `c = n(k+1)`. -/
private theorem es_four_mul_add_three (k : ℕ) : ES (4 * k + 3) := by
  have hc : 3 ≤ (4 * k + 3) * (k + 1) := by nlinarith
  apply es_of_nat_identity _ (k + 1) ((4 * k + 3) * (k + 1) + 1)
    (((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1))
  · omega
  · omega
  · nlinarith
  · nlinarith
  · ring

/-- `n = 8k + 5`: `4/n = 1/(2(k+1)) + 1/(n(k+1)) + 1/(2n(k+1))`. -/
private theorem es_eight_mul_add_five (k : ℕ) : ES (8 * k + 5) := by
  apply es_of_nat_identity _ (2 * (k + 1)) ((8 * k + 5) * (k + 1))
    (2 * ((8 * k + 5) * (k + 1)))
  · omega
  · omega
  · nlinarith
  · nlinarith
  · ring

/-- `n = 3k + 2` (`k ≥ 1`): `4/n = 1/(k+1) + 1/n + 1/(n(k+1))`. -/
private theorem es_three_mul_add_two (k : ℕ) (hk : 1 ≤ k) : ES (3 * k + 2) := by
  apply es_of_nat_identity _ (k + 1) (3 * k + 2) ((3 * k + 2) * (k + 1))
  · omega
  · omega
  · omega
  · nlinarith
  · ring

/-- `n = 120k + 97` (`n ≡ 2 mod 5`): `x = 32k + 26 = 2(2n+1)/15`,
    `4/n = 1/x + 1/(4n) + 1/(2nx)`. -/
private theorem es_120_mul_add_97 (k : ℕ) : ES (120 * k + 97) := by
  apply es_of_nat_identity _ (32 * k + 26) (4 * (120 * k + 97))
    (2 * (120 * k + 97) * (32 * k + 26))
  · omega
  · omega
  · omega
  · nlinarith
  · ring

/-- `n = 120k + 73` (`n ≡ 3 mod 5`): with `t = 3k + 2 = (n+7)/40`,
    `4/n = 1/(10t) + 1/(2nt) + 1/(5nt)`. -/
private theorem es_120_mul_add_73 (k : ℕ) : ES (120 * k + 73) := by
  apply es_of_nat_identity _ (10 * (3 * k + 2)) (2 * (120 * k + 73) * (3 * k + 2))
    (5 * (120 * k + 73) * (3 * k + 2))
  · omega
  · nlinarith
  · nlinarith
  · nlinarith
  · ring

/-- `n = 168k + 73` (`n ≡ 3 mod 7`): `x = 48k + 21 = (2n+1)/7`,
    `4/n = 1/x + 1/(2n) + 1/(2nx)`. -/
private theorem es_168_mul_add_73 (k : ℕ) : ES (168 * k + 73) := by
  apply es_of_nat_identity _ (48 * k + 21) (2 * (168 * k + 73))
    (2 * (168 * k + 73) * (48 * k + 21))
  · omega
  · omega
  · omega
  · nlinarith
  · ring

/-- `n = 168k + 97` (`n ≡ 6 mod 7`): `x = 48k + 28 = 2(n+1)/7`,
    `4/n = 1/x + 1/(2n) + 1/(nx)`. -/
private theorem es_168_mul_add_97 (k : ℕ) : ES (168 * k + 97) := by
  apply es_of_nat_identity _ (48 * k + 28) (2 * (168 * k + 97))
    ((168 * k + 97) * (48 * k + 28))
  · omega
  · omega
  · omega
  · nlinarith
  · ring

/-- `n = 168k + 145` (`n ≡ 5 mod 7`): with `t = k + 1 = (n+23)/168`,
    `4/n = 1/(42t) + 1/(2nt) + 1/(21nt)`. -/
private theorem es_168_mul_add_145 (k : ℕ) : ES (168 * k + 145) := by
  apply es_of_nat_identity _ (42 * (k + 1)) (2 * (168 * k + 145) * (k + 1))
    (21 * (168 * k + 145) * (k + 1))
  · omega
  · omega
  · nlinarith
  · nlinarith
  · ring

/-- Residues mod `5` split into five cases. -/
private theorem mod_five_cases (n : ℕ) :
    n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
  omega

/-- Residues mod `7` split into seven cases. -/
private theorem mod_seven_cases (n : ℕ) :
    n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨
      n % 7 = 6 := by
  omega

/-- CRT step: `n ≡ 1 (mod 24)` and `n ≡ a (mod 5)` fix `n mod 120`. -/
private theorem mod_120_of (n a r : ℕ) (h24 : n % 24 = 1) (ha : n % 5 = a)
    (hr : r % 24 = 1 ∧ r % 5 = a ∧ r < 120) : n % 120 = r := by
  omega

/-- CRT step: `n ≡ 1 (mod 24)` and `n ≡ b (mod 7)` fix `n mod 168`. -/
private theorem mod_168_of (n b r : ℕ) (h24 : n % 24 = 1) (hb : n % 7 = b)
    (hr : r % 24 = 1 ∧ r % 7 = b ∧ r < 168) : n % 168 = r := by
  omega

/-- CRT step: residues mod `24`, `5`, `7` fix `n mod 840`. -/
private theorem mod_840_of (n a b r : ℕ) (h24 : n % 24 = 1) (ha : n % 5 = a)
    (hb : n % 7 = b) (hr : r % 24 = 1 ∧ r % 5 = a ∧ r % 7 = b ∧ r < 840) :
    n % 840 = r := by
  omega

/-- Residual bookkeeping for Mordell's theorem: an `n ≡ 1 (mod 24)`
    coprime to `35` and outside the classes `73, 97 (mod 120)` and
    `73, 97, 145 (mod 168)` lies in one of the six square classes mod `840`. -/
private theorem mordell_residual (n : ℕ) (h24 : n % 24 = 1) (h5 : ¬ n % 5 = 0)
    (h7 : ¬ n % 7 = 0) (h97 : ¬ n % 120 = 97) (h73 : ¬ n % 120 = 73)
    (h73' : ¬ n % 168 = 73) (h97' : ¬ n % 168 = 97) (h145 : ¬ n % 168 = 145) :
    n % 840 = 1 ∨ n % 840 = 121 ∨ n % 840 = 169 ∨ n % 840 = 289 ∨
      n % 840 = 361 ∨ n % 840 = 529 := by
  rcases mod_five_cases n with ha | ha | ha | ha | ha
  · exact absurd ha h5
  · rcases mod_seven_cases n with hb | hb | hb | hb | hb | hb | hb
    · exact absurd hb h7
    · exact Or.inl (mod_840_of n 1 1 1 h24 ha hb (by norm_num))
    · exact Or.inr (Or.inl (mod_840_of n 1 2 121 h24 ha hb (by norm_num)))
    · exact absurd (mod_168_of n 3 73 h24 hb (by norm_num)) h73'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (mod_840_of n 1 4 361 h24 ha hb (by norm_num))))))
    · exact absurd (mod_168_of n 5 145 h24 hb (by norm_num)) h145
    · exact absurd (mod_168_of n 6 97 h24 hb (by norm_num)) h97'
  · exact absurd (mod_120_of n 2 97 h24 ha (by norm_num)) h97
  · exact absurd (mod_120_of n 3 73 h24 ha (by norm_num)) h73
  · rcases mod_seven_cases n with hb | hb | hb | hb | hb | hb | hb
    · exact absurd hb h7
    · exact Or.inr (Or.inr (Or.inl (mod_840_of n 4 1 169 h24 ha hb (by norm_num))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mod_840_of n 4 2 289 h24 ha hb (by norm_num)))))
    · exact absurd (mod_168_of n 3 73 h24 hb (by norm_num)) h73'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (mod_840_of n 4 4 529 h24 ha hb (by norm_num))))))
    · exact absurd (mod_168_of n 5 145 h24 hb (by norm_num)) h145
    · exact absurd (mod_168_of n 6 97 h24 hb (by norm_num)) h97'

/-- **Mordell's residue-class theorem (the Tier-UB target)**: if
    `n % 840 ∉ {1, 121, 169, 289, 361, 529}` and `2 < n`, then `ES n`.
    Fully elementary: a finite family of parametric identities, e.g.
    `n ≡ 2 (mod 3)`: 4/n = 1/n + 1/((n+1)/3) + 1/(n(n+1)/3), etc.;
    each congruence class gets an explicit polynomial witness triple,
    and `840 = 8·3·5·7` splits the classes.  Effort M (identity
    bookkeeping in ℚ; `norm_num`/`field_simp` leaves).  This is the
    slice Bloom explicitly recommends formalizing. -/
theorem mordell_classes (n : ℕ) (hn : 2 < n)
    (h : n % 840 ∉ ({1, 121, 169, 289, 361, 529} : Finset ℕ)) :
    ES n := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  have scale : ∀ p : ℕ, 0 < p → n % p = 0 → ES p → ES n := by
    intro p hp hpn hep
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hpn
    have hqpos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · simp only [hq0, Nat.mul_zero] at hq
        omega
      · exact hq0
    rw [hq]
    exact es_mul p q hp hqpos hep
  by_cases h4 : n % 4 = 0
  · exact scale 4 (by norm_num) h4 es_4
  by_cases h42 : n % 4 = 2
  · rw [show n = 4 * (n / 4) + 2 by omega]
    exact es_four_mul_add_two _ (by omega)
  by_cases h43 : n % 4 = 3
  · rw [show n = 4 * (n / 4) + 3 by omega]
    exact es_four_mul_add_three _
  by_cases h85 : n % 8 = 5
  · rw [show n = 8 * (n / 8) + 5 by omega]
    exact es_eight_mul_add_five _
  by_cases h3 : n % 3 = 0
  · exact scale 3 (by norm_num) h3 es_3
  by_cases h32 : n % 3 = 2
  · rw [show n = 3 * (n / 3) + 2 by omega]
    exact es_three_mul_add_two _ (by omega)
  by_cases h5 : n % 5 = 0
  · exact scale 5 (by norm_num) h5 es_5
  by_cases h7 : n % 7 = 0
  · exact scale 7 (by norm_num) h7 es_7
  by_cases h97 : n % 120 = 97
  · rw [show n = 120 * (n / 120) + 97 by omega]
    exact es_120_mul_add_97 _
  by_cases h73 : n % 120 = 73
  · rw [show n = 120 * (n / 120) + 73 by omega]
    exact es_120_mul_add_73 _
  by_cases h73' : n % 168 = 73
  · rw [show n = 168 * (n / 168) + 73 by omega]
    exact es_168_mul_add_73 _
  by_cases h97' : n % 168 = 97
  · rw [show n = 168 * (n / 168) + 97 by omega]
    exact es_168_mul_add_97 _
  by_cases h145 : n % 168 = 145
  · rw [show n = 168 * (n / 168) + 145 by omega]
    exact es_168_mul_add_145 _
  have h24 : n % 24 = 1 := by omega
  have hbad := mordell_residual n h24 h5 h7 h97 h73 h73' h97' h145
  obtain ⟨h1, h121, h169, h289, h361, h529⟩ := h
  rcases hbad with hr | hr | hr | hr | hr | hr
  · exact absurd hr h1
  · exact absurd hr h121
  · exact absurd hr h169
  · exact absurd hr h289
  · exact absurd hr h361
  · exact absurd hr h529

/-- Sanity: the six Mordell classes are the quadratic residues
    1², 11², 13², 17², 19², 23² reduced mod 840.
    -- PROVABLE (decide). -/
theorem mordell_residue_sanity : (121 : ℕ) = 11 ^ 2 % 840 ∧ (169 : ℕ) = 13 ^ 2 % 840 ∧
    (289 : ℕ) = 17 ^ 2 % 840 ∧ (361 : ℕ) = 19 ^ 2 % 840 ∧
    (529 : ℕ) = 23 ^ 2 % 840 := by
  decide

/-- Non-degeneracy of `ES`: `n = 1` fails — `4 = 1/x + 1/y + 1/z ≤ 3`
    is impossible; keeps the `2 < n` guard honest (n = 2: 2 = ... ≤
    1 + 1/2 + 1/3 < 2 also fails).  -- PROVABLE (bounding the three
    unit fractions).  -/
theorem es_small_nonexistence : ¬ ES 1 ∧ ¬ ES 2 := by
  have bound : ∀ n : ℕ, ES n → (4 : ℚ) / n ≤ 11 / 6 := by
    intro n hen
    obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := hen
    have hy : 2 ≤ y := by omega
    have hz : 3 ≤ z := by omega
    have hxQ : (1 : ℚ) ≤ x := by exact_mod_cast hx
    have hyQ : (2 : ℚ) ≤ y := by exact_mod_cast hy
    have hzQ : (3 : ℚ) ≤ z := by exact_mod_cast hz
    have bx : (1 : ℚ) / x ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) hxQ
    have byy : (1 : ℚ) / y ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hyQ
    have bz : (1 : ℚ) / z ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) hzQ
    rw [heq]
    calc
      (1 : ℚ) / x + 1 / y + 1 / z ≤ 1 / 1 + 1 / 2 + 1 / 3 :=
        add_le_add (add_le_add bx byy) bz
      _ = 11 / 6 := by norm_num
  constructor
  · intro h1
    have hb := bound 1 h1
    norm_num at hb
  · intro h2
    have hb := bound 2 h2
    norm_num at hb

end ErdosCandidates.E242

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch.
   - ES defined over Q with 1 <= x < y < z, matching the "distinct" requirement
     and the strict ordering from the source. Division-free encoding not needed
     since Q division is total.
   - Witnesses verified: 4/3=1/1+1/4+1/12, 4/5=1/2+1/4+1/20,
     4/7=1/2+1/15+1/210 — all confirmed by exact rational arithmetic.
   - Mordell classes {1,121,169,289,361,529} mod 840 verified:
     1^2=1, 11^2=121, 13^2=169, 17^2=289, 19^2=361, 23^2=529, all < 840.
   - mordell_classes stated for all n (not just primes) — matches DB sections
     which say "true for all n except those congruent to..." without prime
     restriction.
   - es_of_es_primes (reduction to primes) matches DB's "It suffices to prove
     this when n is prime."
   - Non-degeneracy (n=1,2) correctly argued: max unit-fraction sum < 4 and < 2.
   - Bloom's recommendation to formalize [BlEl22] equivalence noted; leochlon's
     repo correctly flagged as proving nothing beyond small checks.
-/
