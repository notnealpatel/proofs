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
  sorry

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
