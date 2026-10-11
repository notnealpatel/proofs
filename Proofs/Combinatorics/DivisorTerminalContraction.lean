import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

/-!
# Global divisor-terminal contraction

Choose one divisor successor at each nonterminal vertex. The collision contract
makes this map injective, and parity gives `2 * f p ≤ p + 1`. Its image omits the
maximum of the nonempty support. Comparing finite products of `p / (p - 1)` over
this proper image and the support gives strictness; cancellation yields the bound.
No perfect-number identity, primality assumption, or terminal-count theorem is
formalized here.
-/

set_option autoImplicit false

namespace DivisorTerminalContraction

/-- Vertices with no successor in `Q`, for the directed edge `p → q` given by `q ∣ p + 1`. -/
def terminals (Q : Finset ℕ) : Finset ℕ :=
  Q.filter (fun p => ∀ q ∈ Q, ¬ q ∣ p + 1)

/-- Membership in the terminal set is exactly membership with no outgoing divisor edge. -/
theorem mem_terminals (Q : Finset ℕ) (p : ℕ) :
    p ∈ terminals Q ↔ p ∈ Q ∧ ∀ q ∈ Q, ¬ q ∣ p + 1 := by
  simp [terminals]

example : terminals {7} = {7} := by norm_num [terminals]

private theorem twice_successor_le {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hd : q ∣ p + 1) : 2 * q ≤ p + 1 := by
  obtain ⟨k, hk⟩ := hd
  have he : Even (p + 1) := hp.add_odd (by decide)
  have hek : Even k := by
    rw [hk, Nat.even_mul] at he
    exact he.resolve_left (Nat.not_even_iff_odd.mpr hq)
  obtain ⟨a, ha⟩ := hek
  have hkpos : 0 < k := by
    by_contra hn
    have hz : k = 0 := by omega
    simp [hz] at hk
  have htwo : 2 ≤ k := by omega
  calc
    2 * q ≤ k * q := Nat.mul_le_mul_right q htwo
    _ = p + 1 := by simpa [Nat.mul_comm] using hk.symm

private theorem factor_bounds {p : ℕ} (hp : 3 ≤ p) :
    0 < ((p : ℝ) + 1) / ((p : ℝ) - 1) ∧
    1 < (p : ℝ) / ((p : ℝ) - 1) := by
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hp
  constructor
  · exact div_pos (by linarith) (by linarith)
  · apply (lt_div_iff₀ (by linarith : 0 < (p : ℝ) - 1)).mpr
    linarith

private theorem edge_factor_le {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hedge : 2 * q ≤ p + 1) :
    ((p : ℝ) + 1) / ((p : ℝ) - 1) ≤ (q : ℝ) / ((q : ℝ) - 1) := by
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have her : 2 * (q : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hedge
  apply (div_le_div_iff₀ (by linarith : 0 < (p : ℝ) - 1)
    (by linarith : 0 < (q : ℝ) - 1)).mpr
  nlinarith

private theorem mapping_contraction (Q D : Finset ℕ) (f : ℕ → ℕ)
    (hQ : Q.Nonempty) (hD : D ⊆ Q) (hb : ∀ p ∈ Q, 3 ≤ p)
    (hf : ∀ p ∈ D, f p ∈ Q) (hi : Set.InjOn f D)
    (he : ∀ p ∈ D, 2 * f p ≤ p + 1) :
    (∏ p ∈ Q, (1 + 1 / (p : ℝ))) <
      ∏ p ∈ Q \ D, ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
  classical
  let F : ℕ → ℝ := fun p => ((p : ℝ) + 1) / ((p : ℝ) - 1)
  let G : ℕ → ℝ := fun p => (p : ℝ) / ((p : ℝ) - 1)
  let I := D.image f
  have hI : I ⊆ Q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact hf p hp
  have hmax : Q.max' hQ ∉ I := by
    intro hm
    obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp hm
    have hpmax : p ≤ Q.max' hQ := Finset.le_max' Q p (hD hp)
    have hmaxb := hb (Q.max' hQ) (Finset.max'_mem Q hQ)
    have hedge := he p hp
    rw [hfp] at hedge
    omega
  have hG (p : ℕ) (hp : p ∈ Q) : 1 < G p := (factor_bounds (hb p hp)).2
  have hGpos (p : ℕ) (hp : p ∈ Q) : 0 < G p := lt_trans zero_lt_one (hG p hp)
  have hFpos (p : ℕ) (hp : p ∈ Q) : 0 < F p := (factor_bounds (hb p hp)).1
  have hmissing : 1 < ∏ p ∈ Q \ I, G p := by
    have hlt := Finset.prod_lt_prod
      (s := Q \ I) (f := fun _ => (1 : ℝ)) (g := G)
      (fun _ _ => zero_lt_one)
      (fun p hp => (hG p (Finset.mem_sdiff.mp hp).1).le)
      ⟨Q.max' hQ, Finset.mem_sdiff.mpr ⟨Finset.max'_mem Q hQ, hmax⟩,
        hG (Q.max' hQ) (Finset.max'_mem Q hQ)⟩
    simpa using hlt
  have hIpos : 0 < ∏ p ∈ I, G p := Finset.prod_pos (fun p hp => hGpos p (hI hp))
  have hstrict : (∏ p ∈ I, G p) < ∏ p ∈ Q, G p := by
    rw [← Finset.prod_sdiff hI]
    nlinarith
  have hbound : (∏ p ∈ D, F p) ≤ ∏ p ∈ I, G p := by
    rw [Finset.prod_image hi]
    exact Finset.prod_le_prod
      (fun p hp => (hFpos p (hD hp)).le)
      (fun p hp => edge_factor_le (hb p (hD hp)) (hb (f p) (hf p hp)) (he p hp))
  have hLpos : 0 < ∏ p ∈ Q \ D, F p :=
    Finset.prod_pos (fun p hp => hFpos p (Finset.mem_sdiff.mp hp).1)
  have htotal : (∏ p ∈ Q, F p) < (∏ p ∈ Q \ D, F p) * ∏ p ∈ Q, G p := by
    rw [← Finset.prod_sdiff hD]
    exact mul_lt_mul_of_pos_left (lt_of_le_of_lt hbound hstrict) hLpos
  have hfactor : (∏ p ∈ Q, F p) =
      (∏ p ∈ Q, (1 + 1 / (p : ℝ))) * ∏ p ∈ Q, G p := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hb p hp
    dsimp [F, G]
    field_simp
  rw [hfactor] at htotal
  exact lt_of_mul_lt_mul_right htotal
    (Finset.prod_pos (fun p hp => hGpos p hp)).le

/-- A nonempty odd support with unique incoming divisor edges has its reciprocal
product strictly bounded by the product of its terminal factors. This is a global
conditional combinatorial contraction, not a perfect-number existence assertion. -/
theorem prod_lt_prod_terminals (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hodd : ∀ p ∈ Q, Odd p ∧ 3 ≤ p)
    (hcapacity : ∀ p₁ ∈ Q, ∀ p₂ ∈ Q, ∀ q ∈ Q,
      q ∣ p₁ + 1 → q ∣ p₂ + 1 → p₁ = p₂) :
    (∏ p ∈ Q, (1 + 1 / (p : ℝ))) <
      ∏ p ∈ terminals Q, ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
  classical
  let D := Q \ terminals Q
  have hD : D ⊆ Q := Finset.sdiff_subset
  have hex (p : ℕ) : ∃ q : ℕ, p ∈ D → q ∈ Q ∧ q ∣ p + 1 := by
    by_cases hp : p ∈ D
    · have hn : ¬ ∀ q ∈ Q, ¬ q ∣ p + 1 := by
        intro ht
        exact (Finset.mem_sdiff.mp hp).2 ((mem_terminals Q p).mpr ⟨hD hp, ht⟩)
      push Not at hn
      obtain ⟨q, hq, hd⟩ := hn
      exact ⟨q, fun _ => ⟨hq, hd⟩⟩
    · exact ⟨0, fun hp' => False.elim (hp hp')⟩
  let f : ℕ → ℕ := fun p => Classical.choose (hex p)
  have hf (p : ℕ) (hp : p ∈ D) : f p ∈ Q ∧ f p ∣ p + 1 :=
    Classical.choose_spec (hex p) hp
  have hi : Set.InjOn f D := by
    intro p₁ hp₁ p₂ hp₂ heq
    apply hcapacity p₁ (hD hp₁) p₂ (hD hp₂) (f p₁) (hf p₁ hp₁).1
      (hf p₁ hp₁).2
    rw [heq]
    exact (hf p₂ hp₂).2
  have he (p : ℕ) (hp : p ∈ D) : 2 * f p ≤ p + 1 :=
    twice_successor_le (hodd p (hD hp)).1 (hodd (f p) (hf p hp).1).1 (hf p hp).2
  have hleaves : Q \ D = terminals Q := by
    ext p
    have ht : p ∈ terminals Q → p ∈ Q := fun hp => ((mem_terminals Q p).mp hp).1
    simp only [D, Finset.mem_sdiff]
    tauto
  have hresult := mapping_contraction Q D f hQ hD (fun p hp => (hodd p hp).2)
    (fun p hp => (hf p hp).1) hi he
  rwa [hleaves] at hresult

example : (∏ p ∈ ({7} : Finset ℕ), (1 + 1 / (p : ℝ))) <
    ∏ p ∈ terminals {7}, ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
  apply prod_lt_prod_terminals
  · simp
  · intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    norm_num
  · intro p₁ hp₁ p₂ hp₂ q hq _ _
    simp only [Finset.mem_singleton] at hp₁ hp₂
    exact hp₁.trans hp₂.symm

end DivisorTerminalContraction
