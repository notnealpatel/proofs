import Sorry.Erdos.Unitary1052Transfer

set_option autoImplicit false

namespace Erdos1052

/-- For a base at least eleven and a positive component exponent, the transfer
lower bound and the explicit input `P < 705` force the exponent parameter to be one. -/
theorem component_exponent_eq_one_of_lower_bound (q c P : ℕ)
    (hq : 11 ≤ q) (hc : 0 < c) (hP : P < 705)
    (hbound : 2 * q ^ (2 * c) ≤ P + 1) : c = 1 := by
  by_contra hne
  have hexp : 4 ≤ 2 * c := by omega
  have hqpos : 0 < q := by omega
  have hpow : q ^ 4 ≤ q ^ (2 * c) := Nat.pow_le_pow_right hqpos hexp
  have hbase : 11 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have hlarge : 29282 ≤ 2 * q ^ (2 * c) := calc
    29282 = 2 * 11 ^ 4 := by norm_num
    _ ≤ 2 * q ^ (2 * c) := Nat.mul_le_mul_left 2 (hbase.trans hpow)
  have hupper : P + 1 ≤ 705 := by omega
  omega

/-- Under the unchanged conditional four-core identity, a square component at
base eleven or nineteen has exponent exactly two, provided the separate analytic
input `P < 705` holds. This theorem does not establish that analytic input. -/
theorem fixed_core_seed_exponent_eq_one {ι : Type*} (s : Finset ι)
    (q c : ι → ℕ) (a p e P : ℕ) (i : ι)
    (ha : Even a) (ha12 : 12 ≤ a) (hp : p.Prime) (hp13 : 13 < p)
    (hp24 : p % 24 = 1) (he : 0 < e) (heodd : Odd e) (hP : P = p ^ e)
    (hcomponents : ∀ j ∈ s, (q j).Prime ∧ Odd (q j) ∧
      q j ≠ 3 ∧ q j ≠ 5 ∧ q j ≠ 7 ∧ q j ≠ 13 ∧ q j ≠ p ∧ 0 < c j)
    (hdistinct : Set.InjOn q (↑s : Set ι))
    (hid : (2 ^ a + 1) * (P + 1) * (∏ j ∈ s, (q j ^ (2 * c j) + 1)) =
      2 ^ (a - 6) * 65 * P * (∏ j ∈ s, q j ^ (2 * c j)))
    (hi : i ∈ s) (hseed : q i = 11 ∨ q i = 19) (hsmall : P < 705) :
    c i = 1 := by
  have hmod : q i % 4 = 3 := by
    rcases hseed with h11 | h19
    · rw [h11]
    · rw [h19]
  have hbase : 11 ≤ q i := by
    rcases hseed with h11 | h19 <;> omega
  have hcpos : 0 < c i := by
    rcases hcomponents i hi with ⟨_hq, _hodd, _h3, _h5, _h7, _h13, _hp, hc⟩
    exact hc
  have htransfer := fixed_core_square_component_transfer s q c a p e P i
    ha ha12 hp hp13 hp24 he heodd hP hcomponents hdistinct hid hi hmod
  exact component_exponent_eq_one_of_lower_bound (q i) (c i) P hbase hcpos hsmall
    htransfer.2.2

-- A positive exponent-one model satisfies every generalized lower-bound premise.
example : 11 ≤ (11 : ℕ) ∧ 0 < (1 : ℕ) ∧ (241 : ℕ) < 705 ∧
    2 * (11 : ℕ) ^ (2 * 1) ≤ 241 + 1 := by decide

-- Exponent zero would satisfy the numerical bound but is explicitly excluded.
example : 2 * (11 : ℕ) ^ (2 * 0) ≤ 241 + 1 ∧ ¬ 0 < (0 : ℕ) := by decide

end Erdos1052
