import Sorry.Combinatorics.SelfridgeLacampagneFamilyCarries
import Sorry.Combinatorics.SelfridgeLacampagneFamily

set_option autoImplicit false

namespace SelfridgeLacampagne

/-- For every odd `m ≥ 5`, positive zero-free balanced ternary values cannot have ratio `3^m+4`. -/
theorem btVal_ne_three_pow_add_four_mul (L M : List Bool) (m : ℕ) (hm : 5 ≤ m)
    (hodd : Odd m) (hp : 0 < btVal L) :
    btVal M ≠ ((3 : ℤ) ^ m + 4) * btVal L := by
  intro heq
  obtain ⟨U, _, _, henc⟩ := btVal_sparse_encoding L M m (by omega) hodd hp heq
  let s : ℕ → Bool := fun i => (L.map Bool.not).getD i false
  have hfirst := sparse_encoding_first_five L U m hm henc
  have hprefix : binaryWindow s 0 5 = [s 0, s 0, !(s 0), !(s 0), s 0] := by
    change [s 0, s 1, s 2, s 3, s 4] = _
    change s 1 = s 0 ∧ s 2 = !(s 0) ∧ s 3 = !(s 0) ∧ s 4 = s 0 at hfirst
    rw [hfirst.1, hfirst.2.1, hfirst.2.2.1, hfirst.2.2.2]
  exact no_binary_terminal_window_of_first_five s (L.length - m) m hm (s 0) hprefix
    (fun i hi => sparse_encoding_nae L U m hm hodd henc i hi)
    (sparse_encoding_terminal L U m
      (by have hn := sparse_encoding_length_lower L U m hm henc; omega) henc)

/-- Every odd exponent at least five gives a genuine, unbounded Selfridge–Lacampagne counterexample. -/
theorem isSLCounterexample_three_pow_add_four (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) :
    IsSLCounterexample (3 ^ m + 4) := by
  refine ⟨by positivity, ?_, ?_⟩
  · intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hpow : (3 : ℕ) ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [hpow] at hz
    omega
  · rintro ⟨a, b, ⟨M, _, hvM⟩, ⟨L, hL, hvL⟩, hab⟩
    have hne := btVal_ne_zero L hL
    have hp : 0 < btVal L := by omega
    apply btVal_ne_three_pow_add_four_mul L M m hm hodd hp
    rw [hvM, hvL, hab]
    push_cast
    ring

/-- There are infinitely many positive Selfridge–Lacampagne counterexamples. -/
theorem slCounterexamples_infinite : {k : ℕ | IsSLCounterexample k}.Infinite := by
  have hinj : Function.Injective (fun t : ℕ => 3 ^ (2 * t + 5) + 4) := by
    intro t u h
    change 3 ^ (2 * t + 5) + 4 = 3 ^ (2 * u + 5) + 4 at h
    have hp : (3 : ℕ) ^ (2 * t + 5) = 3 ^ (2 * u + 5) := by omega
    have he := Nat.pow_right_injective (by decide : 2 ≤ (3 : ℕ)) hp
    omega
  apply Set.infinite_of_injective_forall_mem hinj
  intro t
  exact isSLCounterexample_three_pow_add_four (2 * t + 5) (by omega)
    ⟨t + 2, by omega⟩

example : 5 ≤ (5 : ℕ) ∧ Odd (5 : ℕ) := by decide

end SelfridgeLacampagne
