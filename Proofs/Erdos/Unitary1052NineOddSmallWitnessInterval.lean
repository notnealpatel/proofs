import Erdos.Unitary1052NineOddSmallWitness
import Erdos.Unitary1052NineOddWitnessInterval

set_option autoImplicit false

namespace Erdos1052.NineOdd.SmallWitnessInterval

/-- In the ordinary nine-odd branch, no actual eleven-supplier component lies in
[373, 32769): small-witness forcing supplies actual19 and actual25, and the
independent interval kernel excludes the resulting actual-component identity. -/
theorem interval_exclusion (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a) (haEven : Even a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (hlarge : ∃ y ∈ P.image (fun p => p ^ e p), 32768 < y)
    (h3 : 3 ∈ P.image (fun p => p ^ e p))
    (h7 : 7 ∈ P.image (fun p => p ^ e p))
    (h11 : 11 ∈ P.image (fun p => p ^ e p))
    (h13 : 13 ∈ P.image (fun p => p ^ e p))
    (hn5 : 5 ∉ P.image (fun p => p ^ e p))
    (x : ℕ) (hx : x ∈ P.image (fun p => p ^ e p)) (hxlo : 373 ≤ x)
    (hxhi : x < 32769) (hx11 : 11 ∣ x + 1) : False := by
  have hxlo109 : 109 ≤ x := (by decide : 109 ≤ 373).trans hxlo
  obtain ⟨h19, h25⟩ := SmallWitness.actual19_and_actual25_of_small_witness
    a P e hc hp hp2 he ha haEven hid hlarge h3 h7 h11 h13 hn5
    x hx hxlo109 hxhi hx11
  have ho : ∀ p ∈ P, Odd p := by
    intro p hpm
    exact (hp p hpm).odd_of_ne_two (ne_of_gt (hp2 p hpm))
  have hidActual :
      (2 ^ a + 1) * (∏ y ∈ P.image (fun p => p ^ e p), (y + 1)) =
        2 ^ (a + 1) * ∏ y ∈ P.image (fun p => p ^ e p), y := by
    simpa only [Finset.prod_image (component_injOn P e hp he), Nat.pow_succ,
      mul_assoc, mul_left_comm, mul_comm] using hid
  exact WitnessInterval.interval_kernel a P e hc hp ho he ha haEven hidActual
    h3 h7 h11 h13 h19 h25 hn5 hlarge x hx hxlo hxhi hx11

end Erdos1052.NineOdd.SmallWitnessInterval
