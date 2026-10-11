import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

namespace PrimePowerPolynomialRoots

/-- Canonical residues whose integer polynomial value vanishes modulo `m`. -/
noncomputable def residueRoots (P : Polynomial ℤ) (m : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun n => ((P.eval (n.val : ℤ) : ℤ) : ZMod m) = 0

example : residueRoots (Polynomial.C 1) 2 = ∅ := by
  classical
  ext n
  simp [residueRoots]

example : residueRoots (0 : Polynomial ℤ) 1 = Finset.univ := by
  classical
  simp [residueRoots]

/-- Reduction modulo a prime bounds the number of roots modulo its positive powers,
with the conservative penalty `p^(e-1)` and no nonsingularity assumption. -/
theorem card_residueRoots_le (p e d : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (P : Polynomial ℤ) (hP : P.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hd : (P.map (Int.castRingHom (ZMod p))).natDegree ≤ d) :
    (residueRoots P (p ^ e)).card ≤ d * p ^ (e - 1) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let f := P.map (Int.castRingHom (ZMod p))
  have hpow : p ^ e = p ^ (e - 1) * p := by
    conv_lhs => rw [← Nat.sub_add_cancel he, pow_succ]
  have hpdiv : p ∣ p ^ e := by rw [hpow]; exact dvd_mul_left p _
  let π : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
  have hreduce (n : Fin (p ^ e)) (hn : n ∈ residueRoots P (p ^ e)) :
      f.eval (n.val : ZMod p) = 0 := by
    have hz : ((P.eval (n.val : ℤ) : ℤ) : ZMod (p ^ e)) = 0 := by
      simpa [residueRoots] using hn
    have hz' := congrArg π hz
    rw [show f = P.map (Int.castRingHom (ZMod p)) from rfl,
      Polynomial.eval_natCast_map]
    change ((P.eval (n.val : ℤ) : ℤ) : ZMod p) = 0
    simpa only [map_intCast, map_zero] using hz'
  let target := f.roots.toFinset ×ˢ (Finset.univ : Finset (Fin (p ^ (e - 1))))
  let lift (n : Fin (p ^ e)) : ZMod p × Fin (p ^ (e - 1)) :=
    ((n.val : ZMod p), ⟨n.val / p, by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      simpa [hpow] using n.isLt⟩)
  have hmem (n : Fin (p ^ e)) (hn : n ∈ residueRoots P (p ^ e)) : lift n ∈ target := by
    simp only [target, lift, Finset.mem_product, Finset.mem_univ, and_true,
      Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hP).2 (hreduce n hn)
  have hinj : Set.InjOn lift (residueRoots P (p ^ e)) := by
    intro a ha b hb hab
    have hc := congrArg (fun x : ZMod p × Fin (p ^ (e - 1)) => x.1.val) hab
    have hq := congrArg (fun x : ZMod p × Fin (p ^ (e - 1)) => x.2.val) hab
    simp only [lift, ZMod.val_natCast] at hc hq
    apply Fin.ext
    have ha' := Nat.mod_add_div a.val p
    have hb' := Nat.mod_add_div b.val p
    rw [hc, hq] at ha'
    exact ha'.symm.trans hb'
  have hcard : (residueRoots P (p ^ e)).card ≤ target.card :=
    Finset.card_le_card_of_injOn lift hmem hinj
  have hroot : f.roots.toFinset.card ≤ d :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans hd)
  calc
    (residueRoots P (p ^ e)).card ≤ target.card := hcard
    _ = f.roots.toFinset.card * p ^ (e - 1) := by simp [target]
    _ ≤ d * p ^ (e - 1) := Nat.mul_le_mul_right _ hroot

example : Nat.Prime 2 ∧ 1 ≤ (1 : ℕ) ∧
    (Polynomial.C (1 : ℤ)).map (Int.castRingHom (ZMod 2)) ≠ 0 ∧
    ((Polynomial.C (1 : ℤ)).map (Int.castRingHom (ZMod 2))).natDegree ≤ 0 := by
  constructor
  · decide
  constructor
  · decide
  simp

end PrimePowerPolynomialRoots
