import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace SelfridgeLacampagne

set_option maxRecDepth 10000 in
/-- The first five column residues force the prefix `a,a,!a,!a,a`.
This is a finite ten-bit arithmetic check, independent of the later carry bridge. -/
theorem sparse_first_five_residue : ∀ a b c d e x y z u v : Bool,
    (4 * ((if x then 1 else 0) + 3 * (if y then 1 else 0) +
      9 * (if z then 1 else 0) + 27 * (if u then 1 else 0) + 81 * (if v then 1 else 0)) +
    16 * ((if a then 1 else 0) + 3 * (if b then 1 else 0) +
      9 * (if c then 1 else 0) + 27 * (if d then 1 else 0) + 81 * (if e then 1 else 0)) +
    5 : ℤ) % 243 = 0 → b = a ∧ c = !a ∧ d = !a ∧ e = a := by decide

example : ((4 * 37 + 16 * 36 + 5 : ℤ) % 243 = 0) ∧
    false = false ∧ true = !false ∧ true = !false ∧ false = false := by decide

end SelfridgeLacampagne
