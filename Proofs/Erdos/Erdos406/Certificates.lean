/-
This module contains only the stable, kernel-checked bounded computation for
Erdős problem 406.  It is a certificate for exponents at most 200, not
evidence for, or a proof of, the open finiteness conjecture.
-/

import Erdos.Erdos406.Basic

set_option autoImplicit false

namespace Erdos406

/-- Bounded certificate: among exponents in `Finset.range 201`, exactly
`0`, `2`, and `8` give a power of two whose ternary digits are all zero or one.
This is checked by kernel reduction using `decide`; no native evaluator is
used. -/
theorem exponents_le_200_certificate :
    (Finset.range 201).filter (fun n => ZeroOneBase3 (2 ^ n)) = {0, 2, 8} := by
  decide

end Erdos406

#print axioms Erdos406.exponents_le_200_certificate
