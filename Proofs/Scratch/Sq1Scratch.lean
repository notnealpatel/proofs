import Mathlib
import Xlib.TPP
import Xlib.CUCapacity
import Xlib.STPPWreath

open Xlib.STPPWreath Xlib.CUCapacity

-- Check: can we get Nontrivial for wreathGroup (n+1)?
-- wreathGroup (n+1) = ImprimitiveWreathProduct (cyclicGroup (n+1)) (n+1)
-- = SemidirectProduct (Fin (n+1) -> cyclicGroup (n+1)) (Equiv.Perm (Fin (n+1))) _
-- |wreathGroup (n+1)| = (2(n+1))^(n+1) * (n+1)!

-- We need NeZero (2 * (n+1)) for the cyclicGroup to be proper
example (n : ℕ) : NeZero (2 * (n + 1)) := inferInstance

-- Check: Nontrivial (wreathGroup (n+1))?
-- Since |wreathGroup (n+1)| >= 2, the group is nontrivial
-- We can build this from Fintype.one_lt_card
#check @Fintype.one_lt_card_iff_nontrivial
#check ImprimitiveWreathProduct.card

-- Check the pseudoExponent definition
#check @pseudoExponent
-- pseudoExponent G = 3 * Real.log (Fintype.card G) / Real.log (tppCapacity G)

-- Check: the upper bound we want
-- pseudoExponent (wreathGroup n) ≤ Real.log ((2*n)^n * n!) / Real.log (n!)
-- = 3 * log|G| / log(beta) where beta >= (n!)^3
-- ≤ 3 * log|G| / log((n!)^3) = 3 * log|G| / (3 * log(n!)) = log|G| / log(n!)
-- = log((2n)^n * n!) / log(n!)

-- Key: pseudoExponent G = 3 * log|G| / log(beta)
--      beta >= (n!)^3  [from factorial_pow_three_le_tppCapacity]
--      so log(beta) >= log((n!)^3) = 3 * log(n!)
--      hence 3 * log|G| / log(beta) <= 3 * log|G| / (3 * log(n!)) = log|G| / log(n!)

-- This requires log(beta) > 0 and the division to be monotone decreasing

#check Real.log_le_log_of_le
#check div_le_div_of_nonneg_left
#check div_le_div_left
