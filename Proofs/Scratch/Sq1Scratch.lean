import Mathlib
import Xlib.TPP
import Xlib.CUCapacity
import Xlib.STPPWreath

open Xlib.STPPWreath Xlib.CUCapacity Xlib.TPP

-- Check: how to get n ≤ n!
-- For n ≥ 2, n! ≥ n since n! = n * (n-1)! ≥ n * 1 = n
#check Nat.lt_factorial_self  -- n < (n+2)!
-- Not quite. Let me look for self_le_factorial
#check Nat.self_le_factorial  -- ∀ n, n ≤ n.factorial? Let me check

-- Check: log_pow for Nat cast
-- log_pow : log (x ^ n) = n * log x
-- But I need: 3 * log(n!) = log((n!)^3)
-- The issue: `n` in `log_pow` is ℕ, so `↑n * log x`
-- I need to match `3 * log ...` with `↑3 * log ...`
-- Let me try norm_cast

-- Check: 1 ≤ Fintype.card
-- Fintype.card_pos gives 0 < Fintype.card
-- So Fintype.card ≥ 1 follows
#check @Fintype.card_pos -- 0 < Fintype.card α

-- Check Nat.self_le_factorial
example (n : ℕ) : n ≤ n.factorial := Nat.self_le_factorial n
