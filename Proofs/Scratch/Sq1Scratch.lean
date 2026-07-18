import Mathlib

-- log(n+1) - 1 → atTop
-- = log(n+1) + (-1), with log(n+1) → atTop and (-1) → nhds(-1)

-- Step 1: (n+1 : ℝ) → atTop as n → atTop
-- Step 2: log ∘ above → atTop
-- Step 3: log(n+1) + (-1) → atTop

-- Let me try the full chain
example : Filter.Tendsto (fun n : ℕ => Real.log (↑n + 1) - 1)
    Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun n : ℕ => (↑n + 1 : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right _ 1
    exact Filter.tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log (↑n + 1 : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h1
  show Filter.Tendsto (fun n : ℕ => Real.log (↑n + 1) + (-1 : ℝ)) Filter.atTop Filter.atTop
  exact h2.atTop_add tendsto_const_nhds

-- Now: c / (log(n+1) - 1) → 0
example : Filter.Tendsto (fun n : ℕ => (1 + Real.log 2) / (Real.log (↑n + 1) - 1))
    Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun n : ℕ => Real.log (↑n + 1) - 1)
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => (↑n + 1 : ℝ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp h1).atTop_add tendsto_const_nhds
  exact tendsto_const_nhds.div_atTop this
