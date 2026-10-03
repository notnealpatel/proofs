import Erdos.Erdos64.SubcubicFunnelH7

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Erdos64.SubcubicFunnel.PackingCertificate

/-- The row-major cross-identification bit of two seven-vertex copies. -/
def bit (m : BitVec 49) (i j : Fin 7) : Prop :=
  m.getLsbD (7 * i.val + j.val) = true

example : bit (8 : BitVec 49) 0 3 := by unfold bit; decide
example : ¬ bit (8 : BitVec 49) 0 2 := by unfold bit; decide

/-- Necessary local constraints for two induced copies in a subcubic graph:
partial injectivity, inducedness, saturation, and intersection of two pairs
of neighbors when neither matched vertex is saturated. -/
def Valid (m : BitVec 49) : Prop :=
  (∀ i j k, bit m i j → bit m i k → j = k) ∧
  (∀ i j k, bit m i j → bit m k j → i = k) ∧
  (∀ i k, h7.Adj i k → ∀ j l, bit m i j → bit m k l → h7.Adj j l) ∧
  (∀ i, (i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6) → ∀ j, bit m i j →
    ∀ l, h7.Adj j l → ∃ k, h7.Adj i k ∧ bit m k l) ∧
  (∀ j, (j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6) → ∀ i, bit m i j →
    ∀ k, h7.Adj i k → ∃ l, h7.Adj j l ∧ bit m k l) ∧
  (∀ i j, bit m i j →
    (i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6) ∨
    (j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6) ∨
    ∃ k l, h7.Adj i k ∧ h7.Adj j l ∧ bit m k l)

example : Valid 0 := by
  simp [Valid, bit]

private theorem adj_0 (k : Fin 7) : h7.Adj 0 k ↔ k = 2 ∨ k = 3 := by fin_cases k <;> decide

private theorem adj_1 (k : Fin 7) : h7.Adj 1 k ↔ k = 5 ∨ k = 6 := by fin_cases k <;> decide

private theorem adj_2 (k : Fin 7) : h7.Adj 2 k ↔ k = 0 ∨ k = 3 ∨ k = 4 := by fin_cases k <;> decide

private theorem adj_3 (k : Fin 7) : h7.Adj 3 k ↔ k = 0 ∨ k = 2 ∨ k = 6 := by fin_cases k <;> decide

private theorem adj_4 (k : Fin 7) : h7.Adj 4 k ↔ k = 2 ∨ k = 5 := by fin_cases k <;> decide

private theorem adj_5 (k : Fin 7) : h7.Adj 5 k ↔ k = 1 ∨ k = 4 ∨ k = 6 := by fin_cases k <;> decide

private theorem adj_6 (k : Fin 7) : h7.Adj 6 k ↔ k = 1 ∨ k = 3 ∨ k = 5 := by fin_cases k <;> decide

/-- A kernel-checked propositional classification of the local identification
problem. There are one empty, four four-vertex, two six-vertex, and two full
identifications. No cycle exclusion is used in this computation. -/
theorem classify (m : BitVec 49) (h : Valid m) :
    m = 0 ∨ m = 4297129992 ∨ m = 4299685952 ∨
    m = 4539780432896 ∨ m = 9899899625472 ∨
    m = 281543712985092 ∨ m = 35218866078240 ∨
    m = 282578800148737 ∨ m = 35326240751746 := by
  rcases h with ⟨hr,hc,he,hs,ht,hd⟩
  have c2 : m.getLsbD 0 = true → m.getLsbD 2 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hr 0 0 2 ha hb)
  have c5 : m.getLsbD 0 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hc 0 0 3 ha hb)
  have c7 : m.getLsbD 0 = true → m.getLsbD 28 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hc 0 0 4 ha hb)
  have c15 : m.getLsbD 7 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hc 1 0 3 ha hb)
  have c18 : m.getLsbD 1 = true → m.getLsbD 5 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hr 0 1 5 ha hb)
  have c19 : m.getLsbD 7 = true → m.getLsbD 35 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hc 1 0 5 ha hb)
  have c20 : m.getLsbD 1 = true → m.getLsbD 6 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hr 0 1 6 ha hb)
  have c21 : m.getLsbD 7 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hc 1 0 6 ha hb)
  have c23 : m.getLsbD 14 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hc 2 0 3 ha hb)
  have c27 : m.getLsbD 14 = true → m.getLsbD 35 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hc 2 0 5 ha hb)
  have c29 : m.getLsbD 14 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hc 2 0 6 ha hb)
  have c31 : m.getLsbD 21 = true → m.getLsbD 28 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hc 3 0 4 ha hb)
  have c33 : m.getLsbD 21 = true → m.getLsbD 35 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hc 3 0 5 ha hb)
  have c35 : m.getLsbD 21 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 6) (hc 3 0 6 ha hb)
  have c38 : m.getLsbD 4 = true → m.getLsbD 6 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hr 0 4 6 ha hb)
  have c39 : m.getLsbD 28 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hc 4 0 6 ha hb)
  have c40 : m.getLsbD 5 = true → m.getLsbD 6 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hr 0 5 6 ha hb)
  have c41 : m.getLsbD 35 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hc 5 0 6 ha hb)
  have c47 : m.getLsbD 1 = true → m.getLsbD 22 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hc 0 1 3 ha hb)
  have c49 : m.getLsbD 1 = true → m.getLsbD 29 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hc 0 1 4 ha hb)
  have c51 : m.getLsbD 1 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hc 0 1 5 ha hb)
  have c60 : m.getLsbD 8 = true → m.getLsbD 12 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hr 1 1 5 ha hb)
  have c61 : m.getLsbD 8 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hc 1 1 5 ha hb)
  have c63 : m.getLsbD 8 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hc 1 1 6 ha hb)
  have c69 : m.getLsbD 15 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hc 2 1 5 ha hb)
  have c72 : m.getLsbD 10 = true → m.getLsbD 11 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hr 1 3 4 ha hb)
  have c73 : m.getLsbD 22 = true → m.getLsbD 29 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hc 3 1 4 ha hb)
  have c75 : m.getLsbD 22 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hc 3 1 5 ha hb)
  have c79 : m.getLsbD 29 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hc 4 1 5 ha hb)
  have c81 : m.getLsbD 29 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hc 4 1 6 ha hb)
  have c83 : m.getLsbD 36 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hc 5 1 6 ha hb)
  have c84 : m.getLsbD 14 = true → m.getLsbD 15 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 1) (hr 2 0 1 ha hb)
  have c86 : m.getLsbD 14 = true → m.getLsbD 16 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hr 2 0 2 ha hb)
  have c87 : m.getLsbD 2 = true → m.getLsbD 16 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hc 0 2 2 ha hb)
  have c89 : m.getLsbD 2 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hc 0 2 3 ha hb)
  have c90 : m.getLsbD 14 = true → m.getLsbD 18 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hr 2 0 4 ha hb)
  have c92 : m.getLsbD 14 = true → m.getLsbD 19 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hr 2 0 5 ha hb)
  have c93 : m.getLsbD 2 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hc 0 2 5 ha hb)
  have c94 : m.getLsbD 14 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hr 2 0 6 ha hb)
  have c95 : m.getLsbD 2 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hc 0 2 6 ha hb)
  have c96 : m.getLsbD 15 = true → m.getLsbD 16 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 2) (hr 2 1 2 ha hb)
  have c97 : m.getLsbD 9 = true → m.getLsbD 16 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 2) (hc 1 2 2 ha hb)
  have c99 : m.getLsbD 9 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hc 1 2 3 ha hb)
  have c100 : m.getLsbD 15 = true → m.getLsbD 18 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 4) (hr 2 1 4 ha hb)
  have c102 : m.getLsbD 15 = true → m.getLsbD 19 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hr 2 1 5 ha hb)
  have c103 : m.getLsbD 9 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hc 1 2 5 ha hb)
  have c104 : m.getLsbD 15 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hr 2 1 6 ha hb)
  have c105 : m.getLsbD 9 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hc 1 2 6 ha hb)
  have c107 : m.getLsbD 16 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hc 2 2 3 ha hb)
  have c108 : m.getLsbD 16 = true → m.getLsbD 18 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 4) (hr 2 2 4 ha hb)
  have c109 : m.getLsbD 16 = true → m.getLsbD 30 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 4) (hc 2 2 4 ha hb)
  have c110 : m.getLsbD 16 = true → m.getLsbD 19 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hr 2 2 5 ha hb)
  have c111 : m.getLsbD 16 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hc 2 2 5 ha hb)
  have c112 : m.getLsbD 16 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hr 2 2 6 ha hb)
  have c113 : m.getLsbD 16 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hc 2 2 6 ha hb)
  have c115 : m.getLsbD 23 = true → m.getLsbD 30 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hc 3 2 4 ha hb)
  have c117 : m.getLsbD 23 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hc 3 2 5 ha hb)
  have c119 : m.getLsbD 23 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 6) (hc 3 2 6 ha hb)
  have c120 : m.getLsbD 18 = true → m.getLsbD 19 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hr 2 4 5 ha hb)
  have c121 : m.getLsbD 30 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hc 4 2 5 ha hb)
  have c122 : m.getLsbD 18 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hr 2 4 6 ha hb)
  have c123 : m.getLsbD 30 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hc 4 2 6 ha hb)
  have c124 : m.getLsbD 19 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hr 2 5 6 ha hb)
  have c125 : m.getLsbD 37 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hc 5 2 6 ha hb)
  have c126 : m.getLsbD 21 = true → m.getLsbD 22 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 1) (hr 3 0 1 ha hb)
  have c128 : m.getLsbD 21 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hr 3 0 2 ha hb)
  have c130 : m.getLsbD 21 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hr 3 0 3 ha hb)
  have c131 : m.getLsbD 3 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hc 0 3 3 ha hb)
  have c132 : m.getLsbD 21 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hr 3 0 4 ha hb)
  have c133 : m.getLsbD 3 = true → m.getLsbD 31 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hc 0 3 4 ha hb)
  have c134 : m.getLsbD 21 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hr 3 0 5 ha hb)
  have c135 : m.getLsbD 3 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hc 0 3 5 ha hb)
  have c136 : m.getLsbD 21 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hr 3 0 6 ha hb)
  have c138 : m.getLsbD 22 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 2) (hr 3 1 2 ha hb)
  have c140 : m.getLsbD 22 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hr 3 1 3 ha hb)
  have c141 : m.getLsbD 10 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hc 1 3 3 ha hb)
  have c142 : m.getLsbD 22 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 4) (hr 3 1 4 ha hb)
  have c143 : m.getLsbD 10 = true → m.getLsbD 31 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 4) (hc 1 3 4 ha hb)
  have c144 : m.getLsbD 22 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hr 3 1 5 ha hb)
  have c145 : m.getLsbD 10 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hc 1 3 5 ha hb)
  have c146 : m.getLsbD 22 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hr 3 1 6 ha hb)
  have c148 : m.getLsbD 23 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hr 3 2 3 ha hb)
  have c149 : m.getLsbD 17 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hc 2 3 3 ha hb)
  have c150 : m.getLsbD 23 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 4) (hr 3 2 4 ha hb)
  have c152 : m.getLsbD 23 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hr 3 2 5 ha hb)
  have c153 : m.getLsbD 17 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hc 2 3 5 ha hb)
  have c154 : m.getLsbD 23 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hr 3 2 6 ha hb)
  have c156 : m.getLsbD 24 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hr 3 3 4 ha hb)
  have c157 : m.getLsbD 24 = true → m.getLsbD 31 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hc 3 3 4 ha hb)
  have c158 : m.getLsbD 24 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hr 3 3 5 ha hb)
  have c159 : m.getLsbD 24 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hc 3 3 5 ha hb)
  have c160 : m.getLsbD 24 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 6) (hr 3 3 6 ha hb)
  have c161 : m.getLsbD 24 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 6) (hc 3 3 6 ha hb)
  have c162 : m.getLsbD 25 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hr 3 4 5 ha hb)
  have c163 : m.getLsbD 31 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hc 4 3 5 ha hb)
  have c164 : m.getLsbD 25 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hr 3 4 6 ha hb)
  have c166 : m.getLsbD 26 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hr 3 5 6 ha hb)
  have c167 : m.getLsbD 38 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hc 5 3 6 ha hb)
  have c173 : m.getLsbD 4 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hc 0 4 3 ha hb)
  have c178 : m.getLsbD 28 = true → m.getLsbD 34 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hr 4 0 6 ha hb)
  have c179 : m.getLsbD 4 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hc 0 4 6 ha hb)
  have c182 : m.getLsbD 29 = true → m.getLsbD 31 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hr 4 1 3 ha hb)
  have c189 : m.getLsbD 11 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hc 1 4 6 ha hb)
  have c191 : m.getLsbD 18 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hc 2 4 3 ha hb)
  have c195 : m.getLsbD 18 = true → m.getLsbD 39 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hc 2 4 5 ha hb)
  have c196 : m.getLsbD 30 = true → m.getLsbD 34 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hr 4 2 6 ha hb)
  have c197 : m.getLsbD 18 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hc 2 4 6 ha hb)
  have c200 : m.getLsbD 31 = true → m.getLsbD 33 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hr 4 3 5 ha hb)
  have c201 : m.getLsbD 25 = true → m.getLsbD 39 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hc 3 4 5 ha hb)
  have c207 : m.getLsbD 32 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hc 4 4 6 ha hb)
  have c209 : m.getLsbD 39 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hc 5 4 6 ha hb)
  have c210 : m.getLsbD 35 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 1) (hr 5 0 1 ha hb)
  have c211 : m.getLsbD 5 = true → m.getLsbD 12 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 1) (hc 0 5 1 ha hb)
  have c212 : m.getLsbD 35 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hr 5 0 2 ha hb)
  have c213 : m.getLsbD 5 = true → m.getLsbD 19 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hc 0 5 2 ha hb)
  have c214 : m.getLsbD 35 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hr 5 0 3 ha hb)
  have c215 : m.getLsbD 5 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hc 0 5 3 ha hb)
  have c216 : m.getLsbD 35 = true → m.getLsbD 39 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hr 5 0 4 ha hb)
  have c217 : m.getLsbD 5 = true → m.getLsbD 33 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hc 0 5 4 ha hb)
  have c218 : m.getLsbD 35 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hr 5 0 5 ha hb)
  have c219 : m.getLsbD 5 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hc 0 5 5 ha hb)
  have c220 : m.getLsbD 35 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hr 5 0 6 ha hb)
  have c221 : m.getLsbD 5 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hc 0 5 6 ha hb)
  have c222 : m.getLsbD 36 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 2) (hr 5 1 2 ha hb)
  have c223 : m.getLsbD 12 = true → m.getLsbD 19 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 2) (hc 1 5 2 ha hb)
  have c224 : m.getLsbD 36 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hr 5 1 3 ha hb)
  have c225 : m.getLsbD 12 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hc 1 5 3 ha hb)
  have c226 : m.getLsbD 36 = true → m.getLsbD 39 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 4) (hr 5 1 4 ha hb)
  have c228 : m.getLsbD 36 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hr 5 1 5 ha hb)
  have c229 : m.getLsbD 12 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hc 1 5 5 ha hb)
  have c230 : m.getLsbD 36 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 6) (hr 5 1 6 ha hb)
  have c232 : m.getLsbD 37 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hr 5 2 3 ha hb)
  have c233 : m.getLsbD 19 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hc 2 5 3 ha hb)
  have c234 : m.getLsbD 37 = true → m.getLsbD 39 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 4) (hr 5 2 4 ha hb)
  have c235 : m.getLsbD 19 = true → m.getLsbD 33 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 4) (hc 2 5 4 ha hb)
  have c236 : m.getLsbD 37 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hr 5 2 5 ha hb)
  have c237 : m.getLsbD 19 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hc 2 5 5 ha hb)
  have c238 : m.getLsbD 37 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hr 5 2 6 ha hb)
  have c240 : m.getLsbD 38 = true → m.getLsbD 39 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hr 5 3 4 ha hb)
  have c241 : m.getLsbD 26 = true → m.getLsbD 33 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hc 3 5 4 ha hb)
  have c242 : m.getLsbD 38 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hr 5 3 5 ha hb)
  have c243 : m.getLsbD 26 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hc 3 5 5 ha hb)
  have c244 : m.getLsbD 38 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 6) (hr 5 3 6 ha hb)
  have c245 : m.getLsbD 26 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 6) (hc 3 5 6 ha hb)
  have c246 : m.getLsbD 39 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hr 5 4 5 ha hb)
  have c247 : m.getLsbD 33 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hc 4 5 5 ha hb)
  have c248 : m.getLsbD 39 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hr 5 4 6 ha hb)
  have c249 : m.getLsbD 33 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 6) (hc 4 5 6 ha hb)
  have c250 : m.getLsbD 40 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hr 5 5 6 ha hb)
  have c251 : m.getLsbD 40 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hc 5 5 6 ha hb)
  have c254 : m.getLsbD 42 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hr 6 0 2 ha hb)
  have c255 : m.getLsbD 6 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 2) (hc 0 6 2 ha hb)
  have c257 : m.getLsbD 6 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 3) (hc 0 6 3 ha hb)
  have c258 : m.getLsbD 42 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hr 6 0 4 ha hb)
  have c259 : m.getLsbD 6 = true → m.getLsbD 34 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 4) (hc 0 6 4 ha hb)
  have c261 : m.getLsbD 6 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 5) (hc 0 6 5 ha hb)
  have c262 : m.getLsbD 42 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : (0 : Fin 7) ≠ 6) (hr 6 0 6 ha hb)
  have c266 : m.getLsbD 43 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hr 6 1 3 ha hb)
  have c267 : m.getLsbD 13 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 3) (hc 1 6 3 ha hb)
  have c271 : m.getLsbD 13 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (1 : Fin 7) ≠ 5) (hc 1 6 5 ha hb)
  have c275 : m.getLsbD 20 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 3) (hc 2 6 3 ha hb)
  have c276 : m.getLsbD 44 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 4) (hr 6 2 4 ha hb)
  have c279 : m.getLsbD 20 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 5) (hc 2 6 5 ha hb)
  have c280 : m.getLsbD 44 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : (2 : Fin 7) ≠ 6) (hr 6 2 6 ha hb)
  have c283 : m.getLsbD 27 = true → m.getLsbD 34 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 4) (hc 3 6 4 ha hb)
  have c284 : m.getLsbD 45 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hr 6 3 5 ha hb)
  have c285 : m.getLsbD 27 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 5) (hc 3 6 5 ha hb)
  have c287 : m.getLsbD 27 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : (3 : Fin 7) ≠ 6) (hc 3 6 6 ha hb)
  have c289 : m.getLsbD 34 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : (4 : Fin 7) ≠ 5) (hc 4 6 5 ha hb)
  have c293 : m.getLsbD 41 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : (5 : Fin 7) ≠ 6) (hc 5 6 6 ha hb)
  have c301 : m.getLsbD 1 = true → m.getLsbD 16 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 2) (he 0 2 (by decide) 1 2 ha hb)
  have c306 : m.getLsbD 2 = true → m.getLsbD 19 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 0 2 (by decide) 2 5 ha hb)
  have c307 : m.getLsbD 2 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 0 2 (by decide) 2 6 ha hb)
  have c316 : m.getLsbD 4 = true → m.getLsbD 20 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 0 2 (by decide) 4 6 ha hb)
  have c317 : m.getLsbD 5 = true → m.getLsbD 14 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 0 2 (by decide) 5 0 ha hb)
  have c318 : m.getLsbD 5 = true → m.getLsbD 16 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 0 2 (by decide) 5 2 ha hb)
  have c321 : m.getLsbD 6 = true → m.getLsbD 14 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 0) (he 0 2 (by decide) 6 0 ha hb)
  have c322 : m.getLsbD 6 = true → m.getLsbD 16 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 0 2 (by decide) 6 2 ha hb)
  have c323 : m.getLsbD 6 = true → m.getLsbD 18 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 4) (he 0 2 (by decide) 6 4 ha hb)
  have c327 : m.getLsbD 0 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 4) (he 0 3 (by decide) 0 4 ha hb)
  have c328 : m.getLsbD 0 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 5) (he 0 3 (by decide) 0 5 ha hb)
  have c329 : m.getLsbD 0 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 6) (he 0 3 (by decide) 0 6 ha hb)
  have c330 : m.getLsbD 1 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 0) (he 0 3 (by decide) 1 0 ha hb)
  have c332 : m.getLsbD 1 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 2) (he 0 3 (by decide) 1 2 ha hb)
  have c333 : m.getLsbD 1 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 3) (he 0 3 (by decide) 1 3 ha hb)
  have c334 : m.getLsbD 1 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 4) (he 0 3 (by decide) 1 4 ha hb)
  have c337 : m.getLsbD 2 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 0 3 (by decide) 2 5 ha hb)
  have c338 : m.getLsbD 2 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 0 3 (by decide) 2 6 ha hb)
  have c342 : m.getLsbD 3 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 5) (he 0 3 (by decide) 3 5 ha hb)
  have c343 : m.getLsbD 4 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 0) (he 0 3 (by decide) 4 0 ha hb)
  have c345 : m.getLsbD 4 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 3) (he 0 3 (by decide) 4 3 ha hb)
  have c347 : m.getLsbD 4 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 0 3 (by decide) 4 6 ha hb)
  have c348 : m.getLsbD 5 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 0 3 (by decide) 5 0 ha hb)
  have c349 : m.getLsbD 5 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 0 3 (by decide) 5 2 ha hb)
  have c350 : m.getLsbD 5 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 0 3 (by decide) 5 3 ha hb)
  have c352 : m.getLsbD 6 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 0) (he 0 3 (by decide) 6 0 ha hb)
  have c353 : m.getLsbD 6 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 0 3 (by decide) 6 2 ha hb)
  have c357 : m.getLsbD 14 = true → m.getLsbD 22 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 1) (he 2 3 (by decide) 0 1 ha hb)
  have c358 : m.getLsbD 14 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 4) (he 2 3 (by decide) 0 4 ha hb)
  have c359 : m.getLsbD 14 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 5) (he 2 3 (by decide) 0 5 ha hb)
  have c360 : m.getLsbD 14 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 6) (he 2 3 (by decide) 0 6 ha hb)
  have c361 : m.getLsbD 15 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 0) (he 2 3 (by decide) 1 0 ha hb)
  have c363 : m.getLsbD 15 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 2) (he 2 3 (by decide) 1 2 ha hb)
  have c364 : m.getLsbD 15 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 3) (he 2 3 (by decide) 1 3 ha hb)
  have c365 : m.getLsbD 15 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 4) (he 2 3 (by decide) 1 4 ha hb)
  have c366 : m.getLsbD 16 = true → m.getLsbD 22 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 1) (he 2 3 (by decide) 2 1 ha hb)
  have c368 : m.getLsbD 16 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 2 3 (by decide) 2 5 ha hb)
  have c369 : m.getLsbD 16 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 2 3 (by decide) 2 6 ha hb)
  have c373 : m.getLsbD 17 = true → m.getLsbD 26 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 5) (he 2 3 (by decide) 3 5 ha hb)
  have c374 : m.getLsbD 18 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 0) (he 2 3 (by decide) 4 0 ha hb)
  have c375 : m.getLsbD 18 = true → m.getLsbD 22 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 1) (he 2 3 (by decide) 4 1 ha hb)
  have c376 : m.getLsbD 18 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 3) (he 2 3 (by decide) 4 3 ha hb)
  have c378 : m.getLsbD 18 = true → m.getLsbD 27 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 2 3 (by decide) 4 6 ha hb)
  have c379 : m.getLsbD 19 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 2 3 (by decide) 5 0 ha hb)
  have c380 : m.getLsbD 19 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 2 3 (by decide) 5 2 ha hb)
  have c381 : m.getLsbD 19 = true → m.getLsbD 24 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 2 3 (by decide) 5 3 ha hb)
  have c383 : m.getLsbD 20 = true → m.getLsbD 21 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 0) (he 2 3 (by decide) 6 0 ha hb)
  have c384 : m.getLsbD 20 = true → m.getLsbD 23 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 2 3 (by decide) 6 2 ha hb)
  have c385 : m.getLsbD 20 = true → m.getLsbD 25 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 4) (he 2 3 (by decide) 6 4 ha hb)
  have c388 : m.getLsbD 14 = true → m.getLsbD 29 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 1) (he 2 4 (by decide) 0 1 ha hb)
  have c389 : m.getLsbD 14 = true → m.getLsbD 32 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 4) (he 2 4 (by decide) 0 4 ha hb)
  have c390 : m.getLsbD 14 = true → m.getLsbD 33 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 5) (he 2 4 (by decide) 0 5 ha hb)
  have c392 : m.getLsbD 15 = true → m.getLsbD 28 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 0) (he 2 4 (by decide) 1 0 ha hb)
  have c396 : m.getLsbD 15 = true → m.getLsbD 32 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 4) (he 2 4 (by decide) 1 4 ha hb)
  have c397 : m.getLsbD 16 = true → m.getLsbD 29 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 1) (he 2 4 (by decide) 2 1 ha hb)
  have c399 : m.getLsbD 16 = true → m.getLsbD 33 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 2 4 (by decide) 2 5 ha hb)
  have c407 : m.getLsbD 18 = true → m.getLsbD 31 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 3) (he 2 4 (by decide) 4 3 ha hb)
  have c409 : m.getLsbD 18 = true → m.getLsbD 34 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 2 4 (by decide) 4 6 ha hb)
  have c410 : m.getLsbD 19 = true → m.getLsbD 28 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 2 4 (by decide) 5 0 ha hb)
  have c411 : m.getLsbD 19 = true → m.getLsbD 30 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 2 4 (by decide) 5 2 ha hb)
  have c412 : m.getLsbD 19 = true → m.getLsbD 31 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 2 4 (by decide) 5 3 ha hb)
  have c414 : m.getLsbD 20 = true → m.getLsbD 28 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 0) (he 2 4 (by decide) 6 0 ha hb)
  have c415 : m.getLsbD 20 = true → m.getLsbD 30 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 2 4 (by decide) 6 2 ha hb)
  have c416 : m.getLsbD 20 = true → m.getLsbD 32 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 4) (he 2 4 (by decide) 6 4 ha hb)
  have c419 : m.getLsbD 28 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 1) (he 4 5 (by decide) 0 1 ha hb)
  have c421 : m.getLsbD 28 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 5) (he 4 5 (by decide) 0 5 ha hb)
  have c422 : m.getLsbD 28 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 6) (he 4 5 (by decide) 0 6 ha hb)
  have c425 : m.getLsbD 29 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 2) (he 4 5 (by decide) 1 2 ha hb)
  have c426 : m.getLsbD 29 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 3) (he 4 5 (by decide) 1 3 ha hb)
  have c428 : m.getLsbD 30 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 1) (he 4 5 (by decide) 2 1 ha hb)
  have c430 : m.getLsbD 30 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 4 5 (by decide) 2 5 ha hb)
  have c431 : m.getLsbD 30 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 4 5 (by decide) 2 6 ha hb)
  have c432 : m.getLsbD 31 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 1) (he 4 5 (by decide) 3 1 ha hb)
  have c435 : m.getLsbD 31 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 5) (he 4 5 (by decide) 3 5 ha hb)
  have c436 : m.getLsbD 32 = true → m.getLsbD 35 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 0) (he 4 5 (by decide) 4 0 ha hb)
  have c437 : m.getLsbD 32 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 1) (he 4 5 (by decide) 4 1 ha hb)
  have c438 : m.getLsbD 32 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 3) (he 4 5 (by decide) 4 3 ha hb)
  have c440 : m.getLsbD 32 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 4 5 (by decide) 4 6 ha hb)
  have c441 : m.getLsbD 33 = true → m.getLsbD 35 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 4 5 (by decide) 5 0 ha hb)
  have c442 : m.getLsbD 33 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 4 5 (by decide) 5 2 ha hb)
  have c443 : m.getLsbD 33 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 4 5 (by decide) 5 3 ha hb)
  have c446 : m.getLsbD 34 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 4 5 (by decide) 6 2 ha hb)
  have c450 : m.getLsbD 7 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 1) (he 1 5 (by decide) 0 1 ha hb)
  have c452 : m.getLsbD 7 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 5) (he 1 5 (by decide) 0 5 ha hb)
  have c453 : m.getLsbD 7 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 6) (he 1 5 (by decide) 0 6 ha hb)
  have c456 : m.getLsbD 8 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 2) (he 1 5 (by decide) 1 2 ha hb)
  have c457 : m.getLsbD 8 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 3) (he 1 5 (by decide) 1 3 ha hb)
  have c459 : m.getLsbD 9 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 1) (he 1 5 (by decide) 2 1 ha hb)
  have c461 : m.getLsbD 9 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 1 5 (by decide) 2 5 ha hb)
  have c462 : m.getLsbD 9 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 1 5 (by decide) 2 6 ha hb)
  have c463 : m.getLsbD 10 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 1) (he 1 5 (by decide) 3 1 ha hb)
  have c466 : m.getLsbD 10 = true → m.getLsbD 40 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 5) (he 1 5 (by decide) 3 5 ha hb)
  have c468 : m.getLsbD 11 = true → m.getLsbD 36 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 1) (he 1 5 (by decide) 4 1 ha hb)
  have c469 : m.getLsbD 11 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 3) (he 1 5 (by decide) 4 3 ha hb)
  have c471 : m.getLsbD 11 = true → m.getLsbD 41 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 1 5 (by decide) 4 6 ha hb)
  have c472 : m.getLsbD 12 = true → m.getLsbD 35 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 1 5 (by decide) 5 0 ha hb)
  have c473 : m.getLsbD 12 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 1 5 (by decide) 5 2 ha hb)
  have c474 : m.getLsbD 12 = true → m.getLsbD 38 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 1 5 (by decide) 5 3 ha hb)
  have c477 : m.getLsbD 13 = true → m.getLsbD 37 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 1 5 (by decide) 6 2 ha hb)
  have c482 : m.getLsbD 7 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 4) (he 1 6 (by decide) 0 4 ha hb)
  have c484 : m.getLsbD 7 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 6) (he 1 6 (by decide) 0 6 ha hb)
  have c488 : m.getLsbD 8 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 3) (he 1 6 (by decide) 1 3 ha hb)
  have c489 : m.getLsbD 8 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 4) (he 1 6 (by decide) 1 4 ha hb)
  have c493 : m.getLsbD 9 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 1 6 (by decide) 2 6 ha hb)
  have c499 : m.getLsbD 11 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 1) (he 1 6 (by decide) 4 1 ha hb)
  have c500 : m.getLsbD 11 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 3) (he 1 6 (by decide) 4 3 ha hb)
  have c502 : m.getLsbD 11 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 1 6 (by decide) 4 6 ha hb)
  have c504 : m.getLsbD 12 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 1 6 (by decide) 5 2 ha hb)
  have c505 : m.getLsbD 12 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 1 6 (by decide) 5 3 ha hb)
  have c513 : m.getLsbD 35 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 4) (he 5 6 (by decide) 0 4 ha hb)
  have c516 : m.getLsbD 36 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 0) (he 5 6 (by decide) 1 0 ha hb)
  have c518 : m.getLsbD 36 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 2) (he 5 6 (by decide) 1 2 ha hb)
  have c520 : m.getLsbD 36 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 4) (he 5 6 (by decide) 1 4 ha hb)
  have c521 : m.getLsbD 37 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 1) (he 5 6 (by decide) 2 1 ha hb)
  have c523 : m.getLsbD 37 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 5 6 (by decide) 2 5 ha hb)
  have c524 : m.getLsbD 37 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 5 6 (by decide) 2 6 ha hb)
  have c525 : m.getLsbD 38 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 1) (he 5 6 (by decide) 3 1 ha hb)
  have c527 : m.getLsbD 38 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 4) (he 5 6 (by decide) 3 4 ha hb)
  have c528 : m.getLsbD 38 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 5) (he 5 6 (by decide) 3 5 ha hb)
  have c531 : m.getLsbD 39 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 3) (he 5 6 (by decide) 4 3 ha hb)
  have c533 : m.getLsbD 39 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 6) (he 5 6 (by decide) 4 6 ha hb)
  have c534 : m.getLsbD 40 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 5 6 (by decide) 5 0 ha hb)
  have c535 : m.getLsbD 40 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 5 6 (by decide) 5 2 ha hb)
  have c536 : m.getLsbD 40 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 5 6 (by decide) 5 3 ha hb)
  have c538 : m.getLsbD 41 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 0) (he 5 6 (by decide) 6 0 ha hb)
  have c539 : m.getLsbD 41 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 5 6 (by decide) 6 2 ha hb)
  have c540 : m.getLsbD 41 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 4) (he 5 6 (by decide) 6 4 ha hb)
  have c543 : m.getLsbD 21 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 1) (he 3 6 (by decide) 0 1 ha hb)
  have c544 : m.getLsbD 21 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 4) (he 3 6 (by decide) 0 4 ha hb)
  have c545 : m.getLsbD 21 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 5) (he 3 6 (by decide) 0 5 ha hb)
  have c546 : m.getLsbD 21 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 0 6) (he 3 6 (by decide) 0 6 ha hb)
  have c547 : m.getLsbD 22 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 0) (he 3 6 (by decide) 1 0 ha hb)
  have c549 : m.getLsbD 22 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 2) (he 3 6 (by decide) 1 2 ha hb)
  have c551 : m.getLsbD 22 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 1 4) (he 3 6 (by decide) 1 4 ha hb)
  have c552 : m.getLsbD 23 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 1) (he 3 6 (by decide) 2 1 ha hb)
  have c554 : m.getLsbD 23 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 5) (he 3 6 (by decide) 2 5 ha hb)
  have c555 : m.getLsbD 23 = true → m.getLsbD 48 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 2 6) (he 3 6 (by decide) 2 6 ha hb)
  have c556 : m.getLsbD 24 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 1) (he 3 6 (by decide) 3 1 ha hb)
  have c558 : m.getLsbD 24 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 4) (he 3 6 (by decide) 3 4 ha hb)
  have c559 : m.getLsbD 24 = true → m.getLsbD 47 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 3 5) (he 3 6 (by decide) 3 5 ha hb)
  have c560 : m.getLsbD 25 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 0) (he 3 6 (by decide) 4 0 ha hb)
  have c561 : m.getLsbD 25 = true → m.getLsbD 43 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 4 1) (he 3 6 (by decide) 4 1 ha hb)
  have c565 : m.getLsbD 26 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 0) (he 3 6 (by decide) 5 0 ha hb)
  have c566 : m.getLsbD 26 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 2) (he 3 6 (by decide) 5 2 ha hb)
  have c567 : m.getLsbD 26 = true → m.getLsbD 45 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 5 3) (he 3 6 (by decide) 5 3 ha hb)
  have c569 : m.getLsbD 27 = true → m.getLsbD 42 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 0) (he 3 6 (by decide) 6 0 ha hb)
  have c570 : m.getLsbD 27 = true → m.getLsbD 44 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 2) (he 3 6 (by decide) 6 2 ha hb)
  have c571 : m.getLsbD 27 = true → m.getLsbD 46 = true → False := fun ha hb =>
    (by decide : ¬ h7.Adj 6 4) (he 3 6 (by decide) 6 4 ha hb)
  have c573 : m.getLsbD 14 = true → m.getLsbD 2 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 30 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 0 ha 2 (by decide)
  have c574 : m.getLsbD 14 = true → m.getLsbD 3 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 31 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 0 ha 3 (by decide)
  have c575 : m.getLsbD 15 = true → m.getLsbD 5 = true ∨ m.getLsbD 26 = true ∨ m.getLsbD 33 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 1 ha 5 (by decide)
  have c576 : m.getLsbD 15 = true → m.getLsbD 6 = true ∨ m.getLsbD 27 = true ∨ m.getLsbD 34 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 1 ha 6 (by decide)
  have c577 : m.getLsbD 16 = true → m.getLsbD 0 = true ∨ m.getLsbD 21 = true ∨ m.getLsbD 28 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 2 ha 0 (by decide)
  have c578 : m.getLsbD 16 = true → m.getLsbD 3 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 31 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 2 ha 3 (by decide)
  have c579 : m.getLsbD 16 = true → m.getLsbD 4 = true ∨ m.getLsbD 25 = true ∨ m.getLsbD 32 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 2 ha 4 (by decide)
  have c581 : m.getLsbD 17 = true → m.getLsbD 2 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 30 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 3 ha 2 (by decide)
  have c582 : m.getLsbD 17 = true → m.getLsbD 6 = true ∨ m.getLsbD 27 = true ∨ m.getLsbD 34 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 3 ha 6 (by decide)
  have c583 : m.getLsbD 18 = true → m.getLsbD 2 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 30 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 4 ha 2 (by decide)
  have c584 : m.getLsbD 18 = true → m.getLsbD 5 = true ∨ m.getLsbD 26 = true ∨ m.getLsbD 33 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 4 ha 5 (by decide)
  have c585 : m.getLsbD 19 = true → m.getLsbD 1 = true ∨ m.getLsbD 22 = true ∨ m.getLsbD 29 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 5 ha 1 (by decide)
  have c586 : m.getLsbD 19 = true → m.getLsbD 4 = true ∨ m.getLsbD 25 = true ∨ m.getLsbD 32 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 5 ha 4 (by decide)
  have c587 : m.getLsbD 19 = true → m.getLsbD 6 = true ∨ m.getLsbD 27 = true ∨ m.getLsbD 34 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 5 ha 6 (by decide)
  have c588 : m.getLsbD 20 = true → m.getLsbD 1 = true ∨ m.getLsbD 22 = true ∨ m.getLsbD 29 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 6 ha 1 (by decide)
  have c589 : m.getLsbD 20 = true → m.getLsbD 3 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 31 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 6 ha 3 (by decide)
  have c590 : m.getLsbD 20 = true → m.getLsbD 5 = true ∨ m.getLsbD 26 = true ∨ m.getLsbD 33 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      hs 2 (by decide) 6 ha 5 (by decide)
  have c591 : m.getLsbD 21 = true → m.getLsbD 2 = true ∨ m.getLsbD 16 = true ∨ m.getLsbD 44 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 0 ha 2 (by decide)
  have c592 : m.getLsbD 21 = true → m.getLsbD 3 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 45 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 0 ha 3 (by decide)
  have c593 : m.getLsbD 22 = true → m.getLsbD 5 = true ∨ m.getLsbD 19 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 1 ha 5 (by decide)
  have c594 : m.getLsbD 22 = true → m.getLsbD 6 = true ∨ m.getLsbD 20 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 1 ha 6 (by decide)
  have c596 : m.getLsbD 23 = true → m.getLsbD 3 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 45 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 2 ha 3 (by decide)
  have c598 : m.getLsbD 24 = true → m.getLsbD 0 = true ∨ m.getLsbD 14 = true ∨ m.getLsbD 42 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 3 ha 0 (by decide)
  have c599 : m.getLsbD 24 = true → m.getLsbD 2 = true ∨ m.getLsbD 16 = true ∨ m.getLsbD 44 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 3 ha 2 (by decide)
  have c600 : m.getLsbD 24 = true → m.getLsbD 6 = true ∨ m.getLsbD 20 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 3 ha 6 (by decide)
  have c601 : m.getLsbD 25 = true → m.getLsbD 2 = true ∨ m.getLsbD 16 = true ∨ m.getLsbD 44 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 4 ha 2 (by decide)
  have c602 : m.getLsbD 25 = true → m.getLsbD 5 = true ∨ m.getLsbD 19 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 4 ha 5 (by decide)
  have c606 : m.getLsbD 27 = true → m.getLsbD 1 = true ∨ m.getLsbD 15 = true ∨ m.getLsbD 43 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 6 ha 1 (by decide)
  have c607 : m.getLsbD 27 = true → m.getLsbD 3 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 45 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 6 ha 3 (by decide)
  have c608 : m.getLsbD 27 = true → m.getLsbD 5 = true ∨ m.getLsbD 19 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      hs 3 (by decide) 6 ha 5 (by decide)
  have c609 : m.getLsbD 35 = true → m.getLsbD 9 = true ∨ m.getLsbD 30 = true ∨ m.getLsbD 44 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 0 ha 2 (by decide)
  have c610 : m.getLsbD 35 = true → m.getLsbD 10 = true ∨ m.getLsbD 31 = true ∨ m.getLsbD 45 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 0 ha 3 (by decide)
  have c611 : m.getLsbD 36 = true → m.getLsbD 12 = true ∨ m.getLsbD 33 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 1 ha 5 (by decide)
  have c612 : m.getLsbD 36 = true → m.getLsbD 13 = true ∨ m.getLsbD 34 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 1 ha 6 (by decide)
  have c613 : m.getLsbD 37 = true → m.getLsbD 7 = true ∨ m.getLsbD 28 = true ∨ m.getLsbD 42 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 2 ha 0 (by decide)
  have c614 : m.getLsbD 37 = true → m.getLsbD 10 = true ∨ m.getLsbD 31 = true ∨ m.getLsbD 45 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 2 ha 3 (by decide)
  have c615 : m.getLsbD 37 = true → m.getLsbD 11 = true ∨ m.getLsbD 32 = true ∨ m.getLsbD 46 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 2 ha 4 (by decide)
  have c616 : m.getLsbD 38 = true → m.getLsbD 7 = true ∨ m.getLsbD 28 = true ∨ m.getLsbD 42 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 3 ha 0 (by decide)
  have c618 : m.getLsbD 38 = true → m.getLsbD 13 = true ∨ m.getLsbD 34 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 3 ha 6 (by decide)
  have c619 : m.getLsbD 39 = true → m.getLsbD 9 = true ∨ m.getLsbD 30 = true ∨ m.getLsbD 44 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 4 ha 2 (by decide)
  have c620 : m.getLsbD 39 = true → m.getLsbD 12 = true ∨ m.getLsbD 33 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 4 ha 5 (by decide)
  have c622 : m.getLsbD 40 = true → m.getLsbD 11 = true ∨ m.getLsbD 32 = true ∨ m.getLsbD 46 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 5 ha 4 (by decide)
  have c623 : m.getLsbD 40 = true → m.getLsbD 13 = true ∨ m.getLsbD 34 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 5 ha 6 (by decide)
  have c624 : m.getLsbD 41 = true → m.getLsbD 8 = true ∨ m.getLsbD 29 = true ∨ m.getLsbD 43 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 6 ha 1 (by decide)
  have c625 : m.getLsbD 41 = true → m.getLsbD 10 = true ∨ m.getLsbD 31 = true ∨ m.getLsbD 45 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 6 ha 3 (by decide)
  have c626 : m.getLsbD 41 = true → m.getLsbD 12 = true ∨ m.getLsbD 33 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      hs 5 (by decide) 6 ha 5 (by decide)
  have c627 : m.getLsbD 42 = true → m.getLsbD 9 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 37 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 0 ha 2 (by decide)
  have c628 : m.getLsbD 42 = true → m.getLsbD 10 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 38 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 0 ha 3 (by decide)
  have c630 : m.getLsbD 43 = true → m.getLsbD 13 = true ∨ m.getLsbD 27 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 1 ha 6 (by decide)
  have c632 : m.getLsbD 44 = true → m.getLsbD 10 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 38 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 2 ha 3 (by decide)
  have c633 : m.getLsbD 44 = true → m.getLsbD 11 = true ∨ m.getLsbD 25 = true ∨ m.getLsbD 39 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 2 ha 4 (by decide)
  have c634 : m.getLsbD 45 = true → m.getLsbD 7 = true ∨ m.getLsbD 21 = true ∨ m.getLsbD 35 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 3 ha 0 (by decide)
  have c635 : m.getLsbD 45 = true → m.getLsbD 9 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 37 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 3 ha 2 (by decide)
  have c636 : m.getLsbD 45 = true → m.getLsbD 13 = true ∨ m.getLsbD 27 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 3 ha 6 (by decide)
  have c637 : m.getLsbD 46 = true → m.getLsbD 9 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 37 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 4 ha 2 (by decide)
  have c638 : m.getLsbD 46 = true → m.getLsbD 12 = true ∨ m.getLsbD 26 = true ∨ m.getLsbD 40 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 4 ha 5 (by decide)
  have c640 : m.getLsbD 47 = true → m.getLsbD 11 = true ∨ m.getLsbD 25 = true ∨ m.getLsbD 39 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 5 ha 4 (by decide)
  have c641 : m.getLsbD 47 = true → m.getLsbD 13 = true ∨ m.getLsbD 27 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 5 ha 6 (by decide)
  have c642 : m.getLsbD 48 = true → m.getLsbD 8 = true ∨ m.getLsbD 22 = true ∨ m.getLsbD 36 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 6 ha 1 (by decide)
  have c643 : m.getLsbD 48 = true → m.getLsbD 10 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 38 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 6 ha 3 (by decide)
  have c644 : m.getLsbD 48 = true → m.getLsbD 12 = true ∨ m.getLsbD 26 = true ∨ m.getLsbD 40 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      hs 6 (by decide) 6 ha 5 (by decide)
  have c645 : m.getLsbD 2 = true → m.getLsbD 14 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 18 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 0 ha 2 (by decide)
  have c646 : m.getLsbD 2 = true → m.getLsbD 21 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 25 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 0 ha 3 (by decide)
  have c647 : m.getLsbD 9 = true → m.getLsbD 35 = true ∨ m.getLsbD 38 = true ∨ m.getLsbD 39 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 1 ha 5 (by decide)
  have c648 : m.getLsbD 9 = true → m.getLsbD 42 = true ∨ m.getLsbD 45 = true ∨ m.getLsbD 46 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 1 ha 6 (by decide)
  have c650 : m.getLsbD 16 = true → m.getLsbD 21 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 25 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 2 ha 3 (by decide)
  have c654 : m.getLsbD 23 = true → m.getLsbD 42 = true ∨ m.getLsbD 45 = true ∨ m.getLsbD 46 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 3 ha 6 (by decide)
  have c655 : m.getLsbD 30 = true → m.getLsbD 14 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 18 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 4 ha 2 (by decide)
  have c656 : m.getLsbD 30 = true → m.getLsbD 35 = true ∨ m.getLsbD 38 = true ∨ m.getLsbD 39 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 4 ha 5 (by decide)
  have c659 : m.getLsbD 37 = true → m.getLsbD 42 = true ∨ m.getLsbD 45 = true ∨ m.getLsbD 46 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 5 ha 6 (by decide)
  have c661 : m.getLsbD 44 = true → m.getLsbD 21 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 25 = true := by
    intro ha
    simpa [bit, adj_2, or_and_right, exists_or, exists_eq_left] using
      ht 2 (by decide) 6 ha 3 (by decide)
  have c663 : m.getLsbD 3 = true → m.getLsbD 14 = true ∨ m.getLsbD 16 = true ∨ m.getLsbD 20 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 0 ha 2 (by decide)
  have c664 : m.getLsbD 3 = true → m.getLsbD 21 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 27 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 0 ha 3 (by decide)
  have c665 : m.getLsbD 10 = true → m.getLsbD 35 = true ∨ m.getLsbD 37 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 1 ha 5 (by decide)
  have c666 : m.getLsbD 10 = true → m.getLsbD 42 = true ∨ m.getLsbD 44 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 1 ha 6 (by decide)
  have c667 : m.getLsbD 17 = true → m.getLsbD 0 = true ∨ m.getLsbD 2 = true ∨ m.getLsbD 6 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 2 ha 0 (by decide)
  have c668 : m.getLsbD 17 = true → m.getLsbD 21 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 27 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 2 ha 3 (by decide)
  have c673 : m.getLsbD 31 = true → m.getLsbD 14 = true ∨ m.getLsbD 16 = true ∨ m.getLsbD 20 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 4 ha 2 (by decide)
  have c674 : m.getLsbD 31 = true → m.getLsbD 35 = true ∨ m.getLsbD 37 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 4 ha 5 (by decide)
  have c677 : m.getLsbD 38 = true → m.getLsbD 42 = true ∨ m.getLsbD 44 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 5 ha 6 (by decide)
  have c678 : m.getLsbD 45 = true → m.getLsbD 7 = true ∨ m.getLsbD 9 = true ∨ m.getLsbD 13 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 6 ha 1 (by decide)
  have c679 : m.getLsbD 45 = true → m.getLsbD 21 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 27 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 6 ha 3 (by decide)
  have c680 : m.getLsbD 45 = true → m.getLsbD 35 = true ∨ m.getLsbD 37 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_3, or_and_right, exists_or, exists_eq_left] using
      ht 3 (by decide) 6 ha 5 (by decide)
  have c681 : m.getLsbD 5 = true → m.getLsbD 15 = true ∨ m.getLsbD 18 = true ∨ m.getLsbD 20 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 0 ha 2 (by decide)
  have c682 : m.getLsbD 5 = true → m.getLsbD 22 = true ∨ m.getLsbD 25 = true ∨ m.getLsbD 27 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 0 ha 3 (by decide)
  have c683 : m.getLsbD 12 = true → m.getLsbD 36 = true ∨ m.getLsbD 39 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 1 ha 5 (by decide)
  have c684 : m.getLsbD 12 = true → m.getLsbD 43 = true ∨ m.getLsbD 46 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 1 ha 6 (by decide)
  have c686 : m.getLsbD 19 = true → m.getLsbD 22 = true ∨ m.getLsbD 25 = true ∨ m.getLsbD 27 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 2 ha 3 (by decide)
  have c690 : m.getLsbD 26 = true → m.getLsbD 43 = true ∨ m.getLsbD 46 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 3 ha 6 (by decide)
  have c691 : m.getLsbD 33 = true → m.getLsbD 15 = true ∨ m.getLsbD 18 = true ∨ m.getLsbD 20 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 4 ha 2 (by decide)
  have c692 : m.getLsbD 33 = true → m.getLsbD 36 = true ∨ m.getLsbD 39 = true ∨ m.getLsbD 41 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 4 ha 5 (by decide)
  have c693 : m.getLsbD 40 = true → m.getLsbD 8 = true ∨ m.getLsbD 11 = true ∨ m.getLsbD 13 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 5 ha 1 (by decide)
  have c695 : m.getLsbD 40 = true → m.getLsbD 43 = true ∨ m.getLsbD 46 = true ∨ m.getLsbD 48 = true := by
    intro ha
    simpa [bit, adj_5, or_and_right, exists_or, exists_eq_left] using
      ht 5 (by decide) 5 ha 6 (by decide)
  have c699 : m.getLsbD 6 = true → m.getLsbD 15 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 19 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 0 ha 2 (by decide)
  have c700 : m.getLsbD 6 = true → m.getLsbD 22 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 26 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 0 ha 3 (by decide)
  have c701 : m.getLsbD 13 = true → m.getLsbD 36 = true ∨ m.getLsbD 38 = true ∨ m.getLsbD 40 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 1 ha 5 (by decide)
  have c702 : m.getLsbD 13 = true → m.getLsbD 43 = true ∨ m.getLsbD 45 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 1 ha 6 (by decide)
  have c703 : m.getLsbD 20 = true → m.getLsbD 1 = true ∨ m.getLsbD 3 = true ∨ m.getLsbD 5 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 2 ha 0 (by decide)
  have c704 : m.getLsbD 20 = true → m.getLsbD 22 = true ∨ m.getLsbD 24 = true ∨ m.getLsbD 26 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 2 ha 3 (by decide)
  have c709 : m.getLsbD 34 = true → m.getLsbD 15 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 19 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 4 ha 2 (by decide)
  have c710 : m.getLsbD 34 = true → m.getLsbD 36 = true ∨ m.getLsbD 38 = true ∨ m.getLsbD 40 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 4 ha 5 (by decide)
  have c713 : m.getLsbD 41 = true → m.getLsbD 43 = true ∨ m.getLsbD 45 = true ∨ m.getLsbD 47 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 5 ha 6 (by decide)
  have c716 : m.getLsbD 48 = true → m.getLsbD 36 = true ∨ m.getLsbD 38 = true ∨ m.getLsbD 40 = true := by
    intro ha
    simpa [bit, adj_6, or_and_right, exists_or, exists_eq_left] using
      ht 6 (by decide) 6 ha 5 (by decide)
  have c717 : m.getLsbD 0 = true → m.getLsbD 16 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 24 = true := by
    intro ha
    have hp := hd 0 0 ha
    have hn : ¬ ((0 : Fin 7) = 2 ∨ (0 : Fin 7) = 3 ∨ (0 : Fin 7) = 5 ∨ (0 : Fin 7) = 6) := by decide
    have hn' : ¬ ((0 : Fin 7) = 2 ∨ (0 : Fin 7) = 3 ∨ (0 : Fin 7) = 5 ∨ (0 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_0, adj_0, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c718 : m.getLsbD 1 = true → m.getLsbD 19 = true ∨ m.getLsbD 20 = true ∨ m.getLsbD 26 = true ∨ m.getLsbD 27 = true := by
    intro ha
    have hp := hd 0 1 ha
    have hn : ¬ ((0 : Fin 7) = 2 ∨ (0 : Fin 7) = 3 ∨ (0 : Fin 7) = 5 ∨ (0 : Fin 7) = 6) := by decide
    have hn' : ¬ ((1 : Fin 7) = 2 ∨ (1 : Fin 7) = 3 ∨ (1 : Fin 7) = 5 ∨ (1 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_0, adj_1, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c719 : m.getLsbD 4 = true → m.getLsbD 16 = true ∨ m.getLsbD 19 = true ∨ m.getLsbD 23 = true ∨ m.getLsbD 26 = true := by
    intro ha
    have hp := hd 0 4 ha
    have hn : ¬ ((0 : Fin 7) = 2 ∨ (0 : Fin 7) = 3 ∨ (0 : Fin 7) = 5 ∨ (0 : Fin 7) = 6) := by decide
    have hn' : ¬ ((4 : Fin 7) = 2 ∨ (4 : Fin 7) = 3 ∨ (4 : Fin 7) = 5 ∨ (4 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_0, adj_4, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c720 : m.getLsbD 7 = true → m.getLsbD 37 = true ∨ m.getLsbD 38 = true ∨ m.getLsbD 44 = true ∨ m.getLsbD 45 = true := by
    intro ha
    have hp := hd 1 0 ha
    have hn : ¬ ((1 : Fin 7) = 2 ∨ (1 : Fin 7) = 3 ∨ (1 : Fin 7) = 5 ∨ (1 : Fin 7) = 6) := by decide
    have hn' : ¬ ((0 : Fin 7) = 2 ∨ (0 : Fin 7) = 3 ∨ (0 : Fin 7) = 5 ∨ (0 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_1, adj_0, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c721 : m.getLsbD 8 = true → m.getLsbD 40 = true ∨ m.getLsbD 41 = true ∨ m.getLsbD 47 = true ∨ m.getLsbD 48 = true := by
    intro ha
    have hp := hd 1 1 ha
    have hn : ¬ ((1 : Fin 7) = 2 ∨ (1 : Fin 7) = 3 ∨ (1 : Fin 7) = 5 ∨ (1 : Fin 7) = 6) := by decide
    have hn' : ¬ ((1 : Fin 7) = 2 ∨ (1 : Fin 7) = 3 ∨ (1 : Fin 7) = 5 ∨ (1 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_1, adj_1, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c722 : m.getLsbD 11 = true → m.getLsbD 37 = true ∨ m.getLsbD 40 = true ∨ m.getLsbD 44 = true ∨ m.getLsbD 47 = true := by
    intro ha
    have hp := hd 1 4 ha
    have hn : ¬ ((1 : Fin 7) = 2 ∨ (1 : Fin 7) = 3 ∨ (1 : Fin 7) = 5 ∨ (1 : Fin 7) = 6) := by decide
    have hn' : ¬ ((4 : Fin 7) = 2 ∨ (4 : Fin 7) = 3 ∨ (4 : Fin 7) = 5 ∨ (4 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_1, adj_4, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c723 : m.getLsbD 28 = true → m.getLsbD 16 = true ∨ m.getLsbD 17 = true ∨ m.getLsbD 37 = true ∨ m.getLsbD 38 = true := by
    intro ha
    have hp := hd 4 0 ha
    have hn : ¬ ((4 : Fin 7) = 2 ∨ (4 : Fin 7) = 3 ∨ (4 : Fin 7) = 5 ∨ (4 : Fin 7) = 6) := by decide
    have hn' : ¬ ((0 : Fin 7) = 2 ∨ (0 : Fin 7) = 3 ∨ (0 : Fin 7) = 5 ∨ (0 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_4, adj_0, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c724 : m.getLsbD 29 = true → m.getLsbD 19 = true ∨ m.getLsbD 20 = true ∨ m.getLsbD 40 = true ∨ m.getLsbD 41 = true := by
    intro ha
    have hp := hd 4 1 ha
    have hn : ¬ ((4 : Fin 7) = 2 ∨ (4 : Fin 7) = 3 ∨ (4 : Fin 7) = 5 ∨ (4 : Fin 7) = 6) := by decide
    have hn' : ¬ ((1 : Fin 7) = 2 ∨ (1 : Fin 7) = 3 ∨ (1 : Fin 7) = 5 ∨ (1 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_4, adj_1, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  have c725 : m.getLsbD 32 = true → m.getLsbD 16 = true ∨ m.getLsbD 19 = true ∨ m.getLsbD 37 = true ∨ m.getLsbD 40 = true := by
    intro ha
    have hp := hd 4 4 ha
    have hn : ¬ ((4 : Fin 7) = 2 ∨ (4 : Fin 7) = 3 ∨ (4 : Fin 7) = 5 ∨ (4 : Fin 7) = 6) := by decide
    have hn' : ¬ ((4 : Fin 7) = 2 ∨ (4 : Fin 7) = 3 ∨ (4 : Fin 7) = 5 ∨ (4 : Fin 7) = 6) := by decide
    rcases hp with hp | hp | hp
    · exact (hn hp).elim
    · exact (hn' hp).elim
    · simpa [bit, adj_4, adj_4, or_and_right, and_or_left, exists_or, exists_eq_left, or_comm, or_left_comm, or_assoc] using hp
  clear hr hc he hs ht hd
  by_cases b24 : m.getLsbD 24 = true
  ·
    have b21 : ¬ (m.getLsbD 21 = true) := fun h => c130 h b24
    have b3 : ¬ (m.getLsbD 3 = true) := fun h => c131 h b24
    have b22 : ¬ (m.getLsbD 22 = true) := fun h => c140 h b24
    have b10 : ¬ (m.getLsbD 10 = true) := fun h => c141 h b24
    have b23 : ¬ (m.getLsbD 23 = true) := fun h => c148 h b24
    have b17 : ¬ (m.getLsbD 17 = true) := fun h => c149 h b24
    have b25 : ¬ (m.getLsbD 25 = true) := c156 b24
    have b31 : ¬ (m.getLsbD 31 = true) := c157 b24
    have b26 : ¬ (m.getLsbD 26 = true) := c158 b24
    have b38 : ¬ (m.getLsbD 38 = true) := c159 b24
    have b27 : ¬ (m.getLsbD 27 = true) := c160 b24
    have b45 : ¬ (m.getLsbD 45 = true) := c161 b24
    have b1 : ¬ (m.getLsbD 1 = true) := fun h => c333 h b24
    have b4 : ¬ (m.getLsbD 4 = true) := fun h => c345 h b24
    have b5 : ¬ (m.getLsbD 5 = true) := fun h => c350 h b24
    have b15 : ¬ (m.getLsbD 15 = true) := fun h => c364 h b24
    have b18 : ¬ (m.getLsbD 18 = true) := fun h => c376 h b24
    have b19 : ¬ (m.getLsbD 19 = true) := fun h => c381 h b24
    have b43 : ¬ (m.getLsbD 43 = true) := c556 b24
    have b46 : ¬ (m.getLsbD 46 = true) := c558 b24
    have b47 : ¬ (m.getLsbD 47 = true) := c559 b24
    have b35 : ¬ (m.getLsbD 35 = true) := by
      intro h
      rcases c610 h with h | h | h
      · exact (b10 h).elim
      · exact (b31 h).elim
      · exact (b45 h).elim
    have b37 : ¬ (m.getLsbD 37 = true) := by
      intro h
      rcases c614 h with h | h | h
      · exact (b10 h).elim
      · exact (b31 h).elim
      · exact (b45 h).elim
    have b41 : ¬ (m.getLsbD 41 = true) := by
      intro h
      rcases c625 h with h | h | h
      · exact (b10 h).elim
      · exact (b31 h).elim
      · exact (b45 h).elim
    have b6 : ¬ (m.getLsbD 6 = true) := by
      intro h
      rcases c699 h with h | h | h
      · exact (b15 h).elim
      · exact (b17 h).elim
      · exact (b19 h).elim
    have b13 : ¬ (m.getLsbD 13 = true) := by
      intro h
      rcases c702 h with h | h | h
      · exact (b43 h).elim
      · exact (b45 h).elim
      · exact (b47 h).elim
    have b20 : ¬ (m.getLsbD 20 = true) := by
      intro h
      rcases c703 h with h | h | h
      · exact (b1 h).elim
      · exact (b3 h).elim
      · exact (b5 h).elim
    have b34 : ¬ (m.getLsbD 34 = true) := by
      intro h
      rcases c709 h with h | h | h
      · exact (b15 h).elim
      · exact (b17 h).elim
      · exact (b19 h).elim
    have b48 : m.getLsbD 48 = true := by
      rcases c600 b24 with h | h | h
      · exact (b6 h).elim
      · exact (b20 h).elim
      · exact h
    have b33 : ¬ (m.getLsbD 33 = true) := by
      intro h
      rcases c691 h with h | h | h
      · exact (b15 h).elim
      · exact (b18 h).elim
      · exact (b20 h).elim
    have b42 : ¬ (m.getLsbD 42 = true) := fun h => c262 h b48
    have b44 : ¬ (m.getLsbD 44 = true) := fun h => c280 h b48
    have b7 : ¬ (m.getLsbD 7 = true) := fun h => c484 h b48
    have b9 : ¬ (m.getLsbD 9 = true) := fun h => c493 h b48
    have b11 : ¬ (m.getLsbD 11 = true) := fun h => c502 h b48
    have b39 : ¬ (m.getLsbD 39 = true) := fun h => c533 h b48
    have b30 : ¬ (m.getLsbD 30 = true) := by
      intro h
      rcases c656 h with h | h | h
      · exact (b35 h).elim
      · exact (b38 h).elim
      · exact (b39 h).elim
    by_cases b16 : m.getLsbD 16 = true
    ·
      have b14 : ¬ (m.getLsbD 14 = true) := fun h => c86 h b16
      have b2 : ¬ (m.getLsbD 2 = true) := fun h => c87 h b16
      have b29 : ¬ (m.getLsbD 29 = true) := c397 b16
      have b32 : m.getLsbD 32 = true := by
        rcases c579 b16 with h | h | h
        · exact (b4 h).elim
        · exact (b25 h).elim
        · exact h
      have b0 : m.getLsbD 0 = true := by
        rcases c598 b24 with h | h | h
        · exact h
        · exact (b14 h).elim
        · exact (b42 h).elim
      have b28 : ¬ (m.getLsbD 28 = true) := c7 b0
      have b36 : ¬ (m.getLsbD 36 = true) := c437 b32
      have b8 : m.getLsbD 8 = true := by
        rcases c642 b48 with h | h | h
        · exact h
        · exact (b22 h).elim
        · exact (b36 h).elim
      have b12 : ¬ (m.getLsbD 12 = true) := by
        intro h
        rcases c683 h with h | h | h
        · exact (b36 h).elim
        · exact (b39 h).elim
        · exact (b41 h).elim
      have b40 : m.getLsbD 40 = true := by
        rcases c716 b48 with h | h | h
        · exact (b36 h).elim
        · exact (b38 h).elim
        · exact h
      have hfull : m = 282578800148737 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        interval_cases i
        · change m.getLsbD 0 = true
          exact b0
        · change m.getLsbD 1 = false
          exact Bool.eq_false_of_not_eq_true b1
        · change m.getLsbD 2 = false
          exact Bool.eq_false_of_not_eq_true b2
        · change m.getLsbD 3 = false
          exact Bool.eq_false_of_not_eq_true b3
        · change m.getLsbD 4 = false
          exact Bool.eq_false_of_not_eq_true b4
        · change m.getLsbD 5 = false
          exact Bool.eq_false_of_not_eq_true b5
        · change m.getLsbD 6 = false
          exact Bool.eq_false_of_not_eq_true b6
        · change m.getLsbD 7 = false
          exact Bool.eq_false_of_not_eq_true b7
        · change m.getLsbD 8 = true
          exact b8
        · change m.getLsbD 9 = false
          exact Bool.eq_false_of_not_eq_true b9
        · change m.getLsbD 10 = false
          exact Bool.eq_false_of_not_eq_true b10
        · change m.getLsbD 11 = false
          exact Bool.eq_false_of_not_eq_true b11
        · change m.getLsbD 12 = false
          exact Bool.eq_false_of_not_eq_true b12
        · change m.getLsbD 13 = false
          exact Bool.eq_false_of_not_eq_true b13
        · change m.getLsbD 14 = false
          exact Bool.eq_false_of_not_eq_true b14
        · change m.getLsbD 15 = false
          exact Bool.eq_false_of_not_eq_true b15
        · change m.getLsbD 16 = true
          exact b16
        · change m.getLsbD 17 = false
          exact Bool.eq_false_of_not_eq_true b17
        · change m.getLsbD 18 = false
          exact Bool.eq_false_of_not_eq_true b18
        · change m.getLsbD 19 = false
          exact Bool.eq_false_of_not_eq_true b19
        · change m.getLsbD 20 = false
          exact Bool.eq_false_of_not_eq_true b20
        · change m.getLsbD 21 = false
          exact Bool.eq_false_of_not_eq_true b21
        · change m.getLsbD 22 = false
          exact Bool.eq_false_of_not_eq_true b22
        · change m.getLsbD 23 = false
          exact Bool.eq_false_of_not_eq_true b23
        · change m.getLsbD 24 = true
          exact b24
        · change m.getLsbD 25 = false
          exact Bool.eq_false_of_not_eq_true b25
        · change m.getLsbD 26 = false
          exact Bool.eq_false_of_not_eq_true b26
        · change m.getLsbD 27 = false
          exact Bool.eq_false_of_not_eq_true b27
        · change m.getLsbD 28 = false
          exact Bool.eq_false_of_not_eq_true b28
        · change m.getLsbD 29 = false
          exact Bool.eq_false_of_not_eq_true b29
        · change m.getLsbD 30 = false
          exact Bool.eq_false_of_not_eq_true b30
        · change m.getLsbD 31 = false
          exact Bool.eq_false_of_not_eq_true b31
        · change m.getLsbD 32 = true
          exact b32
        · change m.getLsbD 33 = false
          exact Bool.eq_false_of_not_eq_true b33
        · change m.getLsbD 34 = false
          exact Bool.eq_false_of_not_eq_true b34
        · change m.getLsbD 35 = false
          exact Bool.eq_false_of_not_eq_true b35
        · change m.getLsbD 36 = false
          exact Bool.eq_false_of_not_eq_true b36
        · change m.getLsbD 37 = false
          exact Bool.eq_false_of_not_eq_true b37
        · change m.getLsbD 38 = false
          exact Bool.eq_false_of_not_eq_true b38
        · change m.getLsbD 39 = false
          exact Bool.eq_false_of_not_eq_true b39
        · change m.getLsbD 40 = true
          exact b40
        · change m.getLsbD 41 = false
          exact Bool.eq_false_of_not_eq_true b41
        · change m.getLsbD 42 = false
          exact Bool.eq_false_of_not_eq_true b42
        · change m.getLsbD 43 = false
          exact Bool.eq_false_of_not_eq_true b43
        · change m.getLsbD 44 = false
          exact Bool.eq_false_of_not_eq_true b44
        · change m.getLsbD 45 = false
          exact Bool.eq_false_of_not_eq_true b45
        · change m.getLsbD 46 = false
          exact Bool.eq_false_of_not_eq_true b46
        · change m.getLsbD 47 = false
          exact Bool.eq_false_of_not_eq_true b47
        · change m.getLsbD 48 = true
          exact b48
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfull)))))))
    ·
      have b2 : m.getLsbD 2 = true := by
        rcases c599 b24 with h | h | h
        · exact h
        · exact (b16 h).elim
        · exact (b44 h).elim
      have b14 : m.getLsbD 14 = true := by
        rcases c645 b2 with h | h | h
        · exact h
        · exact (b17 h).elim
        · exact (b18 h).elim
      have b28 : ¬ (m.getLsbD 28 = true) := by
        intro h
        rcases c723 h with h | h | h | h
        · exact (b16 h).elim
        · exact (b17 h).elim
        · exact (b37 h).elim
        · exact (b38 h).elim
      have b0 : ¬ (m.getLsbD 0 = true) := fun h => c2 h b2
      have b29 : ¬ (m.getLsbD 29 = true) := c388 b14
      have b32 : ¬ (m.getLsbD 32 = true) := c389 b14
      have b40 : ¬ (m.getLsbD 40 = true) := by
        intro h
        rcases c622 h with h | h | h
        · exact (b11 h).elim
        · exact (b32 h).elim
        · exact (b46 h).elim
      have b12 : m.getLsbD 12 = true := by
        rcases c644 b48 with h | h | h
        · exact h
        · exact (b26 h).elim
        · exact (b40 h).elim
      have b36 : m.getLsbD 36 = true := by
        rcases c683 b12 with h | h | h
        · exact h
        · exact (b39 h).elim
        · exact (b41 h).elim
      have b8 : ¬ (m.getLsbD 8 = true) := fun h => c60 h b12
      have hfull : m = 281543712985092 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        interval_cases i
        · change m.getLsbD 0 = false
          exact Bool.eq_false_of_not_eq_true b0
        · change m.getLsbD 1 = false
          exact Bool.eq_false_of_not_eq_true b1
        · change m.getLsbD 2 = true
          exact b2
        · change m.getLsbD 3 = false
          exact Bool.eq_false_of_not_eq_true b3
        · change m.getLsbD 4 = false
          exact Bool.eq_false_of_not_eq_true b4
        · change m.getLsbD 5 = false
          exact Bool.eq_false_of_not_eq_true b5
        · change m.getLsbD 6 = false
          exact Bool.eq_false_of_not_eq_true b6
        · change m.getLsbD 7 = false
          exact Bool.eq_false_of_not_eq_true b7
        · change m.getLsbD 8 = false
          exact Bool.eq_false_of_not_eq_true b8
        · change m.getLsbD 9 = false
          exact Bool.eq_false_of_not_eq_true b9
        · change m.getLsbD 10 = false
          exact Bool.eq_false_of_not_eq_true b10
        · change m.getLsbD 11 = false
          exact Bool.eq_false_of_not_eq_true b11
        · change m.getLsbD 12 = true
          exact b12
        · change m.getLsbD 13 = false
          exact Bool.eq_false_of_not_eq_true b13
        · change m.getLsbD 14 = true
          exact b14
        · change m.getLsbD 15 = false
          exact Bool.eq_false_of_not_eq_true b15
        · change m.getLsbD 16 = false
          exact Bool.eq_false_of_not_eq_true b16
        · change m.getLsbD 17 = false
          exact Bool.eq_false_of_not_eq_true b17
        · change m.getLsbD 18 = false
          exact Bool.eq_false_of_not_eq_true b18
        · change m.getLsbD 19 = false
          exact Bool.eq_false_of_not_eq_true b19
        · change m.getLsbD 20 = false
          exact Bool.eq_false_of_not_eq_true b20
        · change m.getLsbD 21 = false
          exact Bool.eq_false_of_not_eq_true b21
        · change m.getLsbD 22 = false
          exact Bool.eq_false_of_not_eq_true b22
        · change m.getLsbD 23 = false
          exact Bool.eq_false_of_not_eq_true b23
        · change m.getLsbD 24 = true
          exact b24
        · change m.getLsbD 25 = false
          exact Bool.eq_false_of_not_eq_true b25
        · change m.getLsbD 26 = false
          exact Bool.eq_false_of_not_eq_true b26
        · change m.getLsbD 27 = false
          exact Bool.eq_false_of_not_eq_true b27
        · change m.getLsbD 28 = false
          exact Bool.eq_false_of_not_eq_true b28
        · change m.getLsbD 29 = false
          exact Bool.eq_false_of_not_eq_true b29
        · change m.getLsbD 30 = false
          exact Bool.eq_false_of_not_eq_true b30
        · change m.getLsbD 31 = false
          exact Bool.eq_false_of_not_eq_true b31
        · change m.getLsbD 32 = false
          exact Bool.eq_false_of_not_eq_true b32
        · change m.getLsbD 33 = false
          exact Bool.eq_false_of_not_eq_true b33
        · change m.getLsbD 34 = false
          exact Bool.eq_false_of_not_eq_true b34
        · change m.getLsbD 35 = false
          exact Bool.eq_false_of_not_eq_true b35
        · change m.getLsbD 36 = true
          exact b36
        · change m.getLsbD 37 = false
          exact Bool.eq_false_of_not_eq_true b37
        · change m.getLsbD 38 = false
          exact Bool.eq_false_of_not_eq_true b38
        · change m.getLsbD 39 = false
          exact Bool.eq_false_of_not_eq_true b39
        · change m.getLsbD 40 = false
          exact Bool.eq_false_of_not_eq_true b40
        · change m.getLsbD 41 = false
          exact Bool.eq_false_of_not_eq_true b41
        · change m.getLsbD 42 = false
          exact Bool.eq_false_of_not_eq_true b42
        · change m.getLsbD 43 = false
          exact Bool.eq_false_of_not_eq_true b43
        · change m.getLsbD 44 = false
          exact Bool.eq_false_of_not_eq_true b44
        · change m.getLsbD 45 = false
          exact Bool.eq_false_of_not_eq_true b45
        · change m.getLsbD 46 = false
          exact Bool.eq_false_of_not_eq_true b46
        · change m.getLsbD 47 = false
          exact Bool.eq_false_of_not_eq_true b47
        · change m.getLsbD 48 = true
          exact b48
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfull)))))
  ·
    by_cases b27 : m.getLsbD 27 = true
    ·
      have b21 : ¬ (m.getLsbD 21 = true) := fun h => c136 h b27
      have b22 : ¬ (m.getLsbD 22 = true) := fun h => c146 h b27
      have b23 : ¬ (m.getLsbD 23 = true) := fun h => c154 h b27
      have b25 : ¬ (m.getLsbD 25 = true) := fun h => c164 h b27
      have b26 : ¬ (m.getLsbD 26 = true) := fun h => c166 h b27
      have b6 : ¬ (m.getLsbD 6 = true) := fun h => c257 h b27
      have b13 : ¬ (m.getLsbD 13 = true) := fun h => c267 h b27
      have b20 : ¬ (m.getLsbD 20 = true) := fun h => c275 h b27
      have b34 : ¬ (m.getLsbD 34 = true) := c283 b27
      have b41 : ¬ (m.getLsbD 41 = true) := c285 b27
      have b48 : ¬ (m.getLsbD 48 = true) := c287 b27
      have b0 : ¬ (m.getLsbD 0 = true) := fun h => c329 h b27
      have b2 : ¬ (m.getLsbD 2 = true) := fun h => c338 h b27
      have b4 : ¬ (m.getLsbD 4 = true) := fun h => c347 h b27
      have b14 : ¬ (m.getLsbD 14 = true) := fun h => c360 h b27
      have b16 : ¬ (m.getLsbD 16 = true) := fun h => c369 h b27
      have b18 : ¬ (m.getLsbD 18 = true) := fun h => c378 h b27
      have b42 : ¬ (m.getLsbD 42 = true) := c569 b27
      have b44 : ¬ (m.getLsbD 44 = true) := c570 b27
      have b46 : ¬ (m.getLsbD 46 = true) := c571 b27
      have b36 : ¬ (m.getLsbD 36 = true) := by
        intro h
        rcases c612 h with h | h | h
        · exact (b13 h).elim
        · exact (b34 h).elim
        · exact (b48 h).elim
      have b38 : ¬ (m.getLsbD 38 = true) := by
        intro h
        rcases c618 h with h | h | h
        · exact (b13 h).elim
        · exact (b34 h).elim
        · exact (b48 h).elim
      have b40 : ¬ (m.getLsbD 40 = true) := by
        intro h
        rcases c623 h with h | h | h
        · exact (b13 h).elim
        · exact (b34 h).elim
        · exact (b48 h).elim
      have b3 : ¬ (m.getLsbD 3 = true) := by
        intro h
        rcases c663 h with h | h | h
        · exact (b14 h).elim
        · exact (b16 h).elim
        · exact (b20 h).elim
      have b10 : ¬ (m.getLsbD 10 = true) := by
        intro h
        rcases c666 h with h | h | h
        · exact (b42 h).elim
        · exact (b44 h).elim
        · exact (b48 h).elim
      have b17 : ¬ (m.getLsbD 17 = true) := by
        intro h
        rcases c667 h with h | h | h
        · exact (b0 h).elim
        · exact (b2 h).elim
        · exact (b6 h).elim
      have b31 : ¬ (m.getLsbD 31 = true) := by
        intro h
        rcases c673 h with h | h | h
        · exact (b14 h).elim
        · exact (b16 h).elim
        · exact (b20 h).elim
      have b45 : m.getLsbD 45 = true := by
        rcases c607 b27 with h | h | h
        · exact (b3 h).elim
        · exact (b17 h).elim
        · exact h
      have b30 : ¬ (m.getLsbD 30 = true) := by
        intro h
        rcases c655 h with h | h | h
        · exact (b14 h).elim
        · exact (b17 h).elim
        · exact (b18 h).elim
      have b43 : ¬ (m.getLsbD 43 = true) := fun h => c266 h b45
      have b47 : ¬ (m.getLsbD 47 = true) := c284 b45
      have b8 : ¬ (m.getLsbD 8 = true) := fun h => c488 h b45
      have b11 : ¬ (m.getLsbD 11 = true) := fun h => c500 h b45
      have b12 : ¬ (m.getLsbD 12 = true) := fun h => c505 h b45
      have b39 : ¬ (m.getLsbD 39 = true) := fun h => c531 h b45
      have b33 : ¬ (m.getLsbD 33 = true) := by
        intro h
        rcases c692 h with h | h | h
        · exact (b36 h).elim
        · exact (b39 h).elim
        · exact (b41 h).elim
      by_cases b19 : m.getLsbD 19 = true
      ·
        have b15 : ¬ (m.getLsbD 15 = true) := fun h => c102 h b19
        have b5 : ¬ (m.getLsbD 5 = true) := fun h => c213 h b19
        have b28 : ¬ (m.getLsbD 28 = true) := c410 b19
        have b32 : m.getLsbD 32 = true := by
          rcases c586 b19 with h | h | h
          · exact (b4 h).elim
          · exact (b25 h).elim
          · exact h
        have b1 : m.getLsbD 1 = true := by
          rcases c606 b27 with h | h | h
          · exact h
          · exact (b15 h).elim
          · exact (b43 h).elim
        have b29 : ¬ (m.getLsbD 29 = true) := c49 b1
        have b35 : ¬ (m.getLsbD 35 = true) := c436 b32
        have b7 : m.getLsbD 7 = true := by
          rcases c634 b45 with h | h | h
          · exact h
          · exact (b21 h).elim
          · exact (b35 h).elim
        have b9 : ¬ (m.getLsbD 9 = true) := by
          intro h
          rcases c647 h with h | h | h
          · exact (b35 h).elim
          · exact (b38 h).elim
          · exact (b39 h).elim
        have b37 : m.getLsbD 37 = true := by
          rcases c680 b45 with h | h | h
          · exact (b35 h).elim
          · exact h
          · exact (b41 h).elim
        have hfull : m = 35326240751746 := by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          interval_cases i
          · change m.getLsbD 0 = false
            exact Bool.eq_false_of_not_eq_true b0
          · change m.getLsbD 1 = true
            exact b1
          · change m.getLsbD 2 = false
            exact Bool.eq_false_of_not_eq_true b2
          · change m.getLsbD 3 = false
            exact Bool.eq_false_of_not_eq_true b3
          · change m.getLsbD 4 = false
            exact Bool.eq_false_of_not_eq_true b4
          · change m.getLsbD 5 = false
            exact Bool.eq_false_of_not_eq_true b5
          · change m.getLsbD 6 = false
            exact Bool.eq_false_of_not_eq_true b6
          · change m.getLsbD 7 = true
            exact b7
          · change m.getLsbD 8 = false
            exact Bool.eq_false_of_not_eq_true b8
          · change m.getLsbD 9 = false
            exact Bool.eq_false_of_not_eq_true b9
          · change m.getLsbD 10 = false
            exact Bool.eq_false_of_not_eq_true b10
          · change m.getLsbD 11 = false
            exact Bool.eq_false_of_not_eq_true b11
          · change m.getLsbD 12 = false
            exact Bool.eq_false_of_not_eq_true b12
          · change m.getLsbD 13 = false
            exact Bool.eq_false_of_not_eq_true b13
          · change m.getLsbD 14 = false
            exact Bool.eq_false_of_not_eq_true b14
          · change m.getLsbD 15 = false
            exact Bool.eq_false_of_not_eq_true b15
          · change m.getLsbD 16 = false
            exact Bool.eq_false_of_not_eq_true b16
          · change m.getLsbD 17 = false
            exact Bool.eq_false_of_not_eq_true b17
          · change m.getLsbD 18 = false
            exact Bool.eq_false_of_not_eq_true b18
          · change m.getLsbD 19 = true
            exact b19
          · change m.getLsbD 20 = false
            exact Bool.eq_false_of_not_eq_true b20
          · change m.getLsbD 21 = false
            exact Bool.eq_false_of_not_eq_true b21
          · change m.getLsbD 22 = false
            exact Bool.eq_false_of_not_eq_true b22
          · change m.getLsbD 23 = false
            exact Bool.eq_false_of_not_eq_true b23
          · change m.getLsbD 24 = false
            exact Bool.eq_false_of_not_eq_true b24
          · change m.getLsbD 25 = false
            exact Bool.eq_false_of_not_eq_true b25
          · change m.getLsbD 26 = false
            exact Bool.eq_false_of_not_eq_true b26
          · change m.getLsbD 27 = true
            exact b27
          · change m.getLsbD 28 = false
            exact Bool.eq_false_of_not_eq_true b28
          · change m.getLsbD 29 = false
            exact Bool.eq_false_of_not_eq_true b29
          · change m.getLsbD 30 = false
            exact Bool.eq_false_of_not_eq_true b30
          · change m.getLsbD 31 = false
            exact Bool.eq_false_of_not_eq_true b31
          · change m.getLsbD 32 = true
            exact b32
          · change m.getLsbD 33 = false
            exact Bool.eq_false_of_not_eq_true b33
          · change m.getLsbD 34 = false
            exact Bool.eq_false_of_not_eq_true b34
          · change m.getLsbD 35 = false
            exact Bool.eq_false_of_not_eq_true b35
          · change m.getLsbD 36 = false
            exact Bool.eq_false_of_not_eq_true b36
          · change m.getLsbD 37 = true
            exact b37
          · change m.getLsbD 38 = false
            exact Bool.eq_false_of_not_eq_true b38
          · change m.getLsbD 39 = false
            exact Bool.eq_false_of_not_eq_true b39
          · change m.getLsbD 40 = false
            exact Bool.eq_false_of_not_eq_true b40
          · change m.getLsbD 41 = false
            exact Bool.eq_false_of_not_eq_true b41
          · change m.getLsbD 42 = false
            exact Bool.eq_false_of_not_eq_true b42
          · change m.getLsbD 43 = false
            exact Bool.eq_false_of_not_eq_true b43
          · change m.getLsbD 44 = false
            exact Bool.eq_false_of_not_eq_true b44
          · change m.getLsbD 45 = true
            exact b45
          · change m.getLsbD 46 = false
            exact Bool.eq_false_of_not_eq_true b46
          · change m.getLsbD 47 = false
            exact Bool.eq_false_of_not_eq_true b47
          · change m.getLsbD 48 = false
            exact Bool.eq_false_of_not_eq_true b48
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hfull))))))))
      ·
        have b5 : m.getLsbD 5 = true := by
          rcases c608 b27 with h | h | h
          · exact h
          · exact (b19 h).elim
          · exact (b47 h).elim
        have b15 : m.getLsbD 15 = true := by
          rcases c681 b5 with h | h | h
          · exact h
          · exact (b18 h).elim
          · exact (b20 h).elim
        have b29 : ¬ (m.getLsbD 29 = true) := by
          intro h
          rcases c724 h with h | h | h | h
          · exact (b19 h).elim
          · exact (b20 h).elim
          · exact (b40 h).elim
          · exact (b41 h).elim
        have b1 : ¬ (m.getLsbD 1 = true) := fun h => c18 h b5
        have b28 : ¬ (m.getLsbD 28 = true) := c392 b15
        have b32 : ¬ (m.getLsbD 32 = true) := c396 b15
        have b37 : ¬ (m.getLsbD 37 = true) := by
          intro h
          rcases c615 h with h | h | h
          · exact (b11 h).elim
          · exact (b32 h).elim
          · exact (b46 h).elim
        have b9 : m.getLsbD 9 = true := by
          rcases c635 b45 with h | h | h
          · exact h
          · exact (b23 h).elim
          · exact (b37 h).elim
        have b35 : m.getLsbD 35 = true := by
          rcases c647 b9 with h | h | h
          · exact h
          · exact (b38 h).elim
          · exact (b39 h).elim
        have b7 : ¬ (m.getLsbD 7 = true) := fun h => c19 h b35
        have hfull : m = 35218866078240 := by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          interval_cases i
          · change m.getLsbD 0 = false
            exact Bool.eq_false_of_not_eq_true b0
          · change m.getLsbD 1 = false
            exact Bool.eq_false_of_not_eq_true b1
          · change m.getLsbD 2 = false
            exact Bool.eq_false_of_not_eq_true b2
          · change m.getLsbD 3 = false
            exact Bool.eq_false_of_not_eq_true b3
          · change m.getLsbD 4 = false
            exact Bool.eq_false_of_not_eq_true b4
          · change m.getLsbD 5 = true
            exact b5
          · change m.getLsbD 6 = false
            exact Bool.eq_false_of_not_eq_true b6
          · change m.getLsbD 7 = false
            exact Bool.eq_false_of_not_eq_true b7
          · change m.getLsbD 8 = false
            exact Bool.eq_false_of_not_eq_true b8
          · change m.getLsbD 9 = true
            exact b9
          · change m.getLsbD 10 = false
            exact Bool.eq_false_of_not_eq_true b10
          · change m.getLsbD 11 = false
            exact Bool.eq_false_of_not_eq_true b11
          · change m.getLsbD 12 = false
            exact Bool.eq_false_of_not_eq_true b12
          · change m.getLsbD 13 = false
            exact Bool.eq_false_of_not_eq_true b13
          · change m.getLsbD 14 = false
            exact Bool.eq_false_of_not_eq_true b14
          · change m.getLsbD 15 = true
            exact b15
          · change m.getLsbD 16 = false
            exact Bool.eq_false_of_not_eq_true b16
          · change m.getLsbD 17 = false
            exact Bool.eq_false_of_not_eq_true b17
          · change m.getLsbD 18 = false
            exact Bool.eq_false_of_not_eq_true b18
          · change m.getLsbD 19 = false
            exact Bool.eq_false_of_not_eq_true b19
          · change m.getLsbD 20 = false
            exact Bool.eq_false_of_not_eq_true b20
          · change m.getLsbD 21 = false
            exact Bool.eq_false_of_not_eq_true b21
          · change m.getLsbD 22 = false
            exact Bool.eq_false_of_not_eq_true b22
          · change m.getLsbD 23 = false
            exact Bool.eq_false_of_not_eq_true b23
          · change m.getLsbD 24 = false
            exact Bool.eq_false_of_not_eq_true b24
          · change m.getLsbD 25 = false
            exact Bool.eq_false_of_not_eq_true b25
          · change m.getLsbD 26 = false
            exact Bool.eq_false_of_not_eq_true b26
          · change m.getLsbD 27 = true
            exact b27
          · change m.getLsbD 28 = false
            exact Bool.eq_false_of_not_eq_true b28
          · change m.getLsbD 29 = false
            exact Bool.eq_false_of_not_eq_true b29
          · change m.getLsbD 30 = false
            exact Bool.eq_false_of_not_eq_true b30
          · change m.getLsbD 31 = false
            exact Bool.eq_false_of_not_eq_true b31
          · change m.getLsbD 32 = false
            exact Bool.eq_false_of_not_eq_true b32
          · change m.getLsbD 33 = false
            exact Bool.eq_false_of_not_eq_true b33
          · change m.getLsbD 34 = false
            exact Bool.eq_false_of_not_eq_true b34
          · change m.getLsbD 35 = true
            exact b35
          · change m.getLsbD 36 = false
            exact Bool.eq_false_of_not_eq_true b36
          · change m.getLsbD 37 = false
            exact Bool.eq_false_of_not_eq_true b37
          · change m.getLsbD 38 = false
            exact Bool.eq_false_of_not_eq_true b38
          · change m.getLsbD 39 = false
            exact Bool.eq_false_of_not_eq_true b39
          · change m.getLsbD 40 = false
            exact Bool.eq_false_of_not_eq_true b40
          · change m.getLsbD 41 = false
            exact Bool.eq_false_of_not_eq_true b41
          · change m.getLsbD 42 = false
            exact Bool.eq_false_of_not_eq_true b42
          · change m.getLsbD 43 = false
            exact Bool.eq_false_of_not_eq_true b43
          · change m.getLsbD 44 = false
            exact Bool.eq_false_of_not_eq_true b44
          · change m.getLsbD 45 = true
            exact b45
          · change m.getLsbD 46 = false
            exact Bool.eq_false_of_not_eq_true b46
          · change m.getLsbD 47 = false
            exact Bool.eq_false_of_not_eq_true b47
          · change m.getLsbD 48 = false
            exact Bool.eq_false_of_not_eq_true b48
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfull))))))
    ·
      by_cases b37 : m.getLsbD 37 = true
      ·
        have b2 : ¬ (m.getLsbD 2 = true) := fun h => c93 h b37
        have b9 : ¬ (m.getLsbD 9 = true) := fun h => c103 h b37
        have b16 : ¬ (m.getLsbD 16 = true) := fun h => c111 h b37
        have b23 : ¬ (m.getLsbD 23 = true) := fun h => c117 h b37
        have b30 : ¬ (m.getLsbD 30 = true) := fun h => c121 h b37
        have b44 : ¬ (m.getLsbD 44 = true) := c125 b37
        have b35 : ¬ (m.getLsbD 35 = true) := fun h => c212 h b37
        have b36 : ¬ (m.getLsbD 36 = true) := fun h => c222 h b37
        have b38 : ¬ (m.getLsbD 38 = true) := c232 b37
        have b39 : ¬ (m.getLsbD 39 = true) := c234 b37
        have b40 : ¬ (m.getLsbD 40 = true) := c236 b37
        have b41 : ¬ (m.getLsbD 41 = true) := c238 b37
        have b29 : ¬ (m.getLsbD 29 = true) := fun h => c425 h b37
        have b33 : ¬ (m.getLsbD 33 = true) := fun h => c442 h b37
        have b34 : ¬ (m.getLsbD 34 = true) := fun h => c446 h b37
        have b8 : ¬ (m.getLsbD 8 = true) := fun h => c456 h b37
        have b12 : ¬ (m.getLsbD 12 = true) := fun h => c473 h b37
        have b13 : ¬ (m.getLsbD 13 = true) := fun h => c477 h b37
        have b43 : ¬ (m.getLsbD 43 = true) := c521 b37
        have b47 : ¬ (m.getLsbD 47 = true) := c523 b37
        have b48 : ¬ (m.getLsbD 48 = true) := c524 b37
        have b14 : ¬ (m.getLsbD 14 = true) := by
          intro h
          rcases c573 h with h | h | h
          · exact (b2 h).elim
          · exact (b23 h).elim
          · exact (b30 h).elim
        have b17 : ¬ (m.getLsbD 17 = true) := by
          intro h
          rcases c581 h with h | h | h
          · exact (b2 h).elim
          · exact (b23 h).elim
          · exact (b30 h).elim
        have b18 : ¬ (m.getLsbD 18 = true) := by
          intro h
          rcases c583 h with h | h | h
          · exact (b2 h).elim
          · exact (b23 h).elim
          · exact (b30 h).elim
        have b21 : ¬ (m.getLsbD 21 = true) := by
          intro h
          rcases c591 h with h | h | h
          · exact (b2 h).elim
          · exact (b16 h).elim
          · exact (b44 h).elim
        have b25 : ¬ (m.getLsbD 25 = true) := by
          intro h
          rcases c601 h with h | h | h
          · exact (b2 h).elim
          · exact (b16 h).elim
          · exact (b44 h).elim
        have b45 : ¬ (m.getLsbD 45 = true) := by
          intro h
          rcases c636 h with h | h | h
          · exact (b13 h).elim
          · exact (b27 h).elim
          · exact (b41 h).elim
        have b3 : ¬ (m.getLsbD 3 = true) := by
          intro h
          rcases c664 h with h | h | h
          · exact (b21 h).elim
          · exact (b23 h).elim
          · exact (b27 h).elim
        have b0 : ¬ (m.getLsbD 0 = true) := by
          intro h
          rcases c717 h with h | h | h | h
          · exact (b16 h).elim
          · exact (b17 h).elim
          · exact (b23 h).elim
          · exact (b24 h).elim
        by_cases b20 : m.getLsbD 20 = true
        ·
          have b15 : ¬ (m.getLsbD 15 = true) := fun h => c104 h b20
          have b19 : ¬ (m.getLsbD 19 = true) := fun h => c124 h b20
          have b6 : ¬ (m.getLsbD 6 = true) := fun h => c255 h b20
          have b4 : ¬ (m.getLsbD 4 = true) := fun h => c316 h b20
          have b28 : ¬ (m.getLsbD 28 = true) := c414 b20
          have b32 : ¬ (m.getLsbD 32 = true) := c416 b20
          have b31 : m.getLsbD 31 = true := by
            rcases c589 b20 with h | h | h
            · exact (b3 h).elim
            · exact (b24 h).elim
            · exact h
          have b10 : ¬ (m.getLsbD 10 = true) := fun h => c143 h b31
          have b42 : ¬ (m.getLsbD 42 = true) := by
            intro h
            rcases c628 h with h | h | h
            · exact (b10 h).elim
            · exact (b24 h).elim
            · exact (b38 h).elim
          have b46 : m.getLsbD 46 = true := by
            rcases c659 b37 with h | h | h
            · exact (b42 h).elim
            · exact (b45 h).elim
            · exact h
          have b11 : ¬ (m.getLsbD 11 = true) := fun h => c189 h b46
          have b7 : ¬ (m.getLsbD 7 = true) := fun h => c482 h b46
          have b22 : ¬ (m.getLsbD 22 = true) := fun h => c551 h b46
          have b1 : m.getLsbD 1 = true := by
            rcases c588 b20 with h | h | h
            · exact h
            · exact (b22 h).elim
            · exact (b29 h).elim
          rcases c613 b37 with h | h | h
          · exact (b7 h).elim
          · exact (b28 h).elim
          · exact (b42 h).elim
        ·
          have b31 : ¬ (m.getLsbD 31 = true) := by
            intro h
            rcases c673 h with h | h | h
            · exact (b14 h).elim
            · exact (b16 h).elim
            · exact (b20 h).elim
          have b10 : m.getLsbD 10 = true := by
            rcases c614 b37 with h | h | h
            · exact h
            · exact (b31 h).elim
            · exact (b45 h).elim
          have b42 : m.getLsbD 42 = true := by
            rcases c666 b10 with h | h | h
            · exact h
            · exact (b44 h).elim
            · exact (b48 h).elim
          have b7 : ¬ (m.getLsbD 7 = true) := fun h => c21 h b42
          have b28 : ¬ (m.getLsbD 28 = true) := fun h => c39 h b42
          have b11 : ¬ (m.getLsbD 11 = true) := c72 b10
          have b46 : ¬ (m.getLsbD 46 = true) := c258 b42
          have b22 : ¬ (m.getLsbD 22 = true) := fun h => c547 h b42
          have b26 : ¬ (m.getLsbD 26 = true) := fun h => c565 h b42
          have b32 : m.getLsbD 32 = true := by
            rcases c615 b37 with h | h | h
            · exact (b11 h).elim
            · exact h
            · exact (b46 h).elim
          have b5 : ¬ (m.getLsbD 5 = true) := by
            intro h
            rcases c682 h with h | h | h
            · exact (b22 h).elim
            · exact (b25 h).elim
            · exact (b27 h).elim
          have b19 : ¬ (m.getLsbD 19 = true) := by
            intro h
            rcases c686 h with h | h | h
            · exact (b22 h).elim
            · exact (b25 h).elim
            · exact (b27 h).elim
          have b6 : ¬ (m.getLsbD 6 = true) := by
            intro h
            rcases c700 h with h | h | h
            · exact (b22 h).elim
            · exact (b24 h).elim
            · exact (b26 h).elim
          have b1 : ¬ (m.getLsbD 1 = true) := by
            intro h
            rcases c718 h with h | h | h | h
            · exact (b19 h).elim
            · exact (b20 h).elim
            · exact (b26 h).elim
            · exact (b27 h).elim
          have b4 : ¬ (m.getLsbD 4 = true) := by
            intro h
            rcases c719 h with h | h | h | h
            · exact (b16 h).elim
            · exact (b19 h).elim
            · exact (b23 h).elim
            · exact (b26 h).elim
          have b15 : ¬ (m.getLsbD 15 = true) := fun h => c396 h b32
          have hfull : m = 4539780432896 := by
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            interval_cases i
            · change m.getLsbD 0 = false
              exact Bool.eq_false_of_not_eq_true b0
            · change m.getLsbD 1 = false
              exact Bool.eq_false_of_not_eq_true b1
            · change m.getLsbD 2 = false
              exact Bool.eq_false_of_not_eq_true b2
            · change m.getLsbD 3 = false
              exact Bool.eq_false_of_not_eq_true b3
            · change m.getLsbD 4 = false
              exact Bool.eq_false_of_not_eq_true b4
            · change m.getLsbD 5 = false
              exact Bool.eq_false_of_not_eq_true b5
            · change m.getLsbD 6 = false
              exact Bool.eq_false_of_not_eq_true b6
            · change m.getLsbD 7 = false
              exact Bool.eq_false_of_not_eq_true b7
            · change m.getLsbD 8 = false
              exact Bool.eq_false_of_not_eq_true b8
            · change m.getLsbD 9 = false
              exact Bool.eq_false_of_not_eq_true b9
            · change m.getLsbD 10 = true
              exact b10
            · change m.getLsbD 11 = false
              exact Bool.eq_false_of_not_eq_true b11
            · change m.getLsbD 12 = false
              exact Bool.eq_false_of_not_eq_true b12
            · change m.getLsbD 13 = false
              exact Bool.eq_false_of_not_eq_true b13
            · change m.getLsbD 14 = false
              exact Bool.eq_false_of_not_eq_true b14
            · change m.getLsbD 15 = false
              exact Bool.eq_false_of_not_eq_true b15
            · change m.getLsbD 16 = false
              exact Bool.eq_false_of_not_eq_true b16
            · change m.getLsbD 17 = false
              exact Bool.eq_false_of_not_eq_true b17
            · change m.getLsbD 18 = false
              exact Bool.eq_false_of_not_eq_true b18
            · change m.getLsbD 19 = false
              exact Bool.eq_false_of_not_eq_true b19
            · change m.getLsbD 20 = false
              exact Bool.eq_false_of_not_eq_true b20
            · change m.getLsbD 21 = false
              exact Bool.eq_false_of_not_eq_true b21
            · change m.getLsbD 22 = false
              exact Bool.eq_false_of_not_eq_true b22
            · change m.getLsbD 23 = false
              exact Bool.eq_false_of_not_eq_true b23
            · change m.getLsbD 24 = false
              exact Bool.eq_false_of_not_eq_true b24
            · change m.getLsbD 25 = false
              exact Bool.eq_false_of_not_eq_true b25
            · change m.getLsbD 26 = false
              exact Bool.eq_false_of_not_eq_true b26
            · change m.getLsbD 27 = false
              exact Bool.eq_false_of_not_eq_true b27
            · change m.getLsbD 28 = false
              exact Bool.eq_false_of_not_eq_true b28
            · change m.getLsbD 29 = false
              exact Bool.eq_false_of_not_eq_true b29
            · change m.getLsbD 30 = false
              exact Bool.eq_false_of_not_eq_true b30
            · change m.getLsbD 31 = false
              exact Bool.eq_false_of_not_eq_true b31
            · change m.getLsbD 32 = true
              exact b32
            · change m.getLsbD 33 = false
              exact Bool.eq_false_of_not_eq_true b33
            · change m.getLsbD 34 = false
              exact Bool.eq_false_of_not_eq_true b34
            · change m.getLsbD 35 = false
              exact Bool.eq_false_of_not_eq_true b35
            · change m.getLsbD 36 = false
              exact Bool.eq_false_of_not_eq_true b36
            · change m.getLsbD 37 = true
              exact b37
            · change m.getLsbD 38 = false
              exact Bool.eq_false_of_not_eq_true b38
            · change m.getLsbD 39 = false
              exact Bool.eq_false_of_not_eq_true b39
            · change m.getLsbD 40 = false
              exact Bool.eq_false_of_not_eq_true b40
            · change m.getLsbD 41 = false
              exact Bool.eq_false_of_not_eq_true b41
            · change m.getLsbD 42 = true
              exact b42
            · change m.getLsbD 43 = false
              exact Bool.eq_false_of_not_eq_true b43
            · change m.getLsbD 44 = false
              exact Bool.eq_false_of_not_eq_true b44
            · change m.getLsbD 45 = false
              exact Bool.eq_false_of_not_eq_true b45
            · change m.getLsbD 46 = false
              exact Bool.eq_false_of_not_eq_true b46
            · change m.getLsbD 47 = false
              exact Bool.eq_false_of_not_eq_true b47
            · change m.getLsbD 48 = false
              exact Bool.eq_false_of_not_eq_true b48
          exact Or.inr (Or.inr (Or.inr (Or.inl hfull)))
      ·
        by_cases b26 : m.getLsbD 26 = true
        ·
          have b21 : ¬ (m.getLsbD 21 = true) := fun h => c134 h b26
          have b22 : ¬ (m.getLsbD 22 = true) := fun h => c144 h b26
          have b23 : ¬ (m.getLsbD 23 = true) := fun h => c152 h b26
          have b25 : ¬ (m.getLsbD 25 = true) := fun h => c162 h b26
          have b5 : ¬ (m.getLsbD 5 = true) := fun h => c215 h b26
          have b12 : ¬ (m.getLsbD 12 = true) := fun h => c225 h b26
          have b19 : ¬ (m.getLsbD 19 = true) := fun h => c233 h b26
          have b33 : ¬ (m.getLsbD 33 = true) := c241 b26
          have b40 : ¬ (m.getLsbD 40 = true) := c243 b26
          have b47 : ¬ (m.getLsbD 47 = true) := c245 b26
          have b0 : ¬ (m.getLsbD 0 = true) := fun h => c328 h b26
          have b2 : ¬ (m.getLsbD 2 = true) := fun h => c337 h b26
          have b3 : ¬ (m.getLsbD 3 = true) := fun h => c342 h b26
          have b14 : ¬ (m.getLsbD 14 = true) := fun h => c359 h b26
          have b16 : ¬ (m.getLsbD 16 = true) := fun h => c368 h b26
          have b17 : ¬ (m.getLsbD 17 = true) := fun h => c373 h b26
          have b42 : ¬ (m.getLsbD 42 = true) := c565 b26
          have b44 : ¬ (m.getLsbD 44 = true) := c566 b26
          have b45 : ¬ (m.getLsbD 45 = true) := c567 b26
          have b36 : ¬ (m.getLsbD 36 = true) := by
            intro h
            rcases c611 h with h | h | h
            · exact (b12 h).elim
            · exact (b33 h).elim
            · exact (b47 h).elim
          have b39 : ¬ (m.getLsbD 39 = true) := by
            intro h
            rcases c620 h with h | h | h
            · exact (b12 h).elim
            · exact (b33 h).elim
            · exact (b47 h).elim
          have b41 : ¬ (m.getLsbD 41 = true) := by
            intro h
            rcases c626 h with h | h | h
            · exact (b12 h).elim
            · exact (b33 h).elim
            · exact (b47 h).elim
          have b11 : ¬ (m.getLsbD 11 = true) := by
            intro h
            rcases c722 h with h | h | h | h
            · exact (b37 h).elim
            · exact (b40 h).elim
            · exact (b44 h).elim
            · exact (b47 h).elim
          have b32 : ¬ (m.getLsbD 32 = true) := by
            intro h
            rcases c725 h with h | h | h | h
            · exact (b16 h).elim
            · exact (b19 h).elim
            · exact (b37 h).elim
            · exact (b40 h).elim
          by_cases b38 : m.getLsbD 38 = true
          ·
            have b10 : ¬ (m.getLsbD 10 = true) := fun h => c145 h b38
            have b31 : ¬ (m.getLsbD 31 = true) := fun h => c163 h b38
            have b35 : ¬ (m.getLsbD 35 = true) := fun h => c214 h b38
            have b29 : ¬ (m.getLsbD 29 = true) := fun h => c426 h b38
            have b8 : ¬ (m.getLsbD 8 = true) := fun h => c457 h b38
            have b43 : ¬ (m.getLsbD 43 = true) := c525 b38
            have b46 : ¬ (m.getLsbD 46 = true) := c527 b38
            have b20 : ¬ (m.getLsbD 20 = true) := by
              intro h
              rcases c589 h with h | h | h
              · exact (b3 h).elim
              · exact (b24 h).elim
              · exact (b31 h).elim
            have b48 : ¬ (m.getLsbD 48 = true) := by
              intro h
              rcases c642 h with h | h | h
              · exact (b8 h).elim
              · exact (b22 h).elim
              · exact (b36 h).elim
            have b9 : ¬ (m.getLsbD 9 = true) := by
              intro h
              rcases c648 h with h | h | h
              · exact (b42 h).elim
              · exact (b45 h).elim
              · exact (b46 h).elim
            rcases c677 b38 with h | h | h
            · exact (b42 h).elim
            · exact (b44 h).elim
            · exact (b48 h).elim
          ·
            have b13 : ¬ (m.getLsbD 13 = true) := by
              intro h
              rcases c701 h with h | h | h
              · exact (b36 h).elim
              · exact (b38 h).elim
              · exact (b40 h).elim
            have b34 : ¬ (m.getLsbD 34 = true) := by
              intro h
              rcases c710 h with h | h | h
              · exact (b36 h).elim
              · exact (b38 h).elim
              · exact (b40 h).elim
            have b48 : ¬ (m.getLsbD 48 = true) := by
              intro h
              rcases c716 h with h | h | h
              · exact (b36 h).elim
              · exact (b38 h).elim
              · exact (b40 h).elim
            have b7 : ¬ (m.getLsbD 7 = true) := by
              intro h
              rcases c720 h with h | h | h | h
              · exact (b37 h).elim
              · exact (b38 h).elim
              · exact (b44 h).elim
              · exact (b45 h).elim
            have b8 : ¬ (m.getLsbD 8 = true) := by
              intro h
              rcases c721 h with h | h | h | h
              · exact (b40 h).elim
              · exact (b41 h).elim
              · exact (b47 h).elim
              · exact (b48 h).elim
            have b28 : ¬ (m.getLsbD 28 = true) := by
              intro h
              rcases c723 h with h | h | h | h
              · exact (b16 h).elim
              · exact (b17 h).elim
              · exact (b37 h).elim
              · exact (b38 h).elim
            have b43 : ¬ (m.getLsbD 43 = true) := by
              intro h
              rcases c630 h with h | h | h
              · exact (b13 h).elim
              · exact (b27 h).elim
              · exact (b41 h).elim
            have b10 : ¬ (m.getLsbD 10 = true) := by
              intro h
              rcases c666 h with h | h | h
              · exact (b42 h).elim
              · exact (b44 h).elim
              · exact (b48 h).elim
            have b46 : m.getLsbD 46 = true := by
              rcases c690 b26 with h | h | h
              · exact (b43 h).elim
              · exact h
              · exact (b48 h).elim
            have b4 : ¬ (m.getLsbD 4 = true) := fun h => c179 h b46
            have b18 : ¬ (m.getLsbD 18 = true) := fun h => c197 h b46
            have b35 : ¬ (m.getLsbD 35 = true) := fun h => c513 h b46
            have b9 : m.getLsbD 9 = true := by
              rcases c637 b46 with h | h | h
              · exact h
              · exact (b23 h).elim
              · exact (b37 h).elim
            rcases c647 b9 with h | h | h
            · exact (b35 h).elim
            · exact (b38 h).elim
            · exact (b39 h).elim
        ·
          by_cases b38 : m.getLsbD 38 = true
          ·
            have b3 : ¬ (m.getLsbD 3 = true) := fun h => c135 h b38
            have b10 : ¬ (m.getLsbD 10 = true) := fun h => c145 h b38
            have b17 : ¬ (m.getLsbD 17 = true) := fun h => c153 h b38
            have b31 : ¬ (m.getLsbD 31 = true) := fun h => c163 h b38
            have b45 : ¬ (m.getLsbD 45 = true) := c167 b38
            have b35 : ¬ (m.getLsbD 35 = true) := fun h => c214 h b38
            have b36 : ¬ (m.getLsbD 36 = true) := fun h => c224 h b38
            have b39 : ¬ (m.getLsbD 39 = true) := c240 b38
            have b40 : ¬ (m.getLsbD 40 = true) := c242 b38
            have b41 : ¬ (m.getLsbD 41 = true) := c244 b38
            have b29 : ¬ (m.getLsbD 29 = true) := fun h => c426 h b38
            have b32 : ¬ (m.getLsbD 32 = true) := fun h => c438 h b38
            have b33 : ¬ (m.getLsbD 33 = true) := fun h => c443 h b38
            have b8 : ¬ (m.getLsbD 8 = true) := fun h => c457 h b38
            have b11 : ¬ (m.getLsbD 11 = true) := fun h => c469 h b38
            have b12 : ¬ (m.getLsbD 12 = true) := fun h => c474 h b38
            have b43 : ¬ (m.getLsbD 43 = true) := c525 b38
            have b46 : ¬ (m.getLsbD 46 = true) := c527 b38
            have b47 : ¬ (m.getLsbD 47 = true) := c528 b38
            have b14 : ¬ (m.getLsbD 14 = true) := by
              intro h
              rcases c574 h with h | h | h
              · exact (b3 h).elim
              · exact (b24 h).elim
              · exact (b31 h).elim
            have b16 : ¬ (m.getLsbD 16 = true) := by
              intro h
              rcases c578 h with h | h | h
              · exact (b3 h).elim
              · exact (b24 h).elim
              · exact (b31 h).elim
            have b20 : ¬ (m.getLsbD 20 = true) := by
              intro h
              rcases c589 h with h | h | h
              · exact (b3 h).elim
              · exact (b24 h).elim
              · exact (b31 h).elim
            have b21 : ¬ (m.getLsbD 21 = true) := by
              intro h
              rcases c592 h with h | h | h
              · exact (b3 h).elim
              · exact (b17 h).elim
              · exact (b45 h).elim
            have b23 : ¬ (m.getLsbD 23 = true) := by
              intro h
              rcases c596 h with h | h | h
              · exact (b3 h).elim
              · exact (b17 h).elim
              · exact (b45 h).elim
            have b48 : ¬ (m.getLsbD 48 = true) := by
              intro h
              rcases c644 h with h | h | h
              · exact (b12 h).elim
              · exact (b26 h).elim
              · exact (b40 h).elim
            have b13 : ¬ (m.getLsbD 13 = true) := by
              intro h
              rcases c702 h with h | h | h
              · exact (b43 h).elim
              · exact (b45 h).elim
              · exact (b47 h).elim
            have b0 : ¬ (m.getLsbD 0 = true) := by
              intro h
              rcases c717 h with h | h | h | h
              · exact (b16 h).elim
              · exact (b17 h).elim
              · exact (b23 h).elim
              · exact (b24 h).elim
            have b34 : m.getLsbD 34 = true := by
              rcases c618 b38 with h | h | h
              · exact (b13 h).elim
              · exact h
              · exact (b48 h).elim
            have b28 : ¬ (m.getLsbD 28 = true) := fun h => c178 h b34
            have b30 : ¬ (m.getLsbD 30 = true) := fun h => c196 h b34
            have b6 : ¬ (m.getLsbD 6 = true) := fun h => c259 h b34
            have b18 : ¬ (m.getLsbD 18 = true) := fun h => c409 h b34
            have b22 : ¬ (m.getLsbD 22 = true) := by
              intro h
              rcases c594 h with h | h | h
              · exact (b6 h).elim
              · exact (b20 h).elim
              · exact (b48 h).elim
            have b2 : ¬ (m.getLsbD 2 = true) := by
              intro h
              rcases c645 h with h | h | h
              · exact (b14 h).elim
              · exact (b17 h).elim
              · exact (b18 h).elim
            by_cases b25 : m.getLsbD 25 = true
            ·
              have b4 : ¬ (m.getLsbD 4 = true) := fun h => c173 h b25
              have b1 : ¬ (m.getLsbD 1 = true) := fun h => c334 h b25
              have b15 : ¬ (m.getLsbD 15 = true) := fun h => c365 h b25
              have b42 : ¬ (m.getLsbD 42 = true) := c560 b25
              have b19 : ¬ (m.getLsbD 19 = true) := by
                intro h
                rcases c585 h with h | h | h
                · exact (b1 h).elim
                · exact (b22 h).elim
                · exact (b29 h).elim
              have b44 : m.getLsbD 44 = true := by
                rcases c601 b25 with h | h | h
                · exact (b2 h).elim
                · exact (b16 h).elim
                · exact h
              have b5 : m.getLsbD 5 = true := by
                rcases c602 b25 with h | h | h
                · exact h
                · exact (b19 h).elim
                · exact (b47 h).elim
              have b7 : m.getLsbD 7 = true := by
                rcases c616 b38 with h | h | h
                · exact h
                · exact (b28 h).elim
                · exact (b42 h).elim
              have b9 : ¬ (m.getLsbD 9 = true) := by
                intro h
                rcases c648 h with h | h | h
                · exact (b42 h).elim
                · exact (b45 h).elim
                · exact (b46 h).elim
              rcases c681 b5 with h | h | h
              · exact (b15 h).elim
              · exact (b18 h).elim
              · exact (b20 h).elim
            ·
              have b44 : ¬ (m.getLsbD 44 = true) := by
                intro h
                rcases c633 h with h | h | h
                · exact (b11 h).elim
                · exact (b25 h).elim
                · exact (b39 h).elim
              have b42 : m.getLsbD 42 = true := by
                rcases c677 b38 with h | h | h
                · exact h
                · exact (b44 h).elim
                · exact (b48 h).elim
              have b5 : ¬ (m.getLsbD 5 = true) := by
                intro h
                rcases c682 h with h | h | h
                · exact (b22 h).elim
                · exact (b25 h).elim
                · exact (b27 h).elim
              have b19 : ¬ (m.getLsbD 19 = true) := by
                intro h
                rcases c686 h with h | h | h
                · exact (b22 h).elim
                · exact (b25 h).elim
                · exact (b27 h).elim
              have b15 : m.getLsbD 15 = true := by
                rcases c709 b34 with h | h | h
                · exact h
                · exact (b17 h).elim
                · exact (b19 h).elim
              have b1 : ¬ (m.getLsbD 1 = true) := by
                intro h
                rcases c718 h with h | h | h | h
                · exact (b19 h).elim
                · exact (b20 h).elim
                · exact (b26 h).elim
                · exact (b27 h).elim
              have b4 : ¬ (m.getLsbD 4 = true) := by
                intro h
                rcases c719 h with h | h | h | h
                · exact (b16 h).elim
                · exact (b19 h).elim
                · exact (b23 h).elim
                · exact (b26 h).elim
              have b7 : ¬ (m.getLsbD 7 = true) := fun h => c21 h b42
              rcases c575 b15 with h | h | h
              · exact (b5 h).elim
              · exact (b26 h).elim
              · exact (b33 h).elim
          ·
            by_cases b41 : m.getLsbD 41 = true
            ·
              have b35 : ¬ (m.getLsbD 35 = true) := fun h => c220 h b41
              have b36 : ¬ (m.getLsbD 36 = true) := fun h => c230 h b41
              have b39 : ¬ (m.getLsbD 39 = true) := fun h => c248 h b41
              have b40 : ¬ (m.getLsbD 40 = true) := fun h => c250 h b41
              have b6 : ¬ (m.getLsbD 6 = true) := fun h => c261 h b41
              have b13 : ¬ (m.getLsbD 13 = true) := fun h => c271 h b41
              have b20 : ¬ (m.getLsbD 20 = true) := fun h => c279 h b41
              have b34 : ¬ (m.getLsbD 34 = true) := fun h => c289 h b41
              have b48 : ¬ (m.getLsbD 48 = true) := c293 b41
              have b28 : ¬ (m.getLsbD 28 = true) := fun h => c422 h b41
              have b30 : ¬ (m.getLsbD 30 = true) := fun h => c431 h b41
              have b32 : ¬ (m.getLsbD 32 = true) := fun h => c440 h b41
              have b7 : ¬ (m.getLsbD 7 = true) := fun h => c453 h b41
              have b9 : ¬ (m.getLsbD 9 = true) := fun h => c462 h b41
              have b11 : ¬ (m.getLsbD 11 = true) := fun h => c471 h b41
              have b42 : ¬ (m.getLsbD 42 = true) := c538 b41
              have b44 : ¬ (m.getLsbD 44 = true) := c539 b41
              have b46 : ¬ (m.getLsbD 46 = true) := c540 b41
              have b15 : ¬ (m.getLsbD 15 = true) := by
                intro h
                rcases c576 h with h | h | h
                · exact (b6 h).elim
                · exact (b27 h).elim
                · exact (b34 h).elim
              have b17 : ¬ (m.getLsbD 17 = true) := by
                intro h
                rcases c582 h with h | h | h
                · exact (b6 h).elim
                · exact (b27 h).elim
                · exact (b34 h).elim
              have b19 : ¬ (m.getLsbD 19 = true) := by
                intro h
                rcases c587 h with h | h | h
                · exact (b6 h).elim
                · exact (b27 h).elim
                · exact (b34 h).elim
              have b22 : ¬ (m.getLsbD 22 = true) := by
                intro h
                rcases c594 h with h | h | h
                · exact (b6 h).elim
                · exact (b20 h).elim
                · exact (b48 h).elim
              have b10 : ¬ (m.getLsbD 10 = true) := by
                intro h
                rcases c666 h with h | h | h
                · exact (b42 h).elim
                · exact (b44 h).elim
                · exact (b48 h).elim
              have b45 : ¬ (m.getLsbD 45 = true) := by
                intro h
                rcases c678 h with h | h | h
                · exact (b7 h).elim
                · exact (b9 h).elim
                · exact (b13 h).elim
              have b1 : ¬ (m.getLsbD 1 = true) := by
                intro h
                rcases c718 h with h | h | h | h
                · exact (b19 h).elim
                · exact (b20 h).elim
                · exact (b26 h).elim
                · exact (b27 h).elim
              have b31 : m.getLsbD 31 = true := by
                rcases c625 b41 with h | h | h
                · exact (b10 h).elim
                · exact h
                · exact (b45 h).elim
              have b23 : ¬ (m.getLsbD 23 = true) := by
                intro h
                rcases c654 h with h | h | h
                · exact (b42 h).elim
                · exact (b45 h).elim
                · exact (b46 h).elim
              have b3 : ¬ (m.getLsbD 3 = true) := fun h => c133 h b31
              have b29 : ¬ (m.getLsbD 29 = true) := fun h => c182 h b31
              have b33 : ¬ (m.getLsbD 33 = true) := c200 b31
              have b18 : ¬ (m.getLsbD 18 = true) := fun h => c407 h b31
              have b21 : ¬ (m.getLsbD 21 = true) := by
                intro h
                rcases c592 h with h | h | h
                · exact (b3 h).elim
                · exact (b17 h).elim
                · exact (b45 h).elim
              have b5 : ¬ (m.getLsbD 5 = true) := by
                intro h
                rcases c681 h with h | h | h
                · exact (b15 h).elim
                · exact (b18 h).elim
                · exact (b20 h).elim
              by_cases b25 : m.getLsbD 25 = true
              ·
                have b4 : ¬ (m.getLsbD 4 = true) := fun h => c173 h b25
                have b0 : ¬ (m.getLsbD 0 = true) := fun h => c327 h b25
                have b14 : ¬ (m.getLsbD 14 = true) := fun h => c358 h b25
                have b43 : ¬ (m.getLsbD 43 = true) := c561 b25
                have b16 : ¬ (m.getLsbD 16 = true) := by
                  intro h
                  rcases c577 h with h | h | h
                  · exact (b0 h).elim
                  · exact (b21 h).elim
                  · exact (b28 h).elim
                have b2 : m.getLsbD 2 = true := by
                  rcases c601 b25 with h | h | h
                  · exact h
                  · exact (b16 h).elim
                  · exact (b44 h).elim
                have b47 : m.getLsbD 47 = true := by
                  rcases c602 b25 with h | h | h
                  · exact (b5 h).elim
                  · exact (b19 h).elim
                  · exact h
                have b8 : m.getLsbD 8 = true := by
                  rcases c624 b41 with h | h | h
                  · exact h
                  · exact (b29 h).elim
                  · exact (b43 h).elim
                rcases c645 b2 with h | h | h
                · exact (b14 h).elim
                · exact (b17 h).elim
                · exact (b18 h).elim
              ·
                have b47 : ¬ (m.getLsbD 47 = true) := by
                  intro h
                  rcases c640 h with h | h | h
                  · exact (b11 h).elim
                  · exact (b25 h).elim
                  · exact (b39 h).elim
                have b2 : ¬ (m.getLsbD 2 = true) := by
                  intro h
                  rcases c646 h with h | h | h
                  · exact (b21 h).elim
                  · exact (b24 h).elim
                  · exact (b25 h).elim
                have b16 : ¬ (m.getLsbD 16 = true) := by
                  intro h
                  rcases c650 h with h | h | h
                  · exact (b21 h).elim
                  · exact (b24 h).elim
                  · exact (b25 h).elim
                have b14 : m.getLsbD 14 = true := by
                  rcases c673 b31 with h | h | h
                  · exact h
                  · exact (b16 h).elim
                  · exact (b20 h).elim
                have b43 : m.getLsbD 43 = true := by
                  rcases c713 b41 with h | h | h
                  · exact h
                  · exact (b45 h).elim
                  · exact (b47 h).elim
                have b0 : ¬ (m.getLsbD 0 = true) := by
                  intro h
                  rcases c717 h with h | h | h | h
                  · exact (b16 h).elim
                  · exact (b17 h).elim
                  · exact (b23 h).elim
                  · exact (b24 h).elim
                have b4 : ¬ (m.getLsbD 4 = true) := by
                  intro h
                  rcases c719 h with h | h | h | h
                  · exact (b16 h).elim
                  · exact (b19 h).elim
                  · exact (b23 h).elim
                  · exact (b26 h).elim
                have b8 : ¬ (m.getLsbD 8 = true) := fun h => c63 h b43
                rcases c573 b14 with h | h | h
                · exact (b2 h).elim
                · exact (b23 h).elim
                · exact (b30 h).elim
            ·
              by_cases b23 : m.getLsbD 23 = true
              ·
                have b2 : ¬ (m.getLsbD 2 = true) := fun h => c89 h b23
                have b9 : ¬ (m.getLsbD 9 = true) := fun h => c99 h b23
                have b16 : ¬ (m.getLsbD 16 = true) := fun h => c107 h b23
                have b30 : ¬ (m.getLsbD 30 = true) := c115 b23
                have b44 : ¬ (m.getLsbD 44 = true) := c119 b23
                have b21 : ¬ (m.getLsbD 21 = true) := fun h => c128 h b23
                have b22 : ¬ (m.getLsbD 22 = true) := fun h => c138 h b23
                have b25 : ¬ (m.getLsbD 25 = true) := c150 b23
                have b1 : ¬ (m.getLsbD 1 = true) := fun h => c332 h b23
                have b5 : ¬ (m.getLsbD 5 = true) := fun h => c349 h b23
                have b6 : ¬ (m.getLsbD 6 = true) := fun h => c353 h b23
                have b15 : ¬ (m.getLsbD 15 = true) := fun h => c363 h b23
                have b19 : ¬ (m.getLsbD 19 = true) := fun h => c380 h b23
                have b20 : ¬ (m.getLsbD 20 = true) := fun h => c384 h b23
                have b43 : ¬ (m.getLsbD 43 = true) := c552 b23
                have b47 : ¬ (m.getLsbD 47 = true) := c554 b23
                have b48 : ¬ (m.getLsbD 48 = true) := c555 b23
                have b35 : ¬ (m.getLsbD 35 = true) := by
                  intro h
                  rcases c609 h with h | h | h
                  · exact (b9 h).elim
                  · exact (b30 h).elim
                  · exact (b44 h).elim
                have b39 : ¬ (m.getLsbD 39 = true) := by
                  intro h
                  rcases c619 h with h | h | h
                  · exact (b9 h).elim
                  · exact (b30 h).elim
                  · exact (b44 h).elim
                have b10 : ¬ (m.getLsbD 10 = true) := by
                  intro h
                  rcases c665 h with h | h | h
                  · exact (b35 h).elim
                  · exact (b37 h).elim
                  · exact (b41 h).elim
                have b31 : ¬ (m.getLsbD 31 = true) := by
                  intro h
                  rcases c674 h with h | h | h
                  · exact (b35 h).elim
                  · exact (b37 h).elim
                  · exact (b41 h).elim
                have b45 : ¬ (m.getLsbD 45 = true) := by
                  intro h
                  rcases c680 h with h | h | h
                  · exact (b35 h).elim
                  · exact (b37 h).elim
                  · exact (b41 h).elim
                have b13 : ¬ (m.getLsbD 13 = true) := by
                  intro h
                  rcases c702 h with h | h | h
                  · exact (b43 h).elim
                  · exact (b45 h).elim
                  · exact (b47 h).elim
                have b7 : ¬ (m.getLsbD 7 = true) := by
                  intro h
                  rcases c720 h with h | h | h | h
                  · exact (b37 h).elim
                  · exact (b38 h).elim
                  · exact (b44 h).elim
                  · exact (b45 h).elim
                have b42 : ¬ (m.getLsbD 42 = true) := by
                  intro h
                  rcases c628 h with h | h | h
                  · exact (b10 h).elim
                  · exact (b24 h).elim
                  · exact (b38 h).elim
                have b46 : m.getLsbD 46 = true := by
                  rcases c654 b23 with h | h | h
                  · exact (b42 h).elim
                  · exact (b45 h).elim
                  · exact h
                have b4 : ¬ (m.getLsbD 4 = true) := fun h => c179 h b46
                have b11 : ¬ (m.getLsbD 11 = true) := fun h => c189 h b46
                have b18 : ¬ (m.getLsbD 18 = true) := fun h => c197 h b46
                have b32 : ¬ (m.getLsbD 32 = true) := fun h => c207 h b46
                have b8 : ¬ (m.getLsbD 8 = true) := fun h => c489 h b46
                have b36 : ¬ (m.getLsbD 36 = true) := fun h => c520 h b46
                have b12 : ¬ (m.getLsbD 12 = true) := by
                  intro h
                  rcases c683 h with h | h | h
                  · exact (b36 h).elim
                  · exact (b39 h).elim
                  · exact (b41 h).elim
                have b33 : ¬ (m.getLsbD 33 = true) := by
                  intro h
                  rcases c691 h with h | h | h
                  · exact (b15 h).elim
                  · exact (b18 h).elim
                  · exact (b20 h).elim
                have b40 : ¬ (m.getLsbD 40 = true) := by
                  intro h
                  rcases c693 h with h | h | h
                  · exact (b8 h).elim
                  · exact (b11 h).elim
                  · exact (b13 h).elim
                have b34 : ¬ (m.getLsbD 34 = true) := by
                  intro h
                  rcases c710 h with h | h | h
                  · exact (b36 h).elim
                  · exact (b38 h).elim
                  · exact (b40 h).elim
                have b29 : ¬ (m.getLsbD 29 = true) := by
                  intro h
                  rcases c724 h with h | h | h | h
                  · exact (b19 h).elim
                  · exact (b20 h).elim
                  · exact (b40 h).elim
                  · exact (b41 h).elim
                have b17 : ¬ (m.getLsbD 17 = true) := by
                  intro h
                  rcases c582 h with h | h | h
                  · exact (b6 h).elim
                  · exact (b27 h).elim
                  · exact (b34 h).elim
                have b3 : m.getLsbD 3 = true := by
                  rcases c596 b23 with h | h | h
                  · exact h
                  · exact (b17 h).elim
                  · exact (b45 h).elim
                rcases c638 b46 with h | h | h
                · exact (b12 h).elim
                · exact (b26 h).elim
                · exact (b40 h).elim
              ·
                by_cases b40 : m.getLsbD 40 = true
                ·
                  have b35 : ¬ (m.getLsbD 35 = true) := fun h => c218 h b40
                  have b5 : ¬ (m.getLsbD 5 = true) := fun h => c219 h b40
                  have b36 : ¬ (m.getLsbD 36 = true) := fun h => c228 h b40
                  have b12 : ¬ (m.getLsbD 12 = true) := fun h => c229 h b40
                  have b19 : ¬ (m.getLsbD 19 = true) := fun h => c237 h b40
                  have b39 : ¬ (m.getLsbD 39 = true) := fun h => c246 h b40
                  have b33 : ¬ (m.getLsbD 33 = true) := fun h => c247 h b40
                  have b47 : ¬ (m.getLsbD 47 = true) := c251 b40
                  have b28 : ¬ (m.getLsbD 28 = true) := fun h => c421 h b40
                  have b30 : ¬ (m.getLsbD 30 = true) := fun h => c430 h b40
                  have b31 : ¬ (m.getLsbD 31 = true) := fun h => c435 h b40
                  have b7 : ¬ (m.getLsbD 7 = true) := fun h => c452 h b40
                  have b9 : ¬ (m.getLsbD 9 = true) := fun h => c461 h b40
                  have b10 : ¬ (m.getLsbD 10 = true) := fun h => c466 h b40
                  have b42 : ¬ (m.getLsbD 42 = true) := c534 b40
                  have b44 : ¬ (m.getLsbD 44 = true) := c535 b40
                  have b45 : ¬ (m.getLsbD 45 = true) := c536 b40
                  have b15 : ¬ (m.getLsbD 15 = true) := by
                    intro h
                    rcases c575 h with h | h | h
                    · exact (b5 h).elim
                    · exact (b26 h).elim
                    · exact (b33 h).elim
                  have b18 : ¬ (m.getLsbD 18 = true) := by
                    intro h
                    rcases c584 h with h | h | h
                    · exact (b5 h).elim
                    · exact (b26 h).elim
                    · exact (b33 h).elim
                  have b20 : ¬ (m.getLsbD 20 = true) := by
                    intro h
                    rcases c590 h with h | h | h
                    · exact (b5 h).elim
                    · exact (b26 h).elim
                    · exact (b33 h).elim
                  have b22 : ¬ (m.getLsbD 22 = true) := by
                    intro h
                    rcases c593 h with h | h | h
                    · exact (b5 h).elim
                    · exact (b19 h).elim
                    · exact (b47 h).elim
                  have b25 : ¬ (m.getLsbD 25 = true) := by
                    intro h
                    rcases c602 h with h | h | h
                    · exact (b5 h).elim
                    · exact (b19 h).elim
                    · exact (b47 h).elim
                  have b46 : ¬ (m.getLsbD 46 = true) := by
                    intro h
                    rcases c637 h with h | h | h
                    · exact (b9 h).elim
                    · exact (b23 h).elim
                    · exact (b37 h).elim
                  have b48 : ¬ (m.getLsbD 48 = true) := by
                    intro h
                    rcases c643 h with h | h | h
                    · exact (b10 h).elim
                    · exact (b24 h).elim
                    · exact (b38 h).elim
                  have b43 : m.getLsbD 43 = true := by
                    rcases c695 b40 with h | h | h
                    · exact h
                    · exact (b46 h).elim
                    · exact (b48 h).elim
                  have b6 : ¬ (m.getLsbD 6 = true) := by
                    intro h
                    rcases c700 h with h | h | h
                    · exact (b22 h).elim
                    · exact (b24 h).elim
                    · exact (b26 h).elim
                  have b1 : ¬ (m.getLsbD 1 = true) := by
                    intro h
                    rcases c718 h with h | h | h | h
                    · exact (b19 h).elim
                    · exact (b20 h).elim
                    · exact (b26 h).elim
                    · exact (b27 h).elim
                  have b8 : ¬ (m.getLsbD 8 = true) := fun h => c63 h b43
                  have b29 : ¬ (m.getLsbD 29 = true) := fun h => c81 h b43
                  have b11 : ¬ (m.getLsbD 11 = true) := fun h => c499 h b43
                  have b21 : ¬ (m.getLsbD 21 = true) := fun h => c543 h b43
                  have b32 : m.getLsbD 32 = true := by
                    rcases c622 b40 with h | h | h
                    · exact (b11 h).elim
                    · exact h
                    · exact (b46 h).elim
                  have b13 : m.getLsbD 13 = true := by
                    rcases c630 b43 with h | h | h
                    · exact h
                    · exact (b27 h).elim
                    · exact (b41 h).elim
                  have b2 : ¬ (m.getLsbD 2 = true) := by
                    intro h
                    rcases c646 h with h | h | h
                    · exact (b21 h).elim
                    · exact (b24 h).elim
                    · exact (b25 h).elim
                  have b16 : ¬ (m.getLsbD 16 = true) := by
                    intro h
                    rcases c650 h with h | h | h
                    · exact (b21 h).elim
                    · exact (b24 h).elim
                    · exact (b25 h).elim
                  have b3 : ¬ (m.getLsbD 3 = true) := by
                    intro h
                    rcases c664 h with h | h | h
                    · exact (b21 h).elim
                    · exact (b23 h).elim
                    · exact (b27 h).elim
                  have b17 : ¬ (m.getLsbD 17 = true) := by
                    intro h
                    rcases c668 h with h | h | h
                    · exact (b21 h).elim
                    · exact (b23 h).elim
                    · exact (b27 h).elim
                  have b34 : ¬ (m.getLsbD 34 = true) := by
                    intro h
                    rcases c709 h with h | h | h
                    · exact (b15 h).elim
                    · exact (b17 h).elim
                    · exact (b19 h).elim
                  have b0 : ¬ (m.getLsbD 0 = true) := by
                    intro h
                    rcases c717 h with h | h | h | h
                    · exact (b16 h).elim
                    · exact (b17 h).elim
                    · exact (b23 h).elim
                    · exact (b24 h).elim
                  have b4 : ¬ (m.getLsbD 4 = true) := by
                    intro h
                    rcases c719 h with h | h | h | h
                    · exact (b16 h).elim
                    · exact (b19 h).elim
                    · exact (b23 h).elim
                    · exact (b26 h).elim
                  have b14 : ¬ (m.getLsbD 14 = true) := fun h => c389 h b32
                  have hfull : m = 9899899625472 := by
                    apply BitVec.eq_of_getLsbD_eq
                    intro i hi
                    interval_cases i
                    · change m.getLsbD 0 = false
                      exact Bool.eq_false_of_not_eq_true b0
                    · change m.getLsbD 1 = false
                      exact Bool.eq_false_of_not_eq_true b1
                    · change m.getLsbD 2 = false
                      exact Bool.eq_false_of_not_eq_true b2
                    · change m.getLsbD 3 = false
                      exact Bool.eq_false_of_not_eq_true b3
                    · change m.getLsbD 4 = false
                      exact Bool.eq_false_of_not_eq_true b4
                    · change m.getLsbD 5 = false
                      exact Bool.eq_false_of_not_eq_true b5
                    · change m.getLsbD 6 = false
                      exact Bool.eq_false_of_not_eq_true b6
                    · change m.getLsbD 7 = false
                      exact Bool.eq_false_of_not_eq_true b7
                    · change m.getLsbD 8 = false
                      exact Bool.eq_false_of_not_eq_true b8
                    · change m.getLsbD 9 = false
                      exact Bool.eq_false_of_not_eq_true b9
                    · change m.getLsbD 10 = false
                      exact Bool.eq_false_of_not_eq_true b10
                    · change m.getLsbD 11 = false
                      exact Bool.eq_false_of_not_eq_true b11
                    · change m.getLsbD 12 = false
                      exact Bool.eq_false_of_not_eq_true b12
                    · change m.getLsbD 13 = true
                      exact b13
                    · change m.getLsbD 14 = false
                      exact Bool.eq_false_of_not_eq_true b14
                    · change m.getLsbD 15 = false
                      exact Bool.eq_false_of_not_eq_true b15
                    · change m.getLsbD 16 = false
                      exact Bool.eq_false_of_not_eq_true b16
                    · change m.getLsbD 17 = false
                      exact Bool.eq_false_of_not_eq_true b17
                    · change m.getLsbD 18 = false
                      exact Bool.eq_false_of_not_eq_true b18
                    · change m.getLsbD 19 = false
                      exact Bool.eq_false_of_not_eq_true b19
                    · change m.getLsbD 20 = false
                      exact Bool.eq_false_of_not_eq_true b20
                    · change m.getLsbD 21 = false
                      exact Bool.eq_false_of_not_eq_true b21
                    · change m.getLsbD 22 = false
                      exact Bool.eq_false_of_not_eq_true b22
                    · change m.getLsbD 23 = false
                      exact Bool.eq_false_of_not_eq_true b23
                    · change m.getLsbD 24 = false
                      exact Bool.eq_false_of_not_eq_true b24
                    · change m.getLsbD 25 = false
                      exact Bool.eq_false_of_not_eq_true b25
                    · change m.getLsbD 26 = false
                      exact Bool.eq_false_of_not_eq_true b26
                    · change m.getLsbD 27 = false
                      exact Bool.eq_false_of_not_eq_true b27
                    · change m.getLsbD 28 = false
                      exact Bool.eq_false_of_not_eq_true b28
                    · change m.getLsbD 29 = false
                      exact Bool.eq_false_of_not_eq_true b29
                    · change m.getLsbD 30 = false
                      exact Bool.eq_false_of_not_eq_true b30
                    · change m.getLsbD 31 = false
                      exact Bool.eq_false_of_not_eq_true b31
                    · change m.getLsbD 32 = true
                      exact b32
                    · change m.getLsbD 33 = false
                      exact Bool.eq_false_of_not_eq_true b33
                    · change m.getLsbD 34 = false
                      exact Bool.eq_false_of_not_eq_true b34
                    · change m.getLsbD 35 = false
                      exact Bool.eq_false_of_not_eq_true b35
                    · change m.getLsbD 36 = false
                      exact Bool.eq_false_of_not_eq_true b36
                    · change m.getLsbD 37 = false
                      exact Bool.eq_false_of_not_eq_true b37
                    · change m.getLsbD 38 = false
                      exact Bool.eq_false_of_not_eq_true b38
                    · change m.getLsbD 39 = false
                      exact Bool.eq_false_of_not_eq_true b39
                    · change m.getLsbD 40 = true
                      exact b40
                    · change m.getLsbD 41 = false
                      exact Bool.eq_false_of_not_eq_true b41
                    · change m.getLsbD 42 = false
                      exact Bool.eq_false_of_not_eq_true b42
                    · change m.getLsbD 43 = true
                      exact b43
                    · change m.getLsbD 44 = false
                      exact Bool.eq_false_of_not_eq_true b44
                    · change m.getLsbD 45 = false
                      exact Bool.eq_false_of_not_eq_true b45
                    · change m.getLsbD 46 = false
                      exact Bool.eq_false_of_not_eq_true b46
                    · change m.getLsbD 47 = false
                      exact Bool.eq_false_of_not_eq_true b47
                    · change m.getLsbD 48 = false
                      exact Bool.eq_false_of_not_eq_true b48
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfull))))
                ·
                  by_cases b21 : m.getLsbD 21 = true
                  ·
                    have b0 : ¬ (m.getLsbD 0 = true) := fun h => c5 h b21
                    have b7 : ¬ (m.getLsbD 7 = true) := fun h => c15 h b21
                    have b14 : ¬ (m.getLsbD 14 = true) := fun h => c23 h b21
                    have b28 : ¬ (m.getLsbD 28 = true) := c31 b21
                    have b35 : ¬ (m.getLsbD 35 = true) := c33 b21
                    have b42 : ¬ (m.getLsbD 42 = true) := c35 b21
                    have b22 : ¬ (m.getLsbD 22 = true) := c126 b21
                    have b25 : ¬ (m.getLsbD 25 = true) := c132 b21
                    have b1 : ¬ (m.getLsbD 1 = true) := fun h => c330 h b21
                    have b4 : ¬ (m.getLsbD 4 = true) := fun h => c343 h b21
                    have b5 : ¬ (m.getLsbD 5 = true) := fun h => c348 h b21
                    have b6 : ¬ (m.getLsbD 6 = true) := fun h => c352 h b21
                    have b15 : ¬ (m.getLsbD 15 = true) := fun h => c361 h b21
                    have b18 : ¬ (m.getLsbD 18 = true) := fun h => c374 h b21
                    have b19 : ¬ (m.getLsbD 19 = true) := fun h => c379 h b21
                    have b20 : ¬ (m.getLsbD 20 = true) := fun h => c383 h b21
                    have b43 : ¬ (m.getLsbD 43 = true) := c543 b21
                    have b46 : ¬ (m.getLsbD 46 = true) := c544 b21
                    have b47 : ¬ (m.getLsbD 47 = true) := c545 b21
                    have b48 : ¬ (m.getLsbD 48 = true) := c546 b21
                    have b10 : ¬ (m.getLsbD 10 = true) := by
                      intro h
                      rcases c665 h with h | h | h
                      · exact (b35 h).elim
                      · exact (b37 h).elim
                      · exact (b41 h).elim
                    have b31 : ¬ (m.getLsbD 31 = true) := by
                      intro h
                      rcases c674 h with h | h | h
                      · exact (b35 h).elim
                      · exact (b37 h).elim
                      · exact (b41 h).elim
                    have b45 : ¬ (m.getLsbD 45 = true) := by
                      intro h
                      rcases c680 h with h | h | h
                      · exact (b35 h).elim
                      · exact (b37 h).elim
                      · exact (b41 h).elim
                    have b12 : ¬ (m.getLsbD 12 = true) := by
                      intro h
                      rcases c684 h with h | h | h
                      · exact (b43 h).elim
                      · exact (b46 h).elim
                      · exact (b48 h).elim
                    have b33 : ¬ (m.getLsbD 33 = true) := by
                      intro h
                      rcases c691 h with h | h | h
                      · exact (b15 h).elim
                      · exact (b18 h).elim
                      · exact (b20 h).elim
                    have b13 : ¬ (m.getLsbD 13 = true) := by
                      intro h
                      rcases c702 h with h | h | h
                      · exact (b43 h).elim
                      · exact (b45 h).elim
                      · exact (b47 h).elim
                    have b8 : ¬ (m.getLsbD 8 = true) := by
                      intro h
                      rcases c721 h with h | h | h | h
                      · exact (b40 h).elim
                      · exact (b41 h).elim
                      · exact (b47 h).elim
                      · exact (b48 h).elim
                    have b29 : ¬ (m.getLsbD 29 = true) := by
                      intro h
                      rcases c724 h with h | h | h | h
                      · exact (b19 h).elim
                      · exact (b20 h).elim
                      · exact (b40 h).elim
                      · exact (b41 h).elim
                    have b36 : ¬ (m.getLsbD 36 = true) := by
                      intro h
                      rcases c611 h with h | h | h
                      · exact (b12 h).elim
                      · exact (b33 h).elim
                      · exact (b47 h).elim
                    have b39 : ¬ (m.getLsbD 39 = true) := by
                      intro h
                      rcases c620 h with h | h | h
                      · exact (b12 h).elim
                      · exact (b33 h).elim
                      · exact (b47 h).elim
                    have b44 : ¬ (m.getLsbD 44 = true) := by
                      intro h
                      rcases c632 h with h | h | h
                      · exact (b10 h).elim
                      · exact (b24 h).elim
                      · exact (b38 h).elim
                    have b9 : ¬ (m.getLsbD 9 = true) := by
                      intro h
                      rcases c647 h with h | h | h
                      · exact (b35 h).elim
                      · exact (b38 h).elim
                      · exact (b39 h).elim
                    have b30 : ¬ (m.getLsbD 30 = true) := by
                      intro h
                      rcases c656 h with h | h | h
                      · exact (b35 h).elim
                      · exact (b38 h).elim
                      · exact (b39 h).elim
                    have b34 : ¬ (m.getLsbD 34 = true) := by
                      intro h
                      rcases c710 h with h | h | h
                      · exact (b36 h).elim
                      · exact (b38 h).elim
                      · exact (b40 h).elim
                    have b11 : ¬ (m.getLsbD 11 = true) := by
                      intro h
                      rcases c722 h with h | h | h | h
                      · exact (b37 h).elim
                      · exact (b40 h).elim
                      · exact (b44 h).elim
                      · exact (b47 h).elim
                    have b17 : ¬ (m.getLsbD 17 = true) := by
                      intro h
                      rcases c582 h with h | h | h
                      · exact (b6 h).elim
                      · exact (b27 h).elim
                      · exact (b34 h).elim
                    have b3 : m.getLsbD 3 = true := by
                      rcases c592 b21 with h | h | h
                      · exact h
                      · exact (b17 h).elim
                      · exact (b45 h).elim
                    have b2 : ¬ (m.getLsbD 2 = true) := by
                      intro h
                      rcases c645 h with h | h | h
                      · exact (b14 h).elim
                      · exact (b17 h).elim
                      · exact (b18 h).elim
                    have b16 : m.getLsbD 16 = true := by
                      rcases c663 b3 with h | h | h
                      · exact (b14 h).elim
                      · exact h
                      · exact (b20 h).elim
                    have b32 : m.getLsbD 32 = true := by
                      rcases c579 b16 with h | h | h
                      · exact (b4 h).elim
                      · exact (b25 h).elim
                      · exact h
                    have hfull : m = 4297129992 := by
                      apply BitVec.eq_of_getLsbD_eq
                      intro i hi
                      interval_cases i
                      · change m.getLsbD 0 = false
                        exact Bool.eq_false_of_not_eq_true b0
                      · change m.getLsbD 1 = false
                        exact Bool.eq_false_of_not_eq_true b1
                      · change m.getLsbD 2 = false
                        exact Bool.eq_false_of_not_eq_true b2
                      · change m.getLsbD 3 = true
                        exact b3
                      · change m.getLsbD 4 = false
                        exact Bool.eq_false_of_not_eq_true b4
                      · change m.getLsbD 5 = false
                        exact Bool.eq_false_of_not_eq_true b5
                      · change m.getLsbD 6 = false
                        exact Bool.eq_false_of_not_eq_true b6
                      · change m.getLsbD 7 = false
                        exact Bool.eq_false_of_not_eq_true b7
                      · change m.getLsbD 8 = false
                        exact Bool.eq_false_of_not_eq_true b8
                      · change m.getLsbD 9 = false
                        exact Bool.eq_false_of_not_eq_true b9
                      · change m.getLsbD 10 = false
                        exact Bool.eq_false_of_not_eq_true b10
                      · change m.getLsbD 11 = false
                        exact Bool.eq_false_of_not_eq_true b11
                      · change m.getLsbD 12 = false
                        exact Bool.eq_false_of_not_eq_true b12
                      · change m.getLsbD 13 = false
                        exact Bool.eq_false_of_not_eq_true b13
                      · change m.getLsbD 14 = false
                        exact Bool.eq_false_of_not_eq_true b14
                      · change m.getLsbD 15 = false
                        exact Bool.eq_false_of_not_eq_true b15
                      · change m.getLsbD 16 = true
                        exact b16
                      · change m.getLsbD 17 = false
                        exact Bool.eq_false_of_not_eq_true b17
                      · change m.getLsbD 18 = false
                        exact Bool.eq_false_of_not_eq_true b18
                      · change m.getLsbD 19 = false
                        exact Bool.eq_false_of_not_eq_true b19
                      · change m.getLsbD 20 = false
                        exact Bool.eq_false_of_not_eq_true b20
                      · change m.getLsbD 21 = true
                        exact b21
                      · change m.getLsbD 22 = false
                        exact Bool.eq_false_of_not_eq_true b22
                      · change m.getLsbD 23 = false
                        exact Bool.eq_false_of_not_eq_true b23
                      · change m.getLsbD 24 = false
                        exact Bool.eq_false_of_not_eq_true b24
                      · change m.getLsbD 25 = false
                        exact Bool.eq_false_of_not_eq_true b25
                      · change m.getLsbD 26 = false
                        exact Bool.eq_false_of_not_eq_true b26
                      · change m.getLsbD 27 = false
                        exact Bool.eq_false_of_not_eq_true b27
                      · change m.getLsbD 28 = false
                        exact Bool.eq_false_of_not_eq_true b28
                      · change m.getLsbD 29 = false
                        exact Bool.eq_false_of_not_eq_true b29
                      · change m.getLsbD 30 = false
                        exact Bool.eq_false_of_not_eq_true b30
                      · change m.getLsbD 31 = false
                        exact Bool.eq_false_of_not_eq_true b31
                      · change m.getLsbD 32 = true
                        exact b32
                      · change m.getLsbD 33 = false
                        exact Bool.eq_false_of_not_eq_true b33
                      · change m.getLsbD 34 = false
                        exact Bool.eq_false_of_not_eq_true b34
                      · change m.getLsbD 35 = false
                        exact Bool.eq_false_of_not_eq_true b35
                      · change m.getLsbD 36 = false
                        exact Bool.eq_false_of_not_eq_true b36
                      · change m.getLsbD 37 = false
                        exact Bool.eq_false_of_not_eq_true b37
                      · change m.getLsbD 38 = false
                        exact Bool.eq_false_of_not_eq_true b38
                      · change m.getLsbD 39 = false
                        exact Bool.eq_false_of_not_eq_true b39
                      · change m.getLsbD 40 = false
                        exact Bool.eq_false_of_not_eq_true b40
                      · change m.getLsbD 41 = false
                        exact Bool.eq_false_of_not_eq_true b41
                      · change m.getLsbD 42 = false
                        exact Bool.eq_false_of_not_eq_true b42
                      · change m.getLsbD 43 = false
                        exact Bool.eq_false_of_not_eq_true b43
                      · change m.getLsbD 44 = false
                        exact Bool.eq_false_of_not_eq_true b44
                      · change m.getLsbD 45 = false
                        exact Bool.eq_false_of_not_eq_true b45
                      · change m.getLsbD 46 = false
                        exact Bool.eq_false_of_not_eq_true b46
                      · change m.getLsbD 47 = false
                        exact Bool.eq_false_of_not_eq_true b47
                      · change m.getLsbD 48 = false
                        exact Bool.eq_false_of_not_eq_true b48
                    exact Or.inr (Or.inl hfull)
                  ·
                    have b3 : ¬ (m.getLsbD 3 = true) := by
                      intro h
                      rcases c664 h with h | h | h
                      · exact (b21 h).elim
                      · exact (b23 h).elim
                      · exact (b27 h).elim
                    have b17 : ¬ (m.getLsbD 17 = true) := by
                      intro h
                      rcases c668 h with h | h | h
                      · exact (b21 h).elim
                      · exact (b23 h).elim
                      · exact (b27 h).elim
                    have b45 : ¬ (m.getLsbD 45 = true) := by
                      intro h
                      rcases c679 h with h | h | h
                      · exact (b21 h).elim
                      · exact (b23 h).elim
                      · exact (b27 h).elim
                    by_cases b36 : m.getLsbD 36 = true
                    ·
                      have b1 : ¬ (m.getLsbD 1 = true) := fun h => c51 h b36
                      have b8 : ¬ (m.getLsbD 8 = true) := fun h => c61 h b36
                      have b15 : ¬ (m.getLsbD 15 = true) := fun h => c69 h b36
                      have b22 : ¬ (m.getLsbD 22 = true) := fun h => c75 h b36
                      have b29 : ¬ (m.getLsbD 29 = true) := fun h => c79 h b36
                      have b43 : ¬ (m.getLsbD 43 = true) := c83 b36
                      have b35 : ¬ (m.getLsbD 35 = true) := fun h => c210 h b36
                      have b39 : ¬ (m.getLsbD 39 = true) := c226 b36
                      have b28 : ¬ (m.getLsbD 28 = true) := fun h => c419 h b36
                      have b30 : ¬ (m.getLsbD 30 = true) := fun h => c428 h b36
                      have b31 : ¬ (m.getLsbD 31 = true) := fun h => c432 h b36
                      have b32 : ¬ (m.getLsbD 32 = true) := fun h => c437 h b36
                      have b7 : ¬ (m.getLsbD 7 = true) := fun h => c450 h b36
                      have b9 : ¬ (m.getLsbD 9 = true) := fun h => c459 h b36
                      have b10 : ¬ (m.getLsbD 10 = true) := fun h => c463 h b36
                      have b11 : ¬ (m.getLsbD 11 = true) := fun h => c468 h b36
                      have b42 : ¬ (m.getLsbD 42 = true) := c516 b36
                      have b44 : ¬ (m.getLsbD 44 = true) := c518 b36
                      have b46 : ¬ (m.getLsbD 46 = true) := c520 b36
                      have b14 : ¬ (m.getLsbD 14 = true) := by
                        intro h
                        rcases c574 h with h | h | h
                        · exact (b3 h).elim
                        · exact (b24 h).elim
                        · exact (b31 h).elim
                      have b16 : ¬ (m.getLsbD 16 = true) := by
                        intro h
                        rcases c578 h with h | h | h
                        · exact (b3 h).elim
                        · exact (b24 h).elim
                        · exact (b31 h).elim
                      have b19 : ¬ (m.getLsbD 19 = true) := by
                        intro h
                        rcases c585 h with h | h | h
                        · exact (b1 h).elim
                        · exact (b22 h).elim
                        · exact (b29 h).elim
                      have b20 : ¬ (m.getLsbD 20 = true) := by
                        intro h
                        rcases c588 h with h | h | h
                        · exact (b1 h).elim
                        · exact (b22 h).elim
                        · exact (b29 h).elim
                      have b48 : ¬ (m.getLsbD 48 = true) := by
                        intro h
                        rcases c643 h with h | h | h
                        · exact (b10 h).elim
                        · exact (b24 h).elim
                        · exact (b38 h).elim
                      have b12 : ¬ (m.getLsbD 12 = true) := by
                        intro h
                        rcases c684 h with h | h | h
                        · exact (b43 h).elim
                        · exact (b46 h).elim
                        · exact (b48 h).elim
                      have b6 : ¬ (m.getLsbD 6 = true) := by
                        intro h
                        rcases c699 h with h | h | h
                        · exact (b15 h).elim
                        · exact (b17 h).elim
                        · exact (b19 h).elim
                      have b34 : ¬ (m.getLsbD 34 = true) := by
                        intro h
                        rcases c709 h with h | h | h
                        · exact (b15 h).elim
                        · exact (b17 h).elim
                        · exact (b19 h).elim
                      have b0 : ¬ (m.getLsbD 0 = true) := by
                        intro h
                        rcases c717 h with h | h | h | h
                        · exact (b16 h).elim
                        · exact (b17 h).elim
                        · exact (b23 h).elim
                        · exact (b24 h).elim
                      have b4 : ¬ (m.getLsbD 4 = true) := by
                        intro h
                        rcases c719 h with h | h | h | h
                        · exact (b16 h).elim
                        · exact (b19 h).elim
                        · exact (b23 h).elim
                        · exact (b26 h).elim
                      have b13 : m.getLsbD 13 = true := by
                        rcases c612 b36 with h | h | h
                        · exact h
                        · exact (b34 h).elim
                        · exact (b48 h).elim
                      have b47 : m.getLsbD 47 = true := by
                        rcases c702 b13 with h | h | h
                        · exact (b43 h).elim
                        · exact (b45 h).elim
                        · exact h
                      have b5 : ¬ (m.getLsbD 5 = true) := fun h => c221 h b47
                      have b33 : ¬ (m.getLsbD 33 = true) := fun h => c249 h b47
                      have b18 : ¬ (m.getLsbD 18 = true) := by
                        intro h
                        rcases c584 h with h | h | h
                        · exact (b5 h).elim
                        · exact (b26 h).elim
                        · exact (b33 h).elim
                      have b25 : m.getLsbD 25 = true := by
                        rcases c640 b47 with h | h | h
                        · exact (b11 h).elim
                        · exact h
                        · exact (b39 h).elim
                      have b2 : ¬ (m.getLsbD 2 = true) := by
                        intro h
                        rcases c645 h with h | h | h
                        · exact (b14 h).elim
                        · exact (b17 h).elim
                        · exact (b18 h).elim
                      rcases c601 b25 with h | h | h
                      · exact (b2 h).elim
                      · exact (b16 h).elim
                      · exact (b44 h).elim
                    ·
                      have b13 : ¬ (m.getLsbD 13 = true) := by
                        intro h
                        rcases c701 h with h | h | h
                        · exact (b36 h).elim
                        · exact (b38 h).elim
                        · exact (b40 h).elim
                      have b34 : ¬ (m.getLsbD 34 = true) := by
                        intro h
                        rcases c710 h with h | h | h
                        · exact (b36 h).elim
                        · exact (b38 h).elim
                        · exact (b40 h).elim
                      have b48 : ¬ (m.getLsbD 48 = true) := by
                        intro h
                        rcases c716 h with h | h | h
                        · exact (b36 h).elim
                        · exact (b38 h).elim
                        · exact (b40 h).elim
                      have b43 : ¬ (m.getLsbD 43 = true) := by
                        intro h
                        rcases c630 h with h | h | h
                        · exact (b13 h).elim
                        · exact (b27 h).elim
                        · exact (b41 h).elim
                      have b47 : ¬ (m.getLsbD 47 = true) := by
                        intro h
                        rcases c641 h with h | h | h
                        · exact (b13 h).elim
                        · exact (b27 h).elim
                        · exact (b41 h).elim
                      have b8 : ¬ (m.getLsbD 8 = true) := by
                        intro h
                        rcases c721 h with h | h | h | h
                        · exact (b40 h).elim
                        · exact (b41 h).elim
                        · exact (b47 h).elim
                        · exact (b48 h).elim
                      by_cases b16 : m.getLsbD 16 = true
                      ·
                        have b14 : ¬ (m.getLsbD 14 = true) := fun h => c86 h b16
                        have b2 : ¬ (m.getLsbD 2 = true) := fun h => c87 h b16
                        have b15 : ¬ (m.getLsbD 15 = true) := fun h => c96 h b16
                        have b9 : ¬ (m.getLsbD 9 = true) := fun h => c97 h b16
                        have b18 : ¬ (m.getLsbD 18 = true) := c108 b16
                        have b30 : ¬ (m.getLsbD 30 = true) := c109 b16
                        have b19 : ¬ (m.getLsbD 19 = true) := c110 b16
                        have b20 : ¬ (m.getLsbD 20 = true) := c112 b16
                        have b44 : ¬ (m.getLsbD 44 = true) := c113 b16
                        have b1 : ¬ (m.getLsbD 1 = true) := fun h => c301 h b16
                        have b5 : ¬ (m.getLsbD 5 = true) := fun h => c318 h b16
                        have b6 : ¬ (m.getLsbD 6 = true) := fun h => c322 h b16
                        have b22 : ¬ (m.getLsbD 22 = true) := c366 b16
                        have b29 : ¬ (m.getLsbD 29 = true) := c397 b16
                        have b33 : ¬ (m.getLsbD 33 = true) := c399 b16
                        have b31 : m.getLsbD 31 = true := by
                          rcases c578 b16 with h | h | h
                          · exact (b3 h).elim
                          · exact (b24 h).elim
                          · exact h
                        have b25 : ¬ (m.getLsbD 25 = true) := by
                          intro h
                          rcases c602 h with h | h | h
                          · exact (b5 h).elim
                          · exact (b19 h).elim
                          · exact (b47 h).elim
                        have b35 : ¬ (m.getLsbD 35 = true) := by
                          intro h
                          rcases c609 h with h | h | h
                          · exact (b9 h).elim
                          · exact (b30 h).elim
                          · exact (b44 h).elim
                        have b39 : ¬ (m.getLsbD 39 = true) := by
                          intro h
                          rcases c619 h with h | h | h
                          · exact (b9 h).elim
                          · exact (b30 h).elim
                          · exact (b44 h).elim
                        have b42 : ¬ (m.getLsbD 42 = true) := by
                          intro h
                          rcases c627 h with h | h | h
                          · exact (b9 h).elim
                          · exact (b23 h).elim
                          · exact (b37 h).elim
                        have b46 : ¬ (m.getLsbD 46 = true) := by
                          intro h
                          rcases c637 h with h | h | h
                          · exact (b9 h).elim
                          · exact (b23 h).elim
                          · exact (b37 h).elim
                        rcases c650 b16 with h | h | h
                        · exact (b21 h).elim
                        · exact (b24 h).elim
                        · exact (b25 h).elim
                      ·
                        have b0 : ¬ (m.getLsbD 0 = true) := by
                          intro h
                          rcases c717 h with h | h | h | h
                          · exact (b16 h).elim
                          · exact (b17 h).elim
                          · exact (b23 h).elim
                          · exact (b24 h).elim
                        have b28 : ¬ (m.getLsbD 28 = true) := by
                          intro h
                          rcases c723 h with h | h | h | h
                          · exact (b16 h).elim
                          · exact (b17 h).elim
                          · exact (b37 h).elim
                          · exact (b38 h).elim
                        by_cases b19 : m.getLsbD 19 = true
                        ·
                          have b14 : ¬ (m.getLsbD 14 = true) := fun h => c92 h b19
                          have b15 : ¬ (m.getLsbD 15 = true) := fun h => c102 h b19
                          have b18 : ¬ (m.getLsbD 18 = true) := fun h => c120 h b19
                          have b20 : ¬ (m.getLsbD 20 = true) := c124 b19
                          have b5 : ¬ (m.getLsbD 5 = true) := fun h => c213 h b19
                          have b12 : ¬ (m.getLsbD 12 = true) := fun h => c223 h b19
                          have b33 : ¬ (m.getLsbD 33 = true) := c235 b19
                          have b2 : ¬ (m.getLsbD 2 = true) := fun h => c306 h b19
                          have b30 : ¬ (m.getLsbD 30 = true) := c411 b19
                          have b31 : ¬ (m.getLsbD 31 = true) := c412 b19
                          have b6 : m.getLsbD 6 = true := by
                            rcases c587 b19 with h | h | h
                            · exact h
                            · exact (b27 h).elim
                            · exact (b34 h).elim
                          have b39 : ¬ (m.getLsbD 39 = true) := by
                            intro h
                            rcases c620 h with h | h | h
                            · exact (b12 h).elim
                            · exact (b33 h).elim
                            · exact (b47 h).elim
                          have b46 : ¬ (m.getLsbD 46 = true) := by
                            intro h
                            rcases c638 h with h | h | h
                            · exact (b12 h).elim
                            · exact (b26 h).elim
                            · exact (b40 h).elim
                          have b22 : m.getLsbD 22 = true := by
                            rcases c700 b6 with h | h | h
                            · exact h
                            · exact (b24 h).elim
                            · exact (b26 h).elim
                          have b1 : ¬ (m.getLsbD 1 = true) := fun h => c20 h b6
                          have b4 : ¬ (m.getLsbD 4 = true) := fun h => c38 h b6
                          have b29 : ¬ (m.getLsbD 29 = true) := c73 b22
                          have b25 : ¬ (m.getLsbD 25 = true) := c142 b22
                          have b42 : ¬ (m.getLsbD 42 = true) := c547 b22
                          have b44 : ¬ (m.getLsbD 44 = true) := c549 b22
                          have b32 : m.getLsbD 32 = true := by
                            rcases c586 b19 with h | h | h
                            · exact (b4 h).elim
                            · exact (b25 h).elim
                            · exact h
                          have b9 : ¬ (m.getLsbD 9 = true) := by
                            intro h
                            rcases c648 h with h | h | h
                            · exact (b42 h).elim
                            · exact (b45 h).elim
                            · exact (b46 h).elim
                          have b10 : ¬ (m.getLsbD 10 = true) := by
                            intro h
                            rcases c666 h with h | h | h
                            · exact (b42 h).elim
                            · exact (b44 h).elim
                            · exact (b48 h).elim
                          have b7 : ¬ (m.getLsbD 7 = true) := by
                            intro h
                            rcases c720 h with h | h | h | h
                            · exact (b37 h).elim
                            · exact (b38 h).elim
                            · exact (b44 h).elim
                            · exact (b45 h).elim
                          have b11 : ¬ (m.getLsbD 11 = true) := by
                            intro h
                            rcases c722 h with h | h | h | h
                            · exact (b37 h).elim
                            · exact (b40 h).elim
                            · exact (b44 h).elim
                            · exact (b47 h).elim
                          have b35 : ¬ (m.getLsbD 35 = true) := c436 b32
                          have hfull : m = 4299685952 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            interval_cases i
                            · change m.getLsbD 0 = false
                              exact Bool.eq_false_of_not_eq_true b0
                            · change m.getLsbD 1 = false
                              exact Bool.eq_false_of_not_eq_true b1
                            · change m.getLsbD 2 = false
                              exact Bool.eq_false_of_not_eq_true b2
                            · change m.getLsbD 3 = false
                              exact Bool.eq_false_of_not_eq_true b3
                            · change m.getLsbD 4 = false
                              exact Bool.eq_false_of_not_eq_true b4
                            · change m.getLsbD 5 = false
                              exact Bool.eq_false_of_not_eq_true b5
                            · change m.getLsbD 6 = true
                              exact b6
                            · change m.getLsbD 7 = false
                              exact Bool.eq_false_of_not_eq_true b7
                            · change m.getLsbD 8 = false
                              exact Bool.eq_false_of_not_eq_true b8
                            · change m.getLsbD 9 = false
                              exact Bool.eq_false_of_not_eq_true b9
                            · change m.getLsbD 10 = false
                              exact Bool.eq_false_of_not_eq_true b10
                            · change m.getLsbD 11 = false
                              exact Bool.eq_false_of_not_eq_true b11
                            · change m.getLsbD 12 = false
                              exact Bool.eq_false_of_not_eq_true b12
                            · change m.getLsbD 13 = false
                              exact Bool.eq_false_of_not_eq_true b13
                            · change m.getLsbD 14 = false
                              exact Bool.eq_false_of_not_eq_true b14
                            · change m.getLsbD 15 = false
                              exact Bool.eq_false_of_not_eq_true b15
                            · change m.getLsbD 16 = false
                              exact Bool.eq_false_of_not_eq_true b16
                            · change m.getLsbD 17 = false
                              exact Bool.eq_false_of_not_eq_true b17
                            · change m.getLsbD 18 = false
                              exact Bool.eq_false_of_not_eq_true b18
                            · change m.getLsbD 19 = true
                              exact b19
                            · change m.getLsbD 20 = false
                              exact Bool.eq_false_of_not_eq_true b20
                            · change m.getLsbD 21 = false
                              exact Bool.eq_false_of_not_eq_true b21
                            · change m.getLsbD 22 = true
                              exact b22
                            · change m.getLsbD 23 = false
                              exact Bool.eq_false_of_not_eq_true b23
                            · change m.getLsbD 24 = false
                              exact Bool.eq_false_of_not_eq_true b24
                            · change m.getLsbD 25 = false
                              exact Bool.eq_false_of_not_eq_true b25
                            · change m.getLsbD 26 = false
                              exact Bool.eq_false_of_not_eq_true b26
                            · change m.getLsbD 27 = false
                              exact Bool.eq_false_of_not_eq_true b27
                            · change m.getLsbD 28 = false
                              exact Bool.eq_false_of_not_eq_true b28
                            · change m.getLsbD 29 = false
                              exact Bool.eq_false_of_not_eq_true b29
                            · change m.getLsbD 30 = false
                              exact Bool.eq_false_of_not_eq_true b30
                            · change m.getLsbD 31 = false
                              exact Bool.eq_false_of_not_eq_true b31
                            · change m.getLsbD 32 = true
                              exact b32
                            · change m.getLsbD 33 = false
                              exact Bool.eq_false_of_not_eq_true b33
                            · change m.getLsbD 34 = false
                              exact Bool.eq_false_of_not_eq_true b34
                            · change m.getLsbD 35 = false
                              exact Bool.eq_false_of_not_eq_true b35
                            · change m.getLsbD 36 = false
                              exact Bool.eq_false_of_not_eq_true b36
                            · change m.getLsbD 37 = false
                              exact Bool.eq_false_of_not_eq_true b37
                            · change m.getLsbD 38 = false
                              exact Bool.eq_false_of_not_eq_true b38
                            · change m.getLsbD 39 = false
                              exact Bool.eq_false_of_not_eq_true b39
                            · change m.getLsbD 40 = false
                              exact Bool.eq_false_of_not_eq_true b40
                            · change m.getLsbD 41 = false
                              exact Bool.eq_false_of_not_eq_true b41
                            · change m.getLsbD 42 = false
                              exact Bool.eq_false_of_not_eq_true b42
                            · change m.getLsbD 43 = false
                              exact Bool.eq_false_of_not_eq_true b43
                            · change m.getLsbD 44 = false
                              exact Bool.eq_false_of_not_eq_true b44
                            · change m.getLsbD 45 = false
                              exact Bool.eq_false_of_not_eq_true b45
                            · change m.getLsbD 46 = false
                              exact Bool.eq_false_of_not_eq_true b46
                            · change m.getLsbD 47 = false
                              exact Bool.eq_false_of_not_eq_true b47
                            · change m.getLsbD 48 = false
                              exact Bool.eq_false_of_not_eq_true b48
                          exact Or.inr (Or.inr (Or.inl hfull))
                        ·
                          have b4 : ¬ (m.getLsbD 4 = true) := by
                            intro h
                            rcases c719 h with h | h | h | h
                            · exact (b16 h).elim
                            · exact (b19 h).elim
                            · exact (b23 h).elim
                            · exact (b26 h).elim
                          have b32 : ¬ (m.getLsbD 32 = true) := by
                            intro h
                            rcases c725 h with h | h | h | h
                            · exact (b16 h).elim
                            · exact (b19 h).elim
                            · exact (b37 h).elim
                            · exact (b40 h).elim
                          by_cases b20 : m.getLsbD 20 = true
                          ·
                            have b14 : ¬ (m.getLsbD 14 = true) := fun h => c94 h b20
                            have b15 : ¬ (m.getLsbD 15 = true) := fun h => c104 h b20
                            have b18 : ¬ (m.getLsbD 18 = true) := fun h => c122 h b20
                            have b6 : ¬ (m.getLsbD 6 = true) := fun h => c255 h b20
                            have b2 : ¬ (m.getLsbD 2 = true) := fun h => c307 h b20
                            have b25 : ¬ (m.getLsbD 25 = true) := c385 b20
                            have b30 : ¬ (m.getLsbD 30 = true) := c415 b20
                            have b31 : m.getLsbD 31 = true := by
                              rcases c589 b20 with h | h | h
                              · exact (b3 h).elim
                              · exact (b24 h).elim
                              · exact h
                            have b44 : ¬ (m.getLsbD 44 = true) := by
                              intro h
                              rcases c661 h with h | h | h
                              · exact (b21 h).elim
                              · exact (b24 h).elim
                              · exact (b25 h).elim
                            have b35 : m.getLsbD 35 = true := by
                              rcases c674 b31 with h | h | h
                              · exact h
                              · exact (b37 h).elim
                              · exact (b41 h).elim
                            have b22 : m.getLsbD 22 = true := by
                              rcases c704 b20 with h | h | h
                              · exact h
                              · exact (b24 h).elim
                              · exact (b26 h).elim
                            have b7 : ¬ (m.getLsbD 7 = true) := by
                              intro h
                              rcases c720 h with h | h | h | h
                              · exact (b37 h).elim
                              · exact (b38 h).elim
                              · exact (b44 h).elim
                              · exact (b45 h).elim
                            have b11 : ¬ (m.getLsbD 11 = true) := by
                              intro h
                              rcases c722 h with h | h | h | h
                              · exact (b37 h).elim
                              · exact (b40 h).elim
                              · exact (b44 h).elim
                              · exact (b47 h).elim
                            have b42 : ¬ (m.getLsbD 42 = true) := c41 b35
                            have b1 : ¬ (m.getLsbD 1 = true) := fun h => c47 h b22
                            have b29 : ¬ (m.getLsbD 29 = true) := c73 b22
                            have b10 : ¬ (m.getLsbD 10 = true) := fun h => c143 h b31
                            have b33 : ¬ (m.getLsbD 33 = true) := c200 b31
                            have b39 : ¬ (m.getLsbD 39 = true) := c216 b35
                            have b12 : ¬ (m.getLsbD 12 = true) := fun h => c472 h b35
                            have b46 : ¬ (m.getLsbD 46 = true) := c513 b35
                            have b5 : m.getLsbD 5 = true := by
                              rcases c590 b20 with h | h | h
                              · exact h
                              · exact (b26 h).elim
                              · exact (b33 h).elim
                            have b9 : m.getLsbD 9 = true := by
                              rcases c609 b35 with h | h | h
                              · exact h
                              · exact (b30 h).elim
                              · exact (b44 h).elim
                            rcases c648 b9 with h | h | h
                            · exact (b42 h).elim
                            · exact (b45 h).elim
                            · exact (b46 h).elim
                          ·
                            have b1 : ¬ (m.getLsbD 1 = true) := by
                              intro h
                              rcases c718 h with h | h | h | h
                              · exact (b19 h).elim
                              · exact (b20 h).elim
                              · exact (b26 h).elim
                              · exact (b27 h).elim
                            have b29 : ¬ (m.getLsbD 29 = true) := by
                              intro h
                              rcases c724 h with h | h | h | h
                              · exact (b19 h).elim
                              · exact (b20 h).elim
                              · exact (b40 h).elim
                              · exact (b41 h).elim
                            by_cases b44 : m.getLsbD 44 = true
                            ·
                              have b2 : ¬ (m.getLsbD 2 = true) := fun h => c95 h b44
                              have b9 : ¬ (m.getLsbD 9 = true) := fun h => c105 h b44
                              have b30 : ¬ (m.getLsbD 30 = true) := fun h => c123 h b44
                              have b42 : ¬ (m.getLsbD 42 = true) := fun h => c254 h b44
                              have b46 : ¬ (m.getLsbD 46 = true) := c276 b44
                              have b12 : ¬ (m.getLsbD 12 = true) := fun h => c504 h b44
                              have b22 : ¬ (m.getLsbD 22 = true) := fun h => c549 h b44
                              have b14 : ¬ (m.getLsbD 14 = true) := by
                                intro h
                                rcases c573 h with h | h | h
                                · exact (b2 h).elim
                                · exact (b23 h).elim
                                · exact (b30 h).elim
                              have b18 : ¬ (m.getLsbD 18 = true) := by
                                intro h
                                rcases c583 h with h | h | h
                                · exact (b2 h).elim
                                · exact (b23 h).elim
                                · exact (b30 h).elim
                              have b10 : m.getLsbD 10 = true := by
                                rcases c632 b44 with h | h | h
                                · exact h
                                · exact (b24 h).elim
                                · exact (b38 h).elim
                              have b25 : m.getLsbD 25 = true := by
                                rcases c661 b44 with h | h | h
                                · exact (b21 h).elim
                                · exact (b24 h).elim
                                · exact h
                              have b35 : m.getLsbD 35 = true := by
                                rcases c665 b10 with h | h | h
                                · exact h
                                · exact (b37 h).elim
                                · exact (b41 h).elim
                              have b31 : ¬ (m.getLsbD 31 = true) := by
                                intro h
                                rcases c673 h with h | h | h
                                · exact (b14 h).elim
                                · exact (b16 h).elim
                                · exact (b20 h).elim
                              have b6 : ¬ (m.getLsbD 6 = true) := by
                                intro h
                                rcases c700 h with h | h | h
                                · exact (b22 h).elim
                                · exact (b24 h).elim
                                · exact (b26 h).elim
                              have b7 : ¬ (m.getLsbD 7 = true) := fun h => c19 h b35
                              have b11 : ¬ (m.getLsbD 11 = true) := c72 b10
                              have b39 : ¬ (m.getLsbD 39 = true) := c201 b25
                              have b15 : ¬ (m.getLsbD 15 = true) := fun h => c365 h b25
                              have b33 : ¬ (m.getLsbD 33 = true) := fun h => c441 h b35
                              have b5 : m.getLsbD 5 = true := by
                                rcases c602 b25 with h | h | h
                                · exact h
                                · exact (b19 h).elim
                                · exact (b47 h).elim
                              rcases c681 b5 with h | h | h
                              · exact (b15 h).elim
                              · exact (b18 h).elim
                              · exact (b20 h).elim
                            ·
                              have b7 : ¬ (m.getLsbD 7 = true) := by
                                intro h
                                rcases c720 h with h | h | h | h
                                · exact (b37 h).elim
                                · exact (b38 h).elim
                                · exact (b44 h).elim
                                · exact (b45 h).elim
                              have b11 : ¬ (m.getLsbD 11 = true) := by
                                intro h
                                rcases c722 h with h | h | h | h
                                · exact (b37 h).elim
                                · exact (b40 h).elim
                                · exact (b44 h).elim
                                · exact (b47 h).elim
                              by_cases b18 : m.getLsbD 18 = true
                              ·
                                have b14 : ¬ (m.getLsbD 14 = true) := fun h => c90 h b18
                                have b15 : ¬ (m.getLsbD 15 = true) := fun h => c100 h b18
                                have b25 : ¬ (m.getLsbD 25 = true) := c191 b18
                                have b39 : ¬ (m.getLsbD 39 = true) := c195 b18
                                have b46 : ¬ (m.getLsbD 46 = true) := c197 b18
                                have b6 : ¬ (m.getLsbD 6 = true) := fun h => c323 h b18
                                have b22 : ¬ (m.getLsbD 22 = true) := c375 b18
                                have b31 : ¬ (m.getLsbD 31 = true) := c407 b18
                                have b2 : ¬ (m.getLsbD 2 = true) := by
                                  intro h
                                  rcases c646 h with h | h | h
                                  · exact (b21 h).elim
                                  · exact (b24 h).elim
                                  · exact (b25 h).elim
                                have b5 : ¬ (m.getLsbD 5 = true) := by
                                  intro h
                                  rcases c682 h with h | h | h
                                  · exact (b22 h).elim
                                  · exact (b25 h).elim
                                  · exact (b27 h).elim
                                have b12 : ¬ (m.getLsbD 12 = true) := by
                                  intro h
                                  rcases c683 h with h | h | h
                                  · exact (b36 h).elim
                                  · exact (b39 h).elim
                                  · exact (b41 h).elim
                                have b33 : ¬ (m.getLsbD 33 = true) := by
                                  intro h
                                  rcases c692 h with h | h | h
                                  · exact (b36 h).elim
                                  · exact (b39 h).elim
                                  · exact (b41 h).elim
                                have b30 : m.getLsbD 30 = true := by
                                  rcases c583 b18 with h | h | h
                                  · exact (b2 h).elim
                                  · exact (b23 h).elim
                                  · exact h
                                rcases c584 b18 with h | h | h
                                · exact (b5 h).elim
                                · exact (b26 h).elim
                                · exact (b33 h).elim
                              ·
                                by_cases b14 : m.getLsbD 14 = true
                                ·
                                  have b35 : ¬ (m.getLsbD 35 = true) := c27 b14
                                  have b42 : ¬ (m.getLsbD 42 = true) := c29 b14
                                  have b15 : ¬ (m.getLsbD 15 = true) := c84 b14
                                  have b5 : ¬ (m.getLsbD 5 = true) := fun h => c317 h b14
                                  have b6 : ¬ (m.getLsbD 6 = true) := fun h => c321 h b14
                                  have b22 : ¬ (m.getLsbD 22 = true) := c357 b14
                                  have b25 : ¬ (m.getLsbD 25 = true) := c358 b14
                                  have b33 : ¬ (m.getLsbD 33 = true) := c390 b14
                                  have b31 : m.getLsbD 31 = true := by
                                    rcases c574 b14 with h | h | h
                                    · exact (b3 h).elim
                                    · exact (b24 h).elim
                                    · exact h
                                  have b2 : ¬ (m.getLsbD 2 = true) := by
                                    intro h
                                    rcases c646 h with h | h | h
                                    · exact (b21 h).elim
                                    · exact (b24 h).elim
                                    · exact (b25 h).elim
                                  have b10 : ¬ (m.getLsbD 10 = true) := by
                                    intro h
                                    rcases c665 h with h | h | h
                                    · exact (b35 h).elim
                                    · exact (b37 h).elim
                                    · exact (b41 h).elim
                                  rcases c674 b31 with h | h | h
                                  · exact (b35 h).elim
                                  · exact (b37 h).elim
                                  · exact (b41 h).elim
                                ·
                                  have b2 : ¬ (m.getLsbD 2 = true) := by
                                    intro h
                                    rcases c645 h with h | h | h
                                    · exact (b14 h).elim
                                    · exact (b17 h).elim
                                    · exact (b18 h).elim
                                  have b30 : ¬ (m.getLsbD 30 = true) := by
                                    intro h
                                    rcases c655 h with h | h | h
                                    · exact (b14 h).elim
                                    · exact (b17 h).elim
                                    · exact (b18 h).elim
                                  have b31 : ¬ (m.getLsbD 31 = true) := by
                                    intro h
                                    rcases c673 h with h | h | h
                                    · exact (b14 h).elim
                                    · exact (b16 h).elim
                                    · exact (b20 h).elim
                                  have b25 : ¬ (m.getLsbD 25 = true) := by
                                    intro h
                                    rcases c601 h with h | h | h
                                    · exact (b2 h).elim
                                    · exact (b16 h).elim
                                    · exact (b44 h).elim
                                  by_cases b35 : m.getLsbD 35 = true
                                  ·
                                    have b42 : ¬ (m.getLsbD 42 = true) := c41 b35
                                    have b39 : ¬ (m.getLsbD 39 = true) := c216 b35
                                    have b33 : ¬ (m.getLsbD 33 = true) := fun h => c441 h b35
                                    have b12 : ¬ (m.getLsbD 12 = true) := fun h => c472 h b35
                                    have b46 : ¬ (m.getLsbD 46 = true) := c513 b35
                                    have b9 : m.getLsbD 9 = true := by
                                      rcases c609 b35 with h | h | h
                                      · exact h
                                      · exact (b30 h).elim
                                      · exact (b44 h).elim
                                    have b10 : m.getLsbD 10 = true := by
                                      rcases c610 b35 with h | h | h
                                      · exact h
                                      · exact (b31 h).elim
                                      · exact (b45 h).elim
                                    rcases c648 b9 with h | h | h
                                    · exact (b42 h).elim
                                    · exact (b45 h).elim
                                    · exact (b46 h).elim
                                  ·
                                    have b10 : ¬ (m.getLsbD 10 = true) := by
                                      intro h
                                      rcases c665 h with h | h | h
                                      · exact (b35 h).elim
                                      · exact (b37 h).elim
                                      · exact (b41 h).elim
                                    have b42 : ¬ (m.getLsbD 42 = true) := by
                                      intro h
                                      rcases c628 h with h | h | h
                                      · exact (b10 h).elim
                                      · exact (b24 h).elim
                                      · exact (b38 h).elim
                                    by_cases b5 : m.getLsbD 5 = true
                                    ·
                                      have b6 : ¬ (m.getLsbD 6 = true) := c40 b5
                                      have b12 : ¬ (m.getLsbD 12 = true) := c211 b5
                                      have b33 : ¬ (m.getLsbD 33 = true) := c217 b5
                                      have b15 : ¬ (m.getLsbD 15 = true) := by
                                        intro h
                                        rcases c576 h with h | h | h
                                        · exact (b6 h).elim
                                        · exact (b27 h).elim
                                        · exact (b34 h).elim
                                      have b22 : ¬ (m.getLsbD 22 = true) := by
                                        intro h
                                        rcases c594 h with h | h | h
                                        · exact (b6 h).elim
                                        · exact (b20 h).elim
                                        · exact (b48 h).elim
                                      have b39 : ¬ (m.getLsbD 39 = true) := by
                                        intro h
                                        rcases c620 h with h | h | h
                                        · exact (b12 h).elim
                                        · exact (b33 h).elim
                                        · exact (b47 h).elim
                                      have b46 : ¬ (m.getLsbD 46 = true) := by
                                        intro h
                                        rcases c638 h with h | h | h
                                        · exact (b12 h).elim
                                        · exact (b26 h).elim
                                        · exact (b40 h).elim
                                      have b9 : ¬ (m.getLsbD 9 = true) := by
                                        intro h
                                        rcases c647 h with h | h | h
                                        · exact (b35 h).elim
                                        · exact (b38 h).elim
                                        · exact (b39 h).elim
                                      rcases c681 b5 with h | h | h
                                      · exact (b15 h).elim
                                      · exact (b18 h).elim
                                      · exact (b20 h).elim
                                    ·
                                      have b22 : ¬ (m.getLsbD 22 = true) := by
                                        intro h
                                        rcases c593 h with h | h | h
                                        · exact (b5 h).elim
                                        · exact (b19 h).elim
                                        · exact (b47 h).elim
                                      have b6 : ¬ (m.getLsbD 6 = true) := by
                                        intro h
                                        rcases c700 h with h | h | h
                                        · exact (b22 h).elim
                                        · exact (b24 h).elim
                                        · exact (b26 h).elim
                                      have b15 : ¬ (m.getLsbD 15 = true) := by
                                        intro h
                                        rcases c576 h with h | h | h
                                        · exact (b6 h).elim
                                        · exact (b27 h).elim
                                        · exact (b34 h).elim
                                      have b33 : ¬ (m.getLsbD 33 = true) := by
                                        intro h
                                        rcases c691 h with h | h | h
                                        · exact (b15 h).elim
                                        · exact (b18 h).elim
                                        · exact (b20 h).elim
                                      by_cases b39 : m.getLsbD 39 = true
                                      ·
                                        have b46 : ¬ (m.getLsbD 46 = true) := c209 b39
                                        have b9 : m.getLsbD 9 = true := by
                                          rcases c619 b39 with h | h | h
                                          · exact h
                                          · exact (b30 h).elim
                                          · exact (b44 h).elim
                                        have b12 : m.getLsbD 12 = true := by
                                          rcases c620 b39 with h | h | h
                                          · exact h
                                          · exact (b33 h).elim
                                          · exact (b47 h).elim
                                        rcases c648 b9 with h | h | h
                                        · exact (b42 h).elim
                                        · exact (b45 h).elim
                                        · exact (b46 h).elim
                                      ·
                                        have b9 : ¬ (m.getLsbD 9 = true) := by
                                          intro h
                                          rcases c647 h with h | h | h
                                          · exact (b35 h).elim
                                          · exact (b38 h).elim
                                          · exact (b39 h).elim
                                        have b12 : ¬ (m.getLsbD 12 = true) := by
                                          intro h
                                          rcases c683 h with h | h | h
                                          · exact (b36 h).elim
                                          · exact (b39 h).elim
                                          · exact (b41 h).elim
                                        have b46 : ¬ (m.getLsbD 46 = true) := by
                                          intro h
                                          rcases c637 h with h | h | h
                                          · exact (b9 h).elim
                                          · exact (b23 h).elim
                                          · exact (b37 h).elim
                                        have hfull : m = 0 := by
                                          apply BitVec.eq_of_getLsbD_eq
                                          intro i hi
                                          interval_cases i
                                          · change m.getLsbD 0 = false
                                            exact Bool.eq_false_of_not_eq_true b0
                                          · change m.getLsbD 1 = false
                                            exact Bool.eq_false_of_not_eq_true b1
                                          · change m.getLsbD 2 = false
                                            exact Bool.eq_false_of_not_eq_true b2
                                          · change m.getLsbD 3 = false
                                            exact Bool.eq_false_of_not_eq_true b3
                                          · change m.getLsbD 4 = false
                                            exact Bool.eq_false_of_not_eq_true b4
                                          · change m.getLsbD 5 = false
                                            exact Bool.eq_false_of_not_eq_true b5
                                          · change m.getLsbD 6 = false
                                            exact Bool.eq_false_of_not_eq_true b6
                                          · change m.getLsbD 7 = false
                                            exact Bool.eq_false_of_not_eq_true b7
                                          · change m.getLsbD 8 = false
                                            exact Bool.eq_false_of_not_eq_true b8
                                          · change m.getLsbD 9 = false
                                            exact Bool.eq_false_of_not_eq_true b9
                                          · change m.getLsbD 10 = false
                                            exact Bool.eq_false_of_not_eq_true b10
                                          · change m.getLsbD 11 = false
                                            exact Bool.eq_false_of_not_eq_true b11
                                          · change m.getLsbD 12 = false
                                            exact Bool.eq_false_of_not_eq_true b12
                                          · change m.getLsbD 13 = false
                                            exact Bool.eq_false_of_not_eq_true b13
                                          · change m.getLsbD 14 = false
                                            exact Bool.eq_false_of_not_eq_true b14
                                          · change m.getLsbD 15 = false
                                            exact Bool.eq_false_of_not_eq_true b15
                                          · change m.getLsbD 16 = false
                                            exact Bool.eq_false_of_not_eq_true b16
                                          · change m.getLsbD 17 = false
                                            exact Bool.eq_false_of_not_eq_true b17
                                          · change m.getLsbD 18 = false
                                            exact Bool.eq_false_of_not_eq_true b18
                                          · change m.getLsbD 19 = false
                                            exact Bool.eq_false_of_not_eq_true b19
                                          · change m.getLsbD 20 = false
                                            exact Bool.eq_false_of_not_eq_true b20
                                          · change m.getLsbD 21 = false
                                            exact Bool.eq_false_of_not_eq_true b21
                                          · change m.getLsbD 22 = false
                                            exact Bool.eq_false_of_not_eq_true b22
                                          · change m.getLsbD 23 = false
                                            exact Bool.eq_false_of_not_eq_true b23
                                          · change m.getLsbD 24 = false
                                            exact Bool.eq_false_of_not_eq_true b24
                                          · change m.getLsbD 25 = false
                                            exact Bool.eq_false_of_not_eq_true b25
                                          · change m.getLsbD 26 = false
                                            exact Bool.eq_false_of_not_eq_true b26
                                          · change m.getLsbD 27 = false
                                            exact Bool.eq_false_of_not_eq_true b27
                                          · change m.getLsbD 28 = false
                                            exact Bool.eq_false_of_not_eq_true b28
                                          · change m.getLsbD 29 = false
                                            exact Bool.eq_false_of_not_eq_true b29
                                          · change m.getLsbD 30 = false
                                            exact Bool.eq_false_of_not_eq_true b30
                                          · change m.getLsbD 31 = false
                                            exact Bool.eq_false_of_not_eq_true b31
                                          · change m.getLsbD 32 = false
                                            exact Bool.eq_false_of_not_eq_true b32
                                          · change m.getLsbD 33 = false
                                            exact Bool.eq_false_of_not_eq_true b33
                                          · change m.getLsbD 34 = false
                                            exact Bool.eq_false_of_not_eq_true b34
                                          · change m.getLsbD 35 = false
                                            exact Bool.eq_false_of_not_eq_true b35
                                          · change m.getLsbD 36 = false
                                            exact Bool.eq_false_of_not_eq_true b36
                                          · change m.getLsbD 37 = false
                                            exact Bool.eq_false_of_not_eq_true b37
                                          · change m.getLsbD 38 = false
                                            exact Bool.eq_false_of_not_eq_true b38
                                          · change m.getLsbD 39 = false
                                            exact Bool.eq_false_of_not_eq_true b39
                                          · change m.getLsbD 40 = false
                                            exact Bool.eq_false_of_not_eq_true b40
                                          · change m.getLsbD 41 = false
                                            exact Bool.eq_false_of_not_eq_true b41
                                          · change m.getLsbD 42 = false
                                            exact Bool.eq_false_of_not_eq_true b42
                                          · change m.getLsbD 43 = false
                                            exact Bool.eq_false_of_not_eq_true b43
                                          · change m.getLsbD 44 = false
                                            exact Bool.eq_false_of_not_eq_true b44
                                          · change m.getLsbD 45 = false
                                            exact Bool.eq_false_of_not_eq_true b45
                                          · change m.getLsbD 46 = false
                                            exact Bool.eq_false_of_not_eq_true b46
                                          · change m.getLsbD 47 = false
                                            exact Bool.eq_false_of_not_eq_true b47
                                          · change m.getLsbD 48 = false
                                            exact Bool.eq_false_of_not_eq_true b48
                                        exact Or.inl hfull

end Erdos64.SubcubicFunnel.PackingCertificate
