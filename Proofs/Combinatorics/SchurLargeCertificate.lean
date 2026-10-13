import Combinatorics.SchurNumbers

set_option autoImplicit false

namespace SchurNumbers

private def markedPairs (mark : ℕ → Bool) (xs ys : List ℕ) : Bool :=
  xs.all fun x => ys.all fun y => !(mark (x + y))

example : markedPairs (fun x => x == 1) [1] [1] = true := rfl

private theorem sumFree_of_marked (xs : List ℕ) (mark : ℕ → Bool)
    (hm : xs.all mark = true) (hp : markedPairs mark xs xs = true) :
    SumFree xs.toFinset := by
  intro x hx y hy z hz heq
  have hx' : x ∈ xs := List.mem_toFinset.mp hx
  have hy' : y ∈ xs := List.mem_toFinset.mp hy
  have hz' : z ∈ xs := List.mem_toFinset.mp hz
  have hmark : mark z = true := (List.all_eq_true.mp hm) z hz'
  have hpair := List.all_eq_true.mp (List.all_eq_true.mp hp x hx') y hy'
  rw [heq, hmark] at hpair
  contradiction

private theorem colorable_of_lists {n m : ℕ} (c : ℕ → Fin n)
    (classes : Fin n → List ℕ)
    (hcover : ∀ x ∈ Finset.Icc 1 m, x ∈ classes (c x))
    (hfree : ∀ i, SumFree (classes i).toFinset) : SchurColorable n m := by
  refine ⟨c, fun i => (hfree i).subset ?_⟩
  intro x hx
  obtain ⟨hxI, hci⟩ := Finset.mem_filter.mp hx
  exact List.mem_toFinset.mpr (hci ▸ hcover x hxI)

private theorem pairs_of_chunks (mark : ℕ → Bool) (chunks : List (List ℕ))
    (ys : List ℕ) (h : chunks.all (fun xs => markedPairs mark xs ys) = true) :
    markedPairs mark chunks.flatten ys = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨xs, hxs, hxxs⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp h xs hxs) x hxxs

private def covered {n : ℕ} (c : ℕ → Fin n) (classes : Fin n → List ℕ)
    (lo count : ℕ) : Bool :=
  (List.range count).all fun k => (classes (c (lo + k))).contains (lo + k)

example : covered (fun _ => (0 : Fin 1)) (fun _ => [1]) 1 1 = true := rfl

private theorem covered_spec {n : ℕ} (c : ℕ → Fin n) (classes : Fin n → List ℕ)
    (lo count : ℕ) (h : covered c classes lo count = true)
    (x : ℕ) (hx : lo ≤ x) (hbound : x < lo + count) : x ∈ classes (c x) := by
  have hi : x - lo < count := by omega
  have hh := List.all_eq_true.mp h (x - lo) (List.mem_range.mpr hi)
  have heq : lo + (x - lo) = x := by omega
  rw [heq] at hh
  exact List.contains_iff_mem.mp hh

example : SumFree ([1] : List ℕ).toFinset :=
  sumFree_of_marked [1] (fun x => x == 1) rfl rfl

example : SchurColorable 1 1 := colorable_of_lists (fun _ => 0) (fun _ => [1])
  (by intro x hx; have hh := Finset.mem_Icc.mp hx; have heq : x = 1 := by omega
      simp [heq]) (fun _ => by decide)


/-!
Literal witnesses from Fred Rowley, arXiv:2107.03560 (2021), ancillary
`anc/Specimens_S_7____TFTs-4,5,6.xls`, sheet `S(7) >= 1696`, D6:E1701.
Workbook SHA256: c50cf981c1c437557b261cb8a66e193ee2cf77a8a50b0ae70c986b1c1cbb6fbb.
The six-color witness is the first-536 restriction (D6:E541), not a
transcription of the Fredricksen–Sweet (2000) lists. Neither bound asserts
optimality or novelty. The zero-based label functions below are generated from
these literal classes; kernel certificates check their relationship.
partition536.txt SHA256: 92b987211ade32ae318d741cc8de158705338e090e80720ae1d4f97556a330bd.
partition1696.txt SHA256: 2c52e78d342ba59af661c68a0149808c49649fcbacdc2da13bbc8a128f5640ff.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
private def sixChunk0_0 : List ℕ := [8, 9, 14, 15, 25, 31, 32, 35, 42, 52, 55, 59, 76, 79, 89, 95]

example : sixChunk0_0.length = 16 := rfl

private def sixChunk0_1 : List ℕ := [96, 99, 100, 106, 112, 116, 117, 119, 129, 136, 139, 140, 146, 157, 162, 163]

example : sixChunk0_1.length = 16 := rfl

private def sixChunk0_2 : List ℕ := [180, 186, 220, 226, 227, 230, 237, 243, 247, 249, 250, 260, 266, 267, 270, 271]

example : sixChunk0_2.length = 16 := rfl

private def sixChunk0_3 : List ℕ := [277, 287, 288, 290, 294, 300, 307, 310, 311, 317, 351, 357, 374, 375, 380, 391]

example : sixChunk0_3.length = 16 := rfl

private def sixChunk0_4 : List ℕ := [397, 398, 401, 408, 418, 420, 421, 425, 431, 437, 438, 441, 442, 448, 458, 461]

example : sixChunk0_4.length = 16 := rfl

private def sixChunk0_5 : List ℕ := [478, 482, 485, 495, 502, 505, 506, 512, 522, 523, 528, 529]

example : sixChunk0_5.length = 12 := rfl

private def sixRows0 : List (List ℕ) := [sixChunk0_0, sixChunk0_1, sixChunk0_2, sixChunk0_3, sixChunk0_4, sixChunk0_5]

private def sixClass0 : List ℕ := sixRows0.flatten

example : sixClass0.length = 92 := rfl

private def sixChunk1_0 : List ℕ := [3, 13, 17, 18, 23, 28, 38, 44, 48, 54, 64, 83, 93, 103, 113, 114]

example : sixChunk1_0.length = 16 := rfl

private def sixChunk1_1 : List ℕ := [122, 123, 124, 133, 134, 143, 148, 153, 154, 174, 175, 179, 185, 195, 211, 232]

example : sixChunk1_1.length = 16 := rfl

private def sixChunk1_2 : List ℕ := [242, 252, 253, 254, 263, 264, 273, 274, 283, 284, 285, 295, 305, 326, 342, 352]

example : sixChunk1_2.length = 16 := rfl

private def sixChunk1_3 : List ℕ := [362, 363, 383, 384, 389, 394, 403, 404, 413, 414, 415, 423, 424, 434, 444, 454]

example : sixChunk1_3.length = 16 := rfl

private def sixChunk1_4 : List ℕ := [473, 483, 489, 493, 499, 509, 514, 519, 520, 524, 534]

example : sixChunk1_4.length = 11 := rfl

private def sixRows1 : List (List ℕ) := [sixChunk1_0, sixChunk1_1, sixChunk1_2, sixChunk1_3, sixChunk1_4]

private def sixClass1 : List ℕ := sixRows1.flatten

example : sixClass1.length = 75 := rfl

private def sixChunk2_0 : List ℕ := [2, 5, 12, 19, 22, 26, 29, 36, 39, 43, 46, 50, 53, 56, 60, 63]

example : sixChunk2_0.length = 16 := rfl

private def sixChunk2_1 : List ℕ := [74, 77, 80, 84, 87, 91, 94, 98, 101, 104, 108, 111, 115, 118, 121, 125]

example : sixChunk2_1.length = 16 := rfl

private def sixChunk2_2 : List ℕ := [128, 131, 132, 135, 142, 145, 149, 152, 155, 156, 159, 166, 169, 173, 176, 183]

example : sixChunk2_2.length = 16 := rfl

private def sixChunk2_3 : List ℕ := [190, 193, 197, 204, 210, 214, 217, 221, 224, 228, 231, 234, 238, 241, 244, 245]

example : sixChunk2_3.length = 16 := rfl

private def sixChunk2_4 : List ℕ := [248, 255, 258, 265, 268, 269, 272, 279, 282, 289, 292, 293, 296, 299, 303, 306]

example : sixChunk2_4.length = 16 := rfl

private def sixChunk2_5 : List ℕ := [309, 313, 316, 320, 323, 327, 333, 340, 344, 347, 354, 358, 361, 364, 368, 371]

example : sixChunk2_5.length = 16 := rfl

private def sixChunk2_6 : List ℕ := [378, 381, 382, 385, 388, 392, 395, 402, 405, 406, 409, 412, 416, 419, 422, 426]

example : sixChunk2_6.length = 16 := rfl

private def sixChunk2_7 : List ℕ := [429, 433, 436, 439, 443, 446, 450, 453, 457, 460, 474, 477, 481, 484, 487, 491]

example : sixChunk2_7.length = 16 := rfl

private def sixChunk2_8 : List ℕ := [494, 498, 501, 508, 511, 515, 518, 525, 532, 535]

example : sixChunk2_8.length = 10 := rfl

private def sixRows2 : List (List ℕ) := [sixChunk2_0, sixChunk2_1, sixChunk2_2, sixChunk2_3, sixChunk2_4, sixChunk2_5, sixChunk2_6, sixChunk2_7, sixChunk2_8]

private def sixClass2 : List ℕ := sixRows2.flatten

example : sixClass2.length = 138 := rfl

private def sixChunk3_0 : List ℕ := [4, 7, 10, 21, 27, 30, 33, 47, 67, 70, 85, 86, 109, 110, 126, 127]

example : sixChunk3_0.length = 16 := rfl

private def sixChunk3_1 : List ℕ := [138, 141, 144, 150, 158, 161, 164, 167, 178, 184, 202, 216, 222, 239, 240, 256]

example : sixChunk3_1.length = 16 := rfl

private def sixChunk3_2 : List ℕ := [257, 262, 275, 280, 281, 297, 298, 315, 321, 335, 353, 359, 370, 373, 376, 379]

example : sixChunk3_2.length = 16 := rfl

private def sixChunk3_3 : List ℕ := [387, 393, 396, 399, 410, 411, 427, 428, 451, 452, 467, 470, 490, 504, 507, 510]

example : sixChunk3_3.length = 16 := rfl

private def sixChunk3_4 : List ℕ := [516, 527, 530, 533]

example : sixChunk3_4.length = 4 := rfl

private def sixRows3 : List (List ℕ) := [sixChunk3_0, sixChunk3_1, sixChunk3_2, sixChunk3_3, sixChunk3_4]

private def sixClass3 : List ℕ := sixRows3.flatten

example : sixClass3.length = 68 := rfl

private def sixChunk4_0 : List ℕ := [1, 6, 11, 16, 20, 24, 34, 37, 41, 90, 97, 102, 105, 107, 120, 130]

example : sixChunk4_0.length = 16 := rfl

private def sixChunk4_1 : List ℕ := [137, 147, 151, 160, 165, 168, 170, 172, 177, 182, 229, 233, 236, 246, 251, 259]

example : sixChunk4_1.length = 16 := rfl

private def sixChunk4_2 : List ℕ := [261, 276, 278, 286, 291, 301, 304, 308, 355, 360, 365, 367, 369, 372, 377, 386]

example : sixChunk4_2.length = 16 := rfl

private def sixChunk4_3 : List ℕ := [390, 400, 407, 417, 430, 432, 435, 440, 447, 496, 500, 503, 513, 517, 521, 526]

example : sixChunk4_3.length = 16 := rfl

private def sixChunk4_4 : List ℕ := [531, 536]

example : sixChunk4_4.length = 2 := rfl

private def sixRows4 : List (List ℕ) := [sixChunk4_0, sixChunk4_1, sixChunk4_2, sixChunk4_3, sixChunk4_4]

private def sixClass4 : List ℕ := sixRows4.flatten

example : sixClass4.length = 66 := rfl

private def sixChunk5_0 : List ℕ := [40, 45, 49, 51, 57, 58, 61, 62, 65, 66, 68, 69, 71, 72, 73, 75]

example : sixChunk5_0.length = 16 := rfl

private def sixChunk5_1 : List ℕ := [78, 81, 82, 88, 92, 171, 181, 187, 188, 189, 191, 192, 194, 196, 198, 199]

example : sixChunk5_1.length = 16 := rfl

private def sixChunk5_2 : List ℕ := [200, 201, 203, 205, 206, 207, 208, 209, 212, 213, 215, 218, 219, 223, 225, 235]

example : sixChunk5_2.length = 16 := rfl

private def sixChunk5_3 : List ℕ := [302, 312, 314, 318, 319, 322, 324, 325, 328, 329, 330, 331, 332, 334, 336, 337]

example : sixChunk5_3.length = 16 := rfl

private def sixChunk5_4 : List ℕ := [338, 339, 341, 343, 345, 346, 348, 349, 350, 356, 366, 445, 449, 455, 456, 459]

example : sixChunk5_4.length = 16 := rfl

private def sixChunk5_5 : List ℕ := [462, 463, 464, 465, 466, 468, 469, 471, 472, 475, 476, 479, 480, 486, 488, 492]

example : sixChunk5_5.length = 16 := rfl

private def sixChunk5_6 : List ℕ := [497]

example : sixChunk5_6.length = 1 := rfl

private def sixRows5 : List (List ℕ) := [sixChunk5_0, sixChunk5_1, sixChunk5_2, sixChunk5_3, sixChunk5_4, sixChunk5_5, sixChunk5_6]

private def sixClass5 : List ℕ := sixRows5.flatten

example : sixClass5.length = 97 := rfl

private def sixLabel (x : ℕ) : ℕ :=
  if x.blt 537 then (if x.blt 268 then (if x.blt 134 then (if x.blt 67 then (if x.blt 33 then (if x.blt 16 then (if x.blt 8 then (if x.blt 4 then (if x.blt 2 then (if x.blt 1 then 0 else 4) else (if x.blt 3 then 2 else 1)) else (if x.blt 6 then (if x.blt 5 then 3 else 2) else (if x.blt 7 then 4 else 3))) else (if x.blt 12 then (if x.blt 10 then (if x.blt 9 then 0 else 0) else (if x.blt 11 then 3 else 4)) else (if x.blt 14 then (if x.blt 13 then 2 else 1) else (if x.blt 15 then 0 else 0)))) else (if x.blt 24 then (if x.blt 20 then (if x.blt 18 then (if x.blt 17 then 4 else 1) else (if x.blt 19 then 1 else 2)) else (if x.blt 22 then (if x.blt 21 then 4 else 3) else (if x.blt 23 then 2 else 1))) else (if x.blt 28 then (if x.blt 26 then (if x.blt 25 then 4 else 0) else (if x.blt 27 then 2 else 3)) else (if x.blt 30 then (if x.blt 29 then 1 else 2) else (if x.blt 31 then 3 else (if x.blt 32 then 0 else 0)))))) else (if x.blt 50 then (if x.blt 41 then (if x.blt 37 then (if x.blt 35 then (if x.blt 34 then 3 else 4) else (if x.blt 36 then 0 else 2)) else (if x.blt 39 then (if x.blt 38 then 4 else 1) else (if x.blt 40 then 2 else 5))) else (if x.blt 45 then (if x.blt 43 then (if x.blt 42 then 4 else 0) else (if x.blt 44 then 2 else 1)) else (if x.blt 47 then (if x.blt 46 then 5 else 2) else (if x.blt 48 then 3 else (if x.blt 49 then 1 else 5))))) else (if x.blt 58 then (if x.blt 54 then (if x.blt 52 then (if x.blt 51 then 2 else 5) else (if x.blt 53 then 0 else 2)) else (if x.blt 56 then (if x.blt 55 then 1 else 0) else (if x.blt 57 then 2 else 5))) else (if x.blt 62 then (if x.blt 60 then (if x.blt 59 then 5 else 0) else (if x.blt 61 then 2 else 5)) else (if x.blt 64 then (if x.blt 63 then 5 else 2) else (if x.blt 65 then 1 else (if x.blt 66 then 5 else 5))))))) else (if x.blt 100 then (if x.blt 83 then (if x.blt 75 then (if x.blt 71 then (if x.blt 69 then (if x.blt 68 then 3 else 5) else (if x.blt 70 then 5 else 3)) else (if x.blt 73 then (if x.blt 72 then 5 else 5) else (if x.blt 74 then 5 else 2))) else (if x.blt 79 then (if x.blt 77 then (if x.blt 76 then 5 else 0) else (if x.blt 78 then 2 else 5)) else (if x.blt 81 then (if x.blt 80 then 0 else 2) else (if x.blt 82 then 5 else 5)))) else (if x.blt 91 then (if x.blt 87 then (if x.blt 85 then (if x.blt 84 then 1 else 2) else (if x.blt 86 then 3 else 3)) else (if x.blt 89 then (if x.blt 88 then 2 else 5) else (if x.blt 90 then 0 else 4))) else (if x.blt 95 then (if x.blt 93 then (if x.blt 92 then 2 else 5) else (if x.blt 94 then 1 else 2)) else (if x.blt 97 then (if x.blt 96 then 0 else 0) else (if x.blt 98 then 4 else (if x.blt 99 then 2 else 0)))))) else (if x.blt 117 then (if x.blt 108 then (if x.blt 104 then (if x.blt 102 then (if x.blt 101 then 0 else 2) else (if x.blt 103 then 4 else 1)) else (if x.blt 106 then (if x.blt 105 then 2 else 4) else (if x.blt 107 then 0 else 4))) else (if x.blt 112 then (if x.blt 110 then (if x.blt 109 then 2 else 3) else (if x.blt 111 then 3 else 2)) else (if x.blt 114 then (if x.blt 113 then 0 else 1) else (if x.blt 115 then 1 else (if x.blt 116 then 2 else 0))))) else (if x.blt 125 then (if x.blt 121 then (if x.blt 119 then (if x.blt 118 then 0 else 2) else (if x.blt 120 then 0 else 4)) else (if x.blt 123 then (if x.blt 122 then 2 else 1) else (if x.blt 124 then 1 else 1))) else (if x.blt 129 then (if x.blt 127 then (if x.blt 126 then 2 else 3) else (if x.blt 128 then 3 else 2)) else (if x.blt 131 then (if x.blt 130 then 0 else 4) else (if x.blt 132 then 2 else (if x.blt 133 then 2 else 1)))))))) else (if x.blt 201 then (if x.blt 167 then (if x.blt 150 then (if x.blt 142 then (if x.blt 138 then (if x.blt 136 then (if x.blt 135 then 1 else 2) else (if x.blt 137 then 0 else 4)) else (if x.blt 140 then (if x.blt 139 then 3 else 0) else (if x.blt 141 then 0 else 3))) else (if x.blt 146 then (if x.blt 144 then (if x.blt 143 then 2 else 1) else (if x.blt 145 then 3 else 2)) else (if x.blt 148 then (if x.blt 147 then 0 else 4) else (if x.blt 149 then 1 else 2)))) else (if x.blt 158 then (if x.blt 154 then (if x.blt 152 then (if x.blt 151 then 3 else 4) else (if x.blt 153 then 2 else 1)) else (if x.blt 156 then (if x.blt 155 then 1 else 2) else (if x.blt 157 then 2 else 0))) else (if x.blt 162 then (if x.blt 160 then (if x.blt 159 then 3 else 2) else (if x.blt 161 then 4 else 3)) else (if x.blt 164 then (if x.blt 163 then 0 else 0) else (if x.blt 165 then 3 else (if x.blt 166 then 4 else 2)))))) else (if x.blt 184 then (if x.blt 175 then (if x.blt 171 then (if x.blt 169 then (if x.blt 168 then 3 else 4) else (if x.blt 170 then 2 else 4)) else (if x.blt 173 then (if x.blt 172 then 5 else 4) else (if x.blt 174 then 2 else 1))) else (if x.blt 179 then (if x.blt 177 then (if x.blt 176 then 1 else 2) else (if x.blt 178 then 4 else 3)) else (if x.blt 181 then (if x.blt 180 then 1 else 0) else (if x.blt 182 then 5 else (if x.blt 183 then 4 else 2))))) else (if x.blt 192 then (if x.blt 188 then (if x.blt 186 then (if x.blt 185 then 3 else 1) else (if x.blt 187 then 0 else 5)) else (if x.blt 190 then (if x.blt 189 then 5 else 5) else (if x.blt 191 then 2 else 5))) else (if x.blt 196 then (if x.blt 194 then (if x.blt 193 then 5 else 2) else (if x.blt 195 then 5 else 1)) else (if x.blt 198 then (if x.blt 197 then 5 else 2) else (if x.blt 199 then 5 else (if x.blt 200 then 5 else 5))))))) else (if x.blt 234 then (if x.blt 217 then (if x.blt 209 then (if x.blt 205 then (if x.blt 203 then (if x.blt 202 then 5 else 3) else (if x.blt 204 then 5 else 2)) else (if x.blt 207 then (if x.blt 206 then 5 else 5) else (if x.blt 208 then 5 else 5))) else (if x.blt 213 then (if x.blt 211 then (if x.blt 210 then 5 else 2) else (if x.blt 212 then 1 else 5)) else (if x.blt 215 then (if x.blt 214 then 5 else 2) else (if x.blt 216 then 5 else 3)))) else (if x.blt 225 then (if x.blt 221 then (if x.blt 219 then (if x.blt 218 then 2 else 5) else (if x.blt 220 then 5 else 0)) else (if x.blt 223 then (if x.blt 222 then 2 else 3) else (if x.blt 224 then 5 else 2))) else (if x.blt 229 then (if x.blt 227 then (if x.blt 226 then 5 else 0) else (if x.blt 228 then 0 else 2)) else (if x.blt 231 then (if x.blt 230 then 4 else 0) else (if x.blt 232 then 2 else (if x.blt 233 then 1 else 4)))))) else (if x.blt 251 then (if x.blt 242 then (if x.blt 238 then (if x.blt 236 then (if x.blt 235 then 2 else 5) else (if x.blt 237 then 4 else 0)) else (if x.blt 240 then (if x.blt 239 then 2 else 3) else (if x.blt 241 then 3 else 2))) else (if x.blt 246 then (if x.blt 244 then (if x.blt 243 then 1 else 0) else (if x.blt 245 then 2 else 2)) else (if x.blt 248 then (if x.blt 247 then 4 else 0) else (if x.blt 249 then 2 else (if x.blt 250 then 0 else 0))))) else (if x.blt 259 then (if x.blt 255 then (if x.blt 253 then (if x.blt 252 then 4 else 1) else (if x.blt 254 then 1 else 1)) else (if x.blt 257 then (if x.blt 256 then 2 else 3) else (if x.blt 258 then 3 else 2))) else (if x.blt 263 then (if x.blt 261 then (if x.blt 260 then 4 else 0) else (if x.blt 262 then 4 else 3)) else (if x.blt 265 then (if x.blt 264 then 1 else 1) else (if x.blt 266 then 2 else (if x.blt 267 then 0 else 0))))))))) else (if x.blt 402 then (if x.blt 335 then (if x.blt 301 then (if x.blt 284 then (if x.blt 276 then (if x.blt 272 then (if x.blt 270 then (if x.blt 269 then 2 else 2) else (if x.blt 271 then 0 else 0)) else (if x.blt 274 then (if x.blt 273 then 2 else 1) else (if x.blt 275 then 1 else 3))) else (if x.blt 280 then (if x.blt 278 then (if x.blt 277 then 4 else 0) else (if x.blt 279 then 4 else 2)) else (if x.blt 282 then (if x.blt 281 then 3 else 3) else (if x.blt 283 then 2 else 1)))) else (if x.blt 292 then (if x.blt 288 then (if x.blt 286 then (if x.blt 285 then 1 else 1) else (if x.blt 287 then 4 else 0)) else (if x.blt 290 then (if x.blt 289 then 0 else 2) else (if x.blt 291 then 0 else 4))) else (if x.blt 296 then (if x.blt 294 then (if x.blt 293 then 2 else 2) else (if x.blt 295 then 0 else 1)) else (if x.blt 298 then (if x.blt 297 then 2 else 3) else (if x.blt 299 then 3 else (if x.blt 300 then 2 else 0)))))) else (if x.blt 318 then (if x.blt 309 then (if x.blt 305 then (if x.blt 303 then (if x.blt 302 then 4 else 5) else (if x.blt 304 then 2 else 4)) else (if x.blt 307 then (if x.blt 306 then 1 else 2) else (if x.blt 308 then 0 else 4))) else (if x.blt 313 then (if x.blt 311 then (if x.blt 310 then 2 else 0) else (if x.blt 312 then 0 else 5)) else (if x.blt 315 then (if x.blt 314 then 2 else 5) else (if x.blt 316 then 3 else (if x.blt 317 then 2 else 0))))) else (if x.blt 326 then (if x.blt 322 then (if x.blt 320 then (if x.blt 319 then 5 else 5) else (if x.blt 321 then 2 else 3)) else (if x.blt 324 then (if x.blt 323 then 5 else 2) else (if x.blt 325 then 5 else 5))) else (if x.blt 330 then (if x.blt 328 then (if x.blt 327 then 1 else 2) else (if x.blt 329 then 5 else 5)) else (if x.blt 332 then (if x.blt 331 then 5 else 5) else (if x.blt 333 then 5 else (if x.blt 334 then 2 else 5))))))) else (if x.blt 368 then (if x.blt 351 then (if x.blt 343 then (if x.blt 339 then (if x.blt 337 then (if x.blt 336 then 3 else 5) else (if x.blt 338 then 5 else 5)) else (if x.blt 341 then (if x.blt 340 then 5 else 2) else (if x.blt 342 then 5 else 1))) else (if x.blt 347 then (if x.blt 345 then (if x.blt 344 then 5 else 2) else (if x.blt 346 then 5 else 5)) else (if x.blt 349 then (if x.blt 348 then 2 else 5) else (if x.blt 350 then 5 else 5)))) else (if x.blt 359 then (if x.blt 355 then (if x.blt 353 then (if x.blt 352 then 0 else 1) else (if x.blt 354 then 3 else 2)) else (if x.blt 357 then (if x.blt 356 then 4 else 5) else (if x.blt 358 then 0 else 2))) else (if x.blt 363 then (if x.blt 361 then (if x.blt 360 then 3 else 4) else (if x.blt 362 then 2 else 1)) else (if x.blt 365 then (if x.blt 364 then 1 else 2) else (if x.blt 366 then 4 else (if x.blt 367 then 5 else 4)))))) else (if x.blt 385 then (if x.blt 376 then (if x.blt 372 then (if x.blt 370 then (if x.blt 369 then 2 else 4) else (if x.blt 371 then 3 else 2)) else (if x.blt 374 then (if x.blt 373 then 4 else 3) else (if x.blt 375 then 0 else 0))) else (if x.blt 380 then (if x.blt 378 then (if x.blt 377 then 3 else 4) else (if x.blt 379 then 2 else 3)) else (if x.blt 382 then (if x.blt 381 then 0 else 2) else (if x.blt 383 then 2 else (if x.blt 384 then 1 else 1))))) else (if x.blt 393 then (if x.blt 389 then (if x.blt 387 then (if x.blt 386 then 2 else 4) else (if x.blt 388 then 3 else 2)) else (if x.blt 391 then (if x.blt 390 then 1 else 4) else (if x.blt 392 then 0 else 2))) else (if x.blt 397 then (if x.blt 395 then (if x.blt 394 then 3 else 1) else (if x.blt 396 then 2 else 3)) else (if x.blt 399 then (if x.blt 398 then 0 else 0) else (if x.blt 400 then 3 else (if x.blt 401 then 4 else 0)))))))) else (if x.blt 469 then (if x.blt 435 then (if x.blt 418 then (if x.blt 410 then (if x.blt 406 then (if x.blt 404 then (if x.blt 403 then 2 else 1) else (if x.blt 405 then 1 else 2)) else (if x.blt 408 then (if x.blt 407 then 2 else 4) else (if x.blt 409 then 0 else 2))) else (if x.blt 414 then (if x.blt 412 then (if x.blt 411 then 3 else 3) else (if x.blt 413 then 2 else 1)) else (if x.blt 416 then (if x.blt 415 then 1 else 1) else (if x.blt 417 then 2 else 4)))) else (if x.blt 426 then (if x.blt 422 then (if x.blt 420 then (if x.blt 419 then 0 else 2) else (if x.blt 421 then 0 else 0)) else (if x.blt 424 then (if x.blt 423 then 2 else 1) else (if x.blt 425 then 1 else 0))) else (if x.blt 430 then (if x.blt 428 then (if x.blt 427 then 2 else 3) else (if x.blt 429 then 3 else 2)) else (if x.blt 432 then (if x.blt 431 then 4 else 0) else (if x.blt 433 then 4 else (if x.blt 434 then 2 else 1)))))) else (if x.blt 452 then (if x.blt 443 then (if x.blt 439 then (if x.blt 437 then (if x.blt 436 then 4 else 2) else (if x.blt 438 then 0 else 0)) else (if x.blt 441 then (if x.blt 440 then 2 else 4) else (if x.blt 442 then 0 else 0))) else (if x.blt 447 then (if x.blt 445 then (if x.blt 444 then 2 else 1) else (if x.blt 446 then 5 else 2)) else (if x.blt 449 then (if x.blt 448 then 4 else 0) else (if x.blt 450 then 5 else (if x.blt 451 then 2 else 3))))) else (if x.blt 460 then (if x.blt 456 then (if x.blt 454 then (if x.blt 453 then 3 else 2) else (if x.blt 455 then 1 else 5)) else (if x.blt 458 then (if x.blt 457 then 5 else 2) else (if x.blt 459 then 0 else 5))) else (if x.blt 464 then (if x.blt 462 then (if x.blt 461 then 2 else 0) else (if x.blt 463 then 5 else 5)) else (if x.blt 466 then (if x.blt 465 then 5 else 5) else (if x.blt 467 then 5 else (if x.blt 468 then 3 else 5))))))) else (if x.blt 503 then (if x.blt 486 then (if x.blt 477 then (if x.blt 473 then (if x.blt 471 then (if x.blt 470 then 5 else 3) else (if x.blt 472 then 5 else 5)) else (if x.blt 475 then (if x.blt 474 then 1 else 2) else (if x.blt 476 then 5 else 5))) else (if x.blt 481 then (if x.blt 479 then (if x.blt 478 then 2 else 0) else (if x.blt 480 then 5 else 5)) else (if x.blt 483 then (if x.blt 482 then 2 else 0) else (if x.blt 484 then 1 else (if x.blt 485 then 2 else 0))))) else (if x.blt 494 then (if x.blt 490 then (if x.blt 488 then (if x.blt 487 then 5 else 2) else (if x.blt 489 then 5 else 1)) else (if x.blt 492 then (if x.blt 491 then 3 else 2) else (if x.blt 493 then 5 else 1))) else (if x.blt 498 then (if x.blt 496 then (if x.blt 495 then 2 else 0) else (if x.blt 497 then 4 else 5)) else (if x.blt 500 then (if x.blt 499 then 2 else 1) else (if x.blt 501 then 4 else (if x.blt 502 then 2 else 0)))))) else (if x.blt 520 then (if x.blt 511 then (if x.blt 507 then (if x.blt 505 then (if x.blt 504 then 4 else 3) else (if x.blt 506 then 0 else 0)) else (if x.blt 509 then (if x.blt 508 then 3 else 2) else (if x.blt 510 then 1 else 3))) else (if x.blt 515 then (if x.blt 513 then (if x.blt 512 then 2 else 0) else (if x.blt 514 then 4 else 1)) else (if x.blt 517 then (if x.blt 516 then 2 else 3) else (if x.blt 518 then 4 else (if x.blt 519 then 2 else 1))))) else (if x.blt 528 then (if x.blt 524 then (if x.blt 522 then (if x.blt 521 then 1 else 4) else (if x.blt 523 then 0 else 0)) else (if x.blt 526 then (if x.blt 525 then 1 else 2) else (if x.blt 527 then 4 else 3))) else (if x.blt 532 then (if x.blt 530 then (if x.blt 529 then 0 else 0) else (if x.blt 531 then 3 else 4)) else (if x.blt 534 then (if x.blt 533 then 2 else 3) else (if x.blt 535 then 1 else (if x.blt 536 then 2 else 4)))))))))) else 0

example : sixLabel 1 = 4 := rfl
example : sixLabel 537 = 0 := rfl

private def sixColor (x : ℕ) : Fin 6 := ⟨sixLabel x % 6, Nat.mod_lt _ (by decide)⟩

example : sixColor 0 = 0 := rfl
example : sixColor 1 = 4 := rfl
example : sixColor 537 = 0 := rfl

private def sixClasses (i : Fin 6) : List ℕ :=
  ([sixClass0, sixClass1, sixClass2, sixClass3, sixClass4, sixClass5] : List (List ℕ))[i.val]?.getD []

private def sixMark0 (x : ℕ) : Bool :=
  (if x.blt 270 then (if x.blt 119 then (if x.blt 59 then (if x.blt 31 then (if x.blt 14 then (if x.blt 9 then (x == 8) else if x == 9 then true else false) else if x == 14 then true else (if x.blt 25 then (x == 15) else if x == 25 then true else false)) else if x == 31 then true else (if x.blt 42 then (if x.blt 35 then (x == 32) else if x == 35 then true else false) else if x == 42 then true else (if x.blt 55 then (x == 52) else if x == 55 then true else false))) else if x == 59 then true else (if x.blt 99 then (if x.blt 89 then (if x.blt 79 then (x == 76) else if x == 79 then true else false) else if x == 89 then true else (if x.blt 96 then (x == 95) else if x == 96 then true else false)) else if x == 99 then true else (if x.blt 112 then (if x.blt 106 then (x == 100) else if x == 106 then true else false) else if x == 112 then true else (if x.blt 117 then (x == 116) else if x == 117 then true else false)))) else if x == 119 then true else (if x.blt 226 then (if x.blt 157 then (if x.blt 139 then (if x.blt 136 then (x == 129) else if x == 136 then true else false) else if x == 139 then true else (if x.blt 146 then (x == 140) else if x == 146 then true else false)) else if x == 157 then true else (if x.blt 180 then (if x.blt 163 then (x == 162) else if x == 163 then true else false) else if x == 180 then true else (if x.blt 220 then (x == 186) else if x == 220 then true else false))) else if x == 226 then true else (if x.blt 249 then (if x.blt 237 then (if x.blt 230 then (x == 227) else if x == 230 then true else false) else if x == 237 then true else (if x.blt 247 then (x == 243) else if x == 247 then true else false)) else if x == 249 then true else (if x.blt 266 then (if x.blt 260 then (x == 250) else if x == 260 then true else false) else if x == 266 then true else (x == 267))))) else if x == 270 then true else (if x.blt 420 then (if x.blt 351 then (if x.blt 294 then (if x.blt 287 then (if x.blt 277 then (x == 271) else if x == 277 then true else false) else if x == 287 then true else (if x.blt 290 then (x == 288) else if x == 290 then true else false)) else if x == 294 then true else (if x.blt 310 then (if x.blt 307 then (x == 300) else if x == 307 then true else false) else if x == 310 then true else (if x.blt 317 then (x == 311) else if x == 317 then true else false))) else if x == 351 then true else (if x.blt 397 then (if x.blt 375 then (if x.blt 374 then (x == 357) else if x == 374 then true else false) else if x == 375 then true else (if x.blt 391 then (x == 380) else if x == 391 then true else false)) else if x == 397 then true else (if x.blt 408 then (if x.blt 401 then (x == 398) else if x == 401 then true else false) else if x == 408 then true else (x == 418)))) else if x == 420 then true else (if x.blt 482 then (if x.blt 441 then (if x.blt 431 then (if x.blt 425 then (x == 421) else if x == 425 then true else false) else if x == 431 then true else (if x.blt 438 then (x == 437) else if x == 438 then true else false)) else if x == 441 then true else (if x.blt 458 then (if x.blt 448 then (x == 442) else if x == 448 then true else false) else if x == 458 then true else (if x.blt 478 then (x == 461) else if x == 478 then true else false))) else if x == 482 then true else (if x.blt 512 then (if x.blt 502 then (if x.blt 495 then (x == 485) else if x == 495 then true else false) else if x == 502 then true else (if x.blt 506 then (x == 505) else if x == 506 then true else false)) else if x == 512 then true else (if x.blt 528 then (if x.blt 523 then (x == 522) else if x == 523 then true else false) else if x == 528 then true else (x == 529))))))

example : sixMark0 8 = true := rfl
example : sixMark0 0 = false := rfl

private theorem sixMarked0 : sixClass0.all sixMark0 = true := by decide

private theorem sixPair0_0 : markedPairs sixMark0 sixChunk0_0 sixClass0 = true := by decide

private theorem sixPair0_1 : markedPairs sixMark0 sixChunk0_1 sixClass0 = true := by decide

private theorem sixPair0_2 : markedPairs sixMark0 sixChunk0_2 sixClass0 = true := by decide

private theorem sixPair0_3 : markedPairs sixMark0 sixChunk0_3 sixClass0 = true := by decide

private theorem sixPair0_4 : markedPairs sixMark0 sixChunk0_4 sixClass0 = true := by decide

private theorem sixPair0_5 : markedPairs sixMark0 sixChunk0_5 sixClass0 = true := by decide

private theorem sixFree0 : SumFree sixClass0.toFinset := by
  apply sumFree_of_marked _ sixMark0 sixMarked0
  apply pairs_of_chunks
  simp only [sixRows0, List.all_cons, List.all_nil, sixPair0_0, sixPair0_1, sixPair0_2, sixPair0_3, sixPair0_4, sixPair0_5, Bool.and_self]

private def sixMark1 (x : ℕ) : Bool :=
  (if x.blt 264 then (if x.blt 124 then (if x.blt 54 then (if x.blt 23 then (if x.blt 17 then (if x.blt 13 then (x == 3) else if x == 13 then true else false) else if x == 17 then true else (x == 18)) else if x == 23 then true else (if x.blt 44 then (if x.blt 38 then (x == 28) else if x == 38 then true else false) else if x == 44 then true else (x == 48))) else if x == 54 then true else (if x.blt 113 then (if x.blt 93 then (if x.blt 83 then (x == 64) else if x == 83 then true else false) else if x == 93 then true else (x == 103)) else if x == 113 then true else (if x.blt 122 then (x == 114) else if x == 122 then true else (x == 123)))) else if x == 124 then true else (if x.blt 185 then (if x.blt 153 then (if x.blt 143 then (if x.blt 134 then (x == 133) else if x == 134 then true else false) else if x == 143 then true else (x == 148)) else if x == 153 then true else (if x.blt 175 then (if x.blt 174 then (x == 154) else if x == 174 then true else false) else if x == 175 then true else (x == 179))) else if x == 185 then true else (if x.blt 252 then (if x.blt 232 then (if x.blt 211 then (x == 195) else if x == 211 then true else false) else if x == 232 then true else (x == 242)) else if x == 252 then true else (if x.blt 254 then (x == 253) else if x == 254 then true else (x == 263))))) else if x == 264 then true else (if x.blt 413 then (if x.blt 352 then (if x.blt 285 then (if x.blt 283 then (if x.blt 274 then (x == 273) else if x == 274 then true else false) else if x == 283 then true else (x == 284)) else if x == 285 then true else (if x.blt 326 then (if x.blt 305 then (x == 295) else if x == 305 then true else false) else if x == 326 then true else (x == 342))) else if x == 352 then true else (if x.blt 389 then (if x.blt 383 then (if x.blt 363 then (x == 362) else if x == 363 then true else false) else if x == 383 then true else (x == 384)) else if x == 389 then true else (if x.blt 403 then (x == 394) else if x == 403 then true else (x == 404)))) else if x == 413 then true else (if x.blt 489 then (if x.blt 434 then (if x.blt 423 then (if x.blt 415 then (x == 414) else if x == 415 then true else false) else if x == 423 then true else (x == 424)) else if x == 434 then true else (if x.blt 473 then (if x.blt 454 then (x == 444) else if x == 454 then true else false) else if x == 473 then true else (x == 483))) else if x == 489 then true else (if x.blt 519 then (if x.blt 509 then (if x.blt 499 then (x == 493) else if x == 499 then true else false) else if x == 509 then true else (x == 514)) else if x == 519 then true else (if x.blt 524 then (x == 520) else if x == 524 then true else (x == 534))))))

example : sixMark1 3 = true := rfl
example : sixMark1 0 = false := rfl

private theorem sixMarked1 : sixClass1.all sixMark1 = true := by decide

private theorem sixPair1_0 : markedPairs sixMark1 sixChunk1_0 sixClass1 = true := by decide

private theorem sixPair1_1 : markedPairs sixMark1 sixChunk1_1 sixClass1 = true := by decide

private theorem sixPair1_2 : markedPairs sixMark1 sixChunk1_2 sixClass1 = true := by decide

private theorem sixPair1_3 : markedPairs sixMark1 sixChunk1_3 sixClass1 = true := by decide

private theorem sixPair1_4 : markedPairs sixMark1 sixChunk1_4 sixClass1 = true := by decide

private theorem sixFree1 : SumFree sixClass1.toFinset := by
  apply sumFree_of_marked _ sixMark1 sixMarked1
  apply pairs_of_chunks
  simp only [sixRows1, List.all_cons, List.all_nil, sixPair1_0, sixPair1_1, sixPair1_2, sixPair1_3, sixPair1_4, Bool.and_self]

private def sixMark2 (x : ℕ) : Bool :=
  (if x.blt 269 then (if x.blt 132 then (if x.blt 77 then (if x.blt 39 then (if x.blt 22 then (if x.blt 12 then (if x.blt 5 then (x == 2) else if x == 5 then true else false) else if x == 12 then true else (x == 19)) else if x == 22 then true else (if x.blt 29 then (x == 26) else if x == 29 then true else (x == 36))) else if x == 39 then true else (if x.blt 56 then (if x.blt 50 then (if x.blt 46 then (x == 43) else if x == 46 then true else false) else if x == 50 then true else (x == 53)) else if x == 56 then true else (if x.blt 63 then (x == 60) else if x == 63 then true else (x == 74)))) else if x == 77 then true else (if x.blt 108 then (if x.blt 94 then (if x.blt 87 then (if x.blt 84 then (x == 80) else if x == 84 then true else false) else if x == 87 then true else (x == 91)) else if x == 94 then true else (if x.blt 101 then (x == 98) else if x == 101 then true else (x == 104))) else if x == 108 then true else (if x.blt 121 then (if x.blt 115 then (x == 111) else if x == 115 then true else (x == 118)) else if x == 121 then true else (if x.blt 128 then (x == 125) else if x == 128 then true else (x == 131))))) else if x == 132 then true else (if x.blt 210 then (if x.blt 166 then (if x.blt 152 then (if x.blt 145 then (if x.blt 142 then (x == 135) else if x == 142 then true else false) else if x == 145 then true else (x == 149)) else if x == 152 then true else (if x.blt 156 then (x == 155) else if x == 156 then true else (x == 159))) else if x == 166 then true else (if x.blt 190 then (if x.blt 176 then (if x.blt 173 then (x == 169) else if x == 173 then true else false) else if x == 176 then true else (x == 183)) else if x == 190 then true else (if x.blt 197 then (x == 193) else if x == 197 then true else (x == 204)))) else if x == 210 then true else (if x.blt 241 then (if x.blt 228 then (if x.blt 221 then (if x.blt 217 then (x == 214) else if x == 217 then true else false) else if x == 221 then true else (x == 224)) else if x == 228 then true else (if x.blt 234 then (x == 231) else if x == 234 then true else (x == 238))) else if x == 241 then true else (if x.blt 255 then (if x.blt 245 then (x == 244) else if x == 245 then true else (x == 248)) else if x == 255 then true else (if x.blt 265 then (x == 258) else if x == 265 then true else (x == 268)))))) else if x == 269 then true else (if x.blt 405 then (if x.blt 340 then (if x.blt 303 then (if x.blt 292 then (if x.blt 282 then (if x.blt 279 then (x == 272) else if x == 279 then true else false) else if x == 282 then true else (x == 289)) else if x == 292 then true else (if x.blt 296 then (x == 293) else if x == 296 then true else (x == 299))) else if x == 303 then true else (if x.blt 320 then (if x.blt 313 then (if x.blt 309 then (x == 306) else if x == 309 then true else false) else if x == 313 then true else (x == 316)) else if x == 320 then true else (if x.blt 327 then (x == 323) else if x == 327 then true else (x == 333)))) else if x == 340 then true else (if x.blt 378 then (if x.blt 361 then (if x.blt 354 then (if x.blt 347 then (x == 344) else if x == 347 then true else false) else if x == 354 then true else (x == 358)) else if x == 361 then true else (if x.blt 368 then (x == 364) else if x == 368 then true else (x == 371))) else if x == 378 then true else (if x.blt 388 then (if x.blt 382 then (x == 381) else if x == 382 then true else (x == 385)) else if x == 388 then true else (if x.blt 395 then (x == 392) else if x == 395 then true else (x == 402))))) else if x == 405 then true else (if x.blt 460 then (if x.blt 433 then (if x.blt 419 then (if x.blt 412 then (if x.blt 409 then (x == 406) else if x == 409 then true else false) else if x == 412 then true else (x == 416)) else if x == 419 then true else (if x.blt 426 then (x == 422) else if x == 426 then true else (x == 429))) else if x == 433 then true else (if x.blt 446 then (if x.blt 439 then (x == 436) else if x == 439 then true else (x == 443)) else if x == 446 then true else (if x.blt 453 then (x == 450) else if x == 453 then true else (x == 457)))) else if x == 460 then true else (if x.blt 501 then (if x.blt 487 then (if x.blt 481 then (if x.blt 477 then (x == 474) else if x == 477 then true else false) else if x == 481 then true else (x == 484)) else if x == 487 then true else (if x.blt 494 then (x == 491) else if x == 494 then true else (x == 498))) else if x == 501 then true else (if x.blt 518 then (if x.blt 511 then (x == 508) else if x == 511 then true else (x == 515)) else if x == 518 then true else (if x.blt 532 then (x == 525) else if x == 532 then true else (x == 535)))))))

example : sixMark2 2 = true := rfl
example : sixMark2 0 = false := rfl

private theorem sixMarked2 : sixClass2.all sixMark2 = true := by decide

private theorem sixPair2_0 : markedPairs sixMark2 sixChunk2_0 sixClass2 = true := by decide

private theorem sixPair2_1 : markedPairs sixMark2 sixChunk2_1 sixClass2 = true := by decide

private theorem sixPair2_2 : markedPairs sixMark2 sixChunk2_2 sixClass2 = true := by decide

private theorem sixPair2_3 : markedPairs sixMark2 sixChunk2_3 sixClass2 = true := by decide

private theorem sixPair2_4 : markedPairs sixMark2 sixChunk2_4 sixClass2 = true := by decide

private theorem sixPair2_5 : markedPairs sixMark2 sixChunk2_5 sixClass2 = true := by decide

private theorem sixPair2_6 : markedPairs sixMark2 sixChunk2_6 sixClass2 = true := by decide

private theorem sixPair2_7 : markedPairs sixMark2 sixChunk2_7 sixClass2 = true := by decide

private theorem sixPair2_8 : markedPairs sixMark2 sixChunk2_8 sixClass2 = true := by decide

private theorem sixFree2 : SumFree sixClass2.toFinset := by
  apply sumFree_of_marked _ sixMark2 sixMarked2
  apply pairs_of_chunks
  simp only [sixRows2, List.all_cons, List.all_nil, sixPair2_0, sixPair2_1, sixPair2_2, sixPair2_3, sixPair2_4, sixPair2_5, sixPair2_6, sixPair2_7, sixPair2_8, Bool.and_self]

private def sixMark3 (x : ℕ) : Bool :=
  (if x.blt 275 then (if x.blt 141 then (if x.blt 67 then (if x.blt 27 then (if x.blt 10 then (if x.blt 7 then (x == 4) else if x == 7 then true else false) else if x == 10 then true else (x == 21)) else if x == 27 then true else (if x.blt 33 then (x == 30) else if x == 33 then true else (x == 47))) else if x == 67 then true else (if x.blt 110 then (if x.blt 86 then (if x.blt 85 then (x == 70) else if x == 85 then true else false) else if x == 86 then true else (x == 109)) else if x == 110 then true else (if x.blt 127 then (x == 126) else if x == 127 then true else (x == 138)))) else if x == 141 then true else (if x.blt 202 then (if x.blt 164 then (if x.blt 158 then (if x.blt 150 then (x == 144) else if x == 150 then true else false) else if x == 158 then true else (x == 161)) else if x == 164 then true else (if x.blt 178 then (x == 167) else if x == 178 then true else (x == 184))) else if x == 202 then true else (if x.blt 240 then (if x.blt 222 then (x == 216) else if x == 222 then true else (x == 239)) else if x == 240 then true else (if x.blt 257 then (x == 256) else if x == 257 then true else (x == 262))))) else if x == 275 then true else (if x.blt 399 then (if x.blt 359 then (if x.blt 315 then (if x.blt 297 then (if x.blt 281 then (x == 280) else if x == 281 then true else false) else if x == 297 then true else (x == 298)) else if x == 315 then true else (if x.blt 335 then (x == 321) else if x == 335 then true else (x == 353))) else if x == 359 then true else (if x.blt 379 then (if x.blt 373 then (x == 370) else if x == 373 then true else (x == 376)) else if x == 379 then true else (if x.blt 393 then (x == 387) else if x == 393 then true else (x == 396)))) else if x == 399 then true else (if x.blt 490 then (if x.blt 451 then (if x.blt 427 then (if x.blt 411 then (x == 410) else if x == 411 then true else false) else if x == 427 then true else (x == 428)) else if x == 451 then true else (if x.blt 467 then (x == 452) else if x == 467 then true else (x == 470))) else if x == 490 then true else (if x.blt 516 then (if x.blt 507 then (x == 504) else if x == 507 then true else (x == 510)) else if x == 516 then true else (if x.blt 530 then (x == 527) else if x == 530 then true else (x == 533))))))

example : sixMark3 4 = true := rfl
example : sixMark3 0 = false := rfl

private theorem sixMarked3 : sixClass3.all sixMark3 = true := by decide

private theorem sixPair3_0 : markedPairs sixMark3 sixChunk3_0 sixClass3 = true := by decide

private theorem sixPair3_1 : markedPairs sixMark3 sixChunk3_1 sixClass3 = true := by decide

private theorem sixPair3_2 : markedPairs sixMark3 sixChunk3_2 sixClass3 = true := by decide

private theorem sixPair3_3 : markedPairs sixMark3 sixChunk3_3 sixClass3 = true := by decide

private theorem sixPair3_4 : markedPairs sixMark3 sixChunk3_4 sixClass3 = true := by decide

private theorem sixFree3 : SumFree sixClass3.toFinset := by
  apply sumFree_of_marked _ sixMark3 sixMarked3
  apply pairs_of_chunks
  simp only [sixRows3, List.all_cons, List.all_nil, sixPair3_0, sixPair3_1, sixPair3_2, sixPair3_3, sixPair3_4, Bool.and_self]

private def sixMark4 (x : ℕ) : Bool :=
  (if x.blt 276 then (if x.blt 137 then (if x.blt 41 then (if x.blt 20 then (if x.blt 11 then (if x.blt 6 then (x == 1) else if x == 6 then true else false) else if x == 11 then true else (x == 16)) else if x == 20 then true else (if x.blt 34 then (x == 24) else if x == 34 then true else (x == 37))) else if x == 41 then true else (if x.blt 105 then (if x.blt 97 then (x == 90) else if x == 97 then true else (x == 102)) else if x == 105 then true else (if x.blt 120 then (x == 107) else if x == 120 then true else (x == 130)))) else if x == 137 then true else (if x.blt 182 then (if x.blt 168 then (if x.blt 160 then (if x.blt 151 then (x == 147) else if x == 151 then true else false) else if x == 160 then true else (x == 165)) else if x == 168 then true else (if x.blt 172 then (x == 170) else if x == 172 then true else (x == 177))) else if x == 182 then true else (if x.blt 246 then (if x.blt 233 then (x == 229) else if x == 233 then true else (x == 236)) else if x == 246 then true else (if x.blt 259 then (x == 251) else if x == 259 then true else (x == 261))))) else if x == 276 then true else (if x.blt 407 then (if x.blt 365 then (if x.blt 304 then (if x.blt 291 then (if x.blt 286 then (x == 278) else if x == 286 then true else false) else if x == 291 then true else (x == 301)) else if x == 304 then true else (if x.blt 355 then (x == 308) else if x == 355 then true else (x == 360))) else if x == 365 then true else (if x.blt 377 then (if x.blt 369 then (x == 367) else if x == 369 then true else (x == 372)) else if x == 377 then true else (if x.blt 390 then (x == 386) else if x == 390 then true else (x == 400)))) else if x == 407 then true else (if x.blt 500 then (if x.blt 435 then (if x.blt 430 then (x == 417) else if x == 430 then true else (x == 432)) else if x == 435 then true else (if x.blt 447 then (x == 440) else if x == 447 then true else (x == 496))) else if x == 500 then true else (if x.blt 521 then (if x.blt 513 then (x == 503) else if x == 513 then true else (x == 517)) else if x == 521 then true else (if x.blt 531 then (x == 526) else if x == 531 then true else (x == 536))))))

example : sixMark4 1 = true := rfl
example : sixMark4 0 = false := rfl

private theorem sixMarked4 : sixClass4.all sixMark4 = true := by decide

private theorem sixPair4_0 : markedPairs sixMark4 sixChunk4_0 sixClass4 = true := by decide

private theorem sixPair4_1 : markedPairs sixMark4 sixChunk4_1 sixClass4 = true := by decide

private theorem sixPair4_2 : markedPairs sixMark4 sixChunk4_2 sixClass4 = true := by decide

private theorem sixPair4_3 : markedPairs sixMark4 sixChunk4_3 sixClass4 = true := by decide

private theorem sixPair4_4 : markedPairs sixMark4 sixChunk4_4 sixClass4 = true := by decide

private theorem sixFree4 : SumFree sixClass4.toFinset := by
  apply sumFree_of_marked _ sixMark4 sixMarked4
  apply pairs_of_chunks
  simp only [sixRows4, List.all_cons, List.all_nil, sixPair4_0, sixPair4_1, sixPair4_2, sixPair4_3, sixPair4_4, Bool.and_self]

private def sixMark5 (x : ℕ) : Bool :=
  (if x.blt 302 then (if x.blt 188 then (if x.blt 71 then (if x.blt 61 then (if x.blt 51 then (if x.blt 45 then (x == 40) else if x == 45 then true else (x == 49)) else if x == 51 then true else (if x.blt 58 then (x == 57) else if x == 58 then true else false)) else if x == 61 then true else (if x.blt 66 then (if x.blt 65 then (x == 62) else if x == 65 then true else false) else if x == 66 then true else (if x.blt 69 then (x == 68) else if x == 69 then true else false))) else if x == 71 then true else (if x.blt 82 then (if x.blt 75 then (if x.blt 73 then (x == 72) else if x == 73 then true else false) else if x == 75 then true else (if x.blt 81 then (x == 78) else if x == 81 then true else false)) else if x == 82 then true else (if x.blt 171 then (if x.blt 92 then (x == 88) else if x == 92 then true else false) else if x == 171 then true else (if x.blt 187 then (x == 181) else if x == 187 then true else false)))) else if x == 188 then true else (if x.blt 206 then (if x.blt 198 then (if x.blt 192 then (if x.blt 191 then (x == 189) else if x == 191 then true else false) else if x == 192 then true else (if x.blt 196 then (x == 194) else if x == 196 then true else false)) else if x == 198 then true else (if x.blt 201 then (if x.blt 200 then (x == 199) else if x == 200 then true else false) else if x == 201 then true else (if x.blt 205 then (x == 203) else if x == 205 then true else false))) else if x == 206 then true else (if x.blt 215 then (if x.blt 209 then (if x.blt 208 then (x == 207) else if x == 208 then true else false) else if x == 209 then true else (if x.blt 213 then (x == 212) else if x == 213 then true else false)) else if x == 215 then true else (if x.blt 223 then (if x.blt 219 then (x == 218) else if x == 219 then true else false) else if x == 223 then true else (if x.blt 235 then (x == 225) else if x == 235 then true else false))))) else if x == 302 then true else (if x.blt 356 then (if x.blt 334 then (if x.blt 325 then (if x.blt 319 then (if x.blt 314 then (x == 312) else if x == 314 then true else (x == 318)) else if x == 319 then true else (if x.blt 324 then (x == 322) else if x == 324 then true else false)) else if x == 325 then true else (if x.blt 330 then (if x.blt 329 then (x == 328) else if x == 329 then true else false) else if x == 330 then true else (if x.blt 332 then (x == 331) else if x == 332 then true else false))) else if x == 334 then true else (if x.blt 343 then (if x.blt 338 then (if x.blt 337 then (x == 336) else if x == 337 then true else false) else if x == 338 then true else (if x.blt 341 then (x == 339) else if x == 341 then true else false)) else if x == 343 then true else (if x.blt 348 then (if x.blt 346 then (x == 345) else if x == 346 then true else false) else if x == 348 then true else (if x.blt 350 then (x == 349) else if x == 350 then true else false)))) else if x == 356 then true else (if x.blt 468 then (if x.blt 459 then (if x.blt 449 then (if x.blt 445 then (x == 366) else if x == 445 then true else false) else if x == 449 then true else (if x.blt 456 then (x == 455) else if x == 456 then true else false)) else if x == 459 then true else (if x.blt 464 then (if x.blt 463 then (x == 462) else if x == 463 then true else false) else if x == 464 then true else (if x.blt 466 then (x == 465) else if x == 466 then true else false))) else if x == 468 then true else (if x.blt 479 then (if x.blt 472 then (if x.blt 471 then (x == 469) else if x == 471 then true else false) else if x == 472 then true else (if x.blt 476 then (x == 475) else if x == 476 then true else false)) else if x == 479 then true else (if x.blt 488 then (if x.blt 486 then (x == 480) else if x == 486 then true else false) else if x == 488 then true else (if x.blt 497 then (x == 492) else if x == 497 then true else false))))))

example : sixMark5 40 = true := rfl
example : sixMark5 0 = false := rfl

private theorem sixMarked5 : sixClass5.all sixMark5 = true := by decide

private theorem sixPair5_0 : markedPairs sixMark5 sixChunk5_0 sixClass5 = true := by decide

private theorem sixPair5_1 : markedPairs sixMark5 sixChunk5_1 sixClass5 = true := by decide

private theorem sixPair5_2 : markedPairs sixMark5 sixChunk5_2 sixClass5 = true := by decide

private theorem sixPair5_3 : markedPairs sixMark5 sixChunk5_3 sixClass5 = true := by decide

private theorem sixPair5_4 : markedPairs sixMark5 sixChunk5_4 sixClass5 = true := by decide

private theorem sixPair5_5 : markedPairs sixMark5 sixChunk5_5 sixClass5 = true := by decide

private theorem sixPair5_6 : markedPairs sixMark5 sixChunk5_6 sixClass5 = true := by decide

private theorem sixFree5 : SumFree sixClass5.toFinset := by
  apply sumFree_of_marked _ sixMark5 sixMarked5
  apply pairs_of_chunks
  simp only [sixRows5, List.all_cons, List.all_nil, sixPair5_0, sixPair5_1, sixPair5_2, sixPair5_3, sixPair5_4, sixPair5_5, sixPair5_6, Bool.and_self]

private theorem sixCover0 : covered sixColor sixClasses 1 32 = true := by decide

private theorem sixCover1 : covered sixColor sixClasses 33 32 = true := by decide

private theorem sixCover2 : covered sixColor sixClasses 65 32 = true := by decide

private theorem sixCover3 : covered sixColor sixClasses 97 32 = true := by decide

private theorem sixCover4 : covered sixColor sixClasses 129 32 = true := by decide

private theorem sixCover5 : covered sixColor sixClasses 161 32 = true := by decide

private theorem sixCover6 : covered sixColor sixClasses 193 32 = true := by decide

private theorem sixCover7 : covered sixColor sixClasses 225 32 = true := by decide

private theorem sixCover8 : covered sixColor sixClasses 257 32 = true := by decide

private theorem sixCover9 : covered sixColor sixClasses 289 32 = true := by decide

private theorem sixCover10 : covered sixColor sixClasses 321 32 = true := by decide

private theorem sixCover11 : covered sixColor sixClasses 353 32 = true := by decide

private theorem sixCover12 : covered sixColor sixClasses 385 32 = true := by decide

private theorem sixCover13 : covered sixColor sixClasses 417 32 = true := by decide

private theorem sixCover14 : covered sixColor sixClasses 449 32 = true := by decide

private theorem sixCover15 : covered sixColor sixClasses 481 32 = true := by decide

private theorem sixCover16 : covered sixColor sixClasses 513 24 = true := by decide

private theorem sixCoverage : ∀ x ∈ Finset.Icc 1 536, x ∈ sixClasses (sixColor x) := by
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp hx

  by_cases h1 : x < 33
  · exact covered_spec _ _ 1 32 sixCover0 x (by omega) h1

  by_cases h33 : x < 65
  · exact covered_spec _ _ 33 32 sixCover1 x (by omega) h33

  by_cases h65 : x < 97
  · exact covered_spec _ _ 65 32 sixCover2 x (by omega) h65

  by_cases h97 : x < 129
  · exact covered_spec _ _ 97 32 sixCover3 x (by omega) h97

  by_cases h129 : x < 161
  · exact covered_spec _ _ 129 32 sixCover4 x (by omega) h129

  by_cases h161 : x < 193
  · exact covered_spec _ _ 161 32 sixCover5 x (by omega) h161

  by_cases h193 : x < 225
  · exact covered_spec _ _ 193 32 sixCover6 x (by omega) h193

  by_cases h225 : x < 257
  · exact covered_spec _ _ 225 32 sixCover7 x (by omega) h225

  by_cases h257 : x < 289
  · exact covered_spec _ _ 257 32 sixCover8 x (by omega) h257

  by_cases h289 : x < 321
  · exact covered_spec _ _ 289 32 sixCover9 x (by omega) h289

  by_cases h321 : x < 353
  · exact covered_spec _ _ 321 32 sixCover10 x (by omega) h321

  by_cases h353 : x < 385
  · exact covered_spec _ _ 353 32 sixCover11 x (by omega) h353

  by_cases h385 : x < 417
  · exact covered_spec _ _ 385 32 sixCover12 x (by omega) h385

  by_cases h417 : x < 449
  · exact covered_spec _ _ 417 32 sixCover13 x (by omega) h417

  by_cases h449 : x < 481
  · exact covered_spec _ _ 449 32 sixCover14 x (by omega) h449

  by_cases h481 : x < 513
  · exact covered_spec _ _ 481 32 sixCover15 x (by omega) h481

  exact covered_spec _ _ 513 24 sixCover16 x (by omega) (by omega)

/-- Rowley's first-536 restriction of the seven-color workbook gives a sum-free 6-coloring through 536, including diagonal sums. -/
theorem schur_six_lower : SchurColorable 6 536 := by
  apply colorable_of_lists sixColor sixClasses sixCoverage
  intro i
  fin_cases i

  · exact sixFree0

  · exact sixFree1

  · exact sixFree2

  · exact sixFree3

  · exact sixFree4

  · exact sixFree5

example : SchurColorable 6 536 := schur_six_lower

private def mergeApart : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => true
  | _ + 1, _, [] => true
  | k + 1, a :: as, b :: bs =>
    if a < b then mergeApart k as (b :: bs)
    else if b < a then mergeApart k (a :: as) bs else false
example : mergeApart 5 [1, 3] [2, 4] = true := rfl
example : mergeApart 5 [1, 3] [2, 3] = false := rfl
private theorem mergeApart_sound (k : ℕ) (xs ys : List ℕ)
    (hs : xs.Pairwise (· ≤ ·)) (ht : ys.Pairwise (· ≤ ·))
    (h : mergeApart k xs ys = true) : ∀ z ∈ xs, z ∉ ys := by
  induction k generalizing xs ys with
  | zero => simp [mergeApart] at h
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons a as =>
      cases ys with
      | nil => simp
      | cons b bs =>
        obtain ⟨ha, has⟩ := List.pairwise_cons.mp hs
        obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp ht
        by_cases hab : a < b
        · have hh : mergeApart k as (b :: bs) = true := by simpa [mergeApart, hab] using h
          intro z hz hz'
          rcases List.mem_cons.mp hz with rfl | hzas
          · rcases List.mem_cons.mp hz' with heq | hzbs
            · omega
            · have hba := hb _ hzbs
              omega
          · exact ih as (b :: bs) has ht hh z hzas hz'
        · by_cases hba : b < a
          · have hh : mergeApart k (a :: as) bs = true := by simpa [mergeApart, hab, hba] using h
            intro z hz hz'
            rcases List.mem_cons.mp hz' with rfl | hzbs
            · rcases List.mem_cons.mp hz with heq | hbas
              · omega
              · have hab' := ha _ hbas
                omega
            · exact ih (a :: as) bs hs hbs hh z hz hzbs
          · simp [mergeApart, hab, hba] at h
private def mergeRows (xs ys : List ℕ) : Bool :=
  xs.all fun x => mergeApart (2 * ys.length + 1) ys (ys.map (x + ·))
example : mergeRows [1] [1] = true := rfl
private theorem sumFree_of_merge (xs : List ℕ)
    (hs : xs.Pairwise (· ≤ ·)) (h : mergeRows xs xs = true) : SumFree xs.toFinset := by
  intro x hx y hy z hz heq
  have hx' : x ∈ xs := List.mem_toFinset.mp hx
  have hy' : y ∈ xs := List.mem_toFinset.mp hy
  have hz' : z ∈ xs := List.mem_toFinset.mp hz
  have hm := List.all_eq_true.mp h x hx'
  have hsorted : (xs.map (x + ·)).Pairwise (· ≤ ·) :=
    List.pairwise_map.mpr (hs.imp (fun hab => Nat.add_le_add_left hab x))
  exact mergeApart_sound _ xs (xs.map (x + ·)) hs hsorted hm z hz'
    (List.mem_map.mpr ⟨y, hy', heq⟩)
example : SumFree ([1] : List ℕ).toFinset := sumFree_of_merge [1] (by decide) rfl

private def sevenChunk0_0 : List ℕ := [8, 9, 14, 15, 25, 31, 32, 35, 42, 52, 55, 59, 76, 79, 89, 95]

example : sevenChunk0_0.length = 16 := rfl

private def sevenChunk0_1 : List ℕ := [96, 99, 100, 106, 112, 116, 117, 119, 129, 136, 139, 140, 146, 157, 162, 163]

example : sevenChunk0_1.length = 16 := rfl

private def sevenChunk0_2 : List ℕ := [180, 186, 220, 226, 227, 230, 237, 243, 247, 249, 250, 260, 266, 267, 270, 271]

example : sevenChunk0_2.length = 16 := rfl

private def sevenChunk0_3 : List ℕ := [277, 287, 288, 290, 294, 300, 307, 310, 311, 317, 351, 357, 374, 375, 380, 391]

example : sevenChunk0_3.length = 16 := rfl

private def sevenChunk0_4 : List ℕ := [397, 398, 401, 408, 418, 420, 421, 425, 431, 437, 438, 441, 442, 448, 458, 461]

example : sevenChunk0_4.length = 16 := rfl

private def sevenChunk0_5 : List ℕ := [478, 482, 485, 495, 502, 505, 506, 512, 522, 523, 528, 529, 545, 551, 552, 562]

example : sevenChunk0_5.length = 16 := rfl

private def sevenChunk0_6 : List ℕ := [568, 569, 572, 589, 592, 609, 1088, 1105, 1108, 1125, 1128, 1129, 1135, 1145, 1146, 1152]

example : sevenChunk0_6.length = 16 := rfl

private def sevenChunk0_7 : List ℕ := [1168, 1169, 1174, 1175, 1185, 1191, 1192, 1195, 1202, 1212, 1215, 1219, 1236, 1239, 1249, 1255]

example : sevenChunk0_7.length = 16 := rfl

private def sevenChunk0_8 : List ℕ := [1256, 1259, 1260, 1266, 1272, 1276, 1277, 1279, 1289, 1296, 1299, 1300, 1306, 1317, 1322, 1323]

example : sevenChunk0_8.length = 16 := rfl

private def sevenChunk0_9 : List ℕ := [1340, 1346, 1380, 1386, 1387, 1390, 1397, 1403, 1407, 1409, 1410, 1420, 1426, 1427, 1430, 1431]

example : sevenChunk0_9.length = 16 := rfl

private def sevenChunk0_10 : List ℕ := [1437, 1447, 1448, 1450, 1454, 1460, 1467, 1470, 1471, 1477, 1511, 1517, 1534, 1535, 1540, 1551]

example : sevenChunk0_10.length = 16 := rfl

private def sevenChunk0_11 : List ℕ := [1557, 1558, 1561, 1568, 1578, 1580, 1581, 1585, 1591, 1597, 1598, 1601, 1602, 1608, 1618, 1621]

example : sevenChunk0_11.length = 16 := rfl

private def sevenChunk0_12 : List ℕ := [1638, 1642, 1645, 1655, 1662, 1665, 1666, 1672, 1682, 1683, 1688, 1689]

example : sevenChunk0_12.length = 12 := rfl

private def sevenRows0 : List (List ℕ) := [sevenChunk0_0, sevenChunk0_1, sevenChunk0_2, sevenChunk0_3, sevenChunk0_4, sevenChunk0_5, sevenChunk0_6, sevenChunk0_7, sevenChunk0_8, sevenChunk0_9, sevenChunk0_10, sevenChunk0_11, sevenChunk0_12]

private def sevenClass0 : List ℕ := sevenRows0.flatten

example : sevenClass0.length = 204 := rfl

private def sevenChunk1_0 : List ℕ := [3, 13, 17, 18, 23, 28, 38, 44, 48, 54, 64, 83, 93, 103, 113, 114]

example : sevenChunk1_0.length = 16 := rfl

private def sevenChunk1_1 : List ℕ := [122, 123, 124, 133, 134, 143, 148, 153, 154, 174, 175, 179, 185, 195, 211, 232]

example : sevenChunk1_1.length = 16 := rfl

private def sevenChunk1_2 : List ℕ := [242, 252, 253, 254, 263, 264, 273, 274, 283, 284, 285, 295, 305, 326, 342, 352]

example : sevenChunk1_2.length = 16 := rfl

private def sevenChunk1_3 : List ℕ := [362, 363, 383, 384, 389, 394, 403, 404, 413, 414, 415, 423, 424, 434, 444, 454]

example : sevenChunk1_3.length = 16 := rfl

private def sevenChunk1_4 : List ℕ := [473, 483, 489, 493, 499, 509, 514, 519, 520, 524, 534, 540, 544, 550, 554, 555]

example : sevenChunk1_4.length = 16 := rfl

private def sevenChunk1_5 : List ℕ := [560, 565, 575, 581, 585, 591, 601, 620, 1077, 1096, 1106, 1112, 1116, 1122, 1132, 1137]

example : sevenChunk1_5.length = 16 := rfl

private def sevenChunk1_6 : List ℕ := [1142, 1143, 1147, 1153, 1157, 1163, 1173, 1177, 1178, 1183, 1188, 1198, 1204, 1208, 1214, 1224]

example : sevenChunk1_6.length = 16 := rfl

private def sevenChunk1_7 : List ℕ := [1243, 1253, 1263, 1273, 1274, 1282, 1283, 1284, 1293, 1294, 1303, 1308, 1313, 1314, 1334, 1335]

example : sevenChunk1_7.length = 16 := rfl

private def sevenChunk1_8 : List ℕ := [1345, 1355, 1371, 1392, 1402, 1412, 1413, 1414, 1423, 1424, 1433, 1434, 1443, 1444, 1445, 1455]

example : sevenChunk1_8.length = 16 := rfl

private def sevenChunk1_9 : List ℕ := [1465, 1486, 1502, 1512, 1518, 1522, 1523, 1543, 1544, 1549, 1554, 1563, 1564, 1573, 1574, 1575]

example : sevenChunk1_9.length = 16 := rfl

private def sevenChunk1_10 : List ℕ := [1583, 1584, 1594, 1604, 1614, 1633, 1643, 1649, 1653, 1659, 1669, 1674, 1679, 1680, 1684, 1694]

example : sevenChunk1_10.length = 16 := rfl

private def sevenRows1 : List (List ℕ) := [sevenChunk1_0, sevenChunk1_1, sevenChunk1_2, sevenChunk1_3, sevenChunk1_4, sevenChunk1_5, sevenChunk1_6, sevenChunk1_7, sevenChunk1_8, sevenChunk1_9, sevenChunk1_10]

private def sevenClass1 : List ℕ := sevenRows1.flatten

example : sevenClass1.length = 176 := rfl

private def sevenChunk2_0 : List ℕ := [2, 5, 12, 19, 22, 26, 29, 36, 39, 43, 46, 50, 53, 56, 60, 63]

example : sevenChunk2_0.length = 16 := rfl

private def sevenChunk2_1 : List ℕ := [74, 77, 80, 84, 87, 91, 94, 98, 101, 104, 108, 111, 115, 118, 121, 125]

example : sevenChunk2_1.length = 16 := rfl

private def sevenChunk2_2 : List ℕ := [128, 131, 132, 135, 142, 145, 149, 152, 155, 156, 159, 166, 169, 173, 176, 183]

example : sevenChunk2_2.length = 16 := rfl

private def sevenChunk2_3 : List ℕ := [190, 193, 197, 204, 210, 214, 217, 221, 224, 228, 231, 234, 238, 241, 244, 245]

example : sevenChunk2_3.length = 16 := rfl

private def sevenChunk2_4 : List ℕ := [248, 255, 258, 265, 268, 269, 272, 279, 282, 289, 292, 293, 296, 299, 303, 306]

example : sevenChunk2_4.length = 16 := rfl

private def sevenChunk2_5 : List ℕ := [309, 313, 316, 320, 323, 327, 333, 340, 344, 347, 354, 358, 361, 364, 368, 371]

example : sevenChunk2_5.length = 16 := rfl

private def sevenChunk2_6 : List ℕ := [378, 381, 382, 385, 388, 392, 395, 402, 405, 406, 409, 412, 416, 419, 422, 426]

example : sevenChunk2_6.length = 16 := rfl

private def sevenChunk2_7 : List ℕ := [429, 433, 436, 439, 443, 446, 450, 453, 457, 460, 474, 477, 481, 484, 487, 491]

example : sevenChunk2_7.length = 16 := rfl

private def sevenChunk2_8 : List ℕ := [494, 498, 501, 508, 511, 515, 518, 525, 532, 535, 539, 542, 546, 549, 556, 559]

example : sevenChunk2_8.length = 16 := rfl

private def sevenChunk2_9 : List ℕ := [563, 566, 573, 576, 580, 583, 587, 590, 597, 600, 604, 607, 611, 614, 621, 1076]

example : sevenChunk2_9.length = 16 := rfl

private def sevenChunk2_10 : List ℕ := [1083, 1086, 1090, 1093, 1097, 1100, 1107, 1110, 1114, 1117, 1121, 1124, 1131, 1134, 1138, 1141]

example : sevenChunk2_10.length = 16 := rfl

private def sevenChunk2_11 : List ℕ := [1148, 1151, 1155, 1158, 1162, 1165, 1172, 1179, 1182, 1186, 1189, 1196, 1199, 1203, 1206, 1210]

example : sevenChunk2_11.length = 16 := rfl

private def sevenChunk2_12 : List ℕ := [1213, 1216, 1220, 1223, 1237, 1240, 1244, 1247, 1251, 1254, 1258, 1261, 1264, 1268, 1271, 1275]

example : sevenChunk2_12.length = 16 := rfl

private def sevenChunk2_13 : List ℕ := [1278, 1281, 1285, 1288, 1291, 1292, 1295, 1302, 1305, 1309, 1312, 1315, 1316, 1319, 1326, 1329]

example : sevenChunk2_13.length = 16 := rfl

private def sevenChunk2_14 : List ℕ := [1333, 1336, 1339, 1343, 1350, 1353, 1357, 1364, 1370, 1374, 1377, 1381, 1384, 1388, 1391, 1394]

example : sevenChunk2_14.length = 16 := rfl

private def sevenChunk2_15 : List ℕ := [1398, 1401, 1404, 1405, 1408, 1415, 1418, 1425, 1428, 1429, 1432, 1439, 1442, 1449, 1452, 1453]

example : sevenChunk2_15.length = 16 := rfl

private def sevenChunk2_16 : List ℕ := [1456, 1459, 1463, 1466, 1469, 1473, 1476, 1480, 1483, 1487, 1493, 1500, 1504, 1507, 1514, 1521]

example : sevenChunk2_16.length = 16 := rfl

private def sevenChunk2_17 : List ℕ := [1524, 1528, 1531, 1538, 1541, 1542, 1545, 1548, 1552, 1555, 1562, 1565, 1566, 1569, 1572, 1576]

example : sevenChunk2_17.length = 16 := rfl

private def sevenChunk2_18 : List ℕ := [1579, 1582, 1586, 1589, 1593, 1596, 1599, 1603, 1606, 1610, 1613, 1617, 1620, 1623, 1634, 1637]

example : sevenChunk2_18.length = 16 := rfl

private def sevenChunk2_19 : List ℕ := [1641, 1644, 1647, 1651, 1654, 1658, 1661, 1668, 1671, 1675, 1678, 1685, 1692, 1695]

example : sevenChunk2_19.length = 14 := rfl

private def sevenRows2 : List (List ℕ) := [sevenChunk2_0, sevenChunk2_1, sevenChunk2_2, sevenChunk2_3, sevenChunk2_4, sevenChunk2_5, sevenChunk2_6, sevenChunk2_7, sevenChunk2_8, sevenChunk2_9, sevenChunk2_10, sevenChunk2_11, sevenChunk2_12, sevenChunk2_13, sevenChunk2_14, sevenChunk2_15, sevenChunk2_16, sevenChunk2_17, sevenChunk2_18, sevenChunk2_19]

private def sevenClass2 : List ℕ := sevenRows2.flatten

example : sevenClass2.length = 318 := rfl

private def sevenChunk3_0 : List ℕ := [4, 7, 10, 21, 27, 30, 33, 47, 67, 70, 85, 86, 109, 110, 126, 127]

example : sevenChunk3_0.length = 16 := rfl

private def sevenChunk3_1 : List ℕ := [138, 141, 144, 150, 158, 161, 164, 167, 178, 184, 202, 216, 222, 239, 240, 256]

example : sevenChunk3_1.length = 16 := rfl

private def sevenChunk3_2 : List ℕ := [257, 262, 275, 280, 281, 297, 298, 315, 321, 335, 353, 359, 370, 373, 376, 379]

example : sevenChunk3_2.length = 16 := rfl

private def sevenChunk3_3 : List ℕ := [387, 393, 396, 399, 410, 411, 427, 428, 451, 452, 467, 470, 490, 504, 507, 510]

example : sevenChunk3_3.length = 16 := rfl

private def sevenChunk3_4 : List ℕ := [516, 527, 530, 533, 541, 547, 558, 564, 567, 570, 584, 622, 1075, 1113, 1127, 1130]

example : sevenChunk3_4.length = 16 := rfl

private def sevenChunk3_5 : List ℕ := [1133, 1139, 1150, 1156, 1164, 1167, 1170, 1181, 1187, 1190, 1193, 1207, 1227, 1230, 1245, 1246]

example : sevenChunk3_5.length = 16 := rfl

private def sevenChunk3_6 : List ℕ := [1269, 1270, 1286, 1287, 1298, 1301, 1304, 1310, 1318, 1321, 1324, 1327, 1338, 1344, 1362, 1376]

example : sevenChunk3_6.length = 16 := rfl

private def sevenChunk3_7 : List ℕ := [1382, 1399, 1400, 1416, 1417, 1422, 1435, 1440, 1441, 1457, 1458, 1475, 1481, 1495, 1513, 1519]

example : sevenChunk3_7.length = 16 := rfl

private def sevenChunk3_8 : List ℕ := [1530, 1533, 1536, 1539, 1547, 1553, 1556, 1559, 1570, 1571, 1587, 1588, 1611, 1612, 1627, 1630]

example : sevenChunk3_8.length = 16 := rfl

private def sevenChunk3_9 : List ℕ := [1650, 1664, 1667, 1670, 1676, 1687, 1690, 1693]

example : sevenChunk3_9.length = 8 := rfl

private def sevenRows3 : List (List ℕ) := [sevenChunk3_0, sevenChunk3_1, sevenChunk3_2, sevenChunk3_3, sevenChunk3_4, sevenChunk3_5, sevenChunk3_6, sevenChunk3_7, sevenChunk3_8, sevenChunk3_9]

private def sevenClass3 : List ℕ := sevenRows3.flatten

example : sevenClass3.length = 152 := rfl

private def sevenChunk4_0 : List ℕ := [1, 6, 11, 16, 20, 24, 34, 37, 41, 90, 97, 102, 105, 107, 120, 130]

example : sevenChunk4_0.length = 16 := rfl

private def sevenChunk4_1 : List ℕ := [137, 147, 151, 160, 165, 168, 170, 172, 177, 182, 229, 233, 236, 246, 251, 259]

example : sevenChunk4_1.length = 16 := rfl

private def sevenChunk4_2 : List ℕ := [261, 276, 278, 286, 291, 301, 304, 308, 355, 360, 365, 367, 369, 372, 377, 386]

example : sevenChunk4_2.length = 16 := rfl

private def sevenChunk4_3 : List ℕ := [390, 400, 407, 417, 430, 432, 435, 440, 447, 496, 500, 503, 513, 517, 521, 526]

example : sevenChunk4_3.length = 16 := rfl

private def sevenChunk4_4 : List ℕ := [531, 536, 538, 543, 548, 553, 557, 561, 574, 578, 1119, 1123, 1136, 1140, 1144, 1149]

example : sevenChunk4_4.length = 16 := rfl

private def sevenChunk4_5 : List ℕ := [1154, 1159, 1161, 1166, 1171, 1176, 1180, 1184, 1194, 1197, 1201, 1250, 1257, 1262, 1265, 1267]

example : sevenChunk4_5.length = 16 := rfl

private def sevenChunk4_6 : List ℕ := [1280, 1290, 1297, 1307, 1311, 1320, 1325, 1328, 1330, 1332, 1337, 1342, 1389, 1393, 1396, 1406]

example : sevenChunk4_6.length = 16 := rfl

private def sevenChunk4_7 : List ℕ := [1411, 1419, 1421, 1436, 1438, 1446, 1451, 1461, 1464, 1468, 1515, 1520, 1525, 1527, 1529, 1532]

example : sevenChunk4_7.length = 16 := rfl

private def sevenChunk4_8 : List ℕ := [1537, 1546, 1550, 1560, 1567, 1577, 1590, 1592, 1595, 1600, 1607, 1656, 1660, 1663, 1673, 1677]

example : sevenChunk4_8.length = 16 := rfl

private def sevenChunk4_9 : List ℕ := [1681, 1686, 1691, 1696]

example : sevenChunk4_9.length = 4 := rfl

private def sevenRows4 : List (List ℕ) := [sevenChunk4_0, sevenChunk4_1, sevenChunk4_2, sevenChunk4_3, sevenChunk4_4, sevenChunk4_5, sevenChunk4_6, sevenChunk4_7, sevenChunk4_8, sevenChunk4_9]

private def sevenClass4 : List ℕ := sevenRows4.flatten

example : sevenClass4.length = 148 := rfl

private def sevenChunk5_0 : List ℕ := [40, 45, 49, 51, 57, 58, 61, 62, 65, 66, 68, 69, 71, 72, 73, 75]

example : sevenChunk5_0.length = 16 := rfl

private def sevenChunk5_1 : List ℕ := [78, 81, 82, 88, 92, 171, 181, 187, 188, 189, 191, 192, 194, 196, 198, 199]

example : sevenChunk5_1.length = 16 := rfl

private def sevenChunk5_2 : List ℕ := [200, 201, 203, 205, 206, 207, 208, 209, 212, 213, 215, 218, 219, 223, 225, 235]

example : sevenChunk5_2.length = 16 := rfl

private def sevenChunk5_3 : List ℕ := [302, 312, 314, 318, 319, 322, 324, 325, 328, 329, 330, 331, 332, 334, 336, 337]

example : sevenChunk5_3.length = 16 := rfl

private def sevenChunk5_4 : List ℕ := [338, 339, 341, 343, 345, 346, 348, 349, 350, 356, 366, 445, 449, 455, 456, 459]

example : sevenChunk5_4.length = 16 := rfl

private def sevenChunk5_5 : List ℕ := [462, 463, 464, 465, 466, 468, 469, 471, 472, 475, 476, 479, 480, 486, 488, 492]

example : sevenChunk5_5.length = 16 := rfl

private def sevenChunk5_6 : List ℕ := [497, 593, 596, 623, 1074, 1101, 1104, 1200, 1205, 1209, 1211, 1217, 1218, 1221, 1222, 1225]

example : sevenChunk5_6.length = 16 := rfl

private def sevenChunk5_7 : List ℕ := [1226, 1228, 1229, 1231, 1232, 1233, 1234, 1235, 1238, 1241, 1242, 1248, 1252, 1331, 1341, 1347]

example : sevenChunk5_7.length = 16 := rfl

private def sevenChunk5_8 : List ℕ := [1348, 1349, 1351, 1352, 1354, 1356, 1358, 1359, 1360, 1361, 1363, 1365, 1366, 1367, 1368, 1369]

example : sevenChunk5_8.length = 16 := rfl

private def sevenChunk5_9 : List ℕ := [1372, 1373, 1375, 1378, 1379, 1383, 1385, 1395, 1462, 1472, 1474, 1478, 1479, 1482, 1484, 1485]

example : sevenChunk5_9.length = 16 := rfl

private def sevenChunk5_10 : List ℕ := [1488, 1489, 1490, 1491, 1492, 1494, 1496, 1497, 1498, 1499, 1501, 1503, 1505, 1506, 1508, 1509]

example : sevenChunk5_10.length = 16 := rfl

private def sevenChunk5_11 : List ℕ := [1510, 1516, 1526, 1605, 1609, 1615, 1616, 1619, 1622, 1624, 1625, 1626, 1628, 1629, 1631, 1632]

example : sevenChunk5_11.length = 16 := rfl

private def sevenChunk5_12 : List ℕ := [1635, 1636, 1639, 1640, 1646, 1648, 1652, 1657]

example : sevenChunk5_12.length = 8 := rfl

private def sevenRows5 : List (List ℕ) := [sevenChunk5_0, sevenChunk5_1, sevenChunk5_2, sevenChunk5_3, sevenChunk5_4, sevenChunk5_5, sevenChunk5_6, sevenChunk5_7, sevenChunk5_8, sevenChunk5_9, sevenChunk5_10, sevenChunk5_11, sevenChunk5_12]

private def sevenClass5 : List ℕ := sevenRows5.flatten

example : sevenClass5.length = 200 := rfl

private def sevenChunk6_0 : List ℕ := [537, 571, 577, 579, 582, 586, 588, 594, 595, 598, 599, 602, 603, 605, 606, 608]

example : sevenChunk6_0.length = 16 := rfl

private def sevenChunk6_1 : List ℕ := [610, 612, 613, 615, 616, 617, 618, 619, 624, 625, 626, 627, 628, 629, 630, 631]

example : sevenChunk6_1.length = 16 := rfl

private def sevenChunk6_2 : List ℕ := [632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647]

example : sevenChunk6_2.length = 16 := rfl

private def sevenChunk6_3 : List ℕ := [648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663]

example : sevenChunk6_3.length = 16 := rfl

private def sevenChunk6_4 : List ℕ := [664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679]

example : sevenChunk6_4.length = 16 := rfl

private def sevenChunk6_5 : List ℕ := [680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695]

example : sevenChunk6_5.length = 16 := rfl

private def sevenChunk6_6 : List ℕ := [696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711]

example : sevenChunk6_6.length = 16 := rfl

private def sevenChunk6_7 : List ℕ := [712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]

example : sevenChunk6_7.length = 16 := rfl

private def sevenChunk6_8 : List ℕ := [728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743]

example : sevenChunk6_8.length = 16 := rfl

private def sevenChunk6_9 : List ℕ := [744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759]

example : sevenChunk6_9.length = 16 := rfl

private def sevenChunk6_10 : List ℕ := [760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775]

example : sevenChunk6_10.length = 16 := rfl

private def sevenChunk6_11 : List ℕ := [776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791]

example : sevenChunk6_11.length = 16 := rfl

private def sevenChunk6_12 : List ℕ := [792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807]

example : sevenChunk6_12.length = 16 := rfl

private def sevenChunk6_13 : List ℕ := [808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823]

example : sevenChunk6_13.length = 16 := rfl

private def sevenChunk6_14 : List ℕ := [824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839]

example : sevenChunk6_14.length = 16 := rfl

private def sevenChunk6_15 : List ℕ := [840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855]

example : sevenChunk6_15.length = 16 := rfl

private def sevenChunk6_16 : List ℕ := [856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871]

example : sevenChunk6_16.length = 16 := rfl

private def sevenChunk6_17 : List ℕ := [872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887]

example : sevenChunk6_17.length = 16 := rfl

private def sevenChunk6_18 : List ℕ := [888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903]

example : sevenChunk6_18.length = 16 := rfl

private def sevenChunk6_19 : List ℕ := [904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919]

example : sevenChunk6_19.length = 16 := rfl

private def sevenChunk6_20 : List ℕ := [920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935]

example : sevenChunk6_20.length = 16 := rfl

private def sevenChunk6_21 : List ℕ := [936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951]

example : sevenChunk6_21.length = 16 := rfl

private def sevenChunk6_22 : List ℕ := [952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967]

example : sevenChunk6_22.length = 16 := rfl

private def sevenChunk6_23 : List ℕ := [968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983]

example : sevenChunk6_23.length = 16 := rfl

private def sevenChunk6_24 : List ℕ := [984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999]

example : sevenChunk6_24.length = 16 := rfl

private def sevenChunk6_25 : List ℕ := [1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]

example : sevenChunk6_25.length = 16 := rfl

private def sevenChunk6_26 : List ℕ := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031]

example : sevenChunk6_26.length = 16 := rfl

private def sevenChunk6_27 : List ℕ := [1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047]

example : sevenChunk6_27.length = 16 := rfl

private def sevenChunk6_28 : List ℕ := [1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063]

example : sevenChunk6_28.length = 16 := rfl

private def sevenChunk6_29 : List ℕ := [1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1078, 1079, 1080, 1081, 1082, 1084]

example : sevenChunk6_29.length = 16 := rfl

private def sevenChunk6_30 : List ℕ := [1085, 1087, 1089, 1091, 1092, 1094, 1095, 1098, 1099, 1102, 1103, 1109, 1111, 1115, 1118, 1120]

example : sevenChunk6_30.length = 16 := rfl

private def sevenChunk6_31 : List ℕ := [1126, 1160]

example : sevenChunk6_31.length = 2 := rfl

private def sevenRows6 : List (List ℕ) := [sevenChunk6_0, sevenChunk6_1, sevenChunk6_2, sevenChunk6_3, sevenChunk6_4, sevenChunk6_5, sevenChunk6_6, sevenChunk6_7, sevenChunk6_8, sevenChunk6_9, sevenChunk6_10, sevenChunk6_11, sevenChunk6_12, sevenChunk6_13, sevenChunk6_14, sevenChunk6_15, sevenChunk6_16, sevenChunk6_17, sevenChunk6_18, sevenChunk6_19, sevenChunk6_20, sevenChunk6_21, sevenChunk6_22, sevenChunk6_23, sevenChunk6_24, sevenChunk6_25, sevenChunk6_26, sevenChunk6_27, sevenChunk6_28, sevenChunk6_29, sevenChunk6_30, sevenChunk6_31]

private def sevenClass6 : List ℕ := sevenRows6.flatten

example : sevenClass6.length = 498 := rfl

private def sevenLabel (x : ℕ) : ℕ :=
  cond (x.blt 1697) (cond (x.blt 848) (cond (x.blt 424) (cond (x.blt 212) (cond (x.blt 106) (cond (x.blt 53) (cond (x.blt 26) (cond (x.blt 13) (cond (x.blt 6) (cond (x.blt 3) (cond (x.blt 1) 0 (cond (x.blt 2) 4 2)) (cond (x.blt 4) 1 (cond (x.blt 5) 3 2))) (cond (x.blt 9) (cond (x.blt 7) 4 (cond (x.blt 8) 3 0)) (cond (x.blt 11) (cond (x.blt 10) 0 3) (cond (x.blt 12) 4 2)))) (cond (x.blt 19) (cond (x.blt 16) (cond (x.blt 14) 1 (cond (x.blt 15) 0 0)) (cond (x.blt 17) 4 (cond (x.blt 18) 1 1))) (cond (x.blt 22) (cond (x.blt 20) 2 (cond (x.blt 21) 4 3)) (cond (x.blt 24) (cond (x.blt 23) 2 1) (cond (x.blt 25) 4 0))))) (cond (x.blt 39) (cond (x.blt 32) (cond (x.blt 29) (cond (x.blt 27) 2 (cond (x.blt 28) 3 1)) (cond (x.blt 30) 2 (cond (x.blt 31) 3 0))) (cond (x.blt 35) (cond (x.blt 33) 0 (cond (x.blt 34) 3 4)) (cond (x.blt 37) (cond (x.blt 36) 0 2) (cond (x.blt 38) 4 1)))) (cond (x.blt 46) (cond (x.blt 42) (cond (x.blt 40) 2 (cond (x.blt 41) 5 4)) (cond (x.blt 44) (cond (x.blt 43) 0 2) (cond (x.blt 45) 1 5))) (cond (x.blt 49) (cond (x.blt 47) 2 (cond (x.blt 48) 3 1)) (cond (x.blt 51) (cond (x.blt 50) 5 2) (cond (x.blt 52) 5 0)))))) (cond (x.blt 79) (cond (x.blt 66) (cond (x.blt 59) (cond (x.blt 56) (cond (x.blt 54) 2 (cond (x.blt 55) 1 0)) (cond (x.blt 57) 2 (cond (x.blt 58) 5 5))) (cond (x.blt 62) (cond (x.blt 60) 0 (cond (x.blt 61) 2 5)) (cond (x.blt 64) (cond (x.blt 63) 5 2) (cond (x.blt 65) 1 5)))) (cond (x.blt 72) (cond (x.blt 69) (cond (x.blt 67) 5 (cond (x.blt 68) 3 5)) (cond (x.blt 70) 5 (cond (x.blt 71) 3 5))) (cond (x.blt 75) (cond (x.blt 73) 5 (cond (x.blt 74) 5 2)) (cond (x.blt 77) (cond (x.blt 76) 5 0) (cond (x.blt 78) 2 5))))) (cond (x.blt 92) (cond (x.blt 85) (cond (x.blt 82) (cond (x.blt 80) 0 (cond (x.blt 81) 2 5)) (cond (x.blt 83) 5 (cond (x.blt 84) 1 2))) (cond (x.blt 88) (cond (x.blt 86) 3 (cond (x.blt 87) 3 2)) (cond (x.blt 90) (cond (x.blt 89) 5 0) (cond (x.blt 91) 4 2)))) (cond (x.blt 99) (cond (x.blt 95) (cond (x.blt 93) 5 (cond (x.blt 94) 1 2)) (cond (x.blt 97) (cond (x.blt 96) 0 0) (cond (x.blt 98) 4 2))) (cond (x.blt 102) (cond (x.blt 100) 0 (cond (x.blt 101) 0 2)) (cond (x.blt 104) (cond (x.blt 103) 4 1) (cond (x.blt 105) 2 4))))))) (cond (x.blt 159) (cond (x.blt 132) (cond (x.blt 119) (cond (x.blt 112) (cond (x.blt 109) (cond (x.blt 107) 0 (cond (x.blt 108) 4 2)) (cond (x.blt 110) 3 (cond (x.blt 111) 3 2))) (cond (x.blt 115) (cond (x.blt 113) 0 (cond (x.blt 114) 1 1)) (cond (x.blt 117) (cond (x.blt 116) 2 0) (cond (x.blt 118) 0 2)))) (cond (x.blt 125) (cond (x.blt 122) (cond (x.blt 120) 0 (cond (x.blt 121) 4 2)) (cond (x.blt 123) 1 (cond (x.blt 124) 1 1))) (cond (x.blt 128) (cond (x.blt 126) 2 (cond (x.blt 127) 3 3)) (cond (x.blt 130) (cond (x.blt 129) 2 0) (cond (x.blt 131) 4 2))))) (cond (x.blt 145) (cond (x.blt 138) (cond (x.blt 135) (cond (x.blt 133) 2 (cond (x.blt 134) 1 1)) (cond (x.blt 136) 2 (cond (x.blt 137) 0 4))) (cond (x.blt 141) (cond (x.blt 139) 3 (cond (x.blt 140) 0 0)) (cond (x.blt 143) (cond (x.blt 142) 3 2) (cond (x.blt 144) 1 3)))) (cond (x.blt 152) (cond (x.blt 148) (cond (x.blt 146) 2 (cond (x.blt 147) 0 4)) (cond (x.blt 150) (cond (x.blt 149) 1 2) (cond (x.blt 151) 3 4))) (cond (x.blt 155) (cond (x.blt 153) 2 (cond (x.blt 154) 1 1)) (cond (x.blt 157) (cond (x.blt 156) 2 2) (cond (x.blt 158) 0 3)))))) (cond (x.blt 185) (cond (x.blt 172) (cond (x.blt 165) (cond (x.blt 162) (cond (x.blt 160) 2 (cond (x.blt 161) 4 3)) (cond (x.blt 163) 0 (cond (x.blt 164) 0 3))) (cond (x.blt 168) (cond (x.blt 166) 4 (cond (x.blt 167) 2 3)) (cond (x.blt 170) (cond (x.blt 169) 4 2) (cond (x.blt 171) 4 5)))) (cond (x.blt 178) (cond (x.blt 175) (cond (x.blt 173) 4 (cond (x.blt 174) 2 1)) (cond (x.blt 176) 1 (cond (x.blt 177) 2 4))) (cond (x.blt 181) (cond (x.blt 179) 3 (cond (x.blt 180) 1 0)) (cond (x.blt 183) (cond (x.blt 182) 5 4) (cond (x.blt 184) 2 3))))) (cond (x.blt 198) (cond (x.blt 191) (cond (x.blt 188) (cond (x.blt 186) 1 (cond (x.blt 187) 0 5)) (cond (x.blt 189) 5 (cond (x.blt 190) 5 2))) (cond (x.blt 194) (cond (x.blt 192) 5 (cond (x.blt 193) 5 2)) (cond (x.blt 196) (cond (x.blt 195) 5 1) (cond (x.blt 197) 5 2)))) (cond (x.blt 205) (cond (x.blt 201) (cond (x.blt 199) 5 (cond (x.blt 200) 5 5)) (cond (x.blt 203) (cond (x.blt 202) 5 3) (cond (x.blt 204) 5 2))) (cond (x.blt 208) (cond (x.blt 206) 5 (cond (x.blt 207) 5 5)) (cond (x.blt 210) (cond (x.blt 209) 5 5) (cond (x.blt 211) 2 1)))))))) (cond (x.blt 318) (cond (x.blt 265) (cond (x.blt 238) (cond (x.blt 225) (cond (x.blt 218) (cond (x.blt 215) (cond (x.blt 213) 5 (cond (x.blt 214) 5 2)) (cond (x.blt 216) 5 (cond (x.blt 217) 3 2))) (cond (x.blt 221) (cond (x.blt 219) 5 (cond (x.blt 220) 5 0)) (cond (x.blt 223) (cond (x.blt 222) 2 3) (cond (x.blt 224) 5 2)))) (cond (x.blt 231) (cond (x.blt 228) (cond (x.blt 226) 5 (cond (x.blt 227) 0 0)) (cond (x.blt 229) 2 (cond (x.blt 230) 4 0))) (cond (x.blt 234) (cond (x.blt 232) 2 (cond (x.blt 233) 1 4)) (cond (x.blt 236) (cond (x.blt 235) 2 5) (cond (x.blt 237) 4 0))))) (cond (x.blt 251) (cond (x.blt 244) (cond (x.blt 241) (cond (x.blt 239) 2 (cond (x.blt 240) 3 3)) (cond (x.blt 242) 2 (cond (x.blt 243) 1 0))) (cond (x.blt 247) (cond (x.blt 245) 2 (cond (x.blt 246) 2 4)) (cond (x.blt 249) (cond (x.blt 248) 0 2) (cond (x.blt 250) 0 0)))) (cond (x.blt 258) (cond (x.blt 254) (cond (x.blt 252) 4 (cond (x.blt 253) 1 1)) (cond (x.blt 256) (cond (x.blt 255) 1 2) (cond (x.blt 257) 3 3))) (cond (x.blt 261) (cond (x.blt 259) 2 (cond (x.blt 260) 4 0)) (cond (x.blt 263) (cond (x.blt 262) 4 3) (cond (x.blt 264) 1 1)))))) (cond (x.blt 291) (cond (x.blt 278) (cond (x.blt 271) (cond (x.blt 268) (cond (x.blt 266) 2 (cond (x.blt 267) 0 0)) (cond (x.blt 269) 2 (cond (x.blt 270) 2 0))) (cond (x.blt 274) (cond (x.blt 272) 0 (cond (x.blt 273) 2 1)) (cond (x.blt 276) (cond (x.blt 275) 1 3) (cond (x.blt 277) 4 0)))) (cond (x.blt 284) (cond (x.blt 281) (cond (x.blt 279) 4 (cond (x.blt 280) 2 3)) (cond (x.blt 282) 3 (cond (x.blt 283) 2 1))) (cond (x.blt 287) (cond (x.blt 285) 1 (cond (x.blt 286) 1 4)) (cond (x.blt 289) (cond (x.blt 288) 0 0) (cond (x.blt 290) 2 0))))) (cond (x.blt 304) (cond (x.blt 297) (cond (x.blt 294) (cond (x.blt 292) 4 (cond (x.blt 293) 2 2)) (cond (x.blt 295) 0 (cond (x.blt 296) 1 2))) (cond (x.blt 300) (cond (x.blt 298) 3 (cond (x.blt 299) 3 2)) (cond (x.blt 302) (cond (x.blt 301) 0 4) (cond (x.blt 303) 5 2)))) (cond (x.blt 311) (cond (x.blt 307) (cond (x.blt 305) 4 (cond (x.blt 306) 1 2)) (cond (x.blt 309) (cond (x.blt 308) 0 4) (cond (x.blt 310) 2 0))) (cond (x.blt 314) (cond (x.blt 312) 0 (cond (x.blt 313) 5 2)) (cond (x.blt 316) (cond (x.blt 315) 5 3) (cond (x.blt 317) 2 0))))))) (cond (x.blt 371) (cond (x.blt 344) (cond (x.blt 331) (cond (x.blt 324) (cond (x.blt 321) (cond (x.blt 319) 5 (cond (x.blt 320) 5 2)) (cond (x.blt 322) 3 (cond (x.blt 323) 5 2))) (cond (x.blt 327) (cond (x.blt 325) 5 (cond (x.blt 326) 5 1)) (cond (x.blt 329) (cond (x.blt 328) 2 5) (cond (x.blt 330) 5 5)))) (cond (x.blt 337) (cond (x.blt 334) (cond (x.blt 332) 5 (cond (x.blt 333) 5 2)) (cond (x.blt 335) 5 (cond (x.blt 336) 3 5))) (cond (x.blt 340) (cond (x.blt 338) 5 (cond (x.blt 339) 5 5)) (cond (x.blt 342) (cond (x.blt 341) 2 5) (cond (x.blt 343) 1 5))))) (cond (x.blt 357) (cond (x.blt 350) (cond (x.blt 347) (cond (x.blt 345) 2 (cond (x.blt 346) 5 5)) (cond (x.blt 348) 2 (cond (x.blt 349) 5 5))) (cond (x.blt 353) (cond (x.blt 351) 5 (cond (x.blt 352) 0 1)) (cond (x.blt 355) (cond (x.blt 354) 3 2) (cond (x.blt 356) 4 5)))) (cond (x.blt 364) (cond (x.blt 360) (cond (x.blt 358) 0 (cond (x.blt 359) 2 3)) (cond (x.blt 362) (cond (x.blt 361) 4 2) (cond (x.blt 363) 1 1))) (cond (x.blt 367) (cond (x.blt 365) 2 (cond (x.blt 366) 4 5)) (cond (x.blt 369) (cond (x.blt 368) 4 2) (cond (x.blt 370) 4 3)))))) (cond (x.blt 397) (cond (x.blt 384) (cond (x.blt 377) (cond (x.blt 374) (cond (x.blt 372) 2 (cond (x.blt 373) 4 3)) (cond (x.blt 375) 0 (cond (x.blt 376) 0 3))) (cond (x.blt 380) (cond (x.blt 378) 4 (cond (x.blt 379) 2 3)) (cond (x.blt 382) (cond (x.blt 381) 0 2) (cond (x.blt 383) 2 1)))) (cond (x.blt 390) (cond (x.blt 387) (cond (x.blt 385) 1 (cond (x.blt 386) 2 4)) (cond (x.blt 388) 3 (cond (x.blt 389) 2 1))) (cond (x.blt 393) (cond (x.blt 391) 4 (cond (x.blt 392) 0 2)) (cond (x.blt 395) (cond (x.blt 394) 3 1) (cond (x.blt 396) 2 3))))) (cond (x.blt 410) (cond (x.blt 403) (cond (x.blt 400) (cond (x.blt 398) 0 (cond (x.blt 399) 0 3)) (cond (x.blt 401) 4 (cond (x.blt 402) 0 2))) (cond (x.blt 406) (cond (x.blt 404) 1 (cond (x.blt 405) 1 2)) (cond (x.blt 408) (cond (x.blt 407) 2 4) (cond (x.blt 409) 0 2)))) (cond (x.blt 417) (cond (x.blt 413) (cond (x.blt 411) 3 (cond (x.blt 412) 3 2)) (cond (x.blt 415) (cond (x.blt 414) 1 1) (cond (x.blt 416) 1 2))) (cond (x.blt 420) (cond (x.blt 418) 4 (cond (x.blt 419) 0 2)) (cond (x.blt 422) (cond (x.blt 421) 0 0) (cond (x.blt 423) 2 1))))))))) (cond (x.blt 636) (cond (x.blt 530) (cond (x.blt 477) (cond (x.blt 450) (cond (x.blt 437) (cond (x.blt 430) (cond (x.blt 427) (cond (x.blt 425) 1 (cond (x.blt 426) 0 2)) (cond (x.blt 428) 3 (cond (x.blt 429) 3 2))) (cond (x.blt 433) (cond (x.blt 431) 4 (cond (x.blt 432) 0 4)) (cond (x.blt 435) (cond (x.blt 434) 2 1) (cond (x.blt 436) 4 2)))) (cond (x.blt 443) (cond (x.blt 440) (cond (x.blt 438) 0 (cond (x.blt 439) 0 2)) (cond (x.blt 441) 4 (cond (x.blt 442) 0 0))) (cond (x.blt 446) (cond (x.blt 444) 2 (cond (x.blt 445) 1 5)) (cond (x.blt 448) (cond (x.blt 447) 2 4) (cond (x.blt 449) 0 5))))) (cond (x.blt 463) (cond (x.blt 456) (cond (x.blt 453) (cond (x.blt 451) 2 (cond (x.blt 452) 3 3)) (cond (x.blt 454) 2 (cond (x.blt 455) 1 5))) (cond (x.blt 459) (cond (x.blt 457) 5 (cond (x.blt 458) 2 0)) (cond (x.blt 461) (cond (x.blt 460) 5 2) (cond (x.blt 462) 0 5)))) (cond (x.blt 470) (cond (x.blt 466) (cond (x.blt 464) 5 (cond (x.blt 465) 5 5)) (cond (x.blt 468) (cond (x.blt 467) 5 3) (cond (x.blt 469) 5 5))) (cond (x.blt 473) (cond (x.blt 471) 3 (cond (x.blt 472) 5 5)) (cond (x.blt 475) (cond (x.blt 474) 1 2) (cond (x.blt 476) 5 5)))))) (cond (x.blt 503) (cond (x.blt 490) (cond (x.blt 483) (cond (x.blt 480) (cond (x.blt 478) 2 (cond (x.blt 479) 0 5)) (cond (x.blt 481) 5 (cond (x.blt 482) 2 0))) (cond (x.blt 486) (cond (x.blt 484) 1 (cond (x.blt 485) 2 0)) (cond (x.blt 488) (cond (x.blt 487) 5 2) (cond (x.blt 489) 5 1)))) (cond (x.blt 496) (cond (x.blt 493) (cond (x.blt 491) 3 (cond (x.blt 492) 2 5)) (cond (x.blt 494) 1 (cond (x.blt 495) 2 0))) (cond (x.blt 499) (cond (x.blt 497) 4 (cond (x.blt 498) 5 2)) (cond (x.blt 501) (cond (x.blt 500) 1 4) (cond (x.blt 502) 2 0))))) (cond (x.blt 516) (cond (x.blt 509) (cond (x.blt 506) (cond (x.blt 504) 4 (cond (x.blt 505) 3 0)) (cond (x.blt 507) 0 (cond (x.blt 508) 3 2))) (cond (x.blt 512) (cond (x.blt 510) 1 (cond (x.blt 511) 3 2)) (cond (x.blt 514) (cond (x.blt 513) 0 4) (cond (x.blt 515) 1 2)))) (cond (x.blt 523) (cond (x.blt 519) (cond (x.blt 517) 3 (cond (x.blt 518) 4 2)) (cond (x.blt 521) (cond (x.blt 520) 1 1) (cond (x.blt 522) 4 0))) (cond (x.blt 526) (cond (x.blt 524) 0 (cond (x.blt 525) 1 2)) (cond (x.blt 528) (cond (x.blt 527) 4 3) (cond (x.blt 529) 0 0))))))) (cond (x.blt 583) (cond (x.blt 556) (cond (x.blt 543) (cond (x.blt 536) (cond (x.blt 533) (cond (x.blt 531) 3 (cond (x.blt 532) 4 2)) (cond (x.blt 534) 3 (cond (x.blt 535) 1 2))) (cond (x.blt 539) (cond (x.blt 537) 4 (cond (x.blt 538) 6 4)) (cond (x.blt 541) (cond (x.blt 540) 2 1) (cond (x.blt 542) 3 2)))) (cond (x.blt 549) (cond (x.blt 546) (cond (x.blt 544) 4 (cond (x.blt 545) 1 0)) (cond (x.blt 547) 2 (cond (x.blt 548) 3 4))) (cond (x.blt 552) (cond (x.blt 550) 2 (cond (x.blt 551) 1 0)) (cond (x.blt 554) (cond (x.blt 553) 0 4) (cond (x.blt 555) 1 1))))) (cond (x.blt 569) (cond (x.blt 562) (cond (x.blt 559) (cond (x.blt 557) 2 (cond (x.blt 558) 4 3)) (cond (x.blt 560) 2 (cond (x.blt 561) 1 4))) (cond (x.blt 565) (cond (x.blt 563) 0 (cond (x.blt 564) 2 3)) (cond (x.blt 567) (cond (x.blt 566) 1 2) (cond (x.blt 568) 3 0)))) (cond (x.blt 576) (cond (x.blt 572) (cond (x.blt 570) 0 (cond (x.blt 571) 3 6)) (cond (x.blt 574) (cond (x.blt 573) 0 2) (cond (x.blt 575) 4 1))) (cond (x.blt 579) (cond (x.blt 577) 2 (cond (x.blt 578) 6 4)) (cond (x.blt 581) (cond (x.blt 580) 6 2) (cond (x.blt 582) 1 6)))))) (cond (x.blt 609) (cond (x.blt 596) (cond (x.blt 589) (cond (x.blt 586) (cond (x.blt 584) 2 (cond (x.blt 585) 3 1)) (cond (x.blt 587) 6 (cond (x.blt 588) 2 6))) (cond (x.blt 592) (cond (x.blt 590) 0 (cond (x.blt 591) 2 1)) (cond (x.blt 594) (cond (x.blt 593) 0 5) (cond (x.blt 595) 6 6)))) (cond (x.blt 602) (cond (x.blt 599) (cond (x.blt 597) 5 (cond (x.blt 598) 2 6)) (cond (x.blt 600) 6 (cond (x.blt 601) 2 1))) (cond (x.blt 605) (cond (x.blt 603) 6 (cond (x.blt 604) 6 2)) (cond (x.blt 607) (cond (x.blt 606) 6 6) (cond (x.blt 608) 2 6))))) (cond (x.blt 622) (cond (x.blt 615) (cond (x.blt 612) (cond (x.blt 610) 0 (cond (x.blt 611) 6 2)) (cond (x.blt 613) 6 (cond (x.blt 614) 6 2))) (cond (x.blt 618) (cond (x.blt 616) 6 (cond (x.blt 617) 6 6)) (cond (x.blt 620) (cond (x.blt 619) 6 6) (cond (x.blt 621) 1 2)))) (cond (x.blt 629) (cond (x.blt 625) (cond (x.blt 623) 3 (cond (x.blt 624) 5 6)) (cond (x.blt 627) (cond (x.blt 626) 6 6) (cond (x.blt 628) 6 6))) (cond (x.blt 632) (cond (x.blt 630) 6 (cond (x.blt 631) 6 6)) (cond (x.blt 634) (cond (x.blt 633) 6 6) (cond (x.blt 635) 6 6)))))))) (cond (x.blt 742) (cond (x.blt 689) (cond (x.blt 662) (cond (x.blt 649) (cond (x.blt 642) (cond (x.blt 639) (cond (x.blt 637) 6 (cond (x.blt 638) 6 6)) (cond (x.blt 640) 6 (cond (x.blt 641) 6 6))) (cond (x.blt 645) (cond (x.blt 643) 6 (cond (x.blt 644) 6 6)) (cond (x.blt 647) (cond (x.blt 646) 6 6) (cond (x.blt 648) 6 6)))) (cond (x.blt 655) (cond (x.blt 652) (cond (x.blt 650) 6 (cond (x.blt 651) 6 6)) (cond (x.blt 653) 6 (cond (x.blt 654) 6 6))) (cond (x.blt 658) (cond (x.blt 656) 6 (cond (x.blt 657) 6 6)) (cond (x.blt 660) (cond (x.blt 659) 6 6) (cond (x.blt 661) 6 6))))) (cond (x.blt 675) (cond (x.blt 668) (cond (x.blt 665) (cond (x.blt 663) 6 (cond (x.blt 664) 6 6)) (cond (x.blt 666) 6 (cond (x.blt 667) 6 6))) (cond (x.blt 671) (cond (x.blt 669) 6 (cond (x.blt 670) 6 6)) (cond (x.blt 673) (cond (x.blt 672) 6 6) (cond (x.blt 674) 6 6)))) (cond (x.blt 682) (cond (x.blt 678) (cond (x.blt 676) 6 (cond (x.blt 677) 6 6)) (cond (x.blt 680) (cond (x.blt 679) 6 6) (cond (x.blt 681) 6 6))) (cond (x.blt 685) (cond (x.blt 683) 6 (cond (x.blt 684) 6 6)) (cond (x.blt 687) (cond (x.blt 686) 6 6) (cond (x.blt 688) 6 6)))))) (cond (x.blt 715) (cond (x.blt 702) (cond (x.blt 695) (cond (x.blt 692) (cond (x.blt 690) 6 (cond (x.blt 691) 6 6)) (cond (x.blt 693) 6 (cond (x.blt 694) 6 6))) (cond (x.blt 698) (cond (x.blt 696) 6 (cond (x.blt 697) 6 6)) (cond (x.blt 700) (cond (x.blt 699) 6 6) (cond (x.blt 701) 6 6)))) (cond (x.blt 708) (cond (x.blt 705) (cond (x.blt 703) 6 (cond (x.blt 704) 6 6)) (cond (x.blt 706) 6 (cond (x.blt 707) 6 6))) (cond (x.blt 711) (cond (x.blt 709) 6 (cond (x.blt 710) 6 6)) (cond (x.blt 713) (cond (x.blt 712) 6 6) (cond (x.blt 714) 6 6))))) (cond (x.blt 728) (cond (x.blt 721) (cond (x.blt 718) (cond (x.blt 716) 6 (cond (x.blt 717) 6 6)) (cond (x.blt 719) 6 (cond (x.blt 720) 6 6))) (cond (x.blt 724) (cond (x.blt 722) 6 (cond (x.blt 723) 6 6)) (cond (x.blt 726) (cond (x.blt 725) 6 6) (cond (x.blt 727) 6 6)))) (cond (x.blt 735) (cond (x.blt 731) (cond (x.blt 729) 6 (cond (x.blt 730) 6 6)) (cond (x.blt 733) (cond (x.blt 732) 6 6) (cond (x.blt 734) 6 6))) (cond (x.blt 738) (cond (x.blt 736) 6 (cond (x.blt 737) 6 6)) (cond (x.blt 740) (cond (x.blt 739) 6 6) (cond (x.blt 741) 6 6))))))) (cond (x.blt 795) (cond (x.blt 768) (cond (x.blt 755) (cond (x.blt 748) (cond (x.blt 745) (cond (x.blt 743) 6 (cond (x.blt 744) 6 6)) (cond (x.blt 746) 6 (cond (x.blt 747) 6 6))) (cond (x.blt 751) (cond (x.blt 749) 6 (cond (x.blt 750) 6 6)) (cond (x.blt 753) (cond (x.blt 752) 6 6) (cond (x.blt 754) 6 6)))) (cond (x.blt 761) (cond (x.blt 758) (cond (x.blt 756) 6 (cond (x.blt 757) 6 6)) (cond (x.blt 759) 6 (cond (x.blt 760) 6 6))) (cond (x.blt 764) (cond (x.blt 762) 6 (cond (x.blt 763) 6 6)) (cond (x.blt 766) (cond (x.blt 765) 6 6) (cond (x.blt 767) 6 6))))) (cond (x.blt 781) (cond (x.blt 774) (cond (x.blt 771) (cond (x.blt 769) 6 (cond (x.blt 770) 6 6)) (cond (x.blt 772) 6 (cond (x.blt 773) 6 6))) (cond (x.blt 777) (cond (x.blt 775) 6 (cond (x.blt 776) 6 6)) (cond (x.blt 779) (cond (x.blt 778) 6 6) (cond (x.blt 780) 6 6)))) (cond (x.blt 788) (cond (x.blt 784) (cond (x.blt 782) 6 (cond (x.blt 783) 6 6)) (cond (x.blt 786) (cond (x.blt 785) 6 6) (cond (x.blt 787) 6 6))) (cond (x.blt 791) (cond (x.blt 789) 6 (cond (x.blt 790) 6 6)) (cond (x.blt 793) (cond (x.blt 792) 6 6) (cond (x.blt 794) 6 6)))))) (cond (x.blt 821) (cond (x.blt 808) (cond (x.blt 801) (cond (x.blt 798) (cond (x.blt 796) 6 (cond (x.blt 797) 6 6)) (cond (x.blt 799) 6 (cond (x.blt 800) 6 6))) (cond (x.blt 804) (cond (x.blt 802) 6 (cond (x.blt 803) 6 6)) (cond (x.blt 806) (cond (x.blt 805) 6 6) (cond (x.blt 807) 6 6)))) (cond (x.blt 814) (cond (x.blt 811) (cond (x.blt 809) 6 (cond (x.blt 810) 6 6)) (cond (x.blt 812) 6 (cond (x.blt 813) 6 6))) (cond (x.blt 817) (cond (x.blt 815) 6 (cond (x.blt 816) 6 6)) (cond (x.blt 819) (cond (x.blt 818) 6 6) (cond (x.blt 820) 6 6))))) (cond (x.blt 834) (cond (x.blt 827) (cond (x.blt 824) (cond (x.blt 822) 6 (cond (x.blt 823) 6 6)) (cond (x.blt 825) 6 (cond (x.blt 826) 6 6))) (cond (x.blt 830) (cond (x.blt 828) 6 (cond (x.blt 829) 6 6)) (cond (x.blt 832) (cond (x.blt 831) 6 6) (cond (x.blt 833) 6 6)))) (cond (x.blt 841) (cond (x.blt 837) (cond (x.blt 835) 6 (cond (x.blt 836) 6 6)) (cond (x.blt 839) (cond (x.blt 838) 6 6) (cond (x.blt 840) 6 6))) (cond (x.blt 844) (cond (x.blt 842) 6 (cond (x.blt 843) 6 6)) (cond (x.blt 846) (cond (x.blt 845) 6 6) (cond (x.blt 847) 6 6)))))))))) (cond (x.blt 1272) (cond (x.blt 1060) (cond (x.blt 954) (cond (x.blt 901) (cond (x.blt 874) (cond (x.blt 861) (cond (x.blt 854) (cond (x.blt 851) (cond (x.blt 849) 6 (cond (x.blt 850) 6 6)) (cond (x.blt 852) 6 (cond (x.blt 853) 6 6))) (cond (x.blt 857) (cond (x.blt 855) 6 (cond (x.blt 856) 6 6)) (cond (x.blt 859) (cond (x.blt 858) 6 6) (cond (x.blt 860) 6 6)))) (cond (x.blt 867) (cond (x.blt 864) (cond (x.blt 862) 6 (cond (x.blt 863) 6 6)) (cond (x.blt 865) 6 (cond (x.blt 866) 6 6))) (cond (x.blt 870) (cond (x.blt 868) 6 (cond (x.blt 869) 6 6)) (cond (x.blt 872) (cond (x.blt 871) 6 6) (cond (x.blt 873) 6 6))))) (cond (x.blt 887) (cond (x.blt 880) (cond (x.blt 877) (cond (x.blt 875) 6 (cond (x.blt 876) 6 6)) (cond (x.blt 878) 6 (cond (x.blt 879) 6 6))) (cond (x.blt 883) (cond (x.blt 881) 6 (cond (x.blt 882) 6 6)) (cond (x.blt 885) (cond (x.blt 884) 6 6) (cond (x.blt 886) 6 6)))) (cond (x.blt 894) (cond (x.blt 890) (cond (x.blt 888) 6 (cond (x.blt 889) 6 6)) (cond (x.blt 892) (cond (x.blt 891) 6 6) (cond (x.blt 893) 6 6))) (cond (x.blt 897) (cond (x.blt 895) 6 (cond (x.blt 896) 6 6)) (cond (x.blt 899) (cond (x.blt 898) 6 6) (cond (x.blt 900) 6 6)))))) (cond (x.blt 927) (cond (x.blt 914) (cond (x.blt 907) (cond (x.blt 904) (cond (x.blt 902) 6 (cond (x.blt 903) 6 6)) (cond (x.blt 905) 6 (cond (x.blt 906) 6 6))) (cond (x.blt 910) (cond (x.blt 908) 6 (cond (x.blt 909) 6 6)) (cond (x.blt 912) (cond (x.blt 911) 6 6) (cond (x.blt 913) 6 6)))) (cond (x.blt 920) (cond (x.blt 917) (cond (x.blt 915) 6 (cond (x.blt 916) 6 6)) (cond (x.blt 918) 6 (cond (x.blt 919) 6 6))) (cond (x.blt 923) (cond (x.blt 921) 6 (cond (x.blt 922) 6 6)) (cond (x.blt 925) (cond (x.blt 924) 6 6) (cond (x.blt 926) 6 6))))) (cond (x.blt 940) (cond (x.blt 933) (cond (x.blt 930) (cond (x.blt 928) 6 (cond (x.blt 929) 6 6)) (cond (x.blt 931) 6 (cond (x.blt 932) 6 6))) (cond (x.blt 936) (cond (x.blt 934) 6 (cond (x.blt 935) 6 6)) (cond (x.blt 938) (cond (x.blt 937) 6 6) (cond (x.blt 939) 6 6)))) (cond (x.blt 947) (cond (x.blt 943) (cond (x.blt 941) 6 (cond (x.blt 942) 6 6)) (cond (x.blt 945) (cond (x.blt 944) 6 6) (cond (x.blt 946) 6 6))) (cond (x.blt 950) (cond (x.blt 948) 6 (cond (x.blt 949) 6 6)) (cond (x.blt 952) (cond (x.blt 951) 6 6) (cond (x.blt 953) 6 6))))))) (cond (x.blt 1007) (cond (x.blt 980) (cond (x.blt 967) (cond (x.blt 960) (cond (x.blt 957) (cond (x.blt 955) 6 (cond (x.blt 956) 6 6)) (cond (x.blt 958) 6 (cond (x.blt 959) 6 6))) (cond (x.blt 963) (cond (x.blt 961) 6 (cond (x.blt 962) 6 6)) (cond (x.blt 965) (cond (x.blt 964) 6 6) (cond (x.blt 966) 6 6)))) (cond (x.blt 973) (cond (x.blt 970) (cond (x.blt 968) 6 (cond (x.blt 969) 6 6)) (cond (x.blt 971) 6 (cond (x.blt 972) 6 6))) (cond (x.blt 976) (cond (x.blt 974) 6 (cond (x.blt 975) 6 6)) (cond (x.blt 978) (cond (x.blt 977) 6 6) (cond (x.blt 979) 6 6))))) (cond (x.blt 993) (cond (x.blt 986) (cond (x.blt 983) (cond (x.blt 981) 6 (cond (x.blt 982) 6 6)) (cond (x.blt 984) 6 (cond (x.blt 985) 6 6))) (cond (x.blt 989) (cond (x.blt 987) 6 (cond (x.blt 988) 6 6)) (cond (x.blt 991) (cond (x.blt 990) 6 6) (cond (x.blt 992) 6 6)))) (cond (x.blt 1000) (cond (x.blt 996) (cond (x.blt 994) 6 (cond (x.blt 995) 6 6)) (cond (x.blt 998) (cond (x.blt 997) 6 6) (cond (x.blt 999) 6 6))) (cond (x.blt 1003) (cond (x.blt 1001) 6 (cond (x.blt 1002) 6 6)) (cond (x.blt 1005) (cond (x.blt 1004) 6 6) (cond (x.blt 1006) 6 6)))))) (cond (x.blt 1033) (cond (x.blt 1020) (cond (x.blt 1013) (cond (x.blt 1010) (cond (x.blt 1008) 6 (cond (x.blt 1009) 6 6)) (cond (x.blt 1011) 6 (cond (x.blt 1012) 6 6))) (cond (x.blt 1016) (cond (x.blt 1014) 6 (cond (x.blt 1015) 6 6)) (cond (x.blt 1018) (cond (x.blt 1017) 6 6) (cond (x.blt 1019) 6 6)))) (cond (x.blt 1026) (cond (x.blt 1023) (cond (x.blt 1021) 6 (cond (x.blt 1022) 6 6)) (cond (x.blt 1024) 6 (cond (x.blt 1025) 6 6))) (cond (x.blt 1029) (cond (x.blt 1027) 6 (cond (x.blt 1028) 6 6)) (cond (x.blt 1031) (cond (x.blt 1030) 6 6) (cond (x.blt 1032) 6 6))))) (cond (x.blt 1046) (cond (x.blt 1039) (cond (x.blt 1036) (cond (x.blt 1034) 6 (cond (x.blt 1035) 6 6)) (cond (x.blt 1037) 6 (cond (x.blt 1038) 6 6))) (cond (x.blt 1042) (cond (x.blt 1040) 6 (cond (x.blt 1041) 6 6)) (cond (x.blt 1044) (cond (x.blt 1043) 6 6) (cond (x.blt 1045) 6 6)))) (cond (x.blt 1053) (cond (x.blt 1049) (cond (x.blt 1047) 6 (cond (x.blt 1048) 6 6)) (cond (x.blt 1051) (cond (x.blt 1050) 6 6) (cond (x.blt 1052) 6 6))) (cond (x.blt 1056) (cond (x.blt 1054) 6 (cond (x.blt 1055) 6 6)) (cond (x.blt 1058) (cond (x.blt 1057) 6 6) (cond (x.blt 1059) 6 6)))))))) (cond (x.blt 1166) (cond (x.blt 1113) (cond (x.blt 1086) (cond (x.blt 1073) (cond (x.blt 1066) (cond (x.blt 1063) (cond (x.blt 1061) 6 (cond (x.blt 1062) 6 6)) (cond (x.blt 1064) 6 (cond (x.blt 1065) 6 6))) (cond (x.blt 1069) (cond (x.blt 1067) 6 (cond (x.blt 1068) 6 6)) (cond (x.blt 1071) (cond (x.blt 1070) 6 6) (cond (x.blt 1072) 6 6)))) (cond (x.blt 1079) (cond (x.blt 1076) (cond (x.blt 1074) 6 (cond (x.blt 1075) 5 3)) (cond (x.blt 1077) 2 (cond (x.blt 1078) 1 6))) (cond (x.blt 1082) (cond (x.blt 1080) 6 (cond (x.blt 1081) 6 6)) (cond (x.blt 1084) (cond (x.blt 1083) 6 2) (cond (x.blt 1085) 6 6))))) (cond (x.blt 1099) (cond (x.blt 1092) (cond (x.blt 1089) (cond (x.blt 1087) 2 (cond (x.blt 1088) 6 0)) (cond (x.blt 1090) 6 (cond (x.blt 1091) 2 6))) (cond (x.blt 1095) (cond (x.blt 1093) 6 (cond (x.blt 1094) 2 6)) (cond (x.blt 1097) (cond (x.blt 1096) 6 1) (cond (x.blt 1098) 2 6)))) (cond (x.blt 1106) (cond (x.blt 1102) (cond (x.blt 1100) 6 (cond (x.blt 1101) 2 5)) (cond (x.blt 1104) (cond (x.blt 1103) 6 6) (cond (x.blt 1105) 5 0))) (cond (x.blt 1109) (cond (x.blt 1107) 1 (cond (x.blt 1108) 2 0)) (cond (x.blt 1111) (cond (x.blt 1110) 6 2) (cond (x.blt 1112) 6 1)))))) (cond (x.blt 1139) (cond (x.blt 1126) (cond (x.blt 1119) (cond (x.blt 1116) (cond (x.blt 1114) 3 (cond (x.blt 1115) 2 6)) (cond (x.blt 1117) 1 (cond (x.blt 1118) 2 6))) (cond (x.blt 1122) (cond (x.blt 1120) 4 (cond (x.blt 1121) 6 2)) (cond (x.blt 1124) (cond (x.blt 1123) 1 4) (cond (x.blt 1125) 2 0)))) (cond (x.blt 1132) (cond (x.blt 1129) (cond (x.blt 1127) 6 (cond (x.blt 1128) 3 0)) (cond (x.blt 1130) 0 (cond (x.blt 1131) 3 2))) (cond (x.blt 1135) (cond (x.blt 1133) 1 (cond (x.blt 1134) 3 2)) (cond (x.blt 1137) (cond (x.blt 1136) 0 4) (cond (x.blt 1138) 1 2))))) (cond (x.blt 1152) (cond (x.blt 1145) (cond (x.blt 1142) (cond (x.blt 1140) 3 (cond (x.blt 1141) 4 2)) (cond (x.blt 1143) 1 (cond (x.blt 1144) 1 4))) (cond (x.blt 1148) (cond (x.blt 1146) 0 (cond (x.blt 1147) 0 1)) (cond (x.blt 1150) (cond (x.blt 1149) 2 4) (cond (x.blt 1151) 3 2)))) (cond (x.blt 1159) (cond (x.blt 1155) (cond (x.blt 1153) 0 (cond (x.blt 1154) 1 4)) (cond (x.blt 1157) (cond (x.blt 1156) 2 3) (cond (x.blt 1158) 1 2))) (cond (x.blt 1162) (cond (x.blt 1160) 4 (cond (x.blt 1161) 6 4)) (cond (x.blt 1164) (cond (x.blt 1163) 2 1) (cond (x.blt 1165) 3 2))))))) (cond (x.blt 1219) (cond (x.blt 1192) (cond (x.blt 1179) (cond (x.blt 1172) (cond (x.blt 1169) (cond (x.blt 1167) 4 (cond (x.blt 1168) 3 0)) (cond (x.blt 1170) 0 (cond (x.blt 1171) 3 4))) (cond (x.blt 1175) (cond (x.blt 1173) 2 (cond (x.blt 1174) 1 0)) (cond (x.blt 1177) (cond (x.blt 1176) 0 4) (cond (x.blt 1178) 1 1)))) (cond (x.blt 1185) (cond (x.blt 1182) (cond (x.blt 1180) 2 (cond (x.blt 1181) 4 3)) (cond (x.blt 1183) 2 (cond (x.blt 1184) 1 4))) (cond (x.blt 1188) (cond (x.blt 1186) 0 (cond (x.blt 1187) 2 3)) (cond (x.blt 1190) (cond (x.blt 1189) 1 2) (cond (x.blt 1191) 3 0))))) (cond (x.blt 1205) (cond (x.blt 1198) (cond (x.blt 1195) (cond (x.blt 1193) 0 (cond (x.blt 1194) 3 4)) (cond (x.blt 1196) 0 (cond (x.blt 1197) 2 4))) (cond (x.blt 1201) (cond (x.blt 1199) 1 (cond (x.blt 1200) 2 5)) (cond (x.blt 1203) (cond (x.blt 1202) 4 0) (cond (x.blt 1204) 2 1)))) (cond (x.blt 1212) (cond (x.blt 1208) (cond (x.blt 1206) 5 (cond (x.blt 1207) 2 3)) (cond (x.blt 1210) (cond (x.blt 1209) 1 5) (cond (x.blt 1211) 2 5))) (cond (x.blt 1215) (cond (x.blt 1213) 0 (cond (x.blt 1214) 2 1)) (cond (x.blt 1217) (cond (x.blt 1216) 0 2) (cond (x.blt 1218) 5 5)))))) (cond (x.blt 1245) (cond (x.blt 1232) (cond (x.blt 1225) (cond (x.blt 1222) (cond (x.blt 1220) 0 (cond (x.blt 1221) 2 5)) (cond (x.blt 1223) 5 (cond (x.blt 1224) 2 1))) (cond (x.blt 1228) (cond (x.blt 1226) 5 (cond (x.blt 1227) 5 3)) (cond (x.blt 1230) (cond (x.blt 1229) 5 5) (cond (x.blt 1231) 3 5)))) (cond (x.blt 1238) (cond (x.blt 1235) (cond (x.blt 1233) 5 (cond (x.blt 1234) 5 5)) (cond (x.blt 1236) 5 (cond (x.blt 1237) 0 2))) (cond (x.blt 1241) (cond (x.blt 1239) 5 (cond (x.blt 1240) 0 2)) (cond (x.blt 1243) (cond (x.blt 1242) 5 5) (cond (x.blt 1244) 1 2))))) (cond (x.blt 1258) (cond (x.blt 1251) (cond (x.blt 1248) (cond (x.blt 1246) 3 (cond (x.blt 1247) 3 2)) (cond (x.blt 1249) 5 (cond (x.blt 1250) 0 4))) (cond (x.blt 1254) (cond (x.blt 1252) 2 (cond (x.blt 1253) 5 1)) (cond (x.blt 1256) (cond (x.blt 1255) 2 0) (cond (x.blt 1257) 0 4)))) (cond (x.blt 1265) (cond (x.blt 1261) (cond (x.blt 1259) 2 (cond (x.blt 1260) 0 0)) (cond (x.blt 1263) (cond (x.blt 1262) 2 4) (cond (x.blt 1264) 1 2))) (cond (x.blt 1268) (cond (x.blt 1266) 4 (cond (x.blt 1267) 0 4)) (cond (x.blt 1270) (cond (x.blt 1269) 2 3) (cond (x.blt 1271) 3 2))))))))) (cond (x.blt 1484) (cond (x.blt 1378) (cond (x.blt 1325) (cond (x.blt 1298) (cond (x.blt 1285) (cond (x.blt 1278) (cond (x.blt 1275) (cond (x.blt 1273) 0 (cond (x.blt 1274) 1 1)) (cond (x.blt 1276) 2 (cond (x.blt 1277) 0 0))) (cond (x.blt 1281) (cond (x.blt 1279) 2 (cond (x.blt 1280) 0 4)) (cond (x.blt 1283) (cond (x.blt 1282) 2 1) (cond (x.blt 1284) 1 1)))) (cond (x.blt 1291) (cond (x.blt 1288) (cond (x.blt 1286) 2 (cond (x.blt 1287) 3 3)) (cond (x.blt 1289) 2 (cond (x.blt 1290) 0 4))) (cond (x.blt 1294) (cond (x.blt 1292) 2 (cond (x.blt 1293) 2 1)) (cond (x.blt 1296) (cond (x.blt 1295) 1 2) (cond (x.blt 1297) 0 4))))) (cond (x.blt 1311) (cond (x.blt 1304) (cond (x.blt 1301) (cond (x.blt 1299) 3 (cond (x.blt 1300) 0 0)) (cond (x.blt 1302) 3 (cond (x.blt 1303) 2 1))) (cond (x.blt 1307) (cond (x.blt 1305) 3 (cond (x.blt 1306) 2 0)) (cond (x.blt 1309) (cond (x.blt 1308) 4 1) (cond (x.blt 1310) 2 3)))) (cond (x.blt 1318) (cond (x.blt 1314) (cond (x.blt 1312) 4 (cond (x.blt 1313) 2 1)) (cond (x.blt 1316) (cond (x.blt 1315) 1 2) (cond (x.blt 1317) 2 0))) (cond (x.blt 1321) (cond (x.blt 1319) 3 (cond (x.blt 1320) 2 4)) (cond (x.blt 1323) (cond (x.blt 1322) 3 0) (cond (x.blt 1324) 0 3)))))) (cond (x.blt 1351) (cond (x.blt 1338) (cond (x.blt 1331) (cond (x.blt 1328) (cond (x.blt 1326) 4 (cond (x.blt 1327) 2 3)) (cond (x.blt 1329) 4 (cond (x.blt 1330) 2 4))) (cond (x.blt 1334) (cond (x.blt 1332) 5 (cond (x.blt 1333) 4 2)) (cond (x.blt 1336) (cond (x.blt 1335) 1 1) (cond (x.blt 1337) 2 4)))) (cond (x.blt 1344) (cond (x.blt 1341) (cond (x.blt 1339) 3 (cond (x.blt 1340) 2 0)) (cond (x.blt 1342) 5 (cond (x.blt 1343) 4 2))) (cond (x.blt 1347) (cond (x.blt 1345) 3 (cond (x.blt 1346) 1 0)) (cond (x.blt 1349) (cond (x.blt 1348) 5 5) (cond (x.blt 1350) 5 2))))) (cond (x.blt 1364) (cond (x.blt 1357) (cond (x.blt 1354) (cond (x.blt 1352) 5 (cond (x.blt 1353) 5 2)) (cond (x.blt 1355) 5 (cond (x.blt 1356) 1 5))) (cond (x.blt 1360) (cond (x.blt 1358) 2 (cond (x.blt 1359) 5 5)) (cond (x.blt 1362) (cond (x.blt 1361) 5 5) (cond (x.blt 1363) 3 5)))) (cond (x.blt 1371) (cond (x.blt 1367) (cond (x.blt 1365) 2 (cond (x.blt 1366) 5 5)) (cond (x.blt 1369) (cond (x.blt 1368) 5 5) (cond (x.blt 1370) 5 2))) (cond (x.blt 1374) (cond (x.blt 1372) 1 (cond (x.blt 1373) 5 5)) (cond (x.blt 1376) (cond (x.blt 1375) 2 5) (cond (x.blt 1377) 3 2))))))) (cond (x.blt 1431) (cond (x.blt 1404) (cond (x.blt 1391) (cond (x.blt 1384) (cond (x.blt 1381) (cond (x.blt 1379) 5 (cond (x.blt 1380) 5 0)) (cond (x.blt 1382) 2 (cond (x.blt 1383) 3 5))) (cond (x.blt 1387) (cond (x.blt 1385) 2 (cond (x.blt 1386) 5 0)) (cond (x.blt 1389) (cond (x.blt 1388) 0 2) (cond (x.blt 1390) 4 0)))) (cond (x.blt 1397) (cond (x.blt 1394) (cond (x.blt 1392) 2 (cond (x.blt 1393) 1 4)) (cond (x.blt 1395) 2 (cond (x.blt 1396) 5 4))) (cond (x.blt 1400) (cond (x.blt 1398) 0 (cond (x.blt 1399) 2 3)) (cond (x.blt 1402) (cond (x.blt 1401) 3 2) (cond (x.blt 1403) 1 0))))) (cond (x.blt 1417) (cond (x.blt 1410) (cond (x.blt 1407) (cond (x.blt 1405) 2 (cond (x.blt 1406) 2 4)) (cond (x.blt 1408) 0 (cond (x.blt 1409) 2 0))) (cond (x.blt 1413) (cond (x.blt 1411) 0 (cond (x.blt 1412) 4 1)) (cond (x.blt 1415) (cond (x.blt 1414) 1 1) (cond (x.blt 1416) 2 3)))) (cond (x.blt 1424) (cond (x.blt 1420) (cond (x.blt 1418) 3 (cond (x.blt 1419) 2 4)) (cond (x.blt 1422) (cond (x.blt 1421) 0 4) (cond (x.blt 1423) 3 1))) (cond (x.blt 1427) (cond (x.blt 1425) 1 (cond (x.blt 1426) 2 0)) (cond (x.blt 1429) (cond (x.blt 1428) 0 2) (cond (x.blt 1430) 2 0)))))) (cond (x.blt 1457) (cond (x.blt 1444) (cond (x.blt 1437) (cond (x.blt 1434) (cond (x.blt 1432) 0 (cond (x.blt 1433) 2 1)) (cond (x.blt 1435) 1 (cond (x.blt 1436) 3 4))) (cond (x.blt 1440) (cond (x.blt 1438) 0 (cond (x.blt 1439) 4 2)) (cond (x.blt 1442) (cond (x.blt 1441) 3 3) (cond (x.blt 1443) 2 1)))) (cond (x.blt 1450) (cond (x.blt 1447) (cond (x.blt 1445) 1 (cond (x.blt 1446) 1 4)) (cond (x.blt 1448) 0 (cond (x.blt 1449) 0 2))) (cond (x.blt 1453) (cond (x.blt 1451) 0 (cond (x.blt 1452) 4 2)) (cond (x.blt 1455) (cond (x.blt 1454) 2 0) (cond (x.blt 1456) 1 2))))) (cond (x.blt 1470) (cond (x.blt 1463) (cond (x.blt 1460) (cond (x.blt 1458) 3 (cond (x.blt 1459) 3 2)) (cond (x.blt 1461) 0 (cond (x.blt 1462) 4 5))) (cond (x.blt 1466) (cond (x.blt 1464) 2 (cond (x.blt 1465) 4 1)) (cond (x.blt 1468) (cond (x.blt 1467) 2 0) (cond (x.blt 1469) 4 2)))) (cond (x.blt 1477) (cond (x.blt 1473) (cond (x.blt 1471) 0 (cond (x.blt 1472) 0 5)) (cond (x.blt 1475) (cond (x.blt 1474) 2 5) (cond (x.blt 1476) 3 2))) (cond (x.blt 1480) (cond (x.blt 1478) 0 (cond (x.blt 1479) 5 5)) (cond (x.blt 1482) (cond (x.blt 1481) 2 3) (cond (x.blt 1483) 5 2)))))))) (cond (x.blt 1590) (cond (x.blt 1537) (cond (x.blt 1510) (cond (x.blt 1497) (cond (x.blt 1490) (cond (x.blt 1487) (cond (x.blt 1485) 5 (cond (x.blt 1486) 5 1)) (cond (x.blt 1488) 2 (cond (x.blt 1489) 5 5))) (cond (x.blt 1493) (cond (x.blt 1491) 5 (cond (x.blt 1492) 5 5)) (cond (x.blt 1495) (cond (x.blt 1494) 2 5) (cond (x.blt 1496) 3 5)))) (cond (x.blt 1503) (cond (x.blt 1500) (cond (x.blt 1498) 5 (cond (x.blt 1499) 5 5)) (cond (x.blt 1501) 2 (cond (x.blt 1502) 5 1))) (cond (x.blt 1506) (cond (x.blt 1504) 5 (cond (x.blt 1505) 2 5)) (cond (x.blt 1508) (cond (x.blt 1507) 5 2) (cond (x.blt 1509) 5 5))))) (cond (x.blt 1523) (cond (x.blt 1516) (cond (x.blt 1513) (cond (x.blt 1511) 5 (cond (x.blt 1512) 0 1)) (cond (x.blt 1514) 3 (cond (x.blt 1515) 2 4))) (cond (x.blt 1519) (cond (x.blt 1517) 5 (cond (x.blt 1518) 0 1)) (cond (x.blt 1521) (cond (x.blt 1520) 3 4) (cond (x.blt 1522) 2 1)))) (cond (x.blt 1530) (cond (x.blt 1526) (cond (x.blt 1524) 1 (cond (x.blt 1525) 2 4)) (cond (x.blt 1528) (cond (x.blt 1527) 5 4) (cond (x.blt 1529) 2 4))) (cond (x.blt 1533) (cond (x.blt 1531) 3 (cond (x.blt 1532) 2 4)) (cond (x.blt 1535) (cond (x.blt 1534) 3 0) (cond (x.blt 1536) 0 3)))))) (cond (x.blt 1563) (cond (x.blt 1550) (cond (x.blt 1543) (cond (x.blt 1540) (cond (x.blt 1538) 4 (cond (x.blt 1539) 2 3)) (cond (x.blt 1541) 0 (cond (x.blt 1542) 2 2))) (cond (x.blt 1546) (cond (x.blt 1544) 1 (cond (x.blt 1545) 1 2)) (cond (x.blt 1548) (cond (x.blt 1547) 4 3) (cond (x.blt 1549) 2 1)))) (cond (x.blt 1556) (cond (x.blt 1553) (cond (x.blt 1551) 4 (cond (x.blt 1552) 0 2)) (cond (x.blt 1554) 3 (cond (x.blt 1555) 1 2))) (cond (x.blt 1559) (cond (x.blt 1557) 3 (cond (x.blt 1558) 0 0)) (cond (x.blt 1561) (cond (x.blt 1560) 3 4) (cond (x.blt 1562) 0 2))))) (cond (x.blt 1576) (cond (x.blt 1569) (cond (x.blt 1566) (cond (x.blt 1564) 1 (cond (x.blt 1565) 1 2)) (cond (x.blt 1567) 2 (cond (x.blt 1568) 4 0))) (cond (x.blt 1572) (cond (x.blt 1570) 2 (cond (x.blt 1571) 3 3)) (cond (x.blt 1574) (cond (x.blt 1573) 2 1) (cond (x.blt 1575) 1 1)))) (cond (x.blt 1583) (cond (x.blt 1579) (cond (x.blt 1577) 2 (cond (x.blt 1578) 4 0)) (cond (x.blt 1581) (cond (x.blt 1580) 2 0) (cond (x.blt 1582) 0 2))) (cond (x.blt 1586) (cond (x.blt 1584) 1 (cond (x.blt 1585) 1 0)) (cond (x.blt 1588) (cond (x.blt 1587) 2 3) (cond (x.blt 1589) 3 2))))))) (cond (x.blt 1643) (cond (x.blt 1616) (cond (x.blt 1603) (cond (x.blt 1596) (cond (x.blt 1593) (cond (x.blt 1591) 4 (cond (x.blt 1592) 0 4)) (cond (x.blt 1594) 2 (cond (x.blt 1595) 1 4))) (cond (x.blt 1599) (cond (x.blt 1597) 2 (cond (x.blt 1598) 0 0)) (cond (x.blt 1601) (cond (x.blt 1600) 2 4) (cond (x.blt 1602) 0 0)))) (cond (x.blt 1609) (cond (x.blt 1606) (cond (x.blt 1604) 2 (cond (x.blt 1605) 1 5)) (cond (x.blt 1607) 2 (cond (x.blt 1608) 4 0))) (cond (x.blt 1612) (cond (x.blt 1610) 5 (cond (x.blt 1611) 2 3)) (cond (x.blt 1614) (cond (x.blt 1613) 3 2) (cond (x.blt 1615) 1 5))))) (cond (x.blt 1629) (cond (x.blt 1622) (cond (x.blt 1619) (cond (x.blt 1617) 5 (cond (x.blt 1618) 2 0)) (cond (x.blt 1620) 5 (cond (x.blt 1621) 2 0))) (cond (x.blt 1625) (cond (x.blt 1623) 5 (cond (x.blt 1624) 2 5)) (cond (x.blt 1627) (cond (x.blt 1626) 5 5) (cond (x.blt 1628) 3 5)))) (cond (x.blt 1636) (cond (x.blt 1632) (cond (x.blt 1630) 5 (cond (x.blt 1631) 3 5)) (cond (x.blt 1634) (cond (x.blt 1633) 5 1) (cond (x.blt 1635) 2 5))) (cond (x.blt 1639) (cond (x.blt 1637) 5 (cond (x.blt 1638) 2 0)) (cond (x.blt 1641) (cond (x.blt 1640) 5 5) (cond (x.blt 1642) 2 0)))))) (cond (x.blt 1670) (cond (x.blt 1656) (cond (x.blt 1649) (cond (x.blt 1646) (cond (x.blt 1644) 1 (cond (x.blt 1645) 2 0)) (cond (x.blt 1647) 5 (cond (x.blt 1648) 2 5))) (cond (x.blt 1652) (cond (x.blt 1650) 1 (cond (x.blt 1651) 3 2)) (cond (x.blt 1654) (cond (x.blt 1653) 5 1) (cond (x.blt 1655) 2 0)))) (cond (x.blt 1663) (cond (x.blt 1659) (cond (x.blt 1657) 4 (cond (x.blt 1658) 5 2)) (cond (x.blt 1661) (cond (x.blt 1660) 1 4) (cond (x.blt 1662) 2 0))) (cond (x.blt 1666) (cond (x.blt 1664) 4 (cond (x.blt 1665) 3 0)) (cond (x.blt 1668) (cond (x.blt 1667) 0 3) (cond (x.blt 1669) 2 1))))) (cond (x.blt 1683) (cond (x.blt 1676) (cond (x.blt 1673) (cond (x.blt 1671) 3 (cond (x.blt 1672) 2 0)) (cond (x.blt 1674) 4 (cond (x.blt 1675) 1 2))) (cond (x.blt 1679) (cond (x.blt 1677) 3 (cond (x.blt 1678) 4 2)) (cond (x.blt 1681) (cond (x.blt 1680) 1 1) (cond (x.blt 1682) 4 0)))) (cond (x.blt 1690) (cond (x.blt 1686) (cond (x.blt 1684) 0 (cond (x.blt 1685) 1 2)) (cond (x.blt 1688) (cond (x.blt 1687) 4 3) (cond (x.blt 1689) 0 0))) (cond (x.blt 1693) (cond (x.blt 1691) 3 (cond (x.blt 1692) 4 2)) (cond (x.blt 1695) (cond (x.blt 1694) 3 1) (cond (x.blt 1696) 2 4))))))))))) 0

example : sevenLabel 1 = 4 := rfl
example : sevenLabel 1697 = 0 := rfl

private def sevenColor (x : ℕ) : Fin 7 := ⟨sevenLabel x % 7, Nat.mod_lt _ (by decide)⟩

example : sevenColor 0 = 0 := rfl
example : sevenColor 1 = 4 := rfl
example : sevenColor 1697 = 0 := rfl

private def sevenClasses (i : Fin 7) : List ℕ :=
  ([sevenClass0, sevenClass1, sevenClass2, sevenClass3, sevenClass4, sevenClass5, sevenClass6] : List (List ℕ))[i.val]?.getD []

private theorem sevenSorted0 : sevenClass0.Pairwise (· ≤ ·) := by decide

private theorem sevenMerge0_0 : mergeRows sevenChunk0_0 sevenClass0 = true := by decide

private theorem sevenMerge0_1 : mergeRows sevenChunk0_1 sevenClass0 = true := by decide

private theorem sevenMerge0_2 : mergeRows sevenChunk0_2 sevenClass0 = true := by decide

private theorem sevenMerge0_3 : mergeRows sevenChunk0_3 sevenClass0 = true := by decide

private theorem sevenMerge0_4 : mergeRows sevenChunk0_4 sevenClass0 = true := by decide

private theorem sevenMerge0_5 : mergeRows sevenChunk0_5 sevenClass0 = true := by decide

private theorem sevenMerge0_6 : mergeRows sevenChunk0_6 sevenClass0 = true := by decide

private theorem sevenMerge0_7 : mergeRows sevenChunk0_7 sevenClass0 = true := by decide

private theorem sevenMerge0_8 : mergeRows sevenChunk0_8 sevenClass0 = true := by decide

private theorem sevenMerge0_9 : mergeRows sevenChunk0_9 sevenClass0 = true := by decide

private theorem sevenMerge0_10 : mergeRows sevenChunk0_10 sevenClass0 = true := by decide

private theorem sevenMerge0_11 : mergeRows sevenChunk0_11 sevenClass0 = true := by decide

private theorem sevenMerge0_12 : mergeRows sevenChunk0_12 sevenClass0 = true := by decide

private theorem sevenFree0 : SumFree sevenClass0.toFinset := by
  apply sumFree_of_merge _ sevenSorted0
  have hg : sevenRows0.all (fun chunk => mergeRows chunk sevenClass0) = true := by
    simp only [sevenRows0, List.all_cons, List.all_nil, sevenMerge0_0, sevenMerge0_1, sevenMerge0_2, sevenMerge0_3, sevenMerge0_4, sevenMerge0_5, sevenMerge0_6, sevenMerge0_7, sevenMerge0_8, sevenMerge0_9, sevenMerge0_10, sevenMerge0_11, sevenMerge0_12, Bool.and_self]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨chunk, hc, hxc⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp hg chunk hc) x hxc

private theorem sevenSorted1 : sevenClass1.Pairwise (· ≤ ·) := by decide

private theorem sevenMerge1_0 : mergeRows sevenChunk1_0 sevenClass1 = true := by decide

private theorem sevenMerge1_1 : mergeRows sevenChunk1_1 sevenClass1 = true := by decide

private theorem sevenMerge1_2 : mergeRows sevenChunk1_2 sevenClass1 = true := by decide

private theorem sevenMerge1_3 : mergeRows sevenChunk1_3 sevenClass1 = true := by decide

private theorem sevenMerge1_4 : mergeRows sevenChunk1_4 sevenClass1 = true := by decide

private theorem sevenMerge1_5 : mergeRows sevenChunk1_5 sevenClass1 = true := by decide

private theorem sevenMerge1_6 : mergeRows sevenChunk1_6 sevenClass1 = true := by decide

private theorem sevenMerge1_7 : mergeRows sevenChunk1_7 sevenClass1 = true := by decide

private theorem sevenMerge1_8 : mergeRows sevenChunk1_8 sevenClass1 = true := by decide

private theorem sevenMerge1_9 : mergeRows sevenChunk1_9 sevenClass1 = true := by decide

private theorem sevenMerge1_10 : mergeRows sevenChunk1_10 sevenClass1 = true := by decide

private theorem sevenFree1 : SumFree sevenClass1.toFinset := by
  apply sumFree_of_merge _ sevenSorted1
  have hg : sevenRows1.all (fun chunk => mergeRows chunk sevenClass1) = true := by
    simp only [sevenRows1, List.all_cons, List.all_nil, sevenMerge1_0, sevenMerge1_1, sevenMerge1_2, sevenMerge1_3, sevenMerge1_4, sevenMerge1_5, sevenMerge1_6, sevenMerge1_7, sevenMerge1_8, sevenMerge1_9, sevenMerge1_10, Bool.and_self]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨chunk, hc, hxc⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp hg chunk hc) x hxc

private theorem sevenSorted2 : sevenClass2.Pairwise (· ≤ ·) := by decide

private theorem sevenMerge2_0 : mergeRows sevenChunk2_0 sevenClass2 = true := by decide

private theorem sevenMerge2_1 : mergeRows sevenChunk2_1 sevenClass2 = true := by decide

private theorem sevenMerge2_2 : mergeRows sevenChunk2_2 sevenClass2 = true := by decide

private theorem sevenMerge2_3 : mergeRows sevenChunk2_3 sevenClass2 = true := by decide

private theorem sevenMerge2_4 : mergeRows sevenChunk2_4 sevenClass2 = true := by decide

private theorem sevenMerge2_5 : mergeRows sevenChunk2_5 sevenClass2 = true := by decide

private theorem sevenMerge2_6 : mergeRows sevenChunk2_6 sevenClass2 = true := by decide

private theorem sevenMerge2_7 : mergeRows sevenChunk2_7 sevenClass2 = true := by decide

private theorem sevenMerge2_8 : mergeRows sevenChunk2_8 sevenClass2 = true := by decide

private theorem sevenMerge2_9 : mergeRows sevenChunk2_9 sevenClass2 = true := by decide

private theorem sevenMerge2_10 : mergeRows sevenChunk2_10 sevenClass2 = true := by decide

private theorem sevenMerge2_11 : mergeRows sevenChunk2_11 sevenClass2 = true := by decide

private theorem sevenMerge2_12 : mergeRows sevenChunk2_12 sevenClass2 = true := by decide

private theorem sevenMerge2_13 : mergeRows sevenChunk2_13 sevenClass2 = true := by decide

private theorem sevenMerge2_14 : mergeRows sevenChunk2_14 sevenClass2 = true := by decide

private theorem sevenMerge2_15 : mergeRows sevenChunk2_15 sevenClass2 = true := by decide

private theorem sevenMerge2_16 : mergeRows sevenChunk2_16 sevenClass2 = true := by decide

private theorem sevenMerge2_17 : mergeRows sevenChunk2_17 sevenClass2 = true := by decide

private theorem sevenMerge2_18 : mergeRows sevenChunk2_18 sevenClass2 = true := by decide

private theorem sevenMerge2_19 : mergeRows sevenChunk2_19 sevenClass2 = true := by decide

private theorem sevenFree2 : SumFree sevenClass2.toFinset := by
  apply sumFree_of_merge _ sevenSorted2
  have hg : sevenRows2.all (fun chunk => mergeRows chunk sevenClass2) = true := by
    simp only [sevenRows2, List.all_cons, List.all_nil, sevenMerge2_0, sevenMerge2_1, sevenMerge2_2, sevenMerge2_3, sevenMerge2_4, sevenMerge2_5, sevenMerge2_6, sevenMerge2_7, sevenMerge2_8, sevenMerge2_9, sevenMerge2_10, sevenMerge2_11, sevenMerge2_12, sevenMerge2_13, sevenMerge2_14, sevenMerge2_15, sevenMerge2_16, sevenMerge2_17, sevenMerge2_18, sevenMerge2_19, Bool.and_self]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨chunk, hc, hxc⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp hg chunk hc) x hxc

private theorem sevenSorted3 : sevenClass3.Pairwise (· ≤ ·) := by decide

private theorem sevenMerge3_0 : mergeRows sevenChunk3_0 sevenClass3 = true := by decide

private theorem sevenMerge3_1 : mergeRows sevenChunk3_1 sevenClass3 = true := by decide

private theorem sevenMerge3_2 : mergeRows sevenChunk3_2 sevenClass3 = true := by decide

private theorem sevenMerge3_3 : mergeRows sevenChunk3_3 sevenClass3 = true := by decide

private theorem sevenMerge3_4 : mergeRows sevenChunk3_4 sevenClass3 = true := by decide

private theorem sevenMerge3_5 : mergeRows sevenChunk3_5 sevenClass3 = true := by decide

private theorem sevenMerge3_6 : mergeRows sevenChunk3_6 sevenClass3 = true := by decide

private theorem sevenMerge3_7 : mergeRows sevenChunk3_7 sevenClass3 = true := by decide

private theorem sevenMerge3_8 : mergeRows sevenChunk3_8 sevenClass3 = true := by decide

private theorem sevenMerge3_9 : mergeRows sevenChunk3_9 sevenClass3 = true := by decide

private theorem sevenFree3 : SumFree sevenClass3.toFinset := by
  apply sumFree_of_merge _ sevenSorted3
  have hg : sevenRows3.all (fun chunk => mergeRows chunk sevenClass3) = true := by
    simp only [sevenRows3, List.all_cons, List.all_nil, sevenMerge3_0, sevenMerge3_1, sevenMerge3_2, sevenMerge3_3, sevenMerge3_4, sevenMerge3_5, sevenMerge3_6, sevenMerge3_7, sevenMerge3_8, sevenMerge3_9, Bool.and_self]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨chunk, hc, hxc⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp hg chunk hc) x hxc

private theorem sevenSorted4 : sevenClass4.Pairwise (· ≤ ·) := by decide

private theorem sevenMerge4_0 : mergeRows sevenChunk4_0 sevenClass4 = true := by decide

private theorem sevenMerge4_1 : mergeRows sevenChunk4_1 sevenClass4 = true := by decide

private theorem sevenMerge4_2 : mergeRows sevenChunk4_2 sevenClass4 = true := by decide

private theorem sevenMerge4_3 : mergeRows sevenChunk4_3 sevenClass4 = true := by decide

private theorem sevenMerge4_4 : mergeRows sevenChunk4_4 sevenClass4 = true := by decide

private theorem sevenMerge4_5 : mergeRows sevenChunk4_5 sevenClass4 = true := by decide

private theorem sevenMerge4_6 : mergeRows sevenChunk4_6 sevenClass4 = true := by decide

private theorem sevenMerge4_7 : mergeRows sevenChunk4_7 sevenClass4 = true := by decide

private theorem sevenMerge4_8 : mergeRows sevenChunk4_8 sevenClass4 = true := by decide

private theorem sevenMerge4_9 : mergeRows sevenChunk4_9 sevenClass4 = true := by decide

private theorem sevenFree4 : SumFree sevenClass4.toFinset := by
  apply sumFree_of_merge _ sevenSorted4
  have hg : sevenRows4.all (fun chunk => mergeRows chunk sevenClass4) = true := by
    simp only [sevenRows4, List.all_cons, List.all_nil, sevenMerge4_0, sevenMerge4_1, sevenMerge4_2, sevenMerge4_3, sevenMerge4_4, sevenMerge4_5, sevenMerge4_6, sevenMerge4_7, sevenMerge4_8, sevenMerge4_9, Bool.and_self]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨chunk, hc, hxc⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp hg chunk hc) x hxc

private theorem sevenSorted5 : sevenClass5.Pairwise (· ≤ ·) := by decide

private theorem sevenMerge5_0 : mergeRows sevenChunk5_0 sevenClass5 = true := by decide

private theorem sevenMerge5_1 : mergeRows sevenChunk5_1 sevenClass5 = true := by decide

private theorem sevenMerge5_2 : mergeRows sevenChunk5_2 sevenClass5 = true := by decide

private theorem sevenMerge5_3 : mergeRows sevenChunk5_3 sevenClass5 = true := by decide

private theorem sevenMerge5_4 : mergeRows sevenChunk5_4 sevenClass5 = true := by decide

private theorem sevenMerge5_5 : mergeRows sevenChunk5_5 sevenClass5 = true := by decide

private theorem sevenMerge5_6 : mergeRows sevenChunk5_6 sevenClass5 = true := by decide

private theorem sevenMerge5_7 : mergeRows sevenChunk5_7 sevenClass5 = true := by decide

private theorem sevenMerge5_8 : mergeRows sevenChunk5_8 sevenClass5 = true := by decide

private theorem sevenMerge5_9 : mergeRows sevenChunk5_9 sevenClass5 = true := by decide

private theorem sevenMerge5_10 : mergeRows sevenChunk5_10 sevenClass5 = true := by decide

private theorem sevenMerge5_11 : mergeRows sevenChunk5_11 sevenClass5 = true := by decide

private theorem sevenMerge5_12 : mergeRows sevenChunk5_12 sevenClass5 = true := by decide

private theorem sevenFree5 : SumFree sevenClass5.toFinset := by
  apply sumFree_of_merge _ sevenSorted5
  have hg : sevenRows5.all (fun chunk => mergeRows chunk sevenClass5) = true := by
    simp only [sevenRows5, List.all_cons, List.all_nil, sevenMerge5_0, sevenMerge5_1, sevenMerge5_2, sevenMerge5_3, sevenMerge5_4, sevenMerge5_5, sevenMerge5_6, sevenMerge5_7, sevenMerge5_8, sevenMerge5_9, sevenMerge5_10, sevenMerge5_11, sevenMerge5_12, Bool.and_self]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨chunk, hc, hxc⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp hg chunk hc) x hxc

private theorem sevenSorted6 : sevenClass6.Pairwise (· ≤ ·) := by decide

private theorem sevenMerge6_0 : mergeRows sevenChunk6_0 sevenClass6 = true := by decide

private theorem sevenMerge6_1 : mergeRows sevenChunk6_1 sevenClass6 = true := by decide

private theorem sevenMerge6_2 : mergeRows sevenChunk6_2 sevenClass6 = true := by decide

private theorem sevenMerge6_3 : mergeRows sevenChunk6_3 sevenClass6 = true := by decide

private theorem sevenMerge6_4 : mergeRows sevenChunk6_4 sevenClass6 = true := by decide

private theorem sevenMerge6_5 : mergeRows sevenChunk6_5 sevenClass6 = true := by decide

private theorem sevenMerge6_6 : mergeRows sevenChunk6_6 sevenClass6 = true := by decide

private theorem sevenMerge6_7 : mergeRows sevenChunk6_7 sevenClass6 = true := by decide

private theorem sevenMerge6_8 : mergeRows sevenChunk6_8 sevenClass6 = true := by decide

private theorem sevenMerge6_9 : mergeRows sevenChunk6_9 sevenClass6 = true := by decide

private theorem sevenMerge6_10 : mergeRows sevenChunk6_10 sevenClass6 = true := by decide

private theorem sevenMerge6_11 : mergeRows sevenChunk6_11 sevenClass6 = true := by decide

private theorem sevenMerge6_12 : mergeRows sevenChunk6_12 sevenClass6 = true := by decide

private theorem sevenMerge6_13 : mergeRows sevenChunk6_13 sevenClass6 = true := by decide

private theorem sevenMerge6_14 : mergeRows sevenChunk6_14 sevenClass6 = true := by decide

private theorem sevenMerge6_15 : mergeRows sevenChunk6_15 sevenClass6 = true := by decide

private theorem sevenMerge6_16 : mergeRows sevenChunk6_16 sevenClass6 = true := by decide

private theorem sevenMerge6_17 : mergeRows sevenChunk6_17 sevenClass6 = true := by decide

private theorem sevenMerge6_18 : mergeRows sevenChunk6_18 sevenClass6 = true := by decide

private theorem sevenMerge6_19 : mergeRows sevenChunk6_19 sevenClass6 = true := by decide

private theorem sevenMerge6_20 : mergeRows sevenChunk6_20 sevenClass6 = true := by decide

private theorem sevenMerge6_21 : mergeRows sevenChunk6_21 sevenClass6 = true := by decide

private theorem sevenMerge6_22 : mergeRows sevenChunk6_22 sevenClass6 = true := by decide

private theorem sevenMerge6_23 : mergeRows sevenChunk6_23 sevenClass6 = true := by decide

private theorem sevenMerge6_24 : mergeRows sevenChunk6_24 sevenClass6 = true := by decide

private theorem sevenMerge6_25 : mergeRows sevenChunk6_25 sevenClass6 = true := by decide

private theorem sevenMerge6_26 : mergeRows sevenChunk6_26 sevenClass6 = true := by decide

private theorem sevenMerge6_27 : mergeRows sevenChunk6_27 sevenClass6 = true := by decide

private theorem sevenMerge6_28 : mergeRows sevenChunk6_28 sevenClass6 = true := by decide

private theorem sevenMerge6_29 : mergeRows sevenChunk6_29 sevenClass6 = true := by decide

private theorem sevenMerge6_30 : mergeRows sevenChunk6_30 sevenClass6 = true := by decide

private theorem sevenMerge6_31 : mergeRows sevenChunk6_31 sevenClass6 = true := by decide

private theorem sevenFree6 : SumFree sevenClass6.toFinset := by
  apply sumFree_of_merge _ sevenSorted6
  have hg : sevenRows6.all (fun chunk => mergeRows chunk sevenClass6) = true := by
    simp only [sevenRows6, List.all_cons, List.all_nil, sevenMerge6_0, sevenMerge6_1, sevenMerge6_2, sevenMerge6_3, sevenMerge6_4, sevenMerge6_5, sevenMerge6_6, sevenMerge6_7, sevenMerge6_8, sevenMerge6_9, sevenMerge6_10, sevenMerge6_11, sevenMerge6_12, sevenMerge6_13, sevenMerge6_14, sevenMerge6_15, sevenMerge6_16, sevenMerge6_17, sevenMerge6_18, sevenMerge6_19, sevenMerge6_20, sevenMerge6_21, sevenMerge6_22, sevenMerge6_23, sevenMerge6_24, sevenMerge6_25, sevenMerge6_26, sevenMerge6_27, sevenMerge6_28, sevenMerge6_29, sevenMerge6_30, sevenMerge6_31, Bool.and_self]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨chunk, hc, hxc⟩ := List.mem_flatten.mp hx
  exact List.all_eq_true.mp (List.all_eq_true.mp hg chunk hc) x hxc
private theorem sevenCover0 : covered sevenColor sevenClasses 1 32 = true := by decide

private theorem sevenCover1 : covered sevenColor sevenClasses 33 32 = true := by decide

private theorem sevenCover2 : covered sevenColor sevenClasses 65 32 = true := by decide

private theorem sevenCover3 : covered sevenColor sevenClasses 97 32 = true := by decide

private theorem sevenCover4 : covered sevenColor sevenClasses 129 32 = true := by decide

private theorem sevenCover5 : covered sevenColor sevenClasses 161 32 = true := by decide

private theorem sevenCover6 : covered sevenColor sevenClasses 193 32 = true := by decide

private theorem sevenCover7 : covered sevenColor sevenClasses 225 32 = true := by decide

private theorem sevenCover8 : covered sevenColor sevenClasses 257 32 = true := by decide

private theorem sevenCover9 : covered sevenColor sevenClasses 289 32 = true := by decide

private theorem sevenCover10 : covered sevenColor sevenClasses 321 32 = true := by decide

private theorem sevenCover11 : covered sevenColor sevenClasses 353 32 = true := by decide

private theorem sevenCover12 : covered sevenColor sevenClasses 385 32 = true := by decide

private theorem sevenCover13 : covered sevenColor sevenClasses 417 32 = true := by decide

private theorem sevenCover14 : covered sevenColor sevenClasses 449 32 = true := by decide

private theorem sevenCover15 : covered sevenColor sevenClasses 481 32 = true := by decide

private theorem sevenCover16 : covered sevenColor sevenClasses 513 32 = true := by decide

private theorem sevenCover17 : covered sevenColor sevenClasses 545 32 = true := by decide

private theorem sevenCover18 : covered sevenColor sevenClasses 577 32 = true := by decide

private theorem sevenCover19 : covered sevenColor sevenClasses 609 32 = true := by decide

private theorem sevenCover20 : covered sevenColor sevenClasses 641 32 = true := by decide

private theorem sevenCover21 : covered sevenColor sevenClasses 673 32 = true := by decide

private theorem sevenCover22 : covered sevenColor sevenClasses 705 32 = true := by decide

private theorem sevenCover23 : covered sevenColor sevenClasses 737 32 = true := by decide

private theorem sevenCover24 : covered sevenColor sevenClasses 769 32 = true := by decide

private theorem sevenCover25 : covered sevenColor sevenClasses 801 32 = true := by decide

private theorem sevenCover26 : covered sevenColor sevenClasses 833 32 = true := by decide

private theorem sevenCover27 : covered sevenColor sevenClasses 865 32 = true := by decide

private theorem sevenCover28 : covered sevenColor sevenClasses 897 32 = true := by decide

private theorem sevenCover29 : covered sevenColor sevenClasses 929 32 = true := by decide

private theorem sevenCover30 : covered sevenColor sevenClasses 961 32 = true := by decide

private theorem sevenCover31 : covered sevenColor sevenClasses 993 32 = true := by decide

private theorem sevenCover32 : covered sevenColor sevenClasses 1025 32 = true := by decide

private theorem sevenCover33 : covered sevenColor sevenClasses 1057 32 = true := by decide

private theorem sevenCover34 : covered sevenColor sevenClasses 1089 32 = true := by decide

private theorem sevenCover35 : covered sevenColor sevenClasses 1121 32 = true := by decide

private theorem sevenCover36 : covered sevenColor sevenClasses 1153 32 = true := by decide

private theorem sevenCover37 : covered sevenColor sevenClasses 1185 32 = true := by decide

private theorem sevenCover38 : covered sevenColor sevenClasses 1217 32 = true := by decide

private theorem sevenCover39 : covered sevenColor sevenClasses 1249 32 = true := by decide

private theorem sevenCover40 : covered sevenColor sevenClasses 1281 32 = true := by decide

private theorem sevenCover41 : covered sevenColor sevenClasses 1313 32 = true := by decide

private theorem sevenCover42 : covered sevenColor sevenClasses 1345 32 = true := by decide

private theorem sevenCover43 : covered sevenColor sevenClasses 1377 32 = true := by decide

private theorem sevenCover44 : covered sevenColor sevenClasses 1409 32 = true := by decide

private theorem sevenCover45 : covered sevenColor sevenClasses 1441 32 = true := by decide

private theorem sevenCover46 : covered sevenColor sevenClasses 1473 32 = true := by decide

private theorem sevenCover47 : covered sevenColor sevenClasses 1505 32 = true := by decide

private theorem sevenCover48 : covered sevenColor sevenClasses 1537 32 = true := by decide

private theorem sevenCover49 : covered sevenColor sevenClasses 1569 32 = true := by decide

private theorem sevenCover50 : covered sevenColor sevenClasses 1601 32 = true := by decide

private theorem sevenCover51 : covered sevenColor sevenClasses 1633 32 = true := by decide

private theorem sevenCover52 : covered sevenColor sevenClasses 1665 32 = true := by decide

private theorem sevenCoverage : ∀ x ∈ Finset.Icc 1 1696, x ∈ sevenClasses (sevenColor x) := by
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp hx

  by_cases h1 : x < 33
  · exact covered_spec _ _ 1 32 sevenCover0 x (by omega) h1

  by_cases h33 : x < 65
  · exact covered_spec _ _ 33 32 sevenCover1 x (by omega) h33

  by_cases h65 : x < 97
  · exact covered_spec _ _ 65 32 sevenCover2 x (by omega) h65

  by_cases h97 : x < 129
  · exact covered_spec _ _ 97 32 sevenCover3 x (by omega) h97

  by_cases h129 : x < 161
  · exact covered_spec _ _ 129 32 sevenCover4 x (by omega) h129

  by_cases h161 : x < 193
  · exact covered_spec _ _ 161 32 sevenCover5 x (by omega) h161

  by_cases h193 : x < 225
  · exact covered_spec _ _ 193 32 sevenCover6 x (by omega) h193

  by_cases h225 : x < 257
  · exact covered_spec _ _ 225 32 sevenCover7 x (by omega) h225

  by_cases h257 : x < 289
  · exact covered_spec _ _ 257 32 sevenCover8 x (by omega) h257

  by_cases h289 : x < 321
  · exact covered_spec _ _ 289 32 sevenCover9 x (by omega) h289

  by_cases h321 : x < 353
  · exact covered_spec _ _ 321 32 sevenCover10 x (by omega) h321

  by_cases h353 : x < 385
  · exact covered_spec _ _ 353 32 sevenCover11 x (by omega) h353

  by_cases h385 : x < 417
  · exact covered_spec _ _ 385 32 sevenCover12 x (by omega) h385

  by_cases h417 : x < 449
  · exact covered_spec _ _ 417 32 sevenCover13 x (by omega) h417

  by_cases h449 : x < 481
  · exact covered_spec _ _ 449 32 sevenCover14 x (by omega) h449

  by_cases h481 : x < 513
  · exact covered_spec _ _ 481 32 sevenCover15 x (by omega) h481

  by_cases h513 : x < 545
  · exact covered_spec _ _ 513 32 sevenCover16 x (by omega) h513

  by_cases h545 : x < 577
  · exact covered_spec _ _ 545 32 sevenCover17 x (by omega) h545

  by_cases h577 : x < 609
  · exact covered_spec _ _ 577 32 sevenCover18 x (by omega) h577

  by_cases h609 : x < 641
  · exact covered_spec _ _ 609 32 sevenCover19 x (by omega) h609

  by_cases h641 : x < 673
  · exact covered_spec _ _ 641 32 sevenCover20 x (by omega) h641

  by_cases h673 : x < 705
  · exact covered_spec _ _ 673 32 sevenCover21 x (by omega) h673

  by_cases h705 : x < 737
  · exact covered_spec _ _ 705 32 sevenCover22 x (by omega) h705

  by_cases h737 : x < 769
  · exact covered_spec _ _ 737 32 sevenCover23 x (by omega) h737

  by_cases h769 : x < 801
  · exact covered_spec _ _ 769 32 sevenCover24 x (by omega) h769

  by_cases h801 : x < 833
  · exact covered_spec _ _ 801 32 sevenCover25 x (by omega) h801

  by_cases h833 : x < 865
  · exact covered_spec _ _ 833 32 sevenCover26 x (by omega) h833

  by_cases h865 : x < 897
  · exact covered_spec _ _ 865 32 sevenCover27 x (by omega) h865

  by_cases h897 : x < 929
  · exact covered_spec _ _ 897 32 sevenCover28 x (by omega) h897

  by_cases h929 : x < 961
  · exact covered_spec _ _ 929 32 sevenCover29 x (by omega) h929

  by_cases h961 : x < 993
  · exact covered_spec _ _ 961 32 sevenCover30 x (by omega) h961

  by_cases h993 : x < 1025
  · exact covered_spec _ _ 993 32 sevenCover31 x (by omega) h993

  by_cases h1025 : x < 1057
  · exact covered_spec _ _ 1025 32 sevenCover32 x (by omega) h1025

  by_cases h1057 : x < 1089
  · exact covered_spec _ _ 1057 32 sevenCover33 x (by omega) h1057

  by_cases h1089 : x < 1121
  · exact covered_spec _ _ 1089 32 sevenCover34 x (by omega) h1089

  by_cases h1121 : x < 1153
  · exact covered_spec _ _ 1121 32 sevenCover35 x (by omega) h1121

  by_cases h1153 : x < 1185
  · exact covered_spec _ _ 1153 32 sevenCover36 x (by omega) h1153

  by_cases h1185 : x < 1217
  · exact covered_spec _ _ 1185 32 sevenCover37 x (by omega) h1185

  by_cases h1217 : x < 1249
  · exact covered_spec _ _ 1217 32 sevenCover38 x (by omega) h1217

  by_cases h1249 : x < 1281
  · exact covered_spec _ _ 1249 32 sevenCover39 x (by omega) h1249

  by_cases h1281 : x < 1313
  · exact covered_spec _ _ 1281 32 sevenCover40 x (by omega) h1281

  by_cases h1313 : x < 1345
  · exact covered_spec _ _ 1313 32 sevenCover41 x (by omega) h1313

  by_cases h1345 : x < 1377
  · exact covered_spec _ _ 1345 32 sevenCover42 x (by omega) h1345

  by_cases h1377 : x < 1409
  · exact covered_spec _ _ 1377 32 sevenCover43 x (by omega) h1377

  by_cases h1409 : x < 1441
  · exact covered_spec _ _ 1409 32 sevenCover44 x (by omega) h1409

  by_cases h1441 : x < 1473
  · exact covered_spec _ _ 1441 32 sevenCover45 x (by omega) h1441

  by_cases h1473 : x < 1505
  · exact covered_spec _ _ 1473 32 sevenCover46 x (by omega) h1473

  by_cases h1505 : x < 1537
  · exact covered_spec _ _ 1505 32 sevenCover47 x (by omega) h1505

  by_cases h1537 : x < 1569
  · exact covered_spec _ _ 1537 32 sevenCover48 x (by omega) h1537

  by_cases h1569 : x < 1601
  · exact covered_spec _ _ 1569 32 sevenCover49 x (by omega) h1569

  by_cases h1601 : x < 1633
  · exact covered_spec _ _ 1601 32 sevenCover50 x (by omega) h1601

  by_cases h1633 : x < 1665
  · exact covered_spec _ _ 1633 32 sevenCover51 x (by omega) h1633

  exact covered_spec _ _ 1665 32 sevenCover52 x (by omega) (by omega)

/-- Rowley's 2021 seven-color workbook gives a sum-free 7-coloring through 1696, including diagonal sums. -/
theorem schur_seven_lower : SchurColorable 7 1696 := by
  apply colorable_of_lists sevenColor sevenClasses sevenCoverage
  intro i
  fin_cases i

  · exact sevenFree0

  · exact sevenFree1

  · exact sevenFree2

  · exact sevenFree3

  · exact sevenFree4

  · exact sevenFree5

  · exact sevenFree6

example : SchurColorable 7 1696 := schur_seven_lower

end SchurNumbers
