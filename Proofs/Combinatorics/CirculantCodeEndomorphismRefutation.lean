/-
# Gupta–K N: a circulant-code endomorphism counterexample

Neha Gupta and Suhith K N, *Neural codes and neural ring endomorphisms*,
arXiv:2106.06565v3, Section 5, Conjecture `conj2`, predicts
`|NRE(C)| = (p²+p+3)n + p²(n/p)!` when `3 < p < n-1` and `p ∣ n`.

For `n = 8`, `p = 4`, the certificate below gives 728 distinct pullback
neural ring endomorphisms, exceeding the predicted 216. Only this lower
bound, not exact enumeration of all endomorphisms, is needed.
The neural ring is the function ring `F₂[C]`; its distinguished functions
`x_i(c)` indicate whether neuron `i` fires. A neural ring endomorphism
sends each `x_i` into `{x_j} ∪ {0,1}`.

## Model

* Codewords are indexed by `Fin n` (0-indexed: paper's `c_{k+1}` is
  `codeword n p k`). Codeword `k` contains neuron `j` iff `(k - j) mod n < p`,
  so `codeword n p (p-1)` is `1^p 0^(n-p)` and each row is the previous one
  shifted right by one, as in the paper.
* The neural ring is `Fin n → ZMod 2` (functions on the code), `x_i` is the
  function `neuralX n p i` with `x_i(c_k) = 1` iff neuron `i ∈ c_k`.
-/
import Mathlib

set_option autoImplicit false
-- The four kernel-reduction certificates below exhaust thread creation under a
-- capped address space when elaborated in parallel; elaborate sequentially.
set_option Elab.async false

namespace CirculantCodeEndomorphismRefutation

/-! ## Definitions -/

/-- `codeword n p k j = true` iff neuron `j` fires in the `k`-th codeword
(0-indexed) of the circulant code with support `p` on `n` neurons: the `k`-th
codeword is the block of `p` cyclically consecutive neurons ending at `k`. -/
def codeword (n p : ℕ) (k j : Fin n) : Bool := decide ((k - j : Fin n).val < p)

/-- The element `x_i = ∑_{c_k ∋ i} ρ_{c_k}` of the neural ring
`F_2[C] ≅ (Fin n → ZMod 2)`: its value at codeword `k` is `1` iff neuron `i`
fires in codeword `k`. -/
def neuralX (n p : ℕ) (i : Fin n) : Fin n → ZMod 2 :=
  fun k => if codeword n p k i then 1 else 0

/-- A ring endomorphism `φ` of the neural ring of the circulant code with
support `p` on `n` neurons is a *neural ring endomorphism* if each `φ(x_i)`
lies in `{x_j | j} ∪ {0, 1}`. -/
def IsNRE (n p : ℕ) (φ : (Fin n → ZMod 2) →+* (Fin n → ZMod 2)) : Prop :=
  ∀ i : Fin n, φ (neuralX n p i) = 0 ∨ φ (neuralX n p i) = 1 ∨
    ∃ j : Fin n, φ (neuralX n p i) = neuralX n p j

/-- The unital ring endomorphism `g ↦ g ∘ σ` of `Fin n → ZMod 2` induced by a
code map `σ : Fin n → Fin n`. -/
def pullback {n : ℕ} (σ : Fin n → Fin n) : (Fin n → ZMod 2) →+* (Fin n → ZMod 2) :=
  RingHom.pi fun c => Pi.evalRingHom (fun _ => ZMod 2) (σ c)

/-- Boolean admissibility test for a code map `σ`: for every neuron `i`, the
pulled-back indicator `c ↦ [i ∈ c_{σ c}]` is identically `0`, identically
`1`, or equals the indicator of some `x_j`. -/
def admB (n p : ℕ) (σ : Fin n → Fin n) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all (fun c => !codeword n p (σ c) i) ||
    (List.finRange n).all (fun c => codeword n p (σ c) i) ||
    (List.finRange n).any fun j =>
      (List.finRange n).all fun c => codeword n p (σ c) i == codeword n p c j

/-- Decode a natural number `m < 8 ^ 8` as a map `Fin 8 → Fin 8` through its
base-8 digits (`σ i` is the `i`-th digit). -/
def decode8 (m : ℕ) : Fin 8 → Fin 8 :=
  fun i => ⟨(m / 8 ^ (i : ℕ)) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- Base-8 encoding `∑ i, σ i * 8 ^ i` of a map `σ : Fin 8 → Fin 8`. -/
def encode8 (σ : Fin 8 → Fin 8) : ℕ := ∑ i : Fin 8, (σ i : ℕ) * 8 ^ (i : ℕ)

/-! ## Examples from the paper -/

/-- Paper, Section 5 examples: `n = 4`, `p = 2` gives the code
`{1001, 1100, 0110, 0011}`. -/
example : (List.finRange 4).map (fun k => (List.finRange 4).map (codeword 4 2 k)) =
    [[true, false, false, true], [true, true, false, false],
     [false, true, true, false], [false, false, true, true]] := by decide

/-- `c_p = 1^p 0^(n-p)` for `n = 8`, `p = 4` (0-indexed codeword `3`). -/
example : (List.finRange 8).map (codeword 8 4 3) =
    [true, true, true, true, false, false, false, false] := by decide

/-- The 8 codewords for `n = 8`, `p = 4` are pairwise distinct, so the code
has `n` elements and `Fin 8 → ZMod 2` is its function ring. -/
example : Function.Injective (codeword 8 4) := by decide

/-- Paper: for `n = 6`, `p = 4`, `x_5 = ρ_5 + ρ_6 + ρ_1 + ρ_2`. -/
example : neuralX 6 4 4 = ![1, 1, 0, 0, 1, 1] := by decide

/-- Paper, Remark for `n = 4`, `p = 2`: `x_1 = ρ_1 + ρ_2`. -/
example : neuralX 4 2 0 = ![1, 1, 0, 0] := by decide

/-- Paper, Remark for `n = 4`, `p = 2`: the basis permutation swapping
`ρ_2` and `ρ_3` is not a neural ring endomorphism. -/
example : admB 4 2 ![0, 2, 1, 3] = false := by decide

/-- Paper, Remark for `n = 4`, `p = 2`: there are exactly 36 admissible maps
(the paper's brute-force count `|NRE(C)| = 36`). -/
example : (Finset.univ.filter fun σ : Fin 4 → Fin 4 => admB 4 2 σ = true).card = 36 := by
  decide

/-- `decode8` and `encode8` agree with base-8 digits on a sample. -/
example : decode8 585 = ![1, 1, 1, 1, 0, 0, 0, 0] ∧ encode8 ![1, 1, 1, 1, 0, 0, 0, 0] = 585 := by
  decide

/-! ## Pullback endomorphisms -/

/-- `pullback σ` is precomposition with `σ`. -/
theorem pullback_apply {n : ℕ} (σ : Fin n → Fin n) (g : Fin n → ZMod 2) :
    pullback σ g = g ∘ σ := rfl

/-- Distinct code maps give distinct pullback endomorphisms. -/
theorem pullback_injective {n : ℕ} : Function.Injective (pullback (n := n)) := by
  intro σ τ h
  funext c
  have hc := congrFun (congrArg (fun φ => φ (Pi.single (σ c) 1)) h) c
  simp only [pullback_apply, Function.comp_apply, Pi.single_eq_same] at hc
  by_contra hne
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at hc
  exact one_ne_zero hc

/-- A code map passing the Boolean test `admB` induces a neural ring
endomorphism. -/
theorem isNRE_pullback_of_admB {n p : ℕ} (σ : Fin n → Fin n) (h : admB n p σ = true) :
    IsNRE n p (pullback σ) := by
  intro i
  simp only [admB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    List.any_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rw [pullback_apply]
  rcases h i with (h0 | h1) | ⟨j, -, hj⟩
  · left
    funext c
    simp [neuralX, h0 c]
  · right; left
    funext c
    simp [neuralX, h1 c]
  · right; right
    refine ⟨j, ?_⟩
    funext c
    simp [neuralX, hj c]


/-! ## Certificate: 728 admissible maps for `n = 8`, `p = 4` -/

/-- Codes (base-8 encodings `∑ i, σ i * 8 ^ i`) of admissible maps, block 1 of 4. -/
def codesBlock1 : List ℕ := [
  0, 585, 1170, 1755, 2340, 2925, 3510, 4095, 4680, 6437,
  9360, 10534, 14040, 14631, 18720, 22817, 23400, 26914, 28080, 31011,
  32760, 37440, 39213, 43310, 47407, 51496, 74880, 76086, 80183, 84272,
  112320, 112959, 117048, 149760, 182536, 186633, 187200, 215312, 219409, 223506,
  224640, 248088, 252185, 256282, 260379, 262080, 299520, 301421, 305518, 309615,
  313704, 338294, 342391, 346480, 375167, 379256, 411968, 599040, 600502, 604599,
  608688, 637375, 641464, 674176, 898560, 899583, 903672, 936384, 1198080, 1460288,
  1493064, 1497161, 1497600, 1722496, 1755272, 1759369, 1788048, 1792145, 1796242, 1797120,
  1984704, 2017480, 2021577, 2050256, 2054353, 2058450, 2083032, 2087129, 2091226, 2095323,
  2096640, 2097225, 2100004, 2120481, 2124578, 2128675, 2284297, 2317073, 2321170, 2349849,
  2353946, 2358043, 2359305, 2362212, 2382689, 2386786, 2390883, 2392065, 2394988, 2396160,
  2396745, 2397330, 2397915, 2398500, 2399085, 2399670, 2400255, 2401425, 2403182, 2406105,
  2407279, 2410785, 2411368, 2415465, 2419562, 2420145, 2423659, 2424825, 2434185, 2435958,
  2440055, 2444144, 2448241, 2471625, 2472831, 2476920, 2481017, 2509065, 2509632, 2513729,
  2546505, 2579281, 2583378, 2583945, 2612057, 2616154, 2620251, 2621385, 2696265, 2698166,
  2702263, 2706352, 2710449, 2735039, 2739128, 2743225, 2771840, 2775937, 2808713, 2995785,
  2997247, 3001336, 3005433, 3034048, 3038145, 3070921, 3295305, 3295744, 3299841, 3332617,
  3594825, 3857033, 3889809, 3893906, 3894345, 4119241, 4152017, 4156114, 4184793, 4188890,
  4192987, 4193865]

/-- Codes (base-8 encodings `∑ i, σ i * 8 ^ i`) of admissible maps, block 2 of 4. -/
def codesBlock2 : List ℕ := [
  4194450, 4197668, 4222242, 4226339, 4418834, 4451610, 4455707, 4459876, 4484450, 4488547,
  4492652, 4493970, 4496749, 4517226, 4521323, 4681042, 4713818, 4717915, 4718610, 4722084,
  4746658, 4750755, 4754860, 4756050, 4758957, 4779434, 4783531, 4784130, 4787636, 4788810,
  4791733, 4792320, 4792905, 4793490, 4794075, 4794660, 4795245, 4795830, 4796415, 4798170,
  4799927, 4802850, 4804016, 4807530, 4808113, 4812210, 4816307, 4816890, 4830930, 4832703,
  4836792, 4840889, 4844986, 4868370, 4869504, 4873601, 4877698, 4905810, 4906377, 4910474,
  4943250, 4976026, 4980123, 4980690, 5093010, 5094911, 5099000, 5103097, 5107194, 5131712,
  5135809, 5139906, 5168585, 5172682, 5205458, 5392530, 5393408, 5397505, 5401602, 5430281,
  5434378, 5467154, 5692050, 5692489, 5696586, 5729362, 5991570, 6253778, 6286554, 6290651,
  6291090, 6291675, 6295332, 6324003, 6553371, 6557540, 6586211, 6590316, 6591195, 6594413,
  6618987, 6815579, 6819748, 6848419, 6852524, 6856621, 6881195, 6885300, 6889397, 6890715,
  6893494, 6913971, 7077787, 7077915, 7081956, 7110627, 7114732, 7115355, 7118829, 7143403,
  7147508, 7151605, 7152795, 7155702, 7176179, 7176195, 7180284, 7180875, 7184381, 7185555,
  7188478, 7188480, 7189065, 7189650, 7190235, 7190820, 7191405, 7191990, 7192575, 7194915,
  7196664, 7199595, 7200761, 7204275, 7204858, 7208955, 7227675, 7229376, 7233473, 7237570,
  7241667, 7265115, 7266249, 7270346, 7274443, 7302555, 7303122, 7307219, 7339995, 7489755,
  7491072, 7495169, 7499266, 7503363, 7527945, 7532042, 7536139, 7564818, 7568915, 7601691,
  7789275, 7790153, 7794250, 7798347, 7827026, 7831123, 7863899, 8088795, 8089234, 8093331,
  8126107, 8388315]

/-- Codes (base-8 encodings `∑ i, σ i * 8 ^ i`) of admissible maps, block 3 of 4. -/
def codesBlock3 : List ℕ := [
  8388900, 8651108, 8683884, 8687981, 8688420, 8913316, 8946092, 8950189, 8978868, 8982965,
  8987062, 8987940, 9175524, 9208300, 9212397, 9241076, 9245173, 9249270, 9273852, 9277949,
  9282046, 9286143, 9287460, 9437220, 9469996, 9474093, 9474660, 9502772, 9506869, 9510966,
  9512100, 9535548, 9539645, 9543742, 9547839, 9549540, 9568260, 9572357, 9572940, 9576454,
  9577620, 9580551, 9582300, 9584640, 9585225, 9585810, 9586395, 9586980, 9587565, 9588150,
  9588735, 9588737, 9591660, 9592834, 9596340, 9596931, 9601020, 9601036, 9621513, 9624420,
  9625610, 9629707, 9633812, 9658386, 9661860, 9662483, 9666588, 9695259, 9699300, 9699428,
  9863244, 9883721, 9886500, 9887818, 9891915, 9896020, 9920594, 9924691, 9928796, 9957467,
  9961636, 10158228, 10182802, 10186020, 10186899, 10191004, 10219675, 10223844, 10453212, 10481883,
  10485540, 10486125, 10486564, 10490661, 10523437, 10785645, 11047853, 11080629, 11084726, 11085165,
  11310061, 11342837, 11346934, 11375613, 11379710, 11383807, 11384685, 11571757, 11604533, 11608630,
  11637309, 11641406, 11645503, 11670021, 11674118, 11678215, 11682304, 11684205, 11796525, 11797092,
  11801189, 11833965, 11866741, 11870838, 11871405, 11899517, 11903614, 11907711, 11908845, 11932229,
  11936326, 11940423, 11944512, 11946285, 11960325, 11960908, 11965005, 11969102, 11969685, 11973199,
  11974365, 11977288, 11979045, 11980800, 11981385, 11981970, 11982555, 11983140, 11983725, 11984310,
  11984895, 11985482, 11988405, 11989579, 11993085, 11993684, 11997781, 12018258, 12021165, 12022355,
  12026460, 12030557, 12055131, 12058605, 12059300, 12063397, 12096173, 12255892, 12259989, 12280466,
  12283245, 12284563, 12288668, 12292765, 12317339, 12321508, 12325605, 12358381, 12550876, 12554973,
  12579547, 12582765]

/-- Codes (base-8 encodings `∑ i, σ i * 8 ^ i`) of admissible maps, block 4 of 4. -/
def codesBlock4 : List ℕ := [
  12583350, 12584228, 12588325, 12592422, 12621101, 12625198, 12657974, 12882870, 12883309, 12887406,
  12920182, 13182390, 13444598, 13477374, 13481471, 13481910, 13706294, 13739070, 13743167, 13771782,
  13775879, 13779968, 13781430, 13968502, 14001278, 14005375, 14033990, 14038087, 14042176, 14066766,
  14070863, 14074952, 14079049, 14080950, 14155830, 14156964, 14161061, 14165158, 14193270, 14193837,
  14197934, 14230710, 14263486, 14267583, 14268150, 14296198, 14300295, 14304384, 14305590, 14328974,
  14333071, 14337160, 14341257, 14343030, 14352390, 14353556, 14357070, 14357653, 14361750, 14365847,
  14366430, 14369936, 14371110, 14374033, 14375790, 14376960, 14377545, 14378130, 14378715, 14379300,
  14379885, 14380470, 14381055, 14382227, 14385150, 14386332, 14390429, 14394526, 14415003, 14417910,
  14419172, 14423269, 14427366, 14456045, 14460142, 14492918, 14648540, 14652637, 14656734, 14677211,
  14679990, 14680575, 14681892, 14685989, 14690086, 14694183, 14718765, 14722862, 14726959, 14755638,
  14759735, 14792511, 14980095, 14980973, 14985070, 14989167, 15017846, 15021943, 15054719, 15279615,
  15280054, 15284151, 15316927, 15579135, 15840831, 15873543, 15877632, 15878655, 16103039, 16135751,
  16139840, 16168527, 16172616, 16176713, 16178175, 16365247, 16397959, 16402048, 16430735, 16434824,
  16438921, 16463511, 16467600, 16471697, 16475794, 16477695, 16515135, 16516836, 16520933, 16525030,
  16529127, 16552575, 16553709, 16557806, 16561903, 16590015, 16590582, 16594679, 16627455, 16660167,
  16664256, 16664895, 16692943, 16697032, 16701129, 16702335, 16725719, 16729808, 16733905, 16738002,
  16739775, 16744455, 16746204, 16749135, 16750301, 16753815, 16754398, 16758495, 16762584, 16763175,
  16766681, 16767855, 16770778, 16772535, 16773120, 16773705, 16774290, 16774875, 16775460, 16776045,
  16776630, 16777215]

/-- All 728 codes. -/
def codes : List ℕ := codesBlock1 ++ codesBlock2 ++ codesBlock3 ++ codesBlock4

/-- Every code in block 1 decodes to an admissible map and round-trips through
`encode8` (kernel reduction). -/
theorem codesBlock1_ok :
    (codesBlock1.all fun m => admB 8 4 (decode8 m) && encode8 (decode8 m) == m) = true := by
  decide +kernel

/-- Every code in block 2 decodes to an admissible map and round-trips through
`encode8` (kernel reduction). -/
theorem codesBlock2_ok :
    (codesBlock2.all fun m => admB 8 4 (decode8 m) && encode8 (decode8 m) == m) = true := by
  decide +kernel

/-- Every code in block 3 decodes to an admissible map and round-trips through
`encode8` (kernel reduction). -/
theorem codesBlock3_ok :
    (codesBlock3.all fun m => admB 8 4 (decode8 m) && encode8 (decode8 m) == m) = true := by
  decide +kernel

/-- Every code in block 4 decodes to an admissible map and round-trips through
`encode8` (kernel reduction). -/
theorem codesBlock4_ok :
    (codesBlock4.all fun m => admB 8 4 (decode8 m) && encode8 (decode8 m) == m) = true := by
  decide +kernel

/-- The certificate list has 728 entries. -/
theorem codes_length : codes.length = 728 := by decide +kernel

/-- The certificate list is strictly increasing. -/
theorem codes_isChain : codes.IsChain (· < ·) := by decide +kernel

/-- Every certificate code decodes to an admissible map and round-trips. -/
theorem codes_ok (m : ℕ) (hm : m ∈ codes) :
    admB 8 4 (decode8 m) = true ∧ encode8 (decode8 m) = m := by
  have hall : (codes.all fun m => admB 8 4 (decode8 m) && encode8 (decode8 m) == m) = true := by
    simp only [codes, List.all_append, codesBlock1_ok, codesBlock2_ok, codesBlock3_ok,
      codesBlock4_ok, Bool.and_self]
  have hm' := List.all_eq_true.mp hall m hm
  simpa only [Bool.and_eq_true, beq_iff_eq] using hm'

/-! ## Main results -/

/-- For the circulant code with support `4` on `8` neurons there are at least
728 neural ring endomorphisms (computer enumeration gives exactly 728). -/
theorem le_card_nre_eight_four : 728 ≤ Nat.card {φ // IsNRE 8 4 φ} := by
  haveI : Finite ((Fin 8 → ZMod 2) →+* (Fin 8 → ZMod 2)) := DFunLike.finite _
  have hnodup : codes.Nodup := (List.isChain_iff_pairwise.mp codes_isChain).nodup
  let f : Fin codes.length → {φ // IsNRE 8 4 φ} := fun k =>
    ⟨pullback (decode8 (codes.get k)), isNRE_pullback_of_admB _ (codes_ok _ (List.get_mem _ _)).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hσ : decode8 (codes.get a) = decode8 (codes.get b) :=
      pullback_injective (congrArg Subtype.val hab)
    have hcode : codes.get a = codes.get b := by
      rw [← (codes_ok _ (List.get_mem codes a)).2, ← (codes_ok _ (List.get_mem codes b)).2, hσ]
    exact List.nodup_iff_injective_get.mp hnodup hcode
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, codes_length] at hle

/-- The value `(p^2+p+3) n + p^2 (n/p)!` predicted by Gupta–K N's
Conjecture `conj2` at `n = 8`, `p = 4` is `216`. -/
theorem conj2_prediction_eight_four : (4 ^ 2 + 4 + 3) * 8 + 4 ^ 2 * (8 / 4).factorial = 216 := by
  decide

/-- Counterexample to Gupta–K N, arXiv:2106.06565, Conjecture `conj2` at
`n = 8`, `p = 4` (`3 < 4 < 7`, `4 ∣ 8`): the number of neural ring
endomorphisms exceeds the predicted `(p^2+p+3) n + p^2 (n/p)! = 216`. -/
theorem conj2_prediction_lt_card_eight_four :
    (4 ^ 2 + 4 + 3) * 8 + 4 ^ 2 * (8 / 4).factorial < Nat.card {φ // IsNRE 8 4 φ} := by
  rw [conj2_prediction_eight_four]
  exact lt_of_lt_of_le (by norm_num) le_card_nre_eight_four

/-- Gupta–K N, arXiv:2106.06565, Section 5, Conjecture `conj2` is false:
it is not the case that for every circulant code with support `p` on `n`
neurons with `3 < p < n - 1` and `p ∣ n`,
`|NRE(C)| = (p^2+p+3) n + p^2 (n/p)!`. -/
theorem not_conj2 :
    ¬ ∀ n p : ℕ, 3 < p → p + 1 < n → p ∣ n →
      Nat.card {φ // IsNRE n p φ} = (p ^ 2 + p + 3) * n + p ^ 2 * (n / p).factorial := by
  intro h
  have heq := h 8 4 (by norm_num) (by norm_num) (by norm_num)
  have hlt := conj2_prediction_lt_card_eight_four
  omega

end CirculantCodeEndomorphismRefutation
