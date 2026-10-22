import Sorry.Enumerative.No3APClosedForms

set_option autoImplicit false

namespace A093682

/-- Strict ordered coverage by two members of the block set. -/
def BlockCovered (M : ℕ) (bs : List ℕ) (x : ℕ) : Prop :=
  ∃ p q, BlockMem M bs p ∧ BlockMem M bs q ∧ p < q ∧ q < x ∧ p + x = 2 * q

example : BlockCovered 1 [0] 2 := by
  refine ⟨0, 1, ?_, ?_, by omega, by omega, by omega⟩
  · exact blockMem_mk (M := 1) (bs := [0]) (u := 0) (β := 0) (by decide) ⟨0, binToTernary_zero⟩ (by simp) (by decide)
  · exact blockMem_mk (M := 1) (bs := [0]) (u := 1) (β := 0) (by decide) ⟨1, binToTernary_one⟩ (by simp) (by decide)

/-- The exact finite certificate: ordinary coverage above the threshold in the
first block, and ascending ordinary-or-carry coverage of every missing residue. -/
def BlockCoverageCertificate (M : ℕ) (bs : List ℕ) (h : ℕ) : Prop :=
  (∀ c, h < c → c < M → c ∉ bs →
    ∃ p ∈ bs, ∃ q ∈ bs, p < q ∧ p + c = 2 * q) ∧
  (∀ c, c < M → c ∉ bs →
    ∃ p ∈ bs, ∃ q ∈ bs, p < q ∧ (p + c = 2 * q ∨ p + c + M = 2 * q))

example : BlockCoverageCertificate 1 [0] 0 := by
  constructor <;> intro c
  · intro _ hc hn
    have hc0 : c = 0 := by omega
    exact False.elim (hn (by simp [hc0]))
  · intro hc hn
    have hc0 : c = 0 := by omega
    exact False.elim (hn (by simp [hc0]))

/-- The finite ordered certificate supplies coverage of every missing term above
its threshold, without an AP-free or nonempty-block assumption. -/
theorem blockCovered_of_certificate (M : ℕ) (bs : List ℕ) (h : ℕ)
    (hM : 0 < M) (hlt : ∀ b ∈ bs, b < M)
    (cert : BlockCoverageCertificate M bs h)
    {x : ℕ} (hxg : h < x) (hx : ¬BlockMem M bs x) : BlockCovered M bs x := by
  obtain ⟨s, c, hcM, rfl⟩ : ∃ s c, c < M ∧ M * s + c = x :=
    ⟨x / M, x % M, Nat.mod_lt _ hM, Nat.div_add_mod x M⟩
  have hmod : (M * s + c) % M = c := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hcM]
  have hdiv : (M * s + c) / M = s := by
    rw [Nat.mul_add_div hM, Nat.div_eq_of_lt hcM, Nat.add_zero]
  rw [blockMem_def, hmod, hdiv] at hx
  by_cases hc : c ∈ bs
  · have hs : s ∉ Set.range binToTernary := fun hm => hx ⟨hc, hm⟩
    exact ⟨M * keepOnes s + c, M * capDigits s + c,
      blockMem_mk hM (keepOnes_mem_range s) hc hcM,
      blockMem_mk hM (capDigits_mem_range s) hc hcM,
      block_lt hcM (keepOnes_lt_capDigits hs),
      block_lt hcM (capDigits_lt_of_not_mem_range hs),
      pair_avg_zero (keepOnes_add_self s) (by ring)⟩
  · have ordinary (p q : ℕ) (hp : p ∈ bs) (hq : q ∈ bs)
        (hpq : p < q) (heq : p + c = 2 * q) : BlockCovered M bs (M * s + c) := by
      by_cases hs : s ∈ Set.range binToTernary
      · exact ⟨M * s + p, M * s + q,
          blockMem_mk hM hs hp (hlt _ hp), blockMem_mk hM hs hq (hlt _ hq),
          Nat.add_lt_add_left hpq _, Nat.add_lt_add_left (by omega) _,
          pair_avg_zero (two_mul s).symm heq⟩
      · exact ⟨M * keepOnes s + p, M * capDigits s + q,
          blockMem_mk hM (keepOnes_mem_range s) hp (hlt _ hp),
          blockMem_mk hM (capDigits_mem_range s) hq (hlt _ hq),
          block_lt (hlt _ hp) (keepOnes_lt_capDigits hs),
          block_lt (hlt _ hq) (capDigits_lt_of_not_mem_range hs),
          pair_avg_zero (keepOnes_add_self s) heq⟩
    by_cases hs0 : s = 0
    · subst s
      obtain ⟨p, hp, q, hq, hpq, heq⟩ := cert.1 c (by simpa using hxg) hcM hc
      exact ordinary p q hp hq hpq heq
    · obtain ⟨p, hp, q, hq, hpq, heq | heq⟩ := cert.2 c hcM hc
      · exact ordinary p q hp hq hpq heq
      · obtain ⟨w, rfl⟩ : ∃ w, s = w + 1 := ⟨s - 1, by omega⟩
        by_cases hw : w ∈ Set.range binToTernary
        · exact ⟨M * w + p, M * w + q,
            blockMem_mk hM hw hp (hlt _ hp), blockMem_mk hM hw hq (hlt _ hq),
            Nat.add_lt_add_left hpq _, block_lt (hlt _ hq) (by omega),
            pair_avg_carry (by ring) heq⟩
        · have havg := keepOnes_add_self w
          have hcap := capDigits_lt_of_not_mem_range hw
          exact ⟨M * keepOnes w + p, M * capDigits w + q,
            blockMem_mk hM (keepOnes_mem_range w) hp (hlt _ hp),
            blockMem_mk hM (capDigits_mem_range w) hq (hlt _ hq),
            block_lt (hlt _ hp) (keepOnes_lt_capDigits hw),
            block_lt (hlt _ hq) (by omega), pair_avg_carry (by omega) heq⟩

/-- A natural below four other than two is zero, one, or three. -/
private theorem coverage_high_cases (n : ℕ) (hn : n < 4) (hn2 : n ≠ 2) :
    n = 0 ∨ n = 1 ∨ n = 3 := by
  omega

/-- Arithmetic classification of the two possible ordered high-part pairs in
coverage of the fourth block. -/
private theorem coverage_pair_cases (M u v p q c : ℕ)
    (hpM : p < M) (hqM : q < M) (hcM : c < M)
    (hu : u = 0 ∨ u = 1 ∨ u = 3) (hv : v = 0 ∨ v = 1 ∨ v = 3)
    (hpq : M * u + p < M * v + q)
    (heq : (M * u + p) + (3 * M + c) = 2 * (M * v + q)) :
    (u = 0 ∧ v = 1 ∧ p < q ∧ p + c + M = 2 * q) ∨
      (u = 3 ∧ v = 3 ∧ p < q ∧ p + c = 2 * q) := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    norm_num at * <;> omega

/-- Tests strictly below four blocks force both clauses of the exact certificate. -/
theorem blockCoverageCertificate_of_four_blocks (M : ℕ) (bs : List ℕ) (h : ℕ)
    (hM : 0 < M) (hh : h < M) (hlt : ∀ b ∈ bs, b < M)
    (test : ∀ x, h < x → x < 4 * M → ¬BlockMem M bs x → BlockCovered M bs x) :
    BlockCoverageCertificate M bs h := by
  constructor
  · intro c hhc hcM hc
    have hn : ¬BlockMem M bs c := by
      intro hm
      exact hc (by simpa only [Nat.mod_eq_of_lt hcM] using hm.1)
    obtain ⟨p, q, hp, hq, hpq, hqc, heq⟩ := test c hhc (by omega) hn
    have hpM : p < M := by omega
    have hqM : q < M := by omega
    exact ⟨p, by simpa only [Nat.mod_eq_of_lt hpM] using hp.1,
      q, by simpa only [Nat.mod_eq_of_lt hqM] using hq.1, hpq, heq⟩
  · intro c hcM hc
    have hn : ¬BlockMem M bs (3 * M + c) := by
      intro hm
      exact hc (by simpa [Nat.add_mod, Nat.mod_eq_of_lt hcM] using hm.1)
    obtain ⟨P, Q, hP, hQ, hPQ, hQx, heq⟩ :=
      test (3 * M + c) (by omega) (by omega) hn
    let u := P / M
    let v := Q / M
    let p := P % M
    let q := Q % M
    have hp : p ∈ bs := hP.1
    have hq : q ∈ bs := hQ.1
    have hpM : p < M := hlt p hp
    have hqM : q < M := hlt q hq
    have hPu : M * u + p = P := Nat.div_add_mod P M
    have hQv : M * v + q = Q := Nat.div_add_mod Q M
    have hu4 : u < 4 := (Nat.div_lt_iff_lt_mul hM).mpr (by omega)
    have hv4 : v < 4 := (Nat.div_lt_iff_lt_mul hM).mpr (by omega)
    have hu2 : u ≠ 2 := fun he => two_not_mem_range_binToTernary (he ▸ hP.2)
    have hv2 : v ≠ 2 := fun he => two_not_mem_range_binToTernary (he ▸ hQ.2)
    have cases : (u = 0 ∧ v = 1 ∧ p < q ∧ p + c + M = 2 * q) ∨
        (u = 3 ∧ v = 3 ∧ p < q ∧ p + c = 2 * q) :=
      coverage_pair_cases M u v p q c hpM hqM hcM
        (coverage_high_cases u hu4 hu2) (coverage_high_cases v hv4 hv2)
        (by rw [hPu, hQv]; exact hPQ) (by rw [hPu, hQv]; exact heq)
    rcases cases with ⟨_, _, hpq, he⟩ | ⟨_, _, hpq, he⟩
    · exact ⟨p, hp, q, hq, hpq, Or.inr he⟩
    · exact ⟨p, hp, q, hq, hpq, Or.inl he⟩

/-- Coverage of all missing terms above the threshold is equivalent to the exact
finite ordered residue certificate. -/
theorem blockCovered_iff_certificate (M : ℕ) (bs : List ℕ) (h : ℕ)
    (hM : 0 < M) (hh : h < M) (hlt : ∀ b ∈ bs, b < M) :
    (∀ x, h < x → ¬BlockMem M bs x → BlockCovered M bs x) ↔
      BlockCoverageCertificate M bs h := by
  constructor
  · intro hall
    exact blockCoverageCertificate_of_four_blocks M bs h hM hh hlt
      (fun x hx _ hn => hall x hx hn)
  · intro cert x hx hn
    exact blockCovered_of_certificate M bs h hM hlt cert hx hn

/-- Exact four-block coverage criterion, with strict ordering and literal endpoint
`4 * M`. No AP-free, greedy, nonempty-list, or oracle hypothesis is needed. -/
theorem blockCovered_iff_four_blocks (M : ℕ) (bs : List ℕ) (h : ℕ)
    (hM : 0 < M) (hh : h < M) (hlt : ∀ b ∈ bs, b < M) :
    (∀ x, h < x → ¬BlockMem M bs x → BlockCovered M bs x) ↔
      (∀ x, h < x → x < 4 * M → ¬BlockMem M bs x → BlockCovered M bs x) := by
  constructor
  · intro hall x hx _ hn
    exact hall x hx hn
  · intro test
    exact (blockCovered_iff_certificate M bs h hM hh hlt).mpr
      (blockCoverageCertificate_of_four_blocks M bs h hM hh hlt test)

/-- A concrete simultaneous model of the hypotheses and certificate, including
positive modulus and a genuinely inhabited block and threshold domain. -/
example : 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ (∀ b ∈ [0], b < (1 : ℕ)) ∧
    BlockCoverageCertificate 1 [0] 0 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simp
  · constructor <;> intro c
    · intro _ hc hn
      have hc0 : c = 0 := by omega
      exact False.elim (hn (by simp [hc0]))
    · intro hc hn
      have hc0 : c = 0 := by omega
      exact False.elim (hn (by simp [hc0]))

end A093682
