import Erdos.Erdos132.KnownFivePoint
import Erdos.Erdos132.KnownSixPointGeometry
import Erdos.Erdos132.KnownSixPointCombinatorics

set_option autoImplicit false

open scoped BigOperators

namespace Erdos132.KnownSixPoint
open Erdos132.TwoInteriorCircle

private theorem no_triangle (X : Finset Plane) (hX : 5 ≤ X.card)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hallowed : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = a ∨ dist x y = b)
    (x y z : Plane) (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ (dist x y = dist x z ∧ dist x z = dist y z) := by
  classical
  have hsub : {x,y,z} ⊆ X := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hsmall : ({x,y,z} : Finset Plane).card ≤ 5 := by
    have hle : ({x,y,z} : Finset Plane).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨T, hT₁, hT₂, hT⟩ := Finset.exists_subsuperset_card_eq hsub hsmall hX
  have hxT : x ∈ T := hT₁ (by simp)
  have hyT : y ∈ T := hT₁ (by simp)
  have hzT : z ∈ T := hT₁ (by simp)
  have hallowT : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → dist u v = a ∨ dist u v = b :=
    fun u hu v hv huv => hallowed u (hT₂ hu) v (hT₂ hv) huv
  intro he
  rcases hallowed x hx y hy hxy with h | h
  · exact KnownFivePoint.no_equilateral_triangle_of_two_distances T hT a b ha hb hab
      hallowT x y z hxT hyT hzT hxy hxz hyz ⟨h, he.1.symm.trans h, he.2.symm.trans (he.1.symm.trans h)⟩
  · exact KnownFivePoint.no_equilateral_triangle_of_two_distances T hT b a hb ha hab.symm
      (fun u hu v hv huv => (hallowT u hu v hv huv).symm)
      x y z hxT hyT hzT hxy hxz hyz ⟨h, he.1.symm.trans h, he.2.symm.trans (he.1.symm.trans h)⟩

private theorem color_triangle_free (X : Finset Plane) (hX : 5 ≤ X.card)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hallowed : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = a ∨ dist x y = b)
    {n : ℕ} (p : Fin n → Plane) (hp : Function.Injective p) (hmem : ∀ i, p i ∈ X) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ (decide (dist (p i) (p j) = a) = decide (dist (p i) (p k) = a) ∧
        decide (dist (p i) (p k) = a) = decide (dist (p j) (p k) = a)) := by
  classical
  intro i j k hij hik hjk hc
  have hij' := hallowed (p i) (hmem i) (p j) (hmem j) (hp.ne hij)
  have hik' := hallowed (p i) (hmem i) (p k) (hmem k) (hp.ne hik)
  have hjk' := hallowed (p j) (hmem j) (p k) (hmem k) (hp.ne hjk)
  have he : dist (p i) (p j) = dist (p i) (p k) ∧
      dist (p i) (p k) = dist (p j) (p k) := by
    by_cases h : dist (p i) (p j) = a
    · have h' : dist (p i) (p k) = a := by simpa [h] using hc.1.symm
      have h'' : dist (p j) (p k) = a := by simpa [h'] using hc.2.symm
      exact ⟨h.trans h'.symm, h'.trans h''.symm⟩
    · have h' : dist (p i) (p k) ≠ a := by simpa [h] using hc.1.symm
      have h'' : dist (p j) (p k) ≠ a := by simpa [h'] using hc.2.symm
      exact ⟨(hij'.resolve_left h).trans (hik'.resolve_left h').symm,
        (hik'.resolve_left h').trans (hjk'.resolve_left h'').symm⟩
  exact no_triangle X hX a b ha hb hab hallowed (p i) (p j) (p k)
    (hmem i) (hmem j) (hmem k) (hp.ne hij) (hp.ne hik) (hp.ne hjk) he

private theorem no_two_allowed (X : Finset Plane) (hX : X.card = 6)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ¬ (∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = a ∨ dist x y = b) := by
  classical
  intro hallowed
  let e := (Finset.equivFinOfCardEq hX).symm
  let p : Fin 6 → Plane := fun i => (e i).val
  have hp : Function.Injective p := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ i, p i ∈ X := fun i => (e i).property
  let c : Fin 6 → Fin 6 → Bool := fun i j => decide (dist (p i) (p j) = a)
  have hs : ∀ i j, c i j = c j i := by intro i j; simp [c, dist_comm]
  obtain ⟨i,j,k,hij,hik,hjk,hc⟩ :=
    KnownSixPointCombinatorics.exists_monochromatic_triangle_six c hs
  exact color_triangle_free X (by omega) a b ha hb hab hallowed p hp hmem
    i j k hij hik hjk hc

private theorem exists_cycle (X : Finset Plane) (hX : X.card = 5)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hallowed : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = a ∨ dist x y = b) :
    ∃ p : Fin 5 → Plane, Function.Injective p ∧ (∀ i, p i ∈ X) ∧
      (∀ x ∈ X, x ∈ Set.range p) ∧
      (∀ i, dist (p i) (p (i + 1)) = a) ∧
      (∀ i, dist (p i) (p (i + 2)) = b) := by
  classical
  let e := (Finset.equivFinOfCardEq hX).symm
  let q : Fin 5 → Plane := fun i => (e i).val
  have hq : Function.Injective q := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ i, q i ∈ X := fun i => (e i).property
  let c : Fin 5 → Fin 5 → Bool := fun i j => decide (dist (q i) (q j) = a)
  have hs : ∀ i j, c i j = c j i := by intro i j; simp [c, dist_comm]
  have ht := color_triangle_free X (by omega) a b ha hb hab hallowed q hq hmem
  obtain ⟨f,hf,hside,hstar⟩ := KnownSixPointCombinatorics.cycle_of_triangle_free c hs ht
  have hsurj : Function.Surjective f := (Finite.injective_iff_surjective).mp hf
  refine ⟨q ∘ f, hq.comp hf, fun i => hmem (f i), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := hsurj ((Finset.equivFinOfCardEq hX) ⟨x,hx⟩)
    refine ⟨i, ?_⟩
    simp [q, hi, e]
  · intro i
    simpa [c, Function.comp_def] using hside i
  · intro i
    have hn : dist (q (f i)) (q (f (i + 2))) ≠ a := by simpa [c] using hstar i
    have hne : ∀ i : Fin 5, i ≠ i + 2 := by decide
    exact (hallowed _ (hmem _) _ (hmem _) (hq.ne (hf.ne (hne i)))).resolve_left hn


private theorem positive_pair (X : Finset Plane) (e : Sym2 Plane) (he : e ∈ pairs X) :
    0 < pairDist e := by
  induction e using Sym2.ind with
  | _ x y => exact dist_pos.mpr ((mk_mem_pairs X x y).mp he).2.2

private theorem positive_multiplicity (X : Finset Plane) (d : ℝ)
    (hd : d ∈ (pairs X).image pairDist) : 1 ≤ multiplicity X d := by
  classical
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he,rfl⟩⟩

private theorem counts_two (X : Finset Plane) (a b : ℝ) (hab : a ≠ b) :
    multiplicity X a + multiplicity X b =
      ((pairs X).filter fun e => pairDist e = a ∨ pairDist e = b).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter (pairs X) {a,b} pairDist
  simpa [TwoInteriorCircle.multiplicity, hab] using h

private theorem counts_total (X : Finset Plane) (a b : ℝ) (hab : a ≠ b) :
    multiplicity X a + multiplicity X b +
      ((pairs X).filter fun e => pairDist e ≠ a ∧ pairDist e ≠ b).card =
      (pairs X).card := by
  classical
  rw [counts_two X a b hab]
  simpa only [not_or] using
    (pairs X).card_filter_add_card_filter_not (fun e => pairDist e = a ∨ pairDist e = b)

private theorem multiplicity_insert (P : Finset Plane) (x : Plane) (hx : x ∉ P) (d : ℝ) :
    multiplicity (insert x P) d = multiplicity P d +
      (P.filter fun y => dist x y = d).card := by
  classical
  let I := P.image fun y => s(x,y)
  have hinj : Function.Injective (fun y : Plane => s(x,y)) := by
    intro y z he
    rcases Sym2.eq_iff.mp he with ⟨_,h⟩ | ⟨h₁,h₂⟩
    · exact h
    · exact h₂.trans h₁
  have hdis : Disjoint (pairs P) I := by
    apply Finset.disjoint_left.mpr
    intro e he hi
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hi
    exact hx ((mk_mem_pairs P x y).mp he).1
  have heq : pairs (insert x P) = pairs P ∪ I := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mk_mem_pairs, Finset.mem_insert, Finset.mem_union, I,
        Finset.mem_image, Sym2.eq_iff]
      aesop
  rw [TwoInteriorCircle.multiplicity, heq, Finset.filter_union,
    Finset.card_union_of_disjoint (hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  change multiplicity P d + (I.filter fun e => pairDist e = d).card = _
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
  rfl

private theorem cycle_lower (X : Finset Plane) (p : Fin 5 → Plane)
    (hp : Function.Injective p) (hmem : ∀ i, p i ∈ X) (k : Fin 5)
    (hk : k = 1 ∨ k = 2) (d : ℝ) (hd : ∀ i, dist (p i) (p (i+k)) = d) :
    5 ≤ multiplicity X d := by
  classical
  have hne : ∀ i : Fin 5, i ≠ i+k := by
    rcases hk with rfl | rfl <;> decide
  have hswap : ∀ i j : Fin 5, ¬ (i = j+k ∧ i+k = j) := by
    rcases hk with rfl | rfl <;> decide
  let f : Fin 5 → Sym2 Plane := fun i => s(p i,p (i+k))
  have hf : Function.Injective f := by
    intro i j he
    rcases Sym2.eq_iff.mp he with ⟨h₁,_⟩ | ⟨h₁,h₂⟩
    · exact hp h₁
    · exact False.elim (hswap i j ⟨hp h₁,hp h₂⟩)
  have hsub : Finset.univ.image f ⊆ (pairs X).filter (fun e => pairDist e = d) := by
    intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨(mk_mem_pairs X (p i) (p (i+k))).mpr ⟨hmem i,hmem _, hp.ne (hne i)⟩,hd i⟩
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin, TwoInteriorCircle.multiplicity] using hcard

private theorem cycle_counts (X : Finset Plane) (hX : X.card = 5)
    (p : Fin 5 → Plane) (hp : Function.Injective p) (hmem : ∀ i, p i ∈ X)
    (a b : ℝ) (hab : a ≠ b)
    (hallowed : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = a ∨ dist x y = b)
    (hside : ∀ i, dist (p i) (p (i+1)) = a)
    (hstar : ∀ i, dist (p i) (p (i+2)) = b) :
    multiplicity X a = 5 ∧ multiplicity X b = 5 := by
  classical
  have hA := cycle_lower X p hp hmem 1 (Or.inl rfl) a hside
  have hB := cycle_lower X p hp hmem 2 (Or.inr rfl) b hstar
  have hrem : (pairs X).filter (fun e => pairDist e ≠ a ∧ pairDist e ≠ b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨he,hna,hnb⟩ := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx,hy,hxy⟩ := (mk_mem_pairs X x y).mp he
      exact (hallowed x hx y hy hxy).elim hna hnb
  have htotal := counts_total X a b hab
  rw [hrem, Finset.card_empty, card_pairs, hX] at htotal
  norm_num [Nat.choose] at htotal
  omega


private theorem dist_mem (X : Finset Plane) (x y : Plane)
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    dist x y ∈ (pairs X).image pairDist := by
  classical
  exact Finset.mem_image.mpr ⟨s(x,y), (mk_mem_pairs X x y).mpr ⟨hx,hy,hxy⟩,rfl⟩

private theorem positive_distance (X : Finset Plane) (d : ℝ)
    (hd : d ∈ (pairs X).image pairDist) : 0 < d := by
  classical
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
  exact positive_pair X e he

private theorem three_distances (X : Finset Plane) (hX : X.card = 6) :
    3 ≤ ((pairs X).image pairDist).card := by
  classical
  let D := (pairs X).image pairDist
  have hpc : (pairs X).card = 15 := by rw [card_pairs, hX]; decide
  have hne : D.Nonempty := (Finset.card_pos.mp (by omega : 0 < (pairs X).card)).image _
  obtain ⟨a,ha⟩ := hne
  have hapos := positive_distance X a ha
  by_contra hthree
  change ¬ 3 ≤ D.card at hthree
  have hD : D.card ≤ 2 := by omega
  by_cases htwo : 1 < D.card
  · obtain ⟨a',ha',b',hb',hab'⟩ := Finset.one_lt_card.mp htwo
    have hsub : {a',b'} ⊆ D := by
      intro d hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact ha'
      · exact hb'
    have hcard : ({a',b'} : Finset ℝ).card = 2 := by simp [hab']
    have heq : {a',b'} = D := Finset.eq_of_subset_of_card_le hsub (by omega)
    apply no_two_allowed X hX a' b' (positive_distance X a' ha')
      (positive_distance X b' hb') hab'
    intro x hx y hy hxy
    have hm := dist_mem X x y hx hy hxy
    change dist x y ∈ D at hm
    rw [← heq] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  · apply no_two_allowed X hX a (a+1) hapos (by linarith) (by linarith)
    intro x hx y hy hxy
    left
    exact Finset.card_le_one.mp (by omega : D.card ≤ 1) _
      (dist_mem X x y hx hy hxy) a ha

private theorem large_classes (X : Finset Plane) (hX : X.card = 6)
    (hone : ∀ a ∈ (pairs X).image pairDist, ∀ b ∈ (pairs X).image pairDist,
      multiplicity X a ≤ 6 → multiplicity X b ≤ 6 → a = b) :
    ∃ a b : ℝ, a ≠ b ∧ 0 < a ∧ 0 < b ∧
      multiplicity X a = 7 ∧ multiplicity X b = 7 ∧
      ((pairs X).filter fun e => pairDist e ≠ a ∧ pairDist e ≠ b).card = 1 := by
  classical
  let D := (pairs X).image pairDist
  let G := D.filter fun d => multiplicity X d ≤ 6
  let B := D.filter fun d => ¬ multiplicity X d ≤ 6
  have hG : G.card ≤ 1 := Finset.card_le_one.mpr (by
    intro a ha b hb
    exact hone a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
  have hpartition : G.card + B.card = D.card :=
    D.card_filter_add_card_filter_not (fun d => multiplicity X d ≤ 6)
  have hD : 3 ≤ D.card := three_distances X hX
  have hB : 1 < B.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hB
  have haD : a ∈ D := (Finset.mem_filter.mp ha).1
  have hbD : b ∈ D := (Finset.mem_filter.mp hb).1
  have hA : 7 ≤ multiplicity X a := by
    have h := (Finset.mem_filter.mp ha).2
    omega
  have hB' : 7 ≤ multiplicity X b := by
    have h := (Finset.mem_filter.mp hb).2
    omega
  let R := (pairs X).filter fun e => pairDist e ≠ a ∧ pairDist e ≠ b
  have hR : 0 < R.card := by
    by_contra hzero
    have hempty : R = ∅ := Finset.card_eq_zero.mp (by omega)
    have hsub : D ⊆ {a,b} := by
      intro d hd
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
      by_cases h₁ : pairDist e = a
      · simp [h₁]
      by_cases h₂ : pairDist e = b
      · simp [h₂]
      have hm : e ∈ R := Finset.mem_filter.mpr ⟨he,h₁,h₂⟩
      rw [hempty] at hm
      exact False.elim (Finset.notMem_empty e hm)
    have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  have htotal := counts_total X a b hab
  have hpc : (pairs X).card = 15 := by rw [card_pairs,hX]; decide
  change multiplicity X a + multiplicity X b + R.card = _ at htotal
  rw [hpc] at htotal
  have hAeq : multiplicity X a = 7 := by omega
  have hBeq : multiplicity X b = 7 := by omega
  have hReq : R.card = 1 := by omega
  exact ⟨a,b,hab,positive_distance X a haD,positive_distance X b hbD,hAeq,hBeq,hReq⟩


private theorem no_large_classes (X : Finset Plane) (hX : X.card = 6)
    (a b : ℝ) (hab : a ≠ b) (ha : 0 < a) (hb : 0 < b)
    (hA : multiplicity X a = 7) (hB : multiplicity X b = 7)
    (hR : ((pairs X).filter fun e => pairDist e ≠ a ∧ pairDist e ≠ b).card = 1) : False := by
  classical
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hR
  induction e using Sym2.ind with
  | _ x y =>
    have hxyR : s(x,y) ∈ (pairs X).filter (fun e => pairDist e ≠ a ∧ pairDist e ≠ b) := by
      rw [he]
      exact Finset.mem_singleton_self _
    have hxyX := (Finset.mem_filter.mp hxyR).1
    obtain ⟨hx,hy,hxy⟩ := (mk_mem_pairs X x y).mp hxyX
    let P := X.erase x
    have hxP : x ∉ P := Finset.notMem_erase _ _
    have hP : P.card = 5 := by
      dsimp only [P]
      rw [Finset.card_erase_of_mem hx, hX]
    have hXP : X = insert x P := (Finset.insert_erase hx).symm
    have hallowed : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → dist u v = a ∨ dist u v = b := by
      intro u hu v hv huv
      by_cases h₁ : dist u v = a
      · exact Or.inl h₁
      by_cases h₂ : dist u v = b
      · exact Or.inr h₂
      have huvR : s(u,v) ∈ (pairs X).filter (fun e => pairDist e ≠ a ∧ pairDist e ≠ b) :=
        Finset.mem_filter.mpr ⟨(mk_mem_pairs X u v).mpr
          ⟨Finset.mem_of_mem_erase hu,Finset.mem_of_mem_erase hv,huv⟩,h₁,h₂⟩
      rw [he, Finset.mem_singleton] at huvR
      rcases Sym2.eq_iff.mp huvR with ⟨hux,_⟩ | ⟨_,hvx⟩
      · exact False.elim ((Finset.mem_erase.mp hu).1 hux)
      · exact False.elim ((Finset.mem_erase.mp hv).1 hvx)
    obtain ⟨p,hp,hmem,hcover,hside,hstar⟩ := exists_cycle P hP a b ha hb hab hallowed
    obtain ⟨hPA,hPB⟩ := cycle_counts P hP p hp hmem a b hab hallowed hside hstar
    have hIA := multiplicity_insert P x hxP a
    have hIB := multiplicity_insert P x hxP b
    rw [← hXP, hA, hPA] at hIA
    rw [← hXP, hB, hPB] at hIB
    have hradA : (P.filter fun z => dist x z = a).card = 2 := by omega
    have hradB : (P.filter fun z => dist x z = b).card = 2 := by omega
    have himage : Finset.univ.image p = P := by
      ext z
      constructor
      · intro hz
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
        exact hmem i
      · intro hz
        obtain ⟨i,rfl⟩ := hcover z hz
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hrad (d : ℝ) :
        (Finset.univ.filter (fun i : Fin 5 => dist x (p i) = d)).card =
          (P.filter fun z => dist x z = d).card := by
      rw [← himage, Finset.filter_image, Finset.card_image_of_injective _ hp]
    have hout : x ∉ Set.range p := by
      rintro ⟨i,rfl⟩
      exact hxP (hmem i)
    exact KnownSixPointGeometry.no_two_two_extension_of_five_cycle_metric
      p hp a b ha hb hab hside hstar x hout
      ⟨(hrad a).trans hradA,(hrad b).trans hradB⟩

/-- Every six-point planar set has two distinct positive occurring distances,
    each realized by at least one and at most six unordered pairs. -/
theorem two_good_distances (X : Finset Plane) (hX : X.card = 6) :
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ 0 < d₁ ∧ 0 < d₂ ∧
      (∃ e₁ ∈ pairs X, pairDist e₁ = d₁) ∧
      (∃ e₂ ∈ pairs X, pairDist e₂ = d₂) ∧
      1 ≤ multiplicity X d₁ ∧ multiplicity X d₁ ≤ 6 ∧
      1 ≤ multiplicity X d₂ ∧ multiplicity X d₂ ≤ 6 := by
  classical
  by_contra hfail
  have hone : ∀ a ∈ (pairs X).image pairDist, ∀ b ∈ (pairs X).image pairDist,
      multiplicity X a ≤ 6 → multiplicity X b ≤ 6 → a = b := by
    intro a ha b hb hA hB
    by_contra hab
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp ha
    obtain ⟨f,hf,hfq⟩ := Finset.mem_image.mp hb
    exact hfail ⟨a,b,hab,positive_distance X a ha,positive_distance X b hb,
      ⟨e,he,heq⟩,⟨f,hf,hfq⟩,positive_multiplicity X a ha,hA,
      positive_multiplicity X b hb,hB⟩
  obtain ⟨a,b,hab,ha,hb,hA,hB,hR⟩ := large_classes X hX hone
  exact no_large_classes X hX a b hab ha hb hA hB hR

example : ∃ X : Finset Plane, X.card = 6 ∧
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ 0 < d₁ ∧ 0 < d₂ ∧
      (∃ e₁ ∈ pairs X, pairDist e₁ = d₁) ∧
      (∃ e₂ ∈ pairs X, pairDist e₂ = d₂) ∧
      1 ≤ multiplicity X d₁ ∧ multiplicity X d₁ ≤ 6 ∧
      1 ≤ multiplicity X d₂ ∧ multiplicity X d₂ ≤ 6 := by
  classical
  let p : Fin 6 → Plane := fun i => EuclideanSpace.single 0 (i.val : ℝ)
  have hp : Function.Injective p := by
    intro i j hij
    have hc := congrArg (fun z : Plane => z 0) hij
    simp only [p, PiLp.single_apply, ite_true] at hc
    exact Fin.ext (Nat.cast_injective hc)
  let X := Finset.univ.image p
  have hX : X.card = 6 := by
    rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
  exact ⟨X,hX,two_good_distances X hX⟩

end Erdos132.KnownSixPoint
