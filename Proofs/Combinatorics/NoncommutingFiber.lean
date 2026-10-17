import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic

/-!
# A cardinality bound for three noncommuting coordinate maps

Points of `ℤ³` are represented by the right-associated product `ℤ × (ℤ × ℤ)`.
The sum in `mixedSum` is ordinary coordinatewise pointwise Finset addition.

The proof first derives finite three-coordinate Loomis--Whitney from two
Cauchy--Schwarz inequalities for triangle indicators. For three coordinate-plane
sets, each sum fiber is encoded injectively by three free coordinates. Its pair
projections inject into the three plane sets, so another application of
Loomis--Whitney bounds its squared cardinality. The exact fiber partition and
Cauchy--Schwarz then give a lower bound for the squared sumset cardinality.
Applying ordinary Loomis--Whitney to the original set finishes the argument.
No nonemptiness assumption is required: the zero product case is handled before
cancelling. In particular, this is a constant-one cardinality bound, not an
asymptotic factor-eight claim.
-/

set_option autoImplicit false

namespace NoncommutingFiber

private theorem triangle_bound {α β γ : Type*}
    (I : Finset α) (J : Finset β) (K : Finset γ)
    (f : α → β → ℕ) (g : α → γ → ℕ) (h : β → γ → ℕ) :
    (∑ jk ∈ J ×ˢ K, h jk.1 jk.2 * (∑ i ∈ I, f i jk.1 * g i jk.2)) ^ 2 ≤
      (∑ ij ∈ I ×ˢ J, f ij.1 ij.2 ^ 2) *
      (∑ ik ∈ I ×ˢ K, g ik.1 ik.2 ^ 2) *
      (∑ jk ∈ J ×ˢ K, h jk.1 jk.2 ^ 2) := by
  have inner (j : β) (k : γ) := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => f i j) (fun i => g i k)
  have outer := Finset.sum_mul_sq_le_sq_mul_sq (J ×ˢ K)
    (fun jk => h jk.1 jk.2) (fun jk => ∑ i ∈ I, f i jk.1 * g i jk.2)
  have summed : (∑ jk ∈ J ×ˢ K, (∑ i ∈ I, f i jk.1 * g i jk.2) ^ 2) ≤
      (∑ ij ∈ I ×ˢ J, f ij.1 ij.2 ^ 2) *
      (∑ ik ∈ I ×ˢ K, g ik.1 ik.2 ^ 2) := by
    calc
      _ ≤ ∑ jk ∈ J ×ˢ K, (∑ i ∈ I, f i jk.1 ^ 2) *
          (∑ i ∈ I, g i jk.2 ^ 2) := Finset.sum_le_sum (fun jk _ => inner jk.1 jk.2)
      _ = _ := by
        simp only [Finset.sum_product]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        congr 1
        · exact Finset.sum_comm
        · exact Finset.sum_comm
  calc
    _ ≤ _ := outer
    _ ≤ (∑ jk ∈ J ×ˢ K, h jk.1 jk.2 ^ 2) *
        ((∑ ij ∈ I ×ˢ J, f ij.1 ij.2 ^ 2) *
        (∑ ik ∈ I ×ˢ K, g ik.1 ik.2 ^ 2)) := Nat.mul_le_mul_left _ summed
    _ = _ := by ring

private theorem indicator_sum {α : Type*} [DecidableEq α]
    (S P : Finset α) (hP : P ⊆ S) :
    (∑ x ∈ S, if x ∈ P then (1 : ℕ) else 0) = P.card := by
  have hf : S.filter (fun x => x ∈ P) = P := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hP h, h⟩⟩
  rw [← Finset.sum_filter, hf]
  simp

/-- The finite three-coordinate Loomis--Whitney inequality, counting each projection once. -/
theorem card_sq_le_pair_projections {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (B : Finset (α × β × γ)) :
    B.card ^ 2 ≤ (B.image (fun t => (t.1, t.2.1))).card *
      (B.image (fun t => (t.1, t.2.2))).card *
      (B.image (fun t => (t.2.1, t.2.2))).card := by
  let I := B.image (fun t => t.1)
  let J := B.image (fun t => t.2.1)
  let K := B.image (fun t => t.2.2)
  let P := B.image (fun t => (t.1, t.2.1))
  let Q := B.image (fun t => (t.1, t.2.2))
  let R := B.image (fun t => (t.2.1, t.2.2))
  have hP : P ⊆ I ×ˢ J := by
    rintro _ hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
  have hQ : Q ⊆ I ×ˢ K := by
    rintro _ hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
  have hR : R ⊆ J ×ˢ K := by
    rintro _ hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
  let C := (I ×ˢ (J ×ˢ K)).filter (fun t =>
    (t.1, t.2.1) ∈ P ∧ (t.1, t.2.2) ∈ Q ∧ (t.2.1, t.2.2) ∈ R)
  have hBC : B ⊆ C := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ ht, Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩⟩,
      Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht,
      Finset.mem_image_of_mem _ ht⟩
  have hcount : C.card = ∑ jk ∈ J ×ˢ K,
      (if jk ∈ R then 1 else 0) *
      (∑ i ∈ I, (if (i, jk.1) ∈ P then 1 else 0) *
        (if (i, jk.2) ∈ Q then 1 else 0)) := by
    simp only [C, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product,
      Finset.mul_sum]
    rw [Finset.sum_comm (s := I) (t := J)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm (s := I) (t := K)]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  have ht := triangle_bound I J K
    (fun i j => if (i,j) ∈ P then 1 else 0)
    (fun i k => if (i,k) ∈ Q then 1 else 0)
    (fun j k => if (j,k) ∈ R then 1 else 0)
  have hp : (∑ ij ∈ I ×ˢ J, (if ij ∈ P then (1 : ℕ) else 0) ^ 2) = P.card := by
    simpa using indicator_sum (I ×ˢ J) P hP
  have hq : (∑ ik ∈ I ×ˢ K, (if ik ∈ Q then (1 : ℕ) else 0) ^ 2) = Q.card := by
    simpa using indicator_sum (I ×ˢ K) Q hQ
  have hr : (∑ jk ∈ J ×ˢ K, (if jk ∈ R then (1 : ℕ) else 0) ^ 2) = R.card := by
    simpa using indicator_sum (J ×ˢ K) R hR
  rw [← hcount, hp, hq, hr] at ht
  exact (Nat.pow_le_pow_left (Finset.card_le_card hBC) 2).trans ht

/-- Sum of three points in the coordinate planes, supplied as their two free coordinates. -/
private def planeSum (t : (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ)) : ℤ × ℤ × ℤ :=
  (t.1.1 + t.2.1.1, t.1.2 + t.2.2.1, t.2.1.2 + t.2.2.2)

example : planeSum ((1,2),(3,4),(5,6)) = (4,7,10) := rfl

private theorem plane_fiber_bound (P Q R : Finset (ℤ × ℤ)) (s : ℤ × ℤ × ℤ) :
    ((P ×ˢ (Q ×ˢ R)).filter (fun t => planeSum t = s)).card ^ 2 ≤
      P.card * Q.card * R.card := by
  let E := (P ×ˢ (Q ×ˢ R)).filter (fun t => planeSum t = s)
  let encode := fun t : (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) =>
    (t.1.1, t.1.2, t.2.1.2)
  let F := E.image encode
  have hinj : Set.InjOn encode E := by
    rintro ⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩⟩ hx ⟨⟨a',b'⟩,⟨c',d'⟩,⟨e',f'⟩⟩ hy he
    have hsx := (Finset.mem_filter.mp hx).2
    have hsy := (Finset.mem_filter.mp hy).2
    simp only [planeSum, Prod.ext_iff] at hsx hsy
    simp only [encode, Prod.mk.injEq] at he ⊢
    omega
  have hcard : F.card = E.card := Finset.card_image_of_injOn hinj
  have hcoords (u : ℤ × ℤ × ℤ) (hu : u ∈ F) :
      (u.1,u.2.1) ∈ P ∧ (s.1-u.1,u.2.2) ∈ Q ∧
        (s.2.1-u.2.1,s.2.2-u.2.2) ∈ R := by
    obtain ⟨⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩⟩, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hm, hs⟩ := Finset.mem_filter.mp ht
    obtain ⟨hp,hq,hr⟩ := by simpa only [Finset.mem_product] using hm
    simp only [planeSum, Prod.ext_iff] at hs
    have hc : s.1 - a = c := by omega
    have he : s.2.1 - b = e := by omega
    have hf : s.2.2 - d = f := by omega
    simpa only [encode, hc, he, hf] using And.intro hp (And.intro hq hr)
  have hab : (F.image (fun u => (u.1,u.2.1))).card ≤ P.card := by
    apply Finset.card_le_card
    rintro _ hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact (hcoords u hu).1
  have had : (F.image (fun u => (u.1,u.2.2))).card ≤ Q.card := by
    apply Finset.card_le_card_of_injOn (fun v : ℤ × ℤ => (s.1-v.1,v.2))
    · rintro _ hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact (hcoords u hu).2.1
    · rintro ⟨a,d⟩ _ ⟨a',d'⟩ _ he
      simp only [Prod.mk.injEq] at he ⊢
      omega
  have hbd : (F.image (fun u => (u.2.1,u.2.2))).card ≤ R.card := by
    apply Finset.card_le_card_of_injOn (fun v : ℤ × ℤ => (s.2.1-v.1,s.2.2-v.2))
    · rintro _ hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact (hcoords u hu).2.2
    · rintro ⟨b,d⟩ _ ⟨b',d'⟩ _ he
      simp only [Prod.mk.injEq] at he ⊢
      omega
  have hlw := card_sq_le_pair_projections F
  rw [hcard] at hlw
  exact hlw.trans (Nat.mul_le_mul (Nat.mul_le_mul hab had) hbd)

private theorem plane_sum_card_sq (P Q R : Finset (ℤ × ℤ)) :
    P.card * Q.card * R.card ≤ ((P ×ˢ (Q ×ˢ R)).image planeSum).card ^ 2 := by
  let E := P ×ˢ (Q ×ˢ R)
  let S := E.image planeSum
  let k := P.card * Q.card * R.card
  let n := fun s => (E.filter (fun t => planeSum t = s)).card
  have hpartition : k = ∑ s ∈ S, n s := by
    have h := Finset.card_eq_sum_card_image planeSum E
    simpa only [E, Finset.card_product, k, Nat.mul_assoc] using h
  have hsum : (∑ s ∈ S, n s ^ 2) ≤ S.card * k := by
    calc
      _ ≤ ∑ _s ∈ S, k := Finset.sum_le_sum (fun s _ => plane_fiber_bound P Q R s)
      _ = _ := by simp
  have hcs : k ^ 2 ≤ S.card * (∑ s ∈ S, n s ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℕ)) n
    simpa only [one_mul, one_pow, Finset.sum_const, smul_eq_mul,
      mul_one, ← hpartition] using h
  have hcancel : k * k ≤ S.card ^ 2 * k := by
    calc
      _ = k ^ 2 := by ring
      _ ≤ S.card * (∑ s ∈ S, n s ^ 2) := hcs
      _ ≤ S.card * (S.card * k) := Nat.mul_le_mul_left _ hsum
      _ = _ := by ring
  by_cases hk : k = 0
  · simpa only [k, hk] using (Nat.zero_le (S.card ^ 2))
  · exact Nat.le_of_mul_le_mul_right hcancel (Nat.pos_of_ne_zero hk)

/-- The first integer-coordinate map: `(x,y,z) ↦ (y,-x,0)`. -/
def L0 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.2.1, -t.1, 0)

/-- The second integer-coordinate map: `(x,y,z) ↦ (z,0,-x)`. -/
def L1 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.2.2, 0, -t.1)

/-- The third integer-coordinate map: `(x,y,z) ↦ (0,z,-y)`. -/
def L2 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (0, t.2.2, -t.2.1)

example : L0 (1,2,3) = (2,-1,0) := rfl
example : L1 (1,2,3) = (3,0,-1) := rfl
example : L2 (1,2,3) = (0,3,-2) := rfl

open scoped Pointwise

/-- The ordinary pointwise finite-set sum `L0 A + L1 A + L2 A`.
Images and sums discard duplicates; triples are right-associated `(x,(y,z))`. -/
def mixedSum (A : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  A.image L0 + A.image L1 + A.image L2

example : mixedSum ∅ = ∅ := by simp [mixedSum]
example : mixedSum {(1,2,3)} = {(5,2,-3)} := by decide

private theorem rotated_projection_card (A : Finset (ℤ × ℤ × ℤ))
    (p : (ℤ × ℤ × ℤ) → ℤ × ℤ) :
    (A.image (fun t => ((p t).2, -(p t).1))).card = (A.image p).card := by
  have hinj : Function.Injective (fun v : ℤ × ℤ => (v.2, -v.1)) := by
    rintro ⟨a,b⟩ ⟨a',b'⟩ he
    simp only [Prod.mk.injEq, neg_inj] at he ⊢
    exact ⟨he.2, he.1⟩
  simpa only [Finset.image_image, Function.comp_def] using
    Finset.card_image_of_injective (A.image p) hinj

private theorem mixedSum_plane_image (A : Finset (ℤ × ℤ × ℤ)) :
    mixedSum A =
      (((A.image (fun t => (t.2.1,-t.1))) ×ˢ
        ((A.image (fun t => (t.2.2,-t.1))) ×ˢ
          (A.image (fun t => (t.2.2,-t.2.1))))).image planeSum) := by
  ext s
  constructor
  · intro hs
    obtain ⟨u,hu,r,hr,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_image.mpr
    refine ⟨((x.2.1,-x.1),(y.2.2,-y.1),(z.2.2,-z.2.1)),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hy,
          Finset.mem_image_of_mem _ hz⟩⟩, ?_⟩
    ext <;> simp [planeSum,L0,L1,L2]
  · intro hs
    obtain ⟨⟨p,q,r⟩,ht,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hp,hq,hr⟩ := by simpa only [Finset.mem_product] using ht
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_add.mpr
    refine ⟨L0 x + L1 y, Finset.mem_add.mpr
      ⟨L0 x,Finset.mem_image_of_mem _ hx,L1 y,Finset.mem_image_of_mem _ hy,rfl⟩,
      L2 z,Finset.mem_image_of_mem _ hz, ?_⟩
    ext <;> simp [planeSum,L0,L1,L2]

/-- The product of the three pair-projection cardinalities is bounded by
    the square of the ordinary mixed-sum cardinality. -/
theorem pair_projections_le_mixedSum_sq (A : Finset (ℤ × ℤ × ℤ)) :
    (A.image (fun t => (t.1,t.2.1))).card *
      (A.image (fun t => (t.1,t.2.2))).card *
      (A.image (fun t => (t.2.1,t.2.2))).card ≤ (mixedSum A).card ^ 2 := by
  have hS := plane_sum_card_sq
    (A.image (fun t => (t.2.1,-t.1)))
    (A.image (fun t => (t.2.2,-t.1)))
    (A.image (fun t => (t.2.2,-t.2.1)))
  rw [rotated_projection_card A (fun t => (t.1,t.2.1)),
    rotated_projection_card A (fun t => (t.1,t.2.2)),
    rotated_projection_card A (fun t => (t.2.1,t.2.2)),
    ← mixedSum_plane_image] at hS
  exact hS

/-- For every finite subset of `ℤ³`, the sum of its images under the three
specified noncommuting coordinate maps has at least as many distinct elements. -/
theorem card_le_mixedSum (A : Finset (ℤ × ℤ × ℤ)) : A.card ≤ (mixedSum A).card := by
  have hA := card_sq_le_pair_projections A
  have hS := plane_sum_card_sq
    (A.image (fun t => (t.2.1,-t.1)))
    (A.image (fun t => (t.2.2,-t.1)))
    (A.image (fun t => (t.2.2,-t.2.1)))
  rw [rotated_projection_card A (fun t => (t.1,t.2.1)),
    rotated_projection_card A (fun t => (t.1,t.2.2)),
    rotated_projection_card A (fun t => (t.2.1,t.2.2)),
    ← mixedSum_plane_image] at hS
  exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp
    (hA.trans hS)

example : (mixedSum {(0,0,0),(1,0,0)}).card = 4 := by decide
example : (mixedSum {(1,2,3)}).card = 1 := by decide
example : (mixedSum (∅ : Finset (ℤ × ℤ × ℤ))).card = 0 := by decide

example : ({(1,2,3)} : Finset (ℤ × ℤ × ℤ)).card ^ 2 ≤
    (({(1,2,3)} : Finset (ℤ × ℤ × ℤ)).image (fun t => (t.1,t.2.1))).card *
    (({(1,2,3)} : Finset (ℤ × ℤ × ℤ)).image (fun t => (t.1,t.2.2))).card *
    (({(1,2,3)} : Finset (ℤ × ℤ × ℤ)).image (fun t => (t.2.1,t.2.2))).card :=
  card_sq_le_pair_projections {(1,2,3)}

example : ({(0,0,0),(1,0,0)} : Finset (ℤ × ℤ × ℤ)).card ≤
    (mixedSum {(0,0,0),(1,0,0)}).card := card_le_mixedSum _

example : (∅ : Finset (ℤ × ℤ × ℤ)).card ≤ (mixedSum ∅).card := card_le_mixedSum _

end NoncommutingFiber
