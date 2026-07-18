import Xlib.CharDegreesComm

/-! Micro-probe 2: bisect the congr failure context. Throwaway. -/

open scoped IsMulCommutative

-- P5: full context replication (letI compHom + tower + set φ + IsMulCommutative)
example {G : Type*} [Group G] [Fintype G] (A : Subgroup G) [IsMulCommutative A]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S] : True := by
  haveI : Nontrivial ↥S := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ↥S
  haveI : NeZero (Nat.card ↥A : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set φ : MonoidAlgebra ℂ ↥A →ₐ[ℂ] MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype with hφdef
  letI : Module (MonoidAlgebra ℂ ↥A) ↥S := Module.compHom ↥S φ.toRingHom
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ ↥A) ↥S :=
    ⟨fun c z s => by
      show (φ (c • z)) • s = c • (φ z • s)
      rw [map_smul, smul_assoc]⟩
  obtain ⟨W, -, hW⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (⊤ : Submodule (MonoidAlgebra ℂ ↥A) ↥S)).resolve_left (by
        intro htop
        obtain ⟨x, hx⟩ := exists_ne (0 : ↥S)
        exact hx ((Submodule.eq_bot_iff _).mp htop x Submodule.mem_top))
  haveI := hW
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (R := MonoidAlgebra ℂ ↥A) (M := ↥W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ ↥A) ↥I := IsSimpleModule.congr e.symm
  trivial

-- P6: same but no IsMulCommutative binder (and no scoped instance in play)
example {G : Type*} [Group G] [Fintype G] (A : Subgroup G)
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S] : True := by
  haveI : Nontrivial ↥S := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ↥S
  haveI : NeZero (Nat.card ↥A : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set φ : MonoidAlgebra ℂ ↥A →ₐ[ℂ] MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype with hφdef
  letI : Module (MonoidAlgebra ℂ ↥A) ↥S := Module.compHom ↥S φ.toRingHom
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ ↥A) ↥S :=
    ⟨fun c z s => by
      show (φ (c • z)) • s = c • (φ z • s)
      rw [map_smul, smul_assoc]⟩
  obtain ⟨W, -, hW⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (⊤ : Submodule (MonoidAlgebra ℂ ↥A) ↥S)).resolve_left (by
        intro htop
        obtain ⟨x, hx⟩ := exists_ne (0 : ↥S)
        exact hx ((Submodule.eq_bot_iff _).mp htop x Submodule.mem_top))
  haveI := hW
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (R := MonoidAlgebra ℂ ↥A) (M := ↥W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ ↥A) ↥I := IsSimpleModule.congr e.symm
  trivial
