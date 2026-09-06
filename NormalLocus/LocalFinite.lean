import NormalLocus.LocalModel
import NormalLocus.EtaleOutsideBoundary

/-!
# The local finite restriction, conditional on the external geometric library

This combines the two divisor constructions, Abhyankar's local consequence,
the normalization pieces, R1, and affine Hartogs on the SAME local model.
Finiteness of the pullback from the source is the conclusion, not an input.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

theorem local_restriction_finite
    (H : External.CoreGeometry)
    {X V Y Z : Scheme.{0}} [IsAffine X] [IsAffine V] [IsAffine Y] [IsAffine Z]
    [IsIntegral X] [IsIntegral V] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y]
    (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsFinite π]
    [IsDominant π] [Etale (j ≫ π)] [IsClosedImmersion i]
    (hY : External.ComplexAlgebraic Y)
    (hVnormal : normalPoints V = Set.univ)
    (hYregular : regularPoints Y = Set.univ)
    (hZnormal : normalPoints Z = Set.univ)
    (hdivisor : IsDivisorUnion (Set.range i))
    (hboundary : (Set.range j)ᶜ ⊆ π ⁻¹' Set.range i) :
    AlgebraicGeometry.IsFinite (pullback.snd (j ≫ π) i) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π)
  letI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  letI : IsAffine (LocalModel.W π i) := isAffine_of_isAffineHom (pullback.snd π i)
  letI : IsAffine (LocalModel.T j π i) :=
    isAffine_of_isAffineHom (pullback.fst j (pullback.fst π i))
  letI : Etale (LocalModel.toZ j π i) := LocalModel.toZ_etale j π i
  have hTnormal := H.etaleNormal (LocalModel.T j π i) Z (LocalModel.toZ j π i) hZnormal
  letI : AlgebraicGeometry.IsReduced (LocalModel.T j π i) :=
    normalPoints_isReduced _ hTnormal
  letI : IsAffine (LocalModel.C j π i) :=
    isAffine_of_isAffineHom (LocalModel.k j π i).imageι
  letI : AlgebraicGeometry.IsReduced (LocalModel.C j π i) :=
    image_isReduced_of_affine (LocalModel.k j π i)
  letI : IsLocallyNoetherian (LocalModel.C j π i) :=
    LocallyOfFiniteType.isLocallyNoetherian (LocalModel.q j π i)
  letI : Etale (LocalModel.l j π i ≫ LocalModel.q j π i) := by
    rw [LocalModel.l_q]
    infer_instance
  have hCcomplex : External.ComplexAlgebraic (LocalModel.C j π i) :=
    (hY.of_finiteType π).of_finiteType (LocalModel.cV j π i)
  have hDclosed : IsClosed (π ⁻¹' Set.range i) :=
    i.isClosedEmbedding.isClosed_range.preimage π.continuous
  have hDproper : π ⁻¹' Set.range i ≠ Set.univ := by
    intro h
    apply hdivisor.ne_univ
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨v, rfl⟩ := π.surjective y
    have hv : v ∈ π ⁻¹' Set.range i := h.symm ▸ Set.mem_univ v
    exact hv
  have hcollisionV : π ''
      (closure (j '' ((j ≫ π) ⁻¹' Set.range i)) \ Set.range j) ⊆
      (i '' regularPoints Z)ᶜ := by
    apply collision_from_divisor_decompositions j π j.isOpenEmbedding j.denseRange
      ((j ≫ π) ⁻¹' Set.range i) (π ⁻¹' Set.range i) (i '' regularPoints Z)
      (H.etaleDivisors X Y (j ≫ π) _ hdivisor)
      (H.boundary X V j) hDclosed hDproper
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · exact hboundary
    · rintro a ha ⟨z, hz, he⟩
      obtain ⟨W, haW, hW⟩ := H.abhyankar V Y Z π i hY hVnormal hYregular hdivisor
        (completion_etale_outside_divisor j π i hboundary) a z he.symm hz
      exact ⟨W, W.isOpen, haW, hW⟩
  have hcollision : (LocalModel.q j π i) ''
      (Set.range (LocalModel.l j π i))ᶜ ⊆ (regularPoints Z)ᶜ := by
    rintro _ ⟨c, hc, rfl⟩ hreg
    apply hcollisionV
      (show π (LocalModel.cV j π i c) ∈ π ''
        (closure (j '' ((j ≫ π) ⁻¹' Set.range i)) \ Set.range j) from ?_)
    · refine ⟨LocalModel.q j π i c, hreg, ?_⟩
      exact congrArg (fun f : LocalModel.C j π i ⟶ Y ↦ f c) (LocalModel.q_i j π i)
    · refine ⟨LocalModel.cV j π i c, ⟨?_, ?_⟩, rfl⟩
      · rw [← LocalModel.range_cV]
        exact ⟨c, rfl⟩
      · intro hcj
        have : c ∈ (LocalModel.cV j π i) ⁻¹' Set.range j := hcj
        rw [LocalModel.preimage_source] at this
        exact hc this
  have hclosed := closure_equality_from_pieces H.intersection H.dimension
    (LocalModel.l j π i) (LocalModel.q j π i) hZnormal hcollision
    (H.normalization (LocalModel.T j π i) (LocalModel.C j π i)
      (LocalModel.l j π i) hTnormal hCcomplex)
  letI : AlgebraicGeometry.IsFinite (LocalModel.toZ j π i) := by
    rw [← LocalModel.l_q]
    exact hclosed.2
  exact LocalModel.finite_actual_pullback_of_finite_model j π i

end NormalLocus
