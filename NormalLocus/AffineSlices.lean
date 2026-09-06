import NormalLocus.LocalFinite
import NormalLocus.RestrictionCompatibility
import NormalLocus.DivisorNonomission

/-!
# Applying the local finite theorem on ambient affine slices
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

theorem completion_boundary_restriction
    {X V Y S : Scheme} (j : X ⟶ V) (π : V ⟶ Y) (i : S ⟶ Y)
    (hboundary : (Set.range j)ᶜ ⊆ π ⁻¹' Set.range i) (U : Y.Opens) :
    (Set.range (j ∣_ π ⁻¹ᵁ U))ᶜ ⊆ (π ∣_ U) ⁻¹' Set.range (i ∣_ U) := by
  intro v hv
  rw [range_morphismRestrict] at hv
  have hb : π v.1 ∈ Set.range i := hboundary hv
  rw [Set.mem_preimage, range_morphismRestrict]
  simpa only [Set.mem_preimage, Scheme.Opens.ι_apply, morphismRestrict_base_coe] using hb

theorem finite_on_normal_affine_slice
    (H : External.CoreGeometry)
    {X V Y S : Scheme.{0}} [IsAffine X] [IsAffine V] [IsAffine Y]
    [IsIntegral X] [IsIntegral V] [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ V) (π : V ⟶ Y) (i : S ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsFinite π]
    [IsDominant π] [Etale (j ≫ π)] [IsClosedImmersion i]
    (hY : External.ComplexAlgebraic Y) (hVnormal : normalPoints V = Set.univ)
    (hdivisor : IsDivisorUnion (Set.range i))
    (hboundary : (Set.range j)ᶜ ⊆ π ⁻¹' Set.range i)
    (U : Y.Opens) (hUne : (U : Set Y).Nonempty) (hU : IsAffineOpen U)
    (hZintegral : IsIntegral (i ⁻¹ᵁ U).toScheme)
    (hZnormal : normalPoints (i ⁻¹ᵁ U).toScheme = Set.univ)
    (hUregular : regularPoints U.toScheme = Set.univ) :
    AlgebraicGeometry.IsFinite ((pullback.snd (j ≫ π) i) ∣_ (i ⁻¹ᵁ U)) := by
  letI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π)
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian i
  letI : Nonempty U.toScheme := ⟨⟨hUne.choose, hUne.choose_spec⟩⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (π ⁻¹ᵁ U).toScheme := hU.preimage π
  letI : IsAffine (j ⁻¹ᵁ π ⁻¹ᵁ U).toScheme := hU.preimage (j ≫ π)
  letI : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
  letI : Nonempty (π ⁻¹ᵁ U).toScheme :=
    preimage_nonempty_of_dense_image π π.denseRange U hUne
  letI : Nonempty (j ⁻¹ᵁ π ⁻¹ᵁ U).toScheme :=
    preimage_nonempty_of_dense_image (j ≫ π) (j ≫ π).denseRange U hUne
  letI : IsIntegral (π ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (π ⁻¹ᵁ U).ι
  letI : IsIntegral (j ⁻¹ᵁ π ⁻¹ᵁ U).toScheme :=
    isIntegral_of_isOpenImmersion (j ⁻¹ᵁ π ⁻¹ᵁ U).ι
  letI := hZintegral
  letI : IsDominant (j ∣_ π ⁻¹ᵁ U) :=
    IsZariskiLocalAtTarget.restrict ‹IsDominant j› _
  letI : IsDominant (π ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsDominant π› _
  letI : Etale (j ∣_ π ⁻¹ᵁ U ≫ π ∣_ U) := by
    rw [← morphismRestrict_comp]
    infer_instance
  have hdivU : IsDivisorUnion (Set.range (i ∣_ U)) := by
    rw [range_morphismRestrict]
    exact H.etaleDivisors U.toScheme Y U.ι (Set.range i) hdivisor
  have hlocal := local_restriction_finite H (j ∣_ π ⁻¹ᵁ U) (π ∣_ U) (i ∣_ U)
    (hY.of_finiteType U.ι)
    (normalPoints_openImmersion (π ⁻¹ᵁ U).ι hVnormal)
    hUregular hZnormal hdivU (completion_boundary_restriction j π i hboundary U)
  rw [← morphismRestrict_comp] at hlocal
  exact (MorphismProperty.arrow_mk_iso_iff (@AlgebraicGeometry.IsFinite)
    (baseChangeTargetRestrictionIso (j ≫ π) i U)).mpr hlocal

end NormalLocus
