import NormalLocus.NonProper
import Mathlib.AlgebraicGeometry.OpenImmersion
import NormalLocus.CanonicalFinite

/-!
# The boundary-image identity in a genuine finite completion

Source: `prop:boundary-image`. The proof uses properness and open immersions
directly, so no separate equality of local integral closures is required here.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem proper_restriction_iff_preimage_subset_range
    {X V Y : Scheme} (j : X ⟶ V) (π : V ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsFinite π] (U : Y.Opens) :
    IsProper ((j ≫ π) ∣_ U) ↔ (π ⁻¹ᵁ U : Set V) ⊆ Set.range j := by
  constructor
  · intro hproper
    letI : IsProper (j ∣_ π ⁻¹ᵁ U ≫ π ∣_ U) := by
      rw [← morphismRestrict_comp]
      exact hproper
    letI : IsProper (j ∣_ π ⁻¹ᵁ U) := IsProper.of_comp _ (π ∣_ U)
    letI : IsDominant (j ∣_ π ⁻¹ᵁ U) :=
      IsZariskiLocalAtTarget.restrict ‹IsDominant j› _
    intro v hv
    obtain ⟨x, hx⟩ := (j ∣_ π ⁻¹ᵁ U).surjective ⟨v, hv⟩
    refine ⟨x.1, ?_⟩
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx
  · intro hsub
    letI : Surjective (j ∣_ π ⁻¹ᵁ U) := ⟨by
      rintro ⟨v, hv⟩
      obtain ⟨x, hx⟩ := hsub hv
      have hxU : x ∈ j ⁻¹ᵁ π ⁻¹ᵁ U := by
        change j x ∈ π ⁻¹ᵁ U
        rwa [hx]
      refine ⟨⟨x, hxU⟩, ?_⟩
      apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hx⟩
    letI : IsIso (j ∣_ π ⁻¹ᵁ U) :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
    rw [morphismRestrict_comp]
    infer_instance

/-- In a dense open / finite factorization, the non-properness set is exactly
the image of the omitted boundary. -/
theorem boundary_image_eq_nonProperLocus
    {X V Y : Scheme} (j : X ⟶ V) (π : V ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsFinite π] :
    π '' (Set.range j)ᶜ = nonProperLocus (j ≫ π) := by
  classical
  have hclosed : IsClosed (π '' (Set.range j)ᶜ) :=
    π.isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    intro ⟨U, hyU, hproper⟩
    exact hv ((proper_restriction_iff_preimage_subset_range j π U).mp hproper hyU)
  · intro hy
    by_contra hnot
    let U : Y.Opens := ⟨(π '' (Set.range j)ᶜ)ᶜ, hclosed.isOpen_compl⟩
    apply hy
    refine ⟨U, hnot, (proper_restriction_iff_preimage_subset_range j π U).mpr ?_⟩
    intro v hv
    by_contra hvnot
    exact hv ⟨v, hvnot, rfl⟩

theorem keller_nonProperLocus_eq_boundary_image
    {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    nonProperLocus (schemeMap F) =
      (schemeMap F).fromNormalization '' (Set.range (schemeMap F).toNormalization)ᶜ := by
  letI : Etale (schemeMap F) := keller_schemeMap_etale F hF
  letI : LocallyQuasiFinite (schemeMap F) := keller_schemeMap_quasiFinite F hF
  letI := keller_canonical_normalization_finite F hF
  simpa using (boundary_image_eq_nonProperLocus
    (schemeMap F).toNormalization (schemeMap F).fromNormalization).symm

end NormalLocus
