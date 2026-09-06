import NormalLocus.BoundaryImage

/-!
# The completion is etale away from its boundary image

This verifies the covering hypothesis of Abhyankar on the same completion.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem completion_etale_restriction
    {X V Y : Scheme} (j : X ⟶ V) (π : V ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsFinite π] [Etale (j ≫ π)]
    (U : Y.Opens) (hU : (π ⁻¹ᵁ U : Set V) ⊆ Set.range j) : Etale (π ∣_ U) := by
  letI : IsProper ((j ≫ π) ∣_ U) :=
    (proper_restriction_iff_preimage_subset_range j π U).mpr hU
  letI : IsProper (j ∣_ π ⁻¹ᵁ U ≫ π ∣_ U) := by
    rw [← morphismRestrict_comp]
    infer_instance
  letI : IsProper (j ∣_ π ⁻¹ᵁ U) := IsProper.of_comp _ (π ∣_ U)
  letI : IsDominant (j ∣_ π ⁻¹ᵁ U) :=
    IsZariskiLocalAtTarget.restrict ‹IsDominant j› _
  letI : Surjective (j ∣_ π ⁻¹ᵁ U) := ⟨(j ∣_ π ⁻¹ᵁ U).surjective⟩
  letI : IsIso (j ∣_ π ⁻¹ᵁ U) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  letI : Etale (j ∣_ π ⁻¹ᵁ U ≫ π ∣_ U) := by
    rw [← morphismRestrict_comp]
    infer_instance
  have he : π ∣_ U = inv (j ∣_ π ⁻¹ᵁ U) ≫ (j ∣_ π ⁻¹ᵁ U ≫ π ∣_ U) := by simp
  rw [he]
  infer_instance

theorem completion_etale_outside_divisor
    {X V Y Z : Scheme} (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsFinite π] [Etale (j ≫ π)]
    (hboundary : (Set.range j)ᶜ ⊆ π ⁻¹' Set.range i) :
    ∀ U : Y.Opens, Disjoint (U : Set Y) (Set.range i) → Etale (π ∣_ U) := by
  intro U hU
  apply completion_etale_restriction j π U
  intro v hv
  by_contra hnot
  exact Set.disjoint_left.mp hU hv (hboundary hnot)

end NormalLocus
