import NormalLocus.ExternalGeometry
import NormalLocus.OpenNormal

/-!
# The same pullback and closure model throughout the local proof
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus.LocalModel

noncomputable section

variable {X V Y Z : Scheme.{0}}

abbrev W (π : V ⟶ Y) (i : Z ⟶ Y) := pullback π i
abbrev T (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y) := pullback j (pullback.fst π i)
abbrev k (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y) : T j π i ⟶ W π i :=
  pullback.snd j (pullback.fst π i)
abbrev toZ (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y) : T j π i ⟶ Z :=
  k j π i ≫ pullback.snd π i
abbrev C (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y) := (k j π i).image
abbrev l (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y) : T j π i ⟶ C j π i :=
  (k j π i).toImage
abbrev cV (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y) : C j π i ⟶ V :=
  (k j π i).imageι ≫ pullback.fst π i
abbrev q (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y) : C j π i ⟶ Z :=
  (k j π i).imageι ≫ pullback.snd π i

variable (j : X ⟶ V) (π : V ⟶ Y) (i : Z ⟶ Y)

theorem l_q : l j π i ≫ q j π i = toZ j π i := by
  simp [l, q, toZ]

theorem q_i : q j π i ≫ i = cV j π i ≫ π := by
  simp [q, cV, Category.assoc, pullback.condition]

theorem toZ_etale [Etale (j ≫ π)] : Etale (toZ j π i) := by
  rw [toZ, ← pullbackRightPullbackFstIso_hom_snd π i j]
  infer_instance

theorem range_cV [IsClosedImmersion i] [QuasiCompact (k j π i)] :
    Set.range (cV j π i) = closure (j '' ((j ≫ π) ⁻¹' Set.range i)) := by
  change Set.range ((pullback.fst π i) ∘ (k j π i).imageι) = _
  rw [Set.range_comp, image_inclusion_range,
    ← (pullback.fst π i).isClosedEmbedding.closure_image_eq]
  have h : (pullback.fst π i) '' Set.range (k j π i) =
      j '' ((j ≫ π) ⁻¹' Set.range i) := by
    rw [← Set.range_comp]
    change Set.range (k j π i ≫ pullback.fst π i) = _
    rw [← pullback.condition]
    change Set.range (j ∘ pullback.fst j (pullback.fst π i)) = _
    rw [Set.range_comp, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    rfl
  rw [h]

theorem preimage_source [IsOpenImmersion j] :
    (cV j π i) ⁻¹' Set.range j = Set.range (l j π i) := by
  change (k j π i).imageι ⁻¹' ((pullback.fst π i) ⁻¹' Set.range j) = _
  rw [← Scheme.Pullback.range_snd j (pullback.fst π i)]
  exact preimage_source_eq_range_toImage (k j π i)

theorem finite_actual_pullback_of_finite_model
    [AlgebraicGeometry.IsFinite (toZ j π i)] :
    AlgebraicGeometry.IsFinite (pullback.snd (j ≫ π) i) := by
  have he : (pullbackRightPullbackFstIso π i j).inv ≫ toZ j π i =
      pullback.snd (j ≫ π) i := by
    rw [toZ, ← pullbackRightPullbackFstIso_hom_snd π i j, Iso.inv_hom_id_assoc]
  rw [← he]
  infer_instance

end

end NormalLocus.LocalModel
