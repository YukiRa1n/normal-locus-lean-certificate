import NormalLocus.ExternalStatements

/-!
# Affine Hartogs from the height-one intersection theorem

This implements `lem:affine-hartogs`. Only the general intersection formula is
an external input. Extension of sections, compatibility with restriction, and
reconstruction of the affine scheme are proved here.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem affine_hartogs_restriction_bijective
    (intersection : External.HeightOneIntersection)
    (X : Scheme.{0}) [IsAffine X] [IsIntegral X]
    [IsNoetherianRing Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (U : X.Opens) [Nonempty U]
    (hcodim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 → x ∈ U) :
    Function.Bijective (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  refine ⟨map_injective_of_isIntegral X _, ?_⟩
  intro s
  have hlocal (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 1) :
      (X.germToFunctionField U) s ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range := by
    let xU : U := ⟨x, hcodim x hx⟩
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf xU
    letI := functionField_isScalarTower X U xU
    refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk x) s, ?_⟩
    exact (IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x)
      X.functionField s).symm
  obtain ⟨a, ha⟩ := intersection X ((X.germToFunctionField U) s) hlocal
  refine ⟨a, X.germToFunctionField_injective U ?_⟩
  change (X.germToFunctionField U)
    ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) a) = _
  simpa only [Scheme.germToFunctionField, TopCat.Presheaf.germ_res_apply] using ha

theorem affine_hartogs
    (intersection : External.HeightOneIntersection)
    (X : Scheme.{0}) [IsAffine X] [IsIntegral X]
    [IsNoetherianRing Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hcodim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 → x ∈ U) :
    U = ⊤ := by
  letI : IsAffine U := hU
  have hbij := affine_hartogs_restriction_bijective intersection X U hcodim
  letI : IsIso (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have heq : U.ι.appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    simp [Scheme.Opens.topIso_hom, ← Functor.map_comp]
  letI : IsIso U.ι.appTop := by
    have : IsIso (U.ι.appTop ≫ U.topIso.hom) := heq ▸ inferInstance
    exact IsIso.of_isIso_comp_right U.ι.appTop U.topIso.hom
  letI : IsIso U.ι := by
    have he : U.ι = U.toScheme.isoSpec.hom ≫ Spec.map U.ι.appTop ≫ X.isoSpec.inv := by
      rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨u, rfl⟩ := U.ι.surjective x
  exact u.2

end NormalLocus
