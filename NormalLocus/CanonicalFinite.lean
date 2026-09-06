import NormalLocus.FiniteNormalization
import NormalLocus.Completion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Finiteness on the same canonical normalization used by Zariski Main

The affine integral-closure calculation is transported through mathlib's
`normalizationObjIso`; no identification of different models is assumed.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem finite_fromNormalization_of_finite_integralClosure_top
    {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hfin : letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
      Module.Finite Γ(Y, ⊤) (integralClosure Γ(Y, ⊤) Γ(X, ⊤))) :
    AlgebraicGeometry.IsFinite f.fromNormalization := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  rw [HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.IsFinite)]
  refine ⟨inferInstance, ?_⟩
  change (f.fromNormalization.app ⊤).hom.Finite
  rw [f.fromNormalization_app (isAffineOpen_top Y)]
  apply RingHom.Finite.comp
  · exact RingHom.Finite.of_surjective _
      (f.normalizationObjIso (isAffineOpen_top Y)).symm.commRingCatIsoToRingEquiv.surjective
  · exact RingHom.finite_algebraMap.mpr hfin

theorem canonical_normalization_finite
    {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyQuasiFinite f] [IsDominant f] [IsReduced Y]
    [IsDomain Γ(Y, ⊤)] [CharZero Γ(Y, ⊤)] [IsNoetherianRing Γ(Y, ⊤)]
    [IsIntegrallyClosed Γ(Y, ⊤)] [IsDomain Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)] :
    AlgebraicGeometry.IsFinite f.fromNormalization := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  letI : FaithfulSMul Γ(Y, ⊤) Γ(X, ⊤) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (f.app_injective ⊤)
  letI : Algebra.QuasiFinite Γ(Y, ⊤) Γ(X, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mp ‹LocallyQuasiFinite f›
  apply finite_fromNormalization_of_finite_integralClosure_top f
  exact finite_relative_integralClosure_of_quasiFinite Γ(Y, ⊤) Γ(X, ⊤)

theorem keller_canonical_normalization_finite
    {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    AlgebraicGeometry.IsFinite (schemeMap F).fromNormalization := by
  let R := CommRingCat.of (CoordinateRing n K)
  let e : Γ(Spec R, ⊤) ≃+* CoordinateRing n K :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : IsIntegrallyClosed Γ(Spec R, ⊤) := IsIntegrallyClosed.of_equiv e.symm
  letI : IsNoetherianRing Γ(Spec R, ⊤) :=
    isNoetherianRing_of_ringEquiv (CoordinateRing n K) e.symm
  letI : CharZero Γ(Spec R, ⊤) := charZero_of_injective_ringHom e.symm.injective
  letI : LocallyQuasiFinite (schemeMap F) := keller_schemeMap_quasiFinite F hF
  letI : IsDominant (schemeMap F) := keller_schemeMap_dominant F hF
  exact canonical_normalization_finite (schemeMap F)

/-- The finite morphism and the dense open immersion now belong to the same
canonical completion, with their composition equal to the original Keller map. -/
theorem keller_canonical_finite_completion
    {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    ∃ (V : Scheme)
      (j : Spec (CommRingCat.of (CoordinateRing n K)) ⟶ V)
      (π : V ⟶ Spec (CommRingCat.of (CoordinateRing n K))),
      j ≫ π = schemeMap F ∧ IsOpenImmersion j ∧ QuasiCompact j ∧
        IsDominant j ∧ AlgebraicGeometry.IsFinite π := by
  letI : Etale (schemeMap F) := keller_schemeMap_etale F hF
  letI : LocallyQuasiFinite (schemeMap F) := keller_schemeMap_quasiFinite F hF
  letI := keller_canonical_normalization_finite F hF
  exact ⟨(schemeMap F).normalization, (schemeMap F).toNormalization,
    (schemeMap F).fromNormalization, (schemeMap F).toNormalization_fromNormalization,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

end NormalLocus
