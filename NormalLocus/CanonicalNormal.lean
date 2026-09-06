import NormalLocus.Statement
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Normality of the canonical completion

Normality is expressed using the actual stalk rings in `normalPoints`.
The word "normalization" in an object name is not used as evidence.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem relative_integralClosure_isIntegrallyClosed
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A B] : IsIntegrallyClosed (integralClosure A B) := by
  letI : IsIntegralClosure (integralClosure A B) A (FractionRing B) :=
    IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
      A (integralClosure A B) B (FractionRing B)
  letI : IsIntegrallyClosedIn (integralClosure A B) (FractionRing B) :=
    IsIntegrallyClosedIn.of_isIntegralClosure (R := A)
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn _ (FractionRing B)

theorem normalPoints_eq_univ_of_affine
    (X : Scheme) [IsAffine X] [IsIntegral X] [IsIntegrallyClosed Γ(X, ⊤)] :
    normalPoints X = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let xU : (⊤ : X.Opens) := ⟨x, Set.mem_univ x⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf xU
  let p := (isAffineOpen_top X).primeIdealOf xU
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk xU
  exact ⟨inferInstance,
    isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors⟩

theorem canonical_normalization_normalPoints_eq_univ
    {X Y : Scheme} [IsAffine X] [IsAffine Y] [IsIntegral X]
    [IsIntegrallyClosed Γ(X, ⊤)] (f : X ⟶ Y) :
    normalPoints f.normalization = Set.univ := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : IsIntegrallyClosed Γ(f.normalization, ⊤) := by
    letI := (f.app ⊤).hom.toAlgebra
    letI : IsDomain Γ(X, f ⁻¹ᵁ ⊤) := by
      change IsDomain Γ(X, ⊤)
      infer_instance
    letI : IsIntegrallyClosed Γ(X, f ⁻¹ᵁ ⊤) := by
      change IsIntegrallyClosed Γ(X, ⊤)
      infer_instance
    letI := relative_integralClosure_isIntegrallyClosed Γ(Y, ⊤) Γ(X, f ⁻¹ᵁ ⊤)
    exact IsIntegrallyClosed.of_equiv
      (f.normalizationObjIso (isAffineOpen_top Y)).symm.commRingCatIsoToRingEquiv
  letI : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  exact normalPoints_eq_univ_of_affine f.normalization

theorem polynomial_canonical_normalization_normal
    {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    normalPoints (schemeMap F).normalization = Set.univ := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n K))).commRingCatIsoToRingEquiv
  letI : IsIntegrallyClosed Γ(Spec (CommRingCat.of (CoordinateRing n K)), ⊤) :=
    IsIntegrallyClosed.of_equiv e.symm
  exact canonical_normalization_normalPoints_eq_univ (schemeMap F)

theorem keller_canonical_finite_normal_completion
    {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    ∃ (V : Scheme)
      (j : Spec (CommRingCat.of (CoordinateRing n K)) ⟶ V)
      (π : V ⟶ Spec (CommRingCat.of (CoordinateRing n K))),
      j ≫ π = schemeMap F ∧ IsOpenImmersion j ∧ QuasiCompact j ∧
        IsDominant j ∧ AlgebraicGeometry.IsFinite π ∧ normalPoints V = Set.univ := by
  letI : Etale (schemeMap F) := keller_schemeMap_etale F hF
  letI : LocallyQuasiFinite (schemeMap F) := keller_schemeMap_quasiFinite F hF
  letI := keller_canonical_normalization_finite F hF
  exact ⟨(schemeMap F).normalization, (schemeMap F).toNormalization,
    (schemeMap F).fromNormalization, (schemeMap F).toNormalization_fromNormalization,
    inferInstance, inferInstance, inferInstance, inferInstance,
    polynomial_canonical_normalization_normal F⟩

end NormalLocus
