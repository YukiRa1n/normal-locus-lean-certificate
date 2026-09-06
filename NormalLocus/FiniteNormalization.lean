import NormalLocus.NormalizationAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import NormalLocus.KellerEtale
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Finiteness of the relative integral closure in characteristic zero

This is an affine alternative to the Nagata invocation in `lem:finite-completion`.
Quasi-finiteness gives a finite extension of fraction fields; characteristic zero
makes it separable. The trace argument for a normal Noetherian base then proves
finiteness of the integral closure. No finiteness conclusion is assumed.
-/

namespace NormalLocus

theorem finite_relative_integralClosure
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing B] [IsIntegrallyClosed B]
    [Field K] [CharZero K] [Field L]
    [Algebra A B] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [Algebra.QuasiFinite A B] :
    Module.Finite A (integralClosure A B) := by
  letI : Algebra.QuasiFinite A L := Algebra.QuasiFinite.trans A B L
  letI : Algebra.QuasiFinite K L := Algebra.QuasiFinite.of_restrictScalars A K L
  letI : Module.Finite K L := Module.Finite.of_quasiFinite
  letI : IsIntegralClosure (integralClosure A B) A L :=
    IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn A (integralClosure A B) B L
  exact IsIntegralClosure.finite A K L (integralClosure A B)

theorem finite_relative_integralClosure_of_quasiFinite
    (A B : Type*) [CommRing A] [IsDomain A] [CharZero A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.QuasiFinite A B] :
    Module.Finite A (integralClosure A B) := by
  letI := FractionRing.liftAlgebra A (FractionRing B)
  letI := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  exact finite_relative_integralClosure A B (FractionRing A) (FractionRing B)

theorem keller_relative_integralClosure_finite
    {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    letI := graphAlgebra F
    Module.Finite (CoordinateRing n K)
      (integralClosure (CoordinateRing n K) (CoordinateRing n K)) := by
  letI := graphAlgebra F
  letI : FaithfulSMul (CoordinateRing n K) (CoordinateRing n K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (keller_substitution_injective F hF)
  letI : Algebra.QuasiFinite (CoordinateRing n K) (CoordinateRing n K) :=
    keller_ringHom_quasiFinite F hF
  exact finite_relative_integralClosure_of_quasiFinite (CoordinateRing n K) (CoordinateRing n K)

open CategoryTheory AlgebraicGeometry in
theorem keller_integralClosure_SpecMap_finite
    {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    letI := graphAlgebra F
    letI := (integralClosure (CoordinateRing n K) (CoordinateRing n K)).algebra
    AlgebraicGeometry.IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap (CoordinateRing n K)
        (integralClosure (CoordinateRing n K) (CoordinateRing n K))))) := by
  letI := graphAlgebra F
  letI := (integralClosure (CoordinateRing n K) (CoordinateRing n K)).algebra
  letI := keller_relative_integralClosure_finite F hF
  apply (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr
  exact (RingHom.finite_algebraMap).mpr inferInstance

end NormalLocus
