import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Comparison of the two integral closures in the manuscript

Source: `lem:finite-completion` (the two inclusions) and
`prop:boundary-image` (the finite, normal case).

This proves the affine ring statements. It does not assume that a normal finite
completion of a Keller morphism has already been constructed.
-/

namespace NormalLocus

section

variable (A B K : Type*) [CommRing A] [CommRing B] [Field K]
  [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
  [IsFractionRing B K] [IsIntegrallyClosed B]

/-- Integral elements of the function field already lie in the normal source ring. -/
theorem integral_element_lifts_to_normal_source
    (x : K) (hx : IsIntegral A x) :
    ∃ b : B, IsIntegral A b ∧ algebraMap B K b = x := by
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := B))
  refine ⟨b, ?_, hb⟩
  apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom A B K)
    (IsFractionRing.injective B K)).mp
  change IsIntegral A (algebraMap B K b)
  rwa [hb]

/-- The relative integral closure maps onto the function-field integral closure. -/
theorem relative_integralClosure_map_eq :
    (integralClosure A B).map (IsScalarTower.toAlgHom A B K) = integralClosure A K := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (show IsIntegral A b from hb).map (IsScalarTower.toAlgHom A B K)
  · intro hx
    obtain ⟨b, hb, heq⟩ := integral_element_lifts_to_normal_source A B K x hx
    exact ⟨b, hb, heq⟩

/-- The finite normal source is the whole integral closure in its fraction field. -/
theorem finite_normal_source_isIntegralClosure [Module.Finite A B] :
    IsIntegralClosure B A K := by
  infer_instance

/-- The equality used to rule out boundary points over a proper neighborhood. -/
theorem finite_normal_source_range_eq_integralClosure [Module.Finite A B] :
    (IsScalarTower.toAlgHom A B K).range = integralClosure A K := by
  letI : IsIntegralClosure B A K := finite_normal_source_isIntegralClosure A B K
  ext x
  exact (IsIntegralClosure.isIntegral_iff (R := A) (A := B) (B := K)).symm

end

end NormalLocus
