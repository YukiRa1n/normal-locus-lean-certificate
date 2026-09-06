import NormalLocus.ExternalStatements
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Regular points and the dimension-one part of R1

Regularity is equality of the cotangent-space dimension and the Krull
dimension of the actual local ring. No geometric conclusion is built into it.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

def regularPoints (X : Scheme) : Set X :=
  {x | (Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) : WithBot ℕ∞) =
    ringKrullDim (X.presheaf.stalk x)}

theorem normal_local_ring_dimension_one_regular
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] [IsIntegrallyClosed R] (hdim : ringKrullDim R = 1) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 1 := by
  letI : Ring.KrullDimLE 1 R := ⟨hdim.le⟩
  letI : Ring.DimensionLEOne R :=
    ⟨fun {I} hI hprime ↦
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
        (inferInstance : Ring.KrullDimLE 1 R)) I hI hprime⟩
  have hfield : ¬ IsField R := by
    intro h
    have hz := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at hz
    exact one_ne_zero hz
  exact (integrallyClosed_iff_cotangent_dimension_one R hfield).mp inferInstance

theorem normal_point_dimension_one_regular
    (X : Scheme) [IsLocallyNoetherian X] (x : X)
    (hx : x ∈ normalPoints X) (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    x ∈ regularPoints X := by
  letI : IsDomain (X.presheaf.stalk x) := hx.1
  letI : IsIntegrallyClosed (X.presheaf.stalk x) := hx.2
  change (Module.finrank _ _ : WithBot ℕ∞) = _
  rw [normal_local_ring_dimension_one_regular (X.presheaf.stalk x) hdim, hdim]
  rfl

end NormalLocus
