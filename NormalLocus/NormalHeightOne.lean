import NormalLocus.CurveLocalAlgebra
import Mathlib.RingTheory.Ideal.Height

/-!
# The height-one local algebra of normal Noetherian domains

The prime-height hypothesis is on the original ring. The conclusion concerns
its actual localization, not an independently assumed one-dimensional ring.
This is the local algebra part of the R1 input in the manuscript.
-/

namespace NormalLocus

theorem normal_height_one_localization_isDVR
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let R := Localization.AtPrime p
  have hp0 : p ≠ ⊥ := by
    intro h
    simp [h] at hp
  letI : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p R, hp]
    rfl
  letI : Ring.KrullDimLE 1 R := ⟨hdim.le⟩
  letI : Ring.DimensionLEOne R :=
    ⟨fun {I} hI hprime ↦
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
        (inferInstance : Ring.KrullDimLE 1 R)) I hI hprime⟩
  letI : IsDedekindDomain R :=
    { (inferInstance : IsDomain R), (inferInstance : IsNoetherianRing R),
      ‹Ring.DimensionLEOne R›, ‹IsIntegrallyClosed R› with }
  exact ((IsDiscreteValuationRing.TFAE R
    (IsLocalization.AtPrime.not_isField A hp0 R)).out 2 0).mp
      (inferInstance : IsDedekindDomain R)

theorem normal_height_one_cotangent_dimension
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) = 1 := by
  exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mpr
    (normal_height_one_localization_isDVR A p hp)

end NormalLocus
