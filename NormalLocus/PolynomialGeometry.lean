import NormalLocus.ExternalGeometry

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem polynomial_scheme_normal (n : ℕ) :
    normalPoints (Spec (CommRingCat.of (CoordinateRing n ℂ))) = Set.univ := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n ℂ))).commRingCatIsoToRingEquiv
  letI : IsIntegrallyClosed Γ(Spec (CommRingCat.of (CoordinateRing n ℂ)), ⊤) :=
    IsIntegrallyClosed.of_equiv e.symm
  exact normalPoints_eq_univ_of_affine _

theorem polynomial_scheme_complexAlgebraic (n : ℕ) :
    External.ComplexAlgebraic (Spec (CommRingCat.of (CoordinateRing n ℂ))) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateRing n ℂ)))
  have hs : LocallyOfFiniteType s := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  exact ⟨s, hs, inferInstance⟩

end NormalLocus
