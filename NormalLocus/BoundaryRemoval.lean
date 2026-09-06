import NormalLocus.AffineHartogs
import NormalLocus.RegularPoints

/-!
# Transfer of the collision exclusion and removal of the boundary

The external dimension theorem is a general finite/dominant dimension formula
over a normal target. R1 at dimension one, the implication for boundary points,
and the application of affine Hartogs are proved in this module.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus.External

/-- The local-dimension formula for finite dominant maps of integral
Noetherian schemes over a normal target (integrality and going down). -/
def FiniteLocalDimension : Prop :=
  ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [AlgebraicGeometry.IsFinite g] [IsDominant g],
    normalPoints Y = Set.univ → ∀ x : X,
      ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (g x))

end NormalLocus.External

namespace NormalLocus

theorem height_one_points_avoid_boundary
    {X Y : Scheme} [IsLocallyNoetherian Y] (g : X ⟶ Y) (U : Set X)
    (hnormal : normalPoints Y = Set.univ)
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (Y.presheaf.stalk (g x)))
    (hboundary : g '' Uᶜ ⊆ (regularPoints Y)ᶜ) :
    ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 → x ∈ U := by
  intro x hx
  by_contra hxU
  have hregular : g x ∈ regularPoints Y :=
    normal_point_dimension_one_regular Y (g x)
      (hnormal.symm ▸ Set.mem_univ (g x)) ((hdim x).symm.trans hx)
  exact hboundary ⟨x, hxU, rfl⟩ hregular

theorem affine_boundary_removal
    (intersection : External.HeightOneIntersection)
    (dimension : External.FiniteLocalDimension)
    (X Y : Scheme.{0}) [IsAffine X] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNoetherianRing Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (g : X ⟶ Y) [AlgebraicGeometry.IsFinite g] [IsDominant g]
    (hnormal : normalPoints Y = Set.univ)
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hboundary : g '' (U : Set X)ᶜ ⊆ (regularPoints Y)ᶜ) : U = ⊤ := by
  exact affine_hartogs intersection X U hU
    (height_one_points_avoid_boundary g U hnormal
      (dimension X Y g hnormal) hboundary)

theorem boundary_image_under_normalization
    {T N C Z : Scheme} (i : T ⟶ N) (ν : N ⟶ C)
    (j : T ⟶ C) (q : C ⟶ Z)
    (hpreimage : ν ⁻¹' Set.range j = Set.range i)
    (hcollision : q '' (Set.range j)ᶜ ⊆ (regularPoints Z)ᶜ) :
    (ν ≫ q) '' (Set.range i)ᶜ ⊆ (regularPoints Z)ᶜ := by
  rintro _ ⟨n, hn, rfl⟩
  apply hcollision
  refine ⟨ν n, ?_, rfl⟩
  intro hnj
  exact hn (hpreimage ▸ hnj)

end NormalLocus
