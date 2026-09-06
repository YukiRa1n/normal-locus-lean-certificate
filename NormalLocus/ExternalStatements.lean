import NormalLocus.CanonicalNormal
import NormalLocus.NormalHeightOne

/-!
# Explicit external theorem statements

These declarations name propositions; none asserts that a proposition is true.
Conditional proofs receive their proofs as ordinary explicit arguments.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus.External

/-- A genuine finite-type structure morphism over the complex numbers. -/
def ComplexAlgebraic (X : Scheme.{0}) : Prop :=
  ∃ s : X ⟶ Spec (CommRingCat.of ℂ), LocallyOfFiniteType s ∧ QuasiCompact s

theorem ComplexAlgebraic.of_finiteType
    {X Y : Scheme.{0}} (hY : ComplexAlgebraic Y) (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] : ComplexAlgebraic X := by
  obtain ⟨s, hs, hq⟩ := hY
  letI := hs
  letI := hq
  exact ⟨f ≫ s, inferInstance, inferInstance⟩

theorem ComplexAlgebraic.isLocallyNoetherian
    {X : Scheme.{0}} (hX : ComplexAlgebraic X) : IsLocallyNoetherian X := by
  obtain ⟨s, hs, _⟩ := hX
  letI := hs
  exact LocallyOfFiniteType.isLocallyNoetherian s

noncomputable def globalToFunctionField (X : Scheme.{0}) [IsIntegral X] :
    Γ(X, ⊤) →+* X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, Set.mem_univ _⟩⟩
  exact (X.germToFunctionField ⊤).hom

/-- Stacks 0AVB with the module equal to the base ring, expressed on an affine
scheme through its actual stalks and function field. The bridge between stalks
and prime localizations is built into this geometric formulation. -/
def HeightOneIntersection : Prop :=
  ∀ (X : Scheme.{0}) [IsAffine X] [IsIntegral X]
    [IsNoetherianRing Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (s : X.functionField),
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) →
    s ∈ (globalToFunctionField X).range

end NormalLocus.External
