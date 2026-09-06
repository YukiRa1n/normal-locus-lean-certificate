import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The Zariski Main part of `lem:finite-completion`

The canonical relative normalization is an integral completion. The manuscript
adds a Nagata argument for finiteness (Stacks 03GR). `FiniteNormalization.lean`
proves affine integral-closure finiteness by a characteristic-zero trace argument;
comparison with this canonical scheme construction remains to be implemented.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

/-- Zariski Main gives a genuine open, dense, quasi-compact factor into an
integral morphism. Every property here uses the standard scheme definitions. -/
theorem canonical_integral_completion
    {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f] :
    ∃ (V : Scheme) (j : X ⟶ V) (π : V ⟶ Y),
      j ≫ π = f ∧ IsOpenImmersion j ∧ QuasiCompact j ∧ IsDominant j ∧ IsIntegralHom π := by
  exact ⟨f.normalization, f.toNormalization, f.fromNormalization,
    f.toNormalization_fromNormalization, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- Proper plus quasi-finite is finite: the input used in `prop:boundary-image`. -/
theorem finite_of_proper_quasiFinite
    {X Y : Scheme} (f : X ⟶ Y) [IsProper f] [LocallyQuasiFinite f] :
    AlgebraicGeometry.IsFinite f :=
  AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite f

end NormalLocus
