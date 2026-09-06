import NormalLocus.ExternalStatements

/-!
# Normality and open embeddings

The transfer uses the actual isomorphisms of stalk rings of an open immersion.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem normal_point_openImmersion_iff
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    x ∈ normalPoints X ↔ f x ∈ normalPoints Y := by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  constructor
  · intro hx
    letI : IsDomain (X.presheaf.stalk x) := hx.1
    letI : IsIntegrallyClosed (X.presheaf.stalk x) := hx.2
    exact ⟨Function.Injective.isDomain e e.injective,
      IsIntegrallyClosed.of_equiv e.symm⟩
  · intro hy
    letI : IsDomain (Y.presheaf.stalk (f x)) := hy.1
    letI : IsIntegrallyClosed (Y.presheaf.stalk (f x)) := hy.2
    exact ⟨Function.Injective.isDomain e.symm e.symm.injective,
      IsIntegrallyClosed.of_equiv e⟩

theorem normalPoints_openImmersion
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (hY : normalPoints Y = Set.univ) : normalPoints X = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (normal_point_openImmersion_iff f x).mpr (hY.symm ▸ Set.mem_univ (f x))

theorem normalPoints_isReduced
    (X : Scheme) (hX : normalPoints X = Set.univ) : AlgebraicGeometry.IsReduced X := by
  letI (x : X) : IsDomain (X.presheaf.stalk x) :=
    (show x ∈ normalPoints X from hX.symm ▸ Set.mem_univ x).1
  exact isReduced_of_isReduced_stalk X

end NormalLocus
