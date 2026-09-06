import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Connected.Clopen

/-!
# The final surjectivity step, for actual scheme morphisms

This file does not establish finiteness of a Keller map on a normal locus.
Finiteness and etaleness below are the standard mathlib properties, not
predicates defined by their desired consequences.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

theorem surjective_of_open_closed
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [PreconnectedSpace Y] (f : X → Y)
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) :
    Function.Surjective f := by
  have hclopen : IsClopen (Set.range f) :=
    ⟨hclosed.isClosed_range, hopen.isOpen_range⟩
  have hrange := hclopen.eq_univ (Set.range_nonempty f)
  intro y
  have hy : y ∈ Set.range f := hrange.symm ▸ Set.mem_univ y
  exact hy

/-- A nonempty finite etale morphism onto a preconnected scheme is surjective. -/
theorem finite_etale_surjective
    {X Y : Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.IsFinite f] [Etale f]
    [Nonempty X] [PreconnectedSpace Y] : Function.Surjective f := by
  exact surjective_of_open_closed f f.isOpenMap f.isClosedMap

end NormalLocus
