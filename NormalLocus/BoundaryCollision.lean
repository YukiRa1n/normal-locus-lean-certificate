import Mathlib.Topology.Irreducible

/-!
# The collision argument

`PrimeDivisor` is expressed by its topological codimension-one property: it is
a maximal proper irreducible closed subset of an irreducible ambient space.
No polynomial map, boundary exclusion, or finiteness conclusion occurs in this
definition. In a Noetherian integral scheme this is the usual prime divisor.
-/

open Set

namespace NormalLocus

structure PrimeDivisor {X : Type*} [TopologicalSpace X] (E : Set X) : Prop where
  isClosed : IsClosed E
  isIrreducible : IsIrreducible E
  ne_univ : E ≠ univ
  maximal : ∀ Q : Set X, IsClosed Q → IsIrreducible Q → E ⊆ Q →
    Q = E ∨ Q = univ

/-- An irreducible local neighborhood of a divisor admits no collision of two
distinct prime divisors. This is the contradiction in Step 4 of the TeX proof. -/
theorem prime_divisors_equal_at_irreducible_neighborhood
    {X : Type*} [TopologicalSpace X]
    {D E R W : Set X} {a : X}
    (hD : IsClosed D) (hDproper : D ≠ univ)
    (hE : PrimeDivisor E) (hR : PrimeDivisor R)
    (hED : E ⊆ D) (hRD : R ⊆ D) (haE : a ∈ E) (haR : a ∈ R)
    (hW : IsOpen W) (haW : a ∈ W) (hDW : IsIrreducible (D ∩ W)) : E = R := by
  have hQ : closure (D ∩ W) ⊆ D :=
    closure_minimal inter_subset_left hD
  have hQproper : closure (D ∩ W) ≠ univ := by
    intro h
    exact hDproper (univ_subset_iff.mp (h ▸ hQ))
  have hEQ : E ⊆ closure (D ∩ W) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hE.isIrreducible.2 hW
      ⟨a, haE, haW⟩).trans (closure_mono (inter_subset_inter_left _ hED))
  have hRQ : R ⊆ closure (D ∩ W) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hR.isIrreducible.2 hW
      ⟨a, haR, haW⟩).trans (closure_mono (inter_subset_inter_left _ hRD))
  have he := (hE.maximal _ isClosed_closure hDW.closure hEQ).resolve_right hQproper
  have hr := (hR.maximal _ isClosed_closure hDW.closure hRQ).resolve_right hQproper
  exact he.symm.trans hr

/-- The boundary and interior divisors are different because exactly the
interior one meets the source open. -/
theorem boundary_divisor_ne_interior
    {X : Type*} {U E R : Set X} (hE : E ⊆ Uᶜ) (hR : (R ∩ U).Nonempty) : E ≠ R := by
  rintro rfl
  obtain ⟨x, hxE, hxU⟩ := hR
  exact hE hxE hxU

/-- Combining the two divisor constructions with the local conclusion of
Abhyankar excludes boundary points over regular target points.
The divisor constructions and the external local theorem are explicit inputs
at this stage; subsequent specializations must establish them. -/
theorem boundary_collision_exclusion
    {X Y : Type*} [TopologicalSpace X] (p : X → Y)
    (U C D : Set X) (regular : Set Y)
    (hD : IsClosed D) (hDproper : D ≠ univ)
    (boundary : ∀ a ∈ C \ U,
      ∃ E : Set X, PrimeDivisor E ∧ a ∈ E ∧ E ⊆ Uᶜ ∧ E ⊆ D)
    (interior : ∀ a ∈ C,
      ∃ R : Set X, PrimeDivisor R ∧ a ∈ R ∧ (R ∩ U).Nonempty ∧ R ⊆ D)
    (localStructure : ∀ a ∈ D, p a ∈ regular →
      ∃ W : Set X, IsOpen W ∧ a ∈ W ∧ IsIrreducible (D ∩ W)) :
    p '' (C \ U) ⊆ regularᶜ := by
  rintro _ ⟨a, ha, rfl⟩ hreg
  obtain ⟨E, hE, haE, hEU, hED⟩ := boundary a ha
  obtain ⟨R, hR, haR, hRU, hRD⟩ := interior a ha.1
  obtain ⟨W, hW, haW, hDW⟩ := localStructure a (hED haE) hreg
  exact boundary_divisor_ne_interior hEU hRU
    (prime_divisors_equal_at_irreducible_neighborhood hD hDproper
      hE hR hED hRD haE haR hW haW hDW)

end NormalLocus
