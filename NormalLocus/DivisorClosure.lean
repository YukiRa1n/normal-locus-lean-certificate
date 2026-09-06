import NormalLocus.BoundaryCollision
import Mathlib.Topology.Closure

/-!
# Closing the interior divisors

This proves the construction of the interior divisor in the collision argument
from a finite decomposition of the pullback divisor on the source open.
-/

open Set Topology

namespace NormalLocus

/-- A finite union of actual topological prime divisors, including the empty union. -/
def IsDivisorUnion {X : Type*} [TopologicalSpace X] (S : Set X) : Prop :=
  ∃ E : Finset (Set X), (∀ e ∈ E, PrimeDivisor e) ∧ ⋃₀ (E : Set (Set X)) = S

theorem IsDivisorUnion.ne_univ
    {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    {S : Set X} (hS : IsDivisorUnion S) : S ≠ Set.univ := by
  obtain ⟨E, hE, hu⟩ := hS
  intro heq
  obtain ⟨e, he, hle⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ X) E (fun e he ↦ (hE e he).isClosed)
    (by rw [hu, heq])
  exact (hE e he).ne_univ (Set.univ_subset_iff.mp hle)

theorem IsDivisorUnion.image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) {S : Set X} (hS : IsDivisorUnion S)
    (hf : ∀ E : Set X, PrimeDivisor E → PrimeDivisor (f '' E)) :
    IsDivisorUnion (f '' S) := by
  classical
  obtain ⟨E, hE, hu⟩ := hS
  refine ⟨E.image (Set.image f), ?_, ?_⟩
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact hf d (hE d hd)
  · simp only [Finset.coe_image, ← Set.image_sUnion, hu]

theorem PrimeDivisor.closure_image
    {X V : Type*} [TopologicalSpace X] [TopologicalSpace V]
    {E : Set X} (hE : PrimeDivisor E) (j : X → V)
    (hj : IsOpenEmbedding j) (hd : DenseRange j) :
    PrimeDivisor (closure (j '' E)) := by
  have hpre : j ⁻¹' closure (j '' E) = E := by
    rw [← hj.isEmbedding.closure_eq_preimage_closure_image, hE.isClosed.closure_eq]
  refine ⟨isClosed_closure, (hE.isIrreducible.image j hj.continuous.continuousOn).closure,
    ?_, ?_⟩
  · intro he
    exact hE.ne_univ (by rw [← hpre, he, preimage_univ])
  · intro Q hQc hQi hEQ
    obtain ⟨x, hx⟩ := hE.isIrreducible.1
    have hmeet : (Q ∩ Set.range j).Nonempty :=
      ⟨j x, hEQ (subset_closure ⟨x, hx, rfl⟩), ⟨x, rfl⟩⟩
    have hpreQ : E ⊆ j ⁻¹' Q := fun x hx ↦ hEQ (subset_closure ⟨x, hx, rfl⟩)
    rcases hE.maximal (j ⁻¹' Q) (hQc.preimage hj.continuous)
      (hQi.preimage hj hmeet) hpreQ with heq | heq
    · left
      apply Set.Subset.antisymm
      · have h := subset_closure_inter_of_isPreirreducible_of_isOpen
          hQi.2 hj.isOpen_range hmeet
        rwa [← image_preimage_eq_inter_range, heq] at h
      · exact hEQ
    · right
      apply univ_subset_iff.mp
      rw [← hd.closure_range]
      apply closure_minimal _ hQc
      rintro _ ⟨x, rfl⟩
      change x ∈ j ⁻¹' Q
      rw [heq]
      trivial

theorem interior_divisor_through_closure_point
    {X V : Type*} [TopologicalSpace X] [TopologicalSpace V]
    (j : X → V) (hj : IsOpenEmbedding j) (hd : DenseRange j)
    {T : Set X} (hT : IsDivisorUnion T) {D : Set V} (hD : IsClosed D)
    (hTD : j '' T ⊆ D) {a : V} (ha : a ∈ closure (j '' T)) :
    ∃ R : Set V, PrimeDivisor R ∧ a ∈ R ∧
      (R ∩ Set.range j).Nonempty ∧ R ⊆ D := by
  obtain ⟨E, hE, hunion⟩ := hT
  have ha' : a ∈ ⋃ e ∈ E, closure (j '' e) := by
    rw [← Finset.closure_biUnion]
    have himage : j '' T = ⋃ e ∈ E, j '' e := by
      rw [← hunion, Set.image_sUnion, Set.sUnion_image]
      simp only [Finset.mem_coe]
    rw [← himage]
    exact ha
  obtain ⟨e, he, hae⟩ := Set.mem_iUnion₂.mp ha'
  have heT : e ⊆ T := hunion ▸ Set.subset_sUnion_of_mem he
  refine ⟨closure (j '' e), (hE e he).closure_image j hj hd, hae, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (hE e he).isIrreducible.1
    exact ⟨j x, subset_closure ⟨x, hx, rfl⟩, ⟨x, rfl⟩⟩
  · exact closure_minimal ((Set.image_mono heT).trans hTD) hD

theorem boundary_divisor_through_point
    {V : Type*} [TopologicalSpace V] {U D : Set V}
    (hboundary : IsDivisorUnion Uᶜ) (hD : Uᶜ ⊆ D)
    {a : V} (ha : a ∉ U) :
    ∃ E : Set V, PrimeDivisor E ∧ a ∈ E ∧ E ⊆ Uᶜ ∧ E ⊆ D := by
  obtain ⟨E, hE, hunion⟩ := hboundary
  have haU : a ∈ Uᶜ := ha
  rw [← hunion] at haU
  obtain ⟨e, he, hae⟩ := Set.mem_sUnion.mp haU
  have heU : e ⊆ Uᶜ := hunion ▸ Set.subset_sUnion_of_mem he
  exact ⟨e, hE e he, hae, heU, heU.trans hD⟩

theorem collision_from_divisor_decompositions
    {X V Y : Type*} [TopologicalSpace X] [TopologicalSpace V]
    (j : X → V) (p : V → Y) (hj : IsOpenEmbedding j) (hd : DenseRange j)
    (T : Set X) (D : Set V) (regular : Set Y)
    (hT : IsDivisorUnion T) (hboundary : IsDivisorUnion (Set.range j)ᶜ)
    (hD : IsClosed D) (hDproper : D ≠ univ)
    (hTD : j '' T ⊆ D) (hBD : (Set.range j)ᶜ ⊆ D)
    (localStructure : ∀ a ∈ D, p a ∈ regular →
      ∃ W : Set V, IsOpen W ∧ a ∈ W ∧ IsIrreducible (D ∩ W)) :
    p '' (closure (j '' T) \ Set.range j) ⊆ regularᶜ := by
  apply boundary_collision_exclusion p (Set.range j) (closure (j '' T)) D regular
    hD hDproper
  · intro a ha
    exact boundary_divisor_through_point hboundary hBD ha.2
  · intro a ha
    exact interior_divisor_through_closure_point j hj hd hT hD hTD ha
  · exact localStructure

end NormalLocus
