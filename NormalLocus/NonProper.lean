import NormalLocus.FiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Non-properness as defined in the manuscript

Source: `def:nonproperness`, `prop:boundary-image`, and the last paragraph of
`prop:keller-etale` in Normal_Loci_Keller_Maps_v1.tex.

All points below are scheme points. `KellerEtale.lean` supplies the interface to
field-valued points over an algebraically closed field via the Nullstellensatz.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

/-- A point is non-proper if there is no target-open neighborhood over which
the restricted scheme morphism is proper. This is not defined using its image. -/
def nonProperLocus {X Y : Scheme} (f : X ⟶ Y) : Set Y :=
  { y | ¬ ∃ U : Y.Opens, y ∈ U ∧ IsProper (f ∣_ U) }

theorem nonProperLocus_isClosed {X Y : Scheme} (f : X ⟶ Y) :
    IsClosed (nonProperLocus f) := by
  classical
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨U, hyU, hU⟩ : ∃ U : Y.Opens, y ∈ U ∧ IsProper (f ∣_ U) := by
    simpa only [nonProperLocus, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hy
  exact Filter.mem_of_superset (U.isOpen.mem_nhds hyU) fun z hz =>
    fun hbad => hbad ⟨U, hz, hU⟩

/-- Dominance plus local properness forces an actual preimage.

This proves the scheme-point content of the old
`proper_outside_nonproper_surjective` interface without assuming it as an axiom.
-/
theorem preimage_exists_outside_nonProperLocus
    {X Y : Scheme} (f : X ⟶ Y) [IsDominant f]
    (y : Y) (hy : y ∉ nonProperLocus f) : ∃ x : X, f x = y := by
  classical
  obtain ⟨U, hyU, hU⟩ : ∃ U : Y.Opens, y ∈ U ∧ IsProper (f ∣_ U) := by
    simpa only [nonProperLocus, Set.mem_setOf_eq, not_not] using hy
  letI : IsProper (f ∣_ U) := hU
  letI : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsDominant f› U
  obtain ⟨x, hx⟩ := (f ∣_ U).surjective ⟨y, hyU⟩
  refine ⟨x.1, ?_⟩
  have hx' := congrArg (fun p => U.ι p) hx
  have hcomm := congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ Y => g x)
    (morphismRestrict_ι f U)
  simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hcomm hx'
  exact hcomm.symm.trans hx'

/-- Missing scheme points lie in the non-properness locus. -/
theorem missing_subset_nonProperLocus
    {X Y : Scheme} (f : X ⟶ Y) [IsDominant f] :
    (Set.range f)ᶜ ⊆ nonProperLocus f := by
  classical
  intro y hy
  by_contra hnot
  exact hy (preimage_exists_outside_nonProperLocus f y hnot)

/-- The topological dominance argument in `prop:keller-etale`. -/
theorem etale_isDominant
    {X Y : Scheme} (f : X ⟶ Y) [Etale f]
    [Nonempty X] [PreirreducibleSpace Y] : IsDominant f := by
  exact ⟨f.isOpenMap.isOpen_range.dense (Set.range_nonempty f)⟩

/-- The non-omission statement for etale maps to an irreducible target. -/
theorem etale_missing_subset_nonProperLocus
    {X Y : Scheme} (f : X ⟶ Y) [Etale f]
    [Nonempty X] [PreirreducibleSpace Y] :
    (Set.range f)ᶜ ⊆ nonProperLocus f := by
  letI : IsDominant f := etale_isDominant f
  exact missing_subset_nonProperLocus f

end NormalLocus
