import NormalLocus.AffineSlices

/-!
# The local-to-global normal-locus theorem from the external geometric library

Normal-locus openness is derived from the affine slices. Nonemptiness is
derived from density of the actual pullback image, and finiteness comes from
the local collision/Hartogs theorem. No local finite or surjective conclusion
is supplied as an external assumption to this theorem.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

theorem normal_locus_from_external_geometry
    (H : External.CoreGeometry) (slices : External.NormalAffineSlices)
    {X V Y S : Scheme.{0}} [IsAffine X] [IsAffine V] [IsAffine Y]
    [IsIntegral X] [IsIntegral V] [IsIntegral Y] [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsReduced S]
    (j : X ⟶ V) (π : V ⟶ Y) (i : S ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsFinite π]
    [IsDominant π] [Etale (j ≫ π)] [IsClosedImmersion i]
    (hY : External.ComplexAlgebraic Y)
    (hVnormal : normalPoints V = Set.univ)
    (hYregular : regularPoints Y = Set.univ)
    (hdivisor : IsDivisorUnion (Set.range i))
    (hboundary : (Set.range j)ᶜ ⊆ π ⁻¹' Set.range i)
    (hdense : Dense (Set.range (pullback.snd (j ≫ π) i))) :
    ∃ N : S.Opens, (N : Set S) = normalPoints S ∧
      AlgebraicGeometry.IsFinite (pullback.snd (j ≫ π) (N.ι ≫ i)) ∧
      Etale (pullback.snd (j ≫ π) (N.ι ≫ i)) ∧
      Surjective (pullback.snd (j ≫ π) (N.ι ≫ i)) := by
  let g := pullback.snd (j ≫ π) i
  have hcharts : ∀ y ∈ normalPoints S, ∃ U : S.Opens,
      y ∈ U ∧ (U : Set S) ⊆ normalPoints S ∧ IsIntegral U.toScheme ∧
        AlgebraicGeometry.IsFinite (g ∣_ U) := by
    intro y hy
    obtain ⟨A, hyA, hA, hZintegral, hZnormal, hAregular⟩ := slices S Y i hY hYregular y hy
    refine ⟨i ⁻¹ᵁ A, hyA, ?_, hZintegral,
      finite_on_normal_affine_slice H j π i hY hVnormal hdivisor hboundary
        A ⟨i y, hyA⟩ hA hZintegral hZnormal hAregular⟩
    intro x hx
    exact (normal_point_openImmersion_iff (i ⁻¹ᵁ A).ι ⟨x, hx⟩).mp
      (show (⟨x, hx⟩ : (i ⁻¹ᵁ A).toScheme) ∈ normalPoints (i ⁻¹ᵁ A).toScheme from
        hZnormal.symm ▸ Set.mem_univ _)
  have hopen : IsOpen (normalPoints S) := by
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨U, hyU, hU, _, _⟩ := hcharts y hy
    exact ⟨U, hU, U.isOpen, hyU⟩
  let N : S.Opens := ⟨normalPoints S, hopen⟩
  have hfinite : AlgebraicGeometry.IsFinite (g ∣_ N) := by
    apply finite_restriction_of_local g N
    intro y hy
    obtain ⟨U, hyU, hU, _, hfin⟩ := hcharts y hy
    exact ⟨U, hyU, hU, hfin⟩
  have hsurj : Function.Surjective (g ∣_ N) := by
    apply surjective_restriction_of_local g N
    intro y hy
    obtain ⟨U, hyU, _, hint, hfin⟩ := hcharts y hy
    letI := hint
    letI := hfin
    letI : Nonempty (g ⁻¹ᵁ U).toScheme :=
      preimage_nonempty_of_dense_image g hdense U ⟨y, hyU⟩
    exact ⟨U, hyU, finite_etale_surjective (g ∣_ U)⟩
  have e := restrictBaseChangeIso (j ≫ π) i N
  have hfinite' := (MorphismProperty.arrow_mk_iso_iff (@AlgebraicGeometry.IsFinite) e).mp hfinite
  have hsurj' := (MorphismProperty.arrow_mk_iso_iff (@Surjective) e).mp
    (show Surjective (g ∣_ N) from ⟨hsurj⟩)
  exact ⟨N, rfl, hfinite', inferInstance, hsurj'⟩

end NormalLocus
