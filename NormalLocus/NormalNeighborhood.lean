import NormalLocus.ExternalGeometry
import NormalLocus.OpenNormal

/-!
# The normal affine neighborhood construction from the manuscript

Only normal-locus openness and the stalk/component correspondence are external
inputs. Removing the other components, lifting the open to the ambient scheme,
and choosing an affine neighborhood are proved here.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace NormalLocus

theorem normal_affine_slices
    (normalOpen : External.NormalLocusOpen)
    (components : External.DomainPointUniqueComponent)
    (regularOpen : External.RegularOpenImmersion) : External.NormalAffineSlices := by
  intro S Y _ _ _ i _ hY hYregular y hy
  letI : IsAffine S := isAffine_of_isAffineHom i
  letI : IsLocallyNoetherian Y := hY.isLocallyNoetherian
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian i
  letI : AlgebraicGeometry.IsNoetherian S := ⟨⟩
  have hScomplex := hY.of_finiteType i
  obtain ⟨R, ⟨hR, hyR⟩, huniq⟩ := components S y hy.1
  let others : Set (Set S) := irreducibleComponents S \ {R}
  have hothers : IsClosed (⋃₀ others) := by
    rw [Set.sUnion_eq_biUnion]
    have hf : others.Finite := NoetherianSpace.finite_irreducibleComponents.diff
    exact hf.isClosed_biUnion (fun Q hQ ↦ isClosed_of_mem_irreducibleComponents Q hQ.1)
  have hyothers : y ∉ ⋃₀ others := by
    rintro ⟨Q, hQ, hyQ⟩
    exact hQ.2 (Set.mem_singleton_iff.mpr (huniq Q ⟨hQ.1, hyQ⟩))
  have hsubR : (⋃₀ others)ᶜ ⊆ R := by
    intro x hx
    by_cases he : irreducibleComponent x = R
    · simpa only [he] using (mem_irreducibleComponent (x := x))
    · exact (hx ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x,
          fun h ↦ he (Set.mem_singleton_iff.mp h)⟩,
        mem_irreducibleComponent (x := x)⟩).elim
  let Ω : Set S := normalPoints S ∩ (⋃₀ others)ᶜ
  have hΩopen : IsOpen Ω := (normalOpen S hScomplex).inter hothers.isOpen_compl
  have hyΩ : y ∈ Ω := ⟨hy, hyothers⟩
  have hΩR : Ω ⊆ R := fun _ hx ↦ hsubR hx.2
  have hΩirred : IsIrreducible Ω :=
    ⟨⟨y, hyΩ⟩, hR.1.2.open_subset hΩopen hΩR⟩
  obtain ⟨W, hW, hpre⟩ := i.isEmbedding.isInducing.isOpen_iff.mp hΩopen
  have hyW : i y ∈ W := by
    change y ∈ i ⁻¹' W
    rw [hpre]
    exact hyΩ
  obtain ⟨A, hA, hyA, hAW⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⟨W, hW⟩) hyW
  have hZΩ : (i ⁻¹ᵁ A : Set S) ⊆ Ω := by
    intro x hx
    rw [← hpre]
    exact hAW hx
  have hZirred : IsIrreducible (i ⁻¹ᵁ A : Set S) :=
    ⟨⟨y, hyA⟩, hΩirred.2.open_subset (i ⁻¹ᵁ A).isOpen hZΩ⟩
  letI : IrreducibleSpace (i ⁻¹ᵁ A).toScheme := Subtype.irreducibleSpace hZirred
  have hZnormal : normalPoints (i ⁻¹ᵁ A).toScheme = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (normal_point_openImmersion_iff (i ⁻¹ᵁ A).ι x).mpr (hZΩ x.2).1
  exact ⟨A, hyA, hA, isIntegral_of_irreducibleSpace_of_isReduced _, hZnormal,
    regularOpen A.toScheme Y A.ι hYregular⟩

theorem External.Library.normalSlices (H : External.Library) : External.NormalAffineSlices :=
  normal_affine_slices H.normalOpen H.domainComponents H.regularOpen

end NormalLocus
