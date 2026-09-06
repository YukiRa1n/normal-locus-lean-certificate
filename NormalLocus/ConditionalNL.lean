import NormalLocus.ConditionalGlobal
import NormalLocus.PolynomialGeometry
import NormalLocus.NormalNeighborhood

/-!
# End-to-end conditional NL certificate

The target is exactly the original complex Keller normal-locus statement.
All additional hypotheses are the general propositions in `External.Library`.
They are explicit arguments, not axioms, and no theorem of the unconditional
target is asserted here.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

theorem normal_locus_finite_etale_conditional (external : External.Library) :
    NormalLocusTheorem := by
  intro n F hF
  letI : Etale (schemeMap F) := keller_schemeMap_etale F hF
  letI : LocallyQuasiFinite (schemeMap F) := keller_schemeMap_quasiFinite F hF
  letI : IsDominant (schemeMap F) := keller_schemeMap_dominant F hF
  letI : AlgebraicGeometry.IsFinite (schemeMap F).fromNormalization :=
    keller_canonical_normalization_finite F hF
  letI : IsAffine (schemeMap F).normalization :=
    isAffine_of_isAffineHom (schemeMap F).fromNormalization
  letI : IsLocallyNoetherian (schemeMap F).normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (schemeMap F).fromNormalization
  let j := (schemeMap F).toNormalization
  let π := (schemeMap F).fromNormalization
  let i := nonProperInclusion F
  have hfac : j ≫ π = schemeMap F := (schemeMap F).toNormalization_fromNormalization
  letI : IsDominant (j ≫ π) := hfac.symm ▸ inferInstance
  letI : Etale (j ≫ π) := hfac.symm ▸ inferInstance
  letI : IsDominant π := IsDominant.of_comp j π
  letI : IsClosedImmersion i := nonProperInclusion_isClosedImmersion F
  letI : AlgebraicGeometry.IsReduced (nonProperScheme F) := nonProperScheme_isReduced F
  have hdivisor : IsDivisorUnion (Set.range i) := by
    have hb := external.boundary _ _ j
    have hi := hb.image π (external.divisorImage _ _ π (polynomial_scheme_normal n))
    simpa only [i, range_nonProperInclusion, keller_nonProperLocus_eq_boundary_image F hF,
      j, π] using hi
  have hboundary : (Set.range j)ᶜ ⊆ π ⁻¹' Set.range i := by
    intro a ha
    change π a ∈ Set.range (nonProperInclusion F)
    rw [range_nonProperInclusion, keller_nonProperLocus_eq_boundary_image F hF]
    exact ⟨a, ha, rfl⟩
  have hdense : Dense (Set.range (pullback.snd (j ≫ π) i)) := by
    rw [hfac]
    exact dense_on_divisor_union (schemeMap F) i hdivisor
      (keller_hits_prime_divisor external.divisorEquations F hF)
  have hNL := normal_locus_from_external_geometry external.toCoreGeometry external.normalSlices
    j π i (polynomial_scheme_complexAlgebraic n)
    (polynomial_canonical_normalization_normal F) (external.affineRegular n)
    hdivisor hboundary hdense
  rw [hfac] at hNL
  simpa only [i, NormalLocusConclusion, restrictedMap] using hNL

end NormalLocus
