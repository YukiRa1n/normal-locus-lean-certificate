import NormalLocus
import Lean

open Lean Elab Command

/-- Reject every nonstandard axiom, including ones hidden in transitive dependencies. -/
elab "#audit_axioms " decl:ident : command => do
  let name := decl.getId
  let info ← getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "{name} is not a theorem declaration"
  let axioms ← collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let extra := axioms.filter fun ax => !allowed.contains ax
  unless extra.isEmpty do
    throwError "{name} has nonstandard axioms: {extra}"
  logInfo m!"{name}: standard axioms only: {axioms}"

/-- A complete certificate must have exactly the frozen mathematical target,
and its proof may only use the standard logical axioms. -/
elab "#audit_full_nl" : command => do
  let name := `NormalLocus.normal_locus_finite_etale
  if !(← getEnv).contains name then
    logInfo "FULL_NL_INCOMPLETE: no theorem certificate for the exact NL target"
    return
  let info ← getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "The NL certificate must be a theorem, not a definition or axiom"
  let typeMatches ← liftTermElabM do
    Meta.isDefEq info.type (mkConst `NormalLocus.NormalLocusTheorem)
  unless typeMatches do
    throwError "The NL certificate does not have the exact NormalLocusTheorem type"
  let axioms ← collectAxioms name
  let extra := axioms.filter fun ax =>
    !#[``propext, ``Classical.choice, ``Quot.sound].contains ax
  unless extra.isEmpty do
    throwError "The NL certificate has nonstandard axioms: {extra}"
  logInfo "FULL_NL_VERIFIED: exact target and standard axioms checked"

/-- Check that the external interface has no hidden dependency on the Keller
condition, nonproperness locus, or the NL conclusion. Only project constants
need traversal: mathlib cannot refer back to this project. -/
def auditExternalInterface : CommandElabM Unit := do
  let forbidden := #[`NormalLocus.PolynomialMap, `NormalLocus.IsKeller,
    `NormalLocus.schemeMap, `NormalLocus.nonProperLocus,
    `NormalLocus.nonProperScheme, `NormalLocus.restrictedMap,
    `NormalLocus.NormalLocusConclusion, `NormalLocus.NormalLocusTheorem]
  let mut pending := #[`NormalLocus.External.Library]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then
      throwError "External interface contains NL-specific dependency: {name}"
    let info ← getConstInfo name
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? then
      deps := deps ++ value.getUsedConstants
    if let .inductInfo value := info then
      deps := deps ++ value.ctors.toArray
    for dep in deps do
      if (`NormalLocus).isPrefixOf dep then pending := pending.push dep
  logInfo "EXTERNAL_INTERFACE_CHECKED: no Keller or NL-specific dependencies"

/-- The composition certificate proves Library → the exact original NL target.
It must not gain a local-finiteness assumption or the desired conclusion. -/
elab "#audit_conditional_nl" : command => do
  let name := `NormalLocus.normal_locus_finite_etale_conditional
  if !(← getEnv).contains name then
    logInfo "CONDITIONAL_NL_INCOMPLETE: no composition certificate"
    return
  let info ← getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "The composition certificate must be a theorem"
  let typeMatches ← liftTermElabM do
    let expected ← mkArrow (mkConst `NormalLocus.External.Library)
      (mkConst `NormalLocus.NormalLocusTheorem)
    Meta.isDefEq info.type expected
  unless typeMatches do
    throwError "The composition certificate does not have the exact Library → NL type"
  let axioms ← collectAxioms name
  let extra := axioms.filter fun ax =>
    !#[``propext, ``Classical.choice, ``Quot.sound].contains ax
  unless extra.isEmpty do
    throwError "The composition certificate has nonstandard axioms: {extra}"
  auditExternalInterface
  logInfo "CONDITIONAL_NL_VERIFIED: exact Library → NL target and standard axioms checked"

#audit_axioms NormalLocus.surjective_of_open_closed
#audit_axioms NormalLocus.finite_etale_surjective
#audit_axioms NormalLocus.exists_zero_of_not_isUnit
#audit_axioms NormalLocus.substitution_not_isUnit
#audit_axioms NormalLocus.dominant_hits_hypersurface
#audit_axioms NormalLocus.integrallyClosed_iff_cotangent_dimension_one
#audit_axioms NormalLocus.minimal_primes_equal_in_domain
#audit_axioms NormalLocus.nonProperLocus_isClosed
#audit_axioms NormalLocus.preimage_exists_outside_nonProperLocus
#audit_axioms NormalLocus.missing_subset_nonProperLocus
#audit_axioms NormalLocus.etale_isDominant
#audit_axioms NormalLocus.etale_missing_subset_nonProperLocus
#audit_axioms NormalLocus.integral_element_lifts_to_normal_source
#audit_axioms NormalLocus.relative_integralClosure_map_eq
#audit_axioms NormalLocus.finite_normal_source_isIntegralClosure
#audit_axioms NormalLocus.finite_normal_source_range_eq_integralClosure
#audit_axioms NormalLocus.canonical_integral_completion
#audit_axioms NormalLocus.finite_of_proper_quasiFinite
#audit_axioms NormalLocus.graphEval_section
#audit_axioms NormalLocus.graphEval_relation
#audit_axioms NormalLocus.graph_relation_span_eq_ker
#audit_axioms NormalLocus.graphPrePresentation_jacobian
#audit_axioms NormalLocus.keller_ringHom_etale
#audit_axioms NormalLocus.keller_schemeMap_etale
#audit_axioms NormalLocus.keller_ringHom_quasiFinite
#audit_axioms NormalLocus.keller_schemeMap_quasiFinite
#audit_axioms NormalLocus.keller_schemeMap_dominant
#audit_axioms NormalLocus.keller_substitution_injective
#audit_axioms NormalLocus.keller_hits_hypersurface
#audit_axioms NormalLocus.keller_missing_subset_nonProperLocus
#audit_axioms NormalLocus.rational_preimage_of_scheme_preimage
#audit_axioms NormalLocus.keller_rational_preimage_outside_nonProperLocus
#audit_axioms NormalLocus.finite_relative_integralClosure
#audit_axioms NormalLocus.finite_relative_integralClosure_of_quasiFinite
#audit_axioms NormalLocus.keller_relative_integralClosure_finite
#audit_axioms NormalLocus.keller_integralClosure_SpecMap_finite
#audit_axioms NormalLocus.keller_polynomial_missing_subset
#audit_axioms NormalLocus.finite_fromNormalization_of_finite_integralClosure_top
#audit_axioms NormalLocus.canonical_normalization_finite
#audit_axioms NormalLocus.keller_canonical_normalization_finite
#audit_axioms NormalLocus.keller_canonical_finite_completion
#audit_axioms NormalLocus.proper_restriction_iff_preimage_subset_range
#audit_axioms NormalLocus.boundary_image_eq_nonProperLocus
#audit_axioms NormalLocus.keller_nonProperLocus_eq_boundary_image
#audit_axioms NormalLocus.nonProperScheme_isReduced
#audit_axioms NormalLocus.range_nonProperInclusion
#audit_axioms NormalLocus.nonProperInclusion_isClosedImmersion
#audit_axioms NormalLocus.keller_restrictedMap_etale
#audit_axioms NormalLocus.relative_integralClosure_isIntegrallyClosed
#audit_axioms NormalLocus.normalPoints_eq_univ_of_affine
#audit_axioms NormalLocus.canonical_normalization_normalPoints_eq_univ
#audit_axioms NormalLocus.polynomial_canonical_normalization_normal
#audit_axioms NormalLocus.keller_canonical_finite_normal_completion
#audit_axioms NormalLocus.KummerChart.parameter_pow
#audit_axioms NormalLocus.KummerChart.finite_free
#audit_axioms NormalLocus.KummerChart.parameter_isRegular
#audit_axioms NormalLocus.KummerChart.quotient_equiv_exists
#audit_axioms NormalLocus.KummerChart.parameterIdeal_isRadical
#audit_axioms NormalLocus.KummerChart.parameterIdeal_isPrime
#audit_axioms NormalLocus.KummerChart.radical_baseIdeal
#audit_axioms NormalLocus.normal_height_one_localization_isDVR
#audit_axioms NormalLocus.normal_height_one_cotangent_dimension
#audit_axioms NormalLocus.External.ComplexAlgebraic.of_finiteType
#audit_axioms NormalLocus.External.ComplexAlgebraic.isLocallyNoetherian
#audit_axioms NormalLocus.surjective_of_local_surjective
#audit_axioms NormalLocus.finite_etale_surjective_of_local
#audit_axioms NormalLocus.etale_preimage_open_nonempty
#audit_axioms NormalLocus.etale_pullback_open_nonempty
#audit_axioms NormalLocus.affine_hartogs_restriction_bijective
#audit_axioms NormalLocus.affine_hartogs
#audit_axioms NormalLocus.prime_divisors_equal_at_irreducible_neighborhood
#audit_axioms NormalLocus.boundary_divisor_ne_interior
#audit_axioms NormalLocus.boundary_collision_exclusion
#audit_axioms NormalLocus.image_isReduced_of_affine
#audit_axioms NormalLocus.image_inclusion_range
#audit_axioms NormalLocus.preimage_source_eq_range_toImage
#audit_axioms NormalLocus.finite_closure_factorization
#audit_axioms NormalLocus.closure_openImmersion_isIso_of_normalization_covered
#audit_axioms NormalLocus.finite_of_normalization_covered
#audit_axioms NormalLocus.normal_local_ring_dimension_one_regular
#audit_axioms NormalLocus.normal_point_dimension_one_regular
#audit_axioms NormalLocus.height_one_points_avoid_boundary
#audit_axioms NormalLocus.affine_boundary_removal
#audit_axioms NormalLocus.boundary_image_under_normalization
#audit_axioms NormalLocus.IsDivisorUnion.ne_univ
#audit_axioms NormalLocus.IsDivisorUnion.image
#audit_axioms NormalLocus.PrimeDivisor.closure_image
#audit_axioms NormalLocus.interior_divisor_through_closure_point
#audit_axioms NormalLocus.boundary_divisor_through_point
#audit_axioms NormalLocus.collision_from_divisor_decompositions
#audit_axioms NormalLocus.normalization_piece_covered
#audit_axioms NormalLocus.closure_equality_from_pieces
#audit_axioms NormalLocus.normal_point_openImmersion_iff
#audit_axioms NormalLocus.normalPoints_openImmersion
#audit_axioms NormalLocus.normalPoints_isReduced
#audit_axioms NormalLocus.LocalModel.l_q
#audit_axioms NormalLocus.LocalModel.q_i
#audit_axioms NormalLocus.LocalModel.toZ_etale
#audit_axioms NormalLocus.LocalModel.range_cV
#audit_axioms NormalLocus.LocalModel.preimage_source
#audit_axioms NormalLocus.LocalModel.finite_actual_pullback_of_finite_model
#audit_axioms NormalLocus.completion_etale_restriction
#audit_axioms NormalLocus.completion_etale_outside_divisor
#audit_axioms NormalLocus.local_restriction_finite
#audit_axioms NormalLocus.keller_hits_prime_divisor
#audit_axioms NormalLocus.dense_on_divisor_union
#audit_axioms NormalLocus.preimage_nonempty_of_dense_image
#audit_axioms NormalLocus.range_morphismRestrict
#audit_axioms NormalLocus.finite_restriction_of_local
#audit_axioms NormalLocus.surjective_restriction_of_local
#audit_axioms NormalLocus.completion_boundary_restriction
#audit_axioms NormalLocus.finite_on_normal_affine_slice
#audit_axioms NormalLocus.normal_locus_from_external_geometry
#audit_axioms NormalLocus.polynomial_scheme_normal
#audit_axioms NormalLocus.polynomial_scheme_complexAlgebraic
#audit_axioms NormalLocus.normal_affine_slices
#audit_axioms NormalLocus.External.Library.normalSlices
#audit_axioms NormalLocus.normal_locus_finite_etale_conditional
