import NormalLocus.BoundaryImage
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Analysis.Complex.Basic

/-!
# The reduced non-properness scheme and the exact NL target

The final statement uses actual stalks, quotient rings, open subschemes, and
pullbacks. `NormalLocusTheorem` is a proposition to be proved, not a theorem
certificate. In particular its definition does not assert its truth.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

noncomputable section

def nonProperIdeal {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    Ideal (CoordinateRing n K) :=
  PrimeSpectrum.vanishingIdeal (nonProperLocus (schemeMap F))

def nonProperScheme {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) : Scheme :=
  Spec (CommRingCat.of (CoordinateRing n K ⧸ nonProperIdeal F))

def nonProperInclusion {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    nonProperScheme F ⟶ Spec (CommRingCat.of (CoordinateRing n K)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nonProperIdeal F)))

theorem nonProperScheme_isReduced {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    AlgebraicGeometry.IsReduced (nonProperScheme F) := by
  letI : _root_.IsReduced (CoordinateRing n K ⧸ nonProperIdeal F) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal _)
  unfold nonProperScheme
  infer_instance

theorem range_nonProperInclusion {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    Set.range (nonProperInclusion F) = nonProperLocus (schemeMap F) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (nonProperIdeal F))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  change PrimeSpectrum.zeroLocus (R := CoordinateRing n K)
    (PrimeSpectrum.vanishingIdeal (nonProperLocus (schemeMap F)) : Set (CoordinateRing n K)) = _
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    (nonProperLocus_isClosed (schemeMap F)).closure_eq]

theorem nonProperInclusion_isClosedImmersion
    {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    IsClosedImmersion (nonProperInclusion F) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Normal points are defined by their actual local rings. -/
def normalPoints (X : Scheme) : Set X :=
  { x | IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) }

def restrictedMap {n : ℕ} {K : Type*} [Field K]
    (F : PolynomialMap n K) (U : (nonProperScheme F).Opens) :
    pullback (schemeMap F) (U.ι ≫ nonProperInclusion F) ⟶ U :=
  pullback.snd _ _

/-- The etale part holds on every open subset of the non-properness scheme. -/
theorem keller_restrictedMap_etale {n : ℕ} {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) (U : (nonProperScheme F).Opens) :
    Etale (restrictedMap F U) := by
  letI : Etale (schemeMap F) := keller_schemeMap_etale F hF
  unfold restrictedMap
  infer_instance

/-- The exact scheme-level normal-locus conclusion, including existence of the
normal open locus. No finiteness or surjectivity is built into a hypothesis. -/
def NormalLocusConclusion {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) : Prop :=
  ∃ U : (nonProperScheme F).Opens,
    (U : Set (nonProperScheme F)) = normalPoints (nonProperScheme F) ∧
    AlgebraicGeometry.IsFinite (restrictedMap F U) ∧ Etale (restrictedMap F U) ∧
    Surjective (restrictedMap F U)

/-- Full manuscript target over the complex numbers. This declaration states
the goal; it is not a proof of the goal. -/
def NormalLocusTheorem : Prop :=
  ∀ (n : ℕ) (F : PolynomialMap n ℂ), IsKeller F → NormalLocusConclusion F

end

end NormalLocus
