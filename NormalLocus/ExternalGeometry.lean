import NormalLocus.DivisorClosure
import NormalLocus.NormalizedClosure

/-!
# General geometric inputs for the conditional composition proof

Every input is quantified over arbitrary schemes or divisors. None mentions a
Keller map, an interior closure, the boundary-collision conclusion, or finite
etaleness of the NL restriction. The Abhyankar input is its weaker local
topological consequence; the other inputs record standard normality and
codimension facts. They are propositions passed as arguments, not axioms.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus.External

def AffineBoundaryDivisors : Prop :=
  ∀ (X V : Scheme.{0}) [IsAffine X] [IsAffine V] [IsIntegral V]
    [IsLocallyNoetherian V] (j : X ⟶ V) [IsOpenImmersion j] [IsDominant j],
    IsDivisorUnion (Set.range j)ᶜ

def EtalePullbackDivisors : Prop :=
  ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Etale f] (D : Set Y),
    IsDivisorUnion D → IsDivisorUnion (f ⁻¹' D)

def FiniteDivisorImage : Prop :=
  ∀ (V Y : Scheme.{0}) [IsAffine V] [IsAffine Y] [IsIntegral V] [IsIntegral Y]
    [IsLocallyNoetherian V] [IsLocallyNoetherian Y]
    (π : V ⟶ Y) [AlgebraicGeometry.IsFinite π] [IsDominant π],
    normalPoints Y = Set.univ → ∀ E : Set V,
      PrimeDivisor E → PrimeDivisor (π '' E)

def EtalePreservesNormal : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Etale f],
    normalPoints Y = Set.univ → normalPoints X = Set.univ

/-- Local irreducibility of the reduced inverse divisor, as supplied by
Stacks 0EYH after shrinking around a regular point of the divisor. -/
def AbhyankarLocalIrreducibility : Prop :=
  ∀ (V Y Z : Scheme.{0}) [IsAffine V] [IsAffine Y]
    [IsIntegral V] [IsIntegral Y] [IsLocallyNoetherian V] [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsReduced Z]
    (π : V ⟶ Y) [AlgebraicGeometry.IsFinite π] [IsDominant π]
    (i : Z ⟶ Y) [IsClosedImmersion i],
    ComplexAlgebraic Y → normalPoints V = Set.univ →
    regularPoints Y = Set.univ → IsDivisorUnion (Set.range i) →
    (∀ U : Y.Opens, Disjoint (U : Set Y) (Set.range i) → Etale (π ∣_ U)) →
    ∀ (a : V) (z : Z), π a = i z → z ∈ regularPoints Z →
      ∃ W : V.Opens, a ∈ W ∧ IsIrreducible ((π ⁻¹' Set.range i) ∩ W)

/-- Height-one primes in a polynomial UFD define hypersurfaces. -/
def PolynomialPrimeDivisorEquation : Prop :=
  ∀ (n : ℕ) (E : Set (Spec (CommRingCat.of (CoordinateRing n ℂ)))),
    PrimeDivisor E → ∃ h : CoordinateRing n ℂ,
      (∀ c : ℂ, h ≠ MvPolynomial.C c) ∧ E = PrimeSpectrum.zeroLocus {h}

/-- Normal points of a reduced complex algebraic closed subscheme admit
normal integral ambient-affine slices. This is the general neighborhood
theorem, independent of any map whose nonproperness set is being studied. -/
def NormalAffineSlices : Prop :=
  ∀ (S Y : Scheme.{0}) [IsAffine Y] [IsIntegral Y]
    [AlgebraicGeometry.IsReduced S] (i : S ⟶ Y) [IsClosedImmersion i],
    ComplexAlgebraic Y → regularPoints Y = Set.univ →
    ∀ y : S, y ∈ normalPoints S → ∃ U : Y.Opens,
      i y ∈ U ∧ IsAffineOpen U ∧
      IsIntegral (i ⁻¹ᵁ U).toScheme ∧
      normalPoints (i ⁻¹ᵁ U).toScheme = Set.univ ∧
      regularPoints U.toScheme = Set.univ

/-- The external library boundary of the local combination proof. -/
structure CoreGeometry : Prop where
  intersection : HeightOneIntersection
  dimension : FiniteLocalDimension
  normalization : NormalizationPieces
  boundary : AffineBoundaryDivisors
  etaleDivisors : EtalePullbackDivisors
  etaleNormal : EtalePreservesNormal
  abhyankar : AbhyankarLocalIrreducibility

/-- Polynomial affine space is regular at every actual scheme point. -/
def AffineSpaceRegular : Prop :=
  ∀ n : ℕ, regularPoints (Spec (CommRingCat.of (CoordinateRing n ℂ))) = Set.univ

def NormalLocusOpen : Prop :=
  ∀ (S : Scheme.{0}) [AlgebraicGeometry.IsReduced S],
    ComplexAlgebraic S → IsOpen (normalPoints S)

/-- Irreducible components through a point correspond to minimal primes of
its local ring; a domain has exactly one such component. -/
def DomainPointUniqueComponent : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (x : S),
    IsDomain (S.presheaf.stalk x) →
    ∃! R : Set S, R ∈ irreducibleComponents S ∧ x ∈ R

def RegularOpenImmersion : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsOpenImmersion f],
    regularPoints Y = Set.univ → regularPoints X = Set.univ

/-- All explicitly declared external inputs to the end-to-end conditional theorem. -/
structure Library : Prop extends CoreGeometry where
  divisorImage : FiniteDivisorImage
  divisorEquations : PolynomialPrimeDivisorEquation
  affineRegular : AffineSpaceRegular
  normalOpen : NormalLocusOpen
  domainComponents : DomainPointUniqueComponent
  regularOpen : RegularOpenImmersion

end NormalLocus.External
