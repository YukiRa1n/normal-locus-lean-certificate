import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Local algebra relevant to the curve case

These results concern actual rings, integral closure, minimal prime ideals and
the cotangent space. They do not formalize the smoothness criterion for schemes
over a perfect field, nor the dimension of the non-properness set.
-/

namespace NormalLocus

/-- The local algebra behind normal = regular in dimension one.

The nonfield assumption excludes dimension zero. Under the other assumptions,
the cotangent dimension being one is exactly the regularity condition in
dimension one.
-/
theorem integrallyClosed_iff_cotangent_dimension_one
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] [Ring.DimensionLEOne R] (hfield : ¬ IsField R) :
    IsIntegrallyClosed R ↔
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 1 := by
  constructor
  · intro hnormal
    letI : IsDedekindDomain R :=
      { ‹IsDomain R›, ‹IsNoetherianRing R›, ‹Ring.DimensionLEOne R›, hnormal with }
    have hdvr : IsDiscreteValuationRing R :=
      ((IsDiscreteValuationRing.TFAE R hfield).out 2 0).mp ‹IsDedekindDomain R›
    exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mpr hdvr
  · intro hcotangent
    letI : IsDiscreteValuationRing R :=
      IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hcotangent
    infer_instance

/-- Distinct minimal primes cannot occur in a domain. -/
theorem minimal_primes_equal_in_domain
    {R : Type*} [CommRing R] [IsDomain R]
    {p q : Ideal R} (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R) : p = q := by
  rw [IsDomain.minimalPrimes_eq_singleton_bot] at hp hq
  exact (Set.mem_singleton_iff.mp hp).trans (Set.mem_singleton_iff.mp hq).symm

end NormalLocus
