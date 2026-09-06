import NormalLocus.ExternalGeometry
import NormalLocus.LocalToGlobal
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Nonemptiness on every nonempty open of the nonproperness divisor

The only external input to the polynomial step is that prime divisors of
affine space are hypersurfaces. The Keller non-omission theorem is already
proved, and the density and open-neighborhood deductions are proved here.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

namespace NormalLocus

theorem keller_hits_prime_divisor
    (equations : External.PolynomialPrimeDivisorEquation)
    {n : ℕ} (F : PolynomialMap n ℂ) (hF : IsKeller F)
    (E : Set (Spec (CommRingCat.of (CoordinateRing n ℂ)))) (hE : PrimeDivisor E) :
    (E ∩ Set.range (schemeMap F)).Nonempty := by
  obtain ⟨h, hc, rfl⟩ := equations n E hE
  obtain ⟨x, hx⟩ := keller_hits_hypersurface F hF h hc
  refine ⟨schemeMap F (MvPolynomial.pointToPoint (k := ℂ) x), ?_, ⟨_, rfl⟩⟩
  change {h} ⊆ ((schemeMap F (MvPolynomial.pointToPoint (k := ℂ) x)).asIdeal :
    Set (CoordinateRing n ℂ))
  rw [Set.singleton_subset_iff]
  change MvPolynomial.aeval F h ∈ MvPolynomial.vanishingIdeal ℂ {x}
  intro z hz
  have hzx : z = x := Set.mem_singleton_iff.mp hz
  subst z
  have hcomp : (MvPolynomial.eval x).comp (MvPolynomial.aeval (R := ℂ) F).toRingHom =
      MvPolynomial.eval (evaluate F x) := by
    ext a <;> simp [evaluate]
  change ((MvPolynomial.eval x).comp (MvPolynomial.aeval (R := ℂ) F).toRingHom) h = 0
  rw [hcomp]
  exact hx

theorem dense_on_divisor_union
    {X Y S : Scheme} (f : X ⟶ Y) (i : S ⟶ Y) [Etale f] [IsClosedImmersion i]
    (hD : IsDivisorUnion (Set.range i))
    (hhit : ∀ E : Set Y, PrimeDivisor E → (E ∩ Set.range f).Nonempty) :
    Dense (Set.range (pullback.snd f i)) := by
  rw [Scheme.Pullback.range_snd]
  apply i.isEmbedding.isInducing.dense_iff.mpr
  intro s
  obtain ⟨E, hE, hu⟩ := hD
  have his : i s ∈ ⋃₀ (E : Set (Set Y)) := hu.symm ▸ Set.mem_range_self s
  obtain ⟨e, he, hse⟩ := Set.mem_sUnion.mp his
  have heD : e ⊆ Set.range i := hu ▸ Set.subset_sUnion_of_mem he
  have hd := subset_closure_inter_of_isPreirreducible_of_isOpen
    (hE e he).isIrreducible.2 f.isOpenMap.isOpen_range (hhit e (hE e he)) hse
  apply closure_mono _ hd
  rw [Set.image_preimage_eq_inter_range]
  rintro y ⟨hye, hyf⟩
  exact ⟨hyf, heD hye⟩

theorem preimage_nonempty_of_dense_image
    {X Y : Scheme} (f : X ⟶ Y) (hd : Dense (Set.range f))
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) :
    Nonempty ↥((f ⁻¹ᵁ U).toScheme) := by
  obtain ⟨y, hyU, hyf⟩ := hd.inter_open_nonempty (U : Set Y) U.isOpen hU
  obtain ⟨x, rfl⟩ := hyf
  exact ⟨⟨x, hyU⟩⟩

end NormalLocus
