import NormalLocus.Polynomial
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import NormalLocus.NonProper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# The graph presentation in `prop:keller-etale`

The relations are F_i(x) - y_i in K[y][x]. Their ideal is proved to be the
kernel of evaluation; it is not supplied as an assumption.
-/

open MvPolynomial

namespace NormalLocus

noncomputable section

variable {n : ℕ} {K : Type*} [CommRing K]

abbrev CoordinateRing (n : ℕ) (K : Type*) [CommRing K] := MvPolynomial (Fin n) K

def graphSection : CoordinateRing n K →+* MvPolynomial (Fin n) (CoordinateRing n K) :=
  MvPolynomial.map MvPolynomial.C

def graphEval (F : PolynomialMap n K) :
    MvPolynomial (Fin n) (CoordinateRing n K) →+* CoordinateRing n K :=
  MvPolynomial.eval₂Hom (aeval F).toRingHom X

def graphRelation (F : PolynomialMap n K) (i : Fin n) :
    MvPolynomial (Fin n) (CoordinateRing n K) :=
  graphSection (F i) - C (X i)

theorem graphEval_section (F : PolynomialMap n K) (p : CoordinateRing n K) :
    graphEval F (graphSection p) = p := by
  have heq : (graphEval F).comp graphSection = RingHom.id _ := by
    ext i <;> simp [graphEval, graphSection]
  exact congrArg (fun f : CoordinateRing n K →+* CoordinateRing n K => f p) heq

theorem graphEval_relation (F : PolynomialMap n K) (i : Fin n) :
    graphEval F (graphRelation F i) = 0 := by
  rw [graphRelation, map_sub, graphEval_section]
  simp [graphEval]

theorem graph_relation_span_eq_ker (F : PolynomialMap n K) :
    Ideal.span (Set.range (graphRelation F)) = RingHom.ker (graphEval F) := by
  let I := Ideal.span (Set.range (graphRelation F))
  let q := Ideal.Quotient.mk I
  have hcoeff : (q.comp graphSection).comp (aeval F).toRingHom = q.comp C := by
    ext i
    · simp [graphSection]
    · change q (graphSection (aeval F (X i))) = q (C (X i))
      rw [aeval_X]
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hfactor : (q.comp graphSection).comp (graphEval F) = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [graphEval] using congrArg (fun h : CoordinateRing n K →+*
        MvPolynomial (Fin n) (CoordinateRing n K) ⧸ I => h r) hcoeff
    · intro i
      simp [graphEval, graphSection]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact graphEval_relation F i
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have heq := congrArg (fun f : MvPolynomial (Fin n) (CoordinateRing n K) →+*
        MvPolynomial (Fin n) (CoordinateRing n K) ⧸ I => f p) hfactor
    change graphEval F p = 0 at hp
    simpa [hp] using heq.symm

def graphAlgebra (F : PolynomialMap n K) :
    Algebra (CoordinateRing n K) (CoordinateRing n K) :=
  (aeval F).toRingHom.toAlgebra

def graphPrePresentation (F : PolynomialMap n K) :
    letI := graphAlgebra F
    Algebra.PreSubmersivePresentation (CoordinateRing n K) (CoordinateRing n K)
      (Fin n) (Fin n) := by
  letI := graphAlgebra F
  let G : Algebra.Generators (CoordinateRing n K) (CoordinateRing n K) (Fin n) := {
    val := X
    σ' := graphSection
    aeval_val_σ' := graphEval_section F
  }
  exact {
    toGenerators := G
    relation := graphRelation F
    span_range_relation_eq_ker := by
      rw [G.ker_eq_ker_aeval_val]
      exact graph_relation_span_eq_ker F
    map := id
    map_inj := Function.injective_id
  }

theorem graphPrePresentation_jacobian (F : PolynomialMap n K) :
    letI := graphAlgebra F
    (graphPrePresentation F).jacobian = (jacobian F).det := by
  letI := graphAlgebra F
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, RingHom.map_det]
  have hmatrix :
      (algebraMap (graphPrePresentation F).Ring (CoordinateRing n K)).mapMatrix
        (graphPrePresentation F).jacobiMatrix = (jacobian F).transpose := by
    ext i j : 1
    change (algebraMap (graphPrePresentation F).Ring (CoordinateRing n K))
      ((graphPrePresentation F).jacobiMatrix i j) = pderiv i (F j)
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    change graphEval F (pderiv i (graphRelation F j)) = pderiv i (F j)
    rw [graphRelation, map_sub, pderiv_C, sub_zero]
    change graphEval F (pderiv i (MvPolynomial.map C (F j))) = pderiv i (F j)
    rw [pderiv_map]
    exact graphEval_section F _
  rw [hmatrix, Matrix.det_transpose]

theorem keller_ringHom_etale {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) : (aeval (R := K) F).toRingHom.Etale := by
  letI := graphAlgebra F
  let P : Algebra.SubmersivePresentation (CoordinateRing n K) (CoordinateRing n K)
      (Fin n) (Fin n) := {
    toPreSubmersivePresentation := graphPrePresentation F
    jacobian_isUnit := by
      rw [graphPrePresentation_jacobian]
      obtain ⟨c, hc, hdet⟩ := hF
      rw [hdet]
      exact (isUnit_iff_ne_zero.mpr hc).map C
  }
  have hdim : P.dimension = 0 := by
    change Nat.card (Fin n) - Nat.card (Fin n) = 0
    exact Nat.sub_self _
  letI := P.isStandardSmoothOfRelativeDimension hdim
  change Algebra.Etale (CoordinateRing n K) (CoordinateRing n K)
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr inferInstance

open CategoryTheory AlgebraicGeometry in
def schemeMap (F : PolynomialMap n K) :
    Spec (CommRingCat.of (CoordinateRing n K)) ⟶ Spec (CommRingCat.of (CoordinateRing n K)) :=
  Spec.map (CommRingCat.ofHom (aeval F).toRingHom)

open CategoryTheory AlgebraicGeometry in
theorem keller_schemeMap_etale {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) : Etale (schemeMap F) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact keller_ringHom_etale F hF

theorem keller_ringHom_quasiFinite {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    (aeval (R := K) F).toRingHom.QuasiFinite := by
  letI := graphAlgebra F
  letI : Algebra.Etale (CoordinateRing n K) (CoordinateRing n K) := keller_ringHom_etale F hF
  change Algebra.QuasiFinite (CoordinateRing n K) (CoordinateRing n K)
  infer_instance

open CategoryTheory AlgebraicGeometry in
theorem keller_schemeMap_quasiFinite {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) : LocallyQuasiFinite (schemeMap F) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr
  exact keller_ringHom_quasiFinite F hF

open CategoryTheory AlgebraicGeometry in
theorem keller_schemeMap_dominant {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) : IsDominant (schemeMap F) := by
  letI : Etale (schemeMap F) := keller_schemeMap_etale F hF
  exact etale_isDominant (schemeMap F)

open CategoryTheory AlgebraicGeometry in
theorem keller_substitution_injective {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    Function.Injective (aeval (R := K) F) := by
  have hdense := (keller_schemeMap_dominant F hF).denseRange
  change DenseRange (PrimeSpectrum.comap (aeval F).toRingHom) at hdense
  have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (aeval F).toRingHom).mp hdense
  apply (RingHom.injective_iff_ker_eq_bot (aeval (R := K) F).toRingHom).mpr
  simpa [nilradical_eq_zero] using hker

/-- The non-omission conclusion now follows from the Keller condition alone. -/
theorem keller_hits_hypersurface {K : Type*} [Field K] [IsAlgClosed K]
    (F : PolynomialMap n K) (hF : IsKeller F)
    (h : CoordinateRing n K) (hconstant : ∀ c : K, h ≠ C c) :
    ∃ x : Fin n → K, MvPolynomial.eval (evaluate F x) h = 0 :=
  dominant_hits_hypersurface F (keller_substitution_injective F hF) h hconstant

open CategoryTheory AlgebraicGeometry in
theorem keller_missing_subset_nonProperLocus {K : Type*} [Field K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    (Set.range (schemeMap F))ᶜ ⊆ nonProperLocus (schemeMap F) := by
  letI : IsDominant (schemeMap F) := keller_schemeMap_dominant F hF
  exact missing_subset_nonProperLocus (schemeMap F)

open CategoryTheory AlgebraicGeometry in
/-- A scheme preimage of a rational target point yields a rational preimage over
an algebraically closed field. This supplies the point-level interface in TeX. -/
theorem rational_preimage_of_scheme_preimage {K : Type*} [Field K] [IsAlgClosed K]
    (F : PolynomialMap n K) (y : Fin n → K)
    (hy : MvPolynomial.pointToPoint (k := K) y ∈ Set.range (schemeMap F)) :
    ∃ x : Fin n → K, evaluate F x = y := by
  obtain ⟨p, hp⟩ := hy
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hm
  refine ⟨x, funext fun i => ?_⟩
  have hrel : aeval F (X i - C (y i)) ∈ p.asIdeal := by
    change X i - C (y i) ∈ (schemeMap F p).asIdeal
    rw [hp]
    simp [MvPolynomial.pointToPoint]
  have hzero := (show aeval F (X i - C (y i)) ∈ MvPolynomial.vanishingIdeal K {x}
    from hx ▸ hpm hrel) x (Set.mem_singleton x)
  simpa [evaluate, sub_eq_zero] using hzero

open CategoryTheory AlgebraicGeometry in
/-- The manuscript's non-omission statement for rational points, from the actual
Keller condition and the actual scheme-theoretic non-properness definition. -/
theorem keller_rational_preimage_outside_nonProperLocus {K : Type*}
    [Field K] [IsAlgClosed K] (F : PolynomialMap n K) (hF : IsKeller F) (y : Fin n → K)
    (hy : MvPolynomial.pointToPoint (k := K) y ∉ nonProperLocus (schemeMap F)) :
    ∃ x : Fin n → K, evaluate F x = y := by
  letI : IsDominant (schemeMap F) := keller_schemeMap_dominant F hF
  exact rational_preimage_of_scheme_preimage F y
    (preimage_exists_outside_nonProperLocus (schemeMap F) _ hy)

/-- The non-properness locus as a set of field-valued points. -/
def polynomialNonProperLocus {K : Type*} [Field K] (F : PolynomialMap n K) : Set (Fin n → K) :=
  (MvPolynomial.pointToPoint (k := K)) ⁻¹' nonProperLocus (schemeMap F)

/-- The complete field-valued-point version of Miss(F) ⊆ S_F. -/
theorem keller_polynomial_missing_subset {K : Type*} [Field K] [IsAlgClosed K]
    (F : PolynomialMap n K) (hF : IsKeller F) :
    (Set.range (evaluate F))ᶜ ⊆ polynomialNonProperLocus F := by
  classical
  intro y hy
  by_contra hnot
  exact hy (keller_rational_preimage_outside_nonProperLocus F hF y hnot)

end

end NormalLocus
