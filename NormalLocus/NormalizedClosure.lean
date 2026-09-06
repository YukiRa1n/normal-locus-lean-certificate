import NormalLocus.BoundaryRemoval
import NormalLocus.ClosureFactorization

/-!
# Finite normalization pieces and the closure-equality deduction

The external normalization input is for an arbitrary reduced affine scheme
and a normal dense affine open. It supplies the usual normal components of the
finite normalization and its isomorphism over that open. It contains neither
the collision exclusion nor finiteness of the source map to the NL target.
-/

open CategoryTheory AlgebraicGeometry

namespace NormalLocus

structure NormalizationPiece {T C : Scheme.{0}} (j : T ⟶ C) where
  N : Scheme.{0}
  ν : N ⟶ C
  U : N.Opens
  e : U.toScheme ⟶ T
  comm : U.ι ≫ ν = e ≫ j
  preimage : ν ⁻¹' Set.range j = (U : Set N)
  affine : IsAffine N
  integral : IsIntegral N
  noetherian : IsLocallyNoetherian N
  noetherian_global : IsNoetherianRing Γ(N, ⊤)
  normal_global : IsIntegrallyClosed Γ(N, ⊤)
  finite : AlgebraicGeometry.IsFinite ν
  e_open : IsOpenImmersion e
  e_closed : IsClosedImmersion e
  open_nonempty : Nonempty U

namespace External

/-- Finite normalization, its normal integral components, and its identity
over a normal open (Stacks 0BXQ, 0357, 0H7D), in a pointwise component form.
The finite-type hypothesis is an actual structure morphism over `Spec ℂ`. -/
def NormalizationPieces : Prop :=
  ∀ (T C : Scheme.{0}) [IsAffine T] [IsAffine C]
    [IsLocallyNoetherian C] [AlgebraicGeometry.IsReduced C]
    (j : T ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [IsDominant j],
    normalPoints T = Set.univ → ComplexAlgebraic C →
    ∀ c : C, ∃ (P : NormalizationPiece j) (n : P.N), P.ν n = c

end External

theorem normalization_piece_covered
    (intersection : External.HeightOneIntersection)
    (dimension : External.FiniteLocalDimension)
    {T C Z : Scheme.{0}} [IsAffine T] [IsIntegral Z] [IsLocallyNoetherian Z]
    (j : T ⟶ C) (q : C ⟶ Z) [AlgebraicGeometry.IsFinite q] [Etale (j ≫ q)]
    (hnormal : normalPoints Z = Set.univ)
    (hcollision : q '' (Set.range j)ᶜ ⊆ (regularPoints Z)ᶜ)
    (P : NormalizationPiece j) : P.U = ⊤ := by
  letI := P.affine
  letI := P.integral
  letI := P.noetherian
  letI := P.noetherian_global
  letI := P.normal_global
  letI := P.finite
  letI := P.e_open
  letI := P.e_closed
  letI := P.open_nonempty
  letI : IsAffine P.U.toScheme := isAffine_of_isAffineHom P.e
  letI : Etale (P.U.ι ≫ (P.ν ≫ q)) := by
    rw [← Category.assoc, P.comm, Category.assoc]
    infer_instance
  letI : Nonempty P.U.toScheme := P.open_nonempty
  letI : IsDominant (P.U.ι ≫ (P.ν ≫ q)) := etale_isDominant _
  letI : IsDominant (P.ν ≫ q) := IsDominant.of_comp P.U.ι (P.ν ≫ q)
  apply affine_boundary_removal intersection dimension P.N Z (P.ν ≫ q)
    hnormal P.U (show IsAffineOpen P.U from (inferInstance : IsAffine P.U.toScheme))
  rintro _ ⟨n, hn, rfl⟩
  apply hcollision
  refine ⟨P.ν n, ?_, rfl⟩
  intro hnj
  have : n ∈ P.ν ⁻¹' Set.range j := hnj
  rw [P.preimage] at this
  exact hn this

theorem closure_equality_from_pieces
    (intersection : External.HeightOneIntersection)
    (dimension : External.FiniteLocalDimension)
    {T C Z : Scheme.{0}} [IsAffine T] [IsIntegral Z] [IsLocallyNoetherian Z]
    (j : T ⟶ C) (q : C ⟶ Z) [IsOpenImmersion j]
    [AlgebraicGeometry.IsFinite q] [Etale (j ≫ q)]
    (hnormal : normalPoints Z = Set.univ)
    (hcollision : q '' (Set.range j)ᶜ ⊆ (regularPoints Z)ᶜ)
    (pieces : ∀ c : C, ∃ (P : NormalizationPiece j) (n : P.N), P.ν n = c) :
    IsIso j ∧ AlgebraicGeometry.IsFinite (j ≫ q) := by
  have hj : Function.Surjective j := by
    intro c
    obtain ⟨P, n, hn⟩ := pieces c
    have hU := normalization_piece_covered intersection dimension j q hnormal hcollision P
    have hnU : n ∈ P.U := hU.symm ▸ Set.mem_univ n
    refine ⟨P.e ⟨n, hnU⟩, ?_⟩
    have he := congrArg (fun f : P.U.toScheme ⟶ C ↦ f ⟨n, hnU⟩) P.comm
    exact he.symm.trans hn
  letI : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr
    ⟨inferInstance, ⟨hj⟩⟩
  exact ⟨inferInstance, inferInstance⟩

end NormalLocus
