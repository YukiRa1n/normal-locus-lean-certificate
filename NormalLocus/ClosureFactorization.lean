import NormalLocus.LocalToGlobal
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The closure factorization

The closure is taken inside the finite pullback over `Z`. Its finite map to `Z`
therefore exists scheme-theoretically from the outset. The scheme-theoretic
image of a reduced source is reduced, so this is the reduced closure in the
manuscript. The construction does not assume that the source is already closed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

theorem image_isReduced_of_affine
    {T W : Scheme} [IsAffine W] [AlgebraicGeometry.IsReduced T]
    (k : T ⟶ W) [QuasiCompact k] : AlgebraicGeometry.IsReduced k.image := by
  letI : IsAffine k.image := isAffine_of_isAffineHom k.imageι
  letI : _root_.IsReduced Γ(k.image, ⊤) :=
    isReduced_of_injective k.toImage.appTop.hom (by
      simpa using k.toImage_app_injective ⟨⊤, isAffineOpen_top W⟩)
  exact isReduced_of_isAffine_isReduced k.image

theorem image_inclusion_range
    {T W : Scheme} (k : T ⟶ W) [QuasiCompact k] :
    Set.range k.imageι = closure (Set.range k) := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι,
    Scheme.Hom.support_ker]

theorem preimage_source_eq_range_toImage
    {T W : Scheme} (k : T ⟶ W) :
    k.imageι ⁻¹' Set.range k = Set.range k.toImage := by
  ext c
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, k.imageι.isEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using ht
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp [← Scheme.Hom.comp_apply]⟩

theorem finite_closure_factorization
    {T W Z : Scheme} [IsAffine W] [AlgebraicGeometry.IsReduced T]
    (k : T ⟶ W) (p : W ⟶ Z) [IsOpenImmersion k] [QuasiCompact k]
    [AlgebraicGeometry.IsFinite p] :
    ∃ (C : Scheme) (j : T ⟶ C) (c : C ⟶ W) (q : C ⟶ Z),
      j ≫ c = k ∧ q = c ≫ p ∧ j ≫ q = k ≫ p ∧
      IsOpenImmersion j ∧ IsDominant j ∧ QuasiCompact j ∧
      IsClosedImmersion c ∧ AlgebraicGeometry.IsFinite q ∧
      IsAffine C ∧ AlgebraicGeometry.IsReduced C ∧
      Set.range c = closure (Set.range k) ∧
      c ⁻¹' Set.range k = Set.range j := by
  letI : IsAffine k.image := isAffine_of_isAffineHom k.imageι
  refine ⟨k.image, k.toImage, k.imageι, k.imageι ≫ p,
    k.toImage_imageι, rfl, by simp,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, image_isReduced_of_affine k,
    image_inclusion_range k, preimage_source_eq_range_toImage k⟩

/-- Surjectivity of the lifted source in a normalization forces the original
open embedding into the reduced closure to be an isomorphism. -/
theorem closure_openImmersion_isIso_of_normalization_covered
    {T N C : Scheme} (i : T ⟶ N) (ν : N ⟶ C) (j : T ⟶ C)
    [IsOpenImmersion j] (hν : Function.Surjective ν)
    (hi : Function.Surjective i) (hfac : i ≫ ν = j) : IsIso j := by
  apply (isIso_iff_isOpenImmersion_and_surjective j).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro c
  obtain ⟨n, hn⟩ := hν c
  obtain ⟨t, ht⟩ := hi n
  refine ⟨t, ?_⟩
  rw [← hfac, Scheme.Hom.comp_apply, ht, hn]

theorem finite_of_normalization_covered
    {T N C Z : Scheme} (i : T ⟶ N) (ν : N ⟶ C)
    (j : T ⟶ C) (q : C ⟶ Z) [IsOpenImmersion j]
    [AlgebraicGeometry.IsFinite q] (hν : Function.Surjective ν)
    (hi : Function.Surjective i) (hfac : i ≫ ν = j) :
    AlgebraicGeometry.IsFinite (j ≫ q) := by
  letI := closure_openImmersion_isIso_of_normalization_covered i ν j hν hi hfac
  infer_instance

end NormalLocus
