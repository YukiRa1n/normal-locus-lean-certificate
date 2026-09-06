import NormalLocus.LocalModel

/-!
# Compatibility of the actual pullbacks and target restrictions
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

noncomputable section

theorem range_morphismRestrict
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    Set.range (f ∣_ U) = U.ι ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, by simp only [Scheme.Opens.ι_apply, morphismRestrict_base_coe]⟩
  · rintro ⟨x, hx⟩
    have hxU : x ∈ f ⁻¹ᵁ U := by
      change f x ∈ U
      rw [hx]
      exact y.2
    exact ⟨⟨x, hxU⟩, Subtype.ext (by
      simpa only [morphismRestrict_base_coe, Scheme.Opens.ι_apply] using hx)⟩

def restrictBaseChangeIso
    {X Y S : Scheme} (f : X ⟶ Y) (i : S ⟶ Y) (U : S.Opens) :
    Arrow.mk ((pullback.snd f i) ∣_ U) ≅ Arrow.mk (pullback.snd f (U.ι ≫ i)) := by
  refine Arrow.isoMk
    ((pullbackRestrictIsoRestrict (pullback.snd f i) U).symm ≪≫
      pullbackLeftPullbackSndIso f i U.ι) (Iso.refl _) ?_
  simp [morphismRestrict, Category.assoc]

def pullbackRestrictionsIso
    {X Y S : Scheme} (f : X ⟶ Y) (i : S ⟶ Y) (U : Y.Opens) :
    Arrow.mk (pullback.snd (f ∣_ U) (i ∣_ U)) ≅
      Arrow.mk (pullback.snd f ((i ⁻¹ᵁ U).ι ≫ i)) := by
  have hp := ((IsPullback.of_hasPullback (f ∣_ U) (i ∣_ U)).flip.paste_vert
    (isPullback_morphismRestrict f U)).flip
  rw [morphismRestrict_ι] at hp
  refine Arrow.isoMk hp.isoPullback (Iso.refl _) ?_
  simpa only [Arrow.mk_hom, Arrow.mk_right, Category.comp_id, Iso.refl_hom] using
    hp.isoPullback_hom_snd

def baseChangeTargetRestrictionIso
    {X Y S : Scheme} (f : X ⟶ Y) (i : S ⟶ Y) (U : Y.Opens) :
    Arrow.mk ((pullback.snd f i) ∣_ (i ⁻¹ᵁ U)) ≅
      Arrow.mk (pullback.snd (f ∣_ U) (i ∣_ U)) :=
  restrictBaseChangeIso f i (i ⁻¹ᵁ U) ≪≫ (pullbackRestrictionsIso f i U).symm

theorem finite_restriction_of_local
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens)
    (h : ∀ y ∈ U, ∃ V : Y.Opens, y ∈ V ∧ V ≤ U ∧
      AlgebraicGeometry.IsFinite (f ∣_ V)) : AlgebraicGeometry.IsFinite (f ∣_ U) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro y
  obtain ⟨V, hy, hVU, hV⟩ := h y.1 y.2
  refine ⟨U.ι ⁻¹ᵁ V, hy, ?_⟩
  apply (MorphismProperty.arrow_mk_iso_iff (@AlgebraicGeometry.IsFinite)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mpr
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  rw [he]
  exact hV

theorem surjective_restriction_of_local
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens)
    (h : ∀ y ∈ U, ∃ V : Y.Opens, y ∈ V ∧ Function.Surjective (f ∣_ V)) :
    Function.Surjective (f ∣_ U) := by
  intro y
  obtain ⟨V, hy, hV⟩ := h y.1 y.2
  obtain ⟨x, hx⟩ := hV ⟨y.1, hy⟩
  have hxy : f x.1 = y.1 := by
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx
  have hxU : x.1 ∈ f ⁻¹ᵁ U := by
    change f x.1 ∈ U
    rw [hxy]
    exact y.2
  exact ⟨⟨x.1, hxU⟩, Subtype.ext (by simpa only [morphismRestrict_base_coe] using hxy)⟩

end

end NormalLocus
