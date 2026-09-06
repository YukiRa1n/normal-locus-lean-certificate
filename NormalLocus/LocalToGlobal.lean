import NormalLocus.Statement
import NormalLocus.FiniteEtale
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The target-local part of the manuscript proof

These lemmas prove the gluing and nonemptiness implications on actual schemes.
Their local hypotheses are intermediate conclusions to be supplied by the
boundary argument; they are not declared as external axioms.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NormalLocus

theorem surjective_of_local_surjective
    {X Y : Scheme} (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ Function.Surjective (f ∣_ U)) :
    Function.Surjective f := by
  intro y
  obtain ⟨U, hy, hU⟩ := h y
  obtain ⟨x, hx⟩ := hU ⟨y, hy⟩
  refine ⟨x.1, ?_⟩
  simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx

theorem finite_etale_surjective_of_local
    {X Y : Scheme} (f : X ⟶ Y) [Etale f]
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      AlgebraicGeometry.IsFinite (f ∣_ U) ∧ Nonempty ↥((f ⁻¹ᵁ U).toScheme) ∧
        PreconnectedSpace ↥U.toScheme) :
    AlgebraicGeometry.IsFinite f ∧ Etale f ∧ Function.Surjective f := by
  have hfinite : AlgebraicGeometry.IsFinite f :=
    IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun y ↦ by
      obtain ⟨U, hy, hU, _, _⟩ := h y
      exact ⟨U, hy, hU⟩
  refine ⟨hfinite, inferInstance, surjective_of_local_surjective f ?_⟩
  intro y
  obtain ⟨U, hy, hU, hne, hc⟩ := h y
  letI := hU
  letI := hne
  letI := hc
  exact ⟨U, hy, finite_etale_surjective (f ∣_ U)⟩

/-- A nonempty etale image meets every nonempty open in an irreducible target. -/
theorem etale_preimage_open_nonempty
    {X Y : Scheme} (f : X ⟶ Y) [Etale f] [Nonempty X]
    [PreirreducibleSpace Y] (U : Y.Opens) (hU : (U : Set Y).Nonempty) :
    (f ⁻¹' (U : Set Y)).Nonempty := by
  have hd : Dense (Set.range f) :=
    f.isOpenMap.isOpen_range.dense (Set.range_nonempty f)
  obtain ⟨y, hyU, hyf⟩ := hd.inter_open_nonempty (U : Set Y) U.isOpen hU
  obtain ⟨x, rfl⟩ := hyf
  exact ⟨x, hyU⟩

/-- A hit on a closed irreducible target, followed by etaleness, supplies the
nonempty source required on every nonempty target-open neighborhood. -/
theorem etale_pullback_open_nonempty
    {X Y Z : Scheme} (f : X ⟶ Y) (i : Z ⟶ Y) [Etale f]
    [PreirreducibleSpace Z] (hhit : ∃ x : X, ∃ z : Z, f x = i z)
    (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ((pullback.snd f i) ⁻¹' (U : Set Z)).Nonempty := by
  obtain ⟨x, z, hxz⟩ := hhit
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x z hxz
  letI : Nonempty ↥(pullback f i) := ⟨w⟩
  exact etale_preimage_open_nonempty (pullback.snd f i) U hU

end NormalLocus
