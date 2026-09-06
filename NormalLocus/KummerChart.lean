import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The reduced divisor in a Kummer chart

For `B = A[t]/(t^e - f)`, the quotient by `t` is `A/(f)`.
If `A/(f)` is reduced, the radical of `(f)B` is exactly `(t)`.
These are the local algebra calculations used in Stacks 0EYH.
The existence of Kummer charts (Stacks 0EYG) is not assumed or proved here.
-/

namespace NormalLocus.KummerChart

noncomputable section

open Polynomial

variable {A : Type*} [CommRing A]

abbrev equation (f : A) (e : ℕ) : A[X] := X ^ e - C f

abbrev Ring (f : A) (e : ℕ) := AdjoinRoot (equation f e)

abbrev parameter (f : A) (e : ℕ) : Ring f e := AdjoinRoot.root (equation f e)

abbrev parameterIdeal (f : A) (e : ℕ) : Ideal (Ring f e) := Ideal.span {parameter f e}

theorem parameter_pow (f : A) (e : ℕ) :
    parameter f e ^ e = algebraMap A (Ring f e) f := by
  have h := AdjoinRoot.eval₂_root (equation f e)
  simpa only [equation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
    AdjoinRoot.algebraMap_eq] using h

theorem finite_free (f : A) {e : ℕ} (he : e ≠ 0) :
    Module.Finite A (Ring f e) ∧ Module.Free A (Ring f e) :=
  ⟨(monic_X_pow_sub_C f he).finite_adjoinRoot,
    (monic_X_pow_sub_C f he).free_adjoinRoot⟩

theorem parameter_isRegular (f : A) {e : ℕ} (he : e ≠ 0) (hf : IsRegular f) :
    IsRegular (parameter f e) := by
  letI := (finite_free f he).2
  have hr : IsRegular (algebraMap A (Ring f e) f) := by
    have hs := Module.Flat.isSMulRegular_of_isRegular (M := Ring f e) hf
    apply (Commute.isRegular_iff fun b ↦ mul_comm _ b).mpr
    simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def] using hs
  rw [← parameter_pow] at hr
  exact (IsRegular.pow_iff (Nat.pos_of_ne_zero he)).mp hr

def residueMap (f : A) {e : ℕ} (he : e ≠ 0) :
    Ring f e →+* A ⧸ Ideal.span {f} :=
  AdjoinRoot.lift (Ideal.Quotient.mk (Ideal.span {f})) 0 (by
    simp [equation, zero_pow he])

def residueQuotientMap (f : A) {e : ℕ} (he : e ≠ 0) :
    (Ring f e ⧸ parameterIdeal f e) →+* A ⧸ Ideal.span {f} :=
  Ideal.Quotient.lift _ (residueMap f he) (by
    change parameterIdeal f e ≤ RingHom.ker (residueMap f he)
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change residueMap f he (parameter f e) = 0
    simp [residueMap, parameter])

def baseQuotientMap (f : A) {e : ℕ} (he : e ≠ 0) :
    (A ⧸ Ideal.span {f}) →+* Ring f e ⧸ parameterIdeal f e :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (parameterIdeal f e)).comp (algebraMap A (Ring f e))) (by
      change Ideal.span {f} ≤ RingHom.ker
        ((Ideal.Quotient.mk (parameterIdeal f e)).comp (algebraMap A (Ring f e)))
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      change Ideal.Quotient.mk _ (algebraMap A (Ring f e) f) = 0
      rw [← parameter_pow, map_pow]
      have hz : Ideal.Quotient.mk (parameterIdeal f e) (parameter f e) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [hz, zero_pow he])

def quotientEquiv (f : A) {e : ℕ} (he : e ≠ 0) :
    (Ring f e ⧸ parameterIdeal f e) ≃+* A ⧸ Ideal.span {f} :=
  RingEquiv.ofRingHom (residueQuotientMap f he) (baseQuotientMap f he) (by
    apply Ideal.Quotient.ringHom_ext
    ext a
    simp [residueQuotientMap, baseQuotientMap, residueMap,
      AdjoinRoot.algebraMap_eq]) (by
    apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext a
      simp [residueQuotientMap, baseQuotientMap, residueMap,
        AdjoinRoot.algebraMap_eq]
    · simp [residueQuotientMap, baseQuotientMap, residueMap,
        parameter, parameterIdeal])

theorem quotient_equiv_exists (f : A) {e : ℕ} (he : e ≠ 0) :
    Nonempty ((Ring f e ⧸ parameterIdeal f e) ≃+* A ⧸ Ideal.span {f}) :=
  ⟨quotientEquiv f he⟩

theorem parameterIdeal_isRadical (f : A) {e : ℕ} (he : e ≠ 0)
    [IsReduced (A ⧸ Ideal.span {f})] : (parameterIdeal f e).IsRadical := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact isReduced_of_injective (quotientEquiv f he) (quotientEquiv f he).injective

theorem parameterIdeal_isPrime (f : A) {e : ℕ} (he : e ≠ 0)
    [IsDomain (A ⧸ Ideal.span {f})] : (parameterIdeal f e).IsPrime := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  exact Function.Injective.isDomain (quotientEquiv f he) (quotientEquiv f he).injective

theorem radical_baseIdeal (f : A) {e : ℕ} (he : e ≠ 0)
    [IsReduced (A ⧸ Ideal.span {f})] :
    (Ideal.span {algebraMap A (Ring f e) f}).radical = parameterIdeal f e := by
  rw [← parameter_pow, ← Ideal.span_singleton_pow, Ideal.radical_pow _ he]
  exact (parameterIdeal_isRadical f he).radical

end

end NormalLocus.KummerChart
