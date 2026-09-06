import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Polynomial maps and the hypersurface non-omission step

The Jacobian is the determinant of the matrix of formal partial derivatives.
The non-omission theorem below assumes injectivity of the coordinate-ring map;
it does not assume that a map between affine spaces is surjective on points.
-/

namespace NormalLocus

open MvPolynomial

abbrev PolynomialMap (n : ℕ) (K : Type*) [CommRing K] :=
  Fin n → MvPolynomial (Fin n) K

noncomputable def evaluate {n : ℕ} {K : Type*} [CommRing K]
    (F : PolynomialMap n K) (x : Fin n → K) : Fin n → K :=
  fun i => MvPolynomial.eval x (F i)

noncomputable def jacobian {n : ℕ} {K : Type*} [CommRing K]
    (F : PolynomialMap n K) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  fun i j => pderiv j (F i)

/-- The usual constant, nonzero polynomial Jacobian condition. -/
def IsKeller {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ (jacobian F).det = C c

/-- Every nonunit multivariate polynomial over an algebraically closed field has a zero. -/
theorem exists_zero_of_not_isUnit
    {σ K : Type*} [Finite σ] [Field K] [IsAlgClosed K]
    (p : MvPolynomial σ K) (hp : ¬ IsUnit p) :
    ∃ x : σ → K, MvPolynomial.eval x p = 0 := by
  have hproper : Ideal.span ({p} : Set (MvPolynomial σ K)) ≠ ⊤ := by
    intro heq
    exact hp (Ideal.span_singleton_eq_top.mp heq)
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal _ hproper
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hm
  have hmem : p ∈ MvPolynomial.vanishingIdeal K {x} :=
    hx ▸ hpm (Ideal.subset_span (Set.mem_singleton p))
  refine ⟨x, ?_⟩
  simpa using hmem x (Set.mem_singleton x)

/-- Injective polynomial substitution cannot turn a nonconstant polynomial into a unit. -/
theorem substitution_not_isUnit
    {σ τ K : Type*} [Field K]
    (F : σ → MvPolynomial τ K)
    (hinj : Function.Injective (aeval (R := K) F))
    (h : MvPolynomial σ K) (hconstant : ∀ c : K, h ≠ C c) :
    ¬ IsUnit (aeval F h) := by
  intro hu
  obtain ⟨c, _, heq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  apply hconstant c
  apply hinj
  simpa using heq

/-- A dominant polynomial map hits every hypersurface defined by a nonconstant polynomial.

The explicit `hinj` is the coordinate-ring formulation of dominance.
`KellerEtale.lean` derives it from `IsKeller` and then applies this theorem.
-/
theorem dominant_hits_hypersurface
    {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]
    (F : PolynomialMap n K) (hinj : Function.Injective (aeval (R := K) F))
    (h : MvPolynomial (Fin n) K) (hconstant : ∀ c : K, h ≠ C c) :
    ∃ x : Fin n → K, MvPolynomial.eval (evaluate F x) h = 0 := by
  obtain ⟨x, hx⟩ := exists_zero_of_not_isUnit (aeval F h)
    (substitution_not_isUnit F hinj h hconstant)
  refine ⟨x, ?_⟩
  have hcomp : (MvPolynomial.eval x).comp (aeval F).toRingHom =
      MvPolynomial.eval (evaluate F x) := by
    ext i <;> simp [evaluate]
  change ((MvPolynomial.eval x).comp (aeval F).toRingHom) h = 0 at hx
  rwa [hcomp] at hx

end NormalLocus
