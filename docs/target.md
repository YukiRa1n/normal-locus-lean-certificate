# 结果和全部核心定义

以下是实际源文件中的声明片段，由验证程序逐字比对。完整上下文见对应 Lean 文件。

```lean
abbrev PolynomialMap (n : ℕ) (K : Type*) [CommRing K] :=
  Fin n → MvPolynomial (Fin n) K
```

```lean
noncomputable def jacobian {n : ℕ} {K : Type*} [CommRing K]
    (F : PolynomialMap n K) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  fun i j => pderiv j (F i)
```

```lean
def IsKeller {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ (jacobian F).det = C c
```

```lean
def nonProperLocus {X Y : Scheme} (f : X ⟶ Y) : Set Y :=
  { y | ¬ ∃ U : Y.Opens, y ∈ U ∧ IsProper (f ∣_ U) }
```

```lean
def nonProperIdeal {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    Ideal (CoordinateRing n K) :=
  PrimeSpectrum.vanishingIdeal (nonProperLocus (schemeMap F))
```

```lean
def nonProperScheme {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) : Scheme :=
  Spec (CommRingCat.of (CoordinateRing n K ⧸ nonProperIdeal F))
```

```lean
def nonProperInclusion {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) :
    nonProperScheme F ⟶ Spec (CommRingCat.of (CoordinateRing n K)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nonProperIdeal F)))
```

```lean
def normalPoints (X : Scheme) : Set X :=
  { x | IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) }
```

```lean
def restrictedMap {n : ℕ} {K : Type*} [Field K]
    (F : PolynomialMap n K) (U : (nonProperScheme F).Opens) :
    pullback (schemeMap F) (U.ι ≫ nonProperInclusion F) ⟶ U :=
  pullback.snd _ _
```

```lean
def NormalLocusConclusion {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) : Prop :=
  ∃ U : (nonProperScheme F).Opens,
    (U : Set (nonProperScheme F)) = normalPoints (nonProperScheme F) ∧
    AlgebraicGeometry.IsFinite (restrictedMap F U) ∧ Etale (restrictedMap F U) ∧
    Surjective (restrictedMap F U)
```

```lean
def NormalLocusTheorem : Prop :=
  ∀ (n : ℕ) (F : PolynomialMap n ℂ), IsKeller F → NormalLocusConclusion F
```

## 完整组合证明

```lean
theorem normal_locus_finite_etale_conditional (external : External.Library) :
    NormalLocusTheorem := by
  intro n F hF
  letI : Etale (schemeMap F) := keller_schemeMap_etale F hF
  letI : LocallyQuasiFinite (schemeMap F) := keller_schemeMap_quasiFinite F hF
  letI : IsDominant (schemeMap F) := keller_schemeMap_dominant F hF
  letI : AlgebraicGeometry.IsFinite (schemeMap F).fromNormalization :=
    keller_canonical_normalization_finite F hF
  letI : IsAffine (schemeMap F).normalization :=
    isAffine_of_isAffineHom (schemeMap F).fromNormalization
  letI : IsLocallyNoetherian (schemeMap F).normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (schemeMap F).fromNormalization
  let j := (schemeMap F).toNormalization
  let π := (schemeMap F).fromNormalization
  let i := nonProperInclusion F
  have hfac : j ≫ π = schemeMap F := (schemeMap F).toNormalization_fromNormalization
  letI : IsDominant (j ≫ π) := hfac.symm ▸ inferInstance
  letI : Etale (j ≫ π) := hfac.symm ▸ inferInstance
  letI : IsDominant π := IsDominant.of_comp j π
  letI : IsClosedImmersion i := nonProperInclusion_isClosedImmersion F
  letI : AlgebraicGeometry.IsReduced (nonProperScheme F) := nonProperScheme_isReduced F
  have hdivisor : IsDivisorUnion (Set.range i) := by
    have hb := external.boundary _ _ j
    have hi := hb.image π (external.divisorImage _ _ π (polynomial_scheme_normal n))
    simpa only [i, range_nonProperInclusion, keller_nonProperLocus_eq_boundary_image F hF,
      j, π] using hi
  have hboundary : (Set.range j)ᶜ ⊆ π ⁻¹' Set.range i := by
    intro a ha
    change π a ∈ Set.range (nonProperInclusion F)
    rw [range_nonProperInclusion, keller_nonProperLocus_eq_boundary_image F hF]
    exact ⟨a, ha, rfl⟩
  have hdense : Dense (Set.range (pullback.snd (j ≫ π) i)) := by
    rw [hfac]
    exact dense_on_divisor_union (schemeMap F) i hdivisor
      (keller_hits_prime_divisor external.divisorEquations F hF)
  have hNL := normal_locus_from_external_geometry external.toCoreGeometry external.normalSlices
    j π i (polynomial_scheme_complexAlgebraic n)
    (polynomial_canonical_normalization_normal F) (external.affineRegular n)
    hdivisor hboundary hdense
  rw [hfac] at hNL
  simpa only [i, NormalLocusConclusion, restrictedMap] using hNL
```
