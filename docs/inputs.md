# 13 项外部输入：实际 Lean 声明

以下代码由 `scripts/snippets.py` 从被校验的源文件提取，验证程序逐字比较。每段是其所在命名空间中的声明片段；完整 imports、命名空间和变量环境以源文件为准。`def … : Prop` 定义一个命题，不是该命题的证明。13 项目前均为条件参数。

数学解释及从原引用到接口的转换见 [语义审阅](semantic-review.md)。

## 1. `intersection` / `HeightOneIntersection`

[实际源码](../NormalLocus/ExternalStatements.lean)。TeX 锚点：`lem:affine-hartogs`。

```lean
def HeightOneIntersection : Prop :=
  ∀ (X : Scheme.{0}) [IsAffine X] [IsIntegral X]
    [IsNoetherianRing Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (s : X.functionField),
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) →
    s ∈ (globalToFunctionField X).range
```

原始来源：[Stacks 0AVB](https://stacks.math.columbia.edu/tag/0AVB)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 2. `dimension` / `FiniteLocalDimension`

[实际源码](../NormalLocus/BoundaryRemoval.lean)。TeX 锚点：`prop:boundary-codim-two`。

```lean
def FiniteLocalDimension : Prop :=
  ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [AlgebraicGeometry.IsFinite g] [IsDominant g],
    normalPoints Y = Set.univ → ∀ x : X,
      ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (g x))
```

原始来源：[Stacks 00OG](https://stacks.math.columbia.edu/tag/00OG)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 3. `normalization` / `NormalizationPieces`

[实际源码](../NormalLocus/NormalizedClosure.lean)。TeX 锚点：`prop:boundary-codim-two`。

```lean
def NormalizationPieces : Prop :=
  ∀ (T C : Scheme.{0}) [IsAffine T] [IsAffine C]
    [IsLocallyNoetherian C] [AlgebraicGeometry.IsReduced C]
    (j : T ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [IsDominant j],
    normalPoints T = Set.univ → ComplexAlgebraic C →
    ∀ c : C, ∃ (P : NormalizationPiece j) (n : P.N), P.ν n = c
```

原始来源：[Stacks 0BXQ](https://stacks.math.columbia.edu/tag/0BXQ)、[Stacks 0357](https://stacks.math.columbia.edu/tag/0357)、[Stacks 0H7D](https://stacks.math.columbia.edu/tag/0H7D)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 4. `boundary` / `AffineBoundaryDivisors`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`prop:pure-codim-one`, `thm:boundary-collision`。

```lean
def AffineBoundaryDivisors : Prop :=
  ∀ (X V : Scheme.{0}) [IsAffine X] [IsAffine V] [IsIntegral V]
    [IsLocallyNoetherian V] (j : X ⟶ V) [IsOpenImmersion j] [IsDominant j],
    IsDivisorUnion (Set.range j)ᶜ
```

原始来源：[Stacks 0BCV](https://stacks.math.columbia.edu/tag/0BCV)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 5. `etaleDivisors` / `EtalePullbackDivisors`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`thm:boundary-collision`。

```lean
def EtalePullbackDivisors : Prop :=
  ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Etale f] (D : Set Y),
    IsDivisorUnion D → IsDivisorUnion (f ⁻¹' D)
```

原始来源：[Stacks 02GH](https://stacks.math.columbia.edu/tag/02GH)、[Stacks 00OG](https://stacks.math.columbia.edu/tag/00OG)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 6. `etaleNormal` / `EtalePreservesNormal`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`lem:normal-neighborhood`。

```lean
def EtalePreservesNormal : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Etale f],
    normalPoints Y = Set.univ → normalPoints X = Set.univ
```

原始来源：[Stacks 0336](https://stacks.math.columbia.edu/tag/0336)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 7. `abhyankar` / `AbhyankarLocalIrreducibility`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`thm:boundary-collision`。

```lean
def AbhyankarLocalIrreducibility : Prop :=
  ∀ (V Y Z : Scheme.{0}) [IsAffine V] [IsAffine Y]
    [IsIntegral V] [IsIntegral Y] [IsLocallyNoetherian V] [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsReduced Z]
    (π : V ⟶ Y) [AlgebraicGeometry.IsFinite π] [IsDominant π]
    (i : Z ⟶ Y) [IsClosedImmersion i],
    ComplexAlgebraic Y → normalPoints V = Set.univ →
    regularPoints Y = Set.univ → IsDivisorUnion (Set.range i) →
    (∀ U : Y.Opens, Disjoint (U : Set Y) (Set.range i) → Etale (π ∣_ U)) →
    ∀ (a : V) (z : Z), π a = i z → z ∈ regularPoints Z →
      ∃ W : V.Opens, a ∈ W ∧ IsIrreducible ((π ⁻¹' Set.range i) ∩ W)
```

原始来源：[Stacks 0EYH](https://stacks.math.columbia.edu/tag/0EYH)、[Stacks 0EYG](https://stacks.math.columbia.edu/tag/0EYG)、[Stacks 09E9](https://stacks.math.columbia.edu/tag/09E9)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 8. `divisorImage` / `FiniteDivisorImage`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`prop:pure-codim-one`。

```lean
def FiniteDivisorImage : Prop :=
  ∀ (V Y : Scheme.{0}) [IsAffine V] [IsAffine Y] [IsIntegral V] [IsIntegral Y]
    [IsLocallyNoetherian V] [IsLocallyNoetherian Y]
    (π : V ⟶ Y) [AlgebraicGeometry.IsFinite π] [IsDominant π],
    normalPoints Y = Set.univ → ∀ E : Set V,
      PrimeDivisor E → PrimeDivisor (π '' E)
```

原始来源：[Stacks 00OG](https://stacks.math.columbia.edu/tag/00OG)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 9. `divisorEquations` / `PolynomialPrimeDivisorEquation`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`prop:nonempty`。

```lean
def PolynomialPrimeDivisorEquation : Prop :=
  ∀ (n : ℕ) (E : Set (Spec (CommRingCat.of (CoordinateRing n ℂ)))),
    PrimeDivisor E → ∃ h : CoordinateRing n ℂ,
      (∀ c : ℂ, h ≠ MvPolynomial.C c) ∧ E = PrimeSpectrum.zeroLocus {h}
```

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 10. `affineRegular` / `AffineSpaceRegular`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`thm:boundary-collision`。

```lean
def AffineSpaceRegular : Prop :=
  ∀ n : ℕ, regularPoints (Spec (CommRingCat.of (CoordinateRing n ℂ))) = Set.univ
```

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 11. `normalOpen` / `NormalLocusOpen`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`lem:normal-neighborhood`。

```lean
def NormalLocusOpen : Prop :=
  ∀ (S : Scheme.{0}) [AlgebraicGeometry.IsReduced S],
    ComplexAlgebraic S → IsOpen (normalPoints S)
```

原始来源：[Stacks 0BXQ](https://stacks.math.columbia.edu/tag/0BXQ)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 12. `domainComponents` / `DomainPointUniqueComponent`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`lem:normal-neighborhood`。

```lean
def DomainPointUniqueComponent : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (x : S),
    IsDomain (S.presheaf.stalk x) →
    ∃! R : Set S, R ∈ irreducibleComponents S ∧ x ∈ R
```

原始来源：[Stacks 00ET](https://stacks.math.columbia.edu/tag/00ET)。

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 13. `regularOpen` / `RegularOpenImmersion`

[实际源码](../NormalLocus/ExternalGeometry.lean)。TeX 锚点：`thm:boundary-collision`, `lem:normal-neighborhood`。

```lean
def RegularOpenImmersion : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsOpenImmersion f],
    regularPoints Y = Set.univ → regularPoints X = Set.univ
```

当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。

## 输入中使用的项目定义

### `ComplexAlgebraic`

```lean
def ComplexAlgebraic (X : Scheme.{0}) : Prop :=
  ∃ s : X ⟶ Spec (CommRingCat.of ℂ), LocallyOfFiniteType s ∧ QuasiCompact s
```

### `globalToFunctionField`

```lean
noncomputable def globalToFunctionField (X : Scheme.{0}) [IsIntegral X] :
    Γ(X, ⊤) →+* X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, Set.mem_univ _⟩⟩
  exact (X.germToFunctionField ⊤).hom
```

### `normalPoints`

```lean
def normalPoints (X : Scheme) : Set X :=
  { x | IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) }
```

### `regularPoints`

```lean
def regularPoints (X : Scheme) : Set X :=
  {x | (Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) : WithBot ℕ∞) =
    ringKrullDim (X.presheaf.stalk x)}
```

### `PrimeDivisor`

```lean
structure PrimeDivisor {X : Type*} [TopologicalSpace X] (E : Set X) : Prop where
  isClosed : IsClosed E
  isIrreducible : IsIrreducible E
  ne_univ : E ≠ univ
  maximal : ∀ Q : Set X, IsClosed Q → IsIrreducible Q → E ⊆ Q →
    Q = E ∨ Q = univ
```

### `IsDivisorUnion`

```lean
def IsDivisorUnion {X : Type*} [TopologicalSpace X] (S : Set X) : Prop :=
  ∃ E : Finset (Set X), (∀ e ∈ E, PrimeDivisor e) ∧ ⋃₀ (E : Set (Set X)) = S
```

### `NormalizationPiece`

```lean
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
```

### `CoreGeometry`

```lean
structure CoreGeometry : Prop where
  intersection : HeightOneIntersection
  dimension : FiniteLocalDimension
  normalization : NormalizationPieces
  boundary : AffineBoundaryDivisors
  etaleDivisors : EtalePullbackDivisors
  etaleNormal : EtalePreservesNormal
  abhyankar : AbhyankarLocalIrreducibility
```

### `Library`

```lean
structure Library : Prop extends CoreGeometry where
  divisorImage : FiniteDivisorImage
  divisorEquations : PolynomialPrimeDivisorEquation
  affineRegular : AffineSpaceRegular
  normalOpen : NormalLocusOpen
  domainComponents : DomainPointUniqueComponent
  regularOpen : RegularOpenImmersion
```
