# Normal-Locus Finite Étale Theorem: Proof and Lean Verification

[中文](README.md) | **English**

**The composition proof of the NL theorem is complete and has passed Lean kernel checks, conditional on the 13 external geometric inputs listed in this repository.**

This repository contains the proof source, the external inputs, a review of their mathematical meaning, and reproducible verification tools. The same formal proof has also passed a [complete run in a fresh Ubuntu environment on GitHub](https://github.com/YukiRa1n/normal-locus-lean-certificate/actions/runs/34047288754).

[Exact Lean target and proof](docs/target.md) · [13 external inputs](docs/inputs.md) · [Verification results](verification/results.json) · [GitHub Actions](https://github.com/YukiRa1n/normal-locus-lean-certificate/actions)

The detailed supporting documents linked below are currently in Chinese. Their Lean declarations and source references remain available in full.

## 1. What the theorem says

Let $F:\mathbb A^n_{\mathbb C}\to\mathbb A^n_{\mathbb C}$ be a Keller polynomial map. This means that its Jacobian determinant is a nonzero constant. Let $S_F$ be its nonproperness set, with the reduced scheme structure, and let $S_F^{\mathrm{nor}}$ be its normal locus.

The **Normal-Locus Finite Étale Theorem (NL)** states that the restriction

$$
F^{-1}(S_F^{\mathrm{nor}})\longrightarrow S_F^{\mathrm{nor}}
$$

is **finite, étale, and surjective**, using the external results specified below.

The Lean conclusion uses actual schemes and morphism properties. The following definitions are copied from [Statement.lean](NormalLocus/Statement.lean):

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

The theorem proved in [ConditionalNL.lean](NormalLocus/ConditionalNL.lean) has the following type:

```lean
NormalLocus.normal_locus_finite_etale_conditional :
  NormalLocus.External.Library → NormalLocus.NormalLocusTheorem
```

This states exactly: **if the 13 inputs hold, then NL holds**. A `def … : Prop` defines a proposition. The theorem above supplies its checked conditional proof, whose [complete body](docs/target.md#完整组合证明) is public.

The external results and the steps that adapt their cited statements to these interfaces remain explicit mathematical dependencies. This repository does not prove all of them internally.

## 2. What the executable checks establish

The main theorem and its transitive dependencies have passed the following checks:

| Check | What the program checks |
|---|---|
| No `sorry` or `admit` gaps | The transitive axiom dependencies contain no `sorryAx`, including dependencies of invoked theorems. |
| No additional axioms | The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. Any other axiom causes failure. |
| No native evaluation proof axiom | The same allowlist excludes `Lean.trustCompiler` in this version. The dependency check also rejects unsafe and partial declarations. |
| Kernel verification of the complete proof | After a successful build, the checker replays 75,402 required declarations in an empty environment at trust level 0. |
| Exact target | The main declaration must be a theorem with exactly the type `External.Library → NormalLocusTheorem`. A different target or an additional premise is rejected. |

Lean's standard axiom inspection command is:

```lean
import NormalLocus
#print axioms NormalLocus.normal_locus_finite_etale_conditional
```

It reports only:

```text
propext, Classical.choice, Quot.sound
```

[Audit.lean](Audit.lean) and [scripts/verify.py](scripts/verify.py) enforce these conditions. They return failure if an axiom is outside the allowlist, the target type is wrong, or replay fails. See the [axiom audit](verification/audit.log) and [kernel replay report](verification/replay.json).

These checks establish that the Lean proof has no proof gaps or additional axioms **under the 13 explicit inputs**. The [semantic review](docs/semantic-review.md) separately examines the mathematical meaning of the inputs and target.

<details>
<summary>Relation to the Lean community's five verification criteria</summary>

The Lean community's [Did you prove it?](https://leanprover-community.github.io/did_you_prove_it.html) gives five criteria. This repository provides evidence for each:

| Criterion | Evidence |
|---|---|
| A standard, reproducible Lean project | Lean 4.28.0, a fixed mathlib commit, the [dependency lockfile](lake-manifest.json), and a [source manifest](manifest.json). |
| A successful build | The [build log](verification/build.log) and a [successful fresh CI run](https://github.com/YukiRa1n/normal-locus-lean-certificate/actions/runs/34047288754). |
| The intended theorem is checked | The [project entry point](NormalLocus.lean) imports the theorem. The audit requires a theorem with the exact `Library → NormalLocusTheorem` type. |
| Only standard logical axioms | The transitive axiom allowlist is enforced by the audit and replay checks. |
| The formal statement matches the claim | Core definitions, all 13 inputs, and the target are public. Source consistency checks and a separate semantic review support the correspondence. Compilation alone does not certify this correspondence. |

The fifth criterion requires an explicit scope: this repository claims and proves `Library → NL`. The external inputs are theorem parameters. Passing an axiom audit does not remove them.

These checks assume the usual trust in Lean's logic and implementation. See the [official validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) and the repository's [account of soundness and trust](docs/soundness.md).

</details>

## 3. The external inputs

These inputs express geometric and commutative algebra results. The [input register](docs/inputs.md) gives each complete Lean statement, the definitions it uses, and its sources. The verification program compares the displayed input declarations with the actual source.

| No. | Field | Mathematical input |
|---|---|---|
| 1 | `intersection` | A normal Noetherian domain is the intersection of its height-one localizations. |
| 2 | `dimension` | A local dimension formula for finite dominant maps with normal target. |
| 3 | `normalization` | Components of finite normalization and the isomorphism over the normal open locus. |
| 4 | `boundary` | The boundary of a dense affine open subset is a finite union of prime divisors. |
| 5 | `etaleDivisors` | Étale inverse images preserve the required pure codimension-one divisor decomposition. |
| 6 | `etaleNormal` | Étale morphisms preserve normality. |
| 7 | `abhyankar` | Local irreducibility of the reduced inverse image in a normalized cover at a regular divisor point. |
| 8 | `divisorImage` | A finite dominant map with normal target sends prime divisors to prime divisors. |
| 9 | `divisorEquations` | Prime divisors in complex affine space have nonconstant polynomial equations. |
| 10 | `affineRegular` | Every local ring of complex affine space is regular. |
| 11 | `normalOpen` | The normal locus of a reduced complex algebraic scheme is open. |
| 12 | `domainComponents` | A point whose local ring is a domain lies on a unique irreducible component. |
| 13 | `regularOpen` | Open immersions preserve regularity. |

Some interfaces are consequences of the cited statements. For example, the Abhyankar input also requires a neighborhood restriction, an identification of the normalization, and tameness in characteristic zero. These steps yield the local irreducibility used by the proof.

Accepting the external basis means accepting these **precise inputs and the steps that produce them**, as explained in the [semantic review](docs/semantic-review.md#3-13-项外部输入逐项核对).

<details>
<summary>The actual Lean input structures</summary>

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

```lean
structure Library : Prop extends CoreGeometry where
  divisorImage : FiniteDivisorImage
  divisorEquations : PolynomialPrimeDivisorEquation
  affineRegular : AffineSpaceRegular
  normalOpen : NormalLocusOpen
  domainComponents : DomainPointUniqueComponent
  regularOpen : RegularOpenImmersion
```

</details>

## 4. Proof outline

The formalization follows the main route of the manuscript:

1. Construct a finite normal completion of the same map. Identify its boundary image with the nonproperness set.
2. Construct the relevant closure divisors and boundary divisors near the normal locus. Use the local Abhyankar input to exclude their collision at regular points.
3. Restrict the remaining boundary to codimension at least two. Use normalization and affine Hartogs to remove this boundary and obtain finiteness.
4. Combine étaleness, the argument that no hypersurface is omitted, and the open-and-closed image argument to prove surjectivity. Glue the local conclusions over the normal locus.

Lean checks the complete composition. Finiteness, étaleness, and surjectivity are actual mathlib morphism properties. Actual local rings define the normal locus. The restricted morphism comes from a pullback of the original map F.

The [semantic review](docs/semantic-review.md) explains the correspondence of objects and the organization of the formal proof. Under the listed inputs, their correct interpretation, and Lean's usual trusted foundations, the checked implication gives the NL conclusion.

## 5. Verification evidence and its limits

The recorded verification includes:

- A transitive axiom audit of **118 theorems**, including the final conditional theorem.
- Correct rejection of **four invalid certificates**: a wrong target, an additional axiom, `sorry`, and an additional premise.
- Replay of **75,402 declarations** in a fresh environment at trust level 0.
- Checks that the displayed target, inputs, and Chinese README declarations match the actual Lean source.

See the [result summary](verification/results.json), [axiom audit](verification/audit.log), [replay log](verification/replay.log), and [verification program](scripts/verify.py).

Replay uses the official Lean kernel again. It is **not an independently implemented checker**. The semantic review and external mathematical results remain separate dependencies.

`CONDITIONAL_VERIFIED` means that the executable composition checks passed. `MANUAL_REVIEW` identifies the review of mathematical meaning. `TRUST_ASSUMPTION` identifies the logical and implementation foundations.

`unconditional_nl: INCOMPLETE` means that the repository has not also proved every external input internally. It does not negate the verified `Library → NL` certificate.

## 6. Reproduce the checks

Install Git, Python 3.11 or later, and [elan](https://github.com/leanprover/elan). Then run:

```sh
git clone https://github.com/YukiRa1n/normal-locus-lean-certificate.git
cd normal-locus-lean-certificate
lake exe cache get
python scripts/verify.py
```

The first run downloads the pinned dependencies. Full replay can take some time. A successful run prints `CONDITIONAL_VERIFIED`.

Each push also triggers [GitHub Actions](.github/workflows/verify.yml), which saves the verification logs as run artifacts.

For documentation checks only, run `python scripts/verify.py --check-docs`. This mode explicitly reports that it is a static check.

The `--require-complete` option additionally requires proof of all external inputs. It currently returns exit code 2. Use `--lake /absolute/path/to/lake` to select a Lake executable.

Further reading: the [frozen manuscript](provenance/Normal_Loci_Keller_Maps_v1.tex), [semantic review](docs/semantic-review.md), and [soundness and trust](docs/soundness.md).

## 7. Contributions

- **Research, theorem formulation, proof strategy, and the original manuscript:** GPT-5.6 Sol and GPT-5.6 Pro.
- **Lean formalization and executable verification:** GPT-6 Astra formalized the existing proof and implemented the verification and audit tools.
