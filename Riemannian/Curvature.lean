import Riemannian.Connection
import Riemannian.TangentBundle.SmoothVectorField
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Riemannian.Curvature

Riemann curvature tensor, Ricci curvature, scalar curvature.

## Form

  * `riemannCurvature` — real `noncomputable def` built directly from
    `covDeriv` (Levi-Civita) and `mlieBracket` via the standard formula
    $R(X, Y)Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$.
  * `ricciTraceMap` — the linear map $z \mapsto R(z, X)Y(x)$ on $T_xM$,
    bundling the curvature endomorphism for the trace.
  * `ricci` — real `noncomputable def` via `LinearMap.trace ℝ (TangentSpace I x)`
    applied to `ricciTraceMap`. Finite-dimensional trace operator from
    Mathlib (`LinearMap.trace`); the `[FiniteDimensional ℝ E]` cascade
    propagates through the framework-owned NACG / IPS bridges
    (`Riemannian.Metric`).
  * `scalarCurvature` — real `noncomputable def` via summation of
    $\mathrm{Ric}(e_i, e_i)$ over Mathlib's `stdOrthonormalBasis ℝ
    (TangentSpace I x)`. Basis-independent because the sum equals
    $\mathrm{tr}_g \mathrm{Ric}$ for any orthonormal frame.

## Sorry status

  * `ricciTraceMap.map_add'` and `map_smul'` — PRE-PAPER. The
    `C^\infty(M)`-linearity of the curvature endomorphism in its first
    argument (when extended via constants from $T_xM$) requires the
    Levi-Civita-on-`covDeriv` linearity lemmas. Repair: derive from
    `koszulCovDeriv`'s linearity in $X$ when its linearity proofs land.
  * `ricci_symm` — PRE-PAPER. Symmetry of Ricci requires the algebraic
    Bianchi identity on the Riemann tensor. Repair: framework self-build
    of Bianchi from torsion-freeness + curvature definition.

**Ground truth**: do Carmo 1992 §4 (Riemann curvature, sectional, Ricci).
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [RiemannianMetric I M]

/-! `riemannCurvature` and `riemannCurvature_antisymm` are connection-level
content (depend only on `covDeriv` and `mlieBracket`, not metric). They
live in `Riemannian.Connection.Bianchi` (re-exported via
`Riemannian.Connection`) so that `bianchi_first` can reference them
without circular dependency. -/

/-- **Ricci-trace linear map** at a point: the linear map
$z \mapsto R(z\text{-extended}, X) Y(x)$ on $T_xM$, where
$z\text{-extended}$ is the constant section with value $z$.

`X, Y` are bundled `SmoothVectorField`s, providing the global smoothness
witnesses needed for the underlying covariant-derivative additivity
(via `IsCovariantDerivativeOn.add`) and Lie-bracket linearity
(`mlieBracket_add_left`, `mlieBracket_const_smul_left`). -/
noncomputable def ricciTraceMap
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun z := riemannCurvature (fun _ => z) X Y x
  map_add' z₁ z₂ := by
    show riemannCurvature (fun _ => z₁ + z₂) X Y x
       = riemannCurvature (fun _ => z₁) X Y x + riemannCurvature (fun _ => z₂) X Y x
    -- Three terms in `riemannCurvature`; each is ℝ-linear in the first
    -- argument (a constant section of value `z`). Linearity in `z` flows from:
    --   * `lev.toFun ... x` is a CLM (linear in input vector)
    --   * `covDeriv` is additive in the differentiated section (smoothness witnessed by `Y`)
    --   * `mlieBracket` of constant section + X is the directional derivative of X,
    --     itself ℝ-linear in `z`.
    sorry
  map_smul' c z := by sorry

/-- The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at a point
$x$, defined as the trace of the linear map $z \mapsto R(z, X)Y$ on
$T_xM$:
$$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}(\mathrm{ricciTraceMap}\,X\,Y\,x).$$

**Ground truth**: do Carmo 1992 §4 ex. 1.

Real `noncomputable def` via `LinearMap.trace ℝ (TangentSpace I x)`
applied to `ricciTraceMap`. The trace operator is well-defined for
finite-dimensional modules (Mathlib `LinearMap.trace`); since
$E$ is `[FiniteDimensional ℝ E]` in our cascade, the trace returns
a meaningful scalar.

The ℝ-linearity proofs inside `ricciTraceMap` (`map_add'`,
`map_smul'` in the trace argument $z$) are sorry'd (PRE-PAPER,
repair via Mathlib's `CovariantDerivative` linearity lemmas
applied through `riemannCurvature`'s defining formula). -/
noncomputable def ricci
    (X Y : SmoothVectorField I M) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (ricciTraceMap X Y x)

/-- **Ricci curvature is symmetric**: $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

This is one of the standard tensorial properties (do Carmo 1992 §4
ex. 1). The proof requires the algebraic Bianchi identity on the
Riemann tensor (which yields the symmetry of the trace under
swapping X and Y). PRE-PAPER, repair via constructive proof.

**Stability**: experimental (PRE-PAPER). `@[simp]` deferred until the
proof is closed: marking a sorry'd theorem `@[simp]` violates Mathlib
soundness convention (would let `simp` apply unproven rewrites). When
the Bianchi-identity proof lands, restore `@[simp]`. -/
theorem ricci_symm (X Y : SmoothVectorField I M) (x : M) :
    ricci X Y x = ricci Y X x := by sorry

/-- The **scalar curvature** $\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x)$.

Real `noncomputable def` via summing $\mathrm{Ric}(e_i, e_i)$ over a
standard orthonormal basis $\{e_i\}$ of `TangentSpace I x` (provided
by Mathlib's `stdOrthonormalBasis ℝ (TangentSpace I x)` — applicable
because `Riemannian.InnerProductBridge` gives `InnerProductSpace ℝ`
+ `FiniteDimensional ℝ` on the tangent space).

The choice of orthonormal basis is irrelevant — for any orthonormal
basis the sum equals the metric trace of Ric, which is basis-independent.

**Ground truth**: do Carmo 1992 §4. -/
noncomputable def scalarCurvature (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, ricci (I := I) (M := M)
    (SmoothVectorField.const (I := I) (e i : E))
    (SmoothVectorField.const (I := I) (e i : E)) x

end Riemannian

/-! ## UXTest

Self-test verifying curvature primitives resolve their typeclass
cascade. -/
section UXTest

open Riemannian

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x := riemannCurvature X Y Z x

/-- Antisymmetry corollary `riemannCurvature_antisymm` is invocable. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    riemannCurvature X Y Z x = -riemannCurvature Y X Z x :=
  riemannCurvature_antisymm X Y Z x

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (X Y : SmoothVectorField I M) (x : M) : ℝ := ricci X Y x

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (x : M) : ℝ :=
  scalarCurvature (I := I) x

end UXTest
