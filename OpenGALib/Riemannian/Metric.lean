import OpenGALib.Riemannian.Metric.Basic
import OpenGALib.Riemannian.Metric.Riesz
import OpenGALib.Riemannian.Metric.Smooth

/-!
# RiemannianMetric — facade

Re-exports the three sub-modules:
- `Metric/Basic.lean` — `RiemannianMetric` typeclass, `metricInner` +
  algebra lemmas, NACG / IPS / FiniteDim / CompleteSpace bridges on
  `TangentSpace`.
- `Metric/Riesz.lean` — `metricToDual`, `metricRiesz`,
  `metricInner_eq_iff_eq`, Riesz uniqueness.
- `Metric/Smooth.lean` — `metricInner_smoothAt` smoothness helper +
  `tangentBundle_symmL_smoothAt` (PRE-PAPER sorry'd: chart-level
  smoothness of `Trivialization.symmL`; tracked in
  `docs/SORRY_CATALOG.md`).

**Ground truth**: do Carmo 1992 §1.2; Lee *Smooth Manifolds* Ch. 13.
-/

/-! ## Self-test: typeclass + algebra + Riesz cascade -/

section SelfTest

open OpenGALib

/-- `RiemannianMetric` typeclass + `metricTensor` field accessible. -/
noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v : E) :
    ℝ := g.metricTensor x v v

/-- `symm` typeclass field usable. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v w : E) :
    g.metricTensor x v w = g.metricTensor x w v :=
  g.symm x v w

/-- `posdef` typeclass field usable. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v : E) (hv : v ≠ 0) :
    0 < g.metricTensor x v v :=
  g.posdef x v hv

/-- Bilinearity of `metricInner`. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (a b : ℝ) (V₁ V₂ W : TangentSpace I x) :
    metricInner x (a • V₁ + b • V₂) W = a * metricInner x V₁ W + b * metricInner x V₂ W := by
  rw [metricInner_add_left, metricInner_smul_left, metricInner_smul_left]

/-- `metricRiesz` defining property. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (φ : TangentSpace I x →L[ℝ] ℝ)
    (V : TangentSpace I x) :
    metricInner x (metricRiesz (g := g) x φ) V = φ V :=
  metricRiesz_inner x φ V

end SelfTest
