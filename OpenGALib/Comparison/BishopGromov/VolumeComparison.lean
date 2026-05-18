import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.Comparison.Util.SpaceForm
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Volume.ChartPullback

/-!
# Bishop–Gromov volume comparison

North-star theorem of Layer 3b. Statement only; proof is the multi-stage
goal driving Layer 1 + Layer 3a + Layer 3b. Ground truth: do Carmo
Ch. 10 §2 Thm 2.2; Petersen Ch. 9 Thm 27; Cheeger–Ebin Thm 1.93;
Burago–Burago–Ivanov §6.5.
-/

open scoped Real Manifold InnerProductSpace ENNReal ContDiff Riemannian
open Bundle MeasureTheory Riemannian Set OpenGA.Comparison.BishopGromov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [HasMetric I M] [CompleteSpace M] [IsRiemannianManifold I M]
  [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]

local notation:max "n_M" => Module.finrank ℝ E

scoped[OpenGA.Comparison.BishopGromov]
  notation:max "B(" p ", " r ")" => Metric.ball p r

section
variable {K : ℝ}

local notation:max "V_K^" n:max "(" r:max ")" => spaceFormBallVolume n K r
local notation:max "𝒟_K" => spaceFormAdmissibleRadii K

/-- **Math.** Bishop–Gromov volume comparison.

For a Riemannian manifold `(M, g)` with `Ric_g ≥ (n - 1) K g`, the ratio
`(volumeMeasure g)(B(p, R)) / V_K^n(R)` of the Riemannian-volume ball
to the model space-form ball is monotone non-increasing in `R` on the
admissible radius window `𝒟_K`.

Stated directly on the canonical Riemannian volume `Riemannian.volumeMeasure g`;
the generic-measure stopgap (`IsScalarMultipleOfHausdorff`) is retired
now that `volumeMeasure` is constructed in `Riemannian/Volume/`. The
scale-invariance of the ratio that motivated the stopgap is subsumed:
any scalar multiple of `volumeMeasure g` gives the same ratio, so the
metric-specific statement is no less general for downstream consumers
(which must produce a Riemannian volume anyway). -/
theorem bishopGromov_volume_comparison
    (g : RiemannianMetric I M)
    (hRic : ∀ x : M, ∀ v : TangentSpace I x,
      ((n_M : ℝ) - 1) * K * g.metricInner x v v ≤ (ricciTensor g x v) v)
    (p : M) {r R : ℝ} (hr : r ∈ 𝒟_K) (hR : R ∈ 𝒟_K) (hrR : r ≤ R) :
    (Riemannian.volumeMeasure g).real B(p, R) / V_K^n_M(R)
      ≤ (Riemannian.volumeMeasure g).real B(p, r) / V_K^n_M(r) := by
  sorry

end
