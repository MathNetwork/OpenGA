import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.Comparison.Util.SpaceForm
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Util.Metric.MetricNotation
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

/-- **Math.** **Bishop–Gromov volume comparison**: for a Riemannian
manifold `(M, g)` with Ricci curvature bounded below by `(n-1)K`, the
ratio of the Riemannian volume of a geodesic ball to the volume of the
corresponding ball in the constant-curvature space form is monotone
non-increasing in the radius.

Stated directly on the canonical Riemannian volume `vol_g` (no longer
parameterized over `μ + IsScalarMultipleOfHausdorff`). The proof goes
through exponential-chart polar coordinates `vol_g(B(p,r)) =
∫_0^r ∫_{S_p^{n-1}} J_g(s, v) ds dσ` and Jacobi-field comparison; it
does not need the Federer Hausdorff bridge.

Ground truth: do Carmo Ch.10 §2 Thm 2.2; Petersen Ch.9 Thm 27;
Cheeger–Ebin Thm 1.93; Burago–Burago–Ivanov §6.5. -/
theorem bishopGromov_volume_comparison
    (hRic : ∀ x : M, ∀ v : TangentSpace I x,
      ((n_M : ℝ) - 1) * K * ⟪v, v⟫_g ≤ Ric_g(v, v) x)
    (p : M) {r R : ℝ} (hr : r ∈ 𝒟_K) (hR : R ∈ 𝒟_K) (hrR : r ≤ R) :
    dV_g[(HasMetric.metric : RiemannianMetric I M)].real B(p, R) / V_K^n_M(R) ≤ dV_g[(HasMetric.metric : RiemannianMetric I M)].real B(p, r) / V_K^n_M(r) := by
  sorry

end
