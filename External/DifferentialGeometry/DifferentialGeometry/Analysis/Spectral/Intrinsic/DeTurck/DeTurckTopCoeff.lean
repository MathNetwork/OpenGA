import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


def deTurckPhiMetTotal (g₀ g_bg g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  deTurckLieArm2PrincipalCoeff (I := I) g₀ g g_bg
    + traceHessianCoeff (I := I) (M := M) g₀ g
    - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g
        + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g)



omit [BoundarylessManifold I M] in
theorem phi_realized_eq
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        - (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckPhiMetTotal, linearizedRicciArm2FieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s)
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s)
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgroup : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by
    abel
  rw [hgroup, hhalf]
  abel

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
