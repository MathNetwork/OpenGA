import DifferentialGeometry.Analysis.Elliptic.ScalarHessGraph
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.RankZeroRealization
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner
import DifferentialGeometry.Geometry.Connection.ChartBridge.HessFrobenius
import DifferentialGeometry.Geometry.Operator.LaplacianBridge










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



private theorem rawLap_repr_delta
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) (x : M) :
    rawTensorConnLap (I := I) g 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection x =
      Tensor0SSpace.toRS0
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (Δ_g (I := I) g
            (reprScalar0_smooth (I := I) (M := M) v hv) x)) := by
  rw [rawLap_repr_scalar (I := I) (M := M) g v hv x]
  rw [laplacian_levi_eq (I := I) g
    (reprScalar0_smooth (I := I) (M := M) v hv) x]



theorem lap_energy_eq
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ∫ x, (Δ_g (I := I) g
        (reprScalar0_smooth (I := I) (M := M) v hv) x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖rawTensorConnLapSmooth (I := I) g 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v hv)‖ ^ 2 := by
  let S : SmoothCcTensor g 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) v hv
  let L : SmoothCcTensor g 0 0 :=
    rawTensorConnLapSmooth (I := I) g 0 0 S
  change _ = ‖L‖ ^ 2
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun (I := I) (M := M) g 0 0 L]
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [L, SmoothCcTensor.toFun_apply,
    rawTensorConnLapSmooth_toSection_apply]
  rw [show rawTensorConnLap (I := I) g 0 0
      (fun y : M => S.toSection y) x =
        Tensor0SSpace.toRS0
          ((Tensor0SNabla.tensor0Iso I M x).symm
            (Δ_g (I := I) g
              (reprScalar0_smooth (I := I) (M := M) v hv) x)) by
      simpa only [S] using rawLap_repr_delta (I := I) (M := M) g v hv x]
  rw [inner_toRS0_scalar (I := I) (M := M) g x]
  ring



private theorem repr_lap_inner
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    tensorL2Inner (I := I) (M := M) g 0 0
        (rawTensorConnLapSmooth (I := I) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv)).toFun
        (tensorHsSmoothRepr (I := I) (M := M) v hv).toFun =
      ∫ x, (Δ_g (I := I) g
          (reprScalar0_smooth (I := I) (M := M) v hv) x) *
        reprScalar0 (I := I) (M := M) v hv x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SmoothCcTensor.toFun_apply,
    rawTensorConnLapSmooth_toSection_apply]
  rw [rawLap_repr_delta (I := I) (M := M) g v hv x]
  have hrepr_x :
      (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection x =
        (Tensor0SField.fromScalarField ∞
          (reprScalar0 (I := I) (M := M) v hv)
          (reprScalar0_smooth (I := I) (M := M) v hv)).toTensorRSField ∞ x := by
    exact congrArg (fun T => T x)
      (repr_eq_lift (I := I) (M := M) v hv).symm
  rw [hrepr_x]
  rw [Tensor0SField.toRS0_eq]
  rw [inner_toRS0_zero (I := I) (M := M) g x]
  have hlap : tensor0SSpace_evalScalar x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (Δ_g (I := I) g
          (reprScalar0_smooth (I := I) (M := M) v hv) x)) =
      Δ_g (I := I) g
        (reprScalar0_smooth (I := I) (M := M) v hv) x := by
    change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm _) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hrepr : tensor0SSpace_evalScalar x
      (Tensor0SField.fromScalarField ∞
        (reprScalar0 (I := I) (M := M) v hv)
        (reprScalar0_smooth (I := I) (M := M) v hv) x) =
      reprScalar0 (I := I) (M := M) v hv x := by
    rw [Tensor0SSpace.evalScalar_apply]
    change Tensor0SSpace.toModel
      (Tensor0SField.fromScalarField ∞
        (reprScalar0 (I := I) (M := M) v hv)
        (reprScalar0_smooth (I := I) (M := M) v hv) x) Fin.elim0 = _
    exact Tensor0SField.fromScalarField_apply ∞
      (reprScalar0 (I := I) (M := M) v hv)
      (reprScalar0_smooth (I := I) (M := M) v hv) x Fin.elim0
  rw [hlap, hrepr]



theorem grad_energy_eq
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ∫ x, normGradSqFun (I := I) g
        (reprScalar0 (I := I) (M := M) v hv) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖covGrad (I := I) (M := M) g 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v hv)‖ ^ 2 := by
  let S : SmoothCcTensor g 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) v hv
  let L : SmoothCcTensor g 0 0 :=
    rawTensorConnLapSmooth (I := I) g 0 0 S
  have hscalar :
      ∫ x, normGradSqFun (I := I) g
          (reprScalar0 (I := I) (M := M) v hv) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, reprScalar0 (I := I) (M := M) v hv x *
          Δ_g (I := I) g
            (reprScalar0_smooth (I := I) (M := M) v hv) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [normGradSqFun_def, grad_g_apply] using
      (green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
        (I := I) g
        (reprScalar0_smooth (I := I) (M := M) v hv)
        (reprScalar0_smooth (I := I) (M := M) v hv)
        (HasCompactSupport.of_compactSpace _))
  have htensor :
      ‖covGrad (I := I) (M := M) g 0 0 S‖ ^ 2 =
        -tensorL2Inner (I := I) (M := M) g 0 0 L.toFun S.toFun := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun (I := I) (M := M) g 0 1
        (covGrad (I := I) (M := M) g 0 0 S)]
    simpa only [L] using
      (tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen
        (I := I) (M := M) g 0 S)
  calc
    ∫ x, normGradSqFun (I := I) g
        (reprScalar0 (I := I) (M := M) v hv) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, reprScalar0 (I := I) (M := M) v hv x *
          Δ_g (I := I) g
            (reprScalar0_smooth (I := I) (M := M) v hv) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hscalar
    _ = -∫ x, (Δ_g (I := I) g
            (reprScalar0_smooth (I := I) (M := M) v hv) x) *
          reprScalar0 (I := I) (M := M) v hv x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      congr 1
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => mul_comm _ _)
    _ = -tensorL2Inner (I := I) (M := M) g 0 0 L.toFun S.toFun := by
      rw [← repr_lap_inner (I := I) (M := M) g v hv]
    _ = ‖covGrad (I := I) (M := M) g 0 0 S‖ ^ 2 := htensor.symm



theorem lap_energy_le
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ∫ x, (Δ_g (I := I) g
        (reprScalar0_smooth (I := I) (M := M) v hv) x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤ ‖v‖ ^ 2 := by
  rw [lap_energy_eq (I := I) (M := M) g v hv]
  have hL := rawLap_repr_norm (I := I) (M := M) g v hv
  rw [SmoothCcTensor.norm_toL2] at hL
  nlinarith [norm_nonneg
    (rawTensorConnLapSmooth (I := I) g 0 0
      (tensorHsSmoothRepr (I := I) (M := M) v hv)), norm_nonneg v]



theorem grad_energy_le
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ∫ x, normGradSqFun (I := I) g
        (reprScalar0 (I := I) (M := M) v hv) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤ ‖v‖ ^ 2 := by
  rw [grad_energy_eq (I := I) (M := M) g v hv]
  have hG := grad_repr_norm (I := I) (M := M) g v hv
  rw [SmoothCcTensor.norm_toL2] at hG
  nlinarith [norm_nonneg
    (covGrad (I := I) (M := M) g 0 0
      (tensorHsSmoothRepr (I := I) (M := M) v hv)), norm_nonneg v]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem du_normSq
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) :
    normSq0S (I := I) g x 1 (duSec (I := I) f hf x) =
      normGradSqFun (I := I) g f x := by
  rw [duSec_apply, normSq0S_eq_inner,
    inner0S_differential1FormFun_pair_eq_grad_inner]
  rfl



theorem du_energy_le
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ∫ x, normSq0S (I := I) g x 1
        (duSec (I := I)
          (reprScalar0 (I := I) (M := M) v hv)
          (reprScalar0_smooth (I := I) (M := M) v hv) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤ ‖v‖ ^ 2 := by
  simpa only [du_normSq] using grad_energy_le (I := I) (M := M) g v hv




theorem hess_energy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : tensorHs (I := I) (M := M) g 0 0 2)
        (hv : (Function.support v.coeff).Finite),
        ∫ x, chartHessFrobeniusSq (I := I) g
            (reprScalar0 (I := I) (M := M) v hv) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
          C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hgraph⟩ :=
    DifferentialGeometry.Analysis.Laplacian.scalar_hess_graph
      (I := I) (M := M) g
  refine ⟨1 + C, by linarith, ?_⟩
  intro v hv
  have hgraph' := hgraph
    (f := reprScalar0 (I := I) (M := M) v hv)
    (reprScalar0_smooth (I := I) (M := M) v hv)
  have hlap := lap_energy_le (I := I) (M := M) g v hv
  have hgrad := grad_energy_le (I := I) (M := M) g v hv
  calc
    ∫ x, chartHessFrobeniusSq (I := I) g
        (reprScalar0 (I := I) (M := M) v hv) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        (∫ x, (Δ_g (I := I) g
            (reprScalar0_smooth (I := I) (M := M) v hv) x) ^ 2
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          C * ∫ x, normGradSqFun (I := I) g
            (reprScalar0 (I := I) (M := M) v hv) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hgraph'
    _ ≤ ‖v‖ ^ 2 + C * ‖v‖ ^ 2 :=
      add_le_add hlap (mul_le_mul_of_nonneg_left hgrad hC)
    _ = (1 + C) * ‖v‖ ^ 2 := by ring



theorem hessSec_energy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : tensorHs (I := I) (M := M) g 0 0 2)
        (hv : (Function.support v.coeff).Finite),
        ∫ x, normSq0S (I := I) g x 2
            (leviHessSec (I := I) g
              (reprScalar0 (I := I) (M := M) v hv)
              (reprScalar0_smooth (I := I) (M := M) v hv) x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
          C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hess⟩ := hess_energy_le (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro v hv
  simpa only [hessSec_normSq] using hess v hv

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
