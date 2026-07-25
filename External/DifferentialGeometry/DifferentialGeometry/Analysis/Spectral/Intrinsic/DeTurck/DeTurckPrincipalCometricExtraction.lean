import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RoughLaplacianCometricDoubleTrace
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldDifferentiatedTowerNormalForm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.KoszulSectionParallelRaise
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma g1_inner_injective (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x} (hab : ∀ u : TangentSpace I x, g₁.inner x a u = g₁.inner x b u) :
    a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsplit : g₁.inner x (a - b) (a - b)
        = g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsplit, g₁.symm x (a - b) a, g₁.symm x (a - b) b, hab (a - b)]
    ring
  exact absurd hzero (ne_of_gt hpos)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometricLmodel_covectorOfCLM_inner_loc (g₁ : SmoothRiemannianMetric I M) (y : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I y) :
    g₁.inner y (cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) u = φ (u : E) := by
  have h1 : cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      inverseMetricSharpFib (I := I) g₁ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
      (fun _ : Fin 1 => (u : E)) = φ (u : E)
  rw [Tensor0SBundle.model_covectorOfCLM_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem cometricLmodel_sub_eq_gInvDiffRaisedEndo
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (φ : E →L[ℝ] ℝ) :
    cometricLmodel (I := I) g₁ x (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
        - cometricLmodel (I := I) g₀ x (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      metricComparisonDiffEndo (I := I) g₀ g₁ x
        (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := by
  set α : Tensor0SSpace 1 I x :=
    Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ with hα
  set w₀ : TangentSpace I x := cometricLmodel (I := I) g₀ x α with hw₀
  set w₁ : TangentSpace I x := cometricLmodel (I := I) g₁ x α with hw₁
  apply g1_inner_injective (I := I) g₁ x
  intro u
  have hLHS : g₁.inner x (w₁ - w₀) u = g₁.inner x w₁ u - g₁.inner x w₀ u := by
    rw [map_sub (g₁.inner x), ContinuousLinearMap.sub_apply]
  have hg1w1 : g₁.inner x w₁ u = φ (u : E) := by
    rw [hw₁, hα]; exact cometricLmodel_covectorOfCLM_inner_loc (I := I) g₁ x φ u
  have hg0w0 : g₀.inner x w₀ u = φ (u : E) := by
    rw [hw₀, hα]; exact cometricLmodel_covectorOfCLM_inner_loc (I := I) g₀ x φ u
  have hRHS : g₁.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x w₀) u
      = g₀.inner x w₀ u - g₁.inner x w₀ u :=
    inner_g1_gInvDiffRaisedEndo (I := I) g₀ g₁ x w₀ u
  rw [hLHS, hRHS, hg1w1, hg0w0]


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem ricciArmPrincipalCoeffPure_appCc_sub_eq_gInvDiffContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) W) x v
      - unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons
            (metricComparisonDiffEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  classical
  rw [ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian (I := I) (M := M) g₀ g₀ W x v]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set rest : Fin 3 → E := Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x) : E)
    (fun j : Fin 2 => ((v j : TangentSpace I x) : E)) with hrest
  set f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
    unitModel (I := I) (M := M) g₀ 4 W x with hf
  have hcons : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 W x
        (Fin.cons (z : E) (Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x) : E)
          (fun j : Fin 2 => ((v j : TangentSpace I x) : E))))
        = f (Fin.cons (z : E) rest) := fun z => rfl
  have hslot0 : ∀ a b : TangentSpace I x,
      f (Fin.cons ((a : E)) rest) - f (Fin.cons ((b : E)) rest)
        = f (Fin.cons (((a - b : TangentSpace I x) : E)) rest) := by
    intro a b
    have hcurry : ∀ z : TangentSpace I x,
        f (Fin.cons ((z : E)) rest)
          = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ) f
              ((z : TangentSpace I x) : E)) rest := by
      intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
    rw [hcurry a, hcurry b, hcurry (a - b)]
    rw [show (((a - b : TangentSpace I x) : E)) = ((a : E)) - ((b : E)) from rfl]
    rw [map_sub, ContinuousMultilinearMap.sub_apply]
  have hkey : unitModel (I := I) (M := M) g₀ 4 W x
        (Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v))
        - unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v))
      = unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons
            (metricComparisonDiffEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
    rw [hcons (cometricLmodel (I := I) g₁ x _), hcons (cometricLmodel (I := I) g₀ x _),
      hcons (metricComparisonDiffEndo (I := I) g₀ g₁ x _), hslot0]
    congr 2
    rw [show (((metricComparisonDiffEndo (I := I) g₀ g₁ x
            (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) : TangentSpace I x) : E)) =
        ((cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))
          - cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) : TangentSpace I x) : E) from by
      rw [cometricLmodel_sub_eq_gInvDiffRaisedEndo (I := I) g₀ g₁ x
        ((Module.finBasis ℝ E).cDualBasis k)]]
  exact hkey


theorem connLapCometric_g1_sub_g0_eq_gInvDiffContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v
      - unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons
            (metricComparisonDiffEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace (I := I) g₀ S x v]
  exact ricciArmPrincipalCoeffPure_appCc_sub_eq_gInvDiffContraction (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v

def deTurckPrincipalCometricCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁
    - ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀

def deTurckPrincipalCometricArm (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 :=
  operatorFieldApply (I := I) (M := M) g₀ 4 2
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
    (iteratedCovGrad (I := I) g₀ 0 2 2 S)


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma unitModel_appCc_sub_distrib
    (g₀ : SmoothRiemannianMetric I M) (Φ₁ Φ₂ : SmoothCcTensor g₀ 4 2)
    (W : SmoothCcTensor g₀ 0 4) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₁ - Φ₂) W) x v =
      unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 Φ₁ W) x v
        - unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 Φ₂ W) x v := by
  rw [appCc_sub_left (I := I) (M := M) g₀ 4 2]
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]


theorem deTurckPrincipalCometricArm_unitModel_eq_gInvDiffContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons
            (metricComparisonDiffEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  classical
  rw [deTurckPrincipalCometricArm, deTurckPrincipalCometricCoeff,
    unitModel_appCc_sub_distrib (I := I) (M := M) g₀
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v]
  have hg0 : unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v
      = unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v :=
    (rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace (I := I) g₀ S x v).symm
  rw [hg0]
  exact connLapCometric_g1_sub_g0_eq_gInvDiffContraction (I := I) (M := M) g₀ g₁ S x v


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma deTurckCoeff_clm_eq_doubleTrace_sub (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) =
      cometricDoubleTraceFib (I := I) g₁ 2 x - cometricDoubleTraceFib (I := I) g₀ 2 x := by
  rw [deTurckPrincipalCometricCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply]
  rw [ricciArmPrincipalCoeffPure_toSection (I := I) (M := M) g₀ g₁,
    ricciArmPrincipalCoeffPure_toSection (I := I) (M := M) g₀ g₀]


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma deTurckCoeff_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : Tensor0SSpace 4 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) w) m =
      ∑ k : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel w)
          (Fin.cons
            ((metricComparisonDiffEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E)) m)) := by
  classical
  rw [deTurckCoeff_clm_eq_doubleTrace_sub (I := I) (M := M) g₀ g₁ x,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply, modelDoubleTrace_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set wm : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ := Tensor0SSpace.toModel w with hwm
  set tail : Fin 3 → E := Fin.cons (((Module.finBasis ℝ E) k : E)) m with htail
  have hcurry : ∀ z : TangentSpace I x,
      wm (Fin.cons ((z : E)) tail)
        = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ) wm
            ((z : TangentSpace I x) : E)) tail := by
    intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcurry (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (metricComparisonDiffEndo (I := I) g₀ g₁ x
        (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))))]
  rw [← ContinuousMultilinearMap.sub_apply, ← map_sub]
  congr 2
  rw [cometricLmodel_sub_eq_gInvDiffRaisedEndo (I := I) g₀ g₁ x
    ((Module.finBasis ℝ E).cDualBasis k)]


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma deTurckPrincipalCometricCoeff_eq_appCcRS_doubleTrace_slotInsertEndo
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ =
      DifferentialGeometry.Integral.Connection.ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (DifferentialGeometry.Integral.Connection.endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 4 2 x (fun w => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [deTurckCoeff_toModel_eq (I := I) (M := M) g₀ g₁ x w m,
    DifferentialGeometry.Integral.Connection.appCcRS_toSection,
    ContinuousLinearMap.comp_apply, cometricDoubleTraceField_toSection,
    cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.slotInsertEndoCc_toSection,
    slotInsertEndoFib_apply_eval, Fin.cons_zero, Fin.update_cons_zero]
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometricLmodel_covOf_g0flat_eq (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((g₀.inner x v).toLinearMap.toContinuousLinearMap)) = v := by
  apply g1_inner_injective (I := I) g₀ x
  intro u
  rw [cometricLmodel_covectorOfCLM_inner_loc (I := I) g₀ x
    ((g₀.inner x v).toLinearMap.toContinuousLinearMap) u]
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma flatRecon_eq_basisVec (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (b : Fin n) :
    ∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) = e b := by
  classical
  have hsmul : ∀ k : Fin (Module.finrank ℝ E),
      (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))
        = cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
                ((Module.finBasis ℝ E).cDualBasis k))) := by
    intro k
    rw [map_smul, map_smul]
  rw [Finset.sum_congr rfl (fun k _ => hsmul k)]
  rw [← map_sum, ← map_sum]
  have hcoe : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis k)
        = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k
  have hsum : (∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          ((Module.finBasis ℝ E).cDualBasis k))
      = (g₀.inner x (e b)).toLinearMap.toContinuousLinearMap := by
    have hrepr := cdual_sum_repr (Module.finBasis ℝ E)
      ((g₀.inner x (e b)).toLinearMap.toContinuousLinearMap)
    refine Eq.trans ?_ hrepr
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcoe k]
    congr 1
  rw [hsum]
  exact cometricLmodel_covOf_g0flat_eq (I := I) g₀ x (e b)


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma deTurckCoeff_component_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 4 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      g₀.inner x (e (K 0)) (metricComparisonDiffEndo (I := I) g₀ g₁ x (e (K 1))) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x)
          (coframeS (I := I) (M := M) g₀ x 4 e K))
        (fun k => ((e (J k) : TangentSpace I x) : E)) := rfl
  rw [hcomp, deTurckCoeff_toModel_eq (I := I) (M := M) g₀ g₁ x
    (coframeS (I := I) (M := M) g₀ x 4 e K) (fun k => ((e (J k) : TangentSpace I x) : E))]
  set Rk : Fin (Module.finrank ℝ E) → TangentSpace I x := fun k =>
    cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hRk
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    metricComparisonDiffEndo (I := I) g₀ g₁ x with hΛ
  have hk : ∀ k : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
    intro k
    have hcf : (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = coframeS (I := I) (M := M) g₀ x 4 e K
            (Fin.cons ((Λ (Rk k)) : TangentSpace I x)
              (Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x))
                (fun j => (e (J j) : TangentSpace I x)))) := rfl
    rw [hcf, coframeS_apply, Fin.prod_univ_four]
    change g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * g₀.inner x (e (K 2)) (e (J 0))
          * g₀.inner x (e (K 3)) (e (J 1))
        = _
    rw [horth (K 2) (J 0), horth (K 3) (J 1)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  rw [← Finset.sum_mul]
  congr 1
  have hpull : g₀.inner x (e (K 0)) (Λ
          (∑ k : Fin (Module.finrank ℝ E),
            (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) : ℝ) • Rk k))
      = ∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 0)) (Λ (Rk k)) * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  rw [← hpull, flatRecon_eq_basisVec (I := I) g₀ x e (K 1)]


private lemma sum_pi_fin_succ {n : ℕ} {β : Type*} [AddCommMonoid β]
    {N : ℕ} (g : (Fin (N + 1) → Fin n) → β) :
    (∑ p : Fin (N + 1) → Fin n, g p)
      = ∑ a : Fin n, ∑ q : Fin N → Fin n, g (Fin.cons a q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin n)).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

private lemma deTurckCoeff_componentSqSum_eq (n : ℕ) (f : Fin n → Fin n → ℝ) :
    (∑ K : Fin 4 → Fin n, ∑ J : Fin 2 → Fin n,
      (f (K 0) (K 1) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
      = (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (f a b) ^ 2 := by
  classical
  have hJcollapse : ∀ K : Fin 4 → Fin n,
      (∑ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
        = (f (K 0) (K 1)) ^ 2 := by
    intro K
    have hsplit : ∀ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2
          = (f (K 0) (K 1)) ^ 2 *
              ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
      intro J
      by_cases h2 : K 2 = J 0 <;> by_cases h3 : K 3 = J 1 <;>
        simp [h2, h3]
    rw [Finset.sum_congr rfl (fun J _ => hsplit J), ← Finset.mul_sum]
    rw [sum_pi_fin_succ (fun J : Fin 2 → Fin n =>
      (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))]
    have hinner : ∀ a : Fin n, (∑ q : Fin 1 → Fin n,
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))
        = (if K 2 = a then (1 : ℝ) else 0) := by
      intro a
      rw [sum_pi_fin_succ (fun q : Fin 1 → Fin n =>
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))]
      have hb : ∀ b : Fin n, (∑ _r : Fin 0 → Fin n,
          (if K 2 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 0
            then (1 : ℝ) else 0) *
            (if K 3 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 1
              then (1 : ℝ) else 0))
          = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
        intro b
        have hbody : ∀ r : Fin 0 → Fin n,
            (if K 2 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
              (if K 3 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 then (1 : ℝ) else 0)
            = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
          intro r
          rw [show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 = a from rfl,
            show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 = b from rfl]
        rw [Finset.sum_congr rfl (fun r _ => hbody r), Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_fun, Fintype.card_fin, pow_zero, one_smul]
      rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
      rw [Finset.sum_ite_eq Finset.univ (K 3) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
    rw [Finset.sum_ite_eq Finset.univ (K 2) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun K _ => hJcollapse K)]
  rw [sum_pi_fin_succ (fun K : Fin 4 → Fin n => (f (K 0) (K 1)) ^ 2)]
  have hstep : ∀ a : Fin n, (∑ q : Fin 3 → Fin n,
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)
      = (n : ℝ) ^ 2 * ∑ b : Fin n, (f a b) ^ 2 := by
    intro a
    rw [sum_pi_fin_succ (fun q : Fin 3 → Fin n =>
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)]
    have hb : ∀ b : Fin n, (∑ r : Fin 2 → Fin n,
        (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
          ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2)
        = (n : ℝ) ^ 2 * (f a b) ^ 2 := by
      intro b
      have hval : ∀ r : Fin 2 → Fin n,
          (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
            ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2 = (f a b) ^ 2 := by
        intro r
        rw [show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0 = a from rfl,
          show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1 = b from rfl]
      rw [Finset.sum_congr rfl (fun r _ => hval r), Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum]


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    metricComparisonDiffEndo (I := I) g₀ g₁ x with hΛ
  obtain ⟨n, e, hn, horth, hpar, hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g₀ x 4 2 e hrepr
    (show TensorRSSpace 4 2 I x from
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x)]
  have hcompsq : ∀ (K : Fin 4 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J) ^ 2
        = (g₀.inner x (e (K 0)) (Λ (e (K 1))) *
            ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2 := by
    intro K J
    rw [deTurckCoeff_component_eq (I := I) g₀ g₁ x e horth K J, hΛ]
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hcompsq K J))]
  rw [deTurckCoeff_componentSqSum_eq n (fun a b => g₀.inner x (e a) (Λ (e b)))]
  have hr_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  set r : ℝ := δ / (1 - δ) with hr
  have hper : ∀ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) ≤ r ^ 2 := by
    intro b
    have hsqrt := sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e b)
    rw [← hΛ, ← hr] at hsqrt
    have he1 : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
    rw [he1, Real.sqrt_one, mul_one] at hsqrt
    have hLnn : 0 ≤ g₀.inner x (Λ (e b)) (Λ (e b)) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x (Λ (e b))
    have hsq := Real.sq_sqrt hLnn
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Λ (e b)) (Λ (e b))), hsqrt, hsq, hr_nn]
  have hParseval : ∀ b : Fin n,
      (∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2) = g₀.inner x (Λ (e b)) (Λ (e b)) := by
    intro b
    have hpb := hpar (Λ (e b))
    refine hpb ▸ ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g₀.symm x (e a) (Λ (e b))]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
      ≤ (n : ℝ) * r ^ 2 := by
    rw [Finset.sum_comm]
    calc (∑ b : Fin n, ∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
        = ∑ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) :=
          Finset.sum_congr rfl (fun b _ => hParseval b)
      _ ≤ ∑ _b : Fin n, r ^ 2 := Finset.sum_le_sum (fun b _ => hper b)
      _ = (n : ℝ) * r ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * r ^ 2) := mul_le_mul_of_nonneg_left hAB hn_nn
    _ = (Module.finrank ℝ E : ℝ) ^ 3 * r ^ 2 := by rw [← hnE]; ring


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem riemannianFiberNormSq_deTurckPrincipalCometricArm_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) g₀ h δ) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x) := by
  have hcomp := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 4 2 x
    (show TensorRSSpace 4 2 I x from
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x)
    (show TensorRSSpace 0 4 I x from
      (iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x)
  have harm_sec : (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 0 2 I x from
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x)) := by
    rw [deTurckPrincipalCometricArm,
      appCc_toSection (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 S) x]
  rw [harm_sec]
  refine hcomp.trans ?_
  have hcoeff := riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le
    (I := I) (M := M) g₀ g₁ h htie hδ_lt hδ_nn hδ x
  have hW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
      ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x _
  exact mul_le_mul_of_nonneg_right hcoeff hW_nn


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_smul_local (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_smul_local (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring


omit [NeZero (Module.finrank ℝ E)] in
private lemma combinedTrace42Model_apply_symbolic
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    ricciPrincipalCoeffDoubleTraceModel (E := E) L D m =
      (1 / 2 : ℝ) *
        (modelDoubleTrace (E := E) 2 L
            (ContinuousMultilinearMap.domDomCongr koszulDoubleTraceSlotPerm D) m
          + modelDoubleTrace (E := E) 2 L (ContinuousMultilinearMap.domDomCongr koszulDoubleTraceSlotPerm D)
              (fun j : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) j))
          - modelDoubleTrace (E := E) 2 L D m) := by
  rw [ricciPrincipalCoeffDoubleTraceModel, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
        + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) koszulDoubleTraceSlotPerm
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1)
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)) koszulDoubleTraceSlotPerm
        - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 4 2 x (fun w => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    ricciArmPrincipalCoeff_toSection, ricciArmPrincipalCoeff_toSection,
    ricciArmPrincipalCoeffFib_toModel, ricciArmPrincipalCoeffFib_toModel,
    combinedTrace42Model_apply_symbolic, combinedTrace42Model_apply_symbolic]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add, ContMDiffSection.coe_sub,
    ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  simp only [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, deTurckCoeff_clm_eq_doubleTrace_sub, cometricDoubleTraceFib_toModel,
    Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_sub, ContinuousLinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sub_apply]
  ring


private lemma riemannianFiberNormSq_iteratedCovGrad_ricciArmPrincipalCoeff_sub_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      (10 / 4 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) := by
  classical
  set R3 := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ with hR3
  set R1 := reindexCoeffGen (I := I) (M := M) g₀ 4 2 R3 koszulDoubleTraceSlotPerm with hR1
  set R2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
    (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1) R3)
    koszulDoubleTraceSlotPerm with hR2
  set A := ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
    - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀ with hA
  have hid : A + A = R1 + R2 - R3 := by
    rw [hA, hR1, hR2, hR3]
    exact ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum (I := I) (M := M) g₀ g₁
  have hiter : iteratedCovGrad (I := I) g₀ 4 2 i A + iteratedCovGrad (I := I) g₀ 4 2 i A =
      iteratedCovGrad (I := I) g₀ 4 2 i R1 + iteratedCovGrad (I := I) g₀ 4 2 i R2
        - iteratedCovGrad (I := I) g₀ 4 2 i R3 := by
    rw [← iteratedCovGrad_add, hid, iteratedCovGrad_sub, iteratedCovGrad_add]
  have hsec : (iteratedCovGrad (I := I) g₀ 4 2 i A).toSection x
        + (iteratedCovGrad (I := I) g₀ 4 2 i A).toSection x =
      (iteratedCovGrad (I := I) g₀ 4 2 i R1).toSection x
        + (iteratedCovGrad (I := I) g₀ 4 2 i R2).toSection x
        - (iteratedCovGrad (I := I) g₀ 4 2 i R3).toSection x := by
    have hcg := congrArg (fun T : SmoothCcTensor g₀ 4 (2 + i) =>
      (T.toSection x : TensorRSSpace 4 (2 + i) I x)) hiter
    simpa only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply] using hcg
  set PA0 := (iteratedCovGrad (I := I) g₀ 4 2 i A).toSection x with hPA0
  set PA := (iteratedCovGrad (I := I) g₀ 4 2 i R1).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 4 2 i R2).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 4 2 i R3).toSection x with hPC
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PA =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PC := by
    rw [hPA, hPC, hR1]
    exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R3 koszulDoubleTraceSlotPerm i x
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PB =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PC := by
    rw [hPB, hPC, hR2]
    exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 4 2 koszulDoubleTraceSlotPerm
      (Equiv.swap (0 : Fin 2) 1) R3 i x
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PC := by
    have hh := riemannianFiberNormSq_smul_local (I := I) (M := M) g₀ 4 (2 + i) x (-1 : ℝ) PC
    rw [neg_one_smul] at hh
    rw [hh]; norm_num
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x (PA + PB - PC) ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PC
        + 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PC
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PC := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 (2 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 (2 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (2 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (2 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (2 + i) x PC]
  have hlhs4 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x (PA0 + PA0) =
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PA0 := by
    rw [show PA0 + PA0 = (2 : ℝ) • PA0 from (two_smul ℝ PA0).symm,
      riemannianFiberNormSq_smul_local]
    norm_num
  have hkey : 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PA0 ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x PC := by
    rw [← hlhs4, hsec]
    linarith [hsum]
  linarith [hkey, riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (2 + i) x PC]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_succ_eq_reindex_slotExtend_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)).toSection x) D) m
  rw [DifferentialGeometry.Integral.Connection.slotInsertEndoCc_toSection,
    slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun j : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Equiv.swap_apply_left]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [DifferentialGeometry.Integral.Connection.slotInsertEndoCc_toSection,
    slotInsertEndoFib_apply_eval, TensorMultilinear.tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hswap_succ0 : (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  rw [hswap_succ0]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl, Fin.cons_succ,
      Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 1 + 1)) ≠ 0 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 1 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0, Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]


private lemma rfns_iteratedCovGrad_slotInsertEndoCc_succ_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)).toSection x) := by
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ))).toSection x) := by
    rw [slotInsertEndoCc_succ_eq_reindex_slotExtend_local (I := I) (M := M) g₀ s Λ]
    exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
      (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
      (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)) i x
  rw [hA]
  exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ (s + 1) (s + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) i x


private lemma riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_succ_succ_le
    (g₀ : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 4 4 l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 Λ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 2 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ)).toSection x) := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_succ_le (I := I) (M := M) g₀ 2 Λ l x
  have h2 := rfns_iteratedCovGrad_slotInsertEndoCc_succ_le (I := I) (M := M) g₀ 1 Λ l x
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 4 4 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 Λ)).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 3 l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 Λ)).toSection x) := h1
    _ ≤ (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 2 l
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ)).toSection x)) :=
        mul_le_mul_of_nonneg_left h2 hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ)).toSection x) := by ring


private lemma rfns_iteratedCovGrad_deTurckPrincipalCometricCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) {K : ℝ} (hK_nn : 0 ≤ K)
    (hK_bound : ∀ b : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 b
      ((cometricDoubleTraceField (I := I) g₀ 2).toSection b) ≤ K)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) i * K * (Module.finrank ℝ E : ℝ) ^ 2 *
        ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  classical
  have hcovgrad0 : covGrad (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2) = 0 :=
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2
  rw [deTurckPrincipalCometricCoeff_eq_appCcRS_doubleTrace_slotInsertEndo (I := I) (M := M) g₀ g₁]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I) (M := M) g₀
    i 4 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
  set Full : ℝ := ∑ l ∈ Finset.range (i + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 4 4 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
    with hFull
  have hFull_nn : 0 ≤ Full := by
    rw [hFull]
    exact Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (4 + l) x _)
  have happ_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := by rw [diagonalGridGrowthFactor]; positivity
  have hΦsum : ∑ k ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 4 2 k
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ K := by
    rw [Finset.sum_range_succ' (fun k => riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 4 2 k (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)) i]
    have hzero : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 4 2 (k + 1)
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) = 0 := by
      intro k _
      rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) g₀ 4 2
        (cometricDoubleTraceField (I := I) g₀ 2) hcovgrad0 k]
      simp only [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
        riemannianFiberNormSq_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add, iteratedCovGrad_zero]
    exact hK_bound x
  have hgridsum : ∑ k ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 4 2 k
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - k),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 4 4 l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤ K * Full := by
    calc ∑ k ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + k) x
              ((iteratedCovGrad (I := I) g₀ 4 2 k
                (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - k),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 4 4 l
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ ∑ k ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + k) x
              ((iteratedCovGrad (I := I) g₀ 4 2 k
                (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) * Full := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (2 + k) x _)
          rw [hFull]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (4 + l) x _)
          intro a ha
          simp only [Finset.mem_range] at ha ⊢
          omega
      _ = (∑ k ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + k) x
              ((iteratedCovGrad (I := I) g₀ 4 2 k
                (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)) * Full := by
          rw [← Finset.sum_mul]
      _ ≤ K * Full := mul_le_mul_of_nonneg_right hΦsum hFull_nn
  have hFullLe : Full ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
      ∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 2 l (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
    rw [hFull, Finset.mul_sum]
    refine Finset.sum_le_sum (fun l _ => ?_)
    have hb := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_succ_succ_le (I := I) (M := M) g₀
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) l x
    rw [show gInvDiffSlotCoeff (I := I) g₀ g₁ =
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) from by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro y
      rfl]
    exact hb
  calc diagonalGridGrowthFactor (E := E) i * ∑ k ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + k) x
              ((iteratedCovGrad (I := I) g₀ 4 2 k
                (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - k),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 4 4 l
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) i * (K * Full) := mul_le_mul_of_nonneg_left hgridsum happ_nn
    _ ≤ diagonalGridGrowthFactor (E := E) i * (K * ((Module.finrank ℝ E : ℝ) ^ 2 *
          ∑ l ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 2 l
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))) := by
        refine mul_le_mul_of_nonneg_left ?_ happ_nn
        exact mul_le_mul_of_nonneg_left hFullLe hK_nn
    _ = diagonalGridGrowthFactor (E := E) i * K * (Module.finrank ℝ E : ℝ) ^ 2 *
          ∑ l ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 2 l
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by ring


theorem ricciArmPrincipalCoeff_sub_perOrder_rfns_le_gInvDiffSlotCoeff
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)).toSection x)
      ≤ C i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  obtain ⟨K, hK_nn, hK_bound⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  refine ⟨fun i => (10 / 4 : ℝ) * diagonalGridGrowthFactor (E := E) i * K * (Module.finrank ℝ E : ℝ) ^ 2,
    ?_, ?_⟩
  · intro i
    have happ : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := by rw [diagonalGridGrowthFactor]; positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) happ) hK_nn) (sq_nonneg _)
  · intro g₁ i x
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ricciArmPrincipalCoeff_sub_le (I := I) (M := M)
      g₀ g₁ i x) ?_
    have hH3 := rfns_iteratedCovGrad_deTurckPrincipalCometricCoeff_le (I := I) (M := M)
      g₀ g₁ hK_nn hK_bound i x
    calc (10 / 4 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x)
        ≤ (10 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i * K * (Module.finrank ℝ E : ℝ) ^ 2 *
            ∑ l ∈ Finset.range (i + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)) :=
          mul_le_mul_of_nonneg_left hH3 (by norm_num)
      _ = (10 / 4 : ℝ) * diagonalGridGrowthFactor (E := E) i * K * (Module.finrank ℝ E : ℝ) ^ 2 *
            ∑ l ∈ Finset.range (i + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by ring


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem deTurckPrincipalCometricCoeff_toSection_clm_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) =
      cometricDoubleTraceFib (I := I) g₁ 2 x - cometricDoubleTraceFib (I := I) g₀ 2 x :=
  deTurckCoeff_clm_eq_doubleTrace_sub (I := I) (M := M) g₀ g₁ x


theorem deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
        C i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  obtain ⟨K, hK_nn, hK_bound⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i * K * (Module.finrank ℝ E : ℝ) ^ 2, ?_, ?_⟩
  · intro i
    have happ : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := by rw [diagonalGridGrowthFactor]; positivity
    exact mul_nonneg (mul_nonneg happ hK_nn) (sq_nonneg _)
  · intro g₁ i x
    exact rfns_iteratedCovGrad_deTurckPrincipalCometricCoeff_le (I := I) (M := M)
      g₀ g₁ hK_nn hK_bound i x





theorem coeff_grad_rfns_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 3 x
          ((covGrad (I := I) (M := M) g₀ 4 2
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((covGrad (I := I) (M := M) g₀ 2 2
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  obtain ⟨K, hK, hKpt⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  let n : ℝ := Module.finrank ℝ E
  refine ⟨n ^ 3 * K, mul_nonneg (by positivity) hK, ?_⟩
  intro g₁ x
  let Λ := gInvDiffRaisedEndoField (I := I) g₀ g₁
  let D := cometricDoubleTraceField (I := I) g₀ 2
  let S := endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 Λ
  have hgrad :
      covGrad (I := I) (M := M) g₀ 4 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) =
        ccOperatorFieldComp (I := I) (M := M) g₀ 4 5 3
          (slotExtend (I := I) (M := M) g₀ 4 2 D)
          (covGrad (I := I) (M := M) g₀ 4 4 S) := by
    rw [deTurckPrincipalCometricCoeff_eq_appCcRS_doubleTrace_slotInsertEndo
      (I := I) (M := M) g₀ g₁]
    change covGrad (I := I) (M := M) g₀ 4 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2 D S) = _
    rw [covGrad_appCcRS_eq,
      cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2,
      appCcRS_zero_left, zero_add]
  rw [hgrad, appCcRS_toSection]
  refine le_trans
    (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 4 5 3 x
      (show TensorRSSpace 5 3 I x from
        (slotExtend (I := I) (M := M) g₀ 4 2 D).toSection x)
      (show TensorRSSpace 4 5 I x from
        (covGrad (I := I) (M := M) g₀ 4 4 S).toSection x)) ?_
  have hD : riemannianFiberNormSq (I := I) (M := M) g₀ 5 3 x
      ((slotExtend (I := I) (M := M) g₀ 4 2 D).toSection x) ≤ n * K := by
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ 4 2 D x]
    exact mul_le_mul_of_nonneg_left (hKpt x) (by positivity)
  have hS : riemannianFiberNormSq (I := I) (M := M) g₀ 4 5 x
      ((covGrad (I := I) (M := M) g₀ 4 4 S).toSection x) ≤
        n ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((covGrad (I := I) (M := M) g₀ 2 2
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
    have hs := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_succ_succ_le
      (I := I) (M := M) g₀ Λ 1 x
    simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero,
      Nat.reduceAdd, gInvDiffSlotCoeff_eq_slotInsertEndoCc] using hs
  have hright : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 4 5 x
      ((covGrad (I := I) (M := M) g₀ 4 4 S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 5 x _
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 5 3 x
          ((slotExtend (I := I) (M := M) g₀ 4 2 D).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 5 x
          ((covGrad (I := I) (M := M) g₀ 4 4 S).toSection x)
        ≤ (n * K) * riemannianFiberNormSq (I := I) (M := M) g₀ 4 5 x
          ((covGrad (I := I) (M := M) g₀ 4 4 S).toSection x) :=
      mul_le_mul_of_nonneg_right hD hright
    _ ≤ (n * K) * (n ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
            ((covGrad (I := I) (M := M) g₀ 2 2
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)) :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg (by positivity) hK)
    _ = (n ^ 3 * K) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
            ((covGrad (I := I) (M := M) g₀ 2 2
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by ring

theorem coeff_jet_l2_sq
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        C i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff
      (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j
          (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j
          (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hC g₁ i x)
  refine hnorm.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j
        (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 2 2 j
      (gInvDiffSlotCoeff (I := I) g₀ g₁))]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j
      (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
