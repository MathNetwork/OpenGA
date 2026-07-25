import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound


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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma appCc_sub_left_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ₁ - Φ₂) W =
      operatorFieldApply (I := I) (M := M) g r s Φ₁ W - operatorFieldApply (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ₁ W - operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ₁ W).toSection x -
        (operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) = Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_add2_apply_local (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_sub2_apply_local (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S - S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v - unitModel (I := I) (M := M) g₀ 2 S' x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem deTurckLieTraceCoeff_apply_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (D : SmoothCcTensor g₀ 0 4) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ) D) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g₀ 4 D x)
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieTraceCoeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) =
      deTurckLieTraceFib (I := I) g₁ σ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply,
    cometricDoubleTraceFib_toModel, Tensor0SSpace.toModel_ofModel, modelDoubleTrace_apply]
  simp only [unitModel]


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem deTurckLieArm2PrincipalCoeff_apply_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g₀ 0 4) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg) D) x v =
      ((∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 D x
            ![v 0,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              v 1, (Module.finBasis ℝ E) k])
        + ∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 D x
              ![v 1,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                v 0, (Module.finBasis ℝ E) k])
      - ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 D x
            ![v 0, v 1,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (Module.finBasis ℝ E) k] := by
  rw [deTurckLieArm2PrincipalCoeff, appCc_sub_left_local, appCc_add_left,
    unitModel_sub2_apply_local, unitModel_add2_apply_local,
    deTurckLieTraceCoeff_apply_eq, deTurckLieTraceCoeff_apply_eq,
    traceHessianCoeff_apply_eq]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
        (by funext i; fin_cases i <;> rfl)
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
        (by funext i; fin_cases i <;> rfl)
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
      (by funext i; fin_cases i <;> rfl)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SBundle.Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma connDiffFib_toModel_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SBundle.Tensor0SSpace 1 I x) (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) om) w =
      Tensor0SBundle.Tensor0SSpace.toModel om
        (fun _ : Fin 1 => (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) (w 1))) := rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma deTurckLiePairTraceFib_toModel_eval (g₁ gA gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLiePairTraceFib (I := I) g₁ σ x
          (metricConnDiffLoweredFib (I := I) g₁ gA gB x) D) w =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr σ
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
            (Tensor0SBundle.Tensor0SSpace.toModel D)
            (Tensor0SBundle.Tensor0SSpace.toModel
              (metricConnDiffLoweredFib (I := I) g₁ gA gB x)))
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)))
            (Fin.cons ((Module.finBasis ℝ E) l)
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) w)))) := by
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply,
    Tensor0SSpace.toModel_ofModel, cometricDoubleTraceFib_toModel,
    cometricDoubleTraceFib_toModel, Tensor0SSpace.toModel_ofModel]
  simp only [modelDoubleTrace_apply]


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma deTurckLieKoszulTraceFib_toModel_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ σ x D) w =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel D)
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k,
            (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) (w 1))] := by
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    connDiffFib_toModel_eval, cometricDoubleTraceFib_toModel, domDomCongrFibRank_apply,
    Tensor0SSpace.toModel_ofModel, modelDoubleTrace_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieArm1CoreFib_toModel_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (a b : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) ![a, b] =
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![a,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x b ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k))
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![a,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                ((Module.finBasis ℝ E) k)) b)
      - Tensor0SBundle.Tensor0SSpace.toModel D
          ![a, b,
            (show E from
              (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                b,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) k))
              ((Module.finBasis ℝ E) l))
      - (∑ k : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b),
              (Module.finBasis ℝ E) k])
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                b,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k)) := by
  have hS2 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermInnerTwo x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![a,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x b ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermCorrection x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![a,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) b := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  have hT2 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)
        (domDomCongrFibRank (I := I) 3 deTurckLieArm1VecSlotPerm x D)) ![a, b] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![a, b,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)] := by
    rw [interior_product_toModel_eval, domDomCongrFibRank_apply,
      Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl)
  have hT3 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterZero x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              b,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l) := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  have hT4 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulMidPerm x D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b),
            (Module.finBasis ℝ E) k] := by
    rw [deTurckLieKoszulTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl)
  have hT5 : Tensor0SBundle.Tensor0SSpace.toModel
      (deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterTwo x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) ![a, b] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              b,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
    rw [deTurckLiePairTraceFib_toModel_eval]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl)
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hS2, hB, hT2, hT3, hT4, hT5]


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieArm1CoreFib_toModel_eval' (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (w : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) w =
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![w 0,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k))
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![w 0,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                ((Module.finBasis ℝ E) k)) (w 1))
      - Tensor0SBundle.Tensor0SSpace.toModel D
          ![w 0, w 1,
            (show E from
              (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                w 1,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) ((Module.finBasis ℝ E) k))
              ((Module.finBasis ℝ E) l))
      - (∑ k : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) (w 1)),
              (Module.finBasis ℝ E) k])
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis l)),
                w 1,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))] *
            g₁.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 0) ((Module.finBasis ℝ E) l))
              ((Module.finBasis ℝ E) k)) := by
  have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hw]
  exact deTurckLieArm1CoreFib_toModel_eval (I := I) g₀ g₁ g_bg x D (w 0) (w 1)


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieArm1_swapCore_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x
          (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D)) v =
      Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) ![v 1, v 0] := by
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg (fun t : Fin 2 → E => Tensor0SBundle.Tensor0SSpace.toModel
    (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x D) t)
    (by funext i; fin_cases i <;> rfl)


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieArm1_interiorProduct_eval (g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x) D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x),
          v 0, v 1] := by
  rw [interior_product_toModel_eval]
  exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
    (by funext i; fin_cases i <;> rfl)


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma deTurckLieArm1_koszulZero_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulZeroPerm x D) v =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
          ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k] := by
  rw [deTurckLieKoszulTraceFib_toModel_eval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg (fun t : Fin 3 → E => Tensor0SBundle.Tensor0SSpace.toModel D t)
    (by funext i; fin_cases i <;> rfl)


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieArm1Coeff_apply_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g₀ 0 3) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg) D) x v =
      unitModel (I := I) (M := M) g₀ 3 D x
          ![(show E from
              (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x),
            v 0, v 1]
      + ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 3 D x
                ![v 0,
                  cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis l)),
                  cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 1) ((Module.finBasis ℝ E) l))
                ((Module.finBasis ℝ E) k))
          - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                  ![v 0,
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                    ((Module.finBasis ℝ E) k)) (v 1))
          - unitModel (I := I) (M := M) g₀ 3 D x
              ![v 0, v 1,
                (show E from
                  (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
          - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    v 1,
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) ((Module.finBasis ℝ E) k))
                  ((Module.finBasis ℝ E) l))
          - (∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)),
                  (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)),
                  (Module.finBasis ℝ E) k])
          - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    v 1,
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) ((Module.finBasis ℝ E) l))
                  ((Module.finBasis ℝ E) k)))
      + ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 3 D x
                ![v 1,
                  cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis l)),
                  cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) ((Module.finBasis ℝ E) l))
                ((Module.finBasis ℝ E) k))
          - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                  ![v 1,
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                    ((Module.finBasis ℝ E) k)) (v 0))
          - unitModel (I := I) (M := M) g₀ 3 D x
              ![v 1, v 0,
                (show E from
                  (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
          - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    v 0,
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 1) ((Module.finBasis ℝ E) k))
                  ((Module.finBasis ℝ E) l))
          - (∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)),
                  (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 1) (v 0)),
                  (Module.finBasis ℝ E) k])
          - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 3 D x
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    v 0,
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 1) ((Module.finBasis ℝ E) l))
                  ((Module.finBasis ℝ E) k)))
      + ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 3 D x
            ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (Module.finBasis ℝ E) k] := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          D.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieArm1Coeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from
          deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) =
      deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieArm1Fib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [deTurckLieArm1_interiorProduct_eval, deTurckLieArm1CoreFib_toModel_eval',
    deTurckLieArm1_swapCore_eval, deTurckLieArm1CoreFib_toModel_eval,
    deTurckLieArm1_koszulZero_eval]
  simp only [unitModel]


omit [I.Boundaryless] in
theorem deTurckLieCoeffField_apply_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg) W) x v =
      (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                (v 1)
              + g₁.inner x
                (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                (v 0)))
        + (unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then
                deTurckVFCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0)) x
                else v 1)
            + unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then v 0
                else deTurckVFCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1)) x)) :=
  ricciArmOrder0DeTurckLieCoeff_appCc_eq (I := I) (M := M) g₀ g₁ g_bg W x v


omit [I.Boundaryless] in
theorem deTurckLieDLaCoeffField_apply_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg) W) x v =
      - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                (v 1)
              + g₁.inner x
                (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                (v 0)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieDLaCoeffField_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          Tensor0SBundle.TensorRSSpace.ofCLM (connDiffCovDerivBiContrFib (I := I) g₁ g_bg x)))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) =
      connDiffCovDerivBiContrFib (I := I) g₁ g_bg x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffCovDerivBiContrFib, dLaBiContrFibFixedFrame_toModel, neg_one_mul]
  refine congrArg (fun t => -t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, mul_comm]
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieDLbCoeffField_apply_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg) W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
          (fun j => if j = 0 then
            deTurckVFCovDeriv (I := I) g₁ g_bg
              (smoothExtensionTangent (I := I) x (v 0)) x
            else v 1)
        + unitModel (I := I) (M := M) g₀ 2 W x
          (fun j => if j = 0 then v 0
            else deTurckVFCovDeriv (I := I) g₁ g_bg
              (smoothExtensionTangent (I := I) x (v 1)) x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieDLbCoeffField_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          Tensor0SBundle.TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) =
      deTurckLieDLbFib (I := I) g₁ g_bg x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieDLbFib_toModel]
  rw [deTurckLieWEndo_apply, deTurckLieWEndo_apply]
  congr 1
  · rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp
  · rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma christoffelCorrection_chartModelBasis_pair_self
    (g : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    christoffelCorrection (I := I) g x x ((chartModelBasis E) j) ((chartModelBasis E) i) =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j m (extChartAt I x x) • (chartModelBasis E) m := by
  classical
  rw [christoffelCorrection_apply, trivToE_self_apply (I := I) x ((chartModelBasis E) i)]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_eq_same,
        Finsupp.single_eq_same, one_mul, one_mul]
    · intro j' _ hj'
      refine Finset.sum_eq_zero (fun m _ => ?_)
      rw [Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_eq_same, one_mul,
        Finsupp.single_apply, if_neg (Ne.symm hj'), zero_mul, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro i' _ hi'
    refine Finset.sum_eq_zero (fun j' _ => Finset.sum_eq_zero (fun m _ => ?_))
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (Ne.symm hi'), zero_mul, zero_mul,
      zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma leviCivita_toFun_chartBasis_eval_of_localComponents
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (σ : Π b : M, TangentSpace I b)
    (c : Fin (Module.finrank ℝ E) → E → ℝ)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (σ b)) x)
    (hc : ∀ p : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (c p) (extChartAt I x x))
    (hloc : ∀ b ∈ chartLeviCivitaGoodSet (I := I) x,
      σ b = ∑ p : Fin (Module.finrank ℝ E),
        c p (extChartAt I x b) • chartBasisVecFiber (I := I) x p b)
    (i : Fin (Module.finrank ℝ E)) :
    (LeviCivita (I := I) g₁).toFun σ x ((chartModelBasis E) i) =
      ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i (c p) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
              c m (extChartAt I x x)) •
          chartBasisVecFiber (I := I) x p x := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hy0_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx_good
  have hreprY : ∀ jj : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (∑ m : Fin (Module.finrank ℝ E),
        c m (extChartAt I x x) • (chartModelBasis E) m)) jj = c jj (extChartAt I x x) := by
    intro jj
    rw [Module.Basis.repr_sum_self]
  have hσx : σ x = ∑ m : Fin (Module.finrank ℝ E),
      c m (extChartAt I x x) • (chartModelBasis E) m := by
    rw [hloc x hx_good]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [chartBasisVecFiber_self (I := I) x m]
  have hrepr_x : chartE_section_repr (I := I) x σ x =
      ∑ m : Fin (Module.finrank ℝ E),
        c m (extChartAt I x x) • (chartModelBasis E) m := by
    rw [chartE_section_repr_eq_trivToE, trivToE_self_apply (I := I) x (σ x), hσx]
  have hev : (chartE_section_repr (I := I) x σ ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
      fun y : E => ∑ p : Fin (Module.finrank ℝ E), c p y • (chartModelBasis E) p := by
    have hopen : IsOpen (interior ((extChartAt I x).target : Set E) ∩
        (extChartAt I x).symm ⁻¹' chartLeviCivitaGoodSet (I := I) x) :=
      ContinuousOn.isOpen_inter_preimage
        ((continuousOn_extChartAt_symm x).mono interior_subset)
        isOpen_interior (chartLeviCivitaGoodSet_isOpen (I := I) x)
    have hmem : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) ∩
        (extChartAt I x).symm ⁻¹' chartLeviCivitaGoodSet (I := I) x := by
      refine ⟨hy0_int, ?_⟩
      change (extChartAt I x).symm (extChartAt I x x) ∈ chartLeviCivitaGoodSet (I := I) x
      rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
      exact hx_good
    filter_upwards [hopen.mem_nhds hmem] with y hy
    obtain ⟨hy_int, hy_pre⟩ := hy
    have hb_good : (extChartAt I x).symm y ∈ chartLeviCivitaGoodSet (I := I) x := hy_pre
    have hb_base : (extChartAt I x).symm y ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hb_good
    have hby : extChartAt I x ((extChartAt I x).symm y) = y :=
      (extChartAt I x).right_inv (interior_subset hy_int)
    change chartE_section_repr (I := I) x σ ((extChartAt I x).symm y) =
      ∑ p : Fin (Module.finrank ℝ E), c p y • (chartModelBasis E) p
    rw [chartE_section_repr_eq_trivToE, hloc _ hb_good, hby, map_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [ContinuousLinearMap.map_smul]
    congr 1
    change trivToE (I := I) x ((extChartAt I x).symm y)
        (trivFromE (I := I) x ((extChartAt I x).symm y) ((chartModelBasis E) p)) =
      (chartModelBasis E) p
    exact trivToE_trivFromE (I := I) x hb_base ((chartModelBasis E) p)
  have hfder : fderiv ℝ (chartE_section_repr (I := I) x σ ∘ (extChartAt I x).symm)
      (extChartAt I x x) ((chartModelBasis E) i) =
      ∑ p : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (c p) (extChartAt I x x) • (chartModelBasis E) p := by
    rw [hev.fderiv_eq]
    have hhas : HasFDerivAt
        (fun y : E => ∑ p : Fin (Module.finrank ℝ E), c p y • (chartModelBasis E) p)
        (∑ p : Fin (Module.finrank ℝ E),
          (fderiv ℝ (c p) (extChartAt I x x)).smulRight ((chartModelBasis E) p))
        (extChartAt I x x) :=
      HasFDerivAt.fun_sum (fun p _ =>
        ((hc p).hasFDerivAt.smul_const ((chartModelBasis E) p)))
    rw [hhas.fderiv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [ContinuousLinearMap.smulRight_apply]
    rfl
  have hchris : christoffelCorrection (I := I) g₁ x x
      (∑ m : Fin (Module.finrank ℝ E),
        c m (extChartAt I x x) • (chartModelBasis E) m) ((chartModelBasis E) i) =
      ∑ p : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
            c m (extChartAt I x x)) • (chartModelBasis E) p := by
    rw [christoffelCorrection_apply, trivToE_self_apply (I := I) x ((chartModelBasis E) i)]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [← Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul, hreprY m, mul_comm]
    · intro i' _ hi'
      refine Finset.sum_eq_zero (fun j' _ => Finset.sum_eq_zero (fun p _ => ?_))
      rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (Ne.symm hi'), zero_mul,
        zero_mul, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [LeviCivita_chart_apply (I := I) g₁ x hx_good hσ ((chartModelBasis E) i),
    chartLeviCivita_apply (I := I) g₁ x σ hx_good ((chartModelBasis E) i),
    trivToE_self_apply (I := I) x ((chartModelBasis E) i), hfder, hrepr_x, hchris,
    ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [chartBasisVecFiber_self (I := I) x p, map_add, ContinuousLinearMap.map_smul,
    ContinuousLinearMap.map_smul, trivFromE_self_apply (I := I) x ((chartModelBasis E) p),
    ← add_smul]


open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieCovDerivW_chartBasis_eq (g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (i : Fin (Module.finrank ℝ E)) :
    deTurckVFCovDeriv (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i)) x =
      ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i
            (fun y => chartDeTurckVFComp (I := I) g₁ g_bg x p y) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
              chartDeTurckVFComp (I := I) g₁ g_bg x m (extChartAt I x x)) •
          chartBasisVecFiber (I := I) x p x := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hy0_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx_good
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b)) x :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).mdifferentiableAt
  rw [deTurckVFCovDeriv, smoothExtensionTangent_eq]
  exact leviCivita_toFun_chartBasis_eval_of_localComponents (I := I) g₁ x
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b)
    (fun p y => chartDeTurckVFComp (I := I) g₁ g_bg x p y)
    hσ
    (fun p => chartDeTurckVFComp_differentiableAt_interior (I := I) g₁ g_bg x p hy0_int)
    (fun b hb => PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g₁ g_bg x hb)
    i


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieCovDerivA_chartBasis_eq (g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (i j k : Fin (Module.finrank ℝ E)) :
    deTurckConnDiffCovDeriv (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) j))
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) k)) x =
      ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i
            (fun y => chartChristoffel (I := I) g₁ x k j p y -
              chartChristoffel (I := I) g_bg x k j p y) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
              (chartChristoffel (I := I) g₁ x k j m (extChartAt I x x) -
                chartChristoffel (I := I) g_bg x k j m (extChartAt I x x)) -
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₁ x i j m (extChartAt I x x) *
              (chartChristoffel (I := I) g₁ x k m p (extChartAt I x x) -
                chartChristoffel (I := I) g_bg x k m p (extChartAt I x x)) -
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₁ x i k m (extChartAt I x x) *
              (chartChristoffel (I := I) g₁ x m j p (extChartAt I x x) -
                chartChristoffel (I := I) g_bg x m j p (extChartAt I x x))) •
          chartBasisVecFiber (I := I) x p x := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good
  have hy0_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx_good
  have hΓ : ∀ (g : SmoothRiemannianMetric I M) (a b d : Fin (Module.finrank ℝ E)),
      DifferentiableAt ℝ (chartChristoffel (I := I) g x a b d) (extChartAt I x x) := by
    intro g a b d
    exact ((chartChristoffel_contDiffOn_interior (I := I) g x a b d).contDiffAt
      (isOpen_interior.mem_nhds hy0_int)).differentiableAt (by simp)
  have hYm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (chartBasisVecFiber (I := I) x j b)) x :=
    PDE.DeTurck.chartBasisVecFiber_mdifferentiableAt (I := I) x j hx_base
  have hZm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (chartBasisVecFiber (I := I) x k b)) x :=
    PDE.DeTurck.chartBasisVecFiber_mdifferentiableAt (I := I) x k hx_base
  have hσA : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (chartBasisVecFiber (I := I) x j b)
          (chartBasisVecFiber (I := I) x k b))) x :=
    connDiff_pairing_mdiffAt (I := I) g₁ g_bg hYm hZm
  have hswap : deTurckConnDiffCovDeriv (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) j))
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) k)) x =
      deTurckConnDiffCovDeriv (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (fun b => chartBasisVecFiber (I := I) x j b)
        (fun b => chartBasisVecFiber (I := I) x k b) x := by
    have h1 := dLaCovKernel_apply_extend (I := I) g₁ g_bg x
      ((chartModelBasis E) i) ((chartModelBasis E) j) ((chartModelBasis E) k)
    have h2 := dLaCovKernel_apply_field (I := I) g₁ g_bg x ((chartModelBasis E) i)
      (fun b => chartBasisVecFiber (I := I) x j b)
      (fun b => chartBasisVecFiber (I := I) x k b) hYm hZm
    rw [← h1, ← h2]
    rw [show (fun b => chartBasisVecFiber (I := I) x j b) x = (chartModelBasis E) j from
        chartBasisVecFiber_self (I := I) x j,
      show (fun b => chartBasisVecFiber (I := I) x k b) x = (chartModelBasis E) k from
        chartBasisVecFiber_self (I := I) x k]
  have hterm1 : (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b
        (chartBasisVecFiber (I := I) x j b) (chartBasisVecFiber (I := I) x k b)) x
      ((chartModelBasis E) i) =
      ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i
            (fun y => chartChristoffel (I := I) g₁ x k j p y -
              chartChristoffel (I := I) g_bg x k j p y) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
              (chartChristoffel (I := I) g₁ x k j m (extChartAt I x x) -
                chartChristoffel (I := I) g_bg x k j m (extChartAt I x x))) •
          chartBasisVecFiber (I := I) x p x :=
    leviCivita_toFun_chartBasis_eval_of_localComponents (I := I) g₁ x
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b
        (chartBasisVecFiber (I := I) x j b) (chartBasisVecFiber (I := I) x k b))
      (fun p y => chartChristoffel (I := I) g₁ x k j p y -
        chartChristoffel (I := I) g_bg x k j p y)
      hσA
      (fun p => (hΓ g₁ k j p).fun_sub (hΓ g_bg k j p))
      (fun b hb => PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) g₁ g_bg x hb j k)
      i
  have hLCj : (LeviCivita (I := I) g₁).toFun
      (fun b => chartBasisVecFiber (I := I) x j b) x ((chartModelBasis E) i) =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ x i j m (extChartAt I x x) •
          chartBasisVecFiber (I := I) x m x := by
    rw [PDE.DeTurck.LeviCivita_chartBasisVecFiber_eq (I := I) g₁ x hx_good j
      ((chartModelBasis E) i)]
    rw [christoffelCorrection_chartModelBasis_pair_self (I := I) g₁ x i j, map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [chartBasisVecFiber_self (I := I) x m, ContinuousLinearMap.map_smul,
      trivFromE_self_apply (I := I) x ((chartModelBasis E) m)]
  have hLCk : (LeviCivita (I := I) g₁).toFun
      (fun b => chartBasisVecFiber (I := I) x k b) x ((chartModelBasis E) i) =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ x i k m (extChartAt I x x) •
          chartBasisVecFiber (I := I) x m x := by
    rw [PDE.DeTurck.LeviCivita_chartBasisVecFiber_eq (I := I) g₁ x hx_good k
      ((chartModelBasis E) i)]
    rw [christoffelCorrection_chartModelBasis_pair_self (I := I) g₁ x i k, map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [chartBasisVecFiber_self (I := I) x m, ContinuousLinearMap.map_smul,
      trivFromE_self_apply (I := I) x ((chartModelBasis E) m)]
  have hterm2 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₁).toFun
        (fun b => chartBasisVecFiber (I := I) x j b) x ((chartModelBasis E) i))
      (chartBasisVecFiber (I := I) x k x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x i j m (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k m p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k m p (extChartAt I x x))) •
        chartBasisVecFiber (I := I) x p x := by
    rw [hLCj, map_sum, ContinuousLinearMap.sum_apply]
    have hstep : ∀ m : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          (chartChristoffel (I := I) g₁ x i j m (extChartAt I x x) •
            chartBasisVecFiber (I := I) x m x)
          (chartBasisVecFiber (I := I) x k x) =
        ∑ p : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ x i j m (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k m p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k m p (extChartAt I x x))) •
          chartBasisVecFiber (I := I) x p x := by
      intro m
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
      rw [PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) g₁ g_bg x hx_good m k]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [smul_smul]
    rw [Finset.sum_congr rfl (fun m _ => hstep m), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_smul]
  have hterm3 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      (chartBasisVecFiber (I := I) x j x)
      ((LeviCivita (I := I) g₁).toFun
        (fun b => chartBasisVecFiber (I := I) x k b) x ((chartModelBasis E) i)) =
      ∑ p : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x i k m (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x m j p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x m j p (extChartAt I x x))) •
        chartBasisVecFiber (I := I) x p x := by
    rw [hLCk, map_sum]
    have hstep : ∀ m : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartBasisVecFiber (I := I) x j x)
          (chartChristoffel (I := I) g₁ x i k m (extChartAt I x x) •
            chartBasisVecFiber (I := I) x m x) =
        ∑ p : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ x i k m (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x m j p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x m j p (extChartAt I x x))) •
          chartBasisVecFiber (I := I) x p x := by
      intro m
      rw [ContinuousLinearMap.map_smul]
      rw [PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) g₁ g_bg x hx_good j m]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [smul_smul]
    rw [Finset.sum_congr rfl (fun m _ => hstep m), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_smul]
  rw [hswap]
  have hXeq : smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x =
      (chartModelBasis E) i :=
    smoothExtensionTangent_eq (I := I) x ((chartModelBasis E) i)
  change (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b
        (chartBasisVecFiber (I := I) x j b) (chartBasisVecFiber (I := I) x k b)) x
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        ((LeviCivita (I := I) g₁).toFun
          (fun b => chartBasisVecFiber (I := I) x j b) x
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
        (chartBasisVecFiber (I := I) x k x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartBasisVecFiber (I := I) x j x)
        ((LeviCivita (I := I) g₁).toFun
          (fun b => chartBasisVecFiber (I := I) x k b) x
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)) = _
  rw [hXeq, hterm1, hterm2, hterm3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← sub_smul, ← sub_smul]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
