import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffPieceConnDiffFeed
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffKappaPsiBFeed


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open TensorMultilinear
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam convexPerturbation
  convexPerturbation_gFibreOpBound realizedFam_inner_of_mem Icc_subset_realizedSmallSet)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM metricComparisonEndo
  gInvRaisedEndo_apply gInvRaisedEndo_eq_diff_add_id metricComparisonDiffEndo
  cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

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

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_omega_eval (g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    om (fun _ : Fin 1 => w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om) w := by
  rw [inverseMetricSharpFib_inner (I := I) g₁ x om w, cotangentToDualLinear_apply,
    cotangentToDual_apply]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_psiB_raw (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg).toSection x) om) YZ =
      g₁.inner x
        (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (YZ 1)
          (inverseMetricSharpFib (I := I) g₁ x om)) (YZ 0) := by
  classical
  have hdef : lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
        (sharpFlatEndoCc (I := I) g₀ g₁) := rfl
  rw [hdef, appCcRS_toSection, ContinuousLinearMap.comp_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
      (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om)) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
        (inverseMetricSharpFib (I := I) g₀ x
          (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
    rw [cometricRaiseSlot0Field_toSection]
    rw [cometricRaiseSlot0Fib_clm_apply]]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁ x om with hu
  set Xfib : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      (unitTensor (I := I) (M := M) x) with hXfib
  have happ : (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x u Xfib) YZ =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x u Xfib)
        (fun j : Fin 2 => ((YZ j : TangentSpace I x) : E)) := rfl
  rw [happ, interior_product_toModel_eval]
  have hXmodel : Tensor0SSpace.toModel Xfib =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)) x := rfl
  rw [hXmodel, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply,
    lieArm1_kappa_unitModel_apply]
  rfl

private def lieArm1PsiBKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) : TangentSpace I x :=
  cometricLmodel (I := I) g₁ x
    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      (show E →L[ℝ] ℝ from
        (g₁.inner x v).comp (PDE.DeTurck.connDiff (I := I) g_bg g₁ x w)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1PsiBKernel_inner (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    g₁.inner x (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x v w) u =
      g₁.inner x v (PDE.DeTurck.connDiff (I := I) g_bg g₁ x w u) := by
  rw [lieArm1PsiBKernel, cometricLmodel_covectorOfCLM_inner]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_psiB_hPsi (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg).toSection x) om) YZ =
      om (fun _ : Fin 1 => lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (YZ 0) (YZ 1)) := by
  rw [lieArm1_psiB_raw, lieArm1_omega_eval (I := I) g₁ x om]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (YZ 0) (YZ 1))]
  rw [lieArm1PsiBKernel_inner]
  exact g₁.symm x
    (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (YZ 1)
      (inverseMetricSharpFib (I := I) g₁ x om)) (YZ 0)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma lieArm1PsiBKernel_inner_neg (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    g₁.inner x (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x v w) u =
      -(g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w u) v) := by
  rw [lieArm1PsiBKernel_inner]
  rw [g₁.symm x v (PDE.DeTurck.connDiff (I := I) g_bg g₁ x w u)]
  rw [show PDE.DeTurck.connDiff (I := I) g_bg g₁ x w u =
      -PDE.DeTurck.connDiff (I := I) g₁ g_bg x w u from
    lieArm1_connDiff_antisymm (I := I) (M := M) g_bg g₁ x w u]
  rw [map_neg (g₁.inner x) (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w u)]
  rw [ContinuousLinearMap.neg_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_cometric_collapse_full (g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) •
          (show TangentSpace I x from
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) = w :=
  lieArm1_cometric_collapse (I := I) g₁ x w

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_slot2_collapse (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₀ c₁ : E) (X : TangentSpace I x) :
    Tensor0SSpace.toModel D ![c₀, c₁, (show E from X)] =
      ∑ j : Fin (Module.finrank ℝ E),
        g₁.inner x X ((Module.finBasis ℝ E) j) *
          Tensor0SSpace.toModel D
            ![c₀, c₁,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))] := by
  classical
  have hupd : ∀ z : E, (![c₀, c₁, z] : Fin 3 → E) =
      Function.update ![c₀, c₁, (0 : E)] 2 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hstep1 : Tensor0SSpace.toModel D ![c₀, c₁, (show E from X)] =
      Tensor0SSpace.toModel D (Function.update ![c₀, c₁, (0 : E)] 2
        (show E from (∑ j : Fin (Module.finrank ℝ E),
          g₁.inner x X ((Module.finBasis ℝ E) j) •
            (show TangentSpace I x from
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))) : TangentSpace I x))) := by
    refine Eq.trans (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (hupd (show E from X))) ?_
    exact congrArg
      (fun z : TangentSpace I x =>
        Tensor0SSpace.toModel D (Function.update ![c₀, c₁, (0 : E)] 2 (show E from z)))
      (lieArm1_cometric_collapse_full (I := I) g₁ x X).symm
  rw [hstep1]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (2 : Fin 3))
    (g := fun j : Fin (Module.finrank ℝ E) =>
      g₁.inner x X ((Module.finBasis ℝ E) j) •
        (show E from
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))))
    (m := ![c₀, c₁, (0 : E)])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  rw [hms]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(Tensor0SSpace.toModel D).map_update_smul ![c₀, c₁, (0 : E)] 2
    (g₁.inner x X ((Module.finBasis ℝ E) j))
    (show E from
      cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis j)))]
  rw [smul_eq_mul]
  refine congrArg (fun r : ℝ => g₁.inner x X ((Module.finBasis ℝ E) j) * r) ?_
  exact congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
    (hupd (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis j)))).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm1_slot0_collapse (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₁ c₂ : E) (X : TangentSpace I x) :
    Tensor0SSpace.toModel D ![(show E from X), c₁, c₂] =
      ∑ j : Fin (Module.finrank ℝ E),
        g₁.inner x X ((Module.finBasis ℝ E) j) *
          Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j)),
              c₁, c₂] := by
  classical
  have hupd : ∀ z : E, (![z, c₁, c₂] : Fin 3 → E) =
      Function.update ![(0 : E), c₁, c₂] 0 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hstep1 : Tensor0SSpace.toModel D ![(show E from X), c₁, c₂] =
      Tensor0SSpace.toModel D (Function.update ![(0 : E), c₁, c₂] 0
        (show E from (∑ j : Fin (Module.finrank ℝ E),
          g₁.inner x X ((Module.finBasis ℝ E) j) •
            (show TangentSpace I x from
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))) : TangentSpace I x))) := by
    refine Eq.trans (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (hupd (show E from X))) ?_
    exact congrArg
      (fun z : TangentSpace I x =>
        Tensor0SSpace.toModel D (Function.update ![(0 : E), c₁, c₂] 0 (show E from z)))
      (lieArm1_cometric_collapse_full (I := I) g₁ x X).symm
  rw [hstep1]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (0 : Fin 3))
    (g := fun j : Fin (Module.finrank ℝ E) =>
      g₁.inner x X ((Module.finBasis ℝ E) j) •
        (show E from
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))))
    (m := ![(0 : E), c₁, c₂])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  rw [hms]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(Tensor0SSpace.toModel D).map_update_smul ![(0 : E), c₁, c₂] 0
    (g₁.inner x X ((Module.finBasis ℝ E) j))
    (show E from
      cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis j)))]
  rw [smul_eq_mul]
  refine congrArg (fun r : ℝ => g₁.inner x X ((Module.finBasis ℝ E) j) * r) ?_
  exact congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
    (hupd (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis j)))).symm

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_cometricTrace_eq_chartInvGram (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l •
          F ((chartModelBasis E) l) ((chartModelBasis E) k) := by
  classical
  set L₁ : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (cometricLmodel (I := I) g₁ x).comp
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)) with hL₁
  set F' : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := F.comp L₁ with hF'
  have hFapp : ∀ (φ : E →L[ℝ] ℝ) (v : E),
      F' φ v = F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) v := by
    intro φ v
    rfl
  have htrace :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cDualBasis_trace_basis_indep
      (E := E) (chartModelBasis E) F').symm
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        F' ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => (hFapp _ _).symm)]
  rw [htrace]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hFapp ((chartModelBasis E).cDualBasis k) (chartModelBasis E k)]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum
    (I := I) g₁ x k]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_deTurckVF_cometric_trace (g₁ gB : SmoothRiemannianMetric I M) (x : M) :
    (∑ k : Fin (Module.finrank ℝ E),
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)) =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
        Π y : M, TangentSpace I y) x := by
  classical
  refine riemannianMetric_inner_left_injective (I := I) g₁ x (fun u => ?_)
  set F : E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E E ℝ
        (show E →L[ℝ] ℝ from (g₁.inner x u : TangentSpace I x →L[ℝ] ℝ))).comp
      (show E →L[ℝ] E →L[ℝ] E from
        (PDE.DeTurck.connDiff (I := I) g₁ gB x :
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)) with hFdef
  have h1 : g₁.inner x
      (∑ k : Fin (Module.finrank ℝ E),
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)) u =
      ∑ k : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) := by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [g₁.symm x _ u]
    rfl
  rw [h1, lieArm1_cometricTrace_eq_chartInvGram (I := I) g₁ x F]
  have h2 : ∀ k l : Fin (Module.finrank ℝ E),
      F ((chartModelBasis E) l) ((chartModelBasis E) k) =
        F ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    intro k l
    change (g₁.inner x u : TangentSpace I x →L[ℝ] ℝ)
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          ((chartModelBasis E) l) ((chartModelBasis E) k)) =
      (g₁.inner x u : TangentSpace I x →L[ℝ] ℝ)
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          ((chartModelBasis E) k) ((chartModelBasis E) l))
    rw [PDE.DeTurck.connDiff_symm (I := I) g₁ gB x
      ((chartModelBasis E) l) ((chartModelBasis E) k)]
  have h3 : g₁.inner x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x) u =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l •
          F ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    rw [show ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x) =
        (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x from rfl]
    rw [PDE.DeTurck.deTurckVF_apply_eq (I := I) g₁ gB x]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply]
    rw [chartBasisVecFiber_self (I := I) x k, chartBasisVecFiber_self (I := I) x l]
    refine congrArg (fun r : ℝ =>
      chartInvGramMatrix (I := I) g₁ x x k l • r) ?_
    rw [g₁.symm x _ u]
    rfl
  rw [h3]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [h2 k l]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_slot2_vf_trace (g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₀ c₁ : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![c₀, c₁,
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x))]) =
      Tensor0SSpace.toModel D
        ![c₀, c₁,
          (show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))] := by
  classical
  have hupd : ∀ z : E, (![c₀, c₁, z] : Fin 3 → E) =
      Function.update ![c₀, c₁, (0 : E)] 2 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (2 : Fin 3))
    (g := fun k : Fin (Module.finrank ℝ E) =>
      (show E from
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)))
    (m := ![c₀, c₁, (0 : E)])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  calc (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![c₀, c₁,
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x))])
      = ∑ k : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel D
            (Function.update ![c₀, c₁, (0 : E)] 2
              (show E from
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x))) :=
        Finset.sum_congr rfl (fun k _ =>
          congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _))
    _ = Tensor0SSpace.toModel D
          (Function.update ![c₀, c₁, (0 : E)] 2
            (show E from
              (∑ k : Fin (Module.finrank ℝ E),
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x) : TangentSpace I x))) :=
        hms.symm
    _ = Tensor0SSpace.toModel D
          (Function.update ![c₀, c₁, (0 : E)] 2
            (show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))) :=
        congrArg
          (fun z : TangentSpace I x =>
            Tensor0SSpace.toModel D
              (Function.update ![c₀, c₁, (0 : E)] 2 (show E from z)))
          (lieArm1_deTurckVF_cometric_trace (I := I) (M := M) g₁ gB x)
    _ = Tensor0SSpace.toModel D
          ![c₀, c₁,
            (show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))] :=
        (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _)).symm

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_slot0_vf_trace (g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c₁ c₂ : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![(show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x)),
            c₁, c₂]) =
      Tensor0SSpace.toModel D
        ![(show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x)),
          c₁, c₂] := by
  classical
  have hupd : ∀ z : E, (![z, c₁, c₂] : Fin 3 → E) =
      Function.update ![(0 : E), c₁, c₂] 0 z := by
    intro z
    funext i
    fin_cases i <;> simp [Function.update]
  have hms := ((Tensor0SSpace.toModel D).toMultilinearMap).map_update_sum
    (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := (0 : Fin 3))
    (g := fun k : Fin (Module.finrank ℝ E) =>
      (show E from
        (PDE.DeTurck.connDiff (I := I) g₁ gB x
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) : TangentSpace I x)))
    (m := ![(0 : E), c₁, c₂])
  simp only [ContinuousMultilinearMap.coe_coe] at hms
  calc (∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![(show E from
              (PDE.DeTurck.connDiff (I := I) g₁ gB x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) k) : TangentSpace I x)),
            c₁, c₂])
      = ∑ k : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel D
            (Function.update ![(0 : E), c₁, c₂] 0
              (show E from
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x))) :=
        Finset.sum_congr rfl (fun k _ =>
          congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _))
    _ = Tensor0SSpace.toModel D
          (Function.update ![(0 : E), c₁, c₂] 0
            (show E from
              (∑ k : Fin (Module.finrank ℝ E),
                (PDE.DeTurck.connDiff (I := I) g₁ gB x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ((Module.finBasis ℝ E) k) : TangentSpace I x) : TangentSpace I x))) :=
        hms.symm
    _ = Tensor0SSpace.toModel D
          (Function.update ![(0 : E), c₁, c₂] 0
            (show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x))) :=
        congrArg
          (fun z : TangentSpace I x =>
            Tensor0SSpace.toModel D
              (Function.update ![(0 : E), c₁, c₂] 0 (show E from z)))
          (lieArm1_deTurckVF_cometric_trace (I := I) (M := M) g₁ gB x)
    _ = Tensor0SSpace.toModel D
          ![(show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π y : M, TangentSpace I y) x)),
            c₁, c₂] :=
        (congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t) (hupd _)).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma lieArm1_neg_double_sum (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), -(f k l)) =
      -∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), f k l := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_neg_distrib]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p1 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
        ![(show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x)),
          ((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
    (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g_bg y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g_bg x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ((Module.finBasis ℝ E) k) : TangentSpace I x)),
          ((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E)])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  exact lieArm1_slot0_vf_trace (I := I) (M := M) g₁ g_bg x D
    ((m 0 : TangentSpace I x) : E) ((m 1 : TangentSpace I x) : E)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p2 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 0 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p3 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      -∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) (m 1) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
    (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
    (fun y u v => lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg y u v) x
    (fun om YZ => lieArm1_psiB_hPsi (I := I) (M := M) g₀ g₁ g_bg x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x
          (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 0 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 1)
          ((Module.finBasis ℝ E) k)))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      -(Tensor0SSpace.toModel D
          ![((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))] *
        g₁.inner x
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) j)) (m 1)))
    (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => by
      rw [lieArm1PsiBKernel_inner_neg (I := I) (M := M) g₁ g_bg x (m 1)
        ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) j)]
      ring))) ?_
  rw [Finset.sum_comm]
  exact lieArm1_neg_double_sum (E := E) _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p4 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E),
          (show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  exact lieArm1_slot2_vf_trace (I := I) (M := M) g₁ g₀ x D
    ((m 0 : TangentSpace I x) : E) ((m 1 : TangentSpace I x) : E)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p5 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x)),
          ((m 1 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j)),
            ((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot0_collapse (I := I) (M := M) g₁ x D
        ((m 1 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k)))) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p6 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) : TangentSpace I x)),
            ((Module.finBasis ℝ E) k)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  exact Finset.sum_congr rfl (fun k _ =>
    congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl))

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p7 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          ((m 1 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            ((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((m 1 : TangentSpace I x) : E)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p8 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 1 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p9 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      -∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((m 1 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) (m 0) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
    (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
    (fun y u v => lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg y u v) x
    (fun om YZ => lieArm1_psiB_hPsi (I := I) (M := M) g₀ g₁ g_bg x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (show E from
            (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 0)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x
          (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 0) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        ((m 1 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (lieArm1PsiBKernel (I := I) (M := M) g₁ g_bg x (m 0)
          ((Module.finBasis ℝ E) k)))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      -(Tensor0SSpace.toModel D
          ![((m 1 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))] *
        g₁.inner x
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) j)) (m 0)))
    (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => by
      rw [lieArm1PsiBKernel_inner_neg (I := I) (M := M) g₁ g_bg x (m 0)
        ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) j)]
      ring))) ?_
  rw [Finset.sum_comm]
  exact lieArm1_neg_double_sum (E := E) _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p10 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E), ((m 0 : TangentSpace I x) : E),
          (show E from
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![((m 1 : TangentSpace I x) : E), ((m 0 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  exact lieArm1_slot2_vf_trace (I := I) (M := M) g₁ g₀ x D
    ((m 1 : TangentSpace I x) : E) ((m 0 : TangentSpace I x) : E)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p11 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![(show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x)),
          ((m 0 : TangentSpace I x) : E),
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j)),
            ((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot0_collapse (I := I) (M := M) g₁ x D
        ((m 0 : TangentSpace I x) : E)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k)))) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p12 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (show E from
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) (m 0) : TangentSpace I x)),
            ((Module.finBasis ℝ E) k)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  exact Finset.sum_congr rfl (fun k _ =>
    congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl))

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p13 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis l)),
              ((m 0 : TangentSpace I x) : E),
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k) := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
        ![cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          ((m 0 : TangentSpace I x) : E),
          (show E from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1)
              ((Module.finBasis ℝ E) k) : TangentSpace I x))])
    (Finset.sum_congr rfl (fun k _ =>
      congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
        (by funext i; fin_cases i <;> rfl))) ?_
  refine Eq.trans
    (b := ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
          ((Module.finBasis ℝ E) j) *
        Tensor0SSpace.toModel D
          ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            ((m 0 : TangentSpace I x) : E),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))])
    (Finset.sum_congr rfl (fun k _ =>
      lieArm1_slot2_collapse (I := I) (M := M) g₁ x D
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((m 0 : TangentSpace I x) : E)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k)))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm1_match_p14 (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![(show E from
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) : TangentSpace I x)),
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            ((Module.finBasis ℝ E) k)] := by
  classical
  rw [lieArm1Piece_toModel (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
    (connDiffSection (I := I) g₁ g₀)
    (fun y u v => PDE.DeTurck.connDiff (I := I) g₁ g₀ y u v) x
    (fun om YZ => connDiffFib_apply_eval (I := I) g₁ g₀ x om YZ) D m]
  exact Finset.sum_congr rfl (fun k _ =>
    congrArg (fun t : Fin 3 → E => Tensor0SSpace.toModel D t)
      (by funext i; fin_cases i <;> rfl))

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieArm1_coeff_pieces_pointwise (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
            + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
                (connDiffSection (I := I) g₁ g₀)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀))
            + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
                (connDiffSection (I := I) g₁ g₀)
              - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
                (connDiffSection (I := I) g₁ g₀))
            + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) := by
  classical
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D)
      (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel D
          ![(show E from
              ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x)),
            ((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E)]
        + ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Tensor0SSpace.toModel D
                  ![((m 0 : TangentSpace I x) : E),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
                  ((Module.finBasis ℝ E) k))
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![((m 0 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                      ((Module.finBasis ℝ E) k)) (m 1))
            - Tensor0SSpace.toModel D
                ![((m 0 : TangentSpace I x) : E), ((m 1 : TangentSpace I x) : E),
                  (show E from
                    ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))]
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 1 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) k))
                    ((Module.finBasis ℝ E) l))
            - (∑ k : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)),
                    (show E from
                      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) :
                        TangentSpace I x)),
                    ((Module.finBasis ℝ E) k)])
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 1 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
                    ((Module.finBasis ℝ E) k)))
        + ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Tensor0SSpace.toModel D
                  ![((m 1 : TangentSpace I x) : E),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis l)),
                    cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))] *
                g₁.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) ((Module.finBasis ℝ E) l))
                  ((Module.finBasis ℝ E) k))
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![((m 1 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
                      ((Module.finBasis ℝ E) k)) (m 0))
            - Tensor0SSpace.toModel D
                ![((m 1 : TangentSpace I x) : E), ((m 0 : TangentSpace I x) : E),
                  (show E from
                    ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x))]
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 0 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) k))
                    ((Module.finBasis ℝ E) l))
            - (∑ k : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                  ![cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)),
                    (show E from
                      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) (m 0) :
                        TangentSpace I x)),
                    ((Module.finBasis ℝ E) k)])
            - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                Tensor0SSpace.toModel D
                    ![cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis l)),
                      ((m 0 : TangentSpace I x) : E),
                      cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k))] *
                  g₁.inner x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 1) ((Module.finBasis ℝ E) l))
                    ((Module.finBasis ℝ E) k)))
        + ∑ k : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel D
              ![(show E from
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) : TangentSpace I x)),
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                ((Module.finBasis ℝ E) k)] := by
    rw [show (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
      deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x D from rfl]
    rw [deTurckLieArm1Fib]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
    rw [deTurckLieArm1_interiorProduct_eval, deTurckLieArm1CoreFib_toModel_eval',
      deTurckLieArm1_swapCore_eval, deTurckLieArm1CoreFib_toModel_eval,
      deTurckLieArm1_koszulZero_eval]
  rw [hL]
  have hR : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
          + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)).toSection x) D)
      (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
            (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
          (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
        + (Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          + Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
                  (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E)))
        + (Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          + Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
                  (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E))
          - Tensor0SSpace.toModel
              ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
                (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
                  (connDiffSection (I := I) g₁ g₀)).toSection x) D)
              (fun j : Fin 2 => ((m j : TangentSpace I x) : E)))
        + Tensor0SSpace.toModel
            ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
              (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
                (connDiffSection (I := I) g₁ g₀)).toSection x) D)
            (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) := by
    simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply]
    rfl
  rw [hR]
  rw [lieArm1_match_p1 (I := I) (M := M) g₀ g₁ g_bg x D m,
    lieArm1_match_p2 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p3 (I := I) (M := M) g₀ g₁ g_bg x D m,
    lieArm1_match_p4 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p5 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p6 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p7 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p8 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p9 (I := I) (M := M) g₀ g₁ g_bg x D m,
    lieArm1_match_p10 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p11 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p12 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p13 (I := I) (M := M) g₀ g₁ x D m,
    lieArm1_match_p14 (I := I) (M := M) g₀ g₁ x D m]
  ring

end DifferentialGeometry.Integral.Connection

end
