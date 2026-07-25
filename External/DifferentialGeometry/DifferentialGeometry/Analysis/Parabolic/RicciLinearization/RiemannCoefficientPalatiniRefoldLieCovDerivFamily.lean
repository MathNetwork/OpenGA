import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
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

def deTurckLieCovDerivRefoldC2Family (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  s • ∑ i : Fin 3, ε i • ((1 / 2 : ℝ) •
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) (q i)
      + curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))


omit [BoundarylessManifold I M] in
@[simp] lemma deTurckLieCovDerivRefoldC2Family_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) :
    deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε 0 = 0 := by
  rw [deTurckLieCovDerivRefoldC2Family, zero_smul]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_ccTensorUnitValueSection_domDomCongrSection_swap
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (p q' : TangentSpace I x) :
    Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x)
        ![(p : E), (q' : E)] =
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
        ![(q' : E), (p : E)] := by
  have hbridge : ∀ (S : SmoothCcTensor g₀ 0 2),
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ S x) =
        unitModel (I := I) (M := M) g₀ 2 S x := fun S => rfl
  rw [hbridge, hbridge, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureRefoldMonomialCoeffField_unitValue_trans_swap
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (σ.trans (Equiv.swap (0 : Fin 4) 1)) =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection]
  refine congrArg TensorRSSpace.ofCLM ?_
  refine ContinuousLinearMap.ext (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [curvatureActionMonomialTrace, curvatureActionMonomialTrace,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  have hcons : ∀ (p q' : TangentSpace I x) (j : Fin 4),
      (Fin.cons (p : E) (Fin.cons (q' : E) v) : Fin 4 → E) ((Equiv.swap (0 : Fin 4) 1) j) =
        (Fin.cons (q' : E) (Fin.cons (p : E) v) : Fin 4 → E) j := by
    intro p q' j
    fin_cases j <;> rfl
  have hstep : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (𝕜 := ℝ) (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) : Fin 4 → E)
            ((σ.trans (Equiv.swap (0 : Fin 4) 1)) i)) =
      Tensor0SSpace.toModel (𝕜 := ℝ) (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E)) v) : Fin 4 → E) (σ i)) := by
    intro a b
    congr 1
    refine congrArg _ ?_
    funext i
    exact hcons _ _ (σ i)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep a b))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [toModel_ccTensorUnitValueSection_domDomCongrSection_swap]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorUnitValueSection_add (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S') y =
      ccTensorUnitValueSection (I := I) (M := M) g₀ S y +
        ccTensorUnitValueSection (I := I) (M := M) g₀ S' y := by
  have h : ((S + S').toSection y : TensorRSSpace 0 2 I y) =
      (S.toSection y : TensorRSSpace 0 2 I y) + (S'.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorUnitValueSection_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ)
    (S : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S) y =
      c • ccTensorUnitValueSection (I := I) (M := M) g₀ S y := by
  have h : ((c • S).toSection y : TensorRSSpace 0 2 I y) =
      c • (S.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureRefoldMonomialCoeffField_unitValue_add
    (g₀ g₁ : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S'))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (S + S')) σ =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ
        + curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S')
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S') σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection,
    curvatureRefoldMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hadd : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x)
        + TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x))) G =
      curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G
        + curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x G := rfl
  rw [hadd]
  simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    TensorRSSpace.ofCLM]
  rw [curvatureActionMonomialTrace, curvatureActionMonomialTrace,
    curvatureActionMonomialTrace, curvatureRefoldMonomialFibFixedFrame_toModel,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_add]
  simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [add_mul]


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureRefoldMonomialCoeffField_unitValue_smul
    (g₀ g₁ : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (c • S)) σ =
      c • curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hsmul : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (c • TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x))) G =
      c • curvatureActionMonomialTrace (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G := rfl
  rw [hsmul]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    TensorRSSpace.ofCLM]
  rw [curvatureActionMonomialTrace, curvatureActionMonomialTrace,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_smul]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    (1 / 2 : ℝ) •
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σ
        + curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
          (σ.trans (Equiv.swap (0 : Fin 4) 1))) =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) σ := by
  rw [show curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) σ =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))) σ from by
    congr 1]
  rw [curvatureRefoldMonomialCoeffField_unitValue_smul,
    curvatureRefoldMonomialCoeffField_unitValue_add,
    curvatureRefoldMonomialCoeffField_unitValue_trans_swap]


omit [BoundarylessManifold I M] in
theorem deTurckLieCovDerivRefoldC2Family_eq_symmS_weight (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) :
    deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s =
      s • ∑ i : Fin 3, ε i •
        curvatureActionMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ T)) (q i) := by
  rw [deTurckLieCovDerivRefoldC2Family]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (q i)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
