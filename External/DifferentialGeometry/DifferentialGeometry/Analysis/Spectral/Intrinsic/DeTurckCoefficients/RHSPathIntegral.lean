import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSThreeArmCancel











noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold Tensor0SBundle ContinuousLinearMap MeasureTheory intervalIntegral
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem unitModel_add_app
    (g₀ : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (A + B) x v =
      unitModel (I := I) (M := M) g₀ 2 A x v +
        unitModel (I := I) (M := M) g₀ 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g₀ 2 (A + B) x =
      unitModel (I := I) (M := M) g₀ 2 A x +
        unitModel (I := I) (M := M) g₀ 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [hfun, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem unitModel_sub_app
    (g₀ : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (A - B) x v =
      unitModel (I := I) (M := M) g₀ 2 A x v -
        unitModel (I := I) (M := M) g₀ 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g₀ 2 (A - B) x =
      unitModel (I := I) (M := M) g₀ 2 A x -
        unitModel (I := I) (M := M) g₀ 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]
  rw [hfun, ContinuousMultilinearMap.sub_apply]



def realizedRHSArm
    (g₀ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in


theorem rhsTop_path_joint
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') := by
  have hLie := deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth
    (I := I) g₀ T T' hδ hδ' g_bg
  have hLich := linearizedRicci_arm2FieldLichnerowicz_jointSmooth
    (I := I) g₀ T T' hδ hδ'
  have hadd := joint_rs_add (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLich hLich
  have hsub := joint_rs_sub (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (deTurckLieArm2PrincipalCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1 +
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLie hadd
  refine hsub.congr (fun p _ => ?_)
  beta_reduce
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
    (E := fun z : M => TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [phi_realized_eq (I := I) (M := M) g₀ g_bg T T' hδ hδ' p.2,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]



def rhsTopPathIntegral
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
    (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' s))
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (rhsTop_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ')



def rhsLow0PathIntegral
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 2 2
    (fun s => rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (rhsLow0_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ')



def rhsLow1PathIntegral
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 3 2
    (fun s => rhsLow1Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (rhsLow1_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ')



theorem rhsChartSum_one
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w 1 =
      unitModel (I := I) (M := M) g₀ 2
        (realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ) x ![v, w] := by
  classical
  rw [rhsChartSum, realizedFam_one (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ']
  calc
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          deTurckRicciRHS (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x
            (chartBasisVecFiber (I := I) x i x)
            (chartBasisVecFiber (I := I) x k x) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS
        (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) g_bg x i k
        (self_mem_chartLeviCivitaGoodSet (I := I) x)]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          deTurckRicciRHS (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x
            (chartBasisVecFiber (I := I) x k x)
            (chartBasisVecFiber (I := I) x i x) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [deTurckRicciRHS_symm (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          unitModel (I := I) (M := M) g₀ 2
            (realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ) x
            ![(chartModelBasis E) k, (chartModelBasis E) i] := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T hδ_lt hδ
        (realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ) rfl]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, chartBasisVecFiber_self]
    _ = _ := unitModel_basis_expand_two (I := I) (M := M) g₀
      (realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ) x ![v, w]



theorem rhsChartSum_zero
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    rhsChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w 0 =
      unitModel (I := I) (M := M) g₀ 2
        (realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ') x ![v, w] := by
  classical
  rw [rhsChartSum, realizedFam_zero (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ']
  calc
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          deTurckRicciRHS (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x
            (chartBasisVecFiber (I := I) x i x)
            (chartBasisVecFiber (I := I) x k x) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS
        (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') g_bg x i k
        (self_mem_chartLeviCivitaGoodSet (I := I) x)]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          deTurckRicciRHS (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x
            (chartBasisVecFiber (I := I) x k x)
            (chartBasisVecFiber (I := I) x i x) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [deTurckRicciRHS_symm (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          unitModel (I := I) (M := M) g₀ 2
            (realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ') x
            ![(chartModelBasis E) k, (chartModelBasis E) i] := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' hδ'_lt hδ'
        (realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ') rfl]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, chartBasisVecFiber_self]
    _ = _ := unitModel_basis_expand_two (I := I) (M := M) g₀
      (realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ') x ![v, w]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in




theorem rhsArm_sub_eq_paths
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ -
        realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ' =
      operatorFieldApply (I := I) (M := M) g₀ 2 2
          (rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2
          (rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 4 2
          (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) :=
    realizedSmallSet_isOpen
  set Ψ₀ : ℝ → SmoothCcTensor g₀ 2 2 := fun s =>
    rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s with hΨ₀def
  set Ψ₁ : ℝ → SmoothCcTensor g₀ 3 2 := fun s =>
    rhsLow1Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s with hΨ₁def
  set Ψ₂ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' s) with hΨ₂def
  have hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Ψ₀
      (δ := δ) (δ' := δ') := by
    rw [hΨ₀def]
    exact rhsLow0_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hj1 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Ψ₁
      (δ := δ) (δ' := δ') := by
    rw [hΨ₁def]
    exact rhsLow1_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Ψ₂
      (δ := δ) (δ' := δ') := by
    rw [hΨ₂def]
    exact rhsTop_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hc0 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₀ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Ψ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hj0 x
  have hc1 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₁ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Ψ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hj1 x
  have hc2 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₂ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Ψ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hj2 x
  have hPi0 : rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Ψ₀
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 := rfl
  have hPi1 : rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 := rfl
  have hPi2 : rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψ₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, unitModel_sub_app]
  rw [← rhsChartSum_one (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x,
    ← rhsChartSum_zero (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x]
  rw [rhsSum_sub_eq_int (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x]
  have hI0 : IntervalIntegrable (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x ![v 0, v 1])
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g₀ 2 2 Ψ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSI hc0 x ![v 0, v 1]
  have hI1 : IntervalIntegrable (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x ![v 0, v 1])
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g₀ 3 2 Ψ₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSI hc1 x ![v 0, v 1]
  have hI2 : IntervalIntegrable (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x ![v 0, v 1])
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g₀ 4 2 Ψ₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSI hc2 x ![v 0, v 1]
  have hintegrand : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) 1 →
      rhsSumSlope (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
          x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x ![v 0, v 1] +
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x ![v 0, v 1] +
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x ![v 0, v 1] := by
    rw [MeasureTheory.ae_iff]
    have hnull : volume ({1} : Set ℝ) = 0 := by simp
    refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
    rw [Set.mem_setOf_eq, Classical.not_imp] at hs
    obtain ⟨hsmem, hsneq⟩ := hs
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
    refine hsneq ?_
    simpa only [hΨ₀def, hΨ₁def, hΨ₂def, unitModel_add_app] using
      rhsSlope_eq_arms (I := I) g₀ g_bg T T' hTsymm hT'symm
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) hsIoo
  rw [intervalIntegral.integral_congr_ae hintegrand]
  rw [intervalIntegral.integral_add (hI0.add hI1) hI2,
    intervalIntegral.integral_add hI0 hI1]
  rw [unitModel_add_app, unitModel_add_app, hPi0, hPi1, hPi2]
  rw [pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Ψ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0,
    pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Ψ₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1,
    pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Ψ₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
