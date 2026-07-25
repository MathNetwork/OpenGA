import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSubstitutionFiberNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.DeTurckLieArm2TraceCoeff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricConnDiffLoweredTrilinear
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.DeTurckLieArm1CoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieRealizedFamilyJointSmooth


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

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private theorem connDiffFib_comp_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SBundle.Tensor0SSpace 1 I x) :
    (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x) om =
      (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
          (inverseMetricSharpFib (I := I) g₁ x om)) := by
  rw [connDiffFib_apply, raisedKoszulFib_apply]
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [connDiffPairing_apply, raisedKoszulPairing_apply]
  set D : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) with hD
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁ x om with hu
  have hLHS : om (fun _ : Fin 1 => D) = g₁.inner x u D := by
    rw [← cotangentToDual_apply (I := I) (x := x) om D]
    rw [show cotangentToDual (I := I) (x := x) om D
          = cotangentToDualLinear (I := I) (x := x) om D from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₁ x om D]
  rw [hLHS]
  set P : TangentSpace I x := raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1) with hPdef
  rw [show (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x u)
        (fun _ : Fin 1 => P)
      = cotangentToDual (I := I) (x := x)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x u) P from
      (cotangentToDual_apply (I := I) (x := x) _ P).symm]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g₀ x u P]
  rw [g₀.symm x u P]
  have hPval : P = inverseMetricSharpFib (I := I) g₀ x
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) := by
    rw [hPdef, raisedKoszulVec_apply]
  have hPinner : g₀.inner x P u = cotangentToDual (I := I) (x := x)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u := by
    rw [hPval,
      show cotangentToDual (I := I) (x := x)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u
        = cotangentToDualLinear (I := I) (x := x)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u
        from rfl]
    rw [inverseMetricSharpFib_inner (I := I) g₀ x
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u]
  rw [hPinner, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g₁ x D u]
  rw [g₁.symm x D u, hu]

omit [CompactSpace M] in
private theorem deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 3))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieKoszulTraceFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have htr1 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 1)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))))
    hperm
  have hsharp := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') htr1
  have hflatfield : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ]
      Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) p.1
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (g0FlatField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  have hflat := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflatfield hsharp
  have hkos := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (corrField_raisedKoszulFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hflat
  refine hkos.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply, connDiffFib_comp_eq]

omit [CompactSpace M] in
private theorem deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 6))
    (κfam : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1)
    (hκ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (κfam p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLiePairTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1
          (κfam p) (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hprod := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Y p.1) κfam hYjoint hκ
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
        (Tensor0SBundle.Tensor0SSpace.toModel (κfam p)))) hprod
  have htr4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
              (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
              (Tensor0SBundle.Tensor0SSpace.toModel (κfam p)))))))
    hperm
  have htr2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => cometricDoubleTraceFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 4 p.1
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
              (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
                (Tensor0SBundle.Tensor0SSpace.toModel (κfam p))))))))
    htr4
  refine htr2.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply]

private theorem deTurckLieArm1CoreFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieArm1CoreFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hκA := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hκB := metricConnDiffLowered_bgFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hS2 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermInnerTwo
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hB := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermCorrection
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    hκB Y
  have hpermY := domDomCongrField_jointContMDiffOn (I := I) deTurckLieArm1VecSlotPerm
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hW0 := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hT2 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ : Π b : M, TangentSpace I b) p.1) hW0
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr deTurckLieArm1VecSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hpermY
  have hT3 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermOuterZero
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hT4 := deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1KoszulMidPerm Y
  have hT5 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermOuterTwo
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hs1 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hS2 hB
  have hs2 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs1 hT2
  have hs3 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs2 hT3
  have hs4 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs3 hT4
  have hs5 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs4 hT5
  refine hs5.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]

private theorem deTurckLieArm1Fib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieArm1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hWbg := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hW := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1) hWbg
    (fun p : M × ℝ => Y p.1) hYjoint
  have hcore := deTurckLieArm1CoreFib_realizedFam_apply_jointContMDiffOn (I := I)
    g₀ T T' hδ hδ' g_bg Y
  have hcoreswap := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap (0 : Fin 2) 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => deTurckLieArm1CoreFib (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1 (Y p.1)) hcore
  have hS3 := deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn (I := I)
    g₀ T T' hδ hδ' deTurckLieArm1KoszulZeroPerm Y
  have ha1 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hW hcore
  have ha2 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ ha1 hcoreswap
  have ha3 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ ha2 hS3
  refine ha3.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieArm1Fib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]

theorem deTurckLieArm1Coeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        ((deTurckLieArm1Coeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      deTurckLieArm1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => deTurckLieArm1Fib_realizedFam_apply_jointContMDiffOn (I := I)
      g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 t) ?_
  rw [deTurckLieArm1Coeff_toSection]

theorem deTurckLieArm1Coeff_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => deTurckLieArm1Coeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  deTurckLieArm1Coeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ' g_bg

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem jointTangent_add_local {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TangentSpace I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := E)
    (E := fun z : M => TangentSpace I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := E)
    (E := fun z : M => TangentSpace I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem jointTotalSpace0S_smulScalar_local {d : ℕ} {S : Set ℝ}
    (c : M × ℝ → ℝ)
    (hc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ c ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (c p • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((hc p₀ hp₀).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (c p) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (c p₀) (A p₀)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieEvalScalar_section_contMDiff
    (U : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 0 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 0 I x)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) x (U x)) := by
  have h := TensorMultilinear.contMDiff_section_apply (I := I) (M := M) (n := 0)
    (fun x => U x) U.contMDiff (fun i => i.elim0) (fun i => i.elim0)
  refine h.congr (fun x => ?_)
  rw [Tensor0SBundle.tensor0SSpace_evalScalar, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.apply_apply, Tensor0SBundle.Tensor0SSpace.toModelL_apply]
  exact congrArg _ (Subsingleton.elim _ _)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem dLieEmbedRS_section_contMDiff {d : ℕ}
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 d I z) x
        (show Tensor0SBundle.TensorRSSpace 0 d I x from embedRS (I := I) (M := M) x d (A x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 0 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace d I x)
    (φ := fun x : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x from
        embedRS (I := I) (M := M) x d (A x)))
  intro U
  have hscalar := dLieEvalScalar_section_contMDiff (I := I) U
  have hsmul := ContMDiff.smul_section
    (f := fun x : M => Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) x (U x))
    (s := fun x : M => A x) hscalar hA
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) ?_
  rfl

private noncomputable def dLiePack0S {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) :
    SmoothCcTensor g₀ 0 d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 0 d I x from embedRS (I := I) (M := M) x d (A x))
      contMDiff_toFun := dLieEmbedRS_section_contMDiff (I := I) A hA }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem dLiePack0S_unitEval {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) (y : M) :
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace d I y from
      (dLiePack0S (I := I) g₀ A hA).toSection y) (unitZeroSec (I := I) (M := M) y) = A y :=
  embedRS_unitZeroSec_apply (I := I) (M := M) y d (A y)


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem dLiePack0S_unitEvalSection {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A x))) :
    unitEvalSection (I := I) (M := M) g₀ d (dLiePack0S (I := I) g₀ A hA) = A := by
  funext y
  rw [unitEvalSection_apply]
  exact dLiePack0S_unitEval (I := I) g₀ A hA y

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem dLiePack0S_family_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (g₀ : SmoothRiemannianMetric I M)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hslice : ∀ s : ℝ, ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (A (x, s))))
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 d I z) p.1
        ((dLiePack0S (I := I) g₀ (fun x : M => A (x, p.2)) (hslice p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 0 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace d I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace d I p.1 from
        embedRS (I := I) (M := M) p.1 d (A p)))
    (S := S) ?_
  · refine hCLM.congr (fun p _ => ?_)
    rfl
  · intro U
    have hscalar : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) p.1 (U p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      (dLieEvalScalar_section_contMDiff (I := I) U).comp_contMDiffOn contMDiffOn_fst
    have hsmul := jointTotalSpace0S_smulScalar_local (I := I) (d := d) (S := S)
      (fun p : M × ℝ =>
        Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) p.1 (U p.1))
      hscalar A hA
    refine hsmul.congr (fun p _ => ?_)
    rfl

omit [NeZero (Module.finrank ℝ E)] in
private theorem dLieCovGradVal_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (g₀ : SmoothRiemannianMetric I M) (F : ℝ → SmoothCcTensor g₀ 0 d)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 d ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 d I z) q.1 ((F q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (d + 1) I p.1 from
          (covGrad (I := I) (M := M) g₀ 0 d (F p.2)).toSection p.1)
          (unitZeroSec (I := I) (M := M) p.1)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hstep := covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ 0 d F S hF
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
        (unitZeroSec (I := I) (M := M) p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn contMDiffOn_fst
  exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hstep hunit


omit [NeZero (Module.finrank ℝ E)] in
private theorem dLieCovGradVal_toNabla {d : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (F : SmoothCcTensor g₀ 0 d) (x : M) (v0 : TangentSpace I x)
    (m : Fin d → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (d + 1) I x from
          (covGrad (I := I) (M := M) g₀ 0 d F).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v0 m) =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M d (LeviCivita (I := I) g₀)
          (unitEvalSection (I := I) (M := M) g₀ d F) x v0) m := by
  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g₀ d F x (Fin.cons v0 m)]
  have hzero : (Fin.cons v0 m : Fin (d + 1) → TangentSpace I x) 0 = v0 := rfl
  have htail : Matrix.vecTail (Fin.cons v0 m) = m := by
    funext j
    simp [Matrix.vecTail]
  rw [hzero, htail, tensorCovDerivAt_def (I := I) (M := M) g₀ 0 d F x v0,
    covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ d F.toSection x v0]
  rfl

private def dLieTriEvalFn (V : Π b : M, Tensor0SBundle.Tensor0SSpace 3 I b)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun b => Tensor0SBundle.Tensor0SSpace.toModel (V b) (Fin.cons (A b) (Fin.cons (B b) ![C b]))


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma dLieTriMDiffAt_curried
    (s : ℕ) (W : Π x : M, Tensor0SBundle.Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem dLieNabla3_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SBundle.Tensor0SSpace 3 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 3 V x)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x])) =
      directionalDeriv (I := I) (dLieTriEvalFn (I := I) (M := M) V A B C) x v
        - Tensor0SBundle.Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        - Tensor0SBundle.Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        - Tensor0SBundle.Tensor0SSpace.toModel (V x)
            (Fin.cons (A x)
              (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
  classical
  set W₂ : Π b : M, Tensor0SBundle.Tensor0SSpace 2 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (A b) with hW₂
  have hW₂_mdiff : TensorSectionMDiffAt (I := I) 2 W₂ x :=
    dLieTriMDiffAt_curried (I := I) (M := M) 2 V hV A
  set W₁ : Π b : M, Tensor0SBundle.Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M W₂ b (B b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x :=
    dLieTriMDiffAt_curried (I := I) (M := M) 1 W₂ hW₂_mdiff B
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 2 V hV A v (Fin.cons (B x) ![C x])
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 W₂ hW₂_mdiff B v ![C x]
  have hpeel3 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff C v (fun i => Fin.elim0 i)
  have hbase : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v)
      (fun i => Fin.elim0 i) =
      directionalDeriv (I := I) (dLieTriEvalFn (I := I) (M := M) V A B C) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v]
    have hscalar : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) =
        dLieTriEvalFn (I := I) (M := M) V A B C := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
      change Tensor0SBundle.Tensor0SSpace.toModel (W₁ b)
        (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [hW₁]
      change Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M W₂ b (B b))
        (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
      rw [hW₂]
      change Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.curriedSection I M V b (A b))
        (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := A b)
        (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
      rw [dLieTriEvalFn]
      apply congrArg
      funext k
      fin_cases k <;> rfl
    rw [hscalar]
  have hcorrC : Tensor0SBundle.Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) =
      Tensor0SBundle.Tensor0SSpace.toModel (V x)
        (Fin.cons (A x)
          (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
    rw [hW₁]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W₂ x (B x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ x) (v0 := B x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  have hcorrB : Tensor0SBundle.Tensor0SSpace.toModel (W₂ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
          (Fin.cons (C x) (fun i => Fin.elim0 i))) =
      Tensor0SBundle.Tensor0SSpace.toModel (V x)
        (Fin.cons (A x)
          (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x])) := by
    rw [hW₂]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (A y)) = W₂ from rfl]
  rw [hpeel2]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M W₂ y (B y)) = W₁ from rfl]
  rw [show (![C x] : Fin 1 → TangentSpace I x) = Fin.cons (C x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel3, hbase, hcorrC, hcorrB]
  have hfin1 : ∀ (u : TangentSpace I x), (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons u (fun i => Fin.elim0 i) := by
    intro u; funext k; refine Fin.cases rfl (fun j => j.elim0) k
  rw [hfin1 ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v), hfin1 (C x)]
  ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLie_toModel_g0Flat (g : SmoothRiemannianMetric I M) (x : M)
    (w t : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (Fin.cons t (fun i => Fin.elim0 i)) = g.inner x w t := by
  have h1 : Tensor0SBundle.Tensor0SSpace.toModel
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) =
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (fun _ : Fin 1 => t) := by
    change (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) = _
    congr 1
    funext j
    refine Fin.cases rfl (fun j => j.elim0) j
  rw [h1, ← cotangentToDual_apply (I := I) (x := x) _ t]
  exact DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g x w t

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem dLieFlatSection_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (V x))) :=
  ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) V.contMDiff

private noncomputable def dLieFlatPack (g₀ : SmoothRiemannianMetric I M)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : SmoothCcTensor g₀ 0 1 :=
  dLiePack0S (I := I) g₀
    (fun x : M =>
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (V x))
    (dLieFlatSection_contMDiff (I := I) g₀ V)


omit [NeZero (Module.finrank ℝ E)] in
private theorem dLieFlatCovGradVal_eval (g₀ : SmoothRiemannianMetric I M)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (z t : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          (covGrad (I := I) (M := M) g₀ 0 1 (dLieFlatPack (I := I) g₀ V)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons z (Fin.cons t (fun i => Fin.elim0 i))) =
      g₀.inner x ((LeviCivita (I := I) g₀).toFun (fun b => V b) x z) t := by
  classical
  rw [dLieCovGradVal_toNabla (I := I) g₀ (dLieFlatPack (I := I) g₀ V) x z
    (Fin.cons t (fun i => Fin.elim0 i))]
  rw [show unitEvalSection (I := I) (M := M) g₀ 1 (dLieFlatPack (I := I) g₀ V) =
      (fun b : M =>
        DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ b (V b)) from
    dLiePack0S_unitEvalSection (I := I) g₀ _ _]
  set β : Π b : M, Tensor0SBundle.Tensor0SSpace 1 I b :=
    fun b => DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ b (V b)
    with hβdef
  set Tf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x t, smoothExtensionTangent_contMDiff (I := I) x t⟩
    with hTfdef
  have hTfx : Tf x = t := smoothExtensionTangent_eq (I := I) x t
  have hβm : TensorSectionMDiffAt (I := I) 1 β x :=
    (dLieFlatSection_contMDiff (I := I) g₀ V x).mdifferentiableAt (by simp)
  rw [show (Fin.cons t (fun i => Fin.elim0 i) : Fin 1 → TangentSpace I x) =
      Fin.cons (Tf x) (fun i => Fin.elim0 i) from by rw [hTfx]]
  rw [tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g₀ 0 β hβm Tf z
    (fun i => Fin.elim0 i)]
  rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
    (fun y : M => Tensor0SNabla.curriedSection I M β y (Tf y)) x z]
  have hscalar : Tensor0SNabla.scalarFn I M
      (fun y : M => Tensor0SNabla.curriedSection I M β y (Tf y)) =
      (fun y : M => g₀.inner y (V y) (Tf y)) := by
    funext y
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := β)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := β y) (v0 := Tf y) (vs := (fun i => Fin.elim0 i))]
    exact dLie_toModel_g0Flat (I := I) g₀ y (V y) (Tf y)
  rw [hscalar]
  have hVm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V b)) x :=
    V.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hTfm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Tf b)) x :=
    Tf.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc : IsMetricCompatibleOn (I := I) (LeviCivita (I := I) g₀).toFun g₀ Set.univ :=
    LeviCivita_isMetricCompatible (I := I) g₀
  have hcompat := hmc.apply (Y := fun b => V b) (Z := fun b => Tf b) hVm hTfm
    (Set.mem_univ x) z
  rw [hcompat]
  rw [dLie_toModel_g0Flat (I := I) g₀ x (V x)
    ((LeviCivita (I := I) g₀).toFun (fun y => Tf y) x z)]
  rw [hTfx]
  ring

private noncomputable def dLieLoweredPack (g₀ gm gA gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 3 :=
  dLiePack0S (I := I) g₀
    (fun x : M => metricConnDiffLoweredFib (I := I) gm gA gB x)
    (metricConnDiffLoweredFib_contMDiff (I := I) gm gA gB)


omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieDiagTrace_toModel (g₁ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (p + 2) I x) (u : Fin p → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ p x D) u =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) u)) := by
  classical
  rw [cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ p x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D]
  rw [← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Tensor0SBundle.Tensor0SSpace.toModelL_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (p + 1) x D)
      (smoothOrthoFrame (I := I) g₁ x e x))
    (v0 := smoothOrthoFrame (I := I) g₁ x e x) (vs := u)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x e x)
    (vs := Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) u)]


omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieFrameExpand_update (g₁ : SmoothRiemannianMetric I M) (x : M)
    (L3 : Tensor0SBundle.Tensor0SSpace 3 I x)
    (base : Fin 3 → TangentSpace I x) (i : Fin 3) (w : TangentSpace I x) :
    ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel L3
            (Function.update base i (smoothOrthoFrame (I := I) g₁ x e x)) *
          g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) =
      Tensor0SBundle.Tensor0SSpace.toModel L3 (Function.update base i w) := by
  classical
  have hexp := orthonormal_frame_vector_expansion (I := I) g₁ x w
    (fun e => smoothOrthoFrame (I := I) g₁ x e x)
    (fun e f => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x e f)
  calc ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel L3
            (Function.update base i (smoothOrthoFrame (I := I) g₁ x e x)) *
          g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) =
      ∑ e : Fin (Module.finrank ℝ E),
        (Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap
          (Function.update base i
            (g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) •
              smoothOrthoFrame (I := I) g₁ x e x)) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [(Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap.map_update_smul
          base i (g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x))
          (smoothOrthoFrame (I := I) g₁ x e x)]
        rw [smul_eq_mul, mul_comm]
        rfl
    _ = (Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap
          (Function.update base i
            (∑ e : Fin (Module.finrank ℝ E),
              g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) •
                smoothOrthoFrame (I := I) g₁ x e x)) :=
        ((Tensor0SBundle.Tensor0SSpace.toModel L3).toMultilinearMap.map_update_sum
          (t := Finset.univ) (i := i)
          (g := fun e : Fin (Module.finrank ℝ E) =>
            g₁.inner x w (smoothOrthoFrame (I := I) g₁ x e x) •
              smoothOrthoFrame (I := I) g₁ x e x) (m := base)).symm
    _ = Tensor0SBundle.Tensor0SSpace.toModel L3 (Function.update base i w) := by
        rw [← hexp]
        rfl

private def dLieBiPairPerm : Equiv.Perm (Fin 6) :=
  ⟨![2, 0, 4, 5, 3, 1], ![1, 5, 0, 4, 2, 3], by decide, by decide⟩

private def dLieCorrPermA : Equiv.Perm (Fin 6) :=
  ⟨![0, 4, 5, 3, 2, 1], ![0, 5, 4, 3, 1, 2], by decide, by decide⟩

private def dLieCorrPermB : Equiv.Perm (Fin 6) :=
  ⟨![3, 0, 5, 4, 2, 1], ![1, 5, 4, 0, 3, 2], by decide, by decide⟩

private def dLieCorrPermC : Equiv.Perm (Fin 6) :=
  ⟨![3, 4, 0, 5, 2, 1], ![2, 5, 4, 0, 1, 3], by decide, by decide⟩

private def dLieXiPermA : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩

private def dLieXiPermB : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieUpdateZero (x : M) (a b c u : TangentSpace I x) :
    Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 0 u = ![u, b, c] := by
  funext j
  fin_cases j <;> simp [Function.update]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieUpdateOne (x : M) (a b c u : TangentSpace I x) :
    Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 1 u = ![a, u, c] := by
  funext j
  fin_cases j <;> simp [Function.update]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieUpdateTwo (x : M) (a b c u : TangentSpace I x) :
    Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 2 u = ![a, b, u] := by
  funext j
  fin_cases j <;> simp [Function.update]


omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieCorrA_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₁ 4 x
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))) w =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3] := by
  classical
  rw [dLieDiagTrace_toModel (I := I) g₁ 4 x _ w]
  have hterm : ∀ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w)) =
        Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            ![smoothOrthoFrame (I := I) g₁ x e x, w 2, w 3] *
          g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))
            (smoothOrthoFrame (I := I) g₁ x e x) := by
    intro e
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hargL : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermA i)) ∘ Fin.castAdd 3) =
        ![smoothOrthoFrame (I := I) g₁ x e x, w 2, w 3] := by
      funext j
      fin_cases j <;> rfl
    have hargM : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermA i)) ∘ Fin.natAdd 3) =
        ![w 1, w 0, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    rw [hargL, hargM]
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x]
    rfl
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  have hupd : ∀ u : TangentSpace I x,
      (![u, w 2, w 3] : Fin 3 → TangentSpace I x) =
        Function.update
          (![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3] :
            Fin 3 → TangentSpace I x) 0 u :=
    fun u => (dLieUpdateZero (I := I) x _ (w 2) (w 3) u).symm
  rw [show (∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          ![smoothOrthoFrame (I := I) g₁ x e x, w 2, w 3] *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x)) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          (Function.update
            (![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3] :
              Fin 3 → TangentSpace I x) 0 (smoothOrthoFrame (I := I) g₁ x e x)) *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x) from
    Finset.sum_congr rfl (fun e _ => by rw [← hupd])]
  rw [dLieFrameExpand_update (I := I) g₁ x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (![PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0), w 2, w 3]) 0
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0))]
  exact congrArg _ (hupd _).symm


omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieCorrB_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₁ 4 x
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))) w =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3] := by
  classical
  rw [dLieDiagTrace_toModel (I := I) g₁ 4 x _ w]
  have hterm : ∀ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w)) =
        Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            ![w 1, smoothOrthoFrame (I := I) g₁ x e x, w 3] *
          g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))
            (smoothOrthoFrame (I := I) g₁ x e x) := by
    intro e
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hargL : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermB i)) ∘ Fin.castAdd 3) =
        ![w 1, smoothOrthoFrame (I := I) g₁ x e x, w 3] := by
      funext j
      fin_cases j <;> rfl
    have hargM : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermB i)) ∘ Fin.natAdd 3) =
        ![w 2, w 0, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    rw [hargL, hargM]
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x]
    rfl
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  have hupd : ∀ u : TangentSpace I x,
      (![w 1, u, w 3] : Fin 3 → TangentSpace I x) =
        Function.update
          (![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3] :
            Fin 3 → TangentSpace I x) 1 u :=
    fun u => (dLieUpdateOne (I := I) x (w 1) _ (w 3) u).symm
  rw [show (∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          ![w 1, smoothOrthoFrame (I := I) g₁ x e x, w 3] *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x)) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          (Function.update
            (![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3] :
              Fin 3 → TangentSpace I x) 1 (smoothOrthoFrame (I := I) g₁ x e x)) *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x) from
    Finset.sum_congr rfl (fun e _ => by rw [← hupd])]
  rw [dLieFrameExpand_update (I := I) g₁ x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (![w 1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0), w 3]) 1
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))]
  exact congrArg _ (hupd _).symm


omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieCorrC_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₁ 4 x
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))) w =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)] := by
  classical
  rw [dLieDiagTrace_toModel (I := I) g₁ 4 x _ w]
  have hterm : ∀ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
              (Tensor0SBundle.Tensor0SSpace.toModel
                (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
                  (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                    (Tensor0SBundle.Tensor0SSpace.toModel
                      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))))
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
            (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w)) =
        Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            ![w 1, w 2, smoothOrthoFrame (I := I) g₁ x e x] *
          g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))
            (smoothOrthoFrame (I := I) g₁ x e x) := by
    intro e
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hargL : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermC i)) ∘ Fin.castAdd 3) =
        ![w 1, w 2, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    have hargM : ((fun i : Fin 6 =>
        (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x)
          (Fin.cons (smoothOrthoFrame (I := I) g₁ x e x) w) : Fin 6 → TangentSpace I x)
          (dLieCorrPermC i)) ∘ Fin.natAdd 3) =
        ![w 3, w 0, smoothOrthoFrame (I := I) g₁ x e x] := by
      funext j
      fin_cases j <;> rfl
    rw [hargL, hargM]
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x]
    rfl
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  have hupd : ∀ u : TangentSpace I x,
      (![w 1, w 2, u] : Fin 3 → TangentSpace I x) =
        Function.update
          (![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)] :
            Fin 3 → TangentSpace I x) 2 u :=
    fun u => (dLieUpdateTwo (I := I) x (w 1) (w 2) _ u).symm
  rw [show (∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          ![w 1, w 2, smoothOrthoFrame (I := I) g₁ x e x] *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x)) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
          (Function.update
            (![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)] :
              Fin 3 → TangentSpace I x) 2 (smoothOrthoFrame (I := I) g₁ x e x)) *
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))
          (smoothOrthoFrame (I := I) g₁ x e x) from
    Finset.sum_congr rfl (fun e _ => by rw [← hupd])]
  rw [dLieFrameExpand_update (I := I) g₁ x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (![w 1, w 2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0)]) 2
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 3) (w 0))]
  exact congrArg _ (hupd _).symm


private theorem dLieTheta_eval (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w0 w1 w2 w3 : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) g₀ 0 3
            (dLieLoweredPack (I := I) g₀ g₁ g₁ g_bg)).toSection x)
          (unitZeroSec (I := I) (M := M) x)
        - cometricDoubleTraceFib (I := I) g₁ 4 x
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
              (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
                (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))
        - cometricDoubleTraceFib (I := I) g₁ 4 x
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
              (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
                (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))
        - cometricDoubleTraceFib (I := I) g₁ 4 x
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
              (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
                (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                      (Tensor0SBundle.Tensor0SSpace.toModel
                        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x))))))
        ![w0, w1, w2, w3] =
      g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x w0 w1 w2) w3 := by
  classical
  set Af : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w1, smoothExtensionTangent_contMDiff (I := I) x w1⟩
    with hAfdef
  set Bf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w2, smoothExtensionTangent_contMDiff (I := I) x w2⟩
    with hBfdef
  set Uf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w3, smoothExtensionTangent_contMDiff (I := I) x w3⟩
    with hUfdef
  set V0f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w0, smoothExtensionTangent_contMDiff (I := I) x w0⟩
    with hV0fdef
  have hAfx : Af x = w1 := smoothExtensionTangent_eq (I := I) x w1
  have hBfx : Bf x = w2 := smoothExtensionTangent_eq (I := I) x w2
  have hUfx : Uf x = w3 := smoothExtensionTangent_eq (I := I) x w3
  have hV0fx : V0f x = w0 := smoothExtensionTangent_eq (I := I) x w0
  have hCa : Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 4 x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr dLieCorrPermA
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))) ![w0, w1, w2, w3] =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x w1 w0, w2, w3] :=
    dLieCorrA_eval (I := I) g₀ g₁ g_bg x ![w0, w1, w2, w3]
  have hCb : Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 4 x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr dLieCorrPermB
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))) ![w0, w1, w2, w3] =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w2 w0, w3] :=
    dLieCorrB_eval (I := I) g₀ g₁ g_bg x ![w0, w1, w2, w3]
  have hCu : Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 4 x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr dLieCorrPermC
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))) ![w0, w1, w2, w3] =
      Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        ![w1, w2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w3 w0] :=
    dLieCorrC_eval (I := I) g₀ g₁ g_bg x ![w0, w1, w2, w3]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
  rw [hCa, hCb, hCu]
  rw [show (![w0, w1, w2, w3] : Fin 4 → TangentSpace I x) =
      Fin.cons w0 ![w1, w2, w3] from rfl]
  rw [dLieCovGradVal_toNabla (I := I) g₀ (dLieLoweredPack (I := I) g₀ g₁ g₁ g_bg) x w0
    ![w1, w2, w3]]
  rw [dLieLoweredPack, dLiePack0S_unitEvalSection (I := I) g₀ _ _]
  rw [show (![w1, w2, w3] : Fin 3 → TangentSpace I x) =
      Fin.cons (Af x) (Fin.cons (Bf x) ![Uf x]) from by rw [hAfx, hBfx, hUfx]; rfl]
  have hVsec : TensorSectionMDiffAt (I := I) 3
      (fun b : M => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b) x :=
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg x).mdifferentiableAt (by simp)
  rw [dLieNabla3_consEval_leibnizDefect (I := I) g₀
    (fun b : M => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b) hVsec Af Bf Uf w0]
  have htri : dLieTriEvalFn (I := I) (M := M)
      (fun b : M => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b) Af Bf Uf =
      (fun b : M => g₁.inner b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Af b) (Bf b)) (Uf b)) := by
    funext b
    change Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg b)
      (Fin.cons (Af b) (Fin.cons (Bf b) ![Uf b])) = _
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  rw [htri, directionalDeriv_eq]
  have hDsec := PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg
    (σ := fun b => Af b) (τ := fun b => Bf b) Af.contMDiff Bf.contMDiff
  have hYm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Af b) (Bf b))) x :=
    (hDsec x).mdifferentiableAt (by simp)
  have hUm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Uf b)) x :=
    (Uf.contMDiff x).mdifferentiableAt (by simp)
  have hmc : IsMetricCompatibleOn (I := I) (LeviCivita (I := I) g₁).toFun g₁ Set.univ :=
    LeviCivita_isMetricCompatible (I := I) g₁
  have hcompat := hmc.apply
    (Y := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Af b) (Bf b))
    (Z := fun b => Uf b) hYm hUm (Set.mem_univ x) w0
  rw [hcompat]
  have hc1 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Af b) x w0)
        (Fin.cons (Bf x) ![Uf x])) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        ((LeviCivita (I := I) g₀).toFun (fun b => Af b) x w0) (Bf x)) (Uf x) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hc2 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (Fin.cons (Af x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Bf b) x w0) ![Uf x])) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Af x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Bf b) x w0)) (Uf x) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hc3 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (Fin.cons (Af x)
        (Fin.cons (Bf x) ![(LeviCivita (I := I) g₀).toFun (fun b => Uf b) x w0])) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Af x) (Bf x))
        ((LeviCivita (I := I) g₀).toFun (fun b => Uf b) x w0) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hk1 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x w1 w0, w2, w3] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w1 w0) w2) w3 := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hk2 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      ![w1, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w2 w0, w3] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w1
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w2 w0)) w3 := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  have hk3 : Tensor0SBundle.Tensor0SSpace.toModel
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      ![w1, w2, PDE.DeTurck.connDiff (I := I) g₁ g₀ x w3 w0] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x w1 w2)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w3 w0) := by
    rw [metricConnDiffLoweredFib_toModel]
    rfl
  rw [hc1, hc2, hc3, hk1, hk2, hk3]
  have hker : connDiffCovDerivOp (I := I) g₁ g_bg x w0 w1 w2 =
      deTurckConnDiffCovDeriv (I := I) g₁ g_bg (fun b => V0f b) (fun b => Af b)
        (fun b => Bf b) x := by
    have hV0m : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V0f b)) x :=
      (V0f.contMDiff x).mdifferentiableAt (by simp)
    have hAm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Af b)) x :=
      (Af.contMDiff x).mdifferentiableAt (by simp)
    have hBm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Bf b)) x :=
      (Bf.contMDiff x).mdifferentiableAt (by simp)
    have h3 := dLaCovKernel_apply_field3 (I := I) g₁ g_bg x (fun b => V0f b)
      (fun b => Af b) (fun b => Bf b) hV0m hAm hBm
    beta_reduce at h3
    rw [hV0fx, hAfx, hBfx] at h3
    exact h3
  rw [hker, deTurckConnDiffCovDeriv]
  rw [hV0fx]
  have hsplit : ∀ (Yf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      (LeviCivita (I := I) g₀).toFun (fun b => Yf b) x w0 =
        (LeviCivita (I := I) g₁).toFun (fun b => Yf b) x w0
          - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x) w0 := by
    intro Yf
    have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Yf b)) x :=
      (Yf.contMDiff x).mdifferentiableAt (by simp)
    have h := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b => Yf b) hmd w0
    rw [h]
    abel
  rw [hsplit Af, hsplit Bf, hsplit Uf, hAfx, hBfx, hUfx]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

omit [CompactSpace M] in
theorem deTurckVectorFieldFlat_realizedFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hflatfield : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) p.1
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (g0FlatField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflatfield
    (deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg)

private theorem dLieWEndoA_apply_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set F : ℝ → SmoothCcTensor g₀ 0 1 := fun s : ℝ =>
    dLieFlatPack (I := I) g₀
      (PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
    with hFdef
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 1 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 1 I z) q.1 ((F q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hpack := dLiePack0S_family_jointContMDiffOn (I := I) g₀
      (A := fun p : M × ℝ =>
        DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1))
      (hslice := fun s : ℝ => dLieFlatSection_contMDiff (I := I) g₀
        (PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))
      (deTurckVectorFieldFlat_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg)
    exact hpack.congr (fun p _ => rfl)
  have hCovVal := dLieCovGradVal_jointContMDiffOn (I := I) (d := 1) g₀ F hF
  have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hι := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => Z p.1) hZjoint
    (α := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
        (unitZeroSec (I := I) (M := M) p.1)) hCovVal
  have hsharpField : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (inverseMetricSharpField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharpField hι
  refine happ.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hform : Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
      ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
        (unitZeroSec (I := I) (M := M) p.1)) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
        ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hm : m = Fin.cons (m 0) (fun i => Fin.elim0 i) := by
      funext j
      refine Fin.cases rfl (fun j => j.elim0) j
    have e1 : Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
          ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
            (unitZeroSec (I := I) (M := M) p.1))) m =
        g₀.inner p.1 ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)) (m 0) := by
      change Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I p.1 from
          (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
          (unitZeroSec (I := I) (M := M) p.1))
        (Fin.cons (Z p.1) m) = _
      refine Eq.trans (congrArg (fun args : Fin 1 → TangentSpace I p.1 =>
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            (covGrad (I := I) (M := M) g₀ 0 1 (F p.2)).toSection p.1)
            (unitZeroSec (I := I) (M := M) p.1))
          (Fin.cons (Z p.1) args)) hm) ?_
      exact dLieFlatCovGradVal_eval (I := I) g₀
        (PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg)
        p.1 (Z p.1) (m 0)
    have e2 : Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((LeviCivita (I := I) g₀).toFun
            (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) b) p.1 (Z p.1))) m =
        g₀.inner p.1 ((LeviCivita (I := I) g₀).toFun
          (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) b) p.1 (Z p.1)) (m 0) := by
      refine Eq.trans (congrArg (Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1
          ((LeviCivita (I := I) g₀).toFun
            (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) b) p.1 (Z p.1)))) hm) ?_
      exact dLie_toModel_g0Flat (I := I) g₀ p.1 _ (m 0)
    exact e1.trans e2.symm
  rw [hform, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]

private theorem dLieWEndoB_apply_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1) (Z p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hM := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hW := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hι1 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1) hW
    (α := fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1) hM
  have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hι2 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => Z p.1) hZjoint
    (α := fun p : M × ℝ => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
      ((PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1)
      (metricConnDiffLoweredFib (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) hι1
  have hsharp := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hι2
  refine hsharp.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hform : Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1)
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1) (Z p.1)) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hm : m = Fin.cons (m 0) (fun i => Fin.elim0 i) := by
      funext j
      refine Fin.cases rfl (fun j => j.elim0) j
    have e1 : Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1)
            (metricConnDiffLoweredFib (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      change Tensor0SBundle.Tensor0SSpace.toModel
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
        (Fin.cons ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
              Π b : M, TangentSpace I b) p.1)
          (Fin.cons (Z p.1) m)) = _
      rw [metricConnDiffLoweredFib_toModel]
      rfl
    have e2 : Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      refine Eq.trans (congrArg (Tensor0SBundle.Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
                Π b : M, TangentSpace I b) p.1) (Z p.1)))) hm) ?_
      exact dLie_toModel_g0Flat (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 _ (m 0)
    exact e1.trans e2.symm
  rw [hform, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]

theorem deTurckLieWEndo_realizedFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ =>
      deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Z
  have hA := dLieWEndoA_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Z
  have hB := dLieWEndoB_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Z
  have hsum := jointTangent_add_local (I := I)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hA hB
  refine hsum.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
            Π b : M, TangentSpace I b) b)) p.1 :=
    ((PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).contMDiff
        p.1).mdifferentiableAt (by simp)
  have hcd := PDE.DeTurck.connDiff_apply (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀
    (σ := fun b : M => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
        Π b : M, TangentSpace I b) b) hmd (Z p.1)
  change deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
      (Z p.1) = _
  rw [show deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
      (Z p.1) =
    (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toFun
      (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
          Π b : M, TangentSpace I b) b) p.1 (Z p.1) from rfl]
  rw [show (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
        Π b : M, TangentSpace I b) p.1 =
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
        Π b : M, TangentSpace I b) b) p.1 from rfl]
  rw [hcd]
  abel

private theorem deTurckLieEndoDerivation_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieDLbFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hΛ := deTurckLieWEndo_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have h0 := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ =>
      deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1) hΛ
    (A := fun p : M × ℝ => Y p.1) hY
  have h1 := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀
    (Λ := fun p : M × ℝ =>
      deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1) hΛ
    (A := fun p : M × ℝ => Y p.1) hY
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h0 h1
  refine hsum.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieDLbFib, ContinuousLinearMap.add_apply]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieBiArgY (x : M) (u0 u1 u2 u3 : TangentSpace I x)
    (v : Fin 2 → TangentSpace I x) :
    ((fun i : Fin 6 =>
      (Fin.cons u0 (Fin.cons u1 (Fin.cons u2 (Fin.cons u3 v))) : Fin 6 → TangentSpace I x)
        (dLieBiPairPerm i)) ∘ Fin.castAdd 4) = ![u2, u0] := by
  funext j
  fin_cases j <;> rfl


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieBiArgXi (x : M) (u0 u1 u2 u3 : TangentSpace I x)
    (v : Fin 2 → TangentSpace I x) :
    ((fun i : Fin 6 =>
      (Fin.cons u0 (Fin.cons u1 (Fin.cons u2 (Fin.cons u3 v))) : Fin 6 → TangentSpace I x)
        (dLieBiPairPerm i)) ∘ Fin.natAdd 2) = ![v 0, v 1, u3, u1] := by
  funext j
  fin_cases j <;> rfl


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieXiArgA (x : M) (a0 a1 a2 a3 : TangentSpace I x) :
    (fun i : Fin 4 => (![a0, a1, a2, a3] : Fin 4 → TangentSpace I x) (dLieXiPermA i)) =
      ![a0, a2, a3, a1] := by
  funext j
  fin_cases j <;> rfl


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dLieXiArgB (x : M) (a0 a1 a2 a3 : TangentSpace I x) :
    (fun i : Fin 4 => (![a0, a1, a2, a3] : Fin 4 → TangentSpace I x) (dLieXiPermB i)) =
      ![a1, a2, a3, a0] := by
  funext j
  fin_cases j <;> rfl

private theorem dLaBiContrFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (connDiffCovDerivBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hLraw := metricConnDiffLowered_bgFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hMraw := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hprodLM := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hLraw hMraw
  have hpermA := domDomCongrField_jointContMDiffOn (I := I) dLieCorrPermA
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodLM
  have hpermB := domDomCongrField_jointContMDiffOn (I := I) dLieCorrPermB
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodLM
  have hpermC := domDomCongrField_jointContMDiffOn (I := I) dLieCorrPermC
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodLM
  have hCa := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hpermA
  have hCb := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hpermB
  have hCu := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hpermC
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 3 I z) q.1
        (((fun s : ℝ => dLieLoweredPack (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hpack := dLiePack0S_family_jointContMDiffOn (I := I) g₀
      (A := fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
      (hslice := fun s : ℝ => metricConnDiffLoweredFib_contMDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      hLraw
    exact hpack.congr (fun p _ => rfl)
  have hGrad := dLieCovGradVal_jointContMDiffOn (I := I) (d := 3) g₀
    (fun s : ℝ => dLieLoweredPack (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) hF
  have hs1 := jointTotalSpace0S_sub_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hGrad hCa
  have hs2 := jointTotalSpace0S_sub_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs1 hCb
  have hs3 := jointTotalSpace0S_sub_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs2 hCu
  have hXi1 := domDomCongrField_jointContMDiffOn (I := I) dLieXiPermA
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hs3
  have hXi2 := domDomCongrField_jointContMDiffOn (I := I) dLieXiPermB
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hs3
  have hXi := jointTotalSpace0S_add_local (I := I) (d := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hXi1 hXi2
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hprodYXi := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Y p.1) _ hYjoint hXi
  have hperm := domDomCongrField_jointContMDiffOn (I := I) dLieBiPairPerm
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprodYXi
  have htr4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ' _ hperm
  have htr2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
    g₀ T T' hδ hδ' _ htr4
  have hneg := jointTotalSpace0S_smulFun_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (f := fun _ : ℝ => (-1 : ℝ)) contDiff_const _ htr2
  refine hneg.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [connDiffCovDerivBiContrFib, dLaBiContrFibFixedFrame_toModel,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  simp only [dLieDiagTrace_toModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [neg_one_mul, neg_one_mul, neg_inj]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Bundle.continuousMultilinearMap.modelProduct_apply, dLieBiArgY, dLieBiArgXi,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    dLieXiArgA, dLieXiArgB, dLieTheta_eval, dLieTheta_eval]
  exact mul_comm _ _

theorem dLaBiContrFib_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (connDiffCovDerivBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      connDiffCovDerivBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  exact dLaBiContrFib_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y

private theorem deTurckLieFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hA := dLaBiContrFib_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have hB := deTurckLieEndoDerivation_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hA hB
  refine hsum.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieFib, ContinuousLinearMap.add_apply]

theorem deTurckLieCoeffField_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      deTurckLieFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => deTurckLieFib_realizedFam_apply_jointContMDiffOn (I := I)
      g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [deTurckLieCoeffField_toSection]
  rfl

theorem deTurckLieCoeffField_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  deTurckLieCoeffField_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ' g_bg

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
