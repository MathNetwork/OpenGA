import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamLinearizedChristoffel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem corrField_realizedFam_chartRiemannTensor_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartRiemannTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i j k l (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_riemann (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j k l hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j k l r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem corrField_realizedFam_chartChristoffel_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartChristoffel (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma corrField_realizedFam_chartGramMatrix_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := hG.1 i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartGramOnE (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartGramOnE_def, (extChartAt I α).left_inv hxsrc]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma corrField_genJointGram_const_g0
    (g₀ : SmoothRiemannianMetric I M) (α : M) {S : Set ℝ} :
    ChartGramFamilyJointSmoothNondegenerate (I := I) (fun _ : ℝ => g₀) α S := by
  refine ⟨?_, ?_⟩
  · intro a b s₀ y₀ _hs hy
    have hsnd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) (s₀, y₀) := contDiffAt_snd
    exact (((chartGramOnE_contDiffOn (I := I) g₀ α a b).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) g₀ α hx

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma corrField_chartChristoffel_g0_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (α : M) (i j k : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartChristoffel (I := I) g₀ α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hG := corrField_genJointGram_const_g0 (I := I) g₀ α (S := S)
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I) (fun _ : ℝ => g₀) α hG i j k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) g₀ α i j k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma corrField_chartInvGramMatrix_g0_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I) g₀ α p.1 i j)
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hG := corrField_genJointGram_const_g0 (I := I) g₀ α (S := S)
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartInvGramOnE_contDiffAt_joint (I := I) (fun _ : ℝ => g₀) α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I) g₀ α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma omAppChartBasisVec_jointContMDiffOn
    (om : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x⟯)
    (α : M) (p : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => (om q.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α p q.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  intro p₀ hp₀
  have hOmon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) q.1 (om q.1))
      ((chartAt H α).source ×ˢ S) :=
    (om.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
  have hOmAt := hOmon p₀ hp₀
  have hvbasis : ∀ i : Fin 1, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (![fun b : M => chartBasisVecFiber (I := I) α p b] i q.1))
      ((chartAt H α).source ×ˢ S) p₀ := by
    intro i
    fin_cases i
    exact (chartBasisVec_jointContMDiffOn (I := I) α p p₀
      ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 1
    (s := (chartAt H α).source ×ˢ S) (p₀ := p₀)
    (fun b : M => om b) hOmAt
    (![fun b : M => chartBasisVecFiber (I := I) α p b]) hvbasis
  have hcoe : ∀ q : M × ℝ,
      Tensor0SBundle.Tensor0SSpace.toModel (om q.1)
          (fun i : Fin 1 => ![fun b : M => chartBasisVecFiber (I := I) α p b] i q.1) =
        (om q.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α p q.1) := by
    intro q
    rw [Tensor0SBundle.Tensor0SSpace.toModel]
    rw [tensor0SSpace_continuousLinearEquiv_apply]
    refine congrArg (fun w : Fin 1 → TangentSpace I q.1 => (om q.1) w) ?_
    funext i
    fin_cases i
    rfl
  refine happly.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q _
    exact (hcoe q).symm
  · exact (hcoe p₀).symm

private noncomputable def corrField_outerPairBilinChartα (g : SmoothRiemannianMetric I M) (α : M)
    {x : M} (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g α x k l * K X (chartBasisVecFiber (I := I) α k x)) •
          (ContinuousLinearMap.flip Dd (chartBasisVecFiber (I := I) α l x))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma corrField_outerPairBilinChartα_apply (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    corrField_outerPairBilinChartα (I := I) g α K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k l *
          (K X (chartBasisVecFiber (I := I) α k x) *
            Dd X' (chartBasisVecFiber (I := I) α l x)) := by
  rw [corrField_outerPairBilinChartα, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma corrField_double_frame_bilin_trace_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (K (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x) *
            Dd (chartBasisVecFiber (I := I) α n x) (chartBasisVecFiber (I := I) α l x))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      corrField_outerPairBilinChartα (I := I) g α K Dd (B a) (B a) := by
    intro a
    rw [corrField_outerPairBilinChartα_apply]
    have h := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply, smul_eq_mul] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
    (corrField_outerPairBilinChartα (I := I) g α K Dd) B hB
  simp only [smul_eq_mul] at hout
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [corrField_outerPairBilinChartα_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma corrField_riemannBiContrFib_toModel_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannBiContrFib (I := I) g x D) v =
      2 * ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (g.inner x (riemannOp (LeviCivita (I := I) g) x (v 0)
              (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x)) (v 1) *
            Tensor0SSpace.toModel D
              ![(chartBasisVecFiber (I := I) α n x : E),
                (chartBasisVecFiber (I := I) α l x : E)])) := by
  classical
  set Bf : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with hBf
  have hBf_on : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (Bf i) (Bf j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (riemannOp (LeviCivita (I := I) g) x (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
        frameRiemannKernel (I := I) g x (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) :=
    fun a b => by
      rw [frameRiemannKernel_apply (I := I) g x (v 0) (v 1) (Bf a) (Bf b),
        bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
      rfl
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsummand a b))]
  rw [corrField_double_frame_bilin_trace_chartα (I := I) g α hxbase
    (frameRiemannKernel (I := I) g x (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D)) Bf hBf_on]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x m n * t) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [frameRiemannKernel_apply,
    bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D)
      (chartBasisVecFiber (I := I) α n x) (chartBasisVecFiber (I := I) α l x)]
  rfl

omit [CompactSpace M] in
private lemma corrField_riemannChartLoweredScalar_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
        (riemannOp (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
          (chartBasisVecFiber (I := I) α i p.1)
          (chartBasisVecFiber (I := I) α j p.1)
          (chartBasisVecFiber (I := I) α k p.1))
        (chartBasisVecFiber (I := I) α l p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hRm : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ m : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α k i j m
            (extChartAt I α p.1) *
          chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m l)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun m _ => ?_)
    have hriem := corrField_realizedFam_chartRiemannTensor_jointContMDiffOn
      (I := I) g₀ T T' hδ hδ' α k i j m
    have hgram := corrField_realizedFam_chartGramMatrix_jointContMDiffOn
      (I := I) g₀ T T' hδ hδ' α m l
    exact hriem.mul hgram
  refine hRm.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx
  set gs := realizedFam (I := I) g₀ T T' hδ hδ' p.2 with hgs
  rw [riemannOp_chartBasisVec_alpha_eq (I := I) gs α k i j hxgood]
  rw [map_sum]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g_inner_eq_chartGramMatrix_basis (I := I) gs α p.1 m l, mul_comm]

omit [CompactSpace M] in
private lemma corrField_riemannBiContrFibAppY_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x⟯)
    (α : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel
        (riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
        ![(chartBasisVecFiber (I := I) α (σ 0) p.1 : E),
          (chartBasisVecFiber (I := I) α (σ 1) p.1 : E)])
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYbasis : ∀ n l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (Y p.1)
          ![(chartBasisVecFiber (I := I) α n p.1 : E), (chartBasisVecFiber (I := I) α l p.1 : E)])
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro n l p₀ hp₀
    have hYon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hYmdiff := hYon p₀ hp₀
    have hvbasis : ∀ i : Fin 2, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (![fun b : M => chartBasisVecFiber (I := I) α n b,
              fun b : M => chartBasisVecFiber (I := I) α l b] i p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ := by
      intro i
      fin_cases i
      · exact (chartBasisVec_jointContMDiffOn (I := I) α n p₀
          ⟨hp₀.1, Set.mem_univ _⟩).mono
          (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
      · exact (chartBasisVec_jointContMDiffOn (I := I) α l p₀
          ⟨hp₀.1, Set.mem_univ _⟩).mono
          (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 2
      (s := (chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) (p₀ := p₀)
      (fun b : M => Y b) hYmdiff
      (![fun b : M => chartBasisVecFiber (I := I) α n b,
          fun b : M => chartBasisVecFiber (I := I) α l b]) hvbasis
    refine happly.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      congr 1
      funext i; fin_cases i <;> rfl
    · congr 1; funext i; fin_cases i <;> rfl
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => 2 * ∑ m, ∑ n, chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
          ((realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
              (riemannOp (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
                ((![(chartBasisVecFiber (I := I) α (σ 0) p.1 : E),
                    (chartBasisVecFiber (I := I) α (σ 1) p.1 : E)] : Fin 2 → E) 0)
                (chartBasisVecFiber (I := I) α m p.1) (chartBasisVecFiber (I := I) α k p.1))
              ((![(chartBasisVecFiber (I := I) α (σ 0) p.1 : E),
                    (chartBasisVecFiber (I := I) α (σ 1) p.1 : E)] : Fin 2 → E) 1) *
            Tensor0SSpace.toModel (Y p.1)
              ![(chartBasisVecFiber (I := I) α n p.1 : E),
                (chartBasisVecFiber (I := I) α l p.1 : E)])))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine (contMDiffOn_const (c := (2 : ℝ))).mul ?_
    refine contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α m n).mul ?_
    refine contMDiffOn_finset_sum (fun k _ => contMDiffOn_finset_sum (fun l _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α k l).mul ?_
    refine (corrField_riemannChartLoweredScalar_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
      α (σ 0) m k (σ 1)).mul ?_
    exact hYbasis n l
  refine hcomb.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hx
  rw [corrField_riemannBiContrFib_toModel_chartα (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α hxbase]

omit [CompactSpace M] in
private lemma corrField_riemannBiContrFibAppY_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s
    with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbaseT : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, riemannBiContrFib (I := I) (gfam p.2) p.1 (Y p.1)⟩).2 σ)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σ
    have hscal := corrField_riemannBiContrFibAppY_chartCoord_jointContMDiffOn
      (I := I) g₀ T T' hδ hδ' Y α σ
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1)⟩).2 σ =
          Tensor0SSpace.toModel (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1))
            ![(chartBasisVecFiber (I := I) α (σ 0) q.1 : E),
              (chartBasisVecFiber (I := I) α (σ 1) q.1 : E)] := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1,
          riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1 hqbase
        (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1))
        (fun j => (chartModelBasis E) (σ j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      change Tensor0SSpace.toModel (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1))
          (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σ j))) = _
      congr 1
      funext j
      fin_cases j <;> rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σ : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, riemannBiContrFib (I := I) (gfam p.2) p.1 (Y p.1)⟩).2 σ)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σ => hcoordEach σ)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1,
        riemannBiContrFib (I := I) (gfam p.2) p.1 (Y p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, riemannBiContrFib (I := I) (gfam p₀.2) p₀.1 (Y p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma corrField_raisedKoszulVec_realizedFam_chartα
    (g₀ : SmoothRiemannianMetric I M) (g₁ : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k : Fin (Module.finrank ℝ E)) :
    raisedKoszulVec (I := I) g₀ g₁ x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₀ α x p l *
            (∑ q : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) g₁ α k j q (extChartAt I α x) -
                chartChristoffel (I := I) g₀ α k j q (extChartAt I α x)) *
                chartGramMatrix (I := I) g₁ α x q l)) •
          chartBasisVecFiber (I := I) α p x := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  set W : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x
    (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x) with hW
  set cvx : TangentSpace I x →ₗ[ℝ] ℝ := (g₁.inner x W).toLinearMap with hcvx
  have hraisedeq : raisedKoszulVec (I := I) g₀ g₁ x
        (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₀ x cvx := by
    rw [raisedKoszulVec_apply, inverseMetricSharpFib_apply]
    refine congrArg
      (fun t => DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₀ x t) ?_
    ext w
    rw [cotangentToDualLinear_apply,
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM]
    rfl
  rw [hraisedeq]
  have hlocal := metricSharpChartLocal_eq_metricSharp (I := I) g₀ α (fun _ : M => cvx) hxbase
  rw [← hlocal]
  rw [metricSharpChartLocal]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  rw [metricSharpChartCoeff_def]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  congr 1
  show cvx (chartBasisVecFiber (I := I) α l x) = _
  rw [hcvx]
  change g₁.inner x W (chartBasisVecFiber (I := I) α l x) = _
  rw [hW, DifferentialGeometry.PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) g₁ g₀ α hx j k]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g_inner_eq_chartGramMatrix_basis (I := I) g₁ α x q l]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma corrField_raisedKoszulFibAppOm_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (om : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x⟯)
    (α : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => (om p.1) (fun _ : Fin 1 =>
        raisedKoszulVec (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (chartBasisVecFiber (I := I) α (σ 0) p.1)
          (chartBasisVecFiber (I := I) α (σ 1) p.1)))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ r : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₀ α p.1 r l *
            (∑ q : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α (σ 1) (σ 0) q
                  (extChartAt I α p.1) -
                chartChristoffel (I := I) g₀ α (σ 1) (σ 0) q (extChartAt I α p.1)) *
                chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 q l)) *
          (om p.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α r p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun r _ => ?_)
    refine ContMDiffOn.mul ?_ (omAppChartBasisVec_jointContMDiffOn (I := I) om α r)
    refine contMDiffOn_finset_sum (fun l _ => ?_)
    refine (corrField_chartInvGramMatrix_g0_jointContMDiffOn (I := I) g₀ α r l).mul ?_
    refine contMDiffOn_finset_sum (fun q _ => ?_)
    refine ContMDiffOn.mul ?_
      (corrField_realizedFam_chartGramMatrix_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α q l)
    refine ContMDiffOn.sub ?_ ?_
    · have hΓs := corrField_realizedFam_chartChristoffel_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
        α (σ 1) (σ 0) q
      exact hΓs.mono (fun z hz => ⟨hz.1, hz.2⟩)
    · exact corrField_chartChristoffel_g0_jointContMDiffOn (I := I) g₀ α (σ 1) (σ 0) q
  refine hcomb.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx
  rw [corrField_raisedKoszulVec_realizedFam_chartα (I := I) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α hxgood (σ 0) (σ 1)]
  set φ : TangentSpace I p.1 →L[ℝ] ℝ :=
    continuousMultilinearCurryFin1 ℝ (TangentSpace I p.1) ℝ (om p.1) with hφ
  have hφapply : ∀ v : TangentSpace I p.1, (om p.1) (fun _ : Fin 1 => v) = φ v := by
    intro v; rw [hφ, continuousMultilinearCurryFin1_apply]; rfl
  rw [hφapply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_smul, smul_eq_mul, hφapply, mul_comm]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma corrField_raisedKoszulFibAppOm_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (om : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1) (om p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s
    with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbaseT : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            raisedKoszulFib (I := I) g₀ (gfam p.2) p.1) (om p.1)⟩).2 σ)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σ
    have hscal := corrField_raisedKoszulFibAppOm_chartCoord_jointContMDiffOn
      (I := I) g₀ T T' hδ hδ' om α σ
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, (show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I q.1 from
          raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1)⟩).2 σ =
          (om q.1) (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ (gfam q.2) q.1
            (chartBasisVecFiber (I := I) α (σ 0) q.1)
            (chartBasisVecFiber (I := I) α (σ 1) q.1)) := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1, (show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I q.1 from
          raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) ((show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I q.1 from
            raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1 hqbase
        ((show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I q.1 from
          raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1))
        (fun j => (chartModelBasis E) (σ j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      rw [raisedKoszulFib_apply]
      rw [show (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σ j))) =
          (fun j => chartBasisVecFiber (I := I) α (σ j) q.1) from by
        funext j; rfl]
      rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σ : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I p.1 from
          raisedKoszulFib (I := I) g₀ (gfam p.2) p.1) (om p.1)⟩).2 σ)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σ => hcoordEach σ)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1, (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        raisedKoszulFib (I := I) g₀ (gfam p.2) p.1) (om p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, (show Tensor0SBundle.Tensor0SSpace 1 I p₀.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I p₀.1 from
          raisedKoszulFib (I := I) g₀ (gfam p₀.2) p₀.1) (om p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal

noncomputable def corrFieldChristoffelCoeff0Fib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  riemannBiContrFib (I := I) g₁ x

omit [CompactSpace M] [I.Boundaryless] in
theorem corrFieldChristoffelCoeff0Fib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (Tensor0SBundle.TensorRSSpace.ofCLM (corrFieldChristoffelCoeff0Fib (I := I) g₁ x))) :=
  riemannBiContrFib_contMDiff (I := I) g₁

noncomputable def corrFieldChristoffelCoeff0 (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          Tensor0SBundle.TensorRSSpace.ofCLM (corrFieldChristoffelCoeff0Fib (I := I) g₁ x))
      contMDiff_toFun := corrFieldChristoffelCoeff0Fib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] theorem corrFieldChristoffelCoeff0_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (corrFieldChristoffelCoeff0 (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        Tensor0SBundle.TensorRSSpace.ofCLM (corrFieldChristoffelCoeff0Fib (I := I) g₁ x)) :=
  rfl

theorem corrFieldChristoffelCoeff0_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((corrFieldChristoffelCoeff0 (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      corrFieldChristoffelCoeff0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => corrField_riemannBiContrFibAppY_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [corrFieldChristoffelCoeff0_toSection]
  rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem corrField_raisedKoszulFib_realizedFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1
        ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
          raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro om
  exact corrField_raisedKoszulFibAppOm_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' om

noncomputable def corrFieldChristoffelCoeff1Fib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      raisedKoszulFib (I := I) g₀ g₁ x).comp
    (cometricDoubleTraceFib (I := I) g₁ 1 x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem corrFieldChristoffelCoeff1Fib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) :
    corrFieldChristoffelCoeff1Fib (I := I) g₀ g₁ x D =
      (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          raisedKoszulFib (I := I) g₀ g₁ x)
        (cometricDoubleTraceFib (I := I) g₁ 1 x D) := by
  rw [corrFieldChristoffelCoeff1Fib, ContinuousLinearMap.comp_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem corrFieldChristoffelCoeff1Fib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (corrFieldChristoffelCoeff1Fib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => corrFieldChristoffelCoeff1Fib (I := I) g₀ g₁ x)
  intro Y
  have hdt : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) Y.contMDiff
  have hkos : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            raisedKoszulFib (I := I) g₀ g₁ x)
          (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (raisedKoszulFib_contMDiff (I := I) g₀ g₁) hdt
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [corrFieldChristoffelCoeff1Fib, ContinuousLinearMap.comp_apply]

noncomputable def corrFieldChristoffelCoeff1 (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from corrFieldChristoffelCoeff1Fib (I := I) g₀ g₁ x)
      contMDiff_toFun := corrFieldChristoffelCoeff1Fib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem corrFieldChristoffelCoeff1_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (corrFieldChristoffelCoeff1 (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        corrFieldChristoffelCoeff1Fib (I := I) g₀ g₁ x) :=
  rfl

theorem corrFieldChristoffelCoeff1_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        ((corrFieldChristoffelCoeff1 (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 3 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        corrFieldChristoffelCoeff1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => by
      have hZ := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 1) g₀ T T' hδ hδ'
        (fun q : M × ℝ => Y q.1) (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst)
      have hkos := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
        (corrField_raisedKoszulFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hZ
      refine hkos.congr (fun q _ => ?_)
      refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) q.1 t) ?_
      rw [corrFieldChristoffelCoeff1Fib_apply])
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 t) ?_
  rw [corrFieldChristoffelCoeff1_toSection]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
