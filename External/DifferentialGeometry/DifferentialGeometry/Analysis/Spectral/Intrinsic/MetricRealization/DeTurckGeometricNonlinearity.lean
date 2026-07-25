import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def isRealizableMetricPerturbationAt (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) : Prop :=
  ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
    metricCauchySchwarzBound (I := I) (M := M) g_bg
      (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ'

open scoped Classical in

def realizeMetricAt (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) :
    SmoothRiemannianMetric I M :=
  if h : isRealizableMetricPerturbationAt (I := I) g_bg u then
    tensorSectionRealizeMetric (I := I) g_bg
      (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
        (I := I) (M := M) u h.choose)
      h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  else
    g_bg


omit [BoundarylessManifold I M] in
theorem realizeMetricAt_inner_of_realizable (g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg
      (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ')
    (x : M) (v w : TangentSpace I x) :
    (realizeMetricAt (I := I) g_bg u).inner x v w =
      g_bg.inner x v w + tensorHsBilinFormSymm (I := I) g_bg u hu_fs x v w := by
  classical
  have hex : isRealizableMetricPerturbationAt (I := I) g_bg u := ⟨hu_fs, δ', hδ'_lt, hδ'⟩
  rw [realizeMetricAt, dif_pos hex, tensorSectionRealizeMetric_inner]
  rfl


omit [BoundarylessManifold I M] in
theorem realizeMetricAt_of_not_realizable (g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu : ¬ isRealizableMetricPerturbationAt (I := I) g_bg u) :
    realizeMetricAt (I := I) g_bg u = g_bg := by
  classical
  rw [realizeMetricAt, dif_neg hu]

open scoped Classical in

def deTurckRemainderSection (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) :
    SmoothCcTensor g_bg 0 2 :=
  if h : isRealizableMetricPerturbationAt (I := I) g_bg u then
    { toSection :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g_bg u)).toSection
      hasCompactSupport :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g_bg u)).hasCompactSupport }
      - rawTensorConnLapSmooth (I := I) g_bg 0 2
          (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
            (I := I) (M := M) u h.choose)
  else
    0

private def hCompact (g_bg : SmoothRiemannianMetric I M) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g_bg 0 2) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2

def deTurckGeometricN (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1)) :
    tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) g_bg)
      (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g_bg
      (a : ℝ) (deTurckRemainderSection (I := I) g_bg u) (hCompact (I := I) g_bg)

@[simp] theorem deTurckGeometricN_coeff (g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g_bg 0 2) :
    (deTurckGeometricN (I := I) g_bg a u).coeff i =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) g_bg)
        (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)) i :=
  rfl

theorem deTurckGeometricN_of_not_realizable (g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (hu : ¬ isRealizableMetricPerturbationAt (I := I) g_bg u) :
    deTurckGeometricN (I := I) g_bg a u = 0 := by
  classical
  have hsec : deTurckRemainderSection (I := I) g_bg u = 0 := by
    rw [deTurckRemainderSection, dif_neg hu]
  apply tensorHs.ext (I := I) (M := M)
  funext i
  rw [deTurckGeometricN_coeff, hsec,
    show SmoothCcTensor.toL2 (g := g_bg) (r := 0) (s := 2)
        (0 : SmoothCcTensor g_bg 0 2) = 0 from map_zero _,
    tensorL2Coeff_eq_inner, inner_zero_right]
  rfl

section JointSmoothness

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear Tensor0SBundle


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartFrameVec_eq_chartBasisVecFiber_helper (α : M)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)
      = chartBasisVecFiber (I := I) α i x := by
  rw [chartBasisVecFiber, Trivialization.symmL_apply]


omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem realizedFam_chartDeTurckRicciRHS_jointContMDiffOn
    (g_bg g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α i k (extChartAt I α p.1))
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
  have hentry := gen_joint_chartDeTurckRicciRHS (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG g_bg i k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg α i k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

set_option maxHeartbeats 3200000 in

omit [CompactSpace M] in
theorem deTurckRHSField_realizeMetric_jointContMDiffOn
    (g_bg g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨_, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hinter]
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set α : M := p₀.1 with hα
  set Bb := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBb
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  have hcoord : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => Bb.repr
          (e ⟨p.1, deTurckRHSField (I := I) g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2 σ)
        ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ := by
    intro σ
    have hP1 := realizedFam_chartDeTurckRicciRHS_jointContMDiffOn (I := I) g_bg g₀ T T' hδ hδ'
      α (σ 0) (σ 1)
    have hp₀_in_α : p₀ ∈ (chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') := by
      refine ⟨?_, hp₀.2⟩
      rw [hα]; exact mem_chart_source H p₀.1
    have hP1at : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => chartDeTurckRicciRHS (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α (σ 0) (σ 1) (extChartAt I α p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ := hP1 p₀ hp₀_in_α
    have hαsrc_nhd : ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∈
        nhdsWithin p₀ ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
      have h := inter_mem_nhdsWithin
        ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))
        (((chartAt H α).open_source.prod realizedSmallSet_isOpen).mem_nhds hp₀_in_α)
      refine Filter.mem_of_superset h ?_
      intro q hq; exact hq.2
    refine (hP1at.mono_of_mem_nhdsWithin hαsrc_nhd).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hαsrc_nhd] with p hp
      obtain ⟨hpx, hps⟩ := hp
      have hpgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
        rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
        exact hpx
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ p.1
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      rw [chartFrameVec_eq_chartBasisVecFiber_helper,
        chartFrameVec_eq_chartBasisVecFiber_helper]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α (σ 0) (σ 1) hpgood]
    · have hpgood : p₀.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
        rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
        rw [hα]; exact mem_chart_source H p₀.1
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) p₀.1)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ p₀.1
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      rw [chartFrameVec_eq_chartBasisVecFiber_helper,
        chartFrameVec_eq_chartBasisVecFiber_helper]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) g_bg α (σ 0) (σ 1) hpgood]
  have hpi : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => (Bb.repr
        (e ⟨p.1, deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2 :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ))
      ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ :=
    contMDiffWithinAt_pi_space.2 (fun σ => hcoord σ)
  have hsymm : ContMDiff 𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ)
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun c : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ => Bb.equivFun.symm c) :=
    (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  refine (hsymm.contMDiffAt.comp_contMDiffWithinAt p₀ hpi).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p _
    simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨p.1, deTurckRHSField (I := I) g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨p.1, deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm
  · simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨p₀.1, deTurckRHSField (I := I) g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) p₀.1⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨p₀.1, deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) p₀.1⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem smoothCcChartRepr_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (F p.2).toSection z) p.1)
      (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) := by
  have hrepr :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
        (fun p : M × ℝ =>
          ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
            ⟨p.1, (F p.2).toSection p.1⟩).2)
        (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) := by
    intro p hp
    obtain ⟨hx, hs⟩ := hp
    have hsub : (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) ⊆
        ((Set.univ : Set M) ×ˢ S) := by
      intro q hq; exact ⟨Set.mem_univ _, hq.2⟩
    have hFwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
          TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
        (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) p :=
      (hF p (hsub ⟨hx, hs⟩)).mono hsub
    have hsource : (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
      rw [Bundle.Trivialization.mem_source]
      exact hx
    exact ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
      (s := ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S)
      (x₀ := p)
      (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mp hFwithin).2
  refine hrepr.congr ?_
  intro p hp
  obtain ⟨hx, _hs⟩ := hp
  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
  change (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).linearMapAt ℝ p.1
      ((F p.2).toSection p.1) = _
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hx]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem smoothCcChartRepr_euclid_jointContDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {y₀ : E} (ht₀ : t₀ ∈ S)
    (hy₀ : y₀ ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, y₀) := by
  classical
  have hbase := smoothCcChartRepr_jointContMDiffOn (I := I) g₀ F S α hF
  have hbaseSet_eq :
      (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  rw [hbaseSet_eq] at hbase
  set φ := extChartAt I α with hφ
  have hx0src : φ.symm y₀ ∈ (chartAt H α).source := by
    have := φ.map_target hy₀
    rwa [extChartAt_source] at this
  have htgt_open : IsOpen φ.target := isOpen_extChartAt_target (I := I) α
  have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hmove : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) (t₀, y₀) := by
    refine ContMDiffWithinAt.prodMk ?_ ?_
    · have hsymm_w : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm φ.target y₀ := hsymm_on y₀ hy₀
      exact hsymm_w.comp (t₀, y₀) contMDiffWithinAt_snd (fun q hq => hq.2)
    · exact contMDiffWithinAt_fst
  have hbase_w : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (F p.2).toSection z) p.1)
      ((chartAt H α).source ×ˢ S) ((φ.symm y₀ : M), t₀) :=
    hbase ((φ.symm y₀ : M), t₀) ⟨hx0src, ht₀⟩
  have hmaps : Set.MapsTo (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) ((chartAt H α).source ×ˢ S) := by
    intro q hq
    obtain ⟨hqS, hqtgt⟩ := hq
    refine ⟨?_, hqS⟩
    have := φ.map_target hqtgt
    rwa [extChartAt_source] at this
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) :=
    hbase_w.comp (t₀, y₀) hmove hmaps
  have hself : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
    exact hcomp
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hself
  exact hself

set_option maxHeartbeats 1600000 in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem smoothCcCovApplyChartRepr_euclid_jointContDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {b : M} (ht₀ : t₀ ∈ S)
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, extChartAt I α b) := by
  classical
  set φ := extChartAt I α with hφ
  set chartRep : ℝ → E → Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    fun t y => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
      (fun z : M => (F t).toSection z) (φ.symm y) with hchartRep
  set U : Set E := φ '' chartLeviCivitaGoodSet (I := I) α with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : φ b ∈ U := ⟨b, hb_good, rfl⟩
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
  have hyb_tgt : φ b ∈ φ.target :=
    φ.map_source (by rw [hφ, extChartAt_source]; exact hb_src)
  have hchartRep_w : ∀ y₀ : E, y₀ ∈ φ.target →
      ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2) (S ×ˢ φ.target) (t₀, y₀) := by
    intro y₀ hy₀
    exact smoothCcChartRepr_euclid_jointContDiffWithinAt (I := I) g₀ F S α hF ht₀ hy₀
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := B.contMDiff.contMDiffOn
  have hvec_cd : ContDiffOn ℝ ∞
      (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun ∘ φ.symm) U :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  have hvec_at : ContDiffAt ℝ ∞
      (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun ∘ φ.symm)
      (φ b) :=
    (hvec_cd (φ b) hx_mem).contDiffAt (hU_open.mem_nhds hx_mem)
  have hvec_q : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.chartE_section_repr
        (I := I) α B.toFun (φ.symm q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
    (hvec_at.comp (t₀, φ b) contDiffAt_snd).contDiffWithinAt
  have h_intrinsic : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
        (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun (φ.symm q.2)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    have huncurry : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (q : ℝ × E) (y' : E) => chartRep q.1 y'))
        ((S ×ˢ φ.target) ×ˢ φ.target)
        ((t₀, φ b), (fun q : ℝ × E => q.2) (t₀, φ b)) := by
      have hbrick : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => chartRep r.1 r.2)
          (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_tgt
      have hproj : ContDiffWithinAt ℝ ∞
          (fun r : (ℝ × E) × E => (r.1.1, r.2))
          ((S ×ˢ φ.target) ×ˢ φ.target) ((t₀, φ b), φ b) :=
        (contDiffWithinAt_fst.fst).prodMk contDiffWithinAt_snd
      refine hbrick.comp ((t₀, φ b), φ b) hproj ?_
      rintro ⟨⟨t, y⟩, y'⟩ ⟨⟨ht, _⟩, hy'⟩
      exact ⟨ht, hy'⟩
    have hg : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      contDiffWithinAt_snd
    have htgt_open : IsOpen φ.target := isOpen_extChartAt_target (I := I) α
    have hud : UniqueDiffOn ℝ φ.target := htgt_open.uniqueDiffOn
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    have hsub : (S ×ˢ φ.target) ⊆ (fun q : ℝ × E => q.2) ⁻¹' φ.target := by
      intro q hq; exact hq.2
    have hfdw := ContDiffWithinAt.fderivWithin huncurry hg hud h_le ⟨ht₀, hyb_tgt⟩ hsub
    have hfd_eq : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2) (S ×ˢ φ.target) (t₀, φ b) := by
      refine hfdw.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact (fderivWithin_of_isOpen htgt_open hq.2).symm
      · exact (fderivWithin_of_isOpen htgt_open hyb_tgt).symm
    exact hfd_eq.clm_apply hvec_q
  have hchartRep_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2)
      (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_tgt
  have h_output : ∀ l : Fin 2, ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y' : M => Tensor0SBundle.TensorRSSpace 0 2 I y') α).continuousLinearMapAt ℝ
          (φ.symm q.2)
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) 0 2 g₀ α
            (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l))
      (S ×ˢ φ.target) (t₀, φ b) := by
    intro l
    obtain ⟨Ker, hKer, hK_at⟩ :
        ∃ Ker : E → (Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ]
            Tensor0SBundle.TensorRSModel 0 2 ℝ E),
          (Ker = fun y : E => DifferentialGeometry.Integral.Connection.outputSlotChartKernel
            (I := I) g₀ 0 2 α B.toFun l (φ.symm y)) ∧
          ContDiffAt ℝ ∞ Ker (φ b) :=
      ⟨_, rfl, outputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g₀ 0 2 α B l hb_good⟩
    have hK_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => Ker q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      (ContDiffAt.comp (t₀, φ b) hK_at contDiffAt_snd).contDiffWithinAt
    have h_apply : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Ker q.2 (chartRep q.1 q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
      hK_q.clm_apply hchartRep_q
    refine h_apply.congr_of_eventuallyEq ?_ ?_
    · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
        (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
      refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
      rintro ⟨t, y⟩ hq
      have hy : y ∈ U := hq.2
      obtain ⟨x', hx'_good, hx'y⟩ := hy
      have hx'_src : x' ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
      have hx'_extsrc : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx'_src
      have hx'_inv : φ.symm y = x' := by rw [← hx'y]; exact φ.left_inv hx'_extsrc
      change _ = Ker y (chartRep t y)
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ 0 2 α
        (fun b' : M => (F t).toSection b') B.toFun
        (b := φ.symm y) (by rw [hx'_inv]; exact hx'_src) l)
    · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
      change _ = Ker (φ b) (chartRep t₀ (φ b))
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ 0 2 α
        (fun b' : M => (F t₀).toSection b') B.toFun
        (b := φ.symm (φ b)) (by rw [hgood_inv]; exact hb_src) l)
  have h_sum : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
          (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun (φ.symm q.2))
        + (∑ k : Fin 0,
            (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
                (fun y' : M => Tensor0SBundle.TensorRSSpace 0 2 I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) 0 2 g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) k))
        - (∑ l : Fin 2,
            (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
                (fun y' : M => Tensor0SBundle.TensorRSSpace 0 2 I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) 0 2 g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    refine (h_intrinsic.add (ContDiffWithinAt.sum (fun k _ => Fin.elim0 k))).sub
      (ContDiffWithinAt.sum (fun l _ => h_output l))
  refine h_sum.congr_of_eventuallyEq ?_ ?_
  · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
      (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
    refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
    rintro ⟨t, y⟩ hq
    have hy : y ∈ U := hq.2
    obtain ⟨x', hx'_good, hx'y⟩ := hy
    have hx'_extsrc : x' ∈ φ.source := by
      rw [hφ, extChartAt_source]; exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hy_tgt : y ∈ φ.target := hx'y ▸ φ.map_source hx'_extsrc
    have hy_good : φ.symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [← hx'y, φ.left_inv hx'_extsrc]; exact hx'_good
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ 0 2 α (F t) B hy_tgt hy_good
    change DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t).toSection z)) (φ.symm y) = _
    rw [hchartRep]
    exact hform
  · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ 0 2 α (F t₀) B hyb_tgt (by rw [hgood_inv]; exact hb_good)
    change DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t₀).toSection z)) (φ.symm (φ b)) = _
    rw [hchartRep]
    exact hform

set_option maxHeartbeats 1600000 in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem smoothCcCovApplyChartRepr_manifold_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  set φ := extChartAt I α with hφ
  intro p hp
  obtain ⟨hpx, hps⟩ := hp
  have hpx_good : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]; exact hpx
  have hEu := smoothCcCovApplyChartRepr_euclid_jointContDiffWithinAt (I := I) g₀ F S α B hF hps hpx_good
  have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hmoveOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun q : M × ℝ => (q.2, φ q.1))
        ((chartAt H α).source ×ˢ S) := by
      refine ContMDiffOn.prodMk contMDiffOn_snd ?_
      exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun q hq => hq.1)
    have hm := hmoveOn p ⟨hpx, hps⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  have hEuM : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) (φ.symm q.2))
      (S ×ˢ φ.target) (p.2, φ p.1) := by
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact hEu
  have hmaps : Set.MapsTo (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) (S ×ˢ φ.target) := by
    intro q hq
    obtain ⟨hqx, hqs⟩ := hq
    refine ⟨hqs, ?_⟩
    exact φ.map_source (by rw [hφ, extChartAt_source]; exact hqx)
  have hcomp := hEuM.comp p hmove hmaps
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨hqx, _⟩ := hq
    have hqsrc : q.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hqx
    simp only [Function.comp_apply]
    rw [φ.left_inv hqsrc]
  · simp only [Function.comp_apply]
    have hpsrc : p.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hpx
    rw [φ.left_inv hpsrc]

set_option maxHeartbeats 1600000 in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem smoothCcCovApplySection_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F p.2).toSection z) p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ S) ∩ ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ S := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hCR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) :=
    smoothCcCovApplyChartRepr_manifold_jointContMDiffOn (I := I) g₀ F S α B hF
  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        rw [hα]; exact hx₀src
  have hsource : (⟨p₀.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p₀.2).toSection z) p₀.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
      (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
          ⟨p.1,
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
              B.toFun (fun z : M => (F p.2).toSection z) p.1⟩).2)
      ((chartAt H α).source ×ˢ S) p₀ := by
    refine (hCR p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hpx, _⟩ := hp
      have hpbase : p.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
        change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
            ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
        refine ⟨?_, ?_⟩ <;>
          · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
            rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
              TangentBundle.trivializationAt_baseSet (I := I) α]
            exact hpx
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    · rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet]
  refine ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p.2).toSection z) p.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
    (s := (chartAt H α).source ×ˢ S) (x₀ := p₀)
    (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem genChartRepr_jointContMDiffOn
    (S : Set ℝ) (α : M)
    (Tfam : ℝ → Cₛ^∞⟮I; Tensor0SBundle.TensorRSModel 0 2 ℝ E,
      fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z⟯)
    (hT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (Tfam p.2 p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => Tfam p.2 z) p.1)
      (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) := by
  have hrepr :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
        (fun p : M × ℝ =>
          ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
            ⟨p.1, Tfam p.2 p.1⟩).2)
        (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) := by
    intro p hp
    obtain ⟨hx, hs⟩ := hp
    have hsub : (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) ⊆
        ((Set.univ : Set M) ×ˢ S) := by
      intro q hq; exact ⟨Set.mem_univ _, hq.2⟩
    have hTwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, Tfam p.2 p.1⟩ :
          TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
        (((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S) p :=
      (hT p (hsub ⟨hx, hs⟩)).mono hsub
    have hsource : (⟨p.1, Tfam p.2 p.1⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
      rw [Bundle.Trivialization.mem_source]; exact hx
    exact ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, Tfam p.2 p.1⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
      (s := ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet) ×ˢ S)
      (x₀ := p)
      (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mp hTwithin).2
  refine hrepr.congr ?_
  intro p hp
  obtain ⟨hx, _hs⟩ := hp
  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
    Bundle.Trivialization.continuousLinearMapAt_apply,
    Bundle.Trivialization.coe_linearMapAt_of_mem _ hx]

private def toSmoothCcTensor
    (g₀ : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; Tensor0SBundle.TensorRSModel 0 2 ℝ E,
      fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z⟯) :
    SmoothCcTensor g₀ 0 2 where
  toSection := σ
  hasCompactSupport :=
    IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma toSmoothCcTensor_toSection
    (g₀ : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; Tensor0SBundle.TensorRSModel 0 2 ℝ E,
      fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z⟯) :
    (toSmoothCcTensor (I := I) g₀ σ).toSection = σ := rfl

set_option maxHeartbeats 1600000 in

omit [NeZero (Module.finrank ℝ E)] in
private theorem covApplyGenFamily_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (S : Set ℝ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Tfam : ℝ → Cₛ^∞⟮I; Tensor0SBundle.TensorRSModel 0 2 ℝ E,
      fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z⟯)
    (hT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (Tfam p.2 p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => Tfam p.2 z) p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  exact smoothCcCovApplySection_jointContMDiffOn (I := I) g₀
    (fun t => toSmoothCcTensor (I := I) g₀ (Tfam t)) S B hT

private def covApplySection
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : SmoothCcTensor g₀ 0 2) :
    Cₛ^∞⟮I; Tensor0SBundle.TensorRSModel 0 2 ℝ E,
      fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z⟯ where
  toFun := fun y : M =>
    covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
      B.toFun (fun z : M => T.toSection z) y
  contMDiff_toFun :=
    covApplyRS_contMDiff (I := I) g₀ 0 2 T.toSection.contMDiff_toFun B.contMDiff

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma covApplySection_apply
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : SmoothCcTensor g₀ 0 2) (y : M) :
    covApplySection (I := I) g₀ B T y =
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => T.toSection z) y := rfl

private def christoffelSelfField
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun := fun y : M =>
    covApply (LeviCivita (I := I) g₀) B.toFun B.toFun y
  contMDiff_toFun := by
    have hBplus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% B.toFun) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact B.contMDiff
    have hOn := covApply_contMDiffOn (cov := LeviCivita (I := I) g₀) B.contMDiff hBplus
    intro b
    exact hOn.contMDiffAt (Filter.univ_mem)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] private lemma christoffelSelfField_apply
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    christoffelSelfField (I := I) g₀ B y =
      covApply (LeviCivita (I := I) g₀) B.toFun B.toFun y := rfl

set_option maxHeartbeats 1600000 in

omit [NeZero (Module.finrank ℝ E)] in
private theorem traceTerm1_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1 (B.toFun p.1)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hInner := smoothCcCovApplySection_jointContMDiffOn (I := I) g₀ F S B hF
  have hStep := covApplyGenFamily_jointContMDiffOn (I := I) g₀ S B
    (fun t => covApplySection (I := I) g₀ B (F t)) hInner
  exact hStep

set_option maxHeartbeats 1600000 in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem traceTerm2_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀)).toFun
          (fun z : M => (F p.2).toSection z) p.1
          ((LeviCivita (I := I) g₀).toFun B.toFun p.1 (B.toFun p.1))))
      ((Set.univ : Set M) ×ˢ S) := by
  have hStep := smoothCcCovApplySection_jointContMDiffOn (I := I) g₀ F S
    (christoffelSelfField (I := I) g₀ B) hF
  exact hStep

private def iteratedCovApplySection
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : SmoothCcTensor g₀ 0 2) :
    Cₛ^∞⟮I; Tensor0SBundle.TensorRSModel 0 2 ℝ E,
      fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z⟯ where
  toFun := fun y : M =>
    (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀)).toFun
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => T.toSection z)) y (B.toFun y)
  contMDiff_toFun :=
    covApply_covApply_section_contMDiff (I := I) g₀ 0 2 T.toSection.contMDiff_toFun B.contMDiff

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma iteratedCovApplySection_apply
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : SmoothCcTensor g₀ 0 2) (y : M) :
    iteratedCovApplySection (I := I) g₀ B T y =
      (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => T.toSection z)) y (B.toFun y) := rfl

private def covApplyChristoffelSection
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : SmoothCcTensor g₀ 0 2) :
    Cₛ^∞⟮I; Tensor0SBundle.TensorRSModel 0 2 ℝ E,
      fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z⟯ where
  toFun := fun y : M =>
    (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀)).toFun
      (fun z : M => T.toSection z) y
      ((LeviCivita (I := I) g₀).toFun B.toFun y (B.toFun y))
  contMDiff_toFun :=
    covApply_christoffel_section_contMDiff (I := I) g₀ 0 2 T.toSection.contMDiff_toFun B.contMDiff

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma covApplyChristoffelSection_apply
    (g₀ : SmoothRiemannianMetric I M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : SmoothCcTensor g₀ 0 2) (y : M) :
    covApplyChristoffelSection (I := I) g₀ B T y =
      (TensorRSNabla.tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g₀)).toFun
        (fun z : M => T.toSection z) y
        ((LeviCivita (I := I) g₀).toFun B.toFun y (B.toFun y)) := rfl

set_option maxHeartbeats 3200000 in

private theorem fixedFrameTrace_chartRepr_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α
        (fun z : M => rawTensorConnLap_fixedFrame (I := I) g₀ 0 2
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g₀ α i).toFun)
          (fun y : M => (F p.2).toSection y) z) p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  set Bf : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    fun i => chartFrameNormGlobalSmooth (I := I) (M := M) g₀ α i with hBf
  set baseSet := (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
    (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet with hbaseSet
  have hbaseSet_eq : baseSet = (chartAt H α).source := by
    rw [hbaseSet]
    change ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]; rfl

  have hterm1 : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
        (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => iteratedCovApplySection (I := I) g₀ (Bf i) (F p.2) z) p.1)
        (baseSet ×ˢ S) := by
    intro i
    refine genChartRepr_jointContMDiffOn (I := I) S α
      (fun t => iteratedCovApplySection (I := I) g₀ (Bf i) (F t)) ?_
    have := traceTerm1_jointContMDiffOn (I := I) g₀ F S (Bf i) hF
    exact this
  have hterm2 : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
        (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => covApplyChristoffelSection (I := I) g₀ (Bf i) (F p.2) z) p.1)
        (baseSet ×ˢ S) := by
    intro i
    refine genChartRepr_jointContMDiffOn (I := I) S α
      (fun t => covApplyChristoffelSection (I := I) g₀ (Bf i) (F t)) ?_
    have := traceTerm2_jointContMDiffOn (I := I) g₀ F S (Bf i) hF
    exact this

  have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ => ∑ i : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) 0 2 α (fun z : M => iteratedCovApplySection (I := I) g₀ (Bf i) (F p.2) z) p.1 -
          DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) 0 2 α (fun z : M => covApplyChristoffelSection (I := I) g₀ (Bf i) (F p.2) z) p.1))
      (baseSet ×ˢ S) := by
    intro p hp
    exact ContMDiffWithinAt.sum (fun i _ => (hterm1 i p hp).sub (hterm2 i p hp))

  rw [hbaseSet_eq] at hsum
  refine hsum.congr ?_
  intro p _hp

  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
    rawTensorConnLap_fixedFrame_def, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
    DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
    ← map_sub, iteratedCovApplySection_apply, covApplyChristoffelSection_apply]

set_option maxHeartbeats 3200000 in

theorem rawTensorConnLapSmooth_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (S : Set ℝ)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((rawTensorConnLapSmooth (I := I) g₀ 0 2 (F p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩

  obtain ⟨α, hα_pos⟩ := (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x₀)
  set pou : M → ℝ := fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hpou
  have hpou_cont : Continuous pou := (chartAtlasPOU I M α).contMDiff.continuous

  set U : Set M := {x : M | 0 < pou x} with hU
  have hU_open : IsOpen U := isOpen_lt continuous_const hpou_cont
  have hx₀U : x₀ ∈ U := hα_pos
  have hU_sub_tsupp : U ⊆ tsupport pou := fun x hx => subset_tsupport pou (by
    simp only [Function.mem_support]; exact ne_of_gt hx)
  have htsupp_sub_src : tsupport pou ⊆ (chartAt H α).source := by
    have := (chartAtlasPOU_isSubordinate I M) α
    simpa only [hpou] using this
  have hU_sub_good : U ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro x hx
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]
    exact htsupp_sub_src (hU_sub_tsupp hx)
  refine ⟨U ×ˢ (Set.univ : Set ℝ), hU_open.prod isOpen_univ, ⟨hx₀U, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ S) ∩ (U ×ˢ (Set.univ : Set ℝ)) = U ×ˢ S := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hinter]

  have hCR0 := fixedFrameTrace_chartRepr_jointContMDiffOn (I := I) g₀ F S α hF
  have hU_sub_src : U ⊆ (chartAt H α).source := fun x hx => htsupp_sub_src (hU_sub_tsupp hx)
  have hCR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α
        (fun z : M => rawTensorConnLap_fixedFrame (I := I) g₀ 0 2
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g₀ α i).toFun)
          (fun y : M => (F p.2).toSection y) z) p.1)
      (U ×ˢ S) :=
    hCR0.mono (fun q hq => ⟨hU_sub_src hq.1, hq.2⟩)

  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        exact hU_sub_src hx₀src
  have hsource : (⟨p₀.1,
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F p₀.2)).toSection p₀.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
      (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet

  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
          ⟨p.1, (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F p.2)).toSection p.1⟩).2)
      (U ×ˢ S) p₀ := by
    refine (hCR p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hpx, _⟩ := hp
      have hpgood : p.1 ∈ tsupport pou ∩ chartLeviCivitaGoodSet (I := I) α :=
        ⟨hU_sub_tsupp hpx, hU_sub_good hpx⟩
      have hpbase : p.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
        change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
            ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
        refine ⟨?_, ?_⟩ <;>
          · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
            rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
              TangentBundle.trivializationAt_baseSet (I := I) α]
            exact hU_sub_src hpx
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase,
        rawTensorConnLapSmooth_toSection_apply,
        rawTensorConnLap_via_chartFrameNormGlobalSmooth (I := I) g₀ 0 2 (F p.2) α hpgood]
    · have hp₀good : p₀.1 ∈ tsupport pou ∩ chartLeviCivitaGoodSet (I := I) α :=
        ⟨hU_sub_tsupp hx₀src, hU_sub_good hx₀src⟩
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet,
        rawTensorConnLapSmooth_toSection_apply,
        rawTensorConnLap_via_chartFrameNormGlobalSmooth (I := I) g₀ 0 2 (F p₀.2) α hp₀good]
  refine ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1,
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F p.2)).toSection p.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
    (s := U ×ˢ S) (x₀ := p₀)
    (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

end JointSmoothness

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
