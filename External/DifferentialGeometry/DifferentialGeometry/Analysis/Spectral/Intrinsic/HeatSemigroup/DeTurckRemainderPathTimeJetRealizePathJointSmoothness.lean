import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.ParametricFiberInnerSmooth
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def deTurckRHSReconSection (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport }

section RealizePathJointSmoothness

open Tensor0SBundle TensorMultilinear
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

private instance tensor0SModelNormedAddCommGroup_local {nn : ℕ} :
    NormedAddCommGroup (Tensor0SBundle.Tensor0SModel nn ℝ E) := inferInstance

private instance tensor0SModelNormedSpace_local {nn : ℕ} :
    NormedSpace ℝ (Tensor0SBundle.Tensor0SModel nn ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace nn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem contMDiffWithinAt_curriedSection_prod_full {n : ℕ}
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (n + 1) I p.1)
    (hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace (n + 1) I x) p.1 (T p)) s p₀) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p.1
        (tensor0S_curry (I := I) (M := M) n p.1 (T p))) s p₀ := by
  letI : TopologicalSpace (TotalSpace (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  rw [Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hT_at := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E) (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbase : {p : M × ℝ | p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).baseSet} ∈ nhdsWithin p₀ s := by
      apply nhdsWithin_le_nhds
      apply (continuous_fst.continuousAt).preimage_mem_nhds
      exact (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt _ _ _)
    filter_upwards [hbase] with p hb
    have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p) p₀.1 p.1 hb
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p.1, tensor0S_curry (I := I) (M := M) n p.1 (T p)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p.1, T p⟩).2)
    exact hpt
  · have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p₀) p₀.1 p₀.1 (mem_baseSet_trivializationAt _ _ _)
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p₀.1, tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p₀.1, T p₀⟩).2)
    exact hpt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem contMDiffWithinAt_section_apply_prod_full : ∀ (n : ℕ)
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace n I p.1)
    (_hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1 (T p)) s p₀)
    (v : Fin n → ∀ p : M × ℝ, TangentSpace I p.1)
    (_hv : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p)) s p₀),
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (T p) (fun i => v i p)) s p₀
  | 0, s, p₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffWithinAt_totalSpace
      (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y)
      (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : M × ℝ =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) p₀.1 ⟨p.1, T p⟩).2)) s p₀ :=
      hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p) p₀.1 p.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p) 0)) = (T p) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p) 0)) 0 = (T p) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
    · rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p₀) p₀.1 p₀.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p₀) 0)) = (T p₀) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p₀) 0)) 0 = (T p₀) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p₀) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
  | n + 1, s, p₀, T, hT, v, hv => by
    have hCurry := contMDiffWithinAt_curriedSection_prod_full (I := I) (M := M) T hT
    have hApplied : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
        (fun p : M × ℝ =>
          TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1
            ((tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))) s p₀ :=
      ContMDiffWithinAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace n I x)
        (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
        (b := Prod.fst) (ϕ := fun p : M × ℝ => tensor0S_curry (I := I) (M := M) n p.1 (T p))
        (v := fun p : M × ℝ => v 0 p)
        hCurry (hv 0)
    have hRec := contMDiffWithinAt_section_apply_prod_full n
      (s := s) (p₀ := p₀)
      (fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))
      hApplied
      (fun (i : Fin n) (p : M × ℝ) => v i.succ p)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]
    · change Tensor0SBundle.Tensor0SSpace.toModel (T p₀) (fun i : Fin (n + 1) => v i p₀) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)) (v 0 p₀))
          (fun i : Fin n => v i.succ p₀)
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]

omit [CompactSpace M] in
theorem deTurckRHSField_realizePath_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ}
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (hJ : DifferentialGeometry.PDE.RicciFlow.JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) q.2
        (deTurckRHSField (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ (F q.1) hδ_lt (hδ q.1)) q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgfam
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨s₀, x₀⟩ ⟨hs₀, _⟩
  refine ⟨(Set.univ : Set ℝ) ×ˢ (chartAt H x₀).source,
    isOpen_univ.prod (chartAt H x₀).open_source,
    ⟨Set.mem_univ _, mem_chart_source H x₀⟩, ?_⟩
  have hinter : (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) ∩
      ((Set.univ : Set ℝ) ×ˢ (chartAt H x₀).source) =
      Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.univ_inter]
  rw [hinter]
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  set α : M := p₀.2 with hα
  set Bb := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBb
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  have hgood : Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α ∈
      nhdsWithin p₀ (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source) := by
    have hp₀_good : p₀ ∈ Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α := by
      refine ⟨hp₀.1, ?_⟩
      exact self_mem_chartLeviCivitaGoodSet (I := I) α
    have h := inter_mem_nhdsWithin
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source)
      ((isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α)).mem_nhds
        (⟨Set.mem_univ _, by
            exact self_mem_chartLeviCivitaGoodSet (I := I) α⟩ :
          p₀ ∈ (Set.univ : Set ℝ) ×ˢ chartLeviCivitaGoodSet (I := I) α))
    refine Filter.mem_of_superset h ?_
    rintro q ⟨hq1, hq2⟩
    exact ⟨hq1.1, hq2.2⟩
  have hcoord : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => Bb.repr
          (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2 σ)
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source) p₀ := by
    intro σ
    have hP1 := jointChartDeTurckRicciRHS_alongChart_contMDiffOn (I := I) g_bg T gfam hJ
      α (σ 0) (σ 1)
    refine ((hP1 p₀ ⟨hp₀.1, self_mem_chartLeviCivitaGoodSet (I := I) α⟩).mono_of_mem_nhdsWithin hgood).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hgood] with q hq
      obtain ⟨hqt, hqgood⟩ := hq
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (gfam q.1) q.2)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ q.2
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      have hframe : ∀ i : Fin 2,
          (trivializationAt E (TangentSpace I) α).symmL ℝ q.2 ((chartModelBasis E) (σ i)) =
            chartBasisVecFiber (I := I) α (σ i) q.2 :=
        fun i => by rw [chartBasisVecFiber, Trivialization.symmL_apply]
      rw [hframe 0, hframe 1]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (gfam q.1) g_bg α (σ 0) (σ 1) hqgood]
    · have hp₀good : p₀.2 ∈ chartLeviCivitaGoodSet (I := I) α := by
        exact self_mem_chartLeviCivitaGoodSet (I := I) α
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (gfam p₀.1) p₀.2)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ p₀.2
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      have hframe : ∀ i : Fin 2,
          (trivializationAt E (TangentSpace I) α).symmL ℝ p₀.2 ((chartModelBasis E) (σ i)) =
            chartBasisVecFiber (I := I) α (σ i) p₀.2 :=
        fun i => by rw [chartBasisVecFiber, Trivialization.symmL_apply]
      rw [hframe 0, hframe 1]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (gfam p₀.1) g_bg α (σ 0) (σ 1) hp₀good]
  have hpi : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun q : ℝ × M => (Bb.repr
        (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2 :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source) p₀ :=
    contMDiffWithinAt_pi_space.2 (fun σ => hcoord σ)
  have hsymm : ContMDiff 𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ)
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun c : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ => Bb.equivFun.symm c) :=
    (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  refine (hsymm.contMDiffAt.comp_contMDiffWithinAt p₀ hpi).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q _
    simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨q.2, deTurckRHSField (I := I) g_bg (gfam q.1) q.2⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm
  · simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨p₀.2, deTurckRHSField (I := I) g_bg (gfam p₀.1) p₀.2⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨p₀.2, deTurckRHSField (I := I) g_bg (gfam p₀.1) p₀.2⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_constOfIsEmpty_tensor0S_section :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffAt_fst, ?_⟩
  have hconst : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) ∞
      (fun _ : M × ℝ =>
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) :
          Tensor0SBundle.Tensor0SModel 0 ℝ E)) p₀ :=
    contMDiffAt_const
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards with p
  rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M)
    (fun _ : M => Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) p₀.1 p.1]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.constOfIsEmpty_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [show ((Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) :
        Tensor0SBundle.Tensor0SSpace 0 I p.1) 0) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) :
              Tensor0SBundle.Tensor0SSpace 0 I p.1) 0 from rfl,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem chartTensorInnerPointwise_0s_jointContMDiffOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ} :
    ∀ (n : ℕ)
    (TT SS : M × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (_hT : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => (TT p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (_hS : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => (SS p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1 (TT p) (SS p))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  intro n
  induction n with
  | zero =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ((TT p) (fun i => Fin.elim0 i)) * ((SS p) (fun i => Fin.elim0 i)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      have hempty :
          (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i; exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ => (TT p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (TT p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (TT p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hT0
      have hS_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ => (SS p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (SS p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (SS p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hS0
      exact hT_smooth.mul hS_smooth
  | succ n ih =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (n + 1) g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix (I := I) g α p.1)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1
                    ((TT p).curryLeft ((chartModelBasis E) i))
                    ((SS p).curryLeft ((chartModelBasis E) j)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · have hinv := chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
        have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
          trivializationAt_baseSet_eq_chartAt_source (I := I) α
        rw [hbase_eq] at hinv
        exact hinv.comp contMDiffOn_fst (fun p hp => hp.1)
      · refine ih
            (fun p : M × ℝ => (TT p).curryLeft ((chartModelBasis E) i))
            (fun p : M × ℝ => (SS p).curryLeft ((chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((TT p).curryLeft ((chartModelBasis E) i))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (TT p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((SS p).curryLeft ((chartModelBasis E) j))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (SS p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hS ψ'

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem loweredCompose_zero_basis_eval_jointContMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (Tval : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 2 I p.1)
    (arm : M × ℝ → TensorRSModel 0 2 ℝ E)
    (harm : ∀ p : M × ℝ,
      arm p (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p))
    (hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Tval p))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (φ : Fin (0 + 2) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  have heval : ∀ p : M × ℝ,
      (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p)
          (fun j : Fin 2 => chartBasisVecFiber (I := I) α
            (φ (Fin.natAdd 0 j)) p.1) := by
    intro p
    rw [loweredCompose_apply, lowerAllUpperIndices_apply, separableFormAt_zero, harm p]
    congr 1
  refine ContMDiffOn.congr ?_ (fun p _ => heval p)
  have hv : ∀ j : Fin 2, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro j
    have h := DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartBasisVec_jointContMDiffOn (I := I) α (φ (Fin.natAdd 0 j))
    exact h.mono (Set.prod_mono (subset_refl _) (Set.subset_univ _))
  intro p hp
  exact contMDiffWithinAt_section_apply_prod_full 2 (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
    (p₀ := p) Tval (hTval p hp)
    (fun j p => chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1)
    (fun j => hv j p hp)

theorem deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i).toFun
            p.1)
          ((deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toFun p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgfam
  have hJ : DifferentialGeometry.PDE.RicciFlow.JointChartGramSmooth (I := I) T gfam :=
    jointChartGramSmooth_of_spectralSmooth_timeSmooth (I := I) (M := M)
      g₀ hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hRHS_swap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckRHSField (I := I) g_bg (gfam p.2) p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    have hbase := deTurckRHSField_realizePath_jointContMDiffOn (I := I) g₀ g_bg F hδ_lt hδ hJ
    have hswap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_snd.prodMk contMDiffOn_fst
    have hmaps : Set.MapsTo (fun p : M × ℝ => (p.2, p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
      rintro ⟨x, t⟩ ⟨_, ht⟩; exact ⟨ht, Set.mem_univ _⟩
    exact hbase.comp hswap hmaps
  set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
    with heig_def
  set recon : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t) with hrecon_def
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, t₀⟩ ⟨_, ht₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
  rw [hinter]
  set α : M := x₀ with hα
  have hbridge : ∀ p ∈ (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          (eig.toFun p.1) ((recon p.2).toFun p.1) =
        chartTensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g₀ α p.1
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (eig.toFun p.1))
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((recon p.2).toFun p.1)) := by
    rintro ⟨y, u⟩ ⟨hy, _⟩
    have hb : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hy
    rw [tensorInnerPointwise_bridge_identity (I := I) (M := M) g₀ α 0 2 hb,
      chartTensorInnerPointwise_apply]
  refine ContMDiffOn.congr ?_ hbridge
  have harm_eig : ∀ p : M × ℝ,
      eig.toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (eig.toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := by
    intro p
    rfl
  have hTval_eig : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (eig.toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    have heigM := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_contMDiff
      (I := I) (M := M) g₀ 0 2 i
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) :=
      contMDiff_constOfIsEmpty_tensor0S_section
    have heigP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
          (E := fun z : M => TensorRSSpace 0 2 I z) p.1 (eig.toSection p.1)) :=
      heigM.comp contMDiff_fst
    have happ := ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
      (b := Prod.fst) (ϕ := fun p : M × ℝ => (eig.toSection p.1 : TensorRSSpace 0 2 I p.1))
      (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
      heigP hconst
    refine (happ.contMDiffOn).congr ?_
    rintro ⟨y, u⟩ _
    rfl
  have hcoeff_eig : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (eig.toFun p.1))
            (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn (I := I) (M := M) g₀ α
      (fun p => eig.toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => eig.toFun p.1) harm_eig hTval_eig φ
  have harm_recon : ∀ p : M × ℝ,
      (recon p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (gfam p.2) p.1) := by
    intro p
    have hl : (recon p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((deTurckRHSSection (I := I) g_bg (gfam p.2)).toSection p.1
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := rfl
    rw [hl]
    apply ContinuousMultilinearMap.ext
    intro v
    rw [deTurckRHSSection_toModel_apply, ← deTurckRHSField_toModel_apply]
  have hcoeff_recon : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((recon p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro φ
    refine loweredCompose_zero_basis_eval_jointContMDiffOn (I := I) (M := M) g₀ α
      (fun p => deTurckRHSField (I := I) g_bg (gfam p.2) p.1)
      (fun p => (recon p.2).toFun p.1) harm_recon ?_ φ
    exact hRHS_swap.mono (Set.prod_mono (fun y _ => Set.mem_univ y) (subset_refl _))
  exact chartTensorInnerPointwise_0s_jointContMDiffOn_smooth_args (I := I) (M := M) g₀ α
    (0 + 2)
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (eig.toFun p.1))
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((recon p.2).toFun p.1))
    hcoeff_eig hcoeff_recon

end RealizePathJointSmoothness

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
