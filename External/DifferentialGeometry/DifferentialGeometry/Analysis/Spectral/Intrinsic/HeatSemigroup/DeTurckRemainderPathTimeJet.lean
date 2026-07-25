import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.ParametricFiberInnerSmooth
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJetRealizePathJointSmoothness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJetOneMinusConnLapNormSqContinuity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJetFiniteOrderPairing


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

private theorem exists_smoothCcTensor_of_allOrder_spectralMass
    (g₀ : SmoothRiemannianMetric I M)
    (d : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i) :
    ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = d i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  obtain ⟨B0, hB0s, hB0le⟩ := hmass 0 le_rfl
  set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
    tensorHs_of_spectralMass_majorant (I := I) (M := M) d B0 hB0s hB0le with hv0_def
  set u : TensorL2 0 2 g₀ :=
    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = d i := by
    intro i
    rw [hu_def, tensorHsToL2_tensorL2Coeff]
    simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff]
  have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hBs
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · rw [hu_coeff i]; exact hBle i
  have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
    allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
  obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
  refine ⟨S, fun i => ?_⟩
  have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
        = (S : TensorL2 0 2 g₀) from rfl, hS]
  rw [hSL2, hu_coeff i]

private theorem deTurckRemainder_pathCoeff_timeContDiff
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
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContDiffOn ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T) := by
  classical
  intro i
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hsplit : ∀ t : ℝ,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i
          - tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i := by
    intro t
    have hrem :
        deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)
          = deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t)
            - rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t) := by
      rfl
    rw [hrem, SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  refine ContDiffOn.congr ?_ (fun t _ => hsplit t)
  refine ContDiffOn.sub ?_ ?_
  · have hbridge : ∀ t : ℝ,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
          (inner ℝ (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
            (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) : ℝ) := by
      intro t
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2]
    refine ContDiffOn.congr ?_ (fun t _ => hbridge t)
    exact DifferentialGeometry.Integral.L2.contDiffOn_integral_fiberInner_of_jointContMDiffOn_Icc
      (I := I) (M := M) g₀
      (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
      (fun t => deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))
      (deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn (I := I) (M := M)
        g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass i)
  · have hraw : ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i =
          -i.lambda * φ i t := by
      intro t ht
      rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F t) i,
        hcoeff t ht i]
    refine ContDiffOn.congr ?_ (fun t ht => hraw t ht)
    exact contDiffOn_const.mul (hφ_smooth i).contDiffOn

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem iteratedPartialSnd_contMDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ∀ j : ℕ, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  intro j
  induction j generalizing f with
  | zero =>
      refine hf.congr ?_
      intro p _
      rw [iteratedDerivWithin_zero]
  | succ n ih =>
      have hderiv : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : M × ℝ =>
            derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        DifferentialGeometry.partialSnd_contMDiffOn_Icc f hf
      have hih := ih (fun x s => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) s) hderiv
      refine hih.congr ?_
      intro p _
      rw [iteratedDerivWithin_succ']

private theorem clm_comm_iteratedDerivWithin {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (γ : ℝ → F) {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hγ : ContDiffWithinAt ℝ ∞ γ (Set.Icc (0 : ℝ) T) t) (j : ℕ) :
    iteratedDerivWithin j (fun s => L (γ s)) (Set.Icc (0 : ℝ) T) t =
      L (iteratedDerivWithin j γ (Set.Icc (0 : ℝ) T) t) := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hcomp : (fun s => L (γ s)) = L ∘ γ := rfl
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, hcomp,
    L.iteratedFDerivWithin_comp_left hγ hUD ht (by exact_mod_cast le_top),
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    iteratedDerivWithin_eq_iteratedFDerivWithin]
  rfl

private theorem reconChartRepr_jointContMDiffOn
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
    (α : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M =>
            (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection z) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
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
  have hFieldRepr : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) 2 α
          (fun z : M => deTurckRHSField (I := I) g_bg (gfam p.2) z) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro p hp
    obtain ⟨hx, hs⟩ := hp
    have hbase : p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet := by
      change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
      rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
        TangentBundle.trivializationAt_baseSet (I := I) α]
      exact hx
    have hsub : ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) ⊆
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun q hq => ⟨Set.mem_univ _, hq.2⟩
    have hFwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, deTurckRHSField (I := I) g_bg (gfam p.2) p.1⟩ :
          TotalSpace (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p :=
      (hRHS_swap p (hsub ⟨hx, hs⟩)).mono hsub
    have hsource : (⟨p.1, deTurckRHSField (I := I) g_bg (gfam p.2) p.1⟩ :
        TotalSpace (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)) ∈
        (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).source := by
      rw [Bundle.Trivialization.mem_source]; exact hbase
    have hrepr := ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, deTurckRHSField (I := I) g_bg (gfam p.2) p.1⟩ :
        TotalSpace (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)))
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p)
      (e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α) hsource).mp hFwithin).2
    refine hrepr.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      obtain ⟨hqx, _⟩ := hq
      have hqbase : q.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet := by
        change q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        exact hqx
      rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hqbase]
    · rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbase]
  set Lconst : Tensor0SBundle.Tensor0SModel 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    ContinuousLinearMap.smulRightL ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      with hLconst
  have hLsmooth : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞ (fun v => Lconst v) :=
    Lconst.contMDiff
  refine (hLsmooth.comp_contMDiffOn hFieldRepr).congr ?_
  intro p hp
  obtain ⟨hx, _⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
      TangentBundle.trivializationAt_baseSet (I := I) α]
    exact hx
  apply ContinuousLinearMap.ext
  intro D
  have hsec : (show Tensor0SBundle.Tensor0SSpace 0 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).symmL ℝ p.1 D) =
      ((continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap D) •
        deTurckRHSField (I := I) g_bg (gfam p.2) p.1 := by
    have hsymm0 := Bundle.continuousMultilinearMap.triv_zero_symmL_apply_elim0
      (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) α p.1 hxbase D
    have hcurry : ((continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap D)
        = D 0 := by
      change continuousMultilinearCurryFin0 ℝ E ℝ D = D 0
      rw [continuousMultilinearCurryFin0_apply]
    rw [hcurry]
    change (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) p.1).smulRight
        (deTurckRHSField (I := I) g_bg (gfam p.2) p.1)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).symmL ℝ p.1 D) = _
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply]
    exact congrArg (· • deTurckRHSField (I := I) g_bg (gfam p.2) p.1) hsymm0
  rw [Function.comp_apply,
    DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply_model
      (I := I) 0 2 α
      (fun z : M => (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection z)
      hxbase D,
    hsec, map_smul, hLconst,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    tensor0SChartE_section_repr_apply]

private theorem reconSec_jointContMDiffOn
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
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1))
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
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hCR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M =>
            (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection z) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    reconChartRepr_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass α
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
      (deTurckRHSReconSection (I := I) g₀ g_bg (F p₀.2) hδ_lt (hδ p₀.2)).toSection p₀.1⟩ :
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
            (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1⟩).2)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p₀ := by
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
      (deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
    (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p₀)
    (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem vec_iteratedPartialSnd_contMDiffOn_Icc
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Vf : M → ℝ → V) {T : ℝ} (hT : 0 < T)
    (hVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞ (fun p : M × ℝ => Vf p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) (j : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set A : V ≃L[ℝ] (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) :=
    (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv with hA
  have hAVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
      (fun p : M × ℝ => A (Vf p.1 p.2)) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
    (A.toContinuousLinearMap.contMDiff.comp_contMDiffOn hVf)
  have hcoord : ∀ i : Module.Basis.ofVectorSpaceIndex ℝ V,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    intro i
    have hfi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => A (Vf p.1 p.2) i) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.1 hAVf i
    exact iteratedPartialSnd_contMDiffOn_Icc (fun x s => A (Vf x s) i) hfi j
  have hkey : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => A.symm
        (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    have hpi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
        (fun p : M × ℝ => (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.2 hcoord
    exact A.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hpi
  refine hkey.congr ?_
  intro p hp
  obtain ⟨_, hs⟩ := hp
  have hfiber : ContDiffWithinAt ℝ ∞ (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2 := by
    have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (p.1, u))
        (Set.Icc (0 : ℝ) T) :=
      (contMDiffOn_const (c := p.1)).prodMk contMDiffOn_id
    have hmaps : Set.MapsTo (fun u : ℝ => (p.1, u)) (Set.Icc (0 : ℝ) T)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
    have hcomp := hVf.comp harg hmaps
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp p.2 hs
  have hcomm : (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2)
      = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) := by
    have hAcomm : iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2
        = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin A.toContinuousLinearMap (fun s => Vf p.1 s) hT hs hfiber j
    funext i
    have hfiberA : ContDiffWithinAt ℝ ∞ (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2 :=
      A.toContinuousLinearMap.contDiff.comp_contDiffWithinAt hfiber
    have hproj : iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2
        = (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
            (iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
        (fun s => A (Vf p.1 s)) hT hs hfiberA j
    rw [hproj, hAcomm]
    rfl
  rw [hcomm]
  exact (A.symm_apply_apply _).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem fiber_contDiffOn_Icc_recon
    (f : M → ℝ → ℝ) {T : ℝ}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) (x : M) :
    ContDiffOn ℝ ∞ (fun u : ℝ => f x u) (Set.Icc (0 : ℝ) T) := by
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
  have hcomp := hf.comp harg hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem hasDerivWithinAt_integral_param_Icc_recon
    [MeasurableSpace M] [OpensMeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun t => ∫ x, f x t ∂μ)
      (∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ) (Set.Icc (0 : ℝ) T) t₀ := by
  set s : Set ℝ := Set.Icc (0 : ℝ) T with hs_def
  have hconv : Convex ℝ s := convex_Icc 0 T
  have hUD : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hT
  set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) s t with hFd
  have hf_cont : ContinuousOn (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hf.continuousOn
  have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := partialSnd_contMDiffOn_Icc f hf
  have hFd_cont : ContinuousOn (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hFd_joint.continuousOn
  have hKcompact : IsCompact ((Set.univ : Set M) ×ˢ s) :=
    isCompact_univ.prod (isCompact_Icc)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFd_cont
  have hfiber_deriv : ∀ x : M, ∀ y ∈ s, HasDerivWithinAt (fun u => f x u) (Fd x y) s y := by
    intro x y hy
    have hcd : ContDiffOn ℝ ∞ (fun u : ℝ => f x u) s := fiber_contDiffOn_Icc_recon f hf x
    exact ((hcd.differentiableOn (by simp) y hy)).hasDerivWithinAt
  have hfiber : ∀ x : M, HasDerivWithinAt (fun u => f x u) (Fd x t₀) s t₀ :=
    fun x => hfiber_deriv x t₀ ht₀
  have hbound : ∀ x : M, ∀ t ∈ s, ‖f x t - f x t₀‖ ≤ C * ‖t - t₀‖ := by
    intro x t ht
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => hfiber_deriv x y hy) (fun y hy => ?_) hconv ht₀ ht
    exact hC (x, y) ⟨Set.mem_univ _, hy⟩
  have hf_slice_cont : ∀ t ∈ s, Continuous (fun x : M => f x t) := by
    intro t ht
    have harg : ContinuousOn (fun x : M => (x, t)) (Set.univ : Set M) := by fun_prop
    have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ s) := fun x _ => ⟨Set.mem_univ _, ht⟩
    have := (hf_cont.comp harg hmaps)
    rw [continuousOn_univ] at this
    exact this
  have hf_int : ∀ t ∈ s, Integrable (fun x : M => f x t) μ := by
    intro t ht
    exact integrableOn_univ.mp
      ((hf_slice_cont t ht).continuousOn.integrableOn_compact isCompact_univ)
  set G : ℝ → ℝ := fun t => ∫ x, f x t ∂μ with hG
  set G' : ℝ := ∫ x, Fd x t₀ ∂μ with hG'
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hslope_eq : ∀ t : ℝ, t ∈ s \ {t₀} →
      slope G t₀ t = ∫ x, slope (fun u => f x u) t₀ t ∂μ := by
    intro t ht
    have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
    rw [slope_def_field, hG]
    simp only []
    rw [show (∫ x, f x t ∂μ) - ∫ x, f x t₀ ∂μ
        = ∫ x, (f x t - f x t₀) ∂μ from
      (integral_sub (hf_int t ht.1) (hf_int t₀ ht₀)).symm]
    rw [div_eq_inv_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [slope_def_field, div_eq_inv_mul]
  have heq : (fun t => ∫ x, slope (fun u => f x u) t₀ t ∂μ) =ᶠ[𝓝[s \ {t₀}] t₀]
      slope G t₀ := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨s \ {t₀}, self_mem_nhdsWithin, fun t ht => (hslope_eq t ht).symm⟩
  refine Filter.Tendsto.congr' heq ?_
  · have hmeas : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        AEStronglyMeasurable (fun x : M => slope (fun u => f x u) t₀ t) μ := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      have : Continuous (fun x : M => slope (fun u => f x u) t₀ t) := by
        simp only [slope_def_field]
        exact ((hf_slice_cont t ht.1).sub (hf_slice_cont t₀ ht₀)).div_const _
      exact this.aestronglyMeasurable
    have hbnd : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        ∀ᵐ x ∂μ, ‖slope (fun u => f x u) t₀ t‖ ≤ C := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      refine Filter.Eventually.of_forall (fun x => ?_)
      have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
      have hpos : 0 < ‖t - t₀‖ := by
        rw [norm_pos_iff]; exact sub_ne_zero.mpr htne
      rw [slope_def_field, norm_div, div_le_iff₀ hpos]
      exact hbound x t ht.1
    have hlim : ∀ᵐ x ∂μ, Filter.Tendsto
        (fun t => slope (fun u => f x u) t₀ t) (𝓝[s \ {t₀}] t₀)
        (𝓝 (Fd x t₀)) :=
      Filter.Eventually.of_forall (fun x => (hasDerivWithinAt_iff_tendsto_slope.mp (hfiber x)))
    have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ : M => C)
      (F := fun t x => slope (fun u => f x u) t₀ t)
      (f := fun x => Fd x t₀)
      hmeas hbnd (integrable_const C) hlim
    simpa [hG'] using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem iteratedDerivWithin_integral_param_Icc
    [MeasurableSpace M] [OpensMeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ (j : ℕ) (f : M → ℝ → ℝ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ∀ t₀ ∈ Set.Icc (0 : ℝ) T,
        iteratedDerivWithin j (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) t₀ =
          ∫ x, iteratedDerivWithin j (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  intro j
  induction j with
  | zero =>
      intro f _ t₀ _
      simp only [iteratedDerivWithin_zero]
  | succ n ih =>
      intro f hf t₀ ht₀
      rw [iteratedDerivWithin_succ']
      set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) t
        with hFd
      have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => Fd p.1 p.2)
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := partialSnd_contMDiffOn_Icc f hf
      have hderiv_eqOn : Set.EqOn (derivWithin (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T))
          (fun t => ∫ x, Fd x t ∂μ) (Set.Icc (0 : ℝ) T) := by
        intro t ht
        exact (hasDerivWithinAt_integral_param_Icc_recon μ f hT hf ht).derivWithin (hUD t ht)
      rw [iteratedDerivWithin_congr hderiv_eqOn ht₀]
      rw [ih Fd hFd_joint t₀ ht₀]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact (iteratedDerivWithin_succ').symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem partialSnd_set_contMDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ} (U : Set M)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  rcases le_or_gt T 0 with hT0 | hT0
  · have hzero : Set.EqOn
        (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
        (fun _ : M × ℝ => (0 : ℝ)) (U ×ˢ Set.Icc (0 : ℝ) T) := by
      intro p hp
      have hnacc : ¬ AccPt p.2 (Filter.principal (Set.Icc (0 : ℝ) T)) := by
        rw [accPt_principal_iff_nhdsWithin]
        have hempty : Set.Icc (0 : ℝ) T \ {p.2} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro y hy
          exact hy.2 (Set.mem_singleton_iff.mpr
            ((Set.subsingleton_Icc_of_ge hT0) hy.1 hp.2))
        rw [hempty, nhdsWithin_empty]
        exact not_neBot.mpr rfl
      exact derivWithin_zero_of_not_accPt hnacc
    exact (contMDiffOn_const (c := (0 : ℝ))).congr hzero
  have hUM : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) T) :=
    (uniqueDiffOn_Icc hT0).uniqueMDiffOn
  have hrw : (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) =
      fun p : M × ℝ =>
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) (1 : ℝ) := by
    funext p
    rw [mfderivWithin_eq_fderivWithin]
    exact (fderivWithin_derivWithin (𝕜 := ℝ) (f := fun s => f p.1 s)
      (s := Set.Icc (0 : ℝ) T) (x := p.2)).symm
  rw [hrw, contMDiffOn_infty]
  intro n p₀ hp₀
  have hf' : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n + 1 : WithTop ℕ∞)
      (Function.uncurry (fun (p : M × ℝ) (s : ℝ) => f p.1 s))
      ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) := by
    have harg : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T)
        (U ×ˢ Set.Icc (0 : ℝ) T) :=
      fun q hq => ⟨hq.1.1, hq.2⟩
    have hcomp := (hf (p₀.1, p₀.2) ⟨hp₀.1, hp₀.2⟩).comp (p₀, p₀.2) harg hmaps
    exact hcomp.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞))
  have h_apply :=
    ContMDiffWithinAt.mfderivWithin_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : M × ℝ) (s : ℝ) => f p.1 s)
      (g := fun p : M × ℝ => p.2) (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ))
      (t := U ×ˢ Set.Icc (0 : ℝ) T)
      (u := Set.Icc (0 : ℝ) T)
      (v := U ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p₀) (n := (n : WithTop ℕ∞) + 1) (m := (n : WithTop ℕ∞))
      hf'
      contMDiffWithinAt_snd contMDiffWithinAt_id contMDiffWithinAt_const le_rfl
      (Set.mapsTo_id _) hp₀
      (fun q hq => hq.2) hUM
  simpa [inTangentCoordinates_model_space] using h_apply

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem iteratedPartialSnd_set_contMDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ} (U : Set M)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T)) :
    ∀ j : ℕ, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  intro j
  induction j generalizing f with
  | zero =>
      refine hf.congr ?_
      intro p _
      rw [iteratedDerivWithin_zero]
  | succ n ih =>
      have hderiv : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
          (U ×ˢ Set.Icc (0 : ℝ) T) :=
        partialSnd_set_contMDiffOn_Icc f U hf
      have hih := ih (fun x s => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) s) hderiv
      refine hih.congr ?_
      intro p _
      rw [iteratedDerivWithin_succ']

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem vec_iteratedPartialSnd_set_contMDiffOn_Icc
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {T : ℝ} (U : Set M)
    (Vf : M → ℝ → V)
    (hT : 0 < T)
    (hVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞ (fun p : M × ℝ => Vf p.1 p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T)) (j : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  set A : V ≃L[ℝ] (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) :=
    (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv with hA
  have hAVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
      (fun p : M × ℝ => A (Vf p.1 p.2)) (U ×ˢ Set.Icc (0 : ℝ) T) :=
    (A.toContinuousLinearMap.contMDiff.comp_contMDiffOn hVf)
  have hcoord : ∀ i : Module.Basis.ofVectorSpaceIndex ℝ V,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)
        (U ×ˢ Set.Icc (0 : ℝ) T) := by
    intro i
    have hfi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => A (Vf p.1 p.2) i) (U ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.1 hAVf i
    exact iteratedPartialSnd_set_contMDiffOn_Icc (fun x s => A (Vf x s) i) U hfi j
  have hkey : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞
      (fun p : M × ℝ => A.symm
        (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2))
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
    have hpi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ)) ∞
        (fun p : M × ℝ => (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)) (U ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.2 hcoord
    exact A.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hpi
  refine hkey.congr ?_
  intro p hp
  obtain ⟨hpU, hs⟩ := hp
  have hfiber : ContDiffWithinAt ℝ ∞ (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2 := by
    have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (p.1, u))
        (Set.Icc (0 : ℝ) T) :=
      (contMDiffOn_const (c := p.1)).prodMk contMDiffOn_id
    have hmaps : Set.MapsTo (fun u : ℝ => (p.1, u)) (Set.Icc (0 : ℝ) T)
        (U ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨hpU, hu⟩
    have hcomp := hVf.comp harg hmaps
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp p.2 hs
  have hcomm : (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2)
      = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) := by
    have hAcomm : iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2
        = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin A.toContinuousLinearMap (fun s => Vf p.1 s) hT hs hfiber j
    funext i
    have hfiberA : ContDiffWithinAt ℝ ∞ (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2 :=
      A.toContinuousLinearMap.contDiff.comp_contDiffWithinAt hfiber
    have hproj : iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2
        = (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
            (iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
        (fun s => A (Vf p.1 s)) hT hs hfiberA j
    rw [hproj, hAcomm]
    rfl
  rw [hcomm]
  exact (A.symm_apply_apply _).symm

private theorem deTurckRHSReconSection_timeJet_jointSmooth_section
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
    (j : ℕ) :
    ∃ Rjt : ℝ → SmoothCcTensor g₀ 0 2,
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
          iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t =
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Rjt p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set Rec : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun s => deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s) with hRec
  have hReconSec := reconSec_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ
    φ hφ_smooth hcoeff hmodemass
  set jetD : M → ℝ → Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    fun x t => iteratedDerivWithin j (fun s => (Rec s).toFun x) (Set.Icc (0 : ℝ) T) t
      with hjetD

  have hfiberRepr : ∀ (α : M) (x : M), x ∈ (chartAt H α).source →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
      ContDiffWithinAt ℝ ∞
        (fun s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x)
        (Set.Icc (0 : ℝ) T) t := by
    intro α x hx t ht
    have hCR := reconChartRepr_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ
      φ hφ_smooth hcoeff hmodemass α
    have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (x, u))
        (Set.Icc (0 : ℝ) T) :=
      (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
    have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨hx, hu⟩
    have hcomp := hCR.comp harg hmaps
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp t ht
  have hfiberSec : ∀ x : M, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ContDiffWithinAt ℝ ∞ (fun s => (Rec s).toFun x) (Set.Icc (0 : ℝ) T) t := by
    intro x t ht
    set α : M := x with hα
    have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H x
    have hxRSbase : x ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          exact hxsrc
    have hrepr := hfiberRepr α x hxsrc t ht
    set L : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
      (Tensor0SBundle.TensorRSSpace.toModelL (𝕜 := ℝ) 0 2 x).comp
        (DifferentialGeometry.Integral.Connection.tensorRSChartFiberFromModel (I := I) 0 2 α x)
      with hL
    have hLeq : ∀ s : ℝ, L
        (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x) = (Rec s).toFun x := by
      intro s
      rw [hL, ContinuousLinearMap.comp_apply,
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
      have hfib : DifferentialGeometry.Integral.Connection.tensorRSChartFiberFromModel
            (I := I) 0 2 α x
            ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt ℝ x
              ((Rec s).toSection x)) = (Rec s).toSection x := by
        rw [DifferentialGeometry.Integral.Connection.tensorRSChartFiberFromModel]
        exact Bundle.Trivialization.symmL_continuousLinearMapAt _ hxRSbase ((Rec s).toSection x)
      rw [hfib]
      rfl
    refine (L.contDiff.comp_contDiffWithinAt hrepr).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s _
      simp only [Function.comp_apply]
      exact (hLeq s).symm
    · simp only [Function.comp_apply]
      exact (hLeq t).symm

  have hChartCommute : ∀ (α : M) (x : M), x ∈ (chartAt H α).source → ∀ t ∈ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z t)) x =
        iteratedDerivWithin j
          (fun s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x)
          (Set.Icc (0 : ℝ) T) t := by
    intro α x hx t ht
    have hxRSbase : x ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          exact hx
    set Φ : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt ℝ x).comp
        ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
          : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSSpace 0 2 I x)
      with hΦ
    have hΦeq : ∀ s : ℝ, Φ ((Rec s).toFun x) =
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x := by
      intro s
      rw [hΦ, ContinuousLinearMap.comp_apply,
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
      have hsymm : ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
          : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSSpace 0 2 I x)
          ((Rec s).toFun x) = (Rec s).toSection x := by
        change (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
            ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x)
              ((Rec s).toSection x)) = (Rec s).toSection x
        exact (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv
          (I := I) 0 2 x).symm_apply_apply _
      rw [hsymm]
    have hΦLHS : DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z t)) x =
        Φ (jetD x t) := by
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply, hΦ,
        ContinuousLinearMap.comp_apply]
      rfl
    rw [hΦLHS]
    have hcomm := clm_comm_iteratedDerivWithin Φ (fun s => (Rec s).toFun x) hT ht
      (hfiberSec x t ht) j
    rw [hjetD]
    rw [← hcomm]
    refine iteratedDerivWithin_congr ?_ ht
    intro s _
    exact hΦeq s

  have hChartJet : ∀ α : M, ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z p.2)) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro α
    have hCR := reconChartRepr_jointContMDiffOn (I := I) g₀ g_bg hT F hδ_lt hδ
      φ hφ_smooth hcoeff hmodemass α
    have hvecjet := vec_iteratedPartialSnd_set_contMDiffOn_Icc
      (V := Tensor0SBundle.TensorRSModel 0 2 ℝ E) (U := (chartAt H α).source)
      (fun x s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (Rec s).toSection z) x) hT hCR j
    refine hvecjet.congr ?_
    intro p hp
    obtain ⟨hx, ht⟩ := hp
    exact hChartCommute α p.1 hx p.2 ht

  have hJet : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    refine contMDiffOn_of_locally_contMDiffOn ?_
    rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
    refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
      (chartAt H x₀).open_source.prod isOpen_univ,
      ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
    set α : M := x₀ with hα
    have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
        ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
        (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
      ext ⟨y, u⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
      tauto
    rw [hsub_eq]
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
    have hsource : (⟨p₀.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p₀.1 p₀.2)⟩ :
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
            ⟨p.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)⟩).2)
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p₀ := by
      refine ((hChartJet α) p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
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
      (f := fun p : M × ℝ => (⟨p.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p₀)
      (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
      ⟨contMDiffWithinAt_fst, hfib⟩)

  have hSlice : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) x
          (Tensor0SBundle.TensorRSSpace.ofModel (jetD x t))) := by
    intro t ht
    have harg : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun x : M => (x, t)) (Set.univ : Set M) :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun x _ => ⟨Set.mem_univ _, ht⟩
    have hcomp := hJet.comp harg hmaps
    rw [contMDiffOn_univ] at hcomp
    exact hcomp

  set Rjt : ℝ → SmoothCcTensor g₀ 0 2 := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) T then
      { toSection := ⟨fun x => Tensor0SBundle.TensorRSSpace.ofModel (jetD x t), hSlice t ht⟩
        hasCompactSupport := HasCompactSupport.of_compactSpace _ }
    else 0 with hRjtDef
  have hRjtEq : ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (0 : ℝ) T, Rjt t =
      { toSection := ⟨fun x => Tensor0SBundle.TensorRSSpace.ofModel (jetD x t), hSlice t ht⟩
        hasCompactSupport := HasCompactSupport.of_compactSpace _ } := by
    intro t ht
    rw [hRjtDef]; exact dif_pos ht
  have hRjtSection : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      (Rjt t).toSection x = Tensor0SBundle.TensorRSSpace.ofModel (jetD x t) := by
    intro t ht x
    rw [hRjtEq t ht]
    rfl
  have hRjtToFun : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      (Rjt t).toFun x = jetD x t := by
    intro t ht x
    have : (Rjt t).toFun x = Tensor0SBundle.TensorRSSpace.toModel ((Rjt t).toSection x) := rfl
    rw [this, hRjtSection t ht x, Tensor0SBundle.TensorRSSpace.toModel_ofModel]
  refine ⟨Rjt, ?_, ?_⟩
  · intro i t ht
    haveI : IsFiniteMeasure
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
    set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
      with hμ
    set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
      with heig

    have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (S.toFun x) ∂μ := by
      intro S
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
      rfl

    set fInt : M → ℝ → ℝ := fun x s =>
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (eig.toFun x) ((Rec s).toFun x) with hfInt
    have hfInt_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => fInt p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn (I := I) (M := M)
        g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass i

    have hLHS_eq : (fun s => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rec s)) i)
        = fun s => ∫ x, fInt x s ∂μ := by
      funext s
      rw [hcoeffInt (Rec s)]
    rw [hLHS_eq]

    rw [iteratedDerivWithin_integral_param_Icc μ hT j fInt hfInt_joint t ht]

    have hfiberJet : ∀ x : M, iteratedDerivWithin j (fun s => fInt x s) (Set.Icc (0 : ℝ) T) t =
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (eig.toFun x) (jetD x t) := by
      intro x
      have hL := clm_comm_iteratedDerivWithin
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
          (I := I) (M := M) g₀ 0 2 x (eig.toFun x))
        (fun s => (Rec s).toFun x) hT ht (hfiberSec x t ht) j
      simp only [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply] at hL
      rw [hfInt]
      rw [hjetD]
      exact hL

    have hRHS_eq : (∫ x, iteratedDerivWithin j (fun s => fInt x s) (Set.Icc (0 : ℝ) T) t ∂μ)
        = ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) ((Rjt t).toFun x) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      rw [hfiberJet x, hRjtToFun t ht x]
    rw [hRHS_eq, ← hcoeffInt (Rjt t)]
  · refine hJet.congr ?_
    intro p hp
    obtain ⟨_, ht⟩ := hp
    rw [hRjtSection p.2 ht p.1]

private theorem deTurckRHSReconCoeff_pathCoeff_timeJet_evenMass_uniformConst
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
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ (j k : ℕ), ∃ C : ℝ, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
          (iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ C := by
  classical
  intro j k
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  obtain ⟨Rjt, hRjt_coeff, hRjt_smooth⟩ :=
    deTurckRHSReconSection_timeJet_jointSmooth_section (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass j
  have hcont := deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn (I := I) (M := M)
    g₀ g_bg hT Rjt k hRjt_smooth
  obtain ⟨t₀, ht₀_mem, ht₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT.le) hcont
  refine ⟨‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t₀))‖ ^ 2, ?_⟩
  intro i t ht
  rw [hRjt_coeff i t ht]
  have hweq : tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2 =
      (tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))) i) ^ 2 := by
    rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ hc (Rjt t) i k,
      mul_pow]
    congr 1
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [hweq]
  have hsummable := tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) hc
    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t)))
  have hle_tsum : (tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))) i) ^ 2 ≤
      ∑' i' : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        (tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))) i') ^ 2 :=
    hsummable.le_tsum i (fun i' _ => sq_nonneg _)
  rw [tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) hc
    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t)))] at hle_tsum
  refine le_trans hle_tsum ?_
  exact ht₀_max ht

private theorem deTurckRHSReconCoeff_pathCoeff_timeJet_allOrderMass
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
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                  (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i := by
  classical
  set jet : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hjet_def
  have huniform := deTurckRHSReconCoeff_pathCoeff_timeJet_evenMass_uniformConst
    (I := I) (M := M) g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  intro j σ _hσ
  set s : ℝ := (weylSobolevExp (E := E) : ℝ) + 1 with hs_def
  have hs : (weylSobolevExp (E := E) : ℝ) < s := by rw [hs_def]; linarith
  obtain ⟨k, hk⟩ := exists_nat_ge ((σ + s) / 2)
  have hk2 : σ + s ≤ ((2 * k : ℕ) : ℝ) := by
    push_cast
    have : (σ + s) / 2 ≤ (k : ℝ) := hk
    linarith
  obtain ⟨C, hC⟩ := huniform j k
  refine ⟨fun i => C * tensorSobolevWeight (I := I) (M := M) i (-s),
    (tensorEigen_summable_negpow (I := I) (M := M) g₀ s hs).mul_left C, ?_⟩
  intro i t ht
  have hnegnn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-s) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i (-s)
  have hjsq : 0 ≤ (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 := sq_nonneg _
  have hmono : tensorSobolevWeight (I := I) (M := M) i (σ + s) ≤
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) :=
    tensorSobolevWeight_mono (I := I) (M := M) i hk2
  have hstep : tensorSobolevWeight (I := I) (M := M) i (σ + s) *
        (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
        (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 :=
    mul_le_mul_of_nonneg_right hmono hjsq
  have hCbound : tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
      (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ C := hC i t ht
  have hadd : tensorSobolevWeight (I := I) (M := M) i σ =
      tensorSobolevWeight (I := I) (M := M) i (-s) *
        tensorSobolevWeight (I := I) (M := M) i (σ + s) := by
    rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-s) (σ + s)]
    ring_nf
  calc tensorSobolevWeight (I := I) (M := M) i σ *
        (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2
      = tensorSobolevWeight (I := I) (M := M) i (-s) *
          (tensorSobolevWeight (I := I) (M := M) i (σ + s) *
            (iteratedDerivWithin j (jet i) (Set.Icc (0 : ℝ) T) t) ^ 2) := by
        rw [hadd]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i (-s) * C := by
        refine mul_le_mul_of_nonneg_left ?_ hnegnn
        exact le_trans hstep hCbound
    _ = C * tensorSobolevWeight (I := I) (M := M) i (-s) := by ring

private theorem deTurckRemainder_pathCoeff_timeJet_allOrderMass
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
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                  (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set reconRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hreconRaw_def
  set rawRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F s))) i with hrawRaw_def
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hcpath_def
  have hsplit : ∀ i s, cpath i s = reconRaw i s - rawRaw i s := by
    intro i s
    have hrem :
        deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
          = deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
            - rawTensorConnLapSmooth (I := I) g₀ 0 2 (F s) := rfl
    simp only [hcpath_def, hreconRaw_def, hrawRaw_def]
    rw [hrem, SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  have hrecon_smooth : ∀ i, ContDiffOn ℝ ∞ (reconRaw i) (Set.Icc (0 : ℝ) T) := by
    intro i
    have hbridge : ∀ s : ℝ, reconRaw i s =
        (inner ℝ (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
            (I := I) (M := M) g₀ 0 2 i)
          (deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s)) : ℝ) := by
      intro s
      simp only [hreconRaw_def]
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2]
    refine ContDiffOn.congr ?_ (fun s _ => hbridge s)
    exact DifferentialGeometry.Integral.L2.contDiffOn_integral_fiberInner_of_jointContMDiffOn_Icc
      (I := I) (M := M) g₀
      (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
      (fun s => deTurckRHSReconSection (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
      (deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn (I := I) (M := M)
        g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass i)
  have hraw_eqOn : ∀ i, Set.EqOn (rawRaw i)
      (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) := by
    intro i s hs
    simp only [hrawRaw_def]
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F s) i,
      hcoeff s hs i]
  have hraw_smooth : ∀ i, ContDiffOn ℝ ∞ (rawRaw i) (Set.Icc (0 : ℝ) T) := by
    intro i
    refine ContDiffOn.congr ?_ (hraw_eqOn i)
    exact contDiffOn_const.mul (hφ_smooth i).contDiffOn
  intro j σ hσ
  obtain ⟨Brecon, hBrecon_sum, hBrecon_le⟩ :=
    deTurckRHSReconCoeff_pathCoeff_timeJet_allOrderMass (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass j σ hσ
  obtain ⟨Braw, hBraw_sum, hBraw_le⟩ := hmodemass j (σ + 2) (by linarith)
  refine ⟨fun i => 2 * Brecon i + 2 * Braw i,
    (hBrecon_sum.mul_left 2).add (hBraw_sum.mul_left 2), ?_⟩
  · intro i t ht
    have hUDO : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
    have hcds : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (reconRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hrecon_smooth i) t ht).of_le (mod_cast le_top)
    have hcdr : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (rawRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hraw_smooth i) t ht).of_le (mod_cast le_top)
    have hderivEq : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
        iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t -
          iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t := by
      have hcongr : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => reconRaw i s - rawRaw i s)
            (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (fun s _ => hsplit i s) ht
      rw [hcongr]
      have hsub := iteratedDerivWithin_sub (f := reconRaw i) (g := rawRaw i)
        (n := j) ht hUDO hcds hcdr
      simpa only [Pi.sub_apply] using hsub
    have hrawDerivEq : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
        -i.lambda * iteratedDeriv j (φ i) t := by
      have hcongr : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (hraw_eqOn i) ht
      rw [hcongr,
        iteratedDerivWithin_const_mul ht hUDO (-i.lambda)
          ((hφ_smooth i).contDiffOn.of_le (mod_cast le_top) t ht),
        iteratedDerivWithin_eq_iteratedDeriv hUDO
          ((hφ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht]
    rw [hderivEq]
    set a : ℝ := iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t with ha_def
    set b : ℝ := iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t with hb_def
    have hwσ_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    have hsq : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
    have hweighted : tensorSobolevWeight (I := I) (M := M) i σ * (a - b) ^ 2 ≤
        2 * (tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq hwσ_nn
      nlinarith [this]
    refine le_trans hweighted ?_
    have hterm_recon : tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2 ≤ Brecon i :=
      hBrecon_le i t ht
    have hterm_raw : tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2 ≤ Braw i := by
      have hbsq : b ^ 2 = i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2 := by
        rw [hrawDerivEq]; ring
      have hlam_sq_le : i.lambda ^ 2 ≤ tensorSobolevWeight (I := I) (M := M) i 2 := by
        have hw2 : tensorSobolevWeight (I := I) (M := M) i 2 =
            (1 + i.lambda) ^ 2 := by
          unfold tensorSobolevWeight
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hw2]
        have hlam_nn : 0 ≤ i.lambda := tensor_lambda_nonneg (I := I) (M := M) i
        nlinarith [hlam_nn]
      have hmm : tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          (iteratedDeriv j (φ i) t) ^ 2 ≤ Braw i := hBraw_le i t ht
      have hsplitw : tensorSobolevWeight (I := I) (M := M) i (σ + 2) =
          tensorSobolevWeight (I := I) (M := M) i σ *
            tensorSobolevWeight (I := I) (M := M) i 2 :=
        tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2
      have hdjsq_nn : 0 ≤ (iteratedDeriv j (φ i) t) ^ 2 := sq_nonneg _
      calc tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2
          = tensorSobolevWeight (I := I) (M := M) i σ *
              (i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2) := by rw [hbsq]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i σ *
              (tensorSobolevWeight (I := I) (M := M) i 2 *
                (iteratedDeriv j (φ i) t) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hwσ_nn
            exact mul_le_mul_of_nonneg_right hlam_sq_le hdjsq_nn
        _ = tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
              (iteratedDeriv j (φ i) t) ^ 2 := by rw [hsplitw]; ring
        _ ≤ Braw i := hmm
    nlinarith [hterm_recon, hterm_raw]

theorem deTurckRemainder_path_coeff_timeJet_withMass
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
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          ContDiffOn ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
            (Set.Icc (0 : ℝ) T)) ∧
        (∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
              (Set.Icc (0 : ℝ) T) t =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
        (∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
              tensorSobolevWeight (I := I) (M := M) i σ *
                  (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ^ 2 ≤ B i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i with hcpath_def
  have hsmooth : ∀ i, ContDiffOn ℝ ∞ (cpath i) (Set.Icc (0 : ℝ) T) :=
    deTurckRemainder_pathCoeff_timeContDiff (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hmass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i :=
    deTurckRemainder_pathCoeff_timeJet_allOrderMass (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hconstruct : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t := by
    intro j t ht
    refine exists_smoothCcTensor_of_allOrder_spectralMass (I := I) (M := M)
      g₀ (fun i => iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t) (fun σ hσ => ?_)
    obtain ⟨B, hBs, hBle⟩ := hmass j σ hσ
    exact ⟨B, hBs, fun i => hBle i t ht⟩
  choose! Rjet hRjet using hconstruct
  have hR_coeff : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i =
        iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t := by
    intro j t ht i
    exact hRjet j t ht i
  refine ⟨Rjet, hsmooth, ?_, ?_⟩
  · intro j i t ht
    rw [hR_coeff j t ht i]
  · intro j σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass j σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    rw [hR_coeff j t ht i]
    exact hBle i t ht

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
