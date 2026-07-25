import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreyHigherOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorChartFrameSection
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorL2ChartComponentExt
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartL2BoundedConvergence
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothChartComponent
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.PouCutoffComponentBridge


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Topology Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem exists_zeroContentR_le_fiberNorm_on_pouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {y : EuclN},
        y ∈ chartPouKernel (I := I) (M := M) α →
        tensorComponentAbsSum (I := I) (M := M) g r s S α y ≤
          C * ‖S.toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s

  set Tα : Set M := tsupport
    (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hTα_def
  have hTα_src : Tα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α

  obtain ⟨Craw, hCraw_nn, hCraw⟩ :=
    tensorChartComponentRaw_sq_le_const_mul_tensorInner (I := I) (M := M) g r s α

  set Npair : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
    (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity
  refine ⟨Npair * Real.sqrt Craw, by positivity, ?_⟩
  intro S y hy
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def

  have hb_supp : b ∈ Tα := by
    obtain ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩ := hy
    have hx_chart : x ∈ (chartAt H α).source := hTα_src hx_supp
    have hb_eq : b = x := by
      rw [hb_def, ← hzy, (toEuclidean (E := E)).symm_apply_apply, ← hxz]
      exact (extChartAt I α).left_inv
        (by rw [extChartAt_source (I := I)]; exact hx_chart)
    rw [hb_eq]; exact hx_supp

  have hfib_eq : ‖S.toSection b‖ =
      Real.sqrt (tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) := by
    rw [show S.toFun b = TensorRSSpace.toModel (𝕜 := ℝ) (I := I) (S.toSection b) from rfl]
    exact DifferentialGeometry.Integral.Connection.norm_eq_sqrt_tensorInnerPointwise
      (I := I) (M := M) g r s b (S.toSection b)
  have hInner_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hfib_nn : 0 ≤ ‖S.toSection b‖ := norm_nonneg _

  have h_raw_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorComponentEuclideanChart (I := I) (M := M) g r s S α Idx Jdx y =
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
    intro Idx Jdx
    rw [tensorComponentEuclideanChart, Function.comp_apply, Function.comp_apply, ← hb_def]

  have h_each : ∀ (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))),
      |tensorComponentEuclideanChart (I := I) (M := M) g r s S α q.1 q.2 y| ≤
        Real.sqrt Craw * ‖S.toSection b‖ := by
    intro q
    rw [h_raw_eq q.1 q.2]
    have hsq := hCraw S q.1 q.2 b hb_supp
    have hroot :
        Real.sqrt
            ((tensorChartComponentRaw (I := I) (M := M) g r s S α q.1 q.2 b) ^ 2) ≤
          Real.sqrt (Craw * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs] at hroot
    refine hroot.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hCraw_nn, hfib_eq]
  calc tensorComponentAbsSum (I := I) (M := M) g r s S α y
      = ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          |tensorComponentEuclideanChart (I := I) (M := M) g r s S α q.1 q.2 y| := rfl
    _ ≤ ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          Real.sqrt Craw * ‖S.toSection b‖ :=
        Finset.sum_le_sum (fun q _ => h_each q)
    _ = Npair * Real.sqrt Craw * ‖S.toSection b‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpair_def]; ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
private theorem exists_iteratedFDeriv_chartComponent_le_fiberNorm_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : SmoothCcTensor g r s) (y : EuclN),
        ‖iteratedFDeriv ℝ j
            (tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2) y‖ ≤
          C * ∑ i ∈ Finset.range (j + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
            ‖(iteratedCovGrad g r s i D).toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) := by
  classical

  obtain ⟨Cpou, hCpou_nn, hCpou⟩ :=
    exists_iteratedFDeriv_norm_bound_on_compactR
      (chartPushedRaw_chartAtlasPOU_contDiffOn
        (I := I) (M := M) α)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α)
      (chartImagePOUTsupport_subset_target (I := I) (M := M) α) j

  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum (I := I) (M := M) g r s α j j (le_refl j)

  have h_fib : ∀ i : ℕ,
      ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ (T : SmoothCcTensor g r (s + i)) {z : EuclN},
        z ∈ chartPouKernel (I := I) (M := M) α →
        tensorComponentAbsSum (I := I) (M := M) g r (s + i) T α z ≤
          Ci * (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
            ‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))‖) :=
    fun i => exists_zeroContentR_le_fiberNorm_on_pouKernel (I := I) (M := M) g r (s + i) α
  choose Cfib hCfib_nn hCfib using h_fib
  set Cfibmax : ℝ := (Finset.range (j + 1)).sup' (by simp) Cfib with hCfibmax_def
  have hCfibmax_nn : 0 ≤ Cfibmax :=
    le_trans (hCfib_nn 0) (Finset.le_sup' Cfib (by simp))
  refine ⟨(2 : ℝ) ^ j * Cpou * Cpeel * Cfibmax, by positivity, ?_⟩
  intro D y
  set fibSum : ℝ := ∑ i ∈ Finset.range (j + 1),
    (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
    ‖(iteratedCovGrad g r s i D).toSection
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) with hfibSum_def
  have hfibSum_nn : 0 ≤ fibSum := by
    rw [hfibSum_def]
    refine Finset.sum_nonneg (fun i _ => ?_)
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
    exact norm_nonneg _
  by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
  · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α :=
      chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α hyK
    set ρ : EuclN → ℝ :=
      chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_def
    set raw : EuclN → ℝ :=
      chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g r s D α P.1 P.2)
      with hraw_def

    have h_evEq : tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2 =ᶠ[nhds y]
        (fun z => ρ z * raw z) :=
      tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw_raw
        (I := I) (M := M) g r s D α P.1 P.2 hyT
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_evEq j).self_of_nhds]

    have hO_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hρ_cdOn : ContDiffOn ℝ ∞ ρ (chartTargetEuclid (I := I) (M := M) α) :=
      chartPushedRaw_chartAtlasPOU_contDiffOn
        (I := I) (M := M) α
    have hraw_cdOn : ContDiffOn ℝ ∞ raw (chartTargetEuclid (I := I) (M := M) α) := by
      refine (rawPullR_contDiffOn (I := I) (M := M) g r s D α P.1 P.2).congr (fun z hz => ?_)
      rw [hraw_def, chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]; rfl

    have hLeib := norm_iteratedFDerivWithin_mul_le
      (𝕜 := ℝ) (f := ρ) (g := raw) (n := j) hρ_cdOn hraw_cdOn
      hO_open.uniqueDiffOn hyT (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => ρ z * raw z) j hO_open hyT] at hLeib
    refine le_trans hLeib ?_

    have hbound_term : ∀ l ∈ Finset.range (j + 1),
        (j.choose l : ℝ) *
            ‖iteratedFDerivWithin ℝ l ρ (chartTargetEuclid (I := I) (M := M) α) y‖ *
            ‖iteratedFDerivWithin ℝ (j - l) raw
              (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
          (j.choose l : ℝ) * Cpou * (Cpeel * Cfibmax * fibSum) := by
      intro l hl
      have hlj : l ≤ j := by have := Finset.mem_range.mp hl; omega

      have hρ_l : ‖iteratedFDerivWithin ℝ l ρ
          (chartTargetEuclid (I := I) (M := M) α) y‖ ≤ Cpou := by
        rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := ρ) l hO_open hyT]
        exact hCpou l hlj y hyK

      have hraw_l : ‖iteratedFDerivWithin ℝ (j - l) raw
          (chartTargetEuclid (I := I) (M := M) α) y‖ ≤ Cpeel * Cfibmax * fibSum := by
        rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := raw) (j - l) hO_open hyT]

        have hraw_evEq : raw =ᶠ[nhds y]
            tensorComponentEuclideanChart (I := I) (M := M) g r s D α P.1 P.2 := by
          filter_upwards [hO_open.mem_nhds hyT] with z hz
          rw [hraw_def, chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]; rfl
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hraw_evEq (j - l)).self_of_nhds]

        have hpeel := hCpeel D (j - l) (Nat.sub_le j l) 0 (by omega) P.1 P.2 y hyK
        have h0eq : (iteratedCovGrad g r s 0 D) = D :=
          DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero (I := I) (M := M) g r s D
        rw [h0eq] at hpeel

        have hreindex : (∑ i ∈ Finset.range ((j - l) + 1),
              tensorComponentAbsSum (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) D) α y) =
            ∑ i ∈ Finset.range ((j - l) + 1),
              tensorComponentAbsSum (I := I) (M := M) g r (s + i)
                (iteratedCovGrad g r s i D) α y := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          congr 1 <;> rw [Nat.zero_add]
        rw [hreindex] at hpeel

        refine le_trans hpeel ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hCpeel_nn

        have hstep : ∀ i ∈ Finset.range ((j - l) + 1),
            tensorComponentAbsSum (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i D) α y ≤
              Cfibmax *
                (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                ‖(iteratedCovGrad g r s i D).toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) := by
          intro i hi
          have hij : i ≤ j := by
            have := Finset.mem_range.mp hi; omega
          have hib := hCfib i (iteratedCovGrad g r s i D) hyK
          refine le_trans hib ?_
          letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
          exact mul_le_mul_of_nonneg_right
            (Finset.le_sup' Cfib (Finset.mem_range.mpr (by omega))) (norm_nonneg _)
        calc (∑ i ∈ Finset.range ((j - l) + 1),
              tensorComponentAbsSum (I := I) (M := M) g r (s + i)
                (iteratedCovGrad g r s i D) α y)
            ≤ ∑ i ∈ Finset.range ((j - l) + 1),
                Cfibmax *
                  (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                  ‖(iteratedCovGrad g r s i D).toSection
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) :=
              Finset.sum_le_sum hstep
          _ = Cfibmax * ∑ i ∈ Finset.range ((j - l) + 1),
                (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                ‖(iteratedCovGrad g r s i D).toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) := by
              rw [Finset.mul_sum]
          _ ≤ Cfibmax * fibSum := by
              refine mul_le_mul_of_nonneg_left ?_ hCfibmax_nn
              rw [hfibSum_def]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
              · intro i hi
                exact Finset.mem_range.mpr
                  (lt_of_lt_of_le (Finset.mem_range.mp hi)
                    (Nat.succ_le_succ (Nat.sub_le j l)))
              · letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                exact norm_nonneg _

      have hchoose_nn : 0 ≤ (j.choose l : ℝ) := by positivity
      have hraw_l_nn : 0 ≤ ‖iteratedFDerivWithin ℝ (j - l) raw
          (chartTargetEuclid (I := I) (M := M) α) y‖ := norm_nonneg _
      have h1 : (j.choose l : ℝ) *
          ‖iteratedFDerivWithin ℝ l ρ
            (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
          (j.choose l : ℝ) * Cpou :=
        mul_le_mul_of_nonneg_left hρ_l hchoose_nn
      have h2 : (j.choose l : ℝ) *
            ‖iteratedFDerivWithin ℝ l ρ
              (chartTargetEuclid (I := I) (M := M) α) y‖ *
            ‖iteratedFDerivWithin ℝ (j - l) raw
              (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
          ((j.choose l : ℝ) * Cpou) * (Cpeel * Cfibmax * fibSum) :=
        mul_le_mul h1 hraw_l hraw_l_nn (by positivity)
      have h3 : ((j.choose l : ℝ) * Cpou) * (Cpeel * Cfibmax * fibSum) =
          (j.choose l : ℝ) * Cpou * (Cpeel * Cfibmax * fibSum) := by ring
      exact h3 ▸ h2
    have hsum_choose : (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ)) = (2 : ℝ) ^ j := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    have hstep_sum :
        (∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) *
              ‖iteratedFDerivWithin ℝ l ρ (chartTargetEuclid (I := I) (M := M) α) y‖ *
              ‖iteratedFDerivWithin ℝ (j - l) raw
                (chartTargetEuclid (I := I) (M := M) α) y‖) ≤
          ∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) * Cpou * (Cpeel * Cfibmax * fibSum) :=
      Finset.sum_le_sum hbound_term
    refine hstep_sum.trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum_choose]; ring
  · have h_evZero : tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2 =ᶠ[nhds y]
        (fun _ => (0 : ℝ)) := by
      have hKclosed : IsClosed (chartPouKernel (I := I) (M := M) α) :=
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
      filter_upwards [hKclosed.isOpen_compl.mem_nhds hyK] with z hz
      exact tensorChartComponent_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s D α P.1 P.2 hz
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_evZero j).self_of_nhds,
      iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem tensorChartComponent_allOrder_uniformCauchy
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) (j : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
      ∀ y : EuclN,
        ‖iteratedFDeriv ℝ j
            (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2) y -
          iteratedFDeriv ℝ j
            (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2) y‖ ≤ ε := by
  classical

  set n : ℕ := Module.finrank ℝ E with hn_def
  set k : ℕ := n + 2 * j + 1 with hk_def
  have h_super : 2 * k > n + 2 * j := by rw [hk_def]; omega

  obtain ⟨Cder, hCder_nn, hCder⟩ :=
    exists_iteratedFDeriv_chartComponent_le_fiberNorm_sum (I := I) (M := M) g r s α P j

  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_toSobolev_embedding_Cm_singleNorm
      (I := I) (M := M) g r s k j h_super

  have hF_cauchy_k := Metric.cauchySeq_iff.mp (hF_cauchy k)
  set δ : ℝ := ε / (Cder * Cemb + 1) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  obtain ⟨N, hN⟩ := hF_cauchy_k δ hδ_pos
  refine ⟨N, fun n' n'' hn' hn'' y => ?_⟩

  set D : SmoothCcTensor g r s := F n' - F n'' with hD_def

  have h_comp_sub :
      (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2 -
          tensorChartComponent (I := I) (M := M) g r s (F n'') α P.1 P.2) =
      tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2 := by
    have hsub : D = F n' + (-1 : ℝ) • F n'' := by
      rw [hD_def, neg_one_smul, ← sub_eq_add_neg]
    rw [hsub, tensorChartComponent_add (I := I) (M := M) g r s (F n') ((-1 : ℝ) • F n'') α P.1 P.2,
      tensorChartComponent_smul (I := I) (M := M) g r s (-1 : ℝ) (F n'') α P.1 P.2]
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

  have h_iter_sub :
      iteratedFDeriv ℝ j
          (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2) y -
        iteratedFDeriv ℝ j
          (tensorChartComponent (I := I) (M := M) g r s (F n'') α P.1 P.2) y =
      iteratedFDeriv ℝ j (tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2) y := by
    have hcd1 : ContDiff ℝ (j : ℕ∞)
        (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2) :=
      (tensorChartComponent_contDiff' (I := I) (M := M) g r s (F n') α P.1 P.2).of_le
        (by exact_mod_cast le_top)
    have hcd2 : ContDiff ℝ (j : ℕ∞)
        (tensorChartComponent (I := I) (M := M) g r s (F n'') α P.1 P.2) :=
      (tensorChartComponent_contDiff' (I := I) (M := M) g r s (F n'') α P.1 P.2).of_le
        (by exact_mod_cast le_top)
    rw [← iteratedFDeriv_sub_apply (hcd1.contDiffAt) (hcd2.contDiffAt), h_comp_sub]
  rw [h_iter_sub]

  refine le_trans (hCder D y) ?_

  have hemb := hCemb D ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  set N2k : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) D‖ with hN2k_def
  have hN2k_nn : 0 ≤ N2k := norm_nonneg _

  have hD_small : N2k < δ := by
    rw [hN2k_def, hD_def,
      DifferentialGeometry.PDE.RicciFlow.SmoothCcTensor.toHs_sub (g := g) (2 * k) (F n') (F n'')]
    have := hN n' hn' n'' hn''
    rwa [dist_eq_norm] at this
  have h_fibSum_le :
      (∑ i ∈ Finset.range (j + 1),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
        ‖(iteratedCovGrad g r s i D).toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖)) ≤ Cemb * N2k :=
    hemb
  calc Cder * (∑ i ∈ Finset.range (j + 1),
          (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
          ‖(iteratedCovGrad g r s i D).toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖))
      ≤ Cder * (Cemb * N2k) :=
        mul_le_mul_of_nonneg_left h_fibSum_le hCder_nn
    _ = (Cder * Cemb) * N2k := by ring
    _ ≤ (Cder * Cemb) * δ := by
        refine mul_le_mul_of_nonneg_left hD_small.le ?_
        positivity
    _ ≤ ε := by
        rw [hδ_def]
        have hden_pos : 0 < Cder * Cemb + 1 := by positivity
        rw [mul_div_assoc', div_le_iff₀ hden_pos]
        have hCC_nn : 0 ≤ Cder * Cemb := by positivity
        nlinarith [mul_nonneg hCC_nn hε.le]

omit [BoundarylessManifold I M] in
theorem exists_chartComponent_limit_smooth_compactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) :
    ∃ u : TensorCompIdx (E := E) r s → EuclN → ℝ,
      (∀ P, ContDiffOn ℝ ∞ (u P) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ P, HasCompactSupport (u P) ∧
        tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α) ∧
      (∀ (P : TensorCompIdx (E := E) r s) (y : EuclN),
        Filter.Tendsto
          (fun n => tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y)
          Filter.atTop (𝓝 (u P y))) := by
  classical

  set gseq : TensorCompIdx (E := E) r s → ℕ → EuclN → ℝ :=
    fun P n => tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 with hgseq_def

  have hcauchy : ∀ (P : TensorCompIdx (E := E) r s) (j : ℕ),
      ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ y : EuclN,
        ‖iteratedFDeriv ℝ j (gseq P n) y - iteratedFDeriv ℝ j (gseq P n') y‖ ≤ ε := by
    intro P j ε hε
    exact tensorChartComponent_allOrder_uniformCauchy
      (I := I) (M := M) g r s F hF_cauchy α P j ε hε

  have hcauchy0 : ∀ (P : TensorCompIdx (E := E) r s),
      ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ y : EuclN,
        ‖gseq P n y - gseq P n' y‖ ≤ ε := by
    intro P ε hε
    obtain ⟨N, hN⟩ := hcauchy P 0 ε hε
    refine ⟨N, fun n n' hn hn' y => ?_⟩
    have hraw := hN n n' hn hn' y
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp,
      Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] at hraw
    exact hraw

  have hsmooth : ∀ (P : TensorCompIdx (E := E) r s) (n : ℕ),
      ContDiff ℝ (⊤ : ℕ∞) (gseq P n) := by
    intro P n
    exact tensorChartComponent_contDiff' (I := I) (M := M) g r s (F n) α P.1 P.2

  set u : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => cauchyLimitFun (d := Module.finrank ℝ E)
      (gseq P) (hcauchy0 P) with hu_def
  refine ⟨u, ?_, ?_, ?_⟩
  · intro P
    have hcontDiff : ContDiff ℝ (⊤ : ℕ∞) (u P) := by
      rw [contDiff_infty]
      intro m
      exact (iteratedFDeriv_cauchyLimitFun_eq (d := Module.finrank ℝ E)
        m (hsmooth P) (hcauchy0 P) (fun j _ => hcauchy P j)).1
    exact hcontDiff.contDiffOn
  · intro P
    have hsupp_subset : Function.support (u P) ⊆ chartPouKernel (I := I) (M := M) α := by
      intro z hz
      by_contra hzk

      have hzero : ∀ n, gseq P n z = 0 := by
        intro n
        have hsub := tensorChartComponent_tsupport_subset_chartPouKernel
          (I := I) (M := M) g r s (F n) α P.1 P.2
        exact image_eq_zero_of_notMem_tsupport (fun hmem => hzk (hsub hmem))
      have htends : Filter.Tendsto (fun n => gseq P n z) Filter.atTop (𝓝 (u P z)) :=
        cauchyLimitFun_tendsto (d := Module.finrank ℝ E)
          (hcauchy0 P) z
      have hlim0 : u P z = 0 :=
        tendsto_nhds_unique htends (by simpa only [hzero] using tendsto_const_nhds)
      exact hz hlim0
    have htsupp_subset : tsupport (u P) ⊆ chartPouKernel (I := I) (M := M) α :=
      closure_minimal hsupp_subset
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
    refine ⟨?_, htsupp_subset.trans
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)⟩
    exact HasCompactSupport.of_support_subset_isCompact
      (chartPouKernel_isCompact (I := I) (M := M) α) hsupp_subset
  · intro P y
    exact cauchyLimitFun_tendsto (d := Module.finrank ℝ E) (hcauchy0 P) y

def chartLimitSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1

def globalLimitSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n))) :
    SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    chartLimitSection (I := I) (M := M) g r s F hF_cauchy α

private def chartLimitComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) : TensorCompIdx (E := E) r s → EuclN → ℝ :=
  (exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose

omit [BoundarylessManifold I M] in
private lemma chartLimitComp_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  ((exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 P).2

omit [BoundarylessManifold I M] in
private lemma chartLimitComp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) (y : EuclN) :
    Tendsto
      (fun n => tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y)
      atTop (𝓝 (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y)) :=
  (exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.2 P y

omit [BoundarylessManifold I M] in
private lemma chartLimitComp_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ y : EuclN,
      ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
        chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y‖ ≤ ε := by
  obtain ⟨N, hN⟩ := tensorChartComponent_allOrder_uniformCauchy
    (I := I) (M := M) g r s F hF_cauchy α P 0 (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn y => ?_⟩

  have hcauchy0 : ∀ n', N ≤ n' →
      ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
        tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2 y‖ ≤ ε / 2 := by
    intro n' hn'
    have hraw := hN n n' hn hn' y
    rwa [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp,
      Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] at hraw

  have htends :
      Tendsto (fun n' =>
        ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
          tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2 y‖)
        atTop (𝓝 ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
          chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y‖) :=
    (continuous_norm.tendsto _).comp
      (tendsto_const_nhds.sub
        (chartLimitComp_tendsto (I := I) (M := M) g r s F hF_cauchy α P y))
  have hlim_le : ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y‖ ≤ ε / 2 :=
    le_of_tendsto htends
      (Filter.eventually_atTop.mpr ⟨N, fun n' hn' => hcauchy0 n' hn'⟩)
  linarith

omit [BoundarylessManifold I M] in
private lemma chartLimitComp_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Continuous (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) := by
  have hcdOn : ContDiffOn ℝ ∞
      (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1 P
  have hO : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine continuous_of_tsupport (fun x hx => ?_)
  have hxO : x ∈ chartTargetEuclid (I := I) (M := M) α :=
    chartLimitComp_tsupport (I := I) (M := M) g r s F hF_cauchy α P hx
  exact ((hcdOn.contDiffAt (hO.mem_nhds hxO)).continuousAt)

omit [BoundarylessManifold I M] in
private lemma chartLimitComp_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) :=
  ((exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 P).1

omit [BoundarylessManifold I M] in
private lemma chartLimitComp_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    MemLp (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) 2
      (chartL2Measure (I := I) (M := M) α) := by
  haveI : IsFiniteMeasureOnCompacts (chartL2Measure (I := I) (M := M) α) := by
    rw [chartL2Measure]; infer_instance
  exact Continuous.memLp_of_hasCompactSupport
    (chartLimitComp_continuous (I := I) (M := M) g r s F hF_cauchy α P)
    (chartLimitComp_hasCompactSupport (I := I) (M := M) g r s F hF_cauchy α P)

omit [BoundarylessManifold I M] in
private lemma chartComponent_toLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Tendsto
      (fun n => (tensorChartComponent_memLp (I := I) (M := M) g r s (F n) α P.1 P.2).toLp
        (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2))
      atTop (𝓝 ((chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
        (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P))) := by
  classical
  haveI : IsFiniteMeasureOnCompacts (chartL2Measure (I := I) (M := M) α) := by
    rw [chartL2Measure]; infer_instance
  set μ : Measure EuclN := chartL2Measure (I := I) (M := M) α with hμ_def

  set K : Set EuclN := chartPouKernel (I := I) (M := M) α ∪
    tsupport (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) with hK_def
  have hK_compact : IsCompact K :=
    (chartPouKernel_isCompact (I := I) (M := M) α).union
      (chartLimitComp_hasCompactSupport (I := I) (M := M) g r s F hF_cauchy α P)
  have hμK_lt : μ K < ⊤ := by
    rw [hμ_def, chartL2Measure]
    exact lt_of_le_of_lt (Measure.restrict_apply_le _ K) hK_compact.measure_lt_top
  set c : ℝ≥0∞ := (μ K) ^ ((2 : ℝ≥0∞).toReal⁻¹) with hc_def
  have hc_lt : c < ⊤ := by
    rw [hc_def]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hμK_lt.ne

  set dseq : ℕ → EuclN → ℝ := fun n =>
    tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 -
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P with hdseq_def
  have hdsupp : ∀ n, Function.support (dseq n) ⊆ K := by
    intro n z hz
    rw [Function.mem_support] at hz
    by_contra hzK
    apply hz
    rw [hdseq_def]
    simp only [Pi.sub_apply]
    rw [hK_def, Set.mem_union, not_or] at hzK
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hzK.1
        (tensorChartComponent_tsupport_subset_chartPouKernel
          (I := I) (M := M) g r s (F n) α P.1 P.2 hmem)),
      image_eq_zero_of_notMem_tsupport hzK.2, sub_zero]

  have heLp_le : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      eLpNorm (dseq n) 2 μ ≤ c * ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := chartLimitComp_uniform (I := I) (M := M) g r s F hF_cauchy α P ε hε
    refine ⟨N, fun n hn => ?_⟩

    have hrestrict : eLpNorm (dseq n) 2 (μ.restrict K) = eLpNorm (dseq n) 2 μ :=
      eLpNorm_restrict_eq_of_support_subset (hdsupp n)
    have hbound_ae : ∀ᵐ z ∂(μ.restrict K), ‖dseq n z‖ ≤ ε := by
      filter_upwards with z
      rw [hdseq_def]
      exact hN n hn z
    have hle := eLpNorm_le_of_ae_bound (p := 2) hbound_ae
    rw [hrestrict] at hle
    refine hle.trans ?_
    rw [hc_def, Measure.restrict_apply_univ]

  have htendsto_eLp : Tendsto (fun n => eLpNorm (dseq n) 2 μ) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with hεtop | hεtop
    · obtain ⟨N, hN⟩ := heLp_le 1 one_pos
      exact ⟨N, fun n hn => hεtop ▸ le_top⟩
    rcases eq_or_lt_of_le (zero_le c) with hc0 | hc0
    · obtain ⟨N, hN⟩ := heLp_le 1 one_pos
      refine ⟨N, fun n hn => le_trans (hN n hn) ?_⟩
      rw [← hc0, zero_mul]
      exact zero_le _
    · have hc_ne : c ≠ ⊤ := hc_lt.ne
      have hdiv_ne_top : ε / c ≠ ⊤ := by
        rw [Ne, ENNReal.div_eq_top]; push Not
        exact ⟨fun _ => hc0.ne', fun h => absurd h hεtop⟩
      have hδ_pos : 0 < (ε / c).toReal :=
        ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hε.ne', hc_ne⟩) hdiv_ne_top
      obtain ⟨N, hN⟩ := heLp_le ((ε / c).toReal) hδ_pos
      refine ⟨N, fun n hn => le_trans (hN n hn) ?_⟩
      rw [ENNReal.ofReal_toReal hdiv_ne_top, ENNReal.mul_div_cancel hc0.ne' hc_ne]

  rw [tendsto_iff_edist_tendsto_0]
  have hedist_eq : ∀ n,
      edist ((tensorChartComponent_memLp (I := I) (M := M) g r s (F n) α P.1 P.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2))
        ((chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
          (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P)) =
        eLpNorm (dseq n) 2 μ := by
    intro n
    rw [Lp.edist_toLp_toLp]
  simp only [hedist_eq]
  exact htendsto_eLp

omit [BoundarylessManifold I M] in
private lemma tensorL2ChartComponent_eq_chartLimitComp_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P := by
  classical

  have h_chartEq : ∀ n,
      tensorL2ChartComponent (I := I) (M := M) g r s (F n : TensorL2 r s g) α P =
        (tensorChartComponent_memLp (I := I) (M := M) g r s (F n) α P.1 P.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2) :=
    fun n => tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g r s (F n) α P

  have h_lim_chosen :
      Tendsto (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
          (F n : TensorL2 r s g) α P)
        atTop (𝓝 ((chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
          (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P))) := by
    simp only [h_chartEq]
    exact chartComponent_toLp_tendsto (I := I) (M := M) g r s F hF_cauchy α P

  have h_lim_abstract :
      Tendsto (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
          (F n : TensorL2 r s g) α P)
        atTop (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s u α P)) := by
    have hcont := continuous_tensorL2ChartComponent (I := I) (M := M) g r s α P
    exact (hcont.tendsto u).comp hF_L2

  have h_eq :
      tensorL2ChartComponent (I := I) (M := M) g r s u α P =
        (chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
          (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) :=
    tendsto_nhds_unique h_lim_abstract h_lim_chosen
  rw [h_eq]
  exact MemLp.coeFn_toLp _

omit [BoundarylessManifold I M] in
private lemma tensorChartComponentRaw_chartLimitSection_self
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 P hy

omit [BoundarylessManifold I M] in
private lemma chartLimitSection_toSection_eq_zero_off_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α).toSection x = 0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 hx

omit [BoundarylessManifold I M] in
private lemma tensorChartComponentRaw_chartLimitSection_eq_zero_off_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        β P.1 P.2 x = 0 := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  have hsec : (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α).toSection x = 0 :=
    chartLimitSection_toSection_eq_zero_off_source (I := I) (M := M) g r s F hF_cauchy α hx
  rw [tensorChartComponentRaw_def, tensorTrivProj, hsec,
    ContinuousLinearMap.map_zero, map_zero]

open Classical in

omit [BoundarylessManifold I M] in
private lemma raw_chartLimitSection_eq_ite
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hxβ : x ∈ (chartAt H β).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        β P₀.1 P₀.2 x =
      (if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
              α Q.1 Q.2 x
        else 0) := by
  classical
  by_cases hxα : x ∈ (chartAt H α).source
  · rw [if_pos hxα]
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s
      (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
      α β P₀ ⟨hxα, hxβ⟩
  · rw [if_neg hxα]
    exact tensorChartComponentRaw_chartLimitSection_eq_zero_off_source
      (I := I) (M := M) g r s F hF_cauchy α β P₀ hxα

open Classical in

omit [BoundarylessManifold I M] in
private lemma chartLimitSection_tensorL2ChartComponent_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
                  α Q.1 Q.2 x
            else 0) y) := by
  classical
  have h_coeFn :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α) β P₀
  have h_mem : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [chartL2Measure]
    exact ae_restrict_mem (chartTargetEuclid_isOpen (I := I) (M := M) β).measurableSet
  filter_upwards [h_coeFn, h_mem] with y hy_coe hy
  rw [hy_coe]
  rw [tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s
    (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
    β P₀.1 P₀.2 hy]
  congr 1
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        β P₀.1 P₀.2) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (fun x => if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
              α Q.1 Q.2 x
        else 0) hy]
  exact raw_chartLimitSection_eq_ite (I := I) (M := M) g r s F hF_cauchy
    α β P₀ (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy)

private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f h : X → ℝ} {t : Set X} (ht : MeasurableSet t)
    (h_restrict : f =ᵐ[μ.restrict t] h)
    (h_compl : ∀ x, x ∉ t → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ t := by
    intro x hx
    by_contra hxt
    exact hx (h_compl x hxt)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ t :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact ht.nullMeasurableSet

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma transportChartCenters_subset_chartAtlasPOU_finset' (β : M) :
    transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOU_finset (I := I) (M := M) := by
  intro γ hγ
  rw [mem_transportChartCenters] at hγ
  rw [chartAtlasPOU_finset_mem]
  exact hγ.mono Set.inter_subset_left

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartPushedPouWeight_toEuclidean_extChartAt'
    (α : M) {z : M} (hz : z ∈ (chartAt H α).source) :
    chartPushedPouWeight (I := I) (M := M) α
        ((toEuclidean (E := E)) (extChartAt I α z)) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartPushedPouWeight
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) α hz]

private def chartKernelCutoffPushed' (α : M) : EuclN → ℝ :=
  chartPushedRaw (I := I) (M := M) α
    (fun x => ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoffPushed_eq_one_on_chartPouKernel'
    (α : M) {y : EuclN} (hy : y ∈ chartPouKernel (I := I) (M := M) α) :
    chartKernelCutoffPushed' (I := I) (M := M) α y = 1 := by
  classical
  rw [chartPouKernel] at hy
  obtain ⟨v, ⟨w, hw_supp, hwv⟩, hvy⟩ := hy
  have hw_srcα : w ∈ (chartAt H α).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α hw_supp
  have hw_extsrc : w ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hw_srcα
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
      ⟨v, ⟨w, hw_supp, hwv⟩, hvy⟩
  have hsymm : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = w := by
    rw [← hvy, ← hwv, (toEuclidean (E := E)).symm_apply_apply,
      (extChartAt I α).left_inv hw_extsrc]
  unfold chartKernelCutoffPushed'
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target, hsymm]
  exact chartKernelCutoff_eqOn_one (I := I) (M := M) α hw_supp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartKernelCutoffPushed_toEuclidean_extChartAt'
    (α : M) {z : M} (hz : z ∈ (chartAt H α).source) :
    chartKernelCutoffPushed' (I := I) (M := M) α
        ((toEuclidean (E := E)) (extChartAt I α z)) =
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartKernelCutoffPushed'
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) α hz]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponentU_ae_eq_chartKernelCutoffPushed_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (Q : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartKernelCutoffPushed' (I := I) (M := M) α y *
        ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  have h_off := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s u α Q
  filter_upwards [h_off] with y hy
  by_cases hk : y ∈ chartPouKernel (I := I) (M := M) α
  · rw [chartKernelCutoffPushed_eq_one_on_chartPouKernel' (I := I) (M := M) α hk,
      one_mul]
  · rw [hy hk, mul_zero]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponentU_ae_zero_where_chartPushedPouWeight_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  filter_upwards [tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s u α Q] with y hy hy_zero
  rw [show chartPushedPouWeight (I := I) (M := M) α y =
      chartPushedRaw I α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y from rfl]
    at hy_zero
  rw [hy, hy_zero, zero_mul]

open Classical in

omit [BoundarylessManifold I M] in
private lemma chartLimitSection_transport_term_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u))
    (β α : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      chartPushedRaw I β
        (fun x => if x ∈ (chartAt H α).source then
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
              α Q.1 Q.2 x
          else 0) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
  classical
  set W : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y with hW_def
  set A : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => if x ∈ (chartAt H α).source then
      transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
          α Q.1 Q.2 x
      else 0) y with hA_def
  set B : EuclN → ℝ := fun y =>
    ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y with hB_def
  set RHS : EuclN → ℝ := fun y =>
    chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
      ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
        (chartTransitionEuclid (I := I) (M := M) β α y) with hRHS_def
  have hB_eq : B =ᵐ[chartL2Measure (I := I) (M := M) β] RHS := by
    have h := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M) g r s α β
      P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s u α Q)
    exact h.trans (Filter.EventuallyEq.of_eq rfl)
  have h_goal : (fun y => W y * A y)
      =ᵐ[chartL2Measure (I := I) (M := M) β] (fun y => W y * RHS y) := by
    have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β α) :=
      chartOverlapEuclid_isOpen (I := I) (M := M) β α
    have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β α) :=
      hΩ_open.measurableSet
    have h_restrict_eq :
        (chartL2Measure (I := I) (M := M) β).restrict
          (chartOverlapEuclid (I := I) (M := M) β α) =
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β α) := by
      rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
        Set.inter_eq_left.mpr
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α)]
    have h_on_overlap : (fun y => W y * A y)
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β α)]
        (fun y => W y * RHS y) := by
      rw [h_restrict_eq]
      have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β α)),
          y ∈ chartOverlapEuclid (I := I) (M := M) β α :=
        ae_restrict_mem hΩ_meas

      have h_K_overlap :
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
            =ᵐ[(volume : Measure EuclN).restrict
                (chartOverlapEuclid (I := I) (M := M) α β)]
            chartLimitComp (I := I) (M := M) g r s F hF_cauchy α Q := by
        have h_K := tensorL2ChartComponent_eq_chartLimitComp_aeEq
          (I := I) (M := M) g r s u F hF_cauchy hF_L2 α Q
        simp only [chartL2Measure] at h_K
        exact ae_mono (Measure.restrict_mono_set _
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β)) h_K
      have h_cc := chartTransitionEuclid_comp_ae_eq_restrict
        (I := I) (M := M) β α h_K_overlap

      have h_kc_overlap :
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
            =ᵐ[(volume : Measure EuclN).restrict
                (chartOverlapEuclid (I := I) (M := M) α β)]
            (fun w => chartKernelCutoffPushed' (I := I) (M := M) α w *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) w) := by
        have h_kc := tensorL2ChartComponentU_ae_eq_chartKernelCutoffPushed_mul
          (I := I) (M := M) g r s u α Q
        simp only [chartL2Measure] at h_kc
        exact ae_mono (Measure.restrict_mono_set _
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β)) h_kc
      have h_kc := chartTransitionEuclid_comp_ae_eq_restrict
        (I := I) (M := M) β α h_kc_overlap
      filter_upwards [h_mem, h_cc, h_kc] with y hy_mem hy_cc hy_kc
      have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
        chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α hy_mem
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_srcβ : z ∈ (chartAt H β).source :=
        symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
      have hz_srcα : z ∈ (chartAt H α).source :=
        (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
          (I := I) (M := M) β α hy_target).mp hy_mem
      set zα : EuclN := (toEuclidean (E := E)) (extChartAt I α z) with hzα_def
      have hsymm_target : (toEuclidean (E := E)).symm y ∈
          (extChartAt I β).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
      have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
        rw [hz_def, (extChartAt I β).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      have hT_eq : chartTransitionEuclid (I := I) (M := M) β α y = zα := by
        rw [← hy_eq, hzα_def]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β α hz_srcβ

      have hA_y : A y =
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q z *
            chartLimitComp (I := I) (M := M) g r s F hF_cauchy α Q zα := by
        rw [hA_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, if_pos hz_srcα]
        congr 1
        have h_raw := tensorChartComponentRaw_chartLimitSection_self
          (I := I) (M := M) g r s F hF_cauchy α Q
          (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α
            hz_srcα)
        rw [symm_toEuclidean_symm_toEuclidean_extChartAt
          (I := I) (M := M) α hz_srcα] at h_raw
        rw [h_raw, hzα_def]
      set Uα : ℝ := ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) zα with hUα_def
      have hRHS_y : RHS y =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q z * Uα := by
        rw [hRHS_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hT_eq, ← hUα_def]
        ring
      rw [hT_eq] at hy_cc hy_kc

      have h_cutα_push : chartKernelCutoffPushed' (I := I) (M := M) α zα =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
        rw [hzα_def]
        exact chartKernelCutoffPushed_toEuclidean_extChartAt'
          (I := I) (M := M) α hz_srcα
      rw [h_cutα_push, ← hUα_def] at hy_kc
      rw [← hUα_def] at hy_cc

      rw [hA_y, hRHS_y, ← hy_cc]
      by_cases hWy : W y = 0
      · rw [hWy, zero_mul, zero_mul]
      · have hWy_val : W y =
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
          rw [hW_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def]
        have hz_pou : z ∈ tsupport
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          rw [hWy_val] at hWy
          exact hWy
        have h_cutβ : ((chartKernelCutoff (I := I) (M := M) β :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 1 :=
          chartKernelCutoff_eqOn_one (I := I) (M := M) β hz_pou

        rw [h_cutβ]
        have h_key : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
              M → ℝ) z * 1 *
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q z * Uα =
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q z * Uα := by
          have hcu : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
              M → ℝ) z * Uα = Uα := hy_kc.symm
          linear_combination
            (transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q z) * hcu
        rw [h_key]
    have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β α →
        W y * A y = W y * RHS y := by
      intro y hy_notin
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
      · set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
          with hz_def
        have hz_notin_srcα : z ∉ (chartAt H α).source := by
          intro hz_srcα
          exact hy_notin
            ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
              (I := I) (M := M) β α hy_target).mpr hz_srcα)
        have hA_y : A y = 0 := by
          rw [hA_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def, if_neg hz_notin_srcα]
        have hRHS_y : RHS y = 0 := by
          rw [hRHS_def]
          simp only
          have h_cutα_zero : ((chartKernelCutoff (I := I) (M := M) α :
              C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h =>
              hz_notin_srcα
                (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α h))
          have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
              (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y = 0 := by
            rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
              ← hz_def, transportCoeffManifold_apply, h_cutα_zero]
            ring
          rw [h_coeff_zero, zero_mul]
        rw [hA_y, hRHS_y]
      · have hWy : W y = 0 := by
          rw [hW_def]
          simp only
          exact chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target
        rw [hWy, zero_mul, zero_mul]
    exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap
      h_off_overlap
  refine h_goal.trans ?_
  exact (Filter.EventuallyEq.refl _ W).mul hB_eq.symm

open Classical in

omit [BoundarylessManifold I M] in
private lemma chartLimitSection_tensorL2ChartComponent_eq_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := by
  classical
  refine (chartLimitSection_tensorL2ChartComponent_coeFn_aeEq
    (I := I) (M := M) g r s F hF_cauchy α β P₀).trans ?_
  have h_push : ∀ y : EuclN,
      chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
                  α Q.1 Q.2 x
            else 0) y =
        ∑ Q : TensorCompIdx (E := E) r s,
          (chartPushedRaw I β
              (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
            chartPushedRaw I β
              (fun x => if x ∈ (chartAt H α).source then
                transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                  tensorChartComponentRaw (I := I) (M := M) g r s
                    (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
                    α Q.1 Q.2 x
              else 0) y) := by
    intro y
    have h_ite :
        (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
                  α Q.1 Q.2 x
            else 0) =
          fun x => ∑ Q : TensorCompIdx (E := E) r s,
            (if x ∈ (chartAt H α).source then
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
                  α Q.1 Q.2 x
            else 0) := by
      funext x
      by_cases hp : x ∈ (chartAt H α).source
      · simp only [if_pos hp]
      · simp only [if_neg hp, Finset.sum_const_zero]
    rw [h_ite, chartPushedRaw_finsetSum (I := I) (M := M) β
      (Finset.univ : Finset (TensorCompIdx (E := E) r s)) _ y, Finset.mul_sum]
  have h_terms : ∀ Q : TensorCompIdx (E := E) r s,
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
                α Q.1 Q.2 x
          else 0) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) :=
    fun Q => chartLimitSection_transport_term_aeEq
      (I := I) (M := M) g r s u F hF_cauchy hF_L2 β α P₀ Q
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_terms Q)
  refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq (funext h_push)) ?_
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.mul_sum]

omit [BoundarylessManifold I M] in
private lemma transportSum_u_ae_zero_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_each : ∀ Q : TensorCompIdx (E := E) r s,
      ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
    intro Q
    have h_coeFn := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M)
      g r s α β P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s u α Q)
    refine h_coeFn.trans ?_
    have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β α) :=
      chartOverlapEuclid_isOpen (I := I) (M := M) β α
    have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β α) :=
      hΩ_open.measurableSet
    have h_restrict_eq :
        (chartL2Measure (I := I) (M := M) β).restrict
          (chartOverlapEuclid (I := I) (M := M) β α) =
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β α) := by
      rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
        Set.inter_eq_left.mpr
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α)]

    have h_on_overlap :
        (fun y => chartPushedRaw (I := I) (M := M) β
            (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
            (chartTransitionEuclid (I := I) (M := M) β α y))
          =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
              (chartOverlapEuclid (I := I) (M := M) β α)]
        (fun _ : EuclN => (0 : ℝ)) := by
      rw [h_restrict_eq]

      have h_gate_target :=
        tensorL2ChartComponentU_ae_zero_where_chartPushedPouWeight_zero
          (I := I) (M := M) g r s u α Q
      have h_gate_ite :
          (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            else 0)
            =ᵐ[chartL2Measure (I := I) (M := M) α]
            (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_gate_target] with y hy
        by_cases hw : chartPushedPouWeight (I := I) (M := M) α y = 0
        · rw [if_pos hw]; exact hy hw
        · rw [if_neg hw]
      have h_gate_overlap :
          (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            else 0)
            =ᵐ[(volume : Measure EuclN).restrict
                (chartOverlapEuclid (I := I) (M := M) α β)]
            (fun _ : EuclN => (0 : ℝ)) := by
        simp only [chartL2Measure] at h_gate_ite
        exact ae_mono (Measure.restrict_mono_set _
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β))
          h_gate_ite
      have h_gate_transport := chartTransitionEuclid_comp_ae_eq_restrict
        (I := I) (M := M) β α h_gate_overlap
      have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β α)),
          y ∈ chartOverlapEuclid (I := I) (M := M) β α :=
        ae_restrict_mem hΩ_meas
      filter_upwards [h_mem, h_gate_transport] with y hy_mem hy_gate
      have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
        chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α hy_mem
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_srcβ : z ∈ (chartAt H β).source :=
        symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
      have hz_srcα : z ∈ (chartAt H α).source :=
        (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
          (I := I) (M := M) β α hy_target).mp hy_mem
      have hsymm_target : (toEuclidean (E := E)).symm y ∈
          (extChartAt I β).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
      have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
        rw [hz_def, (extChartAt I β).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      have hT_eq : chartTransitionEuclid (I := I) (M := M) β α y =
          (toEuclidean (E := E)) (extChartAt I α z) := by
        rw [← hy_eq]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β α hz_srcβ
      have h_coeff : chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y =
          transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q z := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target, ← hz_def]
      by_cases hχβ : ((chartKernelCutoff (I := I) (M := M) β :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0
      · rw [h_coeff, transportCoeffManifold_apply, hχβ]
        ring
      · have hρα : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 := by
          by_contra hρα_ne
          exact hα (mem_transportChartCenters_of_pou_cutoff_ne
            (I := I) (M := M) β α hρα_ne hχβ)
        have hw_zero : chartPushedPouWeight (I := I) (M := M) α
            (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
          rw [hT_eq, chartPushedPouWeight_toEuclidean_extChartAt'
            (I := I) (M := M) α hz_srcα, hρα]
        have hy_gate' : (if chartPushedPouWeight (I := I) (M := M) α
              (chartTransitionEuclid (I := I) (M := M) β α y) = 0 then
            ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
              (chartTransitionEuclid (I := I) (M := M) β α y)
          else 0) = 0 := hy_gate
        rw [if_pos hw_zero] at hy_gate'
        rw [hy_gate', mul_zero]
    have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β α →
        chartPushedRaw (I := I) (M := M) β
            (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
            (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
      intro y hy_notin
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
      · set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
          with hz_def
        have hz_notin_srcα : z ∉ (chartAt H α).source := by
          intro hz_srcα
          exact hy_notin
            ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
              (I := I) (M := M) β α hy_target).mpr hz_srcα)
        have hχα_zero : ((chartKernelCutoff (I := I) (M := M) α :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h =>
            hz_notin_srcα
              (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α h))
        have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
            (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y = 0 := by
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def, transportCoeffManifold_apply, hχα_zero]
          ring
        rw [h_coeff_zero, zero_mul]
      · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target,
          zero_mul]
    exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap h_off_overlap
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_each Q)
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.sum_const_zero]

omit [BoundarylessManifold I M] in
theorem globalLimitSection_toL2_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u)) :
    (globalLimitSection (I := I) (M := M) g r s F hF_cauchy : TensorL2 r s g) = u := by
  classical
  refine tensorL2_eq_of_chartComponent_eq (I := I) (M := M) g r s _ u
    (fun β P₀ => ?_)
  apply Lp.ext

  have h_coe_sum :
      (globalLimitSection (I := I) (M := M) g r s F hF_cauchy : TensorL2 r s g) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α :
            TensorL2 r s g) := by
    rw [globalLimitSection, ← smoothToTensorL2_apply (I := I) (M := M) g r s,
      map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [smoothToTensorL2_apply]
  have h_lhs_sum :
      tensorL2ChartComponent (I := I) (M := M) g r s
          (globalLimitSection (I := I) (M := M) g r s F hF_cauchy :
            TensorL2 r s g) β P₀ =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          tensorL2ChartComponent (I := I) (M := M) g r s
            (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α :
              TensorL2 r s g) β P₀ := by
    rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s β P₀,
      h_coe_sum, map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [tensorL2ChartComponentCLM_apply]
  rw [h_lhs_sum]
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) β
    (chartAtlasPOU_finset (I := I) (M := M))
    (fun α => tensorL2ChartComponent (I := I) (M := M) g r s
      (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α :
        TensorL2 r s g) β P₀)).trans ?_

  have h_lhs_terms :
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α :
              TensorL2 r s g) β P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartPushedRaw I β
            (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)) :=
    finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M))
      (fun α _ => chartLimitSection_tensorL2ChartComponent_eq_transport_sum
        (I := I) (M := M) g r s u F hF_cauchy hF_L2 α β P₀)
  refine h_lhs_terms.trans ?_

  refine Filter.EventuallyEq.symm
    ((tensorL2ChartComponent_ae_eq_pou_transport_sum (I := I) (M := M)
      g r s u β P₀).trans ?_)
  have h_subset : transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOU_finset (I := I) (M := M) :=
    transportChartCenters_subset_chartAtlasPOU_finset' (I := I) (M := M) β
  set G : M → EuclN → ℝ := fun α y =>
    chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y
    with hG_def
  have h_rhs_eq :
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ γ ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s u γ Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y) =
        fun y => ∑ γ ∈ transportChartCenters (I := I) (M := M) β, G γ y := by
    funext y
    rw [Finset.mul_sum]
  rw [h_rhs_eq]
  have h_union : chartAtlasPOU_finset (I := I) (M := M) =
      transportChartCenters (I := I) (M := M) β ∪
        (chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β) :=
    (Finset.union_sdiff_of_subset h_subset).symm
  have h_disjoint : Disjoint (transportChartCenters (I := I) (M := M) β)
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β) :=
    Finset.disjoint_sdiff
  have h_split : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        G α y) =
      fun y => (∑ γ ∈ transportChartCenters (I := I) (M := M) β, G γ y) +
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
            transportChartCenters (I := I) (M := M) β, G α y := by
    funext y
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disjoint]
  rw [h_split]
  have h_extra : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β, G α y)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
    have h_each : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β,
        G α =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
      intro α hα
      have hα_notin : α ∉ transportChartCenters (I := I) (M := M) β :=
        (Finset.mem_sdiff.mp hα).2
      have h_zero := transportSum_u_ae_zero_of_notMem
        (I := I) (M := M) g r s u α β P₀ hα_notin
      filter_upwards [h_zero] with y hy
      rw [hG_def]
      change chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s u α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y =
        (0 : ℝ)
      rw [hy, mul_zero]
    have h_sum := finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β)
      (fun α hα => h_each α hα)
    refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
    funext y
    rw [Finset.sum_const_zero]
  filter_upwards [h_extra] with y hy
  rw [show (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β, G α y) = 0 from hy,
    add_zero]

omit [BoundarylessManifold I M] in
theorem smoothCcTensor_limit_of_allOrders_toHs_cauchy
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u)) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u :=
  ⟨globalLimitSection (I := I) (M := M) g r s F hF_cauchy,
    globalLimitSection_toL2_eq (I := I) (M := M) g r s u F hF_cauchy hF_L2⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
