import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.EigenvectorCutoffChartPartialL2


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentEuclid_contDiff_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M)
    (cutoffComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_hasCompactSupport_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_tsupport_subset_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentEuclid_memLp_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemLp (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have h_vol : MemLp (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) 2
      (volume : Measure EuclN) :=
    (cutoffComponentEuclid_contDiff_section (I := I) (M := M)
      g r s S α Idx Jdx).continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure EuclN))
      (cutoffComponentEuclid_hasCompactSupport_section (I := I) (M := M)
        g r s S α Idx Jdx)
  rw [chartL2Measure]
  exact h_vol.restrict _

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenWeakPartial'_cutoffComponentEuclid_section_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    cutoffComponentEuclid_contDiff_section (I := I) (M := M) g r s S α Idx Jdx
  have hu_cpt : HasCompactSupport u :=
    cutoffComponentEuclid_hasCompactSupport_section (I := I) (M := M)
      g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    cutoffComponentEuclid_tsupport_subset_section (I := I) (M := M)
      g r s S α Idx Jdx
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : MemWkp (d := Module.finrank ℝ E) 1 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      hu_smooth hu_cpt hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := Module.finrank ℝ E)
    hp_one hΩ_open hu_smooth hu_W1p k
  rw [chartL2Measure]
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y; rw [euclidPartial_def]

noncomputable def crossRightTestGradTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
            cutoffComponentEuclid (I := I) (M := M) g r s S α P.1 P.2 y *
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y

def crossRightDivFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
      crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma crossRightDivFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((densityOnEuclid_contDiffOn (I := I) g α).mul
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q)).mul
    (crossRightTestGradCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q l)

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_crossRightDivFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q))
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_target (I := I) (M := M) α l
    (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma chartPushedRaw_pou_eq_zero_off_chartPouKernel
    (α : M) {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y = 0 := by
  classical
  by_cases htar : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ htar]
    have hb : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
        tsupport
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
      intro hsupp
      apply hy
      refine ⟨(toEuclidean (E := E)).symm y, ⟨_, hsupp, ?_⟩, ?_⟩
      · have hmem : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
          DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
            (I := I) (M := M) htar
        exact (extChartAt I α).right_inv hmem
      · exact toEuclidean.apply_symm_apply y
    have hb_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
        Function.support
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      fun hc => hb (subset_tsupport _ hc)
    by_contra hc
    exact hb_supp hc
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ htar]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma euclidPartial_chartPushedRaw_pou_eq_zero_off_chartPouKernel
    (α : M) (j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    euclidPartial (E := E) j
        (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y =
      0 := by
  classical
  have hsupp : Function.support
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (chartPushedRaw_pou_eq_zero_off_chartPouKernel (I := I) (M := M) α hzk)
  have htsupp : tsupport
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
      chartPouKernel (I := I) (M := M) α :=
    closure_minimal hsupp
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
  have hy_compl : y ∈ (tsupport
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ :=
    fun hc => hy (htsupp hc)
  have hopen : IsOpen (tsupport
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have hevt :
      chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy_compl) (fun z hz => ?_)
    exact image_eq_zero_of_notMem_tsupport hz
  rw [euclidPartial_def, hevt.fderiv_eq]
  simp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma crossRightTestGradCoeff_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y = 0 := by
  classical
  rw [crossRightTestGradCoeff_def, gradChartCoeffEuclid]
  rw [Finset.sum_eq_zero (fun j _ => ?_), zero_mul]
  rw [euclidPartial_chartPushedRaw_pou_eq_zero_off_chartPouKernel
    (I := I) (M := M) α j hy, mul_zero]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma crossRightDivFactor_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y = 0 := by
  rw [crossRightDivFactor,
    crossRightTestGradCoeff_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s α P₀ Q l hy, mul_zero]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    euclidPartial (E := E) l
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y = 0 := by
  classical
  have hsupp : Function.support
      (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (crossRightDivFactor_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s α P₀ l P Q hzk)
  have htsupp : tsupport
      (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) ⊆
      chartPouKernel (I := I) (M := M) α :=
    closure_minimal hsupp
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
  have hy_compl : y ∈ (tsupport
      (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q))ᶜ :=
    fun hc => hy (htsupp hc)
  have hopen : IsOpen (tsupport
      (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have hevt : crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q
      =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy_compl) (fun z hz => ?_)
    exact image_eq_zero_of_notMem_tsupport hz
  rw [euclidPartial_def, hevt.fderiv_eq]
  simp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma densityOnEuclid_mul_crossRightTestGradTerm_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    (fun y => densityOnEuclid (I := I) g α y *
        crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y) =
      fun y =>
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
              cutoffComponentEuclid (I := I) (M := M) g r s S α P.1 P.2 y := by
  classical
  funext y
  rw [crossRightTestGradTerm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [crossRightDivFactor]
  ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y => densityOnEuclid (I := I) g α y *
        crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  rw [densityOnEuclid_mul_crossRightTestGradTerm_eq (I := I) (M := M)
    g r s S α P₀ l]
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  exact (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q).mul
    ((cutoffComponentEuclid_contDiff_section (I := I) (M := M)
      g r s S α P.1 P.2).contDiffOn)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma integrable_euclidPartial_crossRightTestGradTerm_mul_test
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable
      (fun y => euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y * φ y)
      (volume : Measure EuclN) := by
  classical
  have hcontDiff : ContDiff ℝ ∞
      (fun y => euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
        φ y) :=
    contDiff_partial_coeff_mul_test (I := I) (M := M) α l
      (densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn
        (I := I) (M := M) g r s S α P₀ l)
      hφ.contDiffOn hφ_supp
  have hsupp : HasCompactSupport
      (fun y => euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
        φ y) :=
    hasCompactSupport_partial_coeff_mul_test (E := E) l hφ_cs
  exact hcontDiff.continuous.integrable_of_hasCompactSupport hsupp

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem crossRightTestGradTerm_byParts
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y *
            euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      -∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y) *
          φ y ∂(volume : Measure EuclN) := by
  classical
  have hIBP : ∀ l : Fin (Module.finrank ℝ E),
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y *
            euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
        -∫ y in chartTargetEuclid (I := I) (M := M) α,
          euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
            φ y ∂(volume : Measure EuclN) := by
    intro l
    have hbyParts := chartTarget_integral_byParts (I := I) (M := M) α l
      (densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn
        (I := I) (M := M) g r s S α P₀ l)
      hφ.contDiffOn hφ_cs hφ_supp
    rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume
      (E := E)] at hbyParts
    exact hbyParts
  rw [Finset.sum_congr rfl (fun l _ => hIBP l), Finset.sum_neg_distrib]
  congr 1
  have hsum_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ l : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) l
                (fun z => densityOnEuclid (I := I) g α z *
                  crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y) *
            φ y ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ l : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) l
                  (fun z => densityOnEuclid (I := I) g α z *
                    crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
                φ y) ∂(volume : Measure EuclN) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    simp only [Finset.sum_mul]
  rw [hsum_eq, MeasureTheory.integral_finset_sum _ (fun l _ =>
    (integrable_euclidPartial_crossRightTestGradTerm_mul_test
      (I := I) (M := M) g r s S α P₀ l hφ hφ_cs hφ_supp).restrict)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma differentiableAt_cutoffComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN) :
    DifferentiableAt ℝ
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) y :=
  ((cutoffComponentEuclid_contDiff_section (I := I) (M := M)
    g r s S α Idx Jdx).differentiable (by norm_num)).differentiableAt

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tendsto_sum3
    (α : M) {κ₁ κ₂ κ₃ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    {f : κ₁ → κ₂ → κ₃ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (n : ℕ),
      MemLp (f a b c n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃),
      MemLp (flim a b c) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃),
      Filter.Tendsto (fun n => (hf a b c n).toLp (f a b c n)) atTop
        (𝓝 ((hflim a b c).toLp (flim a b c)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => hf a b c n)))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, f a b c n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => hflim a b c)))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, flim a b c y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, f a b c n y)
    (flim := fun a => fun y => ∑ b, ∑ c, flim a b c y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ (fun c _ => hf a b c n)))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ (fun c _ => hflim a b c)))
    (fun a => tendsto_sumToLp (I := I) (M := M) α
      (f := fun b => fun n y => ∑ c, f a b c n y)
      (flim := fun b => fun y => ∑ c, flim a b c y)
      (fun b n => memLp_finset_sum Finset.univ (fun c _ => hf a b c n))
      (fun b => memLp_finset_sum Finset.univ (fun c _ => hflim a b c))
      (fun b => tendsto_sumToLp (I := I) (M := M) α
        (hf := fun c n => hf a b c n) (hflim := fun c => hflim a b c)
        (h_tendsto a b)))

def cutoffPartialLpLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  i.fst.val •
    eigenvectorCutoffChartPartialLp (I := I) (M := M)
      g r s i α P k

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma memLp_indicatorFactor_mul_cutoffLp
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (w : EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc) (Lp.memLp w)

noncomputable def crossRightGradCoeffDivLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (∑ l : Fin (Module.finrank ℝ E),
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)) y *
              (crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                EuclN → ℝ) y)
      + ∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                  EuclN → ℝ) y

omit [CompleteSpace E] in
theorem crossRightGradCoeffDivLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold crossRightGradCoeffDivLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
            (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q)
            (crossRightLimitComponent (I := I) (M := M)
              g r s i α P))))
  · exact memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
            (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
            (cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P l))))

omit [CompleteSpace E] in
private lemma memLp_factor_mul_cutoffComponentAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hc_zero : ∀ y ∉ chartPouKernel (I := I) (M := M) α, c y = 0) :
    MemLp
      (fun y => c y *
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2 y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, hc_zero y hker]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (cutoffComponentEuclid_memLp_section (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2)

omit [CompleteSpace E] in
private lemma euclidPartial_cutoffComponentEuclid_approx_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2)) 2
      (chartL2Measure (I := I) (M := M) α) :=
  MemLp.ae_eq
    (chosenWeakPartial'_cutoffComponentEuclid_section_ae_eq (I := I) (M := M)
      g r s (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2 k)
    (chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      α P.1 P.2 k)

omit [CompleteSpace E] in
private lemma memLp_factor_mul_cutoffPartialAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hc_zero : ∀ y ∉ chartPouKernel (I := I) (M := M) α, c y = 0) :
    MemLp
      (fun y => c y *
        euclidPartial (E := E) k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        euclidPartial (E := E) k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          euclidPartial (E := E) k
            (cutoffComponentEuclid (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P.1 P.2) y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, hc_zero y hker]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (euclidPartial_cutoffComponentEuclid_approx_memLp (I := I) (M := M)
      g r s i α P k n)

omit [CompleteSpace E] in
private lemma euclidPartial_densityOnEuclid_mul_crossRightTestGradTerm_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) l
        (fun z => densityOnEuclid (I := I) g α z *
          crossRightTestGradTerm (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀ l z) y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              cutoffComponentEuclid (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α P.1 P.2 y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
                euclidPartial (E := E) l
                  (cutoffComponentEuclid (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α P.1 P.2) y := by
  classical
  set wₙ : SmoothCcTensor g r s :=
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    with hwₙ_def
  set Sum2 : EuclN → ℝ := fun z =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q z *
          cutoffComponentEuclid (I := I) (M := M) g r s wₙ α P.1 P.2 z
    with hSum2_def
  have hcoeff_evt :
      (fun z => densityOnEuclid (I := I) g α z *
        crossRightTestGradTerm (I := I) (M := M) g r s wₙ α P₀ l z)
        =ᶠ[𝓝 y] Sum2 := by
    have h_eq := densityOnEuclid_mul_crossRightTestGradTerm_eq
      (I := I) (M := M) g r s wₙ α P₀ l
    rw [hSum2_def]
    rw [h_eq]
  rw [euclidPartial_def, hcoeff_evt.fderiv_eq, ← euclidPartial_def]
  have hleaf_diff : ∀ P Q : TensorCompIdx (E := E) r s,
      DifferentiableAt ℝ
        (fun z => crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q z *
          cutoffComponentEuclid (I := I) (M := M) g r s wₙ α P.1 P.2 z) y :=
    fun P Q =>
      (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
        hy).mul
      (differentiableAt_cutoffComponentEuclid (I := I) (M := M) g r s wₙ α
        P.1 P.2 y)
  rw [hSum2_def, euclidPartial_finsetSum (E := E) l Finset.univ
    (fun P _ => DifferentiableAt.fun_sum (fun Q _ => hleaf_diff P Q))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun Q _ => hleaf_diff P Q)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  exact euclidPartial_mul (E := E) l
    (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q) hy)
    (differentiableAt_cutoffComponentEuclid (I := I) (M := M) g r s wₙ α
      P.1 P.2 y)

omit [CompleteSpace E] in
private lemma tendsto_cutoffComponentSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hc_zero : ∀ y ∉ chartPouKernel (I := I) (M := M) α, c y = 0)
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (crossRightLimitComponent (I := I) (M := M) g r s i α P :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  have hc_eq_ci : ∀ y : EuclN, c y = ci y := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]
    · rw [hci_def, Set.indicator_of_notMem hy, hc_zero y hy]
  have h_cut_tendsto :=
    crossRightComponent_tendsto (I := I) (M := M) g r s i α P
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    h_cut_tendsto
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g) α P))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    have hcomp : (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g) α P : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 :=
      tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P
    filter_upwards [hcomp] with y hy
    rw [hy, hc_eq_ci y]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (crossRightLimitComponent (I := I) (M := M)
          g r s i α P))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g) α P))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

omit [CompleteSpace E] in
private lemma tendsto_cutoffPartialSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hc_zero : ∀ y ∉ chartPouKernel (I := I) (M := M) α, c y = 0)
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        euclidPartial (E := E) k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (cutoffPartialLpLimit (I := I) (M := M) g r s i α P k :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  have hc_eq_ci : ∀ y : EuclN, c y = ci y := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]
    · rw [hci_def, Set.indicator_of_notMem hy, hc_zero y hy]
  have h_part_tendsto :
      Filter.Tendsto
        (fun n => (chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
          g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P.1 P.2 k).toLp _)
        atTop
        (𝓝 (cutoffPartialLpLimit (I := I) (M := M)
          g r s i α P k)) := by
    have h_tendsto :=
      (eigenvectorCutoffChartPartialLp_tendsto (I := I) (M := M)
        g r s i α P k).const_smul i.fst.val
    have h_term : ∀ n : ℕ,
        i.fst.val •
          ((i.fst.val)⁻¹ •
            eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k
              (smoothToTensorH1Compl (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n))) =
          (chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
            g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
            α P.1 P.2 k).toLp _ := by
      intro n
      rw [eigenvectorCutoffChartPartialLp_approx_eq (I := I) (M := M)
        g r s i α P k n, smul_smul, mul_inv_cancel₀ i.fst.val_ne_zero, one_smul]
    rw [show (fun n => (chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
          g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P.1 P.2 k).toLp _) =
        (fun n => i.fst.val •
          ((i.fst.val)⁻¹ •
            eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k
              (smoothToTensorH1Compl (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n))))
        from funext (fun n => (h_term n).symm)]
    exact h_tendsto
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    h_part_tendsto
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp ((chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
          g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P.1 P.2 k).toLp _))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    have hpart : (((chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
        g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
        α P.1 P.2 k).toLp _ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        euclidPartial (E := E) k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) := by
      refine (MemLp.coeFn_toLp _).trans ?_
      exact chosenWeakPartial'_cutoffComponentEuclid_section_ae_eq (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P.1 P.2 k
    filter_upwards [hpart] with y hy
    rw [hy, hc_eq_ci y]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (cutoffPartialLpLimit (I := I) (M := M)
          g r s i α P k))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp ((chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
          g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P.1 P.2 k).toLp _))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

omit [CompleteSpace E] in
theorem crossRightGradCoeffDivSum_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀ l z) y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcomp : MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              cutoffComponentEuclid (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α P.1 P.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_factor_mul_cutoffComponentAtom
            (I := I) (M := M) g r s i α P n
            (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q)
            (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
              (I := I) (M := M) g r s α P₀ l P Q hy))))
  have hpart : MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
              euclidPartial (E := E) l
                (cutoffComponentEuclid (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_factor_mul_cutoffPartialAtom
            (I := I) (M := M) g r s i α P l n
            (crossRightDivFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q)
            (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
              (I := I) (M := M) g r s α P₀ l P Q hy))))
  refine (hcomp.add hpart).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  simp only [Pi.add_apply]
  rw [Finset.sum_congr rfl (fun l _ =>
    euclidPartial_densityOnEuclid_mul_crossRightTestGradTerm_eqOn
      (I := I) (M := M) g r s i α P₀ l n hy),
    Finset.sum_add_distrib]

omit [CompleteSpace E] in
theorem crossRightGradCoeffDivSum_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (crossRightGradCoeffDivSum_memLp (I := I) (M := M)
        g r s i α P₀ n).toLp _)
      atTop
      (𝓝 ((crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _)) := by
  classical
  have h_comp := tendsto_sum3 (I := I) (M := M) α
    (f := fun l P Q n y =>
      euclidPartial (E := E) l
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y)
    (flim := fun l P Q y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)) y *
        (crossRightLimitComponent (I := I) (M := M) g r s i α P :
          EuclN → ℝ) y)
    (fun l P Q n => memLp_factor_mul_cutoffComponentAtom (I := I) (M := M)
      g r s i α P n
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ l P Q hy))
    (fun l P Q => memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q)
      (crossRightLimitComponent (I := I) (M := M) g r s i α P))
    (fun l P Q => tendsto_cutoffComponentSummand (I := I) (M := M)
      g r s i α P
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ l P Q hy)
      (fun n => memLp_factor_mul_cutoffComponentAtom (I := I) (M := M)
        g r s i α P n
        (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q)
        (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ l P Q hy))
      (memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
        (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q)
        (crossRightLimitComponent (I := I) (M := M) g r s i α P)))
  have h_part := tendsto_sum3 (I := I) (M := M) α
    (f := fun l P Q n y =>
      crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
        euclidPartial (E := E) l
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y)
    (flim := fun l P Q y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
        (cutoffPartialLpLimit (I := I) (M := M) g r s i α P l :
          EuclN → ℝ) y)
    (fun l P Q n => memLp_factor_mul_cutoffPartialAtom (I := I) (M := M)
      g r s i α P l n
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ l P Q hy))
    (fun l P Q => memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
      (cutoffPartialLpLimit (I := I) (M := M) g r s i α P l))
    (fun l P Q => tendsto_cutoffPartialSummand (I := I) (M := M)
      g r s i α P l
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ l P Q hy)
      (fun n => memLp_factor_mul_cutoffPartialAtom (I := I) (M := M)
        g r s i α P l n
        (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
        (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ l P Q hy))
      (memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
        (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
        (cutoffPartialLpLimit (I := I) (M := M) g r s i α P l)))
  have h_add := h_comp.add h_part
  have h_termN : ∀ n : ℕ,
      (crossRightGradCoeffDivSum_memLp (I := I) (M := M)
        g r s i α P₀ n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_cutoffComponentAtom
                (I := I) (M := M) g r s i α P n
                (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (fun y hy =>
                  euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
                    (I := I) (M := M) g r s α P₀ l P Q hy))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_cutoffPartialAtom
                (I := I) (M := M) g r s i α P l n
                (crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
                  (I := I) (M := M) g r s α P₀ l P Q hy))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    simp only []
    rw [Finset.sum_congr rfl (fun l _ =>
      euclidPartial_densityOnEuclid_mul_crossRightTestGradTerm_eqOn
        (I := I) (M := M) g r s i α P₀ l n hy),
      Finset.sum_add_distrib]
  have h_termLim :
      (crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
                (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (crossRightLimitComponent (I := I) (M := M)
                  g r s i α P))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_indicatorFactor_mul_cutoffLp (I := I) (M := M) α
                (crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [crossRightGradCoeffDivLimit]
  rw [show (fun n => (crossRightGradCoeffDivSum_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_cutoffComponentAtom
                (I := I) (M := M) g r s i α P n
                (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (fun y hy =>
                  euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
                    (I := I) (M := M) g r s α P₀ l P Q hy))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_cutoffPartialAtom
                (I := I) (M := M) g r s i α P l n
                (crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
                  (I := I) (M := M) g r s α P₀ l P Q hy))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) :
    EuclN → ℝ :=
  crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l

example (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y *
            euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      -∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y) *
          φ y ∂(volume : Measure EuclN) :=
  crossRightTestGradTerm_byParts (I := I) (M := M) g r s S α P₀ hφ hφ_cs hφ_supp

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
