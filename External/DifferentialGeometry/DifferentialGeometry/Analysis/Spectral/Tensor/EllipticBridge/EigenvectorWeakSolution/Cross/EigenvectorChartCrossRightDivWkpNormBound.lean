import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter
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
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen

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

section OffKernelCoefBound


omit [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma wkpNorm_offKernelSmoothCoef_mul_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hcoef_zero_off : ∀ y : EuclN, y ∉ Kkern → coef y = 0)
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_supp : Function.support coef ⊆ Kkern := by
    intro z hz
    by_contra hzk
    exact hz (hcoef_zero_off z hzk)
  have h_tsupp : tsupport coef ⊆ Kkern :=
    closure_minimal h_supp hKkern_compact.isClosed
  have h_tsupp_Ω : tsupport coef ⊆ Ω := h_tsupp.trans hKkern_in
  have hcoef_smooth : ContDiff ℝ (⊤ : ℕ∞) coef := by
    have h_open_compl : IsOpen ((tsupport coef)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport coef
    · have hy_chart : y ∈ Ω := h_tsupp_Ω hy_supp
      exact (hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart)
    · have h_eq_zero : coef =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hcoef_cs : HasCompactSupport coef :=
    HasCompactSupport.of_support_subset_isCompact hKkern_compact h_supp
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hcoef_smooth hcoef_cs K
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hcoef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  refine ⟨h_memWkp, ?_⟩
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hcoef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  exact ⟨Kc, le_of_lt hKc_pos, hKc_bd hfactor_memWkp⟩

end OffKernelCoefBound

section MemWkpFinsetSum


omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_finset_sum_iota
    {k : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    {ι : Type*} (S : Finset ι) (f : ι → EuclN → ℝ)
    (hf : ∀ j ∈ S, MemWkp (d := Module.finrank ℝ E) k 2 (f j) Ω) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => ∑ j ∈ S, f j y) Ω := by
  classical
  induction S using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
  | insert a t ha iht =>
      have h_split : (fun y => ∑ j ∈ insert a t, f j y) =
          (fun y => f a y + ∑ j ∈ t, f j y) := by
        funext y; rw [Finset.sum_insert ha]
      rw [h_split]
      refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ
        (hf a (Finset.mem_insert_self a t)) ?_
      exact iht (fun j hj => hf j (Finset.mem_insert_of_mem hj))

end MemWkpFinsetSum

section UniformConstant


omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_uniform_wkpNorm_bound
    {ι : Type*} [Finite ι] {K : ℕ}
    {Ω : Set EuclN} {f : ι → EuclN → ℝ} {a : ι → ℝ≥0∞}
    (h : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (f j) Ω ≤ ENNReal.ofReal C * a j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j : ι,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (f j) Ω ≤ ENNReal.ofReal C * a j := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose Cf hCf_nn hCf using h
  refine ⟨∑ j : ι, Cf j, Finset.sum_nonneg (fun j _ => hCf_nn j), fun j => ?_⟩
  refine (hCf j).trans (mul_le_mul_left ?_ (a j))
  exact ENNReal.ofReal_le_ofReal
    (Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j))

end UniformConstant

section OffKernelCoefBoundUniform


omit [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma wkpNorm_offKernelSmoothCoef_mul_le_uniform
    (α : M) (K : ℕ)
    {coef : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hcoef_zero_off : ∀ y : EuclN, y ∉ Kkern → coef y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ,
        MemWkp (d := Module.finrank ℝ E) K 2 factor
            (chartTargetEuclid (I := I) (M := M) α) →
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => coef y * factor y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
                (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_supp : Function.support coef ⊆ Kkern := by
    intro z hz
    by_contra hzk
    exact hz (hcoef_zero_off z hzk)
  have h_tsupp : tsupport coef ⊆ Kkern :=
    closure_minimal h_supp hKkern_compact.isClosed
  have h_tsupp_Ω : tsupport coef ⊆ Ω := h_tsupp.trans hKkern_in
  have hcoef_smooth : ContDiff ℝ (⊤ : ℕ∞) coef := by
    have h_open_compl : IsOpen ((tsupport coef)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport coef
    · have hy_chart : y ∈ Ω := h_tsupp_Ω hy_supp
      exact (hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart)
    · have h_eq_zero : coef =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hcoef_cs : HasCompactSupport coef :=
    HasCompactSupport.of_support_subset_isCompact hKkern_compact h_supp
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hcoef_smooth hcoef_cs K
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hcoef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  exact ⟨Kc, le_of_lt hKc_pos, fun factor hfactor => hKc_bd hfactor⟩

end OffKernelCoefBoundUniform

section MainBoundUnconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem wkpNorm_crossRightGradCoeffDivLimit_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ((∑ P : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                ((crossRightLimitComponent (I := I) (M := M)
                    g r s i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ l : Fin (Module.finrank ℝ E),
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s i α P l :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ)
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hKα_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  set Acomp : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => ((crossRightLimitComponent (I := I) (M := M)
      g r s i α P :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hAcomp_def
  set Apart : TensorCompIdx (E := E) r s → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun P l => ((cutoffPartialLpLimit (I := I) (M := M)
      g r s i α P l :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hApart_def
  set Sumcomp : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω with hSumcomp_def
  set Sumpart : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ l : Fin (Module.finrank ℝ E),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω with hSumpart_def
  have hAcomp_memWkp : ∀ P : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (Acomp P) Ω := by
    intro P
    rw [hAcomp_def, hΩ_def]
    exact crossRightLimitComponent_memWkp (I := I) (M := M)
      g r s i α P K h_pou
  have hApart_memWkp : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Apart P l) Ω := by
    intro P l
    rw [hApart_def, hΩ_def]
    exact cutoffPartialLpLimit_memWkp (I := I) (M := M)
      g r s i α P l K h_pou
  set ι : Type _ :=
    Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s with hι_def
  set summandComp : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2)) y *
      Acomp j.2.1 y with hsummandComp_def
  set summandPart : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2) y *
      Apart j.2.1 j.1 y with hsummandPart_def
  have hsummandComp_eq : ∀ j : ι, summandComp j =
      (fun y => euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M)
            g r s α P₀ j.1 j.2.1 j.2.2) y * Acomp j.2.1 y) := by
    intro j
    funext y
    simp only [hsummandComp_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  have hsummandPart_eq : ∀ j : ι, summandPart j =
      (fun y => crossRightDivFactor (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2 y * Apart j.2.1 j.1 y) := by
    intro j
    funext y
    simp only [hsummandPart_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  have hsummandComp_data : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
            ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Acomp j.2.1) Ω := by
    intro j
    rw [hsummandComp_eq j, hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (hAcomp_memWkp j.2.1)
  have hsummandPart_data : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
            ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 j.1) Ω := by
    intro j
    rw [hsummandPart_eq j, hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (hApart_memWkp j.2.1 j.1)
  have hsummandComp_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandComp j) Ω :=
    fun j => (hsummandComp_data j).1
  have hsummandPart_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandPart j) Ω :=
    fun j => (hsummandPart_data j).1
  obtain ⟨Ccomp, hCcomp_nn, hCcomp⟩ :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ι,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
            ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Acomp j.2.1) Ω :=
    exists_uniform_wkpNorm_bound (fun j => (hsummandComp_data j).2)
  obtain ⟨Cpart, hCpart_nn, hCpart⟩ :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ι,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
            ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 j.1) Ω :=
    exists_uniform_wkpNorm_bound (fun j => (hsummandPart_data j).2)
  have h_funcA : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (crossRightDivFactor (I := I) (M := M)
                      g r s α P₀ l P Q)) y *
                (crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandComp j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_funcB : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q) y *
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandPart j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have hsumComp_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandComp j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandComp
      (fun j _ => hsummandComp_memWkp j)
  have hsumPart_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandPart j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandPart
      (fun j _ => hsummandPart_memWkp j)
  have h_triangle :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀) Ω
        ≤ (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) := by
    have h_split : crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ =
        (fun y => (∑ j : ι, summandComp j y) + (∑ j : ι, summandPart j y)) := by
      funext y
      unfold crossRightGradCoeffDivLimit
      rw [h_funcA y, h_funcB y]
    rw [h_split]
    refine le_trans
      (wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hsumComp_memWkp hsumPart_memWkp) (add_le_add ?_ ?_)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandComp
        (fun j _ => hsummandComp_memWkp j)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandPart
        (fun j _ => hsummandPart_memWkp j)
  have h_groupA :
      (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp := by
    have h_each : ∀ j : ι,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
          ENNReal.ofReal Ccomp * Sumcomp := by
      intro j
      refine (hCcomp j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Ccomp))
      rw [hSumcomp_def]
      exact Finset.single_le_sum
        (f := fun P => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω)
        (fun P _ => zero_le _) (Finset.mem_univ j.2.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have h_groupB :
      (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart := by
    have h_each : ∀ j : ι,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
          ENNReal.ofReal Cpart * Sumpart := by
      intro j
      refine (hCpart j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Cpart))
      rw [hSumpart_def]
      refine le_trans ?_
        (Finset.single_le_sum
          (f := fun P => ∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω)
          (fun P _ => zero_le _) (Finset.mem_univ j.2.1))
      exact Finset.single_le_sum
        (f := fun l => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 l) Ω)
        (fun l _ => zero_le _) (Finset.mem_univ j.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  refine ⟨max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart),
    le_max_of_le_left (by positivity), ?_⟩
  have hCcomp_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hCpart_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀) Ω
        ≤ (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) :=
        h_triangle
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp
          + ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart :=
        add_le_add h_groupA h_groupB
    _ ≤ ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * Sumcomp
          + ENNReal.ofReal
              (max ((Fintype.card ι : ℝ) * Ccomp)
                ((Fintype.card ι : ℝ) * Cpart)) * Sumpart :=
        add_le_add (mul_le_mul_left hCcomp_le _)
          (mul_le_mul_left hCpart_le _)
    _ = ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * (Sumcomp + Sumpart) :=
        (mul_add _ _ _).symm

end MainBoundUnconditional

section MainBoundUniformUnconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem wkpNorm_crossRightGradCoeffDivLimit_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  ((crossRightLimitComponent (I := I) (M := M)
                      g r s i α P :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                      ((cutoffPartialLpLimit (I := I) (M := M)
                          g r s i α P l :
                          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                          EuclN → ℝ)
                      (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hKα_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  set ι : Type _ :=
    Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s with hι_def
  have hCcomp_data : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ, MemWkp (d := Module.finrank ℝ E) K 2 factor Ω →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => euclidPartial (E := E) j.1
                (crossRightDivFactor (I := I) (M := M)
                  g r s α P₀ j.1 j.2.1 j.2.2) y * factor y) Ω
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor Ω := by
    intro j
    rw [hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le_uniform (I := I) (M := M) α K
      hKα_compact hKα_in
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
  have hCpart_data : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ, MemWkp (d := Module.finrank ℝ E) K 2 factor Ω →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => crossRightDivFactor (I := I) (M := M)
                g r s α P₀ j.1 j.2.1 j.2.2 y * factor y) Ω
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor Ω := by
    intro j
    rw [hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le_uniform (I := I) (M := M) α K
      hKα_compact hKα_in
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
  choose Ccompf hCcompf_nn hCcompf using hCcomp_data
  choose Cpartf hCpartf_nn hCpartf using hCpart_data
  set Ccomp : ℝ := ∑ j : ι, Ccompf j with hCcomp_def
  set Cpart : ℝ := ∑ j : ι, Cpartf j with hCpart_def
  have hCcomp_nn : 0 ≤ Ccomp :=
    Finset.sum_nonneg (fun j _ => hCcompf_nn j)
  have hCpart_nn : 0 ≤ Cpart :=
    Finset.sum_nonneg (fun j _ => hCpartf_nn j)
  have hCcompf_le : ∀ j : ι, Ccompf j ≤ Ccomp := fun j =>
    Finset.single_le_sum (fun k _ => hCcompf_nn k) (Finset.mem_univ j)
  have hCpartf_le : ∀ j : ι, Cpartf j ≤ Cpart := fun j =>
    Finset.single_le_sum (fun k _ => hCpartf_nn k) (Finset.mem_univ j)
  refine ⟨max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart),
    le_max_of_le_left (by positivity), fun i => ?_⟩
  set Acomp : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => ((crossRightLimitComponent (I := I) (M := M)
      g r s i α P :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hAcomp_def
  set Apart : TensorCompIdx (E := E) r s → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun P l => ((cutoffPartialLpLimit (I := I) (M := M)
      g r s i α P l :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hApart_def
  set Sumcomp : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω with hSumcomp_def
  set Sumpart : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ l : Fin (Module.finrank ℝ E),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω with hSumpart_def
  have hAcomp_memWkp : ∀ P : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (Acomp P) Ω := by
    intro P
    rw [hAcomp_def, hΩ_def]
    exact crossRightLimitComponent_memWkp (I := I) (M := M)
      g r s i α P K (h_pou i)
  have hApart_memWkp : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Apart P l) Ω := by
    intro P l
    rw [hApart_def, hΩ_def]
    exact cutoffPartialLpLimit_memWkp (I := I) (M := M)
      g r s i α P l K (h_pou i)
  set summandComp : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2)) y *
      Acomp j.2.1 y with hsummandComp_def
  set summandPart : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2) y *
      Apart j.2.1 j.1 y with hsummandPart_def
  have hsummandComp_eq : ∀ j : ι, summandComp j =
      (fun y => euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M)
            g r s α P₀ j.1 j.2.1 j.2.2) y * Acomp j.2.1 y) := by
    intro j
    funext y
    simp only [hsummandComp_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  have hsummandPart_eq : ∀ j : ι, summandPart j =
      (fun y => crossRightDivFactor (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2 y * Apart j.2.1 j.1 y) := by
    intro j
    funext y
    simp only [hsummandPart_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  have hCcomp : ∀ j : ι,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
        ENNReal.ofReal Ccomp *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Acomp j.2.1) Ω := by
    intro j
    rw [hsummandComp_eq j]
    refine (hCcompf j (Acomp j.2.1) (hAcomp_memWkp j.2.1)).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCcompf_le j)) _
  have hCpart : ∀ j : ι,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
        ENNReal.ofReal Cpart *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 j.1) Ω := by
    intro j
    rw [hsummandPart_eq j]
    refine (hCpartf j (Apart j.2.1 j.1) (hApart_memWkp j.2.1 j.1)).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCpartf_le j)) _
  have hsummandComp_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandComp j) Ω := by
    intro j
    rw [hsummandComp_eq j, hΩ_def]
    exact (wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (by rw [← hΩ_def]; exact hAcomp_memWkp j.2.1)).1
  have hsummandPart_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandPart j) Ω := by
    intro j
    rw [hsummandPart_eq j, hΩ_def]
    exact (wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (by rw [← hΩ_def]; exact hApart_memWkp j.2.1 j.1)).1
  have h_funcA : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (crossRightDivFactor (I := I) (M := M)
                      g r s α P₀ l P Q)) y *
                (crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandComp j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_funcB : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q) y *
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandPart j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have hsumComp_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandComp j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandComp
      (fun j _ => hsummandComp_memWkp j)
  have hsumPart_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandPart j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandPart
      (fun j _ => hsummandPart_memWkp j)
  have h_triangle :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀) Ω
        ≤ (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) := by
    have h_split : crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ =
        (fun y => (∑ j : ι, summandComp j y) + (∑ j : ι, summandPart j y)) := by
      funext y
      unfold crossRightGradCoeffDivLimit
      rw [h_funcA y, h_funcB y]
    rw [h_split]
    refine le_trans
      (wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hsumComp_memWkp hsumPart_memWkp) (add_le_add ?_ ?_)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandComp
        (fun j _ => hsummandComp_memWkp j)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandPart
        (fun j _ => hsummandPart_memWkp j)
  have h_groupA :
      (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp := by
    have h_each : ∀ j : ι,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
          ENNReal.ofReal Ccomp * Sumcomp := by
      intro j
      refine (hCcomp j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Ccomp))
      rw [hSumcomp_def]
      exact Finset.single_le_sum
        (f := fun P => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω)
        (fun P _ => zero_le _) (Finset.mem_univ j.2.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have h_groupB :
      (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart := by
    have h_each : ∀ j : ι,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
          ENNReal.ofReal Cpart * Sumpart := by
      intro j
      refine (hCpart j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Cpart))
      rw [hSumpart_def]
      refine le_trans ?_
        (Finset.single_le_sum
          (f := fun P => ∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω)
          (fun P _ => zero_le _) (Finset.mem_univ j.2.1))
      exact Finset.single_le_sum
        (f := fun l => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 l) Ω)
        (fun l _ => zero_le _) (Finset.mem_univ j.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have hCcomp_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hCpart_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀) Ω
        ≤ (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) :=
        h_triangle
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp
          + ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart :=
        add_le_add h_groupA h_groupB
    _ ≤ ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * Sumcomp
          + ENNReal.ofReal
              (max ((Fintype.card ι : ℝ) * Ccomp)
                ((Fintype.card ι : ℝ) * Cpart)) * Sumpart :=
        add_le_add (mul_le_mul_left hCcomp_le _)
          (mul_le_mul_left hCpart_le _)
    _ = ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * (Sumcomp + Sumpart) :=
        (mul_add _ _ _).symm

end MainBoundUniformUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
