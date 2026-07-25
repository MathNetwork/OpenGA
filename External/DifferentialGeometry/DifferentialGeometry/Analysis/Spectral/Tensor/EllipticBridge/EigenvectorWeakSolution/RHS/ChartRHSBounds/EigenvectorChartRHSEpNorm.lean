import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRotationENormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderENormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDivENormBound

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Aggregation

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private lemma eLpNorm_sum_le_const_mul_aggregate
    {ι : Type*} [Fintype ι] {μ : Measure EuclN} (F : ι → EuclN → ℝ)
    (A : ℝ≥0∞)
    (hF : ∀ j : ι, MemLp (F j) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧ eLpNorm (F j) 2 μ ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ j : ι, F j y) 2 μ ≤ ENNReal.ofReal C * A := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j y) = ∑ j : ι, F j := by
    funext y
    exact (Finset.sum_apply y Finset.univ F).symm
  rw [h_fun]
  have h_tri : eLpNorm (∑ j : ι, F j) 2 μ ≤ ∑ j : ι, eLpNorm (F j) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, eLpNorm (F j) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    eLpNorm (∑ j : ι, F j) 2 μ
        ≤ ∑ j : ι, eLpNorm (F j) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

end Aggregation

private lemma ofReal_two : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
  norm_num

section TermMemLp

variable (g : SmoothRiemannianMetric I M) (α : M)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma one_div_densityOnEuclid_contDiffOn :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

end TermMemLp

section Aggregate

private lemma le_sixSum (a₁ a₂ a₃ a₄ a₅ a₆ : ℝ≥0∞) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc a₁ ≤ a₁ + a₂ := le_self_add
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₂ ≤ a₁ + a₂ := le_add_self
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₃ ≤ a₁ + a₂ + a₃ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₄ ≤ a₁ + a₂ + a₃ + a₄ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · exact le_add_self

end Aggregate

section MainBound

omit [CompleteSpace E] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

end MainBound

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in

private lemma eLpNorm_sum_le_const_mul_aggregate_uniform
    {ι : Type*} [Fintype ι] {ν : Type*} {μ : Measure EuclN}
    (F : ι → ν → EuclN → ℝ) (A : ν → ℝ≥0∞)
    (hF : ∀ (j : ι) (n : ν), MemLp (F j n) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, eLpNorm (F j n) 2 μ ≤ ENNReal.ofReal C * A n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν,
        eLpNorm (fun y => ∑ j : ι, F j n y) 2 μ ≤ ENNReal.ofReal C * A n := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j n y) = ∑ j : ι, F j n := by
    funext y
    exact (Finset.sum_apply y Finset.univ (fun j => F j n)).symm
  rw [h_fun]
  have h_tri : eLpNorm (∑ j : ι, F j n) 2 μ ≤ ∑ j : ι, eLpNorm (F j n) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j n).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, eLpNorm (F j n) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j n).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    eLpNorm (∑ j : ι, F j n) 2 μ
        ≤ ∑ j : ι, eLpNorm (F j n) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A n := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A n := by
        rw [h_cast]

section BracketTermsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

def eigenvectorChartComponentFun_unconditional : EuclN → ℝ :=
  fun y =>
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

private def rhsTerm1 : EuclN → ℝ :=
  eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀

private def rhsTerm2 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
    ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

private def rhsTerm3 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r s,
    ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

private def rhsTerm4 : EuclN → ℝ :=
  covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀

private def rhsTerm5 : EuclN → ℝ :=
  covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
    g r s i α P₀

private def rhsTerm6 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    (∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M) g r s i α P₀ l y)

private def rhsTerm7 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    crossRightGradCoeffDivLimit (I := I) (M := M) g r s i α P₀ y

private def rhsBracket : EuclN → ℝ :=
  rhsTerm1 (I := I) (M := M) g r s i α P₀ -
      rhsTerm2 (I := I) (M := M) g r s i α P₀ +
      rhsTerm3 (I := I) (M := M) g r s i α P₀ -
      rhsTerm4 (I := I) (M := M) g r s i α P₀ -
      rhsTerm5 (I := I) (M := M) g r s i α P₀ +
      rhsTerm6 (I := I) (M := M) g r s i α P₀ -
      rhsTerm7 (I := I) (M := M) g r s i α P₀

omit [CompleteSpace E] in
private lemma eigenvectorChartRHS_eq_smul_bracket :
    eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
      = (i.fst.val)⁻¹ •
        rhsBracket (I := I) (M := M) g r s i α P₀ := by
  funext y
  simp only [eigenvectorChartRHS, rhsBracket,
    rhsTerm1, rhsTerm2, rhsTerm3,
    rhsTerm4, rhsTerm5, rhsTerm6,
    rhsTerm7, eigenvectorChartComponentFun_unconditional,
    Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]

end BracketTermsUnconditional

section TermMemLpUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma rhsTerm1_memLp_unconditional :
    MemLp (rhsTerm1 (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold rhsTerm1 eigenvectorChartComponentFun_unconditional
  exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    α P₀

omit [CompleteSpace E] in
private lemma rhsTerm2_summand_memLp_unconditional
    (P Q : TensorCompIdx (E := E) r (s + 1)) :
    MemLp
      (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_aezero :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    rw [crossLeftLimitComponent]
    exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
      (I := I) (M := M) g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
      (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossLeftLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
      g r s i α P)
    h_aezero

omit [CompleteSpace E] in
private lemma rhsTerm2_memLp_unconditional :
    MemLp (rhsTerm2 (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  unfold rhsTerm2
  exact memLp_finset_sum _
    (fun P _ => memLp_finset_sum _
      (fun Q _ => rhsTerm2_summand_memLp_unconditional (I := I) (M := M)
        g r s i α P₀ P Q))

omit [CompleteSpace E] in
private lemma rhsTerm3_summand_memLp_unconditional
    (P Q : TensorCompIdx (E := E) r s) :
    MemLp
      (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_aezero :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    rw [crossRightLimitComponent]
    exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
      (I := I) (M := M) g r s
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossRightLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
      g r s i α P)
    h_aezero

omit [CompleteSpace E] in
private lemma rhsTerm3_memLp_unconditional :
    MemLp (rhsTerm3 (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  unfold rhsTerm3
  exact memLp_finset_sum _
    (fun P _ => memLp_finset_sum _
      (fun Q _ => rhsTerm3_summand_memLp_unconditional (I := I) (M := M)
        g r s i α P₀ P Q))

omit [CompleteSpace E] in
private lemma rhsTerm4_memLp_unconditional :
    MemLp (rhsTerm4 (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [rhsTerm4]
  exact covPrincipalRotationCoeffLimit_memLp_weighted_unconditional
    (I := I) (M := M) g r s i α P₀

omit [CompleteSpace E] in
private lemma rhsTerm5_memLp_unconditional :
    MemLp (rhsTerm5 (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [rhsTerm5]
  exact covLowerOrderRotationValueCoeffLimit_memLp_weighted_unconditional
    (I := I) (M := M) g r s i α P₀

omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_memLp_unconditional :
    MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  exact memLp_finset_sum _
    (fun l _ => weightedGradCoeffDivLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀ l)

omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
  Filter.Eventually.of_forall (fun _y hy =>
    Finset.sum_eq_zero (fun l _ =>
      weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
        (I := I) (M := M) g r s i α P₀ l hy))

omit [CompleteSpace E] in
private lemma crossRightGradCoeffDivLimit_memLp_weighted :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

omit [CompleteSpace E] in
private lemma rhsTerm6_memLp_unconditional :
    MemLp (rhsTerm6 (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold rhsTerm6
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (weightedGradCoeffDivLimit_sum_memLp_unconditional (I := I) (M := M)
      g r s i α P₀)
    (weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P₀)

omit [CompleteSpace E] in
private lemma rhsTerm7_memLp_unconditional :
    MemLp (rhsTerm7 (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold rhsTerm7
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
      g r s i α P₀)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))

end TermMemLpUnconditional

section AggregateUnconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private def aggrUchart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
      g r s i α P₀) 2
    ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α))

private def aggrCrossLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r (s + 1),
    eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

private def aggrCrossRight
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    eLpNorm ((crossRightLimitComponent (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

private def aggrPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ k : Fin (Module.finrank ℝ E),
      eLpNorm ((partialLpLimit (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))

private def aggrComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ p : TensorCompIdx (E := E) r s,
    eLpNorm ((componentLpLimit (I := I) (M := M) g r s i α p :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

private def aggrCutoffPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ l : Fin (Module.finrank ℝ E),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
          g r s i α P l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))

private def rhsAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  aggrUchart (I := I) (M := M) g r s i α P₀ +
    aggrCrossLeft (I := I) (M := M) g r s i α P₀ +
    aggrCrossRight (I := I) (M := M) g r s i α P₀ +
    aggrPartial (I := I) (M := M) g r s i α P₀ +
    aggrComponent (I := I) (M := M) g r s i α P₀ +
    aggrCutoffPartial (I := I) (M := M) g r s i α P₀

omit [CompleteSpace E] in
private lemma aggrUchart_le_rhsAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrUchart (I := I) (M := M) g r s i α P₀
      ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  rw [rhsAggregate_unconditional]
  exact (le_sixSum _ _ _ _ _ _).1

omit [CompleteSpace E] in
private lemma aggrCrossLeft_le_rhsAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrCrossLeft (I := I) (M := M) g r s i α P₀
      ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  rw [rhsAggregate_unconditional]
  exact (le_sixSum _ _ _ _ _ _).2.1

omit [CompleteSpace E] in
private lemma aggrCrossRight_le_rhsAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrCrossRight (I := I) (M := M) g r s i α P₀
      ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  rw [rhsAggregate_unconditional]
  exact (le_sixSum _ _ _ _ _ _).2.2.1

omit [CompleteSpace E] in
private lemma aggrPartial_le_rhsAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrPartial (I := I) (M := M) g r s i α P₀
      ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  rw [rhsAggregate_unconditional]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.1

omit [CompleteSpace E] in
private lemma aggrComponent_le_rhsAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrComponent (I := I) (M := M) g r s i α P₀
      ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  rw [rhsAggregate_unconditional]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.2.1

omit [CompleteSpace E] in
private lemma aggrCutoffPartial_le_rhsAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrCutoffPartial (I := I) (M := M) g r s i α P₀
      ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  rw [rhsAggregate_unconditional]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.2.2

end AggregateUnconditional

section TermBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] in
private lemma rhsTerm1_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm1 (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  refine ⟨1, by norm_num, fun i => ?_⟩
  rw [rhsTerm1, ENNReal.ofReal_one, one_mul]
  exact le_trans (le_of_eq rfl)
    (aggrUchart_le_rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀)

omit [CompleteSpace E] in
private lemma rhsTerm2_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm2 (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set F : (TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1)) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have hF_memLp : ∀ (x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1))
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F x i) 2 μw := by
    intro x i
    rw [hμw_def, hF_def]
    exact rhsTerm2_summand_memLp_unconditional (I := I) (M := M)
      g r s i α P₀ x.1 x.2
  have hF_bd : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (F x i) 2 μw
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
    intro x
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M)
          g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    refine ⟨C, hC_nn, fun i => ?_⟩
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    have h_atom_le :
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
      refine le_trans ?_
        (aggrCrossLeft_le_rhsAggregate_unconditional (I := I) (M := M)
          g r s i α P₀)
      rw [hμw_def, aggrCrossLeft]
      exact Finset.single_le_sum
        (f := fun P => eLpNorm ((crossLeftLimitComponent
            (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le _) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd _
      (crossLeftLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α x.1) h_aezero) ?_
    gcongr
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1), F x i y)
      = rhsTerm2 (I := I) (M := M) g r s i α P₀ := by
    funext y
    simp only [rhsTerm2, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd i

omit [CompleteSpace E] in
private lemma rhsTerm3_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm3 (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set F : (TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossRightLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have hF_memLp : ∀ (x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s)
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F x i) 2 μw := by
    intro x i
    rw [hμw_def, hF_def]
    exact rhsTerm3_summand_memLp_unconditional (I := I) (M := M)
      g r s i α P₀ x.1 x.2
  have hF_bd : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (F x i) 2 μw
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
    intro x
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    refine ⟨C, hC_nn, fun i => ?_⟩
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    have h_atom_le :
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
      refine le_trans ?_
        (aggrCrossRight_le_rhsAggregate_unconditional (I := I) (M := M)
          g r s i α P₀)
      rw [hμw_def, aggrCrossRight]
      exact Finset.single_le_sum
        (f := fun P => eLpNorm ((crossRightLimitComponent
            (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le _) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd _
      (crossRightLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α x.1) h_aezero) ?_
    gcongr
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s, F x i y)
      = rhsTerm3 (I := I) (M := M) g r s i α P₀ := by
    funext y
    simp only [rhsTerm3, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd i

omit [CompleteSpace E] in
private lemma rhsTerm4_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm4 (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eLpNorm_covPrincipalRotationCoeffLimit_le_uniform
      (I := I) (M := M) g r s α P₀
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [rhsTerm4]
  refine le_trans (hC_bd i) ?_
  gcongr
  exact aggrPartial_le_rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀

omit [CompleteSpace E] in
private lemma rhsTerm5_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm5 (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eLpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀
  refine ⟨2 * C, by positivity, fun i => ?_⟩
  rw [rhsTerm5]
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (aggrPartial_le_rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀)
      (aggrComponent_le_rhsAggregate_unconditional (I := I) (M := M)
        g r s i α P₀)
  refine le_trans (hC_bd i) ?_
  calc
    ENNReal.ofReal C *
        ((∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))))
        ≤ ENNReal.ofReal C *
            (2 * rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
        rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
          mul_comm C 2]

omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm
            (fun y => ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set F : Fin (Module.finrank ℝ E) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun l i => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ l with hF_def
  have hF_memLp : ∀ (l : Fin (Module.finrank ℝ E))
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F l i) 2 μw := by
    intro l i
    rw [hμw_def, hF_def]
    exact weightedGradCoeffDivLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀ l
  have hF_bd : ∀ l : Fin (Module.finrank ℝ E), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (F l i) 2 μw
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
    intro l
    obtain ⟨C, hC_nn, hC_bd⟩ :=
      eLpNorm_weightedGradCoeffDivLimit_le_uniform_unconditional
        (I := I) (M := M) g r s α P₀ l
    refine ⟨2 * C, by positivity, fun i => ?_⟩
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd i) ?_
    have h_sum_le :
        (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              ∑ l' : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s i α p l' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
        ≤ 2 * rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
      rw [two_mul]
      exact add_le_add
        (aggrComponent_le_rhsAggregate_unconditional (I := I) (M := M)
          g r s i α P₀)
        (aggrPartial_le_rhsAggregate_unconditional (I := I) (M := M)
          g r s i α P₀)
    calc
      ENNReal.ofReal C *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s i α p l' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α))))
          ≤ ENNReal.ofReal C *
              (2 * rhsAggregate_unconditional (I := I) (M := M)
                g r s i α P₀) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
          rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [hμw_def] at hC_bd
  exact hC_bd i

omit [CompleteSpace E] in
private lemma rhsTerm6_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm6 (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀
  refine ⟨C₁ * C₂, by positivity, fun i => ?_⟩
  unfold rhsTerm6
  calc
    eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
          hC₁_bd _
            (weightedGradCoeffDivLimit_sum_memLp_unconditional (I := I) (M := M)
              g r s i α P₀)
            (weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional
              (I := I) (M := M) g r s i α P₀)
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀) := by
        gcongr
        exact hC₂_bd i
    _ = ENNReal.ofReal (C₁ * C₂) *
          rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]

omit [CompleteSpace E] in
private lemma rhsTerm7_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm7 (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    eLpNorm_crossRightGradCoeffDivLimit_le_uniform
      (I := I) (M := M) g r s α P₀
  refine ⟨C₁ * (2 * C₂), by positivity, fun i => ?_⟩
  unfold rhsTerm7
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          eLpNorm ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ l : Fin (Module.finrank ℝ E),
              eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (aggrCrossRight_le_rhsAggregate_unconditional (I := I) (M := M)
        g r s i α P₀)
      (aggrCutoffPartial_le_rhsAggregate_unconditional (I := I) (M := M)
        g r s i α P₀)
  calc
    eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
          hC₁_bd _
            (crossRightGradCoeffDivLimit_memLp_weighted
              (I := I) (M := M) g r s i α P₀)
            (Filter.Eventually.of_forall (fun y hy =>
              crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s i α P₀ hy))
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * rhsAggregate_unconditional (I := I) (M := M)
              g r s i α P₀)) := by
        gcongr
        exact le_trans (hC₂_bd i) (by gcongr)
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_two]
        ring

end TermBoundsUnconditional

section BracketBoundUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] in
private lemma rhsBracket_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsBracket (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
  classical
  obtain ⟨D1, hD1_nn, hD1⟩ := rhsTerm1_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D2, hD2_nn, hD2⟩ := rhsTerm2_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D3, hD3_nn, hD3⟩ := rhsTerm3_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D4, hD4_nn, hD4⟩ := rhsTerm4_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D5, hD5_nn, hD5⟩ := rhsTerm5_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D6, hD6_nn, hD6⟩ := rhsTerm6_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D7, hD7_nn, hD7⟩ := rhsTerm7_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hM1 := rhsTerm1_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM2 := rhsTerm2_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM3 := rhsTerm3_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM4 := rhsTerm4_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM5 := rhsTerm5_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM6 := rhsTerm6_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM7 := rhsTerm7_memLp_unconditional (I := I) (M := M) g r s i α P₀
  rw [← hμw_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  have hB12 := hM1.sub hM2
  have hB123 := hB12.add hM3
  have hB1234 := hB123.sub hM4
  have hB12345 := hB1234.sub hM5
  have hB123456 := hB12345.add hM6
  have h_tri :
      eLpNorm (rhsBracket (I := I) (M := M) g r s i α P₀) 2 μw
        ≤ eLpNorm (rhsTerm1 (I := I) (M := M) g r s i α P₀) 2 μw
          + eLpNorm (rhsTerm2 (I := I) (M := M) g r s i α P₀) 2 μw
          + eLpNorm (rhsTerm3 (I := I) (M := M) g r s i α P₀) 2 μw
          + eLpNorm (rhsTerm4 (I := I) (M := M) g r s i α P₀) 2 μw
          + eLpNorm (rhsTerm5 (I := I) (M := M) g r s i α P₀) 2 μw
          + eLpNorm (rhsTerm6 (I := I) (M := M) g r s i α P₀) 2 μw
          + eLpNorm (rhsTerm7 (I := I) (M := M)
              g r s i α P₀) 2 μw := by
    rw [rhsBracket]
    refine le_trans (eLpNorm_sub_le hB123456.aestronglyMeasurable
      hM7.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hB12345.aestronglyMeasurable
      hM6.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hB1234.aestronglyMeasurable
      hM5.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hB123.aestronglyMeasurable
      hM4.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hB12.aestronglyMeasurable
      hM3.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_sub_le hM1.aestronglyMeasurable
      hM2.aestronglyMeasurable (by norm_num)
  refine le_trans h_tri ?_
  have h_seven :
      eLpNorm (rhsTerm1 (I := I) (M := M) g r s i α P₀) 2 μw
        + eLpNorm (rhsTerm2 (I := I) (M := M) g r s i α P₀) 2 μw
        + eLpNorm (rhsTerm3 (I := I) (M := M) g r s i α P₀) 2 μw
        + eLpNorm (rhsTerm4 (I := I) (M := M) g r s i α P₀) 2 μw
        + eLpNorm (rhsTerm5 (I := I) (M := M) g r s i α P₀) 2 μw
        + eLpNorm (rhsTerm6 (I := I) (M := M) g r s i α P₀) 2 μw
        + eLpNorm (rhsTerm7 (I := I) (M := M) g r s i α P₀) 2 μw
      ≤ ENNReal.ofReal D1 *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D2 *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D3 *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D4 *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D5 *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D6 *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D7 *
            rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
    exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (hD1 i) (hD2 i)) (hD3 i)) (hD4 i)) (hD5 i)) (hD6 i)) (hD7 i)
  refine le_trans h_seven ?_
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

end BracketBoundUnconditional

section MainBoundUnconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_eLpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            (eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
                  g r s i α P₀) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r (s + 1),
                  eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                      g r s i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                      g r s i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ k : Fin (Module.finrank ℝ E),
                    eLpNorm ((partialLpLimit (I := I) (M := M)
                        g r s i α P k :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  eLpNorm ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s i α P l :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := rhsBracket_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  refine ⟨C, hC_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hC_bd_i := hC_bd i
  have h_smul_eq :
      eLpNorm (eigenvectorChartRHS (I := I) (M := M)
          g r s i α P₀) 2 μw
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (rhsBracket (I := I) (M := M)
            g r s i α P₀) 2 μw := by
    rw [eigenvectorChartRHS_eq_smul_bracket (I := I) (M := M)
      g r s i α P₀]
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (i.fst.val)⁻¹
      (rhsBracket (I := I) (M := M) g r s i α P₀)
    rw [Real.enorm_of_nonneg hμ_inv_nn] at h
    exact h
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (rhsBracket (I := I) (M := M)
            g r s i α P₀) 2 μw
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsAggregate_unconditional (I := I) (M := M) g r s i α P₀ := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  exact h_step

end MainBoundUnconditional
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
