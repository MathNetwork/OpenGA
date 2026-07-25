import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRotationWkpNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDivWkpNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSWkpNormProductBounds

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

def eigenvectorResolventChartWkpRegularity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ) : Prop :=
  ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
    MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)

section BracketTermsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

def rhsTerm1 : EuclN → ℝ :=
  fun y =>
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

def rhsTerm2 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
    ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

def rhsTerm3 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r s,
    ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

def rhsTerm4 : EuclN → ℝ :=
  covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀

def rhsTerm5 : EuclN → ℝ :=
  covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
    g r s i α P₀

def rhsTerm6 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    (∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y)

def rhsTerm7 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    crossRightGradCoeffDivLimit (I := I) (M := M) g r s i α P₀ y

def rhsBracket : EuclN → ℝ :=
  rhsTerm1 (I := I) (M := M) g r s i α P₀ -
      rhsTerm2 (I := I) (M := M) g r s i α P₀ +
      rhsTerm3 (I := I) (M := M) g r s i α P₀ -
      rhsTerm4 (I := I) (M := M) g r s i α P₀ -
      rhsTerm5 (I := I) (M := M) g r s i α P₀ +
      rhsTerm6 (I := I) (M := M) g r s i α P₀ -
      rhsTerm7 (I := I) (M := M) g r s i α P₀


omit [CompleteSpace E] in
lemma eigenvectorChartRHS_eq_smul_bracket :
    eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
      = fun y => (i.fst.val)⁻¹ *
          rhsBracket (I := I) (M := M) g r s i α P₀ y := by
  funext y
  simp only [eigenvectorChartRHS, rhsBracket,
    rhsTerm1, rhsTerm2, rhsTerm3,
    rhsTerm4, rhsTerm5, rhsTerm6,
    rhsTerm7, Pi.sub_apply, Pi.add_apply]

end BracketTermsUnconditional

section TermMemWkpUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

omit [CompleteSpace E] in
lemma rhsTerm1_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm1 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm1
  exact eigenvectorChartRHS_summand1_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

omit [CompleteSpace E] in
lemma rhsTerm2_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm2 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm2
  exact eigenvectorChartRHS_summand2_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

omit [CompleteSpace E] in
lemma rhsTerm3_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm3 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm3
  exact eigenvectorChartRHS_summand3_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

omit [CompleteSpace E] in
lemma rhsTerm4_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm4 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm4
  exact eigenvectorChartRHS_summand4_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

omit [CompleteSpace E] in
lemma rhsTerm5_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm5 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm5
  exact eigenvectorChartRHS_summand5_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

omit [CompleteSpace E] in
lemma rhsTerm6_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm6 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm6
  exact eigenvectorChartRHS_summand6_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

omit [CompleteSpace E] in
lemma rhsTerm7_memWkp
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm7 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm7
  exact eigenvectorChartRHS_summand7_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

end TermMemWkpUnconditional

section AggregateUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

def resolventH1ComplChartWkpNorm (N : ℕ) (β : M)
    (Q : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))
        β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) β)

def aggrUchart : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) α)

def aggrCrossLeft : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ((∑ Q : TensorCompIdx (E := E) r s,
        resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i (K + 1) β Q)
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i (K + 1) β' Q)

def aggrCrossRight : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ∑ Q : TensorCompIdx (E := E) r s,
      resolventH1ComplChartWkpNorm (I := I) (M := M) g r s i K β Q

def aggrPartial : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ k : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

def aggrComponent : ℝ≥0∞ :=
  ∑ p : TensorCompIdx (E := E) r s,
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((componentLpLimit (I := I) (M := M)
          g r s i α p :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

def aggrCrossRightLimit : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

def aggrCutoffPartial : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ l : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

def wkpRhsAggregate : ℝ≥0∞ :=
  aggrUchart (I := I) (M := M) g r s i α P₀ K +
    aggrCrossLeft (I := I) (M := M) g r s i α K +
    aggrCrossRight (I := I) (M := M) g r s i α K +
    aggrPartial (I := I) (M := M) g r s i α K +
    aggrComponent (I := I) (M := M) g r s i α K +
    aggrCrossRightLimit (I := I) (M := M) g r s i α K +
    aggrCutoffPartial (I := I) (M := M) g r s i α K

end AggregateUnconditional

section DominationUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)


omit [CompleteSpace E] in
lemma aggrUchart_le :
    aggrUchart (I := I) (M := M) g r s i α P₀ K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).1


omit [CompleteSpace E] in
lemma aggrCrossLeft_le :
    aggrCrossLeft (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).2.1


omit [CompleteSpace E] in
lemma aggrCrossRight_le :
    aggrCrossRight (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.1


omit [CompleteSpace E] in
lemma aggrPartial_le :
    aggrPartial (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.1


omit [CompleteSpace E] in
lemma aggrComponent_le :
    aggrComponent (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.1


omit [CompleteSpace E] in
lemma aggrCrossRightLimit_le :
    aggrCrossRightLimit (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.1


omit [CompleteSpace E] in
lemma aggrCutoffPartial_le :
    aggrCutoffPartial (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.2

omit [CompleteSpace E] in
lemma crossRightGradCoeffDivLimit_memWkp_local
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_term7_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω :=
    rhsTerm7_memWkp (I := I) (M := M) g r s i α P₀ K h_pou
  have h_term7_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        rhsTerm7 (I := I) (M := M) g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp => by
      change (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0
      rw [crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp, mul_zero])
  obtain ⟨h_prod_memWkp, _⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_term7_memWkp h_term7_ae_zero
  have h_ae_eq : (fun y => densityOnEuclid (I := I) g α y *
        rhsTerm7 (I := I) (M := M) g r s i α P₀ y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ := by
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hy' : y ∈ chartTargetEuclid (I := I) (M := M) α := hy
    have h_pos : densityOnEuclid (I := I) g α y ≠ 0 :=
      (densityOnEuclid_pos (I := I) g α hy').ne'
    change densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y)
      = crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y
    rw [← mul_assoc, mul_one_div, div_self h_pos, one_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp

end DominationUnconditional

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
