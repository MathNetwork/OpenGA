import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwins
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightLimit

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section CrossRotationWkpNormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private lemma wkpNorm_doubleSum_le_const_mul_aggregateSum
    {ι κ : Type*} [Fintype κ]
    (S : Finset ι) (W : ι → κ → ℝ≥0∞) (aggr : ι → ℝ≥0∞)
    (Cf : ι → κ → ℝ) (hCf_nn : ∀ j ∈ S, ∀ q : κ, 0 ≤ Cf j q)
    (h_bd : ∀ j ∈ S, ∀ q : κ,
      W j q ≤ ENNReal.ofReal (Cf j q) * aggr j) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ j ∈ S, ∑ q : κ, W j q)
        ≤ ENNReal.ofReal C * ∑ j ∈ S, aggr j := by
  classical
  set Csup : ℝ := 1 + ∑ j ∈ S, ∑ q : κ, Cf j q with hCsup_def
  have hCsup_nn : 0 ≤ Csup := by
    rw [hCsup_def]
    have h_sum_nn : 0 ≤ ∑ j ∈ S, ∑ q : κ, Cf j q :=
      Finset.sum_nonneg (fun j hj =>
        Finset.sum_nonneg (fun q _ => hCf_nn j hj q))
    linarith
  have hCf_le_Csup : ∀ j ∈ S, ∀ q : κ, Cf j q ≤ Csup := by
    intro j hj q
    rw [hCsup_def]
    have h_inner : Cf j q ≤ ∑ q' : κ, Cf j q' :=
      Finset.single_le_sum (f := fun q' => Cf j q')
        (fun q' _ => hCf_nn j hj q') (Finset.mem_univ q)
    have h_outer : (∑ q' : κ, Cf j q') ≤ ∑ j' ∈ S, ∑ q' : κ, Cf j' q' :=
      Finset.single_le_sum (f := fun j' => ∑ q' : κ, Cf j' q')
        (fun j' hj' => Finset.sum_nonneg (fun q' _ => hCf_nn j' hj' q')) hj
    linarith [h_inner.trans h_outer]
  refine ⟨Csup * (Fintype.card κ), by positivity, ?_⟩
  have h_each : ∀ j ∈ S, ∀ q : κ,
      W j q ≤ ENNReal.ofReal Csup * aggr j := by
    intro j hj q
    refine (h_bd j hj q).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCf_le_Csup j hj q)) (zero_le _)
  have h_inner_const : ∀ j ∈ S,
      (∑ q : κ, W j q)
        ≤ (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr j) := by
    intro j hj
    refine (Finset.sum_le_sum (fun q _ => h_each j hj q)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_const_eq : (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup
      = ENNReal.ofReal (Csup * (Fintype.card κ)) := by
    rw [mul_comm Csup, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ _),
      ENNReal.ofReal_natCast]
  calc
    (∑ j ∈ S, ∑ q : κ, W j q)
        ≤ ∑ j ∈ S, (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr j) :=
          Finset.sum_le_sum h_inner_const
    _ = (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup * ∑ j ∈ S, aggr j := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    _ = ENNReal.ofReal (Csup * (Fintype.card κ)) * ∑ j ∈ S, aggr j := by
          rw [h_const_eq]

end CrossRotationWkpNormBounds

section CrossRotationWkpNormBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (K : ℕ)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private lemma wkpNorm_doubleSum_le_const_mul_aggregateSum_uniform
    {δ ι κ : Type*} [Fintype κ]
    (S : Finset ι) (W : δ → ι → κ → ℝ≥0∞) (aggr : δ → ι → ℝ≥0∞)
    (Cf : ι → κ → ℝ) (hCf_nn : ∀ j ∈ S, ∀ q : κ, 0 ≤ Cf j q)
    (h_bd : ∀ (d : δ), ∀ j ∈ S, ∀ q : κ,
      W d j q ≤ ENNReal.ofReal (Cf j q) * aggr d j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : δ,
        (∑ j ∈ S, ∑ q : κ, W d j q)
          ≤ ENNReal.ofReal C * ∑ j ∈ S, aggr d j := by
  classical
  set Csup : ℝ := 1 + ∑ j ∈ S, ∑ q : κ, Cf j q with hCsup_def
  have hCsup_nn : 0 ≤ Csup := by
    rw [hCsup_def]
    have h_sum_nn : 0 ≤ ∑ j ∈ S, ∑ q : κ, Cf j q :=
      Finset.sum_nonneg (fun j hj =>
        Finset.sum_nonneg (fun q _ => hCf_nn j hj q))
    linarith
  have hCf_le_Csup : ∀ j ∈ S, ∀ q : κ, Cf j q ≤ Csup := by
    intro j hj q
    rw [hCsup_def]
    have h_inner : Cf j q ≤ ∑ q' : κ, Cf j q' :=
      Finset.single_le_sum (f := fun q' => Cf j q')
        (fun q' _ => hCf_nn j hj q') (Finset.mem_univ q)
    have h_outer : (∑ q' : κ, Cf j q') ≤ ∑ j' ∈ S, ∑ q' : κ, Cf j' q' :=
      Finset.single_le_sum (f := fun j' => ∑ q' : κ, Cf j' q')
        (fun j' hj' => Finset.sum_nonneg (fun q' _ => hCf_nn j' hj' q')) hj
    linarith [h_inner.trans h_outer]
  refine ⟨Csup * (Fintype.card κ), by positivity, fun d => ?_⟩
  have h_each : ∀ j ∈ S, ∀ q : κ,
      W d j q ≤ ENNReal.ofReal Csup * aggr d j := by
    intro j hj q
    refine (h_bd d j hj q).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCf_le_Csup j hj q)) (zero_le _)
  have h_inner_const : ∀ j ∈ S,
      (∑ q : κ, W d j q)
        ≤ (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr d j) := by
    intro j hj
    refine (Finset.sum_le_sum (fun q _ => h_each j hj q)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_const_eq : (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup
      = ENNReal.ofReal (Csup * (Fintype.card κ)) := by
    rw [mul_comm Csup, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ _),
      ENNReal.ofReal_natCast]
  calc
    (∑ j ∈ S, ∑ q : κ, W d j q)
        ≤ ∑ j ∈ S, (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr d j) :=
          Finset.sum_le_sum h_inner_const
    _ = (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup * ∑ j ∈ S, aggr d j := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    _ = ENNReal.ofReal (Csup * (Fintype.card κ)) * ∑ j ∈ S, aggr d j := by
          rw [h_const_eq]

end CrossRotationWkpNormBoundsUniform

section CrossRightWkpNormBoundUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

omit [CompleteSpace E] in
theorem wkpNorm_crossRightLimitComponent_le
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  have h_unfold : (fun y => ((crossRightLimitComponent (I := I)
        (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent]
  rw [h_unfold]
  exact wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
    g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P K h_pou

end CrossRightWkpNormBoundUnconditional

section CrossRightWkpNormBoundUniformUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (K : ℕ)

omit [CompleteSpace E] in
theorem wkpNorm_crossRightLimitComponent_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r s α P K
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_unfold : (fun y => ((crossRightLimitComponent (I := I)
        (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent]
  rw [h_unfold]
  exact hC_bd
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    (h_pou i)

end CrossRightWkpNormBoundUniformUnconditional

section CrossRotationWkpNormBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

omit [CompleteSpace E] in
theorem wkpNorm_crossLeftLimitComponent_le
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ((∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
              + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  set aggr : M → ℝ≥0∞ := fun β =>
    (∑ Q : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β')
    with haggr_def
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
      g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))
      α P K
      (fun β Q' => eigenvectorCovGrad_pou_memWkp (I := I) (M := M)
        g r s i K h_pou β Q')
  have h_per : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                (tensorCovGradL2Compl (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C * aggr β :=
    fun β Q' => eigenvectorCovGrad_pou_wkpNorm_le (I := I) (M := M)
      g r s i K h_pou β Q'
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum
      (transportChartCenters (I := I) (M := M) α)
      (fun β Q' => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun β => aggr β)
      (fun β Q' => (h_per β Q').choose)
      (fun β _ Q' => (h_per β Q').choose_spec.1)
      (fun β _ Q' => (h_per β Q').choose_spec.2)
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  have h_chain : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α, aggr β) := by
    have h_unfold : (fun y => ((crossLeftLimitComponent (I := I)
          (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent]
    rw [h_unfold]
    refine hC₀_bd.trans ?_
    exact mul_le_mul_of_nonneg_left hC₁_bd (zero_le _)
  refine h_chain.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn]

end CrossRotationWkpNormBoundsUnconditional

section CrossRotationWkpNormBoundsUniformUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (K : ℕ)

omit [CompleteSpace E] in
theorem wkpNorm_crossLeftLimitComponent_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ((∑ Q : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s i))
                        β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β))
                + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                    ∑ Q : TensorCompIdx (E := E) r s,
                      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                        (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                            g r s
                            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                              (eigenvectorResolvent (I := I)
                                (M := M) g r s i))
                            β' Q :
                            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                            EuclN → ℝ) y)
                        (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  set aggr : TensorEigenIdx (I := I) (M := M) g r s → M → ℝ≥0∞ := fun i β =>
    (∑ Q : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β')
    with haggr_def
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r (s + 1) α P K
  set Cf : M → TensorCompIdx (E := E) r (s + 1) → ℝ :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform (I := I) (M := M)
        g r s K h_pou β Q').choose
    with hCf_def
  have hCf_spec : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      0 ≤ Cf β Q' ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2Compl (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (Cf β Q') * aggr i β :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform (I := I) (M := M)
        g r s K h_pou β Q').choose_spec
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum_uniform
      (δ := TensorEigenIdx (I := I) (M := M) g r s)
      (transportChartCenters (I := I) (M := M) α)
      (fun i β Q' => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun i β => aggr i β)
      (fun β Q' => Cf β Q')
      (fun β _ Q' => (hCf_spec β Q').1)
      (fun i β _ Q' => (hCf_spec β Q').2 i)
  refine ⟨C₀ * C₁, by positivity, fun i => ?_⟩
  have h_chain : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α, aggr i β) := by
    have h_unfold : (fun y => ((crossLeftLimitComponent (I := I)
          (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent]
    rw [h_unfold]
    refine (hC₀_bd
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))
      (fun β Q' => eigenvectorCovGrad_pou_memWkp (I := I) (M := M)
        g r s i K (h_pou i) β Q')).trans ?_
    exact mul_le_mul_of_nonneg_left (hC₁_bd i) (zero_le _)
  refine h_chain.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn]

end CrossRotationWkpNormBoundsUniformUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
