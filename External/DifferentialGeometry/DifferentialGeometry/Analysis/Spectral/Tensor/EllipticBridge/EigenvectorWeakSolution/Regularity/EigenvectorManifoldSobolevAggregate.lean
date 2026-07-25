import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentArbitraryKQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorMemWtwokTwo
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

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

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

namespace EigenvectorManifoldAggregateUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)

private noncomputable def perChartCompConstant
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))

omit [CompleteSpace E] in
private lemma perChartCompConstant_nonneg
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    0 ≤ perChartCompConstant (I := I) (M := M) g r s k α Idx Jdx :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).1

omit [CompleteSpace E] in
private lemma perChartCompConstant_bound
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α (Idx, Jdx))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).2 i

private noncomputable def aggregateConstant : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        perChartCompConstant (I := I) (M := M) g r s k α Idx Jdx

omit [CompleteSpace E] in
private lemma aggregateConstant_nonneg :
    0 ≤ aggregateConstant (I := I) (M := M) g r s k := by
  classical
  unfold aggregateConstant
  refine Finset.sum_nonneg fun α _ => ?_
  refine Finset.sum_nonneg fun Idx _ => ?_
  refine Finset.sum_nonneg fun Jdx _ => ?_
  exact perChartCompConstant_nonneg
    (I := I) (M := M) g r s k α Idx Jdx

end EigenvectorManifoldAggregateUnconditional

open EigenvectorManifoldAggregateUnconditional

omit [CompleteSpace E] in
private lemma tensorChartComp_eigenvectorSmooth_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
  have h_ae :
      tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α
        (Idx, Jdx) :=
    eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
      (I := I) (M := M) g r s i α Idx Jdx
  have h_eq :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s
            (eigenvectorSmooth (I := I) (M := M) g r s i)
            α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) =
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α (Idx, Jdx))
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae
  rw [h_eq]
  exact perChartCompConstant_bound
    (I := I) (M := M) g r s k α Idx Jdx i

omit [CompleteSpace E] in
private lemma chartTerm_eigenvectorSmooth_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s
              (eigenvectorSmooth (I := I) (M := M) g r s i)
              α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal
          ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                perChartCompConstant (I := I) (M := M)
                  g r s k α Idx Jdx)
            * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
  classical
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  have h_double_le :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s
                (eigenvectorSmooth (I := I) (M := M) g r s i)
                α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (perChartCompConstant
                  (I := I) (M := M) g r s k α Idx Jdx *
                    (i.fst.val)⁻¹ ^ (2 * k + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ := by
    intro Idx _hIdx
    refine le_trans (Finset.sum_le_sum (fun Jdx _ =>
      tensorChartComp_eigenvectorSmooth_wkpNorm_le
        (I := I) (M := M) g r s k α Idx Jdx i)) ?_
    rw [← Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum h_double_le) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  have h_inner :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (perChartCompConstant (I := I) (M := M)
                  g r s k α Idx Jdx *
                (i.fst.val)⁻¹ ^ (2 * k + 1))) =
          ENNReal.ofReal
            ((∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              perChartCompConstant (I := I) (M := M)
                g r s k α Idx Jdx) *
              (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    intro Idx _hIdx
    rw [Finset.sum_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun Jdx _ =>
      mul_nonneg (perChartCompConstant_nonneg
        (I := I) (M := M) g r s k α Idx Jdx) hμ_pow_nn)]
  rw [Finset.sum_congr rfl h_inner]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun Idx _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Jdx _ =>
        perChartCompConstant_nonneg
          (I := I) (M := M) g r s k α Idx Jdx)) hμ_pow_nn)]
  have h_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx) *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx) *
          (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    rw [Finset.sum_mul]
  rw [h_eq]

omit [CompleteSpace E] in
theorem eigenvectorSmooth_wtwokTwoNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        wtwokTwoNorm (I := I) (M := M) g k
            (eigenvectorSmooth (I := I) (M := M) g r s i)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  refine ⟨aggregateConstant (I := I) (M := M) g r s k,
    aggregateConstant_nonneg (I := I) (M := M) g r s k,
    fun i => ?_⟩
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k
    (eigenvectorSmooth (I := I) (M := M) g r s i)]
  refine le_trans (Finset.sum_le_sum
    (fun α _hα => chartTerm_eigenvectorSmooth_le
      (I := I) (M := M) g r s k α i)) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Idx _ =>
        Finset.sum_nonneg (fun Jdx _ =>
          perChartCompConstant_nonneg
            (I := I) (M := M) g r s k α Idx Jdx))) hμ_pow_nn)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul]
  exact le_of_eq rfl

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
