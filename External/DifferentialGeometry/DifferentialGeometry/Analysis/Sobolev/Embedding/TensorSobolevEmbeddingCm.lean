import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.SpectralPouH2Identify
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifoldHigherOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import Mathlib.Geometry.Manifold.ContMDiff.Basic


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
theorem tensorPouSobolevHilbert_embedding_Ck
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k m : ℕ}
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤
          C *
            ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ :=
  tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g r s k m h_super

end


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorChartComponentScalar_embedding_C0
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (hk : Module.finrank ℝ E < 2 * k)
    (hreg : DifferentialGeometry.Analysis.Sobolev.Chart.RegularExponent.IsRegular
      (Module.finrank ℝ E : ℝ) 2 k)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)),
        ũ x =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart (I := I) (M := M) g k 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx)).toReal) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s T α Idx Jdx
  have h_meas :
      Measurable
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    h_smooth.continuous.measurable
  have h_mem :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart (I := I) (M := M) g k 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g (p := 2) (by norm_num) k h_smooth
  exact DifferentialGeometry.Analysis.Sobolev.Chart.sobolev_embedding_chart_C0_Hk
    (I := I) (M := M) g hk hreg h_meas h_mem

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorFiberNorm_sq_le_chartCenterComponents
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (T : SmoothCcTensor g r s) (x : M) :
    ‖T.toSection x‖ ^ 2 ≤
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.midxPairCard
          (E := E) r s *
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartBasisNormConstant
          (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
              (I := I) (M := M) g r s T x Idx Jdx x) ^ 2 := by
  classical
  set Tmod : TensorRSModel r s ℝ E :=
    TensorRSSpace.toModel (𝕜 := ℝ) (I := I) (T.toSection x) with hTmod_def
  have h_norm_eq : ‖T.toSection x‖ = ‖Tmod‖ := rfl
  have h_raw_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentProjection
          (E := E) r s Idx Jdx Tmod =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s T x Idx Jdx x := by
    intro Idx Jdx
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_def]
    congr 1
    symm
    rw [hTmod_def]
    exact DifferentialGeometry.PDE.RicciFlow.HebeyBlock.triv_eq_toModel_at_chartCenter
      (I := I) r s x (T.toSection x)
  have h_alg :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSModel_norm_sq_le_sum_projection_sq
      (E := E) r s Tmod
  rw [h_norm_eq]
  refine h_alg.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl (fun Idx _ => ?_)
  refine Finset.sum_congr rfl (fun Jdx _ => ?_)
  rw [h_raw_eq Idx Jdx]

end DifferentialGeometry.PDE.RicciFlow
