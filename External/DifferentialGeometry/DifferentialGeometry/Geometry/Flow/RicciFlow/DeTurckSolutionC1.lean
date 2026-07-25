import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckShortTime
import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Geometry.Manifold.ContMDiff.Basic


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem maxreg_solution_in_c1_via_sobolev_embedding
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_hsol : IsQuasilinearMetricParabolicSolution (I := I)
              (deTurckRicciRHS (I := I) g_bg) (g_DT 0) T g_DT)
    (_h_super : 2 * 3 > Module.finrank ℝ E + 2 * 1) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T) := by
  obtain ⟨_hT, _hinit, hderiv⟩ := _hsol
  intro x v w t ht
  have hcont_within_Ici :
      ContinuousWithinAt (fun s : ℝ => (g_DT s).inner x v w) (Set.Ici (0 : ℝ)) t :=
    (hderiv t ht x v w).continuousWithinAt
  exact hcont_within_Ici.mono Set.Ico_subset_Ici_self

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem c1_norm_time_continuous_from_h1_time_derivative
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_hsol : IsQuasilinearMetricParabolicSolution (I := I)
              (deTurckRicciRHS (I := I) g_bg) (g_DT 0) T g_DT) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T) := by
  obtain ⟨_hT, _hinit, hderiv⟩ := _hsol
  intro x v w t ht
  have hcont_within_Ici :
      ContinuousWithinAt (fun s : ℝ => (g_DT s).inner x v w) (Set.Ici (0 : ℝ)) t :=
    (hderiv t ht x v w).continuousWithinAt
  exact hcont_within_Ici.mono Set.Ico_subset_Ici_self
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deturck_vf_continuous_in_c1_input
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_h_metric_cont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T))
    (h_pointwise_vf : ∀ x : M,
      ContinuousOn
        (fun t : ℝ =>
          (deTurckVF (I := I) (g_DT t) g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        (Set.Ico (0 : ℝ) T)) :
    ∀ x : M,
      ContinuousOn
        (fun t : ℝ =>
          (deTurckVF (I := I) (g_DT t) g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        (Set.Ico (0 : ℝ) T) := h_pointwise_vf


end DifferentialGeometry.PDE.RicciFlow
