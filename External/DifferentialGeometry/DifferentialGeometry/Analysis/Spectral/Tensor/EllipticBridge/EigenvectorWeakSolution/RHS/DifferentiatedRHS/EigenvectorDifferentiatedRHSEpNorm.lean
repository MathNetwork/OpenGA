import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNormRestrictedVolumeL2Bounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNormAtomEnvelopeBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNormEigenvalueInverseBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNormUniformAggregateBound

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
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section LayerBoundsUnconditional

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s i α P₀ m l fChartEffPrev with hA_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_coeff : ∀ a b : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro a b
    have h_diffOn : ContDiffOn ℝ ∞
        (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
    have h_fderiv : ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ ∞
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  have h_atom_mem : ∀ a : Fin (Module.finrank ℝ E),
      MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2 μ := by
    intro a
    have h0 := (h_iter a).le_of_le (Nat.zero_le 2)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict
          (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  have h_atom_le : ∀ a : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) ≤ A := by
    intro a
    rw [hA_def, diffNumeratorAggregate]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  refine eLpNorm_sum_le_const_mul_aggregate
    (μ := μ)
    (fun a => fun y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) A ?_ ?_
  · intro a
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem a)
  · intro a
    refine eLpNorm_sum_le_const_mul_aggregate
      (μ := μ)
      (fun b => fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) A ?_ ?_
    · intro b
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem a)
    · intro b
      obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
        (I := I) (M := M) α (h_coeff a b) hK_compact hK_meas hK_in
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      rw [← hμ_def] at hC₀
      refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
      gcongr
      exact le_trans (eLpNorm_iteratedPartial_succ_le
        (I := I) (M := M) g r s i α P₀ m l a) (h_atom_le a)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s i α P₀ m l fChartEffPrev with hA_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_atom_le : ∀ a : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω ≤ A := by
    intro a
    rw [hA_def, diffNumeratorAggregate, ← hΩ_def]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω)
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_chosen_mem : ∀ a b : Fin (Module.finrank ℝ E),
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) 2 μ := by
    intro a b
    have h1 : MemWkp (d := Module.finrank ℝ E) 1 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) Ω :=
      (h_iter a).chosenWeakPartial_mem b
    have h0 := h1.le_of_le (Nat.zero_le 1)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
        (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  refine eLpNorm_sum_le_const_mul_aggregate
    (μ := μ)
    (fun a => fun y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y) A ?_ ?_
  · intro a
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in (h_chosen_mem a b)
  · intro a
    refine eLpNorm_sum_le_const_mul_aggregate
      (μ := μ)
      (fun b => fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y) A ?_ ?_
    · intro b
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m)))
        hK_compact hK_meas hK_in (h_chosen_mem a b)
    · intro b
      obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
        (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m)))
        hK_compact hK_meas hK_in
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω)
      rw [← hμ_def] at hC₀
      refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
      gcongr
      exact le_trans (eLpNorm_chosenWeakPartial_iteratedPartial_succ_le
        (I := I) (M := M) g r s i α P₀ m l a b) (h_atom_le a)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m (Fin.init l) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s i α P₀ m l fChartEffPrev with hA_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_atom_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α) ≤ A := by
    rw [hA_def, diffNumeratorAggregate]
    exact le_trans le_add_self (le_trans le_self_add le_self_add)
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
    (eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s i α P₀ m (Fin.init l))
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  exact le_trans (eLpNorm_iteratedPartial_le
    (I := I) (M := M) g r s i α P₀ m l) h_atom_le

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            fChartEffPrev y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s i α P₀ m l fChartEffPrev with hA_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_atom_le : eLpNorm fChartEffPrev 2 μ ≤ A := by
    rw [hA_def, diffNumeratorAggregate, ← hμ_def]
    exact le_add_self
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in fChartEffPrev
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y =>
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
              fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s i α P₀ m l fChartEffPrev with hA_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_atom_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2 fChartEffPrev Ω ≤ A := by
    rw [hA_def, diffNumeratorAggregate, ← hΩ_def]
    exact le_trans le_add_self le_self_add
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
    (I := I) (M := M) α
    (densityOnEuclid_contDiffOn (I := I) g α)
    hK_compact hK_meas hK_in
    (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
      fChartEffPrev Ω)
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
      (chartPouKernel (I := I) (M := M) α) := by
    rw [hμ_def, Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_le_self)) ?_
  refine le_trans (eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 0 2 Ω _) ?_
  exact le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) 0
    hΩ_open _ (l (Fin.last m))) h_atom_le

end LayerBoundsUnconditional

section MainBoundUnconditional


omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) 1 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (_h_prev_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α → fChartEffPrev y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s i α P₀ m l fChartEffPrev y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s i α P₀ m l fChartEffPrev with hA_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l fChartEffPrev y) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  have hA_mem : MemLp layerA 2 μ := by
    rw [hlayerA_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_coeff : ContDiffOn ℝ ∞
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_diffOn : ContDiffOn ℝ ∞
          (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
      have h_fderiv : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
    have h_atom_mem : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2 μ := by
      have h0 := (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le
        (Nat.zero_le 2)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      h_coeff hK_compact hK_meas hK_in h_atom_mem
  have hB_mem : MemLp layerB 2 μ := by
    rw [hlayerB_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_chosen_mem : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) 2 μ := by
      have h1 := ((h_iter (m + 1) (Fin.cons a (Fin.init l)))).chosenWeakPartial_mem b
      have h0 := h1.le_of_le (Nat.zero_le 1)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in h_chosen_mem
  have hC_mem : MemLp layerC 2 μ := by
    rw [hlayerC_def]
    have h_atom_mem : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l)) 2 μ := by
      have h0 := (h_iter m (Fin.init l)).le_of_le (Nat.zero_le 2)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_atom_mem
  have hD_mem : MemLp layerD 2 μ := by
    rw [hlayerD_def]
    have h_prev_mem : MemLp fChartEffPrev 2 μ := by
      have h0 := h_prev.le_of_le (Nat.zero_le 1)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_prev_mem
  have hE_mem : MemLp layerE 2 μ := by
    rw [hlayerE_def]
    have h_chosen_mem : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2
        (l (Fin.last m)) fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)) 2 μ := by
      have h1 := h_prev.chosenWeakPartial_mem (l (Fin.last m))
      rw [MemWkp_zero] at h1
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h1.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityOnEuclid_contDiffOn (I := I) g α)
      hK_compact hK_meas hK_in h_chosen_mem
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le
    (I := I) (M := M) g r s i α P₀ m l fChartEffPrev
    (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le
    (I := I) (M := M) g r s i α P₀ m l fChartEffPrev
    (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le
    (I := I) (M := M) g r s i α P₀ m l fChartEffPrev
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le
    (I := I) (M := M) g r s i α P₀ m l fChartEffPrev
  obtain ⟨CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le
    (I := I) (M := M) g r s i α P₀ m l fChartEffPrev
  rw [← hμ_def, ← hA_def] at hCA hCB hCC hCD hCE
  refine ⟨CA + CB + CC + CD + CE, by positivity, ?_⟩
  rw [h_num_eq]
  have h_tri :
      eLpNorm (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) 2 μ
        ≤ eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
          + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ := by
    have h_pi : (fun y => layerA y + layerB y - layerC y + layerD y + layerE y)
        = layerA + layerB - layerC + layerD + layerE := by
      funext y
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [h_pi]
    have hAB_mem : MemLp (layerA + layerB) 2 μ := hA_mem.add hB_mem
    have hABC_mem : MemLp (layerA + layerB - layerC) 2 μ := hAB_mem.sub hC_mem
    have hABCD_mem : MemLp (layerA + layerB - layerC + layerD) 2 μ :=
      hABC_mem.add hD_mem
    refine le_trans (eLpNorm_add_le hABCD_mem.aestronglyMeasurable
      hE_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hABC_mem.aestronglyMeasurable
      hD_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hAB_mem.aestronglyMeasurable
      hC_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_add_le hA_mem.aestronglyMeasurable
      hB_mem.aestronglyMeasurable (by norm_num)
  refine le_trans h_tri ?_
  have h_five :
      eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
        + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA hCB) hCC) hCD) hCE
  refine le_trans h_five ?_
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUnconditional

section SharpAtomBoundsUnconditional

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_eigenIndexUniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomA : ℝ) (eAtomA : ℕ) (_hCatomA_nn : 0 ≤ CatomA)
    (hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_coeff : ∀ a b : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro a b
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_diffOn : ContDiffOn ℝ ∞
        (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
    have h_fderiv : ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ ∞
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  have h_main : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2 μ
          ≤ ENNReal.ofReal C *
              (ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M)
                      g r s) i‖) := by
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (F := fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (A := fun i => ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖) ?_ ?_
    · intro a i
      refine memLp_finset_sum _ (fun b _ => ?_)
      have h_atom_mem := iter_memLp_volume_restrict
        (I := I) (M := M) g r s i α P₀ (m + 1)
        (Fin.cons a (Fin.init l)) hK_meas hK_in
      rw [← hμ_def] at h_atom_mem
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (h_coeff a b) hK_compact hK_meas hK_in h_atom_mem
    · intro a
      refine eLpNorm_sum_le_const_mul_aggregate_uniform
        (μ := μ) (ι := Fin (Module.finrank ℝ E))
        (ν := TensorEigenIdx (I := I) (M := M) g r s)
        (F := fun b => fun i => fun y =>
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (A := fun i => ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) ?_ ?_
      · intro b i
        have h_atom_mem := iter_memLp_volume_restrict
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)) hK_meas hK_in
        rw [← hμ_def] at h_atom_mem
        exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
          (h_coeff a b) hK_compact hK_meas hK_in h_atom_mem
      · intro b
        obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
          eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
            (I := I) (M := M) α (h_coeff a b) hK_compact hK_meas hK_in
        rw [← hμ_def] at hC₀
        refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
        gcongr
        exact hAtomA_bd i a
  obtain ⟨C, hC_nn, hC⟩ := h_main
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine le_trans (hC i) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_assoc C CatomA]

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_eigenIndexUniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomB : ℝ) (eAtomB : ℕ) (_hCatomB_nn : 0 ≤ CatomB)
    (hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a b : Fin (Module.finrank ℝ E)),
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_main : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y) 2 μ
          ≤ ENNReal.ofReal C *
              (ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M)
                      g r s) i‖) := by
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (F := fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (A := fun i => ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖) ?_ ?_
    · intro a i
      refine memLp_finset_sum _ (fun b _ => ?_)
      have h_chosen_mem := chosenWp_memLp_volume_restrict b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (Ω := chartTargetEuclid (I := I) (M := M) α)
        hK_meas hK_in
      rw [← hμ_def] at h_chosen_mem
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
        hK_compact hK_meas hK_in h_chosen_mem
    · intro a
      refine eLpNorm_sum_le_const_mul_aggregate_uniform
        (μ := μ) (ι := Fin (Module.finrank ℝ E))
        (ν := TensorEigenIdx (I := I) (M := M) g r s)
        (F := fun b => fun i => fun y =>
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α) y)
        (A := fun i => ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) ?_ ?_
      · intro b i
        have h_chosen_mem := chosenWp_memLp_volume_restrict b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (Ω := chartTargetEuclid (I := I) (M := M) α)
          hK_meas hK_in
        rw [← hμ_def] at h_chosen_mem
        exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
          (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
            (l (Fin.last m)))
          hK_compact hK_meas hK_in h_chosen_mem
      · intro b
        obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
          eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
            (I := I) (M := M) α
            (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
              (l (Fin.last m)))
            hK_compact hK_meas hK_in
        rw [← hμ_def] at hC₀
        refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
        gcongr
        exact hAtomB_bd i a b
  obtain ⟨C, hC_nn, hC⟩ := h_main
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine le_trans (hC i) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_assoc C CatomB]

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_eigenIndexUniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomC : ℝ) (eAtomC : ℕ) (_hCatomC_nn : 0 ≤ CatomC)
    (hAtomC_bd : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans (hC₀ _) ?_
  calc
    ENNReal.ofReal C₀ * eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)) 2 μ
        ≤ ENNReal.ofReal C₀ *
          (ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) := by
          gcongr
          exact hAtomC_bd i
    _ = ENNReal.ofReal (C₀ * CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, mul_assoc C₀ CatomC]

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_eigenIndexUniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (CatomD : ℝ) (eAtomD : ℕ) (_hCatomD_nn : 0 ≤ CatomD)
    (hAtomD_bd : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (fChartEffPrev i) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              fChartEffPrev i y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans (hC₀ _) ?_
  calc
    ENNReal.ofReal C₀ * eLpNorm (fChartEffPrev i) 2 μ
        ≤ ENNReal.ofReal C₀ *
          (ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) := by
          gcongr
          exact hAtomD_bd i
    _ = ENNReal.ofReal (C₀ * CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, mul_assoc C₀ CatomD]

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_eigenIndexUniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (CatomE : ℝ) (eAtomE : ℕ) (_hCatomE_nn : 0 ≤ CatomE)
    (hAtomE_bd : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityOnEuclid (I := I) g α y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityOnEuclid_contDiffOn (I := I) g α)
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans (hC₀ _) ?_
  calc
    ENNReal.ofReal C₀ * eLpNorm
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)) 2 μ
        ≤ ENNReal.ofReal C₀ *
          (ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) := by
          gcongr
          exact hAtomE_bd i
    _ = ENNReal.ofReal (C₀ * CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, mul_assoc C₀ CatomE]

end SharpAtomBoundsUnconditional

section SharpMainBoundUnconditional

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_eLpNorm_le_eigenIndexUniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev_aesm : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      AEStronglyMeasurable (fChartEffPrev i)
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α)))
    (CatomA : ℝ) (eAtomA : ℕ) (hCatomA_nn : 0 ≤ CatomA)
    (hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomB : ℝ) (eAtomB : ℕ) (hCatomB_nn : 0 ≤ CatomB)
    (hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a b : Fin (Module.finrank ℝ E)),
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomC : ℝ) (eAtomC : ℕ) (hCatomC_nn : 0 ≤ CatomC)
    (hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomD : ℝ) (eAtomD : ℕ) (hCatomD_nn : 0 ≤ CatomD)
    (hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm (fChartEffPrev i) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomE : ℝ) (eAtomE : ℕ) (hCatomE_nn : 0 ≤ CatomE)
    (hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i)
            (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m l (fChartEffPrev i) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_eigenIndexUniform
      (I := I) (M := M) g r s α P₀ m l CatomA eAtomA hCatomA_nn hAtomA_bd
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_eigenIndexUniform
      (I := I) (M := M) g r s α P₀ m l CatomB eAtomB hCatomB_nn hAtomB_bd
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_eigenIndexUniform
      (I := I) (M := M) g r s α P₀ m l CatomC eAtomC hCatomC_nn hAtomC_bd
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_eigenIndexUniform
      (I := I) (M := M) g r s α P₀ m l fChartEffPrev CatomD eAtomD
      hCatomD_nn hAtomD_bd
  obtain ⟨CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_eigenIndexUniform
      (I := I) (M := M) g r s α P₀ m l fChartEffPrev CatomE eAtomE
      hCatomE_nn hAtomE_bd
  set e : ℕ := max (max eAtomA (max eAtomB eAtomC)) (max eAtomD eAtomE)
    with he_def
  have heA : eAtomA ≤ e := le_max_of_le_left (le_max_left _ _)
  have heB : eAtomB ≤ e := le_max_of_le_left (le_trans (le_max_left _ _)
    (le_max_right _ _))
  have heC : eAtomC ≤ e := le_max_of_le_left (le_trans (le_max_right _ _)
    (le_max_right _ _))
  have heD : eAtomD ≤ e := le_max_of_le_right (le_max_left _ _)
  have heE : eAtomE ≤ e := le_max_of_le_right (le_max_right _ _)
  have hCA_prod_nn : 0 ≤ CA * CatomA := mul_nonneg hCA_nn hCatomA_nn
  have hCB_prod_nn : 0 ≤ CB * CatomB := mul_nonneg hCB_nn hCatomB_nn
  have hCC_prod_nn : 0 ≤ CC * CatomC := mul_nonneg hCC_nn hCatomC_nn
  have hCD_prod_nn : 0 ≤ CD * CatomD := mul_nonneg hCD_nn hCatomD_nn
  have hCE_prod_nn : 0 ≤ CE * CatomE := mul_nonneg hCE_nn hCatomE_nn
  refine ⟨CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD + CE * CatomE,
    e, by positivity, fun i => ?_⟩
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  set μ : Measure EuclN := (volume : Measure EuclN).restrict K with hμ_def
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev i y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l (fChartEffPrev i) y) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hA_mem : MemLp layerA 2 μ := by
    rw [hlayerA_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_coeff : ContDiffOn ℝ ∞
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_diffOn : ContDiffOn ℝ ∞
          (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
      have h_fderiv : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
    have h_atom_mem := iter_memLp_volume_restrict
      (I := I) (M := M) g r s i α P₀ (m + 1)
      (Fin.cons a (Fin.init l)) hK_meas hK_in
    rw [← hμ_def] at h_atom_mem
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      h_coeff hK_compact hK_meas hK_in h_atom_mem
  have hB_mem : MemLp layerB 2 μ := by
    rw [hlayerB_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_chosen_mem := chosenWp_memLp_volume_restrict b
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      (Ω := chartTargetEuclid (I := I) (M := M) α)
      hK_meas hK_in
    rw [← hμ_def] at h_chosen_mem
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in h_chosen_mem
  have hC_mem : MemLp layerC 2 μ := by
    rw [hlayerC_def]
    have h_atom_mem := iter_memLp_volume_restrict
      (I := I) (M := M) g r s i α P₀ m (Fin.init l) hK_meas hK_in
    rw [← hμ_def] at h_atom_mem
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_atom_mem
  have h_aesm_D : AEStronglyMeasurable layerD μ := by
    rw [hlayerD_def]
    have h_dens_cts : ContinuousOn (densityDerivOnEuclid (I := I) g α
        (l (Fin.last m))) (chartTargetEuclid (I := I) (M := M) α) :=
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m))).continuousOn
    have h_dens_aesm : AEStronglyMeasurable
        (densityDerivOnEuclid (I := I) g α (l (Fin.last m))) μ := by
      have h_K : AEStronglyMeasurable
          (densityDerivOnEuclid (I := I) g α (l (Fin.last m)))
          ((volume : Measure EuclN).restrict K) :=
        (h_dens_cts.mono hK_in).aestronglyMeasurable hK_meas
      simpa [hμ_def, hK_def] using h_K
    exact h_dens_aesm.mul (h_prev_aesm i)
  have h_aesm_E : AEStronglyMeasurable layerE μ := by
    rw [hlayerE_def]
    have h_dens_cts : ContinuousOn (densityOnEuclid (I := I) g α)
        (chartTargetEuclid (I := I) (M := M) α) :=
      (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
    have h_dens_aesm : AEStronglyMeasurable
        (densityOnEuclid (I := I) g α) μ := by
      have h_K : AEStronglyMeasurable
          (densityOnEuclid (I := I) g α)
          ((volume : Measure EuclN).restrict K) :=
        (h_dens_cts.mono hK_in).aestronglyMeasurable hK_meas
      simpa [hμ_def, hK_def] using h_K
    have h_chosen_mem := chosenWp_memLp_volume_restrict (l (Fin.last m))
      (fChartEffPrev i) (Ω := chartTargetEuclid (I := I) (M := M) α)
      hK_meas hK_in
    rw [← hμ_def] at h_chosen_mem
    exact h_dens_aesm.mul h_chosen_mem.aestronglyMeasurable
  have hCA_i := hCA i
  have hCB_i := hCB i
  have hCC_i := hCC i
  have hCD_i := hCD i
  have hCE_i := hCE i
  have hCA_e : eLpNorm layerA 2 μ ≤
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCA_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s i
      hCA_prod_nn heA
  have hCB_e : eLpNorm layerB 2 μ ≤
      ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCB_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s i
      hCB_prod_nn heB
  have hCC_e : eLpNorm layerC 2 μ ≤
      ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCC_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s i
      hCC_prod_nn heC
  have hCD_e : eLpNorm layerD 2 μ ≤
      ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCD_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s i
      hCD_prod_nn heD
  have hCE_e : eLpNorm layerE 2 μ ≤
      ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCE_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s i
      hCE_prod_nn heE
  rw [h_num_eq]
  have h_tri :
      eLpNorm (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) 2 μ
        ≤ eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
          + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ := by
    have h_pi : (fun y => layerA y + layerB y - layerC y + layerD y + layerE y)
        = layerA + layerB - layerC + layerD + layerE := by
      funext y
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [h_pi]
    have hAB_aesm : AEStronglyMeasurable (layerA + layerB) μ :=
      hA_mem.aestronglyMeasurable.add hB_mem.aestronglyMeasurable
    have hABC_aesm : AEStronglyMeasurable (layerA + layerB - layerC) μ :=
      hAB_aesm.sub hC_mem.aestronglyMeasurable
    have hABCD_aesm : AEStronglyMeasurable
        (layerA + layerB - layerC + layerD) μ :=
      hABC_aesm.add h_aesm_D
    refine le_trans (eLpNorm_add_le hABCD_aesm h_aesm_E (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hABC_aesm h_aesm_D (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hAB_aesm
      hC_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_add_le hA_mem.aestronglyMeasurable
      hB_mem.aestronglyMeasurable (by norm_num)
  refine le_trans h_tri ?_
  have h_five :
      eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
        + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ
      ≤ ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_e hCB_e) hCC_e) hCD_e)
      hCE_e
  refine le_trans h_five ?_
  set μi : ℝ := (i.fst.val)⁻¹ ^ e with hμi_def
  have hμi_nn : 0 ≤ μi := by
    rw [hμi_def]
    have h1 : 1 ≤ (i.fst.val)⁻¹ :=
      eigen_inv_one_le (I := I) (M := M) g r s i
    have : 0 ≤ (i.fst.val)⁻¹ := le_trans zero_le_one h1
    exact pow_nonneg this _
  have h_pull :
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs
        = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
            CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) * Rhs := by
    have hp1 : 0 ≤ CA * CatomA + CB * CatomB := add_nonneg hCA_prod_nn hCB_prod_nn
    have hp2 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC :=
      add_nonneg hp1 hCC_prod_nn
    have hp3 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD :=
      add_nonneg hp2 hCD_prod_nn
    have h_sum_ofReal :
        ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e)
          = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) := by
      rw [add_mul, add_mul, add_mul, add_mul,
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCE_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCD_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCC_prod_nn hμi_nn),
        ENNReal.ofReal_add (mul_nonneg hCA_prod_nn hμi_nn)
          (mul_nonneg hCB_prod_nn hμi_nn)]
    calc ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs
        = (ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e)) * Rhs := by
          rw [add_mul, add_mul, add_mul, add_mul]
      _ = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) * Rhs := by
          rw [h_sum_ofReal]
  rw [h_pull]

end SharpMainBoundUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
