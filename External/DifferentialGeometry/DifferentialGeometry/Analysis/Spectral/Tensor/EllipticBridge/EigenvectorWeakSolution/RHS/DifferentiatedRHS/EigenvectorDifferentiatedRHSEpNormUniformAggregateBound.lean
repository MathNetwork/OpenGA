import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNormRestrictedVolumeL2Bounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNormAtomEnvelopeBounds

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

section MainBoundUniformUnconditional

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
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
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) := by
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
  have h_atom_mem : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a : Fin (Module.finrank ℝ E)),
      MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2 μ := by
    intro i a
    have h0 := (h_iter i a).le_of_le (Nat.zero_le 2)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict
          (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  have h_atom_le : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s i α P₀ m l (fChartEffPrev i) := by
    intro i a
    rw [diffNumeratorAggregate]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  refine eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μ) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun i => diffNumeratorAggregate (I := I) (M := M)
      g r s i α P₀ m l (fChartEffPrev i)) ?_ ?_
  · intro a i
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem i a)
  · intro a
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun i => diffNumeratorAggregate (I := I) (M := M)
        g r s i α P₀ m l (fChartEffPrev i)) ?_ ?_
    · intro b i
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem i a)
    · intro b
      obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
        eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
          (I := I) (M := M) α (h_coeff a b) hK_compact hK_meas hK_in
      rw [← hμ_def] at hC₀
      refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
      gcongr
      exact le_trans (eLpNorm_iteratedPartial_succ_le
        (I := I) (M := M) g r s i α P₀ m l a) (h_atom_le i a)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
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
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_atom_le : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s i α P₀ m l (fChartEffPrev i) := by
    intro i a
    rw [diffNumeratorAggregate, ← hΩ_def]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω)
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_chosen_mem : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a b : Fin (Module.finrank ℝ E)),
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) 2 μ := by
    intro i a b
    have h1 : MemWkp (d := Module.finrank ℝ E) 1 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) Ω :=
      (h_iter i a).chosenWeakPartial_mem b
    have h0 := h1.le_of_le (Nat.zero_le 1)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
        (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  refine eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μ) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y)
    (fun i => diffNumeratorAggregate (I := I) (M := M)
      g r s i α P₀ m l (fChartEffPrev i)) ?_ ?_
  · intro a i
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in (h_chosen_mem i a b)
  · intro a
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y)
      (fun i => diffNumeratorAggregate (I := I) (M := M)
        g r s i α P₀ m l (fChartEffPrev i)) ?_ ?_
    · intro b i
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m)))
        hK_compact hK_meas hK_in (h_chosen_mem i a b)
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
      exact le_trans (eLpNorm_chosenWeakPartial_iteratedPartial_succ_le
        (I := I) (M := M) g r s i α P₀ m l a b) (h_atom_le i a)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) := by
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
  have h_atom_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s i α P₀ m l (fChartEffPrev i) := by
    intro i
    rw [diffNumeratorAggregate]
    exact le_trans le_add_self (le_trans le_self_add le_self_add)
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
  gcongr
  exact le_trans (eLpNorm_iteratedPartial_le
    (I := I) (M := M) g r s i α P₀ m l) (h_atom_le i)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              fChartEffPrev i y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) := by
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
  have h_atom_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (fChartEffPrev i) 2 μ ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s i α P₀ m l (fChartEffPrev i) := by
    intro i
    rw [diffNumeratorAggregate, ← hμ_def]
    exact le_add_self
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
  gcongr
  exact h_atom_le i

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityOnEuclid (I := I) g α y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_atom_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2 (fChartEffPrev i) Ω ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s i α P₀ m l (fChartEffPrev i) := by
    intro i
    rw [diffNumeratorAggregate, ← hΩ_def]
    exact le_trans le_add_self le_self_add
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityOnEuclid_contDiffOn (I := I) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α) hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
  gcongr
  have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
      (chartPouKernel (I := I) (M := M) α) := by
    rw [hμ_def, Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_le_self)) ?_
  refine le_trans (eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 0 2 Ω _) ?_
  exact le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) 0
    hΩ_open _ (l (Fin.last m))) (h_atom_le i)


omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) 1 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (_h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ chartPouKernel (I := I) (M := M) α → fChartEffPrev i y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m l (fChartEffPrev i) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m l fChartEffPrev
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m l fChartEffPrev
  obtain ⟨CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m l fChartEffPrev
  refine ⟨CA + CB + CC + CD + CE, by positivity, fun i => ?_⟩
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s i α P₀ m l (fChartEffPrev i) with hA_def
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
      have h0 := (h_iter i (m + 1) (Fin.cons a (Fin.init l))).le_of_le
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
      have h1 := ((h_iter i (m + 1)
        (Fin.cons a (Fin.init l)))).chosenWeakPartial_mem b
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
      have h0 := (h_iter i m (Fin.init l)).le_of_le (Nat.zero_le 2)
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
    have h_prev_mem : MemLp (fChartEffPrev i) 2 μ := by
      have h0 := (h_prev i).le_of_le (Nat.zero_le 1)
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
        (l (Fin.last m)) (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α)) 2 μ := by
      have h1 := (h_prev i).chosenWeakPartial_mem (l (Fin.last m))
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
  have hCA_i := hCA i
  have hCB_i := hCB i
  have hCC_i := hCC i
  have hCD_i := hCD i
  have hCE_i := hCE i
  rw [← hA_def] at hCA_i hCB_i hCC_i hCD_i hCE_i
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
    add_le_add (add_le_add (add_le_add (add_le_add hCA_i hCB_i) hCC_i) hCD_i)
      hCE_i
  refine le_trans h_five ?_
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUniformUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
