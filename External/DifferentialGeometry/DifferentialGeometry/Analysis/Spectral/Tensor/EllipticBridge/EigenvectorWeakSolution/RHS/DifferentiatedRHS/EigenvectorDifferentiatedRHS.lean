import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorLeibnizCommutator

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in

private lemma chosenWeakPartial'_memLp_volume_unconditional
    {Ω : Set EuclN} (k : Fin (Module.finrank ℝ E)) (w : EuclN → ℝ) :
    MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k w Ω) 2
      ((volume : Measure EuclN).restrict Ω) := by
  classical
  by_cases hw : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 w Ω
  · exact chosenWeakPartial'_memLp_of_mem hw k
  · rw [chosenWeakPartial'_of_not_mem hw k]
    exact MemLp.zero

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma one_div_densityOnEuclid_contDiffOn'
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

lemma memLp_volume_compact_contDiffOn_mul
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (hw : MemLp w 2 ((volume : Measure EuclN).restrict K)) :
    MemLp (fun y => c y * w y) 2 ((volume : Measure EuclN).restrict K) := by
  classical
  have hc_contOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hc_contOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  have hc_meas : AEStronglyMeasurable c
      ((volume : Measure EuclN).restrict K) :=
    hc_contOn_K.aestronglyMeasurable hK_meas
  have hc_ae_bd : ∀ᵐ y ∂((volume : Measure EuclN).restrict K), ‖c y‖ ≤ C :=
    (ae_restrict_iff' hK_meas).mpr (Filter.Eventually.of_forall hC_bd)
  refine ⟨hc_meas.mul hw.1, ?_⟩
  have hpt : ∀ᵐ y ∂((volume : Measure EuclN).restrict K),
      ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hc_ae_bd] with y hy
    rw [norm_mul, norm_smul]
    have hC_norm : ‖c y‖ ≤ ‖(C : ℝ)‖ := by
      rw [Real.norm_of_nonneg hC_nn]; exact hy
    exact mul_le_mul_of_nonneg_right hC_norm (norm_nonneg _)
  exact lt_of_le_of_lt
    (eLpNorm_mono_ae (μ := (volume : Measure EuclN).restrict K) hpt)
    (hw.const_smul (C : ℝ)).2

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

def eigenvectorChartComponentFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma eigenvectorChartComponentFun_memLp_volume
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  have h := Lp.memLp (tensorL2ChartComponent (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i) α P₀)
  exact h

def eigenvectorChartIteratedPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _ => eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀
  | m + 1, l =>
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (eigenvectorChartIteratedPartial g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)

omit [CompleteSpace E] in
@[simp] theorem eigenvectorChartIteratedPartial_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin 0 → Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ 0 l =
      eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀ := rfl

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) l =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α) := rfl

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_memLp_volume
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  induction m with
  | zero =>
      rw [eigenvectorChartIteratedPartial_zero]
      exact eigenvectorChartComponentFun_memLp_volume
        (I := I) (M := M) g r s i α P₀
  | succ m _ih =>
      rw [eigenvectorChartIteratedPartial_succ]
      exact chosenWeakPartial'_memLp_volume_unconditional
        (l (Fin.last m)) _

omit [CompleteSpace E] in
private lemma eigenvectorChartIteratedPartial_memLp_volume_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m l) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := eigenvectorChartIteratedPartial_memLp_volume
    (I := I) (M := M) g r s i α P₀ m l
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

def eigenvectorChartRHSDiffNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) (y : EuclN) : ℝ :=
  (∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
  + (∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
  - densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y
  + densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y
  + densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiffNumerator_memLp_volume_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemLp fChartEffPrev 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :
    MemLp (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_prev_K : MemLp fChartEffPrev 2 ((volume : Measure EuclN).restrict K) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
      (g := g) (α := α) h_prev hK_compact hK_meas hK_in
  have hA : MemLp (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2
      ((volume : Measure EuclN).restrict K) := by
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_coeff : ContDiffOn ℝ ∞
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1))
        (chartTargetEuclid (I := I) (M := M) α) := by
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
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      h_coeff hK_compact hK_meas hK_in
      (eigenvectorChartIteratedPartial_memLp_volume_compact
        (I := I) (M := M) g r s i α P₀ (m + 1)
        (Fin.cons a (Fin.init l)) hK_meas hK_in)
  have hB : MemLp (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y) 2
      ((volume : Measure EuclN).restrict K) := by
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    refine memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in ?_
    have h_global := chosenWeakPartial'_memLp_volume_unconditional
      (Ω := chartTargetEuclid (I := I) (M := M) α) b
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
    have h_eq : ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [← h_eq]
    exact h_global.restrict K
  have hC : MemLp (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) y) 2
      ((volume : Measure EuclN).restrict K) :=
    memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in
      (eigenvectorChartIteratedPartial_memLp_volume_compact
        (I := I) (M := M) g r s i α P₀ m (Fin.init l)
        hK_meas hK_in)
  have hD : MemLp (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict K) :=
    memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_prev_K
  have hE : MemLp (fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y) 2
      ((volume : Measure EuclN).restrict K) := by
    refine memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityOnEuclid_contDiffOn (I := I) g α) hK_compact hK_meas hK_in ?_
    have h_global := chosenWeakPartial'_memLp_volume_unconditional
      (Ω := chartTargetEuclid (I := I) (M := M) α) (l (Fin.last m)) fChartEffPrev
    have h_eq : ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [← h_eq]
    exact h_global.restrict K
  have h_total := ((((hA.add hB).sub hC).add hD).add hE)
  refine h_total.ae_eq (Filter.Eventually.of_forall (fun y => ?_))
  simp only [eigenvectorChartRHSDiffNumerator, Pi.add_apply,
    Pi.sub_apply]

def eigenvectorChartRHSDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _ => eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
  | m + 1, l =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
        (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m l
            (eigenvectorChartRHSDiff g r s i α P₀ m (Fin.init l)) y /
          densityOnEuclid (I := I) g α y)

omit [CompleteSpace E] in
@[simp] theorem eigenvectorChartRHSDiff_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin 0 → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ 0 l =
      eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ := rfl

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) l =
      Set.indicator (chartPouKernel (I := I) (M := M) α)
        (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m l
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)) y /
          densityOnEuclid (I := I) g α y) := rfl

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) l y = 0 := by
  rw [eigenvectorChartRHSDiff_succ, Set.indicator_of_notMem hy]

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  induction m with
  | zero =>
      rw [eigenvectorChartRHSDiff_zero]
      exact eigenvectorChartRHS_memLp_weighted
        (I := I) (M := M) g r s i α P₀
  | succ m ih =>
      classical
      set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
      have hK_compact : IsCompact K :=
        chartPouKernel_isCompact (I := I) (M := M) α
      have hK_meas : MeasurableSet K :=
        chartPouKernel_measurableSet (I := I) (M := M) α
      have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
        chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
      have h_prev := ih (Fin.init l)
      have h_num := eigenvectorChartRHSDiffNumerator_memLp_volume_compact
        (I := I) (M := M) g r s i α P₀ m l h_prev
      have h_div : MemLp (fun y => eigenvectorChartRHSDiffNumerator
          (I := I) (M := M) g r s i α P₀ m l
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)) y /
          densityOnEuclid (I := I) g α y) 2
          ((volume : Measure EuclN).restrict K) := by
        have h_eq : (fun y => eigenvectorChartRHSDiffNumerator
            (I := I) (M := M) g r s i α P₀ m l
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s i α P₀ m (Fin.init l)) y /
            densityOnEuclid (I := I) g α y) =
            fun y => (1 / densityOnEuclid (I := I) g α y) *
              eigenvectorChartRHSDiffNumerator (I := I) (M := M)
                g r s i α P₀ m l
                (eigenvectorChartRHSDiff (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l)) y := by
          funext y
          rw [one_div, mul_comm, ← div_eq_mul_inv]
        rw [h_eq]
        exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
          (one_div_densityOnEuclid_contDiffOn' (I := I) (M := M) g α)
          hK_compact hK_meas hK_in h_num
      have h_plain : MemLp (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ (m + 1) l) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
        rw [eigenvectorChartRHSDiff_succ]
        rw [memLp_indicator_iff_restrict hK_meas]
        have h_double : ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)).restrict K =
            (volume : Measure EuclN).restrict K := by
          rw [Measure.restrict_restrict hK_meas]
          congr 1
          exact Set.inter_eq_self_of_subset_left hK_in
        rw [h_double]
        exact h_div
      refine memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
        (I := I) (M := M) g α hK_compact hK_meas hK_in
        (Filter.Eventually.of_forall (fun y hy =>
          eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s i α P₀ m l hy))
        h_plain

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
