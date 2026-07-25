import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionGlobal
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.EigenvectorChartPartialL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.PouComponentBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartAtomLimits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
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
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

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

noncomputable def covPrincipalRotationCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              (partialLpLimit (I := I) (M := M) g r s i α P k :
                EuclN → ℝ) y

omit [CompleteSpace E] in
private lemma covPrincipalRotationCoeff_pouSmul_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) (y : EuclN) :
    covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α P.1 P.2) y := by
  classical
  rw [covPrincipalRotationCoeff_def]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [chartPushedRaw_tensorChartComponentRaw_pouSmul_eq (I := I) (M := M)
    g r s α (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor P.1 P.2]
  rw [principalRotationFactor]
  ring

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ =>
            memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α P k n
              (principalRotationFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))).ae_eq ?_
  exact Filter.EventuallyEq.symm (Filter.Eventually.of_forall (fun y =>
    covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s i α P₀ n y))

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covPrincipalRotationCoeffLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (principalRotationFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ P Q k l)
            (partialLpLimit (I := I) (M := M) g r s i α P k)))))

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covPrincipalRotationCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _)
      atTop
      (𝓝 ((covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _)) := by
  classical
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (n : ℕ),
      MemLp (fun y => principalRotationFactor (I := I) (M := M)
            g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          euclidPartial (E := E) a.2.2.1
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α a.1.1 a.1.2) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_partialAtom (I := I) (M := M) g r s i α a.1
      a.2.2.1 n (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (partialLpLimit (I := I) (M := M) g r s i α a.1 a.2.2.1 :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (partialLpLimit (I := I) (M := M) g r s i α a.1 a.2.2.1)
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      Filter.Tendsto (fun n => (hf a n).toLp _) atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_partialSummand (I := I) (M := M) g r s i α a.1 a.2.2.1
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  have hFn_eq : ∀ n : ℕ,
      covPrincipalRotationCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            euclidPartial (E := E) a.2.2.1
              (tensorChartComponent (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α a.1.1 a.1.2) y := by
    intro n
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s i α P₀ n y]
    simp only [Fintype.sum_prod_type]
  have hFlim_eq :
      covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (partialLpLimit (I := I) (M := M)
              g r s i α a.1 a.2.2.1 : EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ n)
    (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀)
    hFn_eq hFlim_eq

noncomputable def weightedGradCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              (componentLpLimit (I := I) (M := M) g r s i α p :
                EuclN → ℝ) y

omit [CompleteSpace E] in
private lemma weightedGradCoeff_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ l y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α p.1 p.2 y := by
  classical
  simp only [weightedGradCoeff, covLowerOrderRotationGradCoeff_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors (I := I) (M := M) g r s α
    (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor k P.1 P.2 hy]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [weightedGradFactor]
  ring

omit [CompleteSpace E] in
theorem weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ =>
            memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s i α p n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s i α P₀ l n hy)

omit [CompleteSpace E] in
theorem weightedGradCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffLimit (I := I) (M := M)
        g r s i α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (weightedGradFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q k p)
            (componentLpLimit (I := I) (M := M) g r s i α p)))))

omit [CompleteSpace E] in
theorem weightedGradCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _)
      atTop
      (𝓝 ((weightedGradCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _)) := by
  classical
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) (n : ℕ),
      MemLp (fun y => weightedGradFactor (I := I) (M := M)
            g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_componentAtom (I := I) (M := M) g r s i α
      a.2.2.2 n (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (componentLpLimit (I := I) (M := M) g r s i α a.2.2.2 :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (componentLpLimit (I := I) (M := M) g r s i α a.2.2.2)
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      Filter.Tendsto (fun n => (hf a n).toLp _) atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_componentSummand (I := I) (M := M) g r s i α a.2.2.2
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  have hFn_eq : ∀ n : ℕ,
      weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀ l
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y := by
    intro n
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s i α P₀ l n hy]
    simp only [Fintype.sum_prod_type]
  have hFlim_eq :
      weightedGradCoeffLimit (I := I) (M := M) g r s i α P₀ l
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M)
                g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (componentLpLimit (I := I) (M := M)
              g r s i α a.2.2.2 : EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ l n)
    (weightedGradCoeffLimit_memLp (I := I) (M := M) g r s i α P₀ l)
    hFn_eq hFlim_eq

noncomputable def weightedGradCoeffDivLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p))
                  y *
                (componentLpLimit (I := I) (M := M) g r s i α p :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)
                    y *
                  (partialLpLimit (I := I) (M := M) g r s i α p l :
                    EuclN → ℝ) y

omit [CompleteSpace E] in
theorem euclidPartial_weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀ l)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcomp : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α p.1 p.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s i α p n
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  have hpart : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                euclidPartial (E := E) l
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α p.1 p.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α p l n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  refine (hcomp.add hpart).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    euclidPartial_weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀ l
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
      hy)

omit [CompleteSpace E] in
theorem weightedGradCoeffDivLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffDivLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (componentLpLimit (I := I) (M := M) g r s i α p)))))
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (partialLpLimit (I := I) (M := M) g r s i α p l)))))

omit [CompleteSpace E] in
theorem weightedGradCoeffDiv_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n).toLp _)
      atTop
      (𝓝 ((weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _)) := by
  classical
  have h_comp := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      euclidPartial (E := E) l
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s i α p n
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (componentLpLimit (I := I) (M := M) g r s i α p))
    (fun P Q k p => tendsto_componentSummand (I := I) (M := M)
      g r s i α p
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s i α p n
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p)
        (componentLpLimit (I := I) (M := M) g r s i α p)))
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
        euclidPartial (E := E) l
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α p.1 p.2) y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        (partialLpLimit (I := I) (M := M) g r s i α p l :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s i α p l n
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (partialLpLimit (I := I) (M := M) g r s i α p l))
    (fun P Q k p => tendsto_partialSummand (I := I) (M := M)
      g r s i α p l
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s i α p l n
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        (partialLpLimit (I := I) (M := M) g r s i α p l)))
  have h_add := h_comp.add h_part
  have h_termN : ∀ n : ℕ,
      (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom
                  (I := I) (M := M) g r s i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      euclidPartial_weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
        g r s α P₀ l
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
        hy)
  have h_termLim :
      (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (componentLpLimit (I := I) (M := M)
                    g r s i α p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (partialLpLimit (I := I) (M := M)
                    g r s i α p l)))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffDivLimit]
  rw [show (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom
                  (I := I) (M := M) g r s i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

omit [CompleteSpace E] in
theorem weightedGradCoeffDivSum_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => ∑ l : Fin (Module.finrank ℝ E),
        (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
          g r s i α P₀ l n).toLp _)
      atTop
      (𝓝 (∑ l : Fin (Module.finrank ℝ E),
        (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
          g r s i α P₀ l).toLp _)) :=
  tendsto_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => weightedGradCoeffDiv_tendsto (I := I) (M := M)
      g r s i α P₀ l)

noncomputable def covLowerOrderRotationValueCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
                (partialLpLimit (I := I) (M := M) g r s i α P k :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M)
                      g r s i α p : EuclN → ℝ) y

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hpart : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α P k n
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))
  have hcomp : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
                  tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α p.1 p.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_finset_sum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                g r s i α p n
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p))))))
  refine (hpart.add hcomp).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    covLowerOrderRotationValueCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
      hy)

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationValueCoeffLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)
              (partialLpLimit (I := I) (M := M) g r s i α P k)))))
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_finset_sum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p)
                (componentLpLimit (I := I) (M := M)
                  g r s i α p))))))

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _)
      atTop
      (𝓝 ((covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _)) := by
  classical
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k l n y =>
      valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y)
    (flim := fun P Q k l y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
        (partialLpLimit (I := I) (M := M) g r s i α P k :
          EuclN → ℝ) y)
    (fun P Q k l n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s i α P k n
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
    (fun P Q k l => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (partialLpLimit (I := I) (M := M) g r s i α P k))
    (fun P Q k l => tendsto_partialSummand (I := I) (M := M)
      g r s i α P k
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s i α P k n
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
        (partialLpLimit (I := I) (M := M) g r s i α P k)))
  have h_comp := tendsto_sum5 (I := I) (M := M) α
    (f := fun P Q k l p n y =>
      valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k l p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
    (fun P Q k l p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s i α p n
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p))
    (fun P Q k l p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (componentLpLimit (I := I) (M := M) g r s i α p))
    (fun P Q k l p => tendsto_componentSummand (I := I) (M := M)
      g r s i α p
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s i α p n
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ P Q k l p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
        (componentLpLimit (I := I) (M := M) g r s i α p)))
  have h_add := h_part.add h_comp
  have h_termN : ∀ n : ℕ,
      (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom
                    (I := I) (M := M) g r s i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      covLowerOrderRotationValueCoeff_pouSmul_eqOn_section (I := I) (M := M)
        g r s α P₀
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
        hy)
  have h_termLim :
      (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)
                  (partialLpLimit (I := I) (M := M)
                    g r s i α P k)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p)
                    (componentLpLimit (I := I) (M := M)
                      g r s i α p))))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covLowerOrderRotationValueCoeffLimit]
  rw [show (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom
                    (I := I) (M := M) g r s i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
