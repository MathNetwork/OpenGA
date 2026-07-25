import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.SmoothApprox

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def eigenvectorSmoothApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℕ → SmoothCcTensorH1 g r s :=
  Classical.choose (exists_smoothApprox (I := I) (M := M) g r s i)

theorem eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
      atTop
      (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s i)) :=
  Classical.choose_spec
    (exists_smoothApprox (I := I) (M := M) g r s i)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma resolventL2_eq_smul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_eq := eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma smoothApprox_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_l2 :
      Filter.Tendsto
        (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
        atTop
        (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))) :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_term :
      (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))) =
        fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g) := by
    funext n
    exact TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
  rw [h_term, resolventL2_eq_smul_eigenvector (I := I) (M := M)
    g r s i] at h_l2
  exact h_l2

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma smoothApprox_smul_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        i)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_smul :=
    (smoothApprox_coe_tendsto (I := I) (M := M) g r s i).const_smul
      (i.fst.val)⁻¹
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rwa [smul_smul, inv_mul_cancel₀ hμ_ne, one_smul] at h_smul

theorem eigenvectorChartComponentL2_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ =
      (i.fst.val)⁻¹ •
        (tensorChartComponent_memLp (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2) := by
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor) : TensorL2 r s g) α P₀]
  rw [tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P₀]

theorem eigenvectorChartComponentL2_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2 y := by
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor) : TensorL2 r s g) α P₀]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (((eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor) : TensorL2 r s g) α P₀)).trans ?_
  exact (tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P₀).const_smul (i.fst.val)⁻¹

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

theorem eigenvectorChartComponentL2_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀)
      atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P₀)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_clm :=
    ((tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).continuous.tendsto
      _).comp
      (smoothApprox_smul_coe_tendsto (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCLM_apply] at h_clm
  exact h_clm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
