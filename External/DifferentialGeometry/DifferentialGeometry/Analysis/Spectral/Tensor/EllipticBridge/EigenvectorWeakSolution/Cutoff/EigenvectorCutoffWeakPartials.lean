import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.EigenvectorCutoffChartPartialL2
import DifferentialGeometry.Analysis.Sobolev.Tools.WeakPartialLimit

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in

private lemma hasWeakPartialDeriv_congr_ae
    {k : Fin (Module.finrank ℝ E)} {g f g' f' : EuclN → ℝ} {Ω : Set EuclN}
    (hf : f =ᵐ[(volume : Measure EuclN).restrict Ω] f')
    (hg : g =ᵐ[(volume : Measure EuclN).restrict Ω] g')
    (h : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g f Ω) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g' f' Ω := by
  intro φ hφ hφ_supp hφ_sub
  have h_lhs :
      ∫ x in Ω, f' x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) =
        ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) := by
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]
  have h_rhs :
      ∫ x in Ω, g' x * φ x = ∫ x in Ω, g x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  rw [h_lhs, h_rhs]
  exact h φ hφ hφ_supp hφ_sub

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in

private lemma hasWeakPartialDeriv_const_smul
    {k : Fin (Module.finrank ℝ E)} {g f : EuclN → ℝ} {Ω : Set EuclN} (c : ℝ)
    (h : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g f Ω) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (fun x => c • g x) (fun x => c • f x) Ω := by
  intro φ hφ hφ_supp hφ_sub
  have h_base := h φ hφ hφ_supp hφ_sub
  have h_lhs :
      ∫ x in Ω, (c • f x) * (fderiv ℝ φ x) (EuclideanSpace.single k 1) =
        c * ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul]; ring
  have h_rhs :
      ∫ x in Ω, (c • g x) * φ x = c * ∫ x in Ω, g x * φ x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul]; ring
  rw [h_lhs, h_rhs, h_base, mul_neg]

def eigenvectorCutoffChartWeakPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  (eigenvectorCutoffChartPartialLp (I := I) (M := M)
      g r s i α P₀ k :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma cutoff_smoothApprox_smul_coe_tendsto
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
  have h_l2 :
      Filter.Tendsto
        (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n)))
        atTop
        (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))) :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_term :
      (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n))) =
        fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g) := by
    funext n
    exact TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_shadow :
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i) =
        i.fst.val •
          tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i := by
    have h_eq := eigenvector_eq_resolvent_smul
      (I := I) (M := M) g r s i
    rw [h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
  rw [h_term, h_shadow] at h_l2
  have h_smul := h_l2.const_smul (i.fst.val)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hμ_ne, one_smul] at h_smul

lemma eigenvectorCutoffChartComponentL2_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2 y := by
  classical
  rw [show tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ =
      (i.fst.val)⁻¹ •
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g) α P₀ from by
    rw [← tensorL2ChartComponentCutoffCLM_apply, map_smul,
      tensorL2ChartComponentCutoffCLM_apply]]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (((eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor) : TensorL2 r s g) α P₀)).trans ?_
  exact (tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn (I := I) (M := M)
    g r s (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor
    α P₀).const_smul (i.fst.val)⁻¹

lemma eigenvectorCutoffChartPartialLp_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (((i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α) y := by
  classical
  rw [eigenvectorCutoffChartPartialLp_approx_eq (I := I) (M := M)
    g r s i α P₀ k n]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    ((chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      α P₀.1 P₀.2 k).toLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α)))).trans ?_
  exact (MemLp.coeFn_toLp _).const_smul (i.fst.val)⁻¹

private lemma eigenvectorCutoffChartWeakPartial_approx_hasWeakPartialDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (((i.fst.val)⁻¹ •
          eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n)) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_w1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
    cutoffComponentEuclid_memW1p (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      α P₀.1 P₀.2
  have h_weak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α))
        (cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
    chosenWeakPartial'_isWeakPartial_of_mem h_w1p k
  have h_weak_smul :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (fun y => (i.fst.val)⁻¹ •
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y)
        (fun y => (i.fst.val)⁻¹ •
          cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2 y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    hasWeakPartialDeriv_const_smul (i.fst.val)⁻¹ h_weak
  refine hasWeakPartialDeriv_congr_ae ?_ ?_ h_weak_smul
  · exact (eigenvectorCutoffChartComponentL2_approx_coeFn
      (I := I) (M := M) g r s i α P₀ n).symm
  · exact (eigenvectorCutoffChartPartialLp_approx_coeFn
      (I := I) (M := M) g r s i α P₀ k n).symm

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma eigenvectorCutoffChartComponentL2_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀)
      atTop
      (𝓝 (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P₀)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M)
        g r s α P₀).continuous.tendsto _).comp
      (cutoff_smoothApprox_smul_coe_tendsto (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCutoffCLM_apply] at h_clm
  exact h_clm

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma eigenvectorCutoffChartComponent_eLpNorm_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => eLpNorm
        (((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            ((i.fst.val)⁻¹ •
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) -
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i)
            α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)) 2
        (chartL2Measure (I := I) (M := M) α))
      atTop (𝓝 0) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      ((i.fst.val)⁻¹ •
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g)) α P₀)
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      α P₀)).mp
    (eigenvectorCutoffChartComponentL2_tendsto (I := I) (M := M)
      g r s i α P₀)

private lemma eigenvectorCutoffChartPartial_eLpNorm_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => eLpNorm
        ((((i.fst.val)⁻¹ •
            eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
              (smoothToTensorH1Compl (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n)) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) -
          ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
            g r s i α P₀ k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)) 2
        (chartL2Measure (I := I) (M := M) α))
      atTop (𝓝 0) :=
  (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => (i.fst.val)⁻¹ •
      eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
    (eigenvectorCutoffChartPartialLp (I := I) (M := M)
      g r s i α P₀ k)).mp
    (eigenvectorCutoffChartPartialLp_tendsto (I := I) (M := M)
      g r s i α P₀ k)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

theorem eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P₀ k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set uApprox : ℕ → EuclN → ℝ := fun n =>
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
    with huApprox_def
  set gApprox : ℕ → EuclN → ℝ := fun n =>
    (((i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
    with hgApprox_def
  set uLim : EuclN → ℝ :=
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
    with huLim_def
  set gLim : EuclN → ℝ :=
    ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
        g r s i α P₀ k :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
    with hgLim_def
  have hu_n_memLp : ∀ n, MemLp (uApprox n) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    intro n
    simp only [huApprox_def]
    exact Lp.memLp _
  have hg_n_memLp : ∀ n, MemLp (gApprox n) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    intro n
    simp only [hgApprox_def]
    exact Lp.memLp _
  have hu_memLp : MemLp uLim 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    simp only [huLim_def]
    exact Lp.memLp _
  have hg_memLp : MemLp gLim 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    simp only [hgLim_def]
    exact Lp.memLp _
  have h_weak : ∀ n,
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (gApprox n) (uApprox n) (chartTargetEuclid (I := I) (M := M) α) := by
    intro n
    simp only [hgApprox_def, huApprox_def]
    exact eigenvectorCutoffChartWeakPartial_approx_hasWeakPartialDeriv
      (I := I) (M := M) g r s i α P₀ k n
  have h_u_tendsto :
      Filter.Tendsto
        (fun n => eLpNorm (fun x => uApprox n x - uLim x) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) := by
    have h := eigenvectorCutoffChartComponent_eLpNorm_tendsto
      (I := I) (M := M) g r s i α P₀
    simp only [huApprox_def, huLim_def]
    exact h
  have h_g_tendsto :
      Filter.Tendsto
        (fun n => eLpNorm (fun x => gApprox n x - gLim x) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) := by
    have h := eigenvectorCutoffChartPartial_eLpNorm_tendsto
      (I := I) (M := M) g r s i α P₀ k
    simp only [hgApprox_def, hgLim_def]
    exact h
  have h_closure :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k gLim uLim
        (chartTargetEuclid (I := I) (M := M) α) :=
    hasWeakPartialDeriv_of_tendsto_eLpNorm
      (d := Module.finrank ℝ E) (p := 2) (by norm_num) (by norm_num)
      hΩ_open k hu_n_memLp hg_n_memLp hu_memLp hg_memLp h_weak
      h_u_tendsto h_g_tendsto
  rw [hgLim_def, huLim_def] at h_closure
  exact h_closure

theorem eigenvectorCutoffChartWeakPartial_locally_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (eigenvectorCutoffChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  let _ := hK
  have h_memLp : MemLp (eigenvectorCutoffChartWeakPartial
      (I := I) (M := M) g r s i α P₀ k) 2
      (chartL2Measure (I := I) (M := M) α) := by
    rw [eigenvectorCutoffChartWeakPartial]
    exact Lp.memLp _
  have h_le : (volume : Measure EuclN).restrict K ≤
      chartL2Measure (I := I) (M := M) α := by
    rw [chartL2Measure]
    exact Measure.restrict_mono hK_in (le_refl _)
  exact h_memLp.mono_measure h_le

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
