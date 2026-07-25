import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

abbrev TensorCompIdx (r s : ℕ) : Type _ :=
  (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))

def chartL2Measure (α : M) : Measure EuclN :=
  (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)

private def pouTsupportSet (α : M) : Set M :=
  tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

private def pouChartKernel (α : M) : Set E :=
  (extChartAt I α) '' (pouTsupportSet (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouChartKernel_isCompact (α : M) :
    IsCompact (pouChartKernel (I := I) (M := M) α) :=
  chartImage_pouTsupport_isCompact (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouChartKernel_subset_target (α : M) :
    pouChartKernel (I := I) (M := M) α ⊆ (extChartAt I α).target :=
  chartImage_pouTsupport_subset_target (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_tsupport_subset_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) ⊆
      pouTsupportSet (I := I) (M := M) α := by
  classical
  rw [tensorChartComponentScalar_def]
  unfold tensorChartComponentPou pouTsupportSet
  have h_eq :
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x) =
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x) := by
    funext x; rfl
  rw [h_eq]
  exact tsupport_smul_subset_left
    (f := fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    (g := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_tsupport_subset_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) ⊆
      (chartAt H α).source :=
  (tensorChartComponentScalar_tsupport_subset_pouTsupport
    (I := I) (M := M) g r s S α Idx Jdx).trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_chartImage_tsupport_subset_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (extChartAt I α) ''
        (tsupport (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx)) ⊆
      pouChartKernel (I := I) (M := M) α :=
  Set.image_mono
    (tensorChartComponentScalar_tsupport_subset_pouTsupport
      (I := I) (M := M) g r s S α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  have h := tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  exact h.continuous

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (tensorChartComponent_continuous (I := I) (M := M) g r s S α Idx Jdx).measurable

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx) :=
  (tensorChartComponentScalar_contMDiff
    (I := I) (M := M) g r s S α Idx Jdx).continuous

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx) :=
  (tensorChartComponentScalar_continuous
    (I := I) (M := M) g r s S α Idx Jdx).measurable

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponent_eq_chartPushedRaw_scalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx =
      chartPushedRaw I α
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx) := by
  rw [tensorChartComponent_def, tensorChartComponentScalar_def]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponent_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) 2
            (chartL2Measure (I := I) (M := M) α) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖S‖ := by
  classical
  obtain ⟨C₁, hC₁_nn, h_scalar⟩ :=
    tensorChartComponentScalar_eLpNorm_le_uniform (I := I) (M := M) g r s α
  by_cases hker : (pouChartKernel (I := I) (M := M) α).Nonempty
  · obtain ⟨C₂, hC₂_pos, h_bridge⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform
        (I := I) (M := M) g α
        (pouChartKernel_isCompact (I := I) (M := M) α) hker
        (pouChartKernel_subset_target (I := I) (M := M) α)
        (p := 2) (by norm_num) (by norm_num)
    refine ⟨C₂ * C₁, mul_nonneg hC₂_pos.le hC₁_nn, ?_⟩
    intro S Idx Jdx
    rw [tensorChartComponent_eq_chartPushedRaw_scalar
      (I := I) (M := M) g r s S α Idx Jdx]
    have h1 :=
      h_bridge
        (tensorChartComponentScalar_measurable (I := I) (M := M) g r s S α Idx Jdx)
        (tensorChartComponentScalar_tsupport_subset_chart_source
          (I := I) (M := M) g r s S α Idx Jdx)
        (tensorChartComponentScalar_chartImage_tsupport_subset_kernel
          (I := I) (M := M) g r s S α Idx Jdx)
    have h2 := h_scalar S Idx Jdx
    have h_chain :
        eLpNorm (chartPushedRaw I α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C₂ *
            (ENNReal.ofReal C₁ * ENNReal.ofReal ‖S‖) := by
      refine h1.trans ?_
      gcongr
      rwa [SmoothCcTensor.norm_def (I := I) (M := M)]
    rw [chartL2Measure, ENNReal.ofReal_mul hC₂_pos.le, mul_assoc]
    exact h_chain
  · refine ⟨0, le_refl 0, ?_⟩
    intro S Idx Jdx
    have h_supp_empty :
        ¬ (tsupport (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx)).Nonempty := by
      intro h_ne
      exact hker
        ((h_ne.image (extChartAt I α)).mono
          (tensorChartComponentScalar_chartImage_tsupport_subset_kernel
            (I := I) (M := M) g r s S α Idx Jdx))
    have h_scalar_zero :
        tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx = (fun _ : M => (0 : ℝ)) := by
      funext x
      have hx : x ∉ tsupport (tensorChartComponentScalar
          (I := I) (M := M) g r s S α Idx Jdx) := fun hxs =>
        h_supp_empty ⟨x, hxs⟩
      exact image_eq_zero_of_notMem_tsupport hx
    have h_comp_zero :
        tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx =
          (fun _ : EuclN => (0 : ℝ)) := by
      rw [tensorChartComponent_eq_chartPushedRaw_scalar
        (I := I) (M := M) g r s S α Idx Jdx, h_scalar_zero]
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
      · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
      · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    rw [h_comp_zero, ENNReal.ofReal_zero, zero_mul]
    rw [show (fun _ : EuclN => (0 : ℝ)) = (0 : EuclN → ℝ) from rfl, eLpNorm_zero]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponent_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemLp (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    tensorChartComponent_eLpNorm_le_uniform (I := I) (M := M) g r s α
  refine ⟨?_, ?_⟩
  · exact (tensorChartComponent_continuous (I := I) (M := M)
      g r s S α Idx Jdx).aestronglyMeasurable
  · refine lt_of_le_of_lt (h_bound S Idx Jdx) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

private def smoothChartComponentLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (tensorChartComponent_memLp (I := I) (M := M) g r s S α Idx Jdx).toLp _

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ((smoothChartComponentLp (I := I) (M := M) g r s S α Idx Jdx :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := by
  unfold smoothChartComponentLp
  exact MemLp.coeFn_toLp _

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    smoothChartComponentLp (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      smoothChartComponentLp (I := I) (M := M) g r s S₁ α Idx Jdx +
        smoothChartComponentLp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  classical
  apply Lp.ext
  refine (smoothChartComponentLp_coeFn (I := I) (M := M)
    g r s (S₁ + S₂) α Idx Jdx).trans ?_
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
        tensorChartComponent (I := I) (M := M) g r s S₁ α Idx Jdx +
          tensorChartComponent (I := I) (M := M) g r s S₂ α Idx Jdx :=
    tensorChartComponent_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx
  rw [h_fun]
  have h_add :=
    (Lp.coeFn_add (smoothChartComponentLp (I := I) (M := M) g r s S₁ α Idx Jdx)
      (smoothChartComponentLp (I := I) (M := M) g r s S₂ α Idx Jdx))
  refine (Filter.EventuallyEq.add
    (smoothChartComponentLp_coeFn (I := I) (M := M) g r s S₁ α Idx Jdx)
    (smoothChartComponentLp_coeFn (I := I) (M := M) g r s S₂ α Idx Jdx)).symm.trans
    h_add.symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    smoothChartComponentLp (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • smoothChartComponentLp (I := I) (M := M) g r s S α Idx Jdx := by
  classical
  apply Lp.ext
  refine (smoothChartComponentLp_coeFn (I := I) (M := M)
    g r s (c • S) α Idx Jdx).trans ?_
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s (c • S) α Idx Jdx =
        c • tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx :=
    tensorChartComponent_smul (I := I) (M := M) g r s c S α Idx Jdx
  rw [h_fun]
  have h_smul :=
    Lp.coeFn_smul c (smoothChartComponentLp (I := I) (M := M) g r s S α Idx Jdx)
  refine ((smoothChartComponentLp_coeFn (I := I) (M := M)
    g r s S α Idx Jdx).const_smul c).symm.trans h_smul.symm

private def smoothChartComponentLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    SmoothCcTensor g r s →ₗ[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) where
  toFun S := smoothChartComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2
  map_add' S₁ S₂ :=
    smoothChartComponentLp_add (I := I) (M := M) g r s S₁ S₂ α P₀.1 P₀.2
  map_smul' c S :=
    smoothChartComponentLp_smul (I := I) (M := M) g r s c S α P₀.1 P₀.2

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothChartComponentLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (S : SmoothCcTensor g r s) :
    smoothChartComponentLpLin (I := I) (M := M) g r s α P₀ S =
      smoothChartComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2 := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g r s,
        ‖smoothChartComponentLpLin (I := I) (M := M) g r s α P₀ S‖ ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    tensorChartComponent_eLpNorm_le_uniform (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_norm_eq :
      ‖smoothChartComponentLpLin (I := I) (M := M) g r s α P₀ S‖ =
        (eLpNorm (tensorChartComponent (I := I) (M := M)
          g r s S α P₀.1 P₀.2) 2 (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [smoothChartComponentLpLin_apply]
    unfold smoothChartComponentLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_eLp := h_bound S P₀.1 P₀.2
  have h_rhs_lt_top :
      ENNReal.ofReal C * ENNReal.ofReal ‖S‖ ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have h_toReal_le :
      (eLpNorm (tensorChartComponent (I := I) (M := M)
        g r s S α P₀.1 P₀.2) 2 (chartL2Measure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * ENNReal.ofReal ‖S‖).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.toReal_ofReal (norm_nonneg _)]

private def smoothChartComponentLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    SmoothCcTensor g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (smoothChartComponentLpLin (I := I) (M := M) g r s α P₀).mkContinuous
    (smoothChartComponentLpLin_norm_le (I := I) (M := M) g r s α P₀).choose
    (smoothChartComponentLpLin_norm_le (I := I) (M := M) g r s α P₀).choose_spec.2

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothChartComponentLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (S : SmoothCcTensor g r s) :
    smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀ S =
      smoothChartComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2 := rfl

def smoothToTensorL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →L[ℝ] TensorL2 r s g :=
  UniformSpace.Completion.toComplL

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma smoothToTensorL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    smoothToTensorL2 (I := I) (M := M) g r s S = (S : TensorL2 r s g) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma denseRange_smoothToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (smoothToTensorL2 (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorL2 (I := I) (M := M) g r s :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma isUniformInducing_smoothToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorL2 (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorL2 (I := I) (M := M) g r s :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensor g r s)

def tensorL2ChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀)
    (smoothToTensorL2 (I := I) (M := M) g r s) u

def tensorL2ChartComponentCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    TensorL2 r s g →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀)
    (smoothToTensorL2 (I := I) (M := M) g r s)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorL2ChartComponentCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (u : TensorL2 r s g) :
    tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀ u =
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_smoothToTensorL2_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      (tensorChartComponent_memLp (I := I) (M := M)
        g r s S α P₀.1 P₀.2).toLp
        (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2) := by
  classical
  have h_extend :
      tensorL2ChartComponent (I := I) (M := M) g r s
          (smoothToTensorL2 (I := I) (M := M) g r s S) α P₀ =
        smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀ S := by
    unfold tensorL2ChartComponent
    exact ContinuousLinearMap.extend_eq
      (smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀)
      (e := smoothToTensorL2 (I := I) (M := M) g r s)
      (denseRange_smoothToTensorL2 (I := I) (M := M) g r s)
      (isUniformInducing_smoothToTensorL2 (I := I) (M := M) g r s) S
  rw [smoothToTensorL2_apply] at h_extend
  rw [h_extend, smoothChartComponentLpCLM_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_smoothToTensorL2_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 := by
  rw [tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M)
    g r s S α P₀]
  exact MemLp.coeFn_toLp _

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorL2ChartComponent_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (0 : TensorL2 r s g) α P₀ = 0 := by
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀]
  exact map_zero _

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u v : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s (u + v) α P₀ =
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ +
        tensorL2ChartComponent (I := I) (M := M) g r s v α P₀ := by
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀,
    ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ u,
    ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ v]
  exact map_add _ u v

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s (c • u) α P₀ =
      c • tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ := by
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀,
    ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ u]
  exact map_smul _ c u

omit [NeZero (Module.finrank ℝ E)] in
theorem continuous_tensorL2ChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Continuous (fun u : TensorL2 r s g =>
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀) := by
  have h : (fun u : TensorL2 r s g =>
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀) =
      (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀) := by
    funext u
    rw [tensorL2ChartComponentCLM_apply]
  rw [h]
  exact (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).continuous

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  tensorL2ChartComponent (I := I) (M := M) g r s u α P₀

example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    TensorL2 r s g →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
