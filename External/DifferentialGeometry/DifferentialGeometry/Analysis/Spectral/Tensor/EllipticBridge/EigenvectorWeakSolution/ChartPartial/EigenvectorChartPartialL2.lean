import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.ChartPartialUniformBound

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

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_contDiff'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  classical
  rw [tensorChartComponent_def]
  refine DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M) ?_ ?_
  · exact tensorChartComponentPou_contMDiff
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
  · exact tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponent_hasCompactSupport''
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  rw [tensorChartComponent_def]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponent_tsupport_subset'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      ⊆ chartTargetEuclid (I := I) (M := M) α := by
  rw [tensorChartComponent_def]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorChartComponent_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_W1 : MemWkp (d := Module.finrank ℝ E) 1 2
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      (tensorChartComponent_contDiff' (I := I) (M := M) g r s S α Idx Jdx)
      (tensorChartComponent_hasCompactSupport'' (I := I) (M := M) g r s S α Idx Jdx)
      (tensorChartComponent_tsupport_subset' (I := I) (M := M) g r s S α Idx Jdx)
      hp_one 1
  exact MemWkp.one_iff_memW1p.mp h_W1

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartial'_tensorChartComponent_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  have h := chosenWeakPartial'_memLp_of_mem
    (tensorChartComponent_memW1p (I := I) (M := M) g r s S α Idx Jdx) k
  rwa [chartL2Measure]

private def smoothChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chosenWeakPartial'_tensorChartComponent_memLp
    (I := I) (M := M) g r s S α P₀.1 P₀.2 k).toLp _

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartPartialLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ((smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) := by
  unfold smoothChartPartialLp
  exact MemLp.coeFn_toLp _

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartPartialLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothChartPartialLp (I := I) (M := M) g r s (S₁ + S₂) α P₀ k =
      smoothChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k +
        smoothChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s
          (S₁ + S₂).toCcTensor α P₀.1 P₀.2 =
        (fun y => tensorChartComponent (I := I) (M := M)
            g r s S₁.toCcTensor α P₀.1 P₀.2 y +
          tensorChartComponent (I := I) (M := M)
            g r s S₂.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_add,
      tensorChartComponent_add (I := I) (M := M)
        g r s S₁.toCcTensor S₂.toCcTensor α P₀.1 P₀.2]
    rfl
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M) g r s
            (S₁ + S₂).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y =>
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (tensorChartComponent (I := I) (M := M)
              g r s S₁.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y +
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (tensorChartComponent (I := I) (M := M)
              g r s S₂.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartL2Measure, h_fun]
    exact chosenWeakPartial'_add_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (tensorChartComponent_memW1p (I := I) (M := M) g r s S₁ α P₀.1 P₀.2)
      (tensorChartComponent_memW1p (I := I) (M := M) g r s S₂ α P₀.1 P₀.2) k
  refine (smoothChartPartialLp_coeFn
    (I := I) (M := M) g r s (S₁ + S₂) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_add :=
    Lp.coeFn_add (smoothChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k)
      (smoothChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k)
  refine (Filter.EventuallyEq.add
    (smoothChartPartialLp_coeFn (I := I) (M := M) g r s S₁ α P₀ k)
    (smoothChartPartialLp_coeFn (I := I) (M := M) g r s S₂ α P₀ k)).symm.trans
    h_add.symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartPartialLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothChartPartialLp (I := I) (M := M) g r s (c • S) α P₀ k =
      c • smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s
          (c • S).toCcTensor α P₀.1 P₀.2 =
        (fun y => c * tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_smul,
      tensorChartComponent_smul (I := I) (M := M)
        g r s c S.toCcTensor α P₀.1 P₀.2]
    rfl
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => c * chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartL2Measure, h_fun]
    exact chosenWeakPartial'_const_smul_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (tensorChartComponent_memW1p (I := I) (M := M) g r s S α P₀.1 P₀.2) c k
  refine (smoothChartPartialLp_coeFn
    (I := I) (M := M) g r s (c • S) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_smul :=
    Lp.coeFn_smul c (smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k)
  refine Filter.EventuallyEq.trans ?_ h_smul.symm
  filter_upwards [smoothChartPartialLp_coeFn
    (I := I) (M := M) g r s S α P₀ k] with y hy
  rw [Pi.smul_apply, hy, smul_eq_mul]

private def smoothChartPartialLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) where
  toFun S := smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k
  map_add' S₁ S₂ :=
    smoothChartPartialLp_add (I := I) (M := M) g r s S₁ S₂ α P₀ k
  map_smul' c S :=
    smoothChartPartialLp_smul (I := I) (M := M) g r s c S α P₀ k

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothChartPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k S =
      smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

private lemma smoothChartPartialLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ‖smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖ ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    exists_const_sum_eLpNorm_chosenWeakPartial'_tensorChartComponent_le_uniform
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_sum := h_bound S P₀.1 P₀.2
  have h_single :
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ∑ j : Fin (Module.finrank ℝ E),
        eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (tensorChartComponent (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
    Finset.single_le_sum
      (f := fun j : Fin (Module.finrank ℝ E) =>
        eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (tensorChartComponent (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
      (fun j _ => zero_le _) (Finset.mem_univ k)
  have h_eLp :
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartL2Measure (I := I) (M := M) α) ≤
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
    rw [chartL2Measure]
    exact h_single.trans h_sum
  have h_norm_eq :
      ‖smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖ =
        (eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
          (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [smoothChartPartialLpLin_apply]
    unfold smoothChartPartialLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_rhs_lt_top :
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top).ne
  have h_toReal_le :
      (eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartL2Measure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.coe_toReal, coe_nnnorm]

private def smoothChartPartialLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k).mkContinuous
    (smoothChartPartialLpLin_norm_le (I := I) (M := M) g r s α P₀ k).choose
    (smoothChartPartialLpLin_norm_le (I := I) (M := M) g r s α P₀ k).choose_spec.2

@[simp] private lemma smoothChartPartialLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothChartPartialLpCLM (I := I) (M := M) g r s α P₀ k S =
      smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

def eigenvectorChartPartialCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    TensorH1Compl g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

theorem eigenvectorChartPartialCLM_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  unfold eigenvectorChartPartialCLM
  rw [ContinuousLinearMap.extend_eq
    (smoothChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl (I := I) (M := M) g r s) S]
  rfl

def eigenvectorChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (i.fst.val)⁻¹ •
    eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
      (eigenvectorResolvent (I := I) (M := M) g r s i)

theorem eigenvectorChartPartialLp_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (i.fst.val)⁻¹ •
        eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)) =
      (i.fst.val)⁻¹ •
        (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P₀.1 P₀.2 k).toLp
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [eigenvectorChartPartialCLM_smoothToTensorH1Compl
    (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n) α P₀ k]
  rfl

theorem eigenvectorChartPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
      atTop
      (𝓝 (eigenvectorChartPartialLp (I := I) (M := M)
        g r s i α P₀ k)) := by
  have h_clm :=
    ((eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k).continuous.tendsto
      _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_smul := h_clm.const_smul (i.fst.val)⁻¹
  simp only [Function.comp_def] at h_smul
  exact h_smul

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
