import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartPartialUniformBound

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
private lemma cutoffComponentEuclid_contDiff'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  classical
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  refine DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M) ?_ ?_
  · exact cutoffComponentScalar_contMDiff
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
  · exact cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_hasCompactSupport'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_tsupport_subset'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      ⊆ chartTargetEuclid (I := I) (M := M) α := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffComponentEuclid_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_W1 : MemWkp (d := Module.finrank ℝ E) 1 2
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      (cutoffComponentEuclid_contDiff' (I := I) (M := M) g r s S α Idx Jdx)
      (cutoffComponentEuclid_hasCompactSupport' (I := I) (M := M)
        g r s S α Idx Jdx)
      (cutoffComponentEuclid_tsupport_subset' (I := I) (M := M)
        g r s S α Idx Jdx)
      hp_one 1
  exact MemWkp.one_iff_memW1p.mp h_W1

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartial'_cutoffComponentEuclid_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  have h := chosenWeakPartial'_memLp_of_mem
    (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S α Idx Jdx) k
  rwa [chartL2Measure]

private def smoothCutoffChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chosenWeakPartial'_cutoffComponentEuclid_memLp
    (I := I) (M := M) g r s S α P₀.1 P₀.2 k).toLp _

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCutoffChartPartialLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ((smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) := by
  unfold smoothCutoffChartPartialLp
  exact MemLp.coeFn_toLp _

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCutoffChartPartialLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothCutoffChartPartialLp (I := I) (M := M) g r s (S₁ + S₂) α P₀ k =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k +
        smoothCutoffChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      cutoffComponentEuclid (I := I) (M := M) g r s
          (S₁ + S₂).toCcTensor α P₀.1 P₀.2 =
        (fun y => cutoffComponentEuclid (I := I) (M := M)
            g r s S₁.toCcTensor α P₀.1 P₀.2 y +
          cutoffComponentEuclid (I := I) (M := M)
            g r s S₂.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_add,
      cutoffComponentEuclid_add (I := I) (M := M)
        g r s S₁.toCcTensor S₂.toCcTensor α P₀.1 P₀.2]
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (S₁ + S₂).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y =>
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S₁.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y +
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S₂.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartL2Measure, h_fun]
    exact chosenWeakPartial'_add_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S₁ α P₀.1 P₀.2)
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S₂ α P₀.1 P₀.2) k
  refine (smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s (S₁ + S₂) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_add :=
    Lp.coeFn_add (smoothCutoffChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k)
      (smoothCutoffChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k)
  refine (Filter.EventuallyEq.add
    (smoothCutoffChartPartialLp_coeFn (I := I) (M := M) g r s S₁ α P₀ k)
    (smoothCutoffChartPartialLp_coeFn (I := I) (M := M) g r s S₂ α P₀ k)).symm.trans
    h_add.symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCutoffChartPartialLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothCutoffChartPartialLp (I := I) (M := M) g r s (c • S) α P₀ k =
      c • smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      cutoffComponentEuclid (I := I) (M := M) g r s
          (c • S).toCcTensor α P₀.1 P₀.2 =
        (fun y => c • cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_smul,
      cutoffComponentEuclid_smul (I := I) (M := M)
        g r s c S.toCcTensor α P₀.1 P₀.2]
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => c * chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartL2Measure]
    have h_fun' :
        cutoffComponentEuclid (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2 =
          (fun y => c * cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2 y) := by
      rw [h_fun]; funext y; rw [smul_eq_mul]
    rw [h_fun']
    exact chosenWeakPartial'_const_smul_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S α P₀.1 P₀.2) c k
  refine (smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s (c • S) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_smul :=
    Lp.coeFn_smul c (smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k)
  refine Filter.EventuallyEq.trans ?_ h_smul.symm
  filter_upwards [smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s S α P₀ k] with y hy
  rw [Pi.smul_apply, hy, smul_eq_mul]

private def smoothCutoffChartPartialLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) where
  toFun S := smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k
  map_add' S₁ S₂ :=
    smoothCutoffChartPartialLp_add (I := I) (M := M) g r s S₁ S₂ α P₀ k
  map_smul' c S :=
    smoothCutoffChartPartialLp_smul (I := I) (M := M) g r s c S α P₀ k

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothCutoffChartPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

private lemma smoothCutoffChartPartialLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ‖smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖
          ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    exists_const_sum_eLpNorm_chosenWeakPartial'_cutoffComponentEuclid_le_uniform
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_sum := h_bound S P₀.1 P₀.2
  have h_single :
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ∑ j : Fin (Module.finrank ℝ E),
        eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
    Finset.single_le_sum
      (f := fun j : Fin (Module.finrank ℝ E) =>
        eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
      (fun j _ => zero_le _) (Finset.mem_univ k)
  have h_eLp :
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartL2Measure (I := I) (M := M) α) ≤
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
    rw [chartL2Measure]
    exact h_single.trans h_sum
  have h_norm_eq :
      ‖smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖ =
        (eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
          (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [smoothCutoffChartPartialLpLin_apply]
    unfold smoothCutoffChartPartialLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_rhs_lt_top :
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top).ne
  have h_toReal_le :
      (eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartL2Measure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.coe_toReal, coe_nnnorm]

private def smoothCutoffChartPartialLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k).mkContinuous
    (smoothCutoffChartPartialLpLin_norm_le (I := I) (M := M) g r s α P₀ k).choose
    (smoothCutoffChartPartialLpLin_norm_le
      (I := I) (M := M) g r s α P₀ k).choose_spec.2

@[simp] private lemma smoothCutoffChartPartialLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k S =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToTensorH1Compl'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

def eigenvectorCutoffChartPartialCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    TensorH1Compl g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

theorem eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  unfold eigenvectorCutoffChartPartialCLM
  rw [ContinuousLinearMap.extend_eq
    (smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl' (I := I) (M := M) g r s) S]
  rfl

def eigenvectorCutoffChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (i.fst.val)⁻¹ •
    eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
      (eigenvectorResolvent (I := I) (M := M) g r s i)

theorem eigenvectorCutoffChartPartialLp_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)) =
      (i.fst.val)⁻¹ •
        (chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
          g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P₀.1 P₀.2 k).toLp
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl
    (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n) α P₀ k]
  rfl

theorem eigenvectorCutoffChartPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
      atTop
      (𝓝 (eigenvectorCutoffChartPartialLp (I := I) (M := M)
        g r s i α P₀ k)) := by
  have h_clm :=
    ((eigenvectorCutoffChartPartialCLM
        (I := I) (M := M) g r s α P₀ k).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_smul := h_clm.const_smul (i.fst.val)⁻¹
  simp only [Function.comp_def] at h_smul
  exact h_smul

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
