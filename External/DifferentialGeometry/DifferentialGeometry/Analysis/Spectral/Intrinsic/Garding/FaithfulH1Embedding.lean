import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.SobolevScaleSummable
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem oneMinusConnLapSmooth_toL2_inner_eq_h1_general
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) :
    ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        (v : TensorL2 0 s g)⟫_ℝ =
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩,
        smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨v⟩⟫_ℝ := by
  have h_rhs :
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩,
          smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨v⟩⟫_ℝ =
        ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ +
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply,
      UniformSpace.Completion.inner_coe, SmoothCcTensorH1.inner_def,
      tensorH1Inner_def]
    rw [show tensorL2Inner (I := I) (M := M) g 0 s
            (⟨T⟩ : SmoothCcTensorH1 g 0 s).toCcTensor.toFun
            (⟨v⟩ : SmoothCcTensorH1 g 0 s).toCcTensor.toFun =
          ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ by
        rw [UniformSpace.Completion.inner_coe]
        exact (SmoothCcTensor.inner_def _ _).symm]
  rw [h_rhs]
  have h_dir :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T).toFun
          (covGrad (I := I) (M := M) g 0 s v).toFun :=
    (tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 s T v).symm
  have h_green :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T).toFun
          (covGrad (I := I) (M := M) g 0 s v).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general
      (I := I) (M := M) g s hint T v
  have h_lhs :
      ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
            TensorL2 0 s g),
          (v : TensorL2 0 s g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 s
            (oneMinusConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_l2_Tv :
      ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_split :
      tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmooth (I := I) g 0 s T).toFun v.toFun =
        tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun -
          tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
    have h_coe :
        ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
              TensorL2 0 s g),
            (v : TensorL2 0 s g)⟫_ℝ =
          ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ -
            ⟪((rawTensorConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
                TensorL2 0 s g),
              (v : TensorL2 0 s g)⟫_ℝ := by
      rw [show (oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) =
            T - rawTensorConnLapSmooth (I := I) g 0 s T from rfl,
        UniformSpace.Completion.coe_sub, inner_sub_left]
    rw [← h_lhs, h_coe]
    rw [show ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
    rw [show ⟪((rawTensorConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
            TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
  rw [h_lhs, h_split, h_l2_Tv, h_dir, h_green]
  ring

theorem inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T : SmoothCcTensor g 0 s) (w : TensorH1Compl g 0 s) :
    ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩, w⟫_ℝ =
      ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s w⟫_ℝ := by
  set A : TensorH1Compl g 0 s → ℝ :=
    fun w => ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩, w⟫_ℝ with hA
  set B : TensorH1Compl g 0 s → ℝ :=
    fun w => ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s w⟫_ℝ with hB
  have hA_cont : Continuous A := by
    rw [hA]
    exact (innerSL ℝ
      (smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩)).continuous
  have hB_cont : Continuous B := by
    rw [hB]
    exact ((innerSL ℝ
        ((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g)).comp
      (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s)).continuous
  have h_eq_on :
      A ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) =
        B ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) := by
    funext V
    have hcoe : (V : TensorH1Compl g 0 s) =
        smoothToTensorH1Compl (I := I) (M := M) g 0 s V := rfl
    simp only [Function.comp_apply, hA, hB, hcoe]
    have hV : V = (⟨V.toCcTensor⟩ : SmoothCcTensorH1 g 0 s) := by
      cases V; rfl
    rw [hV]
    rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
    rw [← oneMinusConnLapSmooth_toL2_inner_eq_h1_general
      (I := I) (M := M) g s hint T V.toCcTensor]
  have h_dense :
      DenseRange ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) :=
    UniformSpace.Completion.denseRange_coe
  have h_AB : A = B := h_dense.equalizer hA_cont hB_cont h_eq_on
  exact congr_fun h_AB w

theorem TensorH1ComplToTensorL2_injective_of_green
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  refine ext_inner_left ℝ ?_
  intro v
  rw [inner_zero_right]
  set A : TensorH1Compl g 0 s → ℝ := fun v => ⟪v, w⟫_ℝ with hA
  have hA_cont : Continuous A := by
    rw [hA]
    exact Continuous.inner continuous_id continuous_const
  have h_eq_on :
      A ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) =
        (fun _ : SmoothCcTensorH1 g 0 s => (0 : ℝ)) := by
    funext V
    simp only [Function.comp_apply, hA]
    have hcoe : (V : TensorH1Compl g 0 s) =
        smoothToTensorH1Compl (I := I) (M := M) g 0 s V := rfl
    rw [hcoe]
    have hV : V = (⟨V.toCcTensor⟩ : SmoothCcTensorH1 g 0 s) := by cases V; rfl
    rw [hV]
    rw [inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green
      (I := I) (M := M) g s hint V.toCcTensor w]
    rw [hw, inner_zero_right]
  have h_dense :
      DenseRange ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq :
      A = (fun _ : TensorH1Compl g 0 s => (0 : ℝ)) :=
    h_dense.equalizer hA_cont continuous_const h_eq_on
  have := congr_fun h_eq v
  rw [hA] at this
  exact this

theorem TensorH1ComplToTensorL2_injective_two
    (g : SmoothRiemannianMetric I M) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 2) :=
  TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g 2
    (loweringIntertwiner_two (I := I) (M := M) g)

theorem TensorH1ComplToTensorL2_injective_three
    (g : SmoothRiemannianMetric I M) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 3) :=
  TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g 3
    (loweringIntertwiner_three (I := I) (M := M) g)

theorem smoothEigen_h1_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    smoothToTensorH1Compl (I := I) (M := M) g 0 s
        ⟨eigenvectorSmooth (I := I) (M := M) g 0 s i⟩ =
      (i.fst.val)⁻¹ •
        eigenvectorResolvent (I := I) (M := M) g 0 s i := by
  apply TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g s
    (loweringIntertwiner_gen (I := I) (M := M) g s)
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
  change (eigenvectorSmooth (I := I) (M := M) g 0 s i :
        TensorL2 0 s g) =
      TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s
        ((i.fst.val)⁻¹ •
          eigenvectorResolvent (I := I) (M := M) g 0 s i)
  rw [eigenvectorSmooth_toL2 (I := I) (M := M) g 0 s i,
    map_smul]
  exact eigenvector_eq_resolvent_smul (I := I) (M := M) g 0 s i

theorem smoothToTensorH1Compl_eigenvectorSmooth_eq
    (g : SmoothRiemannianMetric I M)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    smoothToTensorH1Compl (I := I) (M := M) g 0 2
        ⟨eigenvectorSmooth (I := I) (M := M) g 0 2 i⟩ =
      (i.fst.val)⁻¹ •
        eigenvectorResolvent (I := I) (M := M) g 0 2 i := by
  exact smoothEigen_h1_eq (I := I) (M := M) g 2 i

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorEigenIdx_val_pos
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem one_add_lambda_eq_inv_val
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s) :
    1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) i = (i.fst.val)⁻¹ := by
  have hpos : 0 < i.fst.val := tensorEigenIdx_val_pos (I := I) (M := M) i
  change 1 + tensorLaplacianEigenvalueOf i.fst.val = (i.fst.val)⁻¹
  rw [tensorLaplacianEigenvalueOf]
  field_simp
  ring

theorem oneMinus_coeff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 s))
    (T : SmoothCcTensor g 0 s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 s T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  classical
  have hb :
      tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact i =
        (eigenvectorSmooth (I := I) (M := M) g 0 s i :
          TensorL2 0 s g) := by
    rw [tensorResolventHilbertEigenbasisSigma_apply,
      eigenvectorSmooth_toL2 (I := I) (M := M) g 0 s i]
  rw [tensorL2Coeff_eq_inner, tensorL2Coeff_eq_inner, hb,
    SmoothCcTensor.toL2_apply, SmoothCcTensor.toL2_apply]
  rw [real_inner_comm
    ((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
      TensorL2 0 s g)
    (eigenvectorSmooth (I := I) (M := M) g 0 s i : TensorL2 0 s g),
    oneMinusConnLapSmooth_toL2_inner_eq_h1_general (I := I) (M := M) g s
      (loweringIntertwiner_gen (I := I) (M := M) g s) T
      (eigenvectorSmooth (I := I) (M := M) g 0 s i)]
  rw [smoothEigen_h1_eq (I := I) (M := M) g s i,
    inner_smul_right]
  rw [real_inner_comm
    (eigenvectorResolvent (I := I) (M := M) g 0 s i)
    (smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩),
    eigenvectorSmooth_weak_eigen (I := I) (M := M) g 0 s i ⟨T⟩]
  rw [show ((⟨T⟩ : SmoothCcTensorH1 g 0 s).toCcTensor : TensorL2 0 s g) =
        (T : TensorL2 0 s g) from rfl,
    real_inner_comm
      (eigenvectorSmooth (I := I) (M := M) g 0 s i : TensorL2 0 s g)
      (T : TensorL2 0 s g),
    one_add_lambda_eq_inv_val (I := I) (M := M) i]

theorem rawLap_coeff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 s))
    (T : SmoothCcTensor g 0 s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 s T)) i =
      (- Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  have h_split :
      rawTensorConnLapSmooth (I := I) g 0 s T =
        T - oneMinusConnLapSmooth (I := I) g 0 s T := by
    rw [show oneMinusConnLapSmooth (I := I) g 0 s T =
          T - rawTensorConnLapSmooth (I := I) g 0 s T from rfl]
    abel
  rw [h_split, map_sub, tensorL2Coeff_eq_inner, inner_sub_right,
    ← tensorL2Coeff_eq_inner, ← tensorL2Coeff_eq_inner,
    oneMinus_coeff (I := I) (M := M) g s h_compact T i]
  ring

theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 2 T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  exact oneMinus_coeff (I := I) (M := M) g 2 h_compact T i

theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) (k : ℕ) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ k *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ,
        tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
          (I := I) (M := M) g h_compact (oneMinusConnLapSmoothIter (I := I) g 0 2 k T) i,
        ih, pow_succ]
      ring

theorem smoothCcTensor_tensorL2Coeff_weighted_summable_even
    (g : SmoothRiemannianMetric I M) (k : ℕ) (T : SmoothCcTensor g 0 2)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
        (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i) ^ 2) := by
  classical
  have h_term :
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 T) i) ^ 2) =
        fun i => (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2
            (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) i) ^ 2 := by
    funext i
    rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
      (I := I) (M := M) g h_compact T i k]
    rw [mul_pow]
    congr 1
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [h_term]
  have h_parseval := tensorParseval_l2Coeff_ofCompact_sq
    (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))
  exact tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))

theorem smoothCcTensor_tensorL2Coeff_weighted_summable
    (g : SmoothRiemannianMetric I M) (a : ℝ) (T : SmoothCcTensor g 0 2)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i a *
        (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i) ^ 2) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (a / 2)
  have hak : a ≤ (2 * k : ℕ) := by
    have : a / 2 ≤ (k : ℝ) := hk
    push_cast
    linarith
  exact summable_tensorSobolevWeight_of_even
    (I := I) (M := M)
    (fun i => tensorL2Coeff (I := I) (M := M) h_compact
      (SmoothCcTensor.toL2 T) i)
    hak
    (smoothCcTensor_tensorL2Coeff_weighted_summable_even
      (I := I) (M := M) g k T h_compact)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
