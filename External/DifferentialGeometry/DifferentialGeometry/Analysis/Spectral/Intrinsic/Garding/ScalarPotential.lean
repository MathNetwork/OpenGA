import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricAppHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricScalarSmul
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


abbrev ScalarH1Core (q : SmoothRiemannianMetric I M) :=
  tensorHs.finiteSupportSubmodule
    (I := I) (M := M) (g := q) (r := 0) (s := 0) 1

private noncomputable def scalarSmulLin
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    SmoothCcTensor q 0 0 →ₗ[Real] SmoothCcTensor q 0 0 where
  toFun := scalarSmul (I := I) (M := M) q 0 0 ζ
  map_add' := by
    intro S T
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    change (ζ : M → Real) x • (S.toSection x + T.toSection x) =
      (ζ : M → Real) x • S.toSection x +
        (ζ : M → Real) x • T.toSection x
    exact smul_add _ _ _
  map_smul' := by
    intro c S
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    change (ζ : M → Real) x • (c • S.toSection x) =
      c • ((ζ : M → Real) x • S.toSection x)
    rw [smul_smul, smul_smul, mul_comm]



noncomputable def scalarPotSec
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    ScalarH1Core (I := I) (M := M) q →ₗ[Real] SmoothCcTensor q 0 0 :=
  (scalarSmulLin (I := I) (M := M) q ζ).comp
    (finiteReprLin (I := I) (M := M) q 0 0 1)

omit [BoundarylessManifold I M] in

theorem scalarPotSec_apply
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) (x : M) :
    (scalarPotSec (I := I) (M := M) q ζ v).toSection x =
      (ζ : M → Real) x •
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x := by
  rfl



noncomputable def scalarPotCore
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    ScalarH1Core (I := I) (M := M) q →ₗ[Real] TensorL2 0 0 q :=
  (SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0)).toLinearMap.comp
    (scalarPotSec (I := I) (M := M) q ζ)

omit [BoundarylessManifold I M] in

theorem scalarPotCore_apply
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) :
    scalarPotCore (I := I) (M := M) q ζ v =
      SmoothCcTensor.toL2
        (scalarSmul (I := I) (M := M) q 0 0 ζ
          (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)) := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem scalarSmul_norm_le
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C)
    (S : SmoothCcTensor q 0 0) :
    ‖scalarSmul (I := I) (M := M) q 0 0 ζ S‖ ≤ C * ‖S‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) q
  let base : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q 0 0 x (S.toFun x) (S.toFun x)
  let weighted : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q 0 0 x
      ((scalarSmul (I := I) (M := M) q 0 0 ζ S).toFun x)
      ((scalarSmul (I := I) (M := M) q 0 0 ζ S).toFun x)
  have hpoint : ∀ x : M, weighted x ≤ C ^ 2 * base x := by
    intro x
    have hsq : ((ζ : M → Real) x) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hC).2 (hζ x)
    have hbase : 0 ≤ base x :=
      tensorInnerPointwise_nonneg (I := I) (M := M) q 0 0 x (S.toFun x)
    dsimp only [weighted, base]
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]
    nlinarith [mul_le_mul_of_nonneg_right hsq hbase]
  have hweighted : Integrable weighted μ := by
    exact (SmoothCcTensor.memL2_toFun
      (scalarSmul (I := I) (M := M) q 0 0 ζ S)).integrable_inner_self
  have hbase : Integrable base μ := by
    exact (SmoothCcTensor.memL2_toFun S).integrable_inner_self
  have hint : (∫ x, weighted x ∂μ) ≤ ∫ x, C ^ 2 * base x ∂μ :=
    integral_mono_ae hweighted (hbase.const_mul (C ^ 2))
      (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hint
  have hsq :
      ‖scalarSmul (I := I) (M := M) q 0 0 ζ S‖ ^ 2 ≤
        (C * ‖S‖) ^ 2 := by
    simpa only [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun, tensorL2Inner, weighted, base, μ, mul_pow] using hint
  have hrhs : 0 ≤ C * ‖S‖ := mul_nonneg hC (norm_nonneg S)
  nlinarith [norm_nonneg
    (scalarSmul (I := I) (M := M) q 0 0 ζ S)]

omit [BoundarylessManifold I M] in
private theorem finiteRepr_norm
    (q : SmoothRiemannianMetric I M)
    (v : ScalarH1Core (I := I) (M := M) q) :
    ‖tensorHsSmoothRepr (I := I) (M := M) v.1 v.2‖ ≤ ‖v‖ := by
  rw [← SmoothCcTensor.norm_toL2]
  rw [SmoothCcTensor.toL2_apply,
    tensorHsSmoothRepr_toL2 (I := I) (M := M)
      (show (0 : Real) ≤ 1 by norm_num) v.1 v.2,
    tensorHsToL2_apply]
  exact tensorHs.norm_toL2Fun_ofCompact_le (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
    (show (0 : Real) ≤ 1 by norm_num) v.1



omit [BoundarylessManifold I M] in
theorem scalarPotCore_norm
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C)
    (v : ScalarH1Core (I := I) (M := M) q) :
    ‖scalarPotCore (I := I) (M := M) q ζ v‖ ≤ C * ‖v‖ := by
  rw [scalarPotCore_apply, SmoothCcTensor.norm_toL2]
  calc
    _ ≤ C * ‖tensorHsSmoothRepr (I := I) (M := M) v.1 v.2‖ :=
      scalarSmul_norm_le (I := I) (M := M) q ζ hC hζ _
    _ ≤ C * ‖v‖ :=
      mul_le_mul_of_nonneg_left (finiteRepr_norm (I := I) (M := M) q v) hC

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [IsManifold I ∞ M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private theorem exists_pot_bound
    (ζ : C^∞⟮I, M; Real⟯) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : M, |(ζ : M → Real) x| ≤ C := by
  classical
  have hcont : Continuous (fun x : M => |(ζ : M → Real) x|) :=
    continuous_abs.comp ζ.contMDiff.continuous
  have hcompact := (isCompact_univ (X := M)).image hcont
  obtain ⟨C₀, hC₀⟩ := hcompact.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  exact (hC₀ ⟨x, Set.mem_univ _, rfl⟩).trans (le_max_left _ _)



noncomputable def scalarPotOp
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    tensorHs (I := I) (M := M) q 0 0 1 →L[Real] TensorL2 0 0 q :=
  (scalarPotCore (I := I) (M := M) q ζ).extendOfNorm
    (ScalarH1Core (I := I) (M := M) q).subtype



omit [BoundarylessManifold I M] in
theorem scalarPotOp_core
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) :
    scalarPotOp (I := I) (M := M) q ζ v.1 =
      scalarPotCore (I := I) (M := M) q ζ v := by
  obtain ⟨C, hC, hζ⟩ := exists_pot_bound (I := I) (M := M) ζ
  have hdense : DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C, ?_⟩
  intro w
  simpa only [Submodule.coe_subtype] using
    scalarPotCore_norm (I := I) (M := M) q ζ hC hζ w



omit [BoundarylessManifold I M] in
theorem scalarPotOp_norm
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C) :
    ‖scalarPotOp (I := I) (M := M) q ζ‖ ≤ C := by
  have hdense : DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  apply LinearMap.opNorm_extendOfNorm_le hdense hC
  intro w
  simpa only [Submodule.coe_subtype] using
    scalarPotCore_norm (I := I) (M := M) q ζ hC hζ w

private noncomputable def scalarL2ToH0
    (q : SmoothRiemannianMetric I M) :
    TensorL2 0 0 q →ₗᵢ[Real] tensorHs (I := I) (M := M) q 0 0 0 :=
  (tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) q 0 0)).symm.toLinearIsometry



noncomputable def scalarPotH0
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    tensorHs (I := I) (M := M) q 0 0 1 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 0 :=
  (scalarL2ToH0 (I := I) (M := M) q).toContinuousLinearMap.comp
    (scalarPotOp (I := I) (M := M) q ζ)

omit [BoundarylessManifold I M] in

@[simp] theorem scalarPotH0_apply
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : tensorHs (I := I) (M := M) q 0 0 1) :
    scalarPotH0 (I := I) (M := M) q ζ v =
      (tensorHsZeroEquivL2 (I := I) (M := M)
        (tensorResolventL2_isCompactOperator
          (I := I) (M := M) q 0 0)).symm
        (scalarPotOp (I := I) (M := M) q ζ v) := rfl



omit [BoundarylessManifold I M] in
theorem scalarPotH0_test
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (u : tensorHs (I := I) (M := M) q 0 0 1)
    (v : ScalarH1Core (I := I) (M := M) q) :
    inner Real
        (tensorHsZeroEquivL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0)
          (scalarPotH0 (I := I) (M := M) q ζ u))
        (tensorHsToL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0)
          (show (0 : Real) ≤ 1 by norm_num) v.1) =
      inner Real
        (tensorHsToL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0)
          (show (0 : Real) ≤ 1 by norm_num) u)
        (scalarPotCore (I := I) (M := M) q ζ v) := by
  let J := tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
  let inc := tensorHsToL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
    (show (0 : Real) ≤ 1 by norm_num)
  have hdense :
      DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  change inner Real (J (scalarPotH0 (I := I) (M := M) q ζ u))
      (inc v.1) =
    inner Real (inc u) (scalarPotCore (I := I) (M := M) q ζ v)
  refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
  · exact ((innerSL Real).flip (inc v.1)).continuous.comp
      (J.continuous.comp
        (scalarPotH0 (I := I) (M := M) q ζ).continuous)
  · exact ((innerSL Real).flip
      (scalarPotCore (I := I) (M := M) q ζ v)).continuous.comp
        inc.continuous
  · intro w
    rw [scalarPotH0_apply, LinearIsometryEquiv.apply_symm_apply]
    change inner Real (scalarPotOp (I := I) (M := M) q ζ w.1)
        (inc v.1) =
      inner Real (inc w.1) (scalarPotCore (I := I) (M := M) q ζ v)
    rw [scalarPotOp_core]
    rw [← tensorHsSmoothRepr_toL2 (I := I) (M := M)
        (show (0 : Real) ≤ 1 by norm_num) v.1 v.2,
      ← tensorHsSmoothRepr_toL2 (I := I) (M := M)
        (show (0 : Real) ≤ 1 by norm_num) w.1 w.2,
      scalarPotCore_apply, scalarPotCore_apply]
    change inner Real
        (SmoothCcTensor.toL2
          (scalarSmul (I := I) (M := M) q 0 0 ζ
            (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)))
        (SmoothCcTensor.toL2
          (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)) =
      inner Real
        (SmoothCcTensor.toL2
          (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2))
        (SmoothCcTensor.toL2
          (scalarSmul (I := I) (M := M) q 0 0 ζ
            (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)))
    rw [SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_toL2]
    rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
    unfold tensorL2Inner
    apply integral_congr_ae
    filter_upwards with x
    rw [scalarSmul_toFun_apply, scalarSmul_toFun_apply,
      tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]

omit [BoundarylessManifold I M] in

theorem scalarPotH0_norm
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    ‖scalarPotH0 (I := I) (M := M) q ζ‖ =
      ‖scalarPotOp (I := I) (M := M) q ζ‖ := by
  unfold scalarPotH0
  exact (scalarL2ToH0 (I := I) (M := M) q).norm_toContinuousLinearMap_comp

omit [BoundarylessManifold I M] in
private theorem scalarPotCore_sub
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) :
    scalarPotCore (I := I) (M := M) q ζ v -
        scalarPotCore (I := I) (M := M) q η v =
      scalarPotCore (I := I) (M := M) q (ζ - η) v := by
  rw [scalarPotCore_apply, scalarPotCore_apply, scalarPotCore_apply, ← map_sub]
  congr 1
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change (ζ : M → Real) x •
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x -
      (η : M → Real) x •
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x =
    ((ζ : M → Real) x - (η : M → Real) x) •
      (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x
  exact (sub_smul _ _ _).symm



omit [BoundarylessManifold I M] in
theorem scalarPot_pair_core
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C)
    (hζη : ∀ x : M, |(ζ : M → Real) x - (η : M → Real) x| ≤ C)
    (v : ScalarH1Core (I := I) (M := M) q) :
    ‖scalarPotCore (I := I) (M := M) q ζ v -
        scalarPotCore (I := I) (M := M) q η v‖ ≤ C * ‖v‖ := by
  rw [scalarPotCore_sub]
  apply scalarPotCore_norm (I := I) (M := M) q (ζ - η) hC
  intro x
  change |(ζ : M → Real) x - (η : M → Real) x| ≤ C
  exact hζη x



omit [BoundarylessManifold I M] in
theorem scalarPot_pair_norm
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C)
    (hζη : ∀ x : M, |(ζ : M → Real) x - (η : M → Real) x| ≤ C) :
    ‖scalarPotOp (I := I) (M := M) q ζ -
        scalarPotOp (I := I) (M := M) q η‖ ≤ C := by
  have hdense : DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  apply (scalarPotOp (I := I) (M := M) q ζ -
    scalarPotOp (I := I) (M := M) q η).opNorm_le_bound hC
  intro u
  refine hdense.induction_on u ?_ ?_
  · exact isClosed_le
      (scalarPotOp (I := I) (M := M) q ζ -
        scalarPotOp (I := I) (M := M) q η).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro v
    rw [ContinuousLinearMap.sub_apply]
    simp only [Submodule.coe_subtype]
    rw [scalarPotOp_core (I := I) (M := M) q ζ v,
      scalarPotOp_core (I := I) (M := M) q η v]
    exact scalarPot_pair_core (I := I) (M := M) q ζ η hC hζη v



omit [BoundarylessManifold I M] in
theorem scalarPotH0_pair
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C)
    (hζη : ∀ x : M, |(ζ : M → Real) x - (η : M → Real) x| ≤ C) :
    ‖scalarPotH0 (I := I) (M := M) q ζ -
        scalarPotH0 (I := I) (M := M) q η‖ ≤ C := by
  apply (scalarPotH0 (I := I) (M := M) q ζ -
    scalarPotH0 (I := I) (M := M) q η).opNorm_le_bound hC
  intro u
  rw [ContinuousLinearMap.sub_apply]
  change ‖(scalarL2ToH0 (I := I) (M := M) q)
          (scalarPotOp (I := I) (M := M) q ζ u) -
        (scalarL2ToH0 (I := I) (M := M) q)
          (scalarPotOp (I := I) (M := M) q η u)‖ ≤ C * ‖u‖
  rw [← map_sub, LinearIsometry.norm_map]
  change ‖(scalarPotOp (I := I) (M := M) q ζ -
      scalarPotOp (I := I) (M := M) q η) u‖ ≤ C * ‖u‖
  calc
    _ ≤ ‖scalarPotOp (I := I) (M := M) q ζ -
          scalarPotOp (I := I) (M := M) q η‖ * ‖u‖ :=
      (scalarPotOp (I := I) (M := M) q ζ -
        scalarPotOp (I := I) (M := M) q η).le_opNorm u
    _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right
      (scalarPot_pair_norm (I := I) (M := M) q ζ η hC hζη) (norm_nonneg u)

private theorem smulHs_bound
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) (m : ℕ) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ U : SmoothCcTensor q 0 0,
        ‖ccTensorToHs (I := I) (M := M) q 0 (m : Real)
            (scalarSmul (I := I) (M := M) q 0 0 ζ U)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) q 0 (m : Real) U‖ := by
  let zeta : Real → C^∞⟮I, M; Real⟯ := fun _ => ζ
  have hzeta :
      ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
        (fun p : M × Real => (zeta p.2 : M → Real) p.1)
        ((Set.univ : Set M) ×ˢ (Set.univ : Set Real)) := by
    exact (ζ.contMDiff.comp contMDiff_fst).contMDiffOn
  obtain ⟨C, hC, hbound⟩ :=
    smul_hs_unif (I := I) (M := M) q zeta
      (K := ({0} : Set Real)) (S := Set.univ)
      isCompact_singleton (Set.subset_univ _) hzeta m
  refine ⟨C, hC, ?_⟩
  intro U
  simpa only [zeta] using hbound 0 (Set.mem_singleton 0) U



noncomputable def scalarPotHs
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) (m : ℕ) :
    tensorHs (I := I) (M := M) q 0 0 (m : Real) →L[Real]
      tensorHs (I := I) (M := M) q 0 0 (m : Real) :=
  ((ccToHsLin (I := I) (M := M) q 0 (m : Real)).comp
      (scalarSmulLin (I := I) (M := M) q ζ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) q 0 (m : Real))



theorem scalarPotHs_core
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) (m : ℕ)
    (U : SmoothCcTensor q 0 0) :
    scalarPotHs (I := I) (M := M) q ζ m
        (ccTensorToHs (I := I) (M := M) q 0 (m : Real) U) =
      ccTensorToHs (I := I) (M := M) q 0 (m : Real)
        (scalarSmul (I := I) (M := M) q 0 0 ζ U) := by
  obtain ⟨C, hC, hbound⟩ := smulHs_bound (I := I) (M := M) q ζ m
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 (m : Real)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  change
    (((ccToHsLin (I := I) (M := M) q 0 (m : Real)).comp
        (scalarSmulLin (I := I) (M := M) q ζ)).extendOfNorm
      (ccToHsLin (I := I) (M := M) q 0 (m : Real)))
        ((ccToHsLin (I := I) (M := M) q 0 (m : Real)) U) =
      ((ccToHsLin (I := I) (M := M) q 0 (m : Real)).comp
        (scalarSmulLin (I := I) (M := M) q ζ)) U
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C, ?_⟩
  intro W
  simpa only [ccToHsLin_apply, scalarSmulLin, LinearMap.comp_apply] using hbound W



theorem scalarPotHs_app
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) (m : ℕ)
    (U : tensorHs (I := I) (M := M) q 0 0 (m : Real)) :
    scalarPotHs (I := I) (M := M) q ζ m U =
      appHs q 0 0 m (scalarCc (I := I) (M := M) q ζ) U := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 (m : Real)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  refine hdense.induction_on U (isClosed_eq ?_ ?_) ?_
  · exact (scalarPotHs (I := I) (M := M) q ζ m).continuous
  · exact (appHs q 0 0 m (scalarCc (I := I) (M := M) q ζ)).continuous
  · intro W
    simp only [ccToHsLin_apply]
    rw [scalarPotHs_core, appHs_core, app_scalarCc]

private theorem ccHs_inc
    (q : SmoothRiemannianMetric I M) {τ σ : Real} (hτσ : τ ≤ σ)
    (U : SmoothCcTensor q 0 0) :
    tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0) hτσ
        (ccTensorToHs (I := I) (M := M) q 0 σ U) =
      ccTensorToHs (I := I) (M := M) q 0 τ U := by
  apply tensorHs.ext
  funext i
  simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

private theorem scalarPotH0_cc
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (U : SmoothCcTensor q 0 0) :
    scalarPotH0 (I := I) (M := M) q ζ
        (ccTensorToHs (I := I) (M := M) q 0 1 U) =
      ccTensorToHs (I := I) (M := M) q 0 0
        (scalarSmul (I := I) (M := M) q 0 0 ζ U) := by
  have hn1 : ((1 : ℕ) : Real) ≤ (1 : Real) := by norm_num
  have h0n : (0 : Real) ≤ ((1 : ℕ) : Real) := by norm_num
  have hdense : DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  have hcompat (u : tensorHs (I := I) (M := M) q 0 0 1) :
      scalarPotH0 (I := I) (M := M) q ζ u =
        tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
          h0n
          (scalarPotHs (I := I) (M := M) q ζ 1
            (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
              hn1 u)) := by
    refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
    · exact (scalarPotH0 (I := I) (M := M) q ζ).continuous
    · exact
        (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
          h0n).continuous.comp
            ((scalarPotHs (I := I) (M := M) q ζ 1).continuous.comp
              (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
                hn1).continuous)
    · intro v
      let S : SmoothCcTensor q 0 0 :=
        tensorHsSmoothRepr (I := I) (M := M) v.1 v.2
      let W : SmoothCcTensor q 0 0 :=
        scalarSmul (I := I) (M := M) q 0 0 ζ S
      have hrepr :
          ccTensorToHs (I := I) (M := M) q 0 1 S = v.1 := by
        simpa only [ccToHsLin_apply, S] using
          ccToHsLin_repr (I := I) (M := M) q 0
            (show (0 : Real) ≤ 1 by norm_num) v.1 v.2
      have hreprn :
          tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
              hn1 v.1 =
            ccTensorToHs (I := I) (M := M) q 0 ((1 : ℕ) : Real) S := by
        rw [← hrepr]
        exact ccHs_inc (I := I) (M := M) q hn1 S
      calc
        scalarPotH0 (I := I) (M := M) q ζ v.1 =
            (tensorHsZeroEquivL2 (I := I) (M := M)
              (tensorResolventL2_isCompactOperator
                (I := I) (M := M) q 0 0)).symm
              (SmoothCcTensor.toL2 W) := by
          rw [scalarPotH0_apply, scalarPotOp_core, scalarPotCore_apply]
        _ = ccTensorToHs (I := I) (M := M) q 0 0 W := by
          apply tensorHs.ext
          funext i
          rw [tensorHsZeroEquivL2_symm_coeff, ccTensorToHs_coeff]
        _ = tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
              h0n
              (ccTensorToHs (I := I) (M := M) q 0 ((1 : ℕ) : Real) W) :=
          (ccHs_inc (I := I) (M := M) q
            h0n W).symm
        _ = tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
              h0n
              (scalarPotHs (I := I) (M := M) q ζ 1
                (ccTensorToHs (I := I) (M := M) q 0 ((1 : ℕ) : Real) S)) := by
          rw [scalarPotHs_core]
        _ = tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
              h0n
              (scalarPotHs (I := I) (M := M) q ζ 1
                (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
                  hn1 v.1)) := by
          rw [hreprn]
  calc
    scalarPotH0 (I := I) (M := M) q ζ
        (ccTensorToHs (I := I) (M := M) q 0 1 U) =
      tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
        h0n
        (scalarPotHs (I := I) (M := M) q ζ 1
          (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
            hn1 (ccTensorToHs (I := I) (M := M) q 0 1 U))) :=
      hcompat _
    _ = tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
        h0n
        (ccTensorToHs (I := I) (M := M) q 0 ((1 : ℕ) : Real)
          (scalarSmul (I := I) (M := M) q 0 0 ζ U)) := by
      rw [ccHs_inc (I := I) (M := M) q hn1,
        scalarPotHs_core]
    _ = ccTensorToHs (I := I) (M := M) q 0 0
        (scalarSmul (I := I) (M := M) q 0 0 ζ U) :=
      ccHs_inc (I := I) (M := M) q h0n _



theorem scalarPotHs_inc
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (m : ℕ) (hm : (1 : Real) ≤ (m : Real))
    (u : tensorHs (I := I) (M := M) q 0 0 (m : Real)) :
    tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
        (zero_le_one.trans hm)
        (scalarPotHs (I := I) (M := M) q ζ m u) =
      scalarPotH0 (I := I) (M := M) q ζ
        (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
          hm u) := by
  have h0m : (0 : Real) ≤ (m : Real) := zero_le_one.trans hm
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 (m : Real)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 h0m
  refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
  · exact
      (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
        h0m).continuous.comp
          (scalarPotHs (I := I) (M := M) q ζ m).continuous
  · exact
      (scalarPotH0 (I := I) (M := M) q ζ).continuous.comp
        (tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
          hm).continuous
  · intro U
    simp only [ccToHsLin_apply]
    rw [scalarPotHs_core,
      ccHs_inc (I := I) (M := M) q h0m,
      ccHs_inc (I := I) (M := M) q hm,
      scalarPotH0_cc]



theorem scalarPotHs_unif
    (q : SmoothRiemannianMetric I M)
    (zeta : Real → C^∞⟮I, M; Real⟯) {S K : Set Real}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hzeta : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ S)) (m : ℕ) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ K → ‖scalarPotHs (I := I) (M := M) q (zeta t) m‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    smul_hs_unif (I := I) (M := M) q zeta hK hKS hzeta m
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 (m : Real)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  unfold scalarPotHs
  apply LinearMap.opNorm_extendOfNorm_le hdense hC
  intro U
  simpa only [ccToHsLin_apply, scalarSmulLin, LinearMap.comp_apply] using
    hbound t ht U

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
