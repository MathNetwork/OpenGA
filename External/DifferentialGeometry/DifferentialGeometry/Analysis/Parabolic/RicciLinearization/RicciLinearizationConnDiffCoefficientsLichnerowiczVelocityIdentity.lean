import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Tensor.Multilinear.ModelProductContinuousBilinear
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficientsFibreOperators


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section NormedVelocitySecondCovGrad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def velocitySecondCovGradCc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection
  hasCompactSupport :=
    (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).hasCompactSupport


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_smul_two (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_add_two (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x =
      unitModel (I := I) (M := M) g₀ 2 S x + unitModel (I := I) (M := M) g₀ 2 S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_add_two_apply (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  rw [unitModel_add_two, ContinuousMultilinearMap.add_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_sub_two (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (b : M) (p q : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (T - T') b p q =
      smoothCcTensorBilinForm (I := I) g₀ T b p q - smoothCcTensorBilinForm (I := I) g₀ T' b p q := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  have hmulti : (ccTensorMultilinear (I := I) g₀ (T - T') b : Tensor0SBundle.Tensor0SSpace 2 I b) =
      (ccTensorMultilinear (I := I) g₀ T b : Tensor0SBundle.Tensor0SSpace 2 I b)
        - (ccTensorMultilinear (I := I) g₀ T' b : Tensor0SBundle.Tensor0SSpace 2 I b) := by
    unfold ccTensorMultilinear
    rw [SmoothCcTensor.toSection_sub]
    rfl
  have hmodel : ccTensorModel (I := I) g₀ (T - T') b =
      ccTensorModel (I := I) g₀ T b - ccTensorModel (I := I) g₀ T' b := by
    unfold ccTensorModel
    rw [hmulti, Tensor0SBundle.Tensor0SSpace.toModel_sub]
  rw [hmodel, ContinuousMultilinearMap.sub_apply]

end NormedVelocitySecondCovGrad


private lemma zero_mem_realizedSmallSet' {δ δ' : ℝ} (hδ'_lt : δ' < 1) :
    (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') := by
  change |1 - (0 : ℝ)| * δ' + |(0 : ℝ)| * δ < 1
  rw [sub_zero, abs_one, abs_zero, one_mul, zero_mul, add_zero]
  exact hδ'_lt


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma dualToCotangent_smul_c {x : M} (c : ℝ) (α : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (c • α)
      = c • dualToCotangent (I := I) (x := x) α := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_smul, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ccTensorBilin_smul_c (g : SmoothRiemannianMetric I M) (c : ℝ)
    (S : SmoothCcTensor g 0 2) (b : M) (p q : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g (c • S) b p q = c * smoothCcTensorBilinForm (I := I) g S b p q := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply]
  have hmulti : (ccTensorMultilinear (I := I) g (c • S) b : Tensor0SBundle.Tensor0SSpace 2 I b) =
      c • (ccTensorMultilinear (I := I) g S b : Tensor0SBundle.Tensor0SSpace 2 I b) := by
    unfold ccTensorMultilinear
    rw [SmoothCcTensor.toSection_smul]
    rfl
  have hmodel : ccTensorModel (I := I) g (c • S) b = c • ccTensorModel (I := I) g S b := by
    unfold ccTensorModel
    rw [hmulti, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  rw [hmodel, ContinuousMultilinearMap.smul_apply, smul_eq_mul]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_smul_c (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_smul_gen (g : SmoothRiemannianMetric I M) {n : ℕ}
    (c : ℝ) (W : SmoothCcTensor g 0 n) (x : M) :
    unitModel (I := I) (M := M) g n (c • W) x =
      c • unitModel (I := I) (M := M) g n W x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]


private lemma koszulPair_eq_smul_dual_linearizedKoszul
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (Zf Yf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    koszulCovGradCovec (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedFam (I := I) g₀ T T' hδ hδ' 0)
        Zf Yf b =
      ((0 : ℝ) - s) • dualToCotangent (I := I)
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Yf b) (Zf b)) := by
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs)
  have h0mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    zero_mem_realizedSmallSet' hδ'_lt
  have hcd := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    (s₀ := s) (s := 0) hsmem h0mem b (Yf b) (Zf b)
  rw [koszulCovGradCovec, hcd]
  have hlm : ((realizedFam (I := I) g₀ T T' hδ hδ' 0).inner b
      (((0 : ℝ) - s) •
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 0) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Yf b) (Zf b)))).toLinearMap =
      ((0 : ℝ) - s) •
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Yf b) (Zf b)) := by
    apply LinearMap.ext
    intro z
    rw [LinearMap.smul_apply]
    change ((realizedFam (I := I) g₀ T T' hδ hδ' 0).inner b
      (((0 : ℝ) - s) • DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 0) b _)) z = _
    rw [map_smul, ContinuousLinearMap.smul_apply, DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp]
  rw [hlm, dualToCotangent_smul_c]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitEval_bilin_eq (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (y : M) (m : Fin 2 → TangentSpace I y) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
          S.toSection y) (unitZeroSec (I := I) (M := M) y)) m =
      smoothCcTensorBilinForm (I := I) g S y (m 0) (m 1) := by
  have hm : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ccTensorBilin_apply]
  rw [show ccTensorModel (I := I) g S y ![m 0, m 1] =
      Tensor0SBundle.Tensor0SSpace.toModel
        (ccTensorMultilinear (I := I) g S y : Tensor0SBundle.Tensor0SSpace 2 I y)
        ![m 0, m 1] from rfl]
  conv_lhs => rw [hm]
  rfl


omit [BoundarylessManifold I M] in
private lemma velocity_unitEval_domDomCongr_swap
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) :
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y) =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
          (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
            (unitZeroSec (I := I) (M := M) y)) := by
  apply Tensor0SBundle.tensor0SSpace_ext 2 y
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hswapargs : (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y)) (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) =
      smoothCcTensorBilinForm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (m 1) (m 0) := by
    rw [unitEval_bilin_eq (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y]
    congr 1
  rw [unitEval_bilin_eq (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y]
  rw [hswapargs]
  rw [show smoothCcTensorBilinForm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (m 0) (m 1) =
      smoothCcTensorBilinForm (I := I) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) y (m 0) (m 1) from rfl]
  rw [show smoothCcTensorBilinForm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (m 1) (m 0) =
      smoothCcTensorBilinForm (I := I) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) y (m 1) (m 0) from rfl]
  rw [ccTensorBilin_symmS, ccTensorBilin_symmS,
    ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  ring

section NormedUnitEvaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitEval_tensorSectionMDiffAt (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) :
    TensorSectionMDiffAt (I := I) n
      (fun y : M =>
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y from
          W.toSection y) (unitZeroSec (I := I) (M := M) y)) x := by
  have hsm := ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff
  exact ((hsm x).mdifferentiableAt (by simp))


omit [NeZero (Module.finrank ℝ E)] in
lemma unitModel_covGrad_eval (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) (v : Fin (n + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (n + 1) (covGrad (I := I) (M := M) g 0 n W) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        (show Tensor0SBundle.Tensor0SSpace n I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace n I y from
                W.toSection y) (unitZeroSec (I := I) (M := M) y)) x (v 0))
        (Matrix.vecTail v) := by
  rw [unitModel]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 n W x
    (unitZeroSec (I := I) (M := M) x) v]
  congr 1
  rw [tensorCovDerivAt_def]
  rw [TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) 0 n
    (LeviCivita (I := I) g) W.toSection (unitZeroSec (I := I) (M := M)) x (v 0)]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
      (fun y : M => unitZeroSec (I := I) (M := M) y) x (v 0)) = 0 from
    Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x (v 0)]
  rw [map_zero, sub_zero]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma inverseMetricSharpFib_dualToCotangent (g : SmoothRiemannianMetric I M)
    (x : M) (φ : Module.Dual ℝ (TangentSpace I x)) :
    inverseMetricSharpFib (I := I) g x (dualToCotangent (I := I) φ) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g x φ := by
  rw [inverseMetricSharpFib_apply, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToCLM_smul_c {x : M} (c : ℝ) (β : Tensor0SBundle.Tensor0SSpace 1 I x) :
    cotangentToCLM (I := I) (c • β) = c • cotangentToCLM (I := I) β := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.smul_apply]
  rw [show (cotangentToCLM (I := I) (c • β)) w = cotangentToDual (I := I) (c • β) w from rfl]
  rw [show (cotangentToCLM (I := I) β) w = cotangentToDual (I := I) β w from rfl]
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rfl

end NormedUnitEvaluation

section NormedToModelApply

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma toModel_apply_tangent {n : ℕ} (x : M)
    (D : Tensor0SBundle.Tensor0SSpace n I x) (m : Fin n → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel D m =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin n => TangentSpace I x) ℝ from D) m := rfl

end NormedToModelApply


private theorem cotangentCov_linearizedKoszul_eval
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))).toFun
        (fun b : M => cotangentToCLM (I := I)
          (dualToCotangent (I := I)
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Y b) (Z b)))) x (X x)) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
                (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
                (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
              (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
              ![(LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                  (fun b => Z b) x (X x), Y x, ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![Z x, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Y b) x (X x), ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![(LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Y b) x (X x), Z x, ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![Y x, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Z b) x (X x), ζ]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![ζ, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Z b) x (X x), Y x]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![ζ, Z x, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Y b) x (X x)]) := by
  classical
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs)
  have h0mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    zero_mem_realizedSmallSet' hδ'_lt
  have hsne : (0 : ℝ) - s ≠ 0 := by
    have h0 : (0 : ℝ) - s < 0 := by linarith [hs.1]
    exact ne_of_lt h0
  have hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (((0 : ℝ) - s) • realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b u w =
        (realizedFam (I := I) g₀ T T' hδ hδ' 0).inner b u w -
          (realizedFam (I := I) g₀ T T' hδ hδ' s).inner b u w := by
    intro b u w
    rw [ccTensorBilin_smul_c,
      realizedVelocityCc_bilin (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s b u w]
    have haff := realizedFam_inner_affine (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (s₀ := s) (s := 0) hsmem h0mem b u w
    linarith [haff]
  have h996 := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedFam (I := I) g₀ T T' hδ hδ' 0)
    (((0 : ℝ) - s) • realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) hbil X Y Z x ζ
  rw [cotangentToDual_dualToCotangent] at h996
  have hθ₀ : (fun b : M => cotangentToCLM (I := I)
        (dualToCotangent (I := I)
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Y b) (Z b)))) =
      ((0 : ℝ) - s)⁻¹ • (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' 0) Z Y b)) := by
    funext b
    rw [Pi.smul_apply,
      koszulPair_eq_smul_dual_linearizedKoszul (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs Z Y b,
      cotangentToCLM_smul_c, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  have hsc := (cotangentCov
      (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))).isCovariantDerivativeOnUniv.smul_const
    (σ := fun b : M => cotangentToCLM (I := I)
      (koszulCovGradCovec (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedFam (I := I) g₀ T T' hδ hδ' 0) Z Y b))
    (x := x) (((0 : ℝ) - s)⁻¹)
    (koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedFam (I := I) g₀ T T' hδ hδ' 0) Z Y x)
    (Set.mem_univ x)
  rw [ContinuousLinearMap.coe_coe] at h996
  rw [hθ₀, hsc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h996]
  rw [iteratedCovGrad_smul_c, covGrad_smul, unitModel_smul_gen, unitModel_smul_gen]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  field_simp


private lemma velocity_covGrad_swap12
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, c] =
      unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, c, b] := by
  rw [unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x ![a, b, c],
    (unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x ![a, c, b])]
  simp only [Matrix.cons_val_zero, Matrix.tail_cons]
  have hnat := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 1
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (Equiv.swap (0 : Fin 2) 1)
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    x a
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x)
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x)
    (fun y => velocity_unitEval_domDomCongr_swap (I := I) g₀ T T' hδ hδ' s y)
  rw [toModel_apply_tangent, toModel_apply_tangent]
  have happ := congrArg
    (fun (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ) =>
      T ![b, c]) hnat
  dsimp only at happ
  rw [ContinuousMultilinearMap.domDomCongr_apply] at happ
  have hvec : (fun i => (![b, c] : Fin 2 → TangentSpace I x) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![c, b] := by
    funext i
    fin_cases i <;> simp
  rw [hvec] at happ
  exact happ


private lemma velocity_covGrad_unitEval_domDomCongr_swap12
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) :
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
        (unitZeroSec (I := I) (M := M) y) =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I y) ℝ from
          (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
            (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
            (unitZeroSec (I := I) (M := M) y)) := by
  apply Tensor0SBundle.tensor0SSpace_ext 3 y
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have h1 : ∀ (mm : Fin 3 → TangentSpace I y),
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I y) ℝ from
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
          (unitZeroSec (I := I) (M := M) y)) mm =
      unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) y mm := fun mm => rfl
  rw [h1, h1]
  have hm : m = ![m 0, m 1, m 2] := by
    funext i
    fin_cases i <;> simp
  have hmσ : (fun i => m ((Equiv.swap (1 : Fin 3) 2) i)) = ![m 0, m 2, m 1] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [hmσ]
  conv_lhs => rw [hm]
  exact velocity_covGrad_swap12 (I := I) g₀ T T' hδ hδ' s y (m 0) (m 1) (m 2)


private lemma velocity_secondCovGrad_swap23
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (a b c d : TangentSpace I x) :
    unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
        (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, c, d] =
      unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
        (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, d, c] := by
  have hunf : iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) =
      covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) := rfl
  rw [hunf]
  rw [unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, c, d],
    (unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, d, c])]
  simp only [Matrix.cons_val_zero, Matrix.tail_cons]
  have hnat := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 2
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (Equiv.swap (1 : Fin 3) 2)
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    x a
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x)
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x)
    (fun y => velocity_covGrad_unitEval_domDomCongr_swap12 (I := I) g₀ T T' hδ hδ' s y)
  rw [toModel_apply_tangent, toModel_apply_tangent]
  have happ := congrArg
    (fun (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ) =>
      T ![b, c, d]) hnat
  dsimp only at happ
  rw [ContinuousMultilinearMap.domDomCongr_apply] at happ
  have hvec : (fun i => (![b, c, d] : Fin 3 → TangentSpace I x) ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![b, d, c] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [hvec] at happ
  exact happ


private lemma lkc_eq_endpoint_flat
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (b : M) (u ζ : TangentSpace I b) :
    linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b u ζ =
      (1 - s)⁻¹ •
        ((realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ)).toLinearMap := by
  classical
  have h1mem : (1 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    one_mem_realizedSmallSet hδ_lt
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs)
  have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs.2)
  ext z
  have hkey := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    hsmem h1mem b u ζ
  have hinner : (realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ) z =
      (1 - s) *
        linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b u ζ z := by
    rw [hkey, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp]
  rw [LinearMap.smul_apply]
  rw [show (((realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ)).toLinearMap) z =
      (realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ) z from rfl]
  rw [hinner, smul_eq_mul]
  field_simp


private lemma lkc_basis_contMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  have hΛ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' 1) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      Z.contMDiff Y.contMDiff
  have hflat : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) b
        (g0FlatCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1) b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)) hΛ
  set Kf : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E,
      (fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)⟯ :=
    ⟨fun b : M => g0FlatCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1) b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)), hflat⟩ with hKf
  have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Kf α j
  have heq : ∀ b ∈ (chartAt H α).source,
      linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b) =
        (1 - s)⁻¹ *
          Tensor0SBundle.Tensor0SSpace.toModel (Kf b)
            (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) := by
    intro b _
    rw [lkc_eq_endpoint_flat (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs b (Z b) (Y b)]
    rw [LinearMap.smul_apply, smul_eq_mul]
    congr 1
  have hcomb : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (1 - s)⁻¹ *
        Tensor0SBundle.Tensor0SSpace.toModel (Kf b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source :=
    contMDiffOn_const.mul hbase
  exact hcomb.congr heq


private lemma metricSharp_linearizedKoszulCovec_contMDiff
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)))) := by
  apply metricSharp_contMDiff_total (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (cv := fun b : M =>
      linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b))
  intro α j
  exact lkc_basis_contMDiffOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs Y Z α j


private theorem covDerivLinearizedConn_inner_towers
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
          (fun b => X b) (fun b => Y b) (fun b => Z b) x) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
            (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Y x, Z x, ζ]
          + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Z x, Y x, ζ]
          - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, ζ, Y x, Z x]) := by
  classical
  have hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) y)
          (dualToCotangent (I := I)
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y))))) x := by
    have hfun : (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) y)
          (dualToCotangent (I := I)
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y))))) =
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
          (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) y
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y)))) := by
      funext y
      rw [inverseMetricSharpFib_dualToCotangent]
    rw [hfun]
    exact ((metricSharp_linearizedKoszulCovec_contMDiff (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs Y Z x).mdifferentiableAt
      (by simp))
  have hpar := inverseMetricSharpField_covGrad_eq_zero
    (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (fun y : M => dualToCotangent (I := I)
      (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y)))
    hβ (X x)
  have hfield : (fun b : M =>
      linearizedConnSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)) =
      (fun b : M => (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b)
        (dualToCotangent (I := I)
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)))) := by
    funext b
    rw [inverseMetricSharpFib_dualToCotangent]
    rfl
  rw [covDerivLinearizedConn]
  rw [map_sub, map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rw [hfield, hpar]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    ContinuousLinearMap.coe_coe]
  rw [cotangentCov_linearizedKoszul_eval (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs X Z Y x ζ]
  rw [show linearizedConnSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x (Z x)
      (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (fun b => X b) (fun b => Y b) x) =
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
      (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x (Z x)
        (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (fun b => X b) (fun b => Y b) x)) from rfl]
  rw [show linearizedConnSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x
      (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (fun b => X b) (fun b => Z b) x) (Y x) =
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
      (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x
        (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (fun b => X b) (fun b => Z b) x) (Y x)) from rfl]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp, DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp]
  rw [linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  rw [covApply_apply, covApply_apply]
  ring

private def perm4_1023 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 0, 2, 3] ![1, 0, 2, 3] (by decide) (by decide)


private lemma vec4_update_zero {F : Type*} (a b c d z : F) :
    Function.update ![a, b, c, d] 0 z = ![z, b, c, d] := by
  funext k
  fin_cases k <;> simp [Function.update]


private lemma vec4_update_three {F : Type*} (a b c d z : F) :
    Function.update ![a, b, c, d] 3 z = ![a, b, c, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

private def cmmSlotPairCLM (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun om => ContinuousMultilinearMap.toContinuousLinearMap
        (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![(0 : E), p, q, om] (0 : Fin 4)
      map_add' := fun om om' => by
        apply ContinuousLinearMap.ext
        intro u
        rw [ContinuousLinearMap.add_apply]
        change (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            (Function.update ![(0 : E), p, q, om + om'] 0 u) =
          (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
              (Function.update ![(0 : E), p, q, om] 0 u) +
            (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
              (Function.update ![(0 : E), p, q, om'] 0 u)
        rw [vec4_update_zero, vec4_update_zero, vec4_update_zero]
        have hupd : (![u, p, q, om + om'] : Fin 4 → E) =
            Function.update ![u, p, q, om] 3 (om + om') := by
          rw [vec4_update_three]
        rw [hupd]
        rw [ContinuousMultilinearMap.map_update_add
          (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![u, p, q, om] 3 om om']
        rw [vec4_update_three, vec4_update_three]
      map_smul' := fun c om => by
        apply ContinuousLinearMap.ext
        intro u
        rw [RingHom.id_apply, ContinuousLinearMap.smul_apply]
        change (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            (Function.update ![(0 : E), p, q, (c • om)] 0 u) =
          c • (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
              (Function.update ![(0 : E), p, q, om] 0 u)
        rw [vec4_update_zero, vec4_update_zero]
        have hupd : (![u, p, q, (c • om)] : Fin 4 → E) =
            Function.update ![u, p, q, om] 3 (c • om) := by
          rw [vec4_update_three]
        rw [hupd]
        rw [ContinuousMultilinearMap.map_update_smul
          (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![u, p, q, om] 3 c om]
        rw [vec4_update_three] }


omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorRank4OuterSlotBilinearCLM_apply (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q om u : E) :
    cmmSlotPairCLM (E := E) D p q om u = D ![u, p, q, om] := by
  change (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
      (Function.update ![(0 : E), p, q, om] 0 u) = D ![u, p, q, om]
  rw [vec4_update_zero]

private def sharpCovCLM (g₁ : SmoothRiemannianMetric I M) (x : M) :
    (E →L[ℝ] ℝ) →L[ℝ] E :=
  (cometricLmodel (I := I) g₁ x).comp (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sharpCovCLM_apply (g₁ : SmoothRiemannianMetric I M) (x : M) (φ : E →L[ℝ] ℝ) :
    sharpCovCLM (I := I) (M := M) g₁ x φ =
      cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) := rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma inner_sharpCovCLM (g₁ : SmoothRiemannianMetric I M) (x : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I x) :
    g₁.inner x (sharpCovCLM (I := I) (M := M) g₁ x φ) u = φ (u : E) := by
  rw [sharpCovCLM_apply]
  exact cometricLmodel_covectorOfCLM_inner (I := I) g₁ x φ u


section NormedContinuousDualBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma cDualBasis_eq_coord (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E)) :
    B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
  rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
    (congrFun (Module.Basis.coe_dualBasis B) k)

end NormedContinuousDualBasis


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sharp_dual_coeff_symm (g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (k l : Fin (Module.finrank ℝ E)) :
    B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) =
      B.cDualBasis k (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l)) := by
  rw [← inner_sharpCovCLM (I := I) g₁ x (B.cDualBasis l)
    (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))]
  rw [← inner_sharpCovCLM (I := I) g₁ x (B.cDualBasis k)
    (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l))]
  exact g₁.symm x _ _


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sharpCov_basis_expand (g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (k : Fin (Module.finrank ℝ E)) :
    sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k) =
      ∑ l : Fin (Module.finrank ℝ E),
        (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) • B l := by
  have hl : ∀ l : Fin (Module.finrank ℝ E),
      B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) =
        B.repr (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) l := by
    intro l
    rw [cDualBasis_eq_coord (E := E)]
    rfl
  rw [show (∑ l : Fin (Module.finrank ℝ E),
      (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) • B l) =
      ∑ l : Fin (Module.finrank ℝ E),
        (B.repr (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) l) • B l from
    Finset.sum_congr rfl (fun l _ => by rw [hl l])]
  exact (B.sum_repr (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))).symm


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma bilinCLM_diag_swap (g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (Λ : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E),
        Λ (B k) (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) =
      ∑ k : Fin (Module.finrank ℝ E),
        Λ (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) (B k) := by
  have hexp : ∀ k, sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k) =
      ∑ l : Fin (Module.finrank ℝ E),
        (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) • B l :=
    fun k => sharpCov_basis_expand (I := I) g₁ x B k
  calc
    (∑ k : Fin (Module.finrank ℝ E),
        Λ (B k) (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)))
        = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) *
              Λ (B k) (B l) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          conv_lhs => rw [hexp k]
          rw [map_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [map_smul, smul_eq_mul]
    _ = ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) *
              Λ (B k) (B l) := Finset.sum_comm
    _ = ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            (B.cDualBasis k (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l))) *
              Λ (B k) (B l) := by
          refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [sharp_dual_coeff_symm (I := I) g₁ x B l k]
    _ = ∑ l : Fin (Module.finrank ℝ E),
            Λ (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l)) (B l) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          conv_rhs => rw [hexp l]
          rw [map_sum, ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPair_trace_basis_indep (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q : E) :
    (∑ i : Fin (Module.finrank ℝ E),
        D ![(chartModelBasis E i : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![(Module.finBasis ℝ E k : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k)] := by
  have h := cDualBasis_trace_basis_indep (chartModelBasis E)
    ((cmmSlotPairCLM (E := E) D p q).comp (sharpCovCLM (I := I) (M := M) g₁ x))
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).comp (sharpCovCLM (I := I) (M := M) g₁ x))
        ((chartModelBasis E).cDualBasis k) (chartModelBasis E k)) =
      ∑ i : Fin (Module.finrank ℝ E),
        D ![(chartModelBasis E i : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((chartModelBasis E).cDualBasis i)] from
    Finset.sum_congr rfl (fun i _ => by
      rw [ContinuousLinearMap.comp_apply, tensorRank4OuterSlotBilinearCLM_apply])] at h
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).comp (sharpCovCLM (I := I) (M := M) g₁ x))
        ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![(Module.finBasis ℝ E k : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k)] from
    Finset.sum_congr rfl (fun k _ => by
      rw [ContinuousLinearMap.comp_apply, tensorRank4OuterSlotBilinearCLM_apply])] at h
  exact h


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPair_trace_swap (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q : E) :
    (∑ i : Fin (Module.finrank ℝ E),
        D ![(chartModelBasis E i : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k), p, q,
          (Module.finBasis ℝ E k : E)] := by
  rw [slotPair_trace_basis_indep (I := I) g₁ x D p q]
  have hswap := bilinCLM_diag_swap (I := I) g₁ x (Module.finBasis ℝ E)
    ((cmmSlotPairCLM (E := E) D p q).flip)
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).flip) ((Module.finBasis ℝ E) k)
        (sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k))) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![(Module.finBasis ℝ E k : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k)] from
    Finset.sum_congr rfl (fun k _ => by
      rw [ContinuousLinearMap.flip_apply, tensorRank4OuterSlotBilinearCLM_apply])] at hswap
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).flip)
        (sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k))
        ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k), p, q,
          (Module.finBasis ℝ E k : E)] from
    Finset.sum_congr rfl (fun k _ => by
      rw [ContinuousLinearMap.flip_apply, tensorRank4OuterSlotBilinearCLM_apply])] at hswap
  exact hswap


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma appCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ Ψ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ - Ψ) W =
      operatorFieldApply (I := I) (M := M) g r s Φ W - operatorFieldApply (I := I) (M := M) g r s Ψ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ W - operatorFieldApply (I := I) (M := M) g r s Ψ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x -
        (operatorFieldApply (I := I) (M := M) g r s Ψ W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ - Ψ).toSection x : Tensor0SBundle.TensorRSSpace r s I x) =
      Φ.toSection x - Ψ.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma appCc_smul_left' (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (c • Φ) W =
      c • operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : Tensor0SBundle.TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_sub_gen (g : SmoothRiemannianMetric I M) {n : ℕ}
    (S S' : SmoothCcTensor g 0 n) (x : M) :
    unitModel (I := I) (M := M) g n (S - S') x =
      unitModel (I := I) (M := M) g n S x - unitModel (I := I) (M := M) g n S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]

private def perm4_1032 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 0, 3, 2] ![1, 0, 3, 2] (by decide) (by decide)


omit [NeZero (Module.finrank ℝ E)] in
private lemma domDomCongr_0312_eval (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (a b c d : E) :
    ContinuousMultilinearMap.domDomCongr perm4_0312
      (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![a, b, c, d] = D ![a, d, b, c] := by
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl


omit [NeZero (Module.finrank ℝ E)] in
private lemma domDomCongr_1032_eval (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (a b c d : E) :
    ContinuousMultilinearMap.domDomCongr perm4_1032
      (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![a, b, c, d] = D ![b, a, d, c] := by
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl


omit [NeZero (Module.finrank ℝ E)] in
private lemma domDomCongr_1203_eval (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (a b c d : E) :
    ContinuousMultilinearMap.domDomCongr perm4_1203
      (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![a, b, c, d] = D ![b, c, a, d] := by
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl


private lemma finCons_vec3_eq {F : Type*} (a b c d : F) :
    (Fin.cons a ![b, c, d] : Fin 4 → F) = ![a, b, c, d] := by
  funext i
  fin_cases i <;> rfl


private lemma finCons_cons_pair_eq {F : Type*} (a b : F) (v : Fin 2 → F) :
    (Fin.cons a (Fin.cons b v) : Fin 4 → F) = ![a, b, v 0, v 1] := by
  funext i
  fin_cases i <;> rfl

theorem linearizedRicciAt_eq_lichnerowicz_velocitySecondCovGrad
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v := by
  classical
  have hD4rfl : ∀ (m : Fin 4 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x m := fun m => rfl
  have hconv : ∀ k : Fin (Module.finrank ℝ E),
      sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k) =
        cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)) := fun k => rfl
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v =
      (1 / 2 : ℝ) *
        ((∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k])
          + (∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k])
          - (∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1]))
      - (1 / 2 : ℝ) *
          (∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k]) := by
    rw [show linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) -
          (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl]
    rw [appCc_sub_left, appCc_smul_left', unitModel_sub_gen, unitModel_smul_gen,
      ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x v]
    rw [traceHessianCoeff_apply_eq (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x v]
    have hterm : ∀ k : Fin (Module.finrank ℝ E),
        (unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![v 0, v 1, (Module.finBasis ℝ E) k])
          + unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 1, v 0, (Module.finBasis ℝ E) k])
          - unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) v))) =
        (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k]
          + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k]
          - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1]) := by
      intro k
      rw [← hconv k]
      rw [finCons_vec3_eq (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k)) (v 0) (v 1) ((Module.finBasis ℝ E) k)]
      rw [finCons_vec3_eq (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k)) (v 1) (v 0) ((Module.finBasis ℝ E) k)]
      rw [finCons_cons_pair_eq (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k)) ((Module.finBasis ℝ E) k) v]
      rw [hD4rfl, hD4rfl, hD4rfl]
    have htrace : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace 4 I x from
                (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
                (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v)) =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
      intro k
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      have hargs : (fun i => (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v) : Fin 4 → TangentSpace I x)
          (traceHessianSlotPerm i)) =
        ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
        funext i
        fin_cases i <;> rfl
      rw [hargs]
      exact hD4rfl _
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        (unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![v 0, v 1, (Module.finBasis ℝ E) k])
          + unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 1, v 0, (Module.finBasis ℝ E) k])
          - unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) v)))) =
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1]) from
      Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace 4 I x from
                (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
                (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v))) =
        ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] from
      Finset.sum_congr rfl (fun k _ => htrace k)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hRHS]
  have hks := linearizedRicciAt_eq_palatini_covDeriv (I := I) (g₀ := g₀) (T := T) (T' := T')
    (x := x) (v := v 0) (w := v 1) hδ_lt hδ hδ'_lt hδ' (s₀ := s) hs
  rw [hks]
  have hsum : ∀ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x (v 1)) x
          - covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x)) i =
      ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1])) := by
    intro i
    have hrepr : ∀ (W : TangentSpace I x),
        ((chartModelBasis E).repr W) i =
          (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x W (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) := by
      intro W
      rw [(realizedFam (I := I) g₀ T T' hδ hδ' s).symm x W (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)), inner_sharpCovCLM, cDualBasis_eq_coord]
      rfl
    rw [map_sub, Finsupp.sub_apply, hrepr, hrepr]
    set Bi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hBi
    set V0f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hV0f
    set V1f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 1),
        smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩ with hV1f
    have hBix : (Bi x : TangentSpace I x) = (chartModelBasis E) i := smoothExtensionTangent_eq (I := I) x ((chartModelBasis E) i)
    have hV0x : (V0f x : TangentSpace I x) = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
    have hV1x : (V1f x : TangentSpace I x) = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
    have hA := covDerivLinearizedConn_inner_towers (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs
      Bi V0f V1f x (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i))
    have hB := covDerivLinearizedConn_inner_towers (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs
      V0f Bi V1f x (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i))
    rw [hBix, hV0x, hV1x] at hA hB
    have hA' : (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
          (smoothExtensionTangent (I := I) x (v 0))
          (smoothExtensionTangent (I := I) x (v 1)) x) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) =
        (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1]) := hA
    have hB' : (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
          (smoothExtensionTangent (I := I) x (v 0))
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
          (smoothExtensionTangent (I := I) x (v 1)) x) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) =
        (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1]) := hB
    rw [hA', hB']
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x (v 1)) x
          - covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x)) i) =
    ∑ i : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1])) from
    Finset.sum_congr rfl (fun i _ => hsum i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hTA1 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k] :=
    slotPair_trace_swap (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 0) (v 1)
  have hTA2 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k] :=
    slotPair_trace_swap (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 1) (v 0)
  have hTA3 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1] := by
    have hcan : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1] =
          ContinuousMultilinearMap.domDomCongr perm4_0312
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] := by
      intro i
      rw [domDomCongr_0312_eval]
    have hcan' : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr perm4_0312
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k] =
          unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1] := by
      intro k
      rw [domDomCongr_0312_eval]
    rw [show (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1]) =
        ∑ i : Fin (Module.finrank ℝ E),
          ContinuousMultilinearMap.domDomCongr perm4_0312
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] from
      Finset.sum_congr rfl (fun i _ => hcan i)]
    rw [slotPair_trace_swap (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 0) (v 1)]
    exact Finset.sum_congr rfl (fun k _ => hcan' k)
  have hTB2 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
    have hcan : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] =
          ContinuousMultilinearMap.domDomCongr perm4_1203
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] := by
      intro i
      rw [domDomCongr_1203_eval]
    have hcan' : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr perm4_1203
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k] =
          unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
      intro k
      rw [domDomCongr_1203_eval]
    rw [show (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
        ∑ i : Fin (Module.finrank ℝ E),
          ContinuousMultilinearMap.domDomCongr perm4_1203
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] from
      Finset.sum_congr rfl (fun i _ => hcan i)]
    rw [slotPair_trace_swap (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 0) (v 1)]
    exact Finset.sum_congr rfl (fun k _ => hcan' k)
  have hmid : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1] := by
    have hstep1 : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] = unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 1] := by
      intro i
      exact velocity_secondCovGrad_swap23 (I := I) g₀ T T' hδ hδ' s x (v 0) ((chartModelBasis E) i)
        (v 1) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i))
    have hswap := bilinCLM_diag_swap (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x (chartModelBasis E)
      ((cmmSlotPairCLM (E := E)
        (ContinuousMultilinearMap.domDomCongr perm4_1032
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
    have hL : ∀ i : Fin (Module.finrank ℝ E),
        ((cmmSlotPairCLM (E := E)
          (ContinuousMultilinearMap.domDomCongr perm4_1032
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
          ((chartModelBasis E) i) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 1] := by
      intro i
      rw [ContinuousLinearMap.flip_apply, tensorRank4OuterSlotBilinearCLM_apply, domDomCongr_1032_eval]
    have hR : ∀ i : Fin (Module.finrank ℝ E),
        ((cmmSlotPairCLM (E := E)
          (ContinuousMultilinearMap.domDomCongr perm4_1032
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
          (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) ((chartModelBasis E) i) =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1] := by
      intro i
      rw [ContinuousLinearMap.flip_apply, tensorRank4OuterSlotBilinearCLM_apply, domDomCongr_1032_eval]
    calc (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)])
        = ∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 1] :=
          Finset.sum_congr rfl (fun i _ => hstep1 i)
      _ = ∑ i : Fin (Module.finrank ℝ E),
            ((cmmSlotPairCLM (E := E)
              (ContinuousMultilinearMap.domDomCongr perm4_1032
                (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
              ((chartModelBasis E) i) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) :=
          Finset.sum_congr rfl (fun i _ => (hL i).symm)
      _ = ∑ i : Fin (Module.finrank ℝ E),
            ((cmmSlotPairCLM (E := E)
              (ContinuousMultilinearMap.domDomCongr perm4_1032
                (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
              (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) ((chartModelBasis E) i) := hswap
      _ = ∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1] :=
          Finset.sum_congr rfl (fun i _ => hR i)
  rw [hTA1, hTA2, hTA3, hTB2, hmid]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
