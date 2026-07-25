import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm)

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
def gInvDiffRaisedEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => metricComparisonDiffEndo (I := I) g₀ g₁ x
  contMDiff_toFun := gInvDiffRaisedEndo_contMDiff (I := I) g₀ g₁

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem inverseMetricSharpFib_g0FlatY_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (inverseMetricSharpFib (I := I) g₁ b (g0FlatCLM (I := I) g₀ b (Y b)))) := by
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
          (I := I) g₁ b ((g₀.inner b (Y b)).toLinearMap))) := by
    apply metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlat_chartComponent_contMDiffOn (I := I) g₀ Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₀ g₁ x (Y x)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cotangent_g0FlatY_mdiffAtCotangent
    (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (Y b))) x := by
  have heq : (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (Y b))) =
      metricFlat (I := I) g₀ (fun b : M => Y b) := by
    funext b
    apply ContinuousLinearMap.ext
    intro w
    rw [metricFlat_apply]
    change cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ b (Y b)) w = _
    exact cotangentToDual_g0FlatCLM (I := I) g₀ b (Y b) w
  rw [heq]
  exact metricFlat_mdiff (I := I) g₀ (Y.contMDiff.mdifferentiableAt (by norm_num))

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem endoCov_gInvDiffRaisedField_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) := by
  classical
  set β : Π b : M, Tensor0SSpace 1 I b := fun b : M => g0FlatCLM (I := I) g₀ b (Y b) with hβdef
  set gradY : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v with hgradY
  have hYmd := Y.mdifferentiableAt (x := x)
  have hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₁ y) (β y))) x :=
    ((inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y) x).mdifferentiableAt
      (by norm_num)
  have hβ₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) x := by
    have hcong : (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) =
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) := by
      funext y
      rw [hβdef]
      rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ y (Y y)]
    rw [hcong]
    exact Y.mdifferentiableAt (x := x)
  have hβcot : MDiffAtCotangent (I := I) (fun b : M => cotangentToCLM (I := I) (β b)) x :=
    cotangent_g0FlatY_mdiffAtCotangent (I := I) g₀ Y x
  have hsharpY_mdiff :=
    ((inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y) x).mdifferentiableAt
      (by norm_num)
  have hΛapply : (gInvDiffRaisedEndoField (I := I) g₀ g₁ : Π y : M, _) =
      fun y : M => metricComparisonDiffEndo (I := I) g₀ g₁ y := rfl
  have hLeibniz := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) Y x v
  rw [hLeibniz]
  have hΛval : ∀ y : M, (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y) =
      (inverseMetricSharpFib (I := I) g₁ y) (β y) - Y y := by
    intro y
    rw [hβdef]
    change metricComparisonDiffEndo (I := I) g₀ g₁ y (Y y) = _
    rw [gInvDiffRaisedEndo_apply]
  have hΛx : (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) gradY =
      (inverseMetricSharpFib (I := I) g₁ x) (g0FlatCLM (I := I) g₀ x gradY) - gradY := by
    change metricComparisonDiffEndo (I := I) g₀ g₁ x gradY = _
    rw [gInvDiffRaisedEndo_apply]
  have hsplit : (LeviCivita (I := I) g₀) (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) x v =
      (LeviCivita (I := I) g₀).toFun (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) x v
        - (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v := by
    have hfun : (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) =
        (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) - (fun y : M => Y y) := by
      funext y
      rw [Pi.sub_apply, hΛval y]
    have hop : (LeviCivita (I := I) g₀).toFun
          (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) x =
        (LeviCivita (I := I) g₀).toFun
            (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) x
          - (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x := by
      rw [hfun]
      exact cov_toFun_sub (LeviCivita (I := I) g₀) hsharpY_mdiff hYmd
    have hopv := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hop
    simpa using hopv
  rw [hsplit]
  have hcross := covGrad_inverseMetricSharpFib_cross (I := I) g₀ g₁ β hβ hβcot v
  rw [hcross]
  have hT1 : inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v)) =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x gradY) := by
    have hB := inverseMetricSharpField_covGrad_eq_zero (I := I) g₀ β hβ₀ v
    have hseceq : (fun b : M => (inverseMetricSharpFib (I := I) g₀ b) (β b)) =
        (fun y : M => Y y) := by
      funext y
      rw [hβdef, inverseMetricSharpFib_g0FlatCLM (I := I) g₀ y (Y y)]
    rw [hseceq] at hB
    have hflat : g0FlatCLM (I := I) g₀ x gradY =
        dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v) := by
      rw [hgradY, hB,
        Analysis.Sobolev.TensorHilbert.g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x _]
    rw [hflat]
  rw [hT1, hΛx]
  rw [show (inverseMetricSharpFib (I := I) g₁ x) (β x) =
      metricComparisonEndo (I := I) g₀ g₁ x (Y x) from by
    rw [hβdef, gInvRaisedEndo_apply]]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma sqrt_g0_inner_add_le'
    (g₀ : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g₀.inner x (a + b) (a + b)) ≤
      Real.sqrt (g₀.inner x a a) + Real.sqrt (g₀.inner x b b) := by
  set na := Real.sqrt (g₀.inner x a a) with hna
  set nb := Real.sqrt (g₀.inner x b b) with hnb
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hsum_nn : 0 ≤ g₀.inner x (a + b) (a + b) :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x (a + b)
  have hna_nn : 0 ≤ na := Real.sqrt_nonneg _
  have hnb_nn : 0 ≤ nb := Real.sqrt_nonneg _
  have hna_sq : na ^ 2 = g₀.inner x a a := by rw [hna, Real.sq_sqrt haa_nn]
  have hnb_sq : nb ^ 2 = g₀.inner x b b := by rw [hnb, Real.sq_sqrt hbb_nn]
  have hcross : g₀.inner x a b ≤ na * nb := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x a b
    rw [← hna, ← hnb] at habs
    exact le_trans (le_abs_self _) habs
  have hexpand : g₀.inner x (a + b) (a + b) =
      g₀.inner x a a + 2 * g₀.inner x a b + g₀.inner x b b := by
    have h1 : g₀.inner x (a + b) (a + b)
        = g₀.inner x a (a + b) + g₀.inner x b (a + b) := by
      rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
    have h2 : g₀.inner x a (a + b) = g₀.inner x a a + g₀.inner x a b :=
      map_add (g₀.inner x a) a b
    have h3 : g₀.inner x b (a + b) = g₀.inner x b a + g₀.inner x b b :=
      map_add (g₀.inner x b) a b
    have h4 : g₀.inner x b a = g₀.inner x a b := g₀.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hle_sq : g₀.inner x (a + b) (a + b) ≤ (na + nb) ^ 2 := by
    rw [hexpand]
    have hsq : (na + nb) ^ 2 = na ^ 2 + 2 * (na * nb) + nb ^ 2 := by ring
    rw [hsq, hna_sq, hnb_sq]
    nlinarith [hcross]
  have hsum_pos_nn : 0 ≤ na + nb := add_nonneg hna_nn hnb_nn
  calc Real.sqrt (g₀.inner x (a + b) (a + b))
      ≤ Real.sqrt ((na + nb) ^ 2) := Real.sqrt_le_sqrt hle_sq
    _ = na + nb := by rw [Real.sqrt_sq hsum_pos_nn]

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem sqrt_inner_endoCov_gInvDiffRaisedField_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x))
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x))) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x (Y x) (Y x)) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ := connDiff_gFibreNorm_le_iteratedCovGrad (I := I) (M := M) g₀
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound Y x v
  have hcoeff : 0 < 1 - δ := by linarith
  set w : TangentSpace I x := Y x with hw_def
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  set Nw : ℝ := Real.sqrt (g₀.inner x w w) with hNw_def
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNw_nn : 0 ≤ Nw := Real.sqrt_nonneg _
  have hinv_le : 1 / (1 - δ) ≤ 2 := by rw [div_le_iff₀ hcoeff]; linarith
  set EC : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) with hEC_def
  set T2 : TangentSpace I x :=
    - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x w) v
    with hT2_def
  set T3 : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x
      (dualToCotangent (I := I)
        (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap)
    with hT3_def
  have hEC_eq : EC = T2 + T3 := by
    rw [hEC_def, hT2_def, hT3_def, hw_def]
    exact endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v
  have hgir := sqrt_inner_gInvRaisedEndo_le (I := I) g₀ g₁
    (ccTensorBilinSymm (I := I) g₀ T) (fun y a b => h y a b)
    (by linarith : δ < 1) hδ0 hbound x w
  rw [← hNw_def] at hgir
  have hT2_bound : Real.sqrt (g₀.inner x T2 T2) ≤ 2 * C₀ * G * Nv * Nw := by
    have hraw := hpw g₁ T h hδ hδ0 hbound x (metricComparisonEndo (I := I) g₀ g₁ x w) v
    rw [← hNv_def] at hraw
    have hT2_sq : g₀.inner x T2 T2 =
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (metricComparisonEndo (I := I) g₀ g₁ x w) v)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (metricComparisonEndo (I := I) g₀ g₁ x w) v) := by
      simp only [hT2_def, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
    rw [hT2_sq]
    refine hraw.trans ?_
    have hgir' : Real.sqrt (g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x w)
        (metricComparisonEndo (I := I) g₀ g₁ x w)) ≤ 2 * Nw := by
      refine hgir.trans ?_
      exact mul_le_mul_of_nonneg_right hinv_le hNw_nn
    calc C₀ * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
              Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
            Real.sqrt (g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x w)
              (metricComparisonEndo (I := I) g₀ g₁ x w)) * Nv
        ≤ C₀ * G * (2 * Nw) * Nv := by
          rw [← hG_def]
          gcongr
      _ = 2 * C₀ * G * Nv * Nw := by ring
  have hT3_bound : Real.sqrt (g₀.inner x T3 T3) ≤ 2 * C₀ * G * Nv * Nw := by
    set Dfun : TangentSpace I x →L[ℝ] ℝ :=
      (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)) with hDfun_def
    set p : TangentSpace I x :=
      inverseMetricSharpFib (I := I) g₀ x (dualToCotangent (I := I) Dfun.toLinearMap)
      with hp_def
    have hT3eq : T3 = inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x p) := by
      rw [hT3_def]
      congr 1
      exact (g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x
        (dualToCotangent (I := I) Dfun.toLinearMap)).symm
    set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNpdef
    have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
    have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
    have hNp_sq : Np ^ 2 = g₀.inner x p p := Real.sq_sqrt hpp_nn
    have hDval : ∀ z : TangentSpace I x, Dfun z =
        - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) := by
      intro z
      rw [hDfun_def, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply]
      change - cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ x w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) = _
      rw [cotangentToDual_g0FlatCLM]
    have hpz : ∀ z : TangentSpace I x, g₀.inner x p z = Dfun z := by
      intro z
      rw [hp_def, inverseMetricSharpFib_inner (I := I) g₀ x
        (dualToCotangent (I := I) Dfun.toLinearMap) z]
      rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
      rfl
    have hpp_val : g₀.inner x p p =
        - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v) := by
      rw [hpz p, hDval p]
    have hconn_p := hpw g₁ T h hδ hδ0 hbound x p v
    rw [← hNv_def, ← hNpdef] at hconn_p
    have hconnG : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) ≤ C₀ * G * Np * Nv := hconn_p
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x w
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
    rw [← hNw_def] at hcs
    have hNp_le : Np ≤ C₀ * G * Nv * Nw := by
      have hpp_le : g₀.inner x p p ≤
          Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) := by
        rw [hpp_val]
        calc - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            ≤ |g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)| := neg_le_abs _
          _ ≤ Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) := hcs
      have hKnn : 0 ≤ C₀ * G * Nv * Nw :=
        mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn) hNw_nn
      have hchain : Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) ≤
          Nw * (C₀ * G * Np * Nv) :=
        mul_le_mul_of_nonneg_left hconnG hNw_nn
      have hpp_le2 : g₀.inner x p p ≤ (C₀ * G * Nv * Nw) * Np := by
        refine hpp_le.trans (hchain.trans ?_)
        nlinarith [hNw_nn, hNp_nn, mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn]
      nlinarith [hNp_sq, hNp_nn, hpp_le2, hKnn]
    have hsharp := norm_inverseMetricSharpFib_g0Flat_le (I := I) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T) (fun y a b => h y a b)
      (by linarith : δ < 1) hδ0 hbound x p
    rw [← hNpdef] at hsharp
    rw [hT3eq]
    refine hsharp.trans ?_
    have hstep : (1 / (1 - δ)) * Np ≤ 2 * Np :=
      mul_le_mul_of_nonneg_right hinv_le hNp_nn
    refine hstep.trans ?_
    nlinarith [hNp_le, hNp_nn, mul_nonneg (mul_nonneg hC₀0 hG_nn) (mul_nonneg hNv_nn hNw_nn)]
  have htri : Real.sqrt (g₀.inner x EC EC) ≤
      Real.sqrt (g₀.inner x T2 T2) + Real.sqrt (g₀.inner x T3 T3) := by
    rw [hEC_eq]
    exact sqrt_g0_inner_add_le' (I := I) g₀ x T2 T3
  refine htri.trans ?_
  have hsum : Real.sqrt (g₀.inner x T2 T2) + Real.sqrt (g₀.inner x T3 T3) ≤
      (2 * C₀ * G * Nv * Nw) + (2 * C₀ * G * Nv * Nw) := add_le_add hT2_bound hT3_bound
  refine hsum.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn) hNw_nn]

end InnerProductSpaceModel

end Connection
end Integral
end DifferentialGeometry

end
