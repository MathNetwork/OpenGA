import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.NonlinearitySpectral
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def ccTensorMultilinear (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  MixedSection.toMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ T.toSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem ccTensorMultilinear_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorMultilinear (I := I) g T x =
      T.toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) :=
  rfl

def ccTensorModel (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  Tensor0SSpace.toModel
    (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x)

def smoothCcTensorBilinForm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (bilinFormToModel E).symm (ccTensorModel (I := I) g T x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilin_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g T x v w =
      ccTensorModel (I := I) g T x ![v, w] :=
  bilinFormToModel_symm_apply E (ccTensorModel (I := I) g T x) v w

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilin_abs_le_fibreNorm_mul_sqrt
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (v w : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
    |smoothCcTensorBilinForm (I := I) g₀ T x v w| ≤
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2

  obtain ⟨n, e, _hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  set B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    smoothCcTensorBilinForm (I := I) g₀ T x with hB_def

  set coef : Fin n × Fin n → ℝ :=
    fun p => g₀.inner x (e p.1) v * g₀.inner x (e p.2) w with hcoef_def
  set comp : Fin n × Fin n → ℝ := fun p => B (e p.1) (e p.2) with hcomp_def

  have hexpV : v = ∑ i : Fin n, g₀.inner x (e i) v • e i := hexpand v
  have hexpW : w = ∑ j : Fin n, g₀.inner x (e j) w • e j := hexpand w
  have hvalue : B v w = ∑ p : Fin n × Fin n, coef p * comp p := by
    have hBv : B v = ∑ i : Fin n, g₀.inner x (e i) v • B (e i) := by
      conv_lhs => rw [hexpV]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
    have hBvw : B v w =
        ∑ i : Fin n, g₀.inner x (e i) v • (B (e i) w) := by
      rw [hBv, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ContinuousLinearMap.smul_apply]
    have hBeiw : ∀ i : Fin n, B (e i) w =
        ∑ j : Fin n, g₀.inner x (e j) w • B (e i) (e j) := by
      intro i
      conv_lhs => rw [hexpW]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul]
    rw [hBvw]
    have hdouble : (∑ i : Fin n, g₀.inner x (e i) v • (B (e i) w)) =
        ∑ i : Fin n, ∑ j : Fin n,
          (g₀.inner x (e i) v * g₀.inner x (e j) w) • B (e i) (e j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hBeiw i, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_smul]
    rw [hdouble, ← Fintype.sum_prod_type'
      (f := fun (i j : Fin n) =>
        (g₀.inner x (e i) v * g₀.inner x (e j) w) • B (e i) (e j))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hcoef_def, hcomp_def, smul_eq_mul]

  have hCS : (∑ p : Fin n × Fin n, coef p * comp p) ^ 2 ≤
      (∑ p : Fin n × Fin n, coef p ^ 2) * ∑ p : Fin n × Fin n, comp p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp

  have hcoefsq : (∑ p : Fin n × Fin n, coef p ^ 2) =
      g₀.inner x v v * g₀.inner x w w := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => coef p ^ 2)]
    rw [show (∑ i : Fin n, ∑ j : Fin n, coef (i, j) ^ 2) =
          (∑ i : Fin n, g₀.inner x (e i) v ^ 2) *
            ∑ j : Fin n, g₀.inner x (e j) w ^ 2 from ?_]
    · rw [hpars v, hpars w]
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hcoef_def]
      ring

  have hcomp_fiber : ∀ (K : Fin 0 → Fin n) (i j : Fin n),
      comp (i, j) = fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        (T.toSection x) n e K (![i, j] : Fin 2 → Fin n) := by
    intro K i j

    have hconst : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k))) :
          Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply Tensor0SBundle.tensor0SSpace_ext
      intro u
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k)))) u =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u
      rw [show ((ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u : ℝ) = 1 from rfl]
      change (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ)
          (fun k => g₀.inner x (e (K k)) (u k)) = 1
      rw [ContinuousMultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_of_isEmpty _

    have hcompij : comp (i, j) = ccTensorModel (I := I) g₀ T x ![e i, e j] := by
      rw [hcomp_def, hB_def]
      exact ccTensorBilin_apply (I := I) g₀ T x (e i) (e j)
    rw [hcompij]

    unfold fiberNormSqComponent
    rw [hconst]
    have htuple : (fun k => e ((![i, j] : Fin 2 → Fin n) k)) =
        (![e i, e j] : Fin 2 → TangentSpace I x) := by
      funext k; fin_cases k <;> rfl
    rw [htuple]

    change ccTensorModel (I := I) g₀ T x ![e i, e j] =
      ((T.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        ![e i, e j] : ℝ)
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply]
    rfl
  have hcompsq : (∑ p : Fin n × Fin n, comp p ^ 2) =
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 2 x
      (T.toSection x)]

    rw [hrfns (T.toSection x)]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n =>
      ∑ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 2 (T.toSection x) n e K J)]

    refine (Fintype.sum_equiv (finTwoArrowEquiv (Fin n))
      (fun J : Fin 2 → Fin n =>
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 2 (T.toSection x) n e
          (default : Fin 0 → Fin n) J)
      (fun p : Fin n × Fin n => comp p ^ 2) ?_).symm
    intro J
    have hJ : (![J 0, J 1] : Fin 2 → Fin n) = J := by
      funext k; fin_cases k <;> rfl
    simp only [finTwoArrowEquiv_apply, Equiv.toFun_as_coe, piFinTwoEquiv_apply]
    rw [fiberNormSqSummand_eq_component_sq,
      hcomp_fiber (default : Fin 0 → Fin n) (J 0) (J 1), hJ]

  have hnorm_nn : 0 ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ := norm_nonneg _
  have hvv_nn : 0 ≤ g₀.inner x v v :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hww_nn : 0 ≤ g₀.inner x w w :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have habs_sq : |B v w| ^ 2 ≤
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
        (g₀.inner x v v * g₀.inner x w w) := by
    rw [sq_abs, hvalue]
    calc (∑ p : Fin n × Fin n, coef p * comp p) ^ 2
        ≤ (∑ p : Fin n × Fin n, coef p ^ 2) * ∑ p : Fin n × Fin n, comp p ^ 2 := hCS
      _ = (g₀.inner x v v * g₀.inner x w w) *
            ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
            (g₀.inner x v v * g₀.inner x w w) := by ring

  have hrhs_nn : 0 ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
      Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg (mul_nonneg hnorm_nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (abs_nonneg (B v w))]
  rw [show ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) =
      Real.sqrt (‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
        (g₀.inner x v v * g₀.inner x w w)) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn,
      Real.sqrt_mul hvv_nn, mul_assoc]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilin_scalar_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    (Y W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => smoothCcTensorBilinForm (I := I) g T x (Y x) (W x)) := by
  have h_eval : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        Tensor0SSpace.toModel (ccTensorMultilinear (I := I) g T b)
          (fun i : Fin 2 => (![fun b => Y b, fun b => W b] : Fin 2 → ∀ b : M,
            TangentSpace I b) i b)) :=
    TensorMultilinear.contMDiff_section_apply
      (n := 2) (ccTensorMultilinear (I := I) g T)
      (ccTensorMultilinear (I := I) g T).contMDiff
      (![fun b => Y b, fun b => W b])
      (by
        intro i
        fin_cases i
        · exact Y.contMDiff
        · exact W.contMDiff)
  refine h_eval.congr ?_
  intro x
  rw [ccTensorBilin_apply]
  change ccTensorModel (I := I) g T x ![Y x, W x] =
    ccTensorModel (I := I) g T x _
  congr 1
  funext i
  fin_cases i <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem ccTensorBilin_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (smoothCcTensorBilinForm (I := I) g T b)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => smoothCcTensorBilinForm (I := I) g T x)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => smoothCcTensorBilinForm (I := I) g T x (Y x))
  intro W
  have h_scalar := ccTensorBilin_scalar_contMDiff (I := I) g T Y W
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change smoothCcTensorBilinForm (I := I) g T y (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, smoothCcTensorBilinForm (I := I) g T y (Y y) (W y)⟩).2
  rfl

def ccTensorBilinSymm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (smoothCcTensorBilinForm (I := I) g T x +
    (smoothCcTensorBilinForm (I := I) g T x).flip)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem ccTensorBilinSymm_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g T x v w =
      (1 / 2 : ℝ) *
        (smoothCcTensorBilinForm (I := I) g T x v w +
          smoothCcTensorBilinForm (I := I) g T x w v) := by
  simp only [ccTensorBilinSymm, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_symm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g T x v w =
      ccTensorBilinSymm (I := I) g T x w v := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, add_comm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem ccTensorBilinSymm_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (ccTensorBilinSymm (I := I) g T b)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ccTensorBilinSymm (I := I) g T x)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ccTensorBilinSymm (I := I) g T x (Y x))
  intro W
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilinSymm (I := I) g T x (Y x) (W x)) := by
    have h_eq : (fun x : M => ccTensorBilinSymm (I := I) g T x (Y x) (W x))
        = fun x : M => (1 / 2 : ℝ) *
            (smoothCcTensorBilinForm (I := I) g T x (Y x) (W x) +
              smoothCcTensorBilinForm (I := I) g T x (W x) (Y x)) := by
      funext x; rw [ccTensorBilinSymm_apply]
    rw [h_eq]
    exact (contMDiff_const).mul
      ((ccTensorBilin_scalar_contMDiff (I := I) g T Y W).add
        (ccTensorBilin_scalar_contMDiff (I := I) g T W Y))
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ccTensorBilinSymm (I := I) g T y (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ccTensorBilinSymm (I := I) g T y (Y y) (W y)⟩).2
  rfl

def tensorSectionRealizeMetric (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ) :
    SmoothRiemannianMetric I M :=
  perturbedMetric (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
    (ccTensorBilinSymm_symm (I := I) g T)
    (ccTensorBilinSymm_contMDiff (I := I) g T) hδ_lt hδ

omit [CompactSpace M] in
@[simp] theorem tensorSectionRealizeMetric_inner (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ)
    (x : M) (v w : TangentSpace I x) :
    (tensorSectionRealizeMetric (I := I) g T hδ_lt hδ).inner x v w =
      g.inner x v w + ccTensorBilinSymm (I := I) g T x v w := by
  unfold tensorSectionRealizeMetric
  rw [perturbedMetric_inner, perturbedInner_apply]

omit [CompactSpace M] in
theorem exists_smooth_metric_of_smooth_tensor_small
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g.inner x v w + ccTensorBilinSymm (I := I) g T x v w :=
  ⟨tensorSectionRealizeMetric (I := I) g T hδ'_lt hδ',
    fun x v w => tensorSectionRealizeMetric_inner (I := I) g T hδ'_lt hδ' x v w⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorMultilinear_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (c • T) x : Tensor0SSpace 2 I x)
      = c • (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_smul]
  change ((c • T.toSection) x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
    = c • ((T.toSection x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousLinearMap.smul_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorModel_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (c • T) x = c • ccTensorModel (I := I) g T x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_smul, Tensor0SSpace.toModel_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (c • T) x v w =
      c * ccTensorBilinSymm (I := I) g T x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem gFibreOpBound_ccTensorBilinSymm_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ) :
    metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (c • T)) (|c| * δ) := by
  intro x v w
  rw [ccTensorBilinSymm_smul, abs_mul]
  have hb := hδ x v w
  have hsqv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsqw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  calc |c| * |ccTensorBilinSymm (I := I) g T x v w|
      ≤ |c| * (δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg c)
    _ = |c| * δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

def tensorHsBilinFormSymm (g : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ccTensorBilinSymm (I := I) g
    (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M) u hu_fs) x

theorem exists_smooth_metric_of_tensorHs_small
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg
      (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g_bg.inner x v w + tensorHsBilinFormSymm (I := I) g_bg u hu_fs x v w :=
  exists_smooth_metric_of_smooth_tensor_small (I := I) g_bg
    (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M) u hu_fs) hδ'_lt hδ'

open scoped Classical in

noncomputable def realizeMetricMap (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) :
    SmoothRiemannianMetric I M :=
  if h : ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
      metricCauchySchwarzBound (I := I) (M := M) g_bg
        (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ' then
    tensorSectionRealizeMetric (I := I) g_bg
      (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
        (I := I) (M := M) u h.choose)
      h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  else
    g_bg

theorem realizeMetricMap_eq_of_small (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg
      (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ')
    (x : M) (v w : TangentSpace I x) :
    (realizeMetricMap (I := I) g_bg a u).inner x v w =
      g_bg.inner x v w + tensorHsBilinFormSymm (I := I) g_bg u hu_fs x v w := by
  classical
  have hex : ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
      metricCauchySchwarzBound (I := I) (M := M) g_bg
        (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ' :=
    ⟨hu_fs, δ', hδ'_lt, hδ'⟩
  rw [realizeMetricMap, dif_pos hex]
  rw [tensorSectionRealizeMetric_inner]
  rfl

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
