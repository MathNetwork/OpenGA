import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.BareSlot0CurryParseval
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma frame03_data
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 3 I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin 3 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 3 S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set e : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _ with he_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => e i, ?_, ?_, ?_⟩
  · intro v
    have hpars : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right e v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner x v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner x (e i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (e i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner x v v := hnorm_sq
  · intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i = v :=
      OrthonormalBasis.sum_repr' e v
    have hcongr : (∑ i : Fin n, g.inner x (e i) v • e i) =
        ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hinner_eq (e i) v]
    rw [hcongr, hrepr]
  · intro S
    rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor03_component_eq_toModel
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 3 I x) {n : ℕ} (e : Fin n → TangentSpace I x)
    (J : Fin 3 → Fin n) (K₀ : Fin 0 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 0 3 W n e K₀ J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (fun i : Fin 3 => e (J i)) := by
  classical
  unfold fiberNormSqComponent
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun l : Fin 0 => g₀.inner x (e (K₀ l))) : Tensor0SSpace 0 I x) =
      coframeS (I := I) (M := M) g₀ x 0 e K₀ from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g₀ x e K₀]
  rfl

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem abs_tensor03_unit_eval_le_fibreNorm_mul_sqrt
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 3 I x) (a b c : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
    |Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons a (Fin.cons b ![c]))| ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨n, e, hpars, hexpand, hrfns⟩ := frame03_data (I := I) (M := M) g₀ x
  set vec : Fin 3 → TangentSpace I x := ![a, b, c] with hvec_def
  set Bcmm : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ :=
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from W)
        (unitZeroSec (I := I) (M := M) x)) with hBcmm_def
  set coef : (Fin 3 → Fin n) → ℝ :=
    fun J => ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) with hcoef_def
  set comp : (Fin 3 → Fin n) → ℝ :=
    fun J => Bcmm (fun i : Fin 3 => e (J i)) with hcomp_def
  have hBval : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from W)
        (unitZeroSec (I := I) (M := M) x))
      (Fin.cons a (Fin.cons b ![c])) = Bcmm vec := by
    rw [hBcmm_def]
    congr 1
  rw [hBval]
  have hexp : ∀ i : Fin 3, vec i = ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j :=
    fun i => hexpand (vec i)
  have hvalue : Bcmm vec = ∑ J : Fin 3 → Fin n, coef J * comp J := by
    have hrw : Bcmm vec = Bcmm (fun i : Fin 3 => ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j) := by
      congr 1
      funext i
      exact hexp i
    rw [hrw, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hcoef_def, hcomp_def]
    rw [ContinuousMultilinearMap.map_smul_univ]
    rw [smul_eq_mul]
  have hCS : (∑ J : Fin 3 → Fin n, coef J * comp J) ^ 2 ≤
      (∑ J : Fin 3 → Fin n, coef J ^ 2) * ∑ J : Fin 3 → Fin n, comp J ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hcoefsq : (∑ J : Fin 3 → Fin n, coef J ^ 2) =
      g₀.inner x a a * g₀.inner x b b * g₀.inner x c c := by
    have hpow : ∀ J : Fin 3 → Fin n, coef J ^ 2 =
        ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2 := by
      intro J
      rw [hcoef_def, ← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun J _ => hpow J)]
    rw [show (∑ J : Fin 3 → Fin n, ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2) =
        ∑ J ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset (Fin n))),
          ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2 from by
      rw [Fintype.piFinset_univ]]
    rw [← Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin n)))
      (fun i j => g₀.inner x (e j) (vec i) ^ 2)]
    have hfac : ∏ i : Fin 3, (∑ j : Fin n, g₀.inner x (e j) (vec i) ^ 2) =
        g₀.inner x (vec 0) (vec 0) * (g₀.inner x (vec 1) (vec 1) *
          (g₀.inner x (vec 2) (vec 2) * 1)) := by
      rw [Fin.prod_univ_three]
      rw [hpars (vec 0), hpars (vec 1), hpars (vec 2)]
      ring
    rw [hfac]
    have h0 : vec 0 = a := rfl
    have h1 : vec 1 = b := rfl
    have h2 : vec 2 = c := rfl
    rw [h0, h1, h2]; ring
  have hcompsq : (∑ J : Fin 3 → Fin n, comp J ^ 2) =
      ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 3 x W]
    rw [hrfns W]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n =>
      ∑ J : Fin 3 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 3 W n e K J)]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq,
      tensor03_component_eq_toModel (I := I) (M := M) g₀ x W e J (default : Fin 0 → Fin n)]
  have hnorm_nn : 0 ≤ ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ := norm_nonneg _
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hcc_nn : 0 ≤ g₀.inner x c c := metric_inner_self_nonneg (I := I) (M := M) g₀ x c
  have habs_sq : (Bcmm vec) ^ 2 ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 *
        (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c) := by
    rw [hvalue]
    calc (∑ J : Fin 3 → Fin n, coef J * comp J) ^ 2
        ≤ (∑ J : Fin 3 → Fin n, coef J ^ 2) *
            ∑ J : Fin 3 → Fin n, comp J ^ 2 := hCS
      _ = (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c) *
            ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 *
            (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c) := by ring
  have hrhs_nn : 0 ≤ ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
      Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
        Real.sqrt (g₀.inner x c c) :=
    mul_nonneg (mul_nonneg (mul_nonneg hnorm_nn (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (abs_nonneg (Bcmm vec)), sq_abs]
  rw [show ‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) =
      Real.sqrt (‖(W : Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 *
        (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c)) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn]
    rw [Real.sqrt_mul (mul_nonneg haa_nn hbb_nn), Real.sqrt_mul haa_nn]
    ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma frame04_data
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 4 I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 4 x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin 4 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 4 S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set e : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _ with he_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => e i, ?_, ?_, ?_⟩
  · intro v
    have hpars : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right e v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner x v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner x (e i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (e i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner x v v := hnorm_sq
  · intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i = v :=
      OrthonormalBasis.sum_repr' e v
    have hcongr : (∑ i : Fin n, g.inner x (e i) v • e i) =
        ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hinner_eq (e i) v]
    rw [hcongr, hrepr]
  · intro S
    rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor04_component_eq_toModel
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 4 I x) {n : ℕ} (e : Fin n → TangentSpace I x)
    (J : Fin 4 → Fin n) (K₀ : Fin 0 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 0 4 W n e K₀ J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (fun i : Fin 4 => e (J i)) := by
  classical
  unfold fiberNormSqComponent
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun l : Fin 0 => g₀.inner x (e (K₀ l))) : Tensor0SSpace 0 I x) =
      coframeS (I := I) (M := M) g₀ x 0 e K₀ from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g₀ x e K₀]
  rfl

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem abs_tensor04_unit_eval_le_fibreNorm_mul_sqrt
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 4 I x) (a b c d : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
    |Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons a (Fin.cons b (Fin.cons c ![d])))| ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  obtain ⟨n, e, hpars, hexpand, hrfns⟩ := frame04_data (I := I) (M := M) g₀ x
  set vec : Fin 4 → TangentSpace I x := ![a, b, c, d] with hvec_def
  set Bcmm : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from W)
        (unitZeroSec (I := I) (M := M) x)) with hBcmm_def
  set coef : (Fin 4 → Fin n) → ℝ :=
    fun J => ∏ i : Fin 4, g₀.inner x (e (J i)) (vec i) with hcoef_def
  set comp : (Fin 4 → Fin n) → ℝ :=
    fun J => Bcmm (fun i : Fin 4 => e (J i)) with hcomp_def
  have hBval : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from W)
        (unitZeroSec (I := I) (M := M) x))
      (Fin.cons a (Fin.cons b (Fin.cons c ![d]))) = Bcmm vec := by
    rw [hBcmm_def]
    congr 1
  rw [hBval]
  have hexp : ∀ i : Fin 4, vec i = ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j :=
    fun i => hexpand (vec i)
  have hvalue : Bcmm vec = ∑ J : Fin 4 → Fin n, coef J * comp J := by
    have hrw : Bcmm vec = Bcmm (fun i : Fin 4 => ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j) := by
      congr 1
      funext i
      exact hexp i
    rw [hrw, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hcoef_def, hcomp_def]
    rw [ContinuousMultilinearMap.map_smul_univ]
    rw [smul_eq_mul]
  have hCS : (∑ J : Fin 4 → Fin n, coef J * comp J) ^ 2 ≤
      (∑ J : Fin 4 → Fin n, coef J ^ 2) * ∑ J : Fin 4 → Fin n, comp J ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hcoefsq : (∑ J : Fin 4 → Fin n, coef J ^ 2) =
      g₀.inner x a a * g₀.inner x b b * g₀.inner x c c * g₀.inner x d d := by
    have hpow : ∀ J : Fin 4 → Fin n, coef J ^ 2 =
        ∏ i : Fin 4, g₀.inner x (e (J i)) (vec i) ^ 2 := by
      intro J
      rw [hcoef_def, ← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun J _ => hpow J)]
    rw [show (∑ J : Fin 4 → Fin n, ∏ i : Fin 4, g₀.inner x (e (J i)) (vec i) ^ 2) =
        ∑ J ∈ Fintype.piFinset (fun _ : Fin 4 => (Finset.univ : Finset (Fin n))),
          ∏ i : Fin 4, g₀.inner x (e (J i)) (vec i) ^ 2 from by
      rw [Fintype.piFinset_univ]]
    rw [← Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (Fin n)))
      (fun i j => g₀.inner x (e j) (vec i) ^ 2)]
    have hfac : ∏ i : Fin 4, (∑ j : Fin n, g₀.inner x (e j) (vec i) ^ 2) =
        g₀.inner x (vec 0) (vec 0) * (g₀.inner x (vec 1) (vec 1) *
          (g₀.inner x (vec 2) (vec 2) * (g₀.inner x (vec 3) (vec 3) * 1))) := by
      rw [Fin.prod_univ_four]
      rw [hpars (vec 0), hpars (vec 1), hpars (vec 2), hpars (vec 3)]
      ring
    rw [hfac]
    have h0 : vec 0 = a := rfl
    have h1 : vec 1 = b := rfl
    have h2 : vec 2 = c := rfl
    have h3 : vec 3 = d := rfl
    rw [h0, h1, h2, h3]; ring
  have hcompsq : (∑ J : Fin 4 → Fin n, comp J ^ 2) =
      ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 4 x W]
    rw [hrfns W]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n =>
      ∑ J : Fin 4 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 4 W n e K J)]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq,
      tensor04_component_eq_toModel (I := I) (M := M) g₀ x W e J (default : Fin 0 → Fin n)]
  have hnorm_nn : 0 ≤ ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ := norm_nonneg _
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hcc_nn : 0 ≤ g₀.inner x c c := metric_inner_self_nonneg (I := I) (M := M) g₀ x c
  have hdd_nn : 0 ≤ g₀.inner x d d := metric_inner_self_nonneg (I := I) (M := M) g₀ x d
  have habs_sq : (Bcmm vec) ^ 2 ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2 *
        (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c * g₀.inner x d d) := by
    rw [hvalue]
    calc (∑ J : Fin 4 → Fin n, coef J * comp J) ^ 2
        ≤ (∑ J : Fin 4 → Fin n, coef J ^ 2) *
            ∑ J : Fin 4 → Fin n, comp J ^ 2 := hCS
      _ = (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c * g₀.inner x d d) *
            ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2 *
            (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c * g₀.inner x d d) := by ring
  rw [← Real.sqrt_sq (abs_nonneg (Bcmm vec)), sq_abs]
  rw [show ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d) =
      Real.sqrt (‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2 *
        (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c * g₀.inner x d d)) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn]
    rw [Real.sqrt_mul (mul_nonneg (mul_nonneg haa_nn hbb_nn) hcc_nn),
      Real.sqrt_mul (mul_nonneg haa_nn hbb_nn), Real.sqrt_mul haa_nn]
    ring

private def covGrad3Eval
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)).toSection x)
      (unitZeroSec (I := I) (M := M) x))
    (Fin.cons (P x) (Fin.cons (Q x) ![R x]))

omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad3Eval_eq_metricDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covGrad3Eval (I := I) (M := M) g₀ T P Q R x =
      metricDiffCovDeriv (I := I) g₁ g₀
        (fun b => P b) (fun b => Q b) (fun b => R b) x := by
  have hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T) b u w =
        g₁.inner b u w - g₀.inner b u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁ T hg₁
  rw [covGrad3Eval,
    covGrad02_unitModel_eval_eq_metricDiffCovDeriv' (I := I) (M := M) g₀ g₁ g₀
      (ccTensor02Symm (I := I) g₀ T) hbil P Q R x]
  have hzero : metricDiffCovDeriv (I := I) g₀ g₀
      (fun b => P b) (fun b => Q b) (fun b => R b) x = 0 := by
    unfold metricDiffCovDeriv; rw [sub_self]
  rw [hzero, sub_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma connDiff_inner_eq_half_covGrad3Eval
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    2 * g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      covGrad3Eval (I := I) (M := M) g₀ T X Y Z x
        + covGrad3Eval (I := I) (M := M) g₀ T Y X Z x
        - covGrad3Eval (I := I) (M := M) g₀ T Z X Y x := by
  rw [covGrad3Eval_eq_metricDiff (I := I) (M := M) g₀ g₁ T hg₁ X Y Z x,
    covGrad3Eval_eq_metricDiff (I := I) (M := M) g₀ g₁ T hg₁ Y X Z x,
    covGrad3Eval_eq_metricDiff (I := I) (M := M) g₀ g₁ T hg₁ Z X Y x]
  exact connDiff_koszul_metricDiff (I := I) g₁ g₀
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma abs_covGrad3Eval_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
    |covGrad3Eval (I := I) (M := M) g₀ T P Q R x| ≤
      ‖((covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)).toSection x :
          Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
        Real.sqrt (g₀.inner x (P x) (P x)) *
          Real.sqrt (g₀.inner x (Q x) (Q x)) *
            Real.sqrt (g₀.inner x (R x) (R x)) := by
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  exact abs_tensor03_unit_eval_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ x
    ((covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)).toSection x)
    (P x) (Q x) (R x)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private lemma norm_covGrad_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
    ‖((covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤
      ‖((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
          Tensor0SBundle.TensorRSSpace 0 3 I x)‖ := by
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  set Tsw : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) T with hTsw_def
  have hsymm : ccTensor02Symm (I := I) g₀ T = (1 / 2 : ℝ) • (T + Tsw) := rfl
  have hcovGrad_eq : covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T) =
      (1 / 2 : ℝ) • (covGrad (I := I) (M := M) g₀ 0 2 T +
        covGrad (I := I) (M := M) g₀ 0 2 Tsw) := by
    rw [hsymm, covGrad_smul, covGrad_add]
  have htoSec : ((covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x) =
      (1 / 2 : ℝ) • ((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x +
        (covGrad (I := I) (M := M) g₀ 0 2 Tsw).toSection x) := by
    rw [hcovGrad_eq]
    rfl
  have hsw_norm : ‖((covGrad (I := I) (M := M) g₀ 0 2 Tsw).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ =
      ‖((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
          Tensor0SBundle.TensorRSSpace 0 3 I x)‖ := by
    have hfib := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ (s := 2) (Equiv.swap 0 1) T 1 x
    have hiter : iteratedCovGrad (I := I) g₀ 0 2 1 T =
        covGrad (I := I) (M := M) g₀ 0 2 T := by
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
    have hiter_sw : iteratedCovGrad (I := I) g₀ 0 2 1
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) T) =
        covGrad (I := I) (M := M) g₀ 0 2 Tsw := by
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero, hTsw_def]
    rw [hiter_sw, hiter] at hfib
    rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 3 x,
        riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 3 x] at hfib
    have hnn1 : (0 : ℝ) ≤ ‖((covGrad (I := I) (M := M) g₀ 0 2 Tsw).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ := norm_nonneg _
    have hnn2 : (0 : ℝ) ≤ ‖((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ := norm_nonneg _
    nlinarith [hfib, hnn1, hnn2]
  rw [htoSec, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]; norm_num
  rw [habs]
  have htri := norm_add_le
    ((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)
    ((covGrad (I := I) (M := M) g₀ 0 2 Tsw).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)
  rw [hsw_norm] at htri
  nlinarith [htri, norm_nonneg ((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
    Tensor0SBundle.TensorRSSpace 0 3 I x)]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiff_gFibreNorm_le_iteratedCovGrad
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M) (v w : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  refine ⟨3, by norm_num, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x v w
  have hcoeff : 0 < 1 - δ := by linarith
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x w).choose with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x v).choose with hY_def
  have hXx : X x = w := (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x w).choose_spec
  have hYx : Y x = v := (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x v).choose_spec
  set u : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w with hu_def
  have hu_eq : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) = u := by
    rw [hXx, hYx]
  set θ : Tensor0SSpace 1 I x := koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
    with hθ_def
  have hu_sharp : u = inverseMetricSharpFib (I := I) g₁ x θ := by
    rw [← hu_eq, hθ_def]
    exact connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X Y x
  set p : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x θ with hp_def
  have hθ_flat : θ = g0FlatCLM (I := I) g₀ x p := by
    rw [hp_def, g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x θ]
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x p).choose with hZ_def
  have hZx : Z x = p := (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x p).choose_spec
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  set Nw : ℝ := Real.sqrt (g₀.inner x w w) with hNw_def
  set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNp_def
  set Gnorm : ℝ := ‖((covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hGnorm_def
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNw_nn : 0 ≤ Nw := Real.sqrt_nonneg _
  have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
  have hGnorm_nn : 0 ≤ Gnorm := norm_nonneg _

  have hpp_eq : g₀.inner x p p = g₁.inner x u (Z x) := by
    have h1 : g₀.inner x p p =
        cotangentToDualLinear (I := I) θ p := by
      rw [hp_def, inverseMetricSharpFib_inner (I := I) g₀ x θ p]
    rw [h1, cotangentToDualLinear_apply]
    rw [show cotangentToDual (I := I) θ p = cotangentToDual (I := I) θ (Z x) from by
      rw [hZx]]
    rw [hθ_def]
    rw [koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x (Z x)]
    rw [hu_eq]

  have hkoszul : 2 * g₁.inner x u (Z x) =
      covGrad3Eval (I := I) (M := M) g₀ T X Y Z x
        + covGrad3Eval (I := I) (M := M) g₀ T Y X Z x
        - covGrad3Eval (I := I) (M := M) g₀ T Z X Y x := by
    have h := connDiff_inner_eq_half_covGrad3Eval (I := I) (M := M) g₀ g₁ T hg₁ X Y Z x
    rw [hu_eq] at h
    exact h

  have hbd1 := abs_covGrad3Eval_le (I := I) (M := M) g₀ T X Y Z x
  have hbd2 := abs_covGrad3Eval_le (I := I) (M := M) g₀ T Y X Z x
  have hbd3 := abs_covGrad3Eval_le (I := I) (M := M) g₀ T Z X Y x
  rw [hXx, hYx, hZx, ← hGnorm_def, ← hNv_def, ← hNw_def, ← hNp_def] at hbd1 hbd2 hbd3

  have htriple : |2 * g₀.inner x p p| ≤ 3 * Gnorm * Nv * Nw * Np := by
    rw [hpp_eq, hkoszul]
    have hsum : |covGrad3Eval (I := I) (M := M) g₀ T X Y Z x
          + covGrad3Eval (I := I) (M := M) g₀ T Y X Z x
          - covGrad3Eval (I := I) (M := M) g₀ T Z X Y x| ≤
        |covGrad3Eval (I := I) (M := M) g₀ T X Y Z x|
          + |covGrad3Eval (I := I) (M := M) g₀ T Y X Z x|
          + |covGrad3Eval (I := I) (M := M) g₀ T Z X Y x| := by
      have ht1 := abs_sub (covGrad3Eval (I := I) (M := M) g₀ T X Y Z x
          + covGrad3Eval (I := I) (M := M) g₀ T Y X Z x)
        (covGrad3Eval (I := I) (M := M) g₀ T Z X Y x)
      have ht2 := abs_add_le (covGrad3Eval (I := I) (M := M) g₀ T X Y Z x)
        (covGrad3Eval (I := I) (M := M) g₀ T Y X Z x)
      linarith [ht1, ht2]
    refine hsum.trans ?_
    nlinarith [hbd1, hbd2, hbd3, hGnorm_nn, hNv_nn, hNw_nn, hNp_nn]

  have hNp_le : Np ≤ (3 / 2) * Gnorm * Nv * Nw := by
    have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
    have hNp_sq : Np ^ 2 = g₀.inner x p p := by
      rw [hNp_def, Real.sq_sqrt hpp_nn]
    have htriple' : 2 * g₀.inner x p p ≤ 3 * Gnorm * Nv * Nw * Np := by
      have := (abs_le.mp htriple).2
      linarith [this]
    have hK_nn : 0 ≤ (3 / 2) * Gnorm * Nv * Nw :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGnorm_nn) hNv_nn) hNw_nn
    nlinarith [htriple', hNp_sq, hNp_nn, hK_nn]

  have hneumann : Real.sqrt (g₀.inner x u u) ≤ (1 / (1 - δ)) * Np := by
    have hsfib := norm_inverseMetricSharpFib_g0Flat_le
      (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T) hg₁
      (by linarith : δ < 1) hδ0 hbound x p
    rw [← hNp_def] at hsfib
    have huu : g₀.inner x u u =
        g₀.inner x (inverseMetricSharpFib (I := I) g₁ x
            (g0FlatCLM (I := I) g₀ x p))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x p)) := by
      rw [hu_sharp, ← hθ_flat]
    rw [huu]
    exact hsfib

  have hsymmnorm := norm_covGrad_symmS_le (I := I) (M := M) g₀ T x
  rw [← hGnorm_def] at hsymmnorm
  have hiter_norm : ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ =
      ‖((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ := by
    have hiter : iteratedCovGrad (I := I) g₀ 0 2 1 T =
        covGrad (I := I) (M := M) g₀ 0 2 T := by
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
    rw [hiter]
  rw [hiter_norm]
  set Gt : ℝ := ‖((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hGt_def
  have hGt_nn : 0 ≤ Gt := norm_nonneg _
  have hGle : Gnorm ≤ Gt := hsymmnorm

  have hinv_le : 1 / (1 - δ) ≤ 2 := by
    rw [div_le_iff₀ hcoeff]; linarith
  have hstep : Real.sqrt (g₀.inner x u u) ≤ (1 / (1 - δ)) * ((3 / 2) * Gnorm * Nv * Nw) := by
    refine hneumann.trans ?_
    have hinv_nn : 0 ≤ 1 / (1 - δ) := by positivity
    exact mul_le_mul_of_nonneg_left hNp_le hinv_nn
  refine hstep.trans ?_
  have hbase_nn : 0 ≤ (3 / 2) * Gnorm * Nv * Nw :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGnorm_nn) hNv_nn) hNw_nn
  have h1 : (1 / (1 - δ)) * ((3 / 2) * Gnorm * Nv * Nw) ≤ 2 * ((3 / 2) * Gnorm * Nv * Nw) :=
    mul_le_mul_of_nonneg_right hinv_le hbase_nn
  refine h1.trans ?_
  have h2 : 2 * ((3 / 2) * Gnorm * Nv * Nw) = 3 * Gnorm * Nv * Nw := by ring
  rw [h2]
  have h3 : 3 * Gnorm * Nv * Nw ≤ 3 * Gt * Nv * Nw := by
    have hf : (3 : ℝ) * Gnorm ≤ 3 * Gt := by linarith
    have hf2 : 3 * Gnorm * Nv ≤ 3 * Gt * Nv :=
      mul_le_mul_of_nonneg_right hf hNv_nn
    exact mul_le_mul_of_nonneg_right hf2 hNw_nn
  exact h3

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (_hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M) (v w : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  have hceil0 : 0 < 1 - δ₀ := by linarith
  refine ⟨(1 / (1 - δ₀)) * (3 / 2), by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x v w
  have hcoeff : 0 < 1 - δ := by linarith
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x w).choose with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x v).choose with hY_def
  have hXx : X x = w := (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x w).choose_spec
  have hYx : Y x = v := (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x v).choose_spec
  set u : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w with hu_def
  have hu_eq : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) = u := by
    rw [hXx, hYx]
  set θ : Tensor0SSpace 1 I x := koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
    with hθ_def
  have hu_sharp : u = inverseMetricSharpFib (I := I) g₁ x θ := by
    rw [← hu_eq, hθ_def]
    exact connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X Y x
  set p : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x θ with hp_def
  have hθ_flat : θ = g0FlatCLM (I := I) g₀ x p := by
    rw [hp_def, g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x θ]
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x p).choose with hZ_def
  have hZx : Z x = p := (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x p).choose_spec
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  set Nw : ℝ := Real.sqrt (g₀.inner x w w) with hNw_def
  set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNp_def
  set Gnorm : ℝ := ‖((covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T)).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hGnorm_def
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNw_nn : 0 ≤ Nw := Real.sqrt_nonneg _
  have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
  have hGnorm_nn : 0 ≤ Gnorm := norm_nonneg _
  have hpp_eq : g₀.inner x p p = g₁.inner x u (Z x) := by
    have h1 : g₀.inner x p p =
        cotangentToDualLinear (I := I) θ p := by
      rw [hp_def, inverseMetricSharpFib_inner (I := I) g₀ x θ p]
    rw [h1, cotangentToDualLinear_apply]
    rw [show cotangentToDual (I := I) θ p = cotangentToDual (I := I) θ (Z x) from by
      rw [hZx]]
    rw [hθ_def]
    rw [koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x (Z x)]
    rw [hu_eq]
  have hkoszul : 2 * g₁.inner x u (Z x) =
      covGrad3Eval (I := I) (M := M) g₀ T X Y Z x
        + covGrad3Eval (I := I) (M := M) g₀ T Y X Z x
        - covGrad3Eval (I := I) (M := M) g₀ T Z X Y x := by
    have h := connDiff_inner_eq_half_covGrad3Eval (I := I) (M := M) g₀ g₁ T hg₁ X Y Z x
    rw [hu_eq] at h
    exact h
  have hbd1 := abs_covGrad3Eval_le (I := I) (M := M) g₀ T X Y Z x
  have hbd2 := abs_covGrad3Eval_le (I := I) (M := M) g₀ T Y X Z x
  have hbd3 := abs_covGrad3Eval_le (I := I) (M := M) g₀ T Z X Y x
  rw [hXx, hYx, hZx, ← hGnorm_def, ← hNv_def, ← hNw_def, ← hNp_def] at hbd1 hbd2 hbd3
  have htriple : |2 * g₀.inner x p p| ≤ 3 * Gnorm * Nv * Nw * Np := by
    rw [hpp_eq, hkoszul]
    have hsum : |covGrad3Eval (I := I) (M := M) g₀ T X Y Z x
          + covGrad3Eval (I := I) (M := M) g₀ T Y X Z x
          - covGrad3Eval (I := I) (M := M) g₀ T Z X Y x| ≤
        |covGrad3Eval (I := I) (M := M) g₀ T X Y Z x|
          + |covGrad3Eval (I := I) (M := M) g₀ T Y X Z x|
          + |covGrad3Eval (I := I) (M := M) g₀ T Z X Y x| := by
      have ht1 := abs_sub (covGrad3Eval (I := I) (M := M) g₀ T X Y Z x
          + covGrad3Eval (I := I) (M := M) g₀ T Y X Z x)
        (covGrad3Eval (I := I) (M := M) g₀ T Z X Y x)
      have ht2 := abs_add_le (covGrad3Eval (I := I) (M := M) g₀ T X Y Z x)
        (covGrad3Eval (I := I) (M := M) g₀ T Y X Z x)
      linarith [ht1, ht2]
    refine hsum.trans ?_
    nlinarith [hbd1, hbd2, hbd3, hGnorm_nn, hNv_nn, hNw_nn, hNp_nn]
  have hNp_le : Np ≤ (3 / 2) * Gnorm * Nv * Nw := by
    have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
    have hNp_sq : Np ^ 2 = g₀.inner x p p := by
      rw [hNp_def, Real.sq_sqrt hpp_nn]
    have htriple' : 2 * g₀.inner x p p ≤ 3 * Gnorm * Nv * Nw * Np := by
      have := (abs_le.mp htriple).2
      linarith [this]
    have hK_nn : 0 ≤ (3 / 2) * Gnorm * Nv * Nw :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGnorm_nn) hNv_nn) hNw_nn
    nlinarith [htriple', hNp_sq, hNp_nn, hK_nn]
  have hneumann : Real.sqrt (g₀.inner x u u) ≤ (1 / (1 - δ)) * Np := by
    have hsfib := norm_inverseMetricSharpFib_g0Flat_le
      (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T) hg₁
      (by linarith : δ < 1) hδ0 hbound x p
    rw [← hNp_def] at hsfib
    have huu : g₀.inner x u u =
        g₀.inner x (inverseMetricSharpFib (I := I) g₁ x
            (g0FlatCLM (I := I) g₀ x p))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x p)) := by
      rw [hu_sharp, ← hθ_flat]
    rw [huu]
    exact hsfib
  have hsymmnorm := norm_covGrad_symmS_le (I := I) (M := M) g₀ T x
  rw [← hGnorm_def] at hsymmnorm
  have hiter_norm : ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ =
      ‖((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ := by
    have hiter : iteratedCovGrad (I := I) g₀ 0 2 1 T =
        covGrad (I := I) (M := M) g₀ 0 2 T := by
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
    rw [hiter]
  rw [hiter_norm]
  set Gt : ℝ := ‖((covGrad (I := I) (M := M) g₀ 0 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hGt_def
  have hGt_nn : 0 ≤ Gt := norm_nonneg _
  have hGle : Gnorm ≤ Gt := hsymmnorm
  have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
    rw [div_le_div_iff₀ hcoeff hceil0]; linarith
  have hstep : Real.sqrt (g₀.inner x u u) ≤ (1 / (1 - δ)) * ((3 / 2) * Gnorm * Nv * Nw) := by
    refine hneumann.trans ?_
    have hinv_nn : 0 ≤ 1 / (1 - δ) := by positivity
    exact mul_le_mul_of_nonneg_left hNp_le hinv_nn
  refine hstep.trans ?_
  have hbase_nn : 0 ≤ (3 / 2) * Gnorm * Nv * Nw :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGnorm_nn) hNv_nn) hNw_nn
  have h1 : (1 / (1 - δ)) * ((3 / 2) * Gnorm * Nv * Nw) ≤
      (1 / (1 - δ₀)) * ((3 / 2) * Gnorm * Nv * Nw) :=
    mul_le_mul_of_nonneg_right hinv_le hbase_nn
  refine h1.trans ?_
  have hinv₀_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  have hGmul : (3 / 2) * Gnorm * Nv * Nw ≤ (3 / 2) * Gt * Nv * Nw := by
    have hf : (3 / 2 : ℝ) * Gnorm ≤ (3 / 2) * Gt := by linarith
    have hf2 : (3 / 2) * Gnorm * Nv ≤ (3 / 2) * Gt * Nv :=
      mul_le_mul_of_nonneg_right hf hNv_nn
    exact mul_le_mul_of_nonneg_right hf2 hNw_nn
  have hcombine : (1 / (1 - δ₀)) * ((3 / 2) * Gnorm * Nv * Nw) ≤
      (1 / (1 - δ₀)) * ((3 / 2) * Gt * Nv * Nw) :=
    mul_le_mul_of_nonneg_left hGmul hinv₀_nn
  refine hcombine.trans ?_
  have hfinal : (1 / (1 - δ₀)) * ((3 / 2) * Gt * Nv * Nw) =
      (1 / (1 - δ₀)) * (3 / 2) * Gt * Nv * Nw := by ring
  rw [hfinal]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_connDiffFib
    (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        (connDiffFib (I := I) g₁ g₀ x) n e K J =
      g₀.inner x (e (K 0))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        (connDiffFib (I := I) g₁ g₀ x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 1) ℝ).compContinuousLinearMap
          (fun k => g₀.inner x (e (K k)))))
        (fun k => e (J k)) from rfl]
  rw [connDiffFib_apply_eval]
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 1) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e (K k))))
      (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        ((fun k => e (J k)) 0) ((fun k => e (J k)) 1)) =
      ∏ k : Fin 1, g₀.inner x (e (K k))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1))) from rfl]
  rw [Fin.prod_univ_one]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffSection_riemannianFiberNormSq_le_iteratedCovGrad
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ := connDiff_gFibreNorm_le_iteratedCovGrad (I := I) (M := M) g₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * C₀, by positivity, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := hn
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hconnDiffSec : (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x :=
    connDiffSection_toSection (I := I) g₁ g₀ x
  rw [hconnDiffSec]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x
    (connDiffFib (I := I) g₁ g₀ x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        (connDiffFib (I := I) g₁ g₀ x) n e K J) ^ 2 ≤ C₀ ^ 2 * G ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_connDiffFib]
    set u : TangentSpace I x :=
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)) with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hkk : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by
      rw [horth (K 0) (K 0)]; simp
    rw [hkk, one_mul] at hcs
    have hsqrt := hpw g₁ T h hδ hδ0 hbound x (e (J 0)) (e (J 1))
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one] at hsqrt
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u :=
      Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hsq_le : g₀.inner x u u ≤ (C₀ * G) ^ 2 := by
      rw [← hsqrt_eq]
      have := mul_self_le_mul_self hsqrt_nn hsqrt
      nlinarith [this, hsqrt]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (C₀ * G) ^ 2 := hsq_le
      _ = C₀ ^ 2 * G ^ 2 := by ring
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
          (connDiffFib (I := I) g₁ g₀ x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n, C₀ ^ 2 * G ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
        (C₀ ^ 2 * G ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * C₀) ^ 2 * G ^ 2 := by
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        rw [Fintype.card_fin, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 3) ^ 2 = (n : ℝ) ^ 3 :=
          Real.sq_sqrt (by positivity)
        rw [mul_pow, hsq]
        push_cast
        ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffSection_riemannianFiberNormSq_le_iteratedCovGrad_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * C₀, by positivity, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := hn
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hconnDiffSec : (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x :=
    connDiffSection_toSection (I := I) g₁ g₀ x
  rw [hconnDiffSec]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x
    (connDiffFib (I := I) g₁ g₀ x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        (connDiffFib (I := I) g₁ g₀ x) n e K J) ^ 2 ≤ C₀ ^ 2 * G ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_connDiffFib]
    set u : TangentSpace I x :=
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)) with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hkk : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by
      rw [horth (K 0) (K 0)]; simp
    rw [hkk, one_mul] at hcs
    have hsqrt := hpw g₁ T h hδ hδ0 hbound x (e (J 0)) (e (J 1))
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one] at hsqrt
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u :=
      Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hsq_le : g₀.inner x u u ≤ (C₀ * G) ^ 2 := by
      rw [← hsqrt_eq]
      have := mul_self_le_mul_self hsqrt_nn hsqrt
      nlinarith [this, hsqrt]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (C₀ * G) ^ 2 := hsq_le
      _ = C₀ ^ 2 * G ^ 2 := by ring
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
          (connDiffFib (I := I) g₁ g₀ x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n, C₀ ^ 2 * G ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
        (C₀ ^ 2 * G ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * C₀) ^ 2 * G ^ 2 := by
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        rw [Fintype.card_fin, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 3) ^ 2 = (n : ℝ) ^ 3 :=
          Real.sq_sqrt (by positivity)
        rw [mul_pow, hsq]
        push_cast
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
