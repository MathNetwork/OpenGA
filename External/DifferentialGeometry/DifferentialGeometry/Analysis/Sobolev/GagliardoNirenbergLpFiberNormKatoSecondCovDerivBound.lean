import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RankRReadingDominationUniformSup
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormDiscreteLogConvex
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormHolderIntegrability
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GagliardoNirenbergLpFiberNormCovGradFrameSum

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section GeneralValenceRS

open Bundle Tensor0SBundle Tensor0SNabla TensorRSNabla TensorMultilinear

set_option maxHeartbeats 1600000 in

private theorem secondCovDeriv_frame_diag_fiberNormSq_sum_le_rs
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (w : Integral.L2.SmoothCcTensor g r m) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g r m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g r m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) ≤
      riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
        ((covGrad (I := I) (M := M) g r (m + 1)
            (covGrad (I := I) (M := M) g r m w)).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b

  set T2 : Tensor0SBundle.TensorRSSpace r (m + 1 + 1) I x :=
    (covGrad (I := I) (M := M) g r (m + 1)
      (covGrad (I := I) (M := M) g r m w)).toSection x with hT2_def

  have hcomp : ∀ (i : Fin n) (K : Fin r → Fin n) (J : Fin m → Fin n),
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r m
          (Integral.Connection.tensorSecondCovDeriv (I := I) g r m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) n e K J =
        Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
          (Fin.cons i (Fin.cons i J)) := by
    intro i K J
    set ωK : Tensor0SBundle.Tensor0SSpace r I x :=
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k))) with hωK

    have htuple : (fun k : Fin (m + 1 + 1) =>
          e ((Fin.cons i (Fin.cons i J) : Fin (m + 1 + 1) → Fin n) k)) =
        Fin.cons (e i) (Fin.cons (e i) (fun k : Fin m => e (J k))) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · simp
      · intro j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro l; simp

    have hbridge := secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) (M := M) g r m w
      (Integral.Connection.smoothOrthoFrame_smooth (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame_smooth (I := I) g x i) x ωK
      (fun k : Fin m => e (J k))

    change ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace m I x from
          Integral.Connection.tensorSecondCovDeriv (I := I) g r m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) ωK) (fun k : Fin m => e (J k)) =
      ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (m + 1 + 1) I x
          from T2) ωK)
        (fun k : Fin (m + 1 + 1) =>
          e ((Fin.cons i (Fin.cons i J) : Fin (m + 1 + 1) → Fin n) k))
    rw [show ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace
            (m + 1 + 1) I x from T2) ωK)
          (fun k : Fin (m + 1 + 1) =>
            e ((Fin.cons i (Fin.cons i J) : Fin (m + 1 + 1) → Fin n) k)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace
              (m + 1 + 1) I x from T2) ωK)
          (Fin.cons (e i) (Fin.cons (e i) (fun k : Fin m => e (J k)))) from by
      rw [htuple]; rfl]
    rw [hT2_def]
    exact hbridge.symm

  have hdiag_term : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g r m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) =
        ∑ K : Fin r → Fin n, ∑ J : Fin m → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
            (Fin.cons i (Fin.cons i J))) ^ 2 := by
    intro i
    rw [riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_orthonormalFrame (I := I) (M := M) g r m x _ e hn_def
      horth]
    refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
    rw [hcomp i K J]

  rw [riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_orthonormalFrame (I := I) (M := M) g r (m + 1 + 1) x T2 e
    hn_def horth]
  rw [Finset.sum_congr rfl (fun i _ => hdiag_term i)]

  have hfull : ∀ K : Fin r → Fin n,
      (∑ J : Fin (m + 1 + 1) → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
            J) ^ 2) =
        ∑ a : Fin n, ∑ b : Fin n, ∑ J : Fin m → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
            (Fin.cons a (Fin.cons b J))) ^ 2 := by
    intro K
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin n))
          (fun pr : Fin n × (Fin (m + 1) → Fin n) =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
              (Fin.cons pr.1 pr.2)) ^ 2)
          (fun J'' : Fin (m + 1 + 1) → Fin n =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
              J'') ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n))
          (fun pr : Fin n × (Fin m → Fin n) =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
              (Fin.cons a (Fin.cons pr.1 pr.2))) ^ 2)
          (fun J' : Fin (m + 1) → Fin n =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
              (Fin.cons a J')) ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]

  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun K _ => ?_)
  rw [hfull K]

  refine Finset.sum_le_sum (fun i _ => ?_)
  exact Finset.single_le_sum (f := fun b : Fin n =>
      ∑ J : Fin m → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (m + 1 + 1) T2 n e K
          (Fin.cons i (Fin.cons b J))) ^ 2)
    (fun b _ => Finset.sum_nonneg (fun J _ => sq_nonneg _)) (Finset.mem_univ i)

set_option maxHeartbeats 1600000 in

theorem rawConnLap_innerWith_sqrt_finrank_bound_rs
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (w : Integral.L2.SmoothCcTensor g r m) (x : M) :
    |Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        ((rawTensorConnLapSmooth (I := I) g r m w).toFun x) (w.toFun x)| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
          ((covGrad (I := I) (M := M) g r (m + 1)
            (covGrad (I := I) (M := M) g r m w)).toSection x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set aw : ℝ := riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) with haw_def
  set cw : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
      ((covGrad (I := I) (M := M) g r (m + 1)
        (covGrad (I := I) (M := M) g r m w)).toSection x) with hcw_def
  have haw_nn : 0 ≤ aw := riemannianFiberNormSq_nonneg (I := I) (M := M) g r m x _
  have hcw_nn : 0 ≤ cw := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) x _

  set D : Fin n → Tensor0SBundle.TensorRSSpace r m I x :=
    fun i => Integral.Connection.tensorSecondCovDeriv (I := I) g r m
      (Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (fun y : M => w.toSection y) x with hD_def

  have htrace : (rawTensorConnLapSmooth (I := I) g r m w).toFun x =
      Tensor0SBundle.TensorRSSpace.toModel (∑ i : Fin n, D i) := by
    have h1 : (rawTensorConnLapSmooth (I := I) g r m w).toFun x =
        Tensor0SBundle.TensorRSSpace.toModel
          ((rawTensorConnLapSmooth (I := I) g r m w).toSection x) := rfl
    rw [h1, Integral.Connection.rawTensorConnLapSmooth_toSection_apply (I := I) (M := M) g r m w x,
      Integral.Connection.rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r m
        (fun y : M => w.toSection y) x]

  have hsum_aux : ∀ (s' : Finset (Fin n)),
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
          (Tensor0SBundle.TensorRSSpace.toModel (∑ i ∈ s', D i)) (w.toFun x) =
        ∑ i ∈ s', Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
          (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x) := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, Tensor0SBundle.TensorRSSpace.toModel_zero]
        exact Integral.L2.tensorInnerPointwise_zero_left (I := I) (M := M) g r m x (w.toFun x)
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, Finset.sum_insert hi₀, Tensor0SBundle.TensorRSSpace.toModel_add,
          Integral.L2.tensorInnerPointwise_add_left, ih]
  have hsum : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        ((rawTensorConnLapSmooth (I := I) g r m w).toFun x) (w.toFun x) =
      ∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x) := by
    rw [htrace]
    exact hsum_aux Finset.univ

  set rr : Fin n → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g r m x (D i) with hrr_def
  have hrr_nn : ∀ i, 0 ≤ rr i := fun i =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r m x (D i)
  have hCSi : ∀ i, |Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤
      Real.sqrt (rr i) * Real.sqrt aw := by
    intro i
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r m x
      (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)
    have hDi_self : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i))
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) = rr i := by
      rw [show rr i = riemannianFiberNormSq (I := I) (M := M) g r m x (D i) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r m x (D i)]
    have hw_self : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (w.toFun x) (w.toFun x) = aw := by
      rw [show aw = riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r m x (w.toSection x)]
      rfl
    rw [hDi_self, hw_self] at hsq
    have habs : |Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤ Real.sqrt (rr i * aw) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (hrr_nn i)] at habs
    exact habs
  rw [hsum]
  have hstep1 : |∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤
      ∑ i : Fin n, Real.sqrt (rr i) * Real.sqrt aw := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun i _ => hCSi i)
  have hdiscrete : (∑ i : Fin n, Real.sqrt (rr i)) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, rr i := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ)) (fun i => Real.sqrt (rr i))
    have hone : ∑ _i : Fin n, (1 : ℝ) ^ 2 = (n : ℝ) := by
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
    have hsqrt_sq : ∑ i : Fin n, Real.sqrt (rr i) ^ 2 = ∑ i : Fin n, rr i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.sq_sqrt (hrr_nn i)]
    have hlhs : (∑ i : Fin n, (1 : ℝ) * Real.sqrt (rr i)) = ∑ i : Fin n, Real.sqrt (rr i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_mul]
    rw [hlhs, hone, hsqrt_sq] at hcs
    exact hcs
  have hdiag : ∑ i : Fin n, rr i ≤ cw :=
    secondCovDeriv_frame_diag_fiberNormSq_sum_le_rs (I := I) (M := M) g r m w x
  have hsum_sqrt_nn : 0 ≤ ∑ i : Fin n, Real.sqrt (rr i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsum_r_nn : 0 ≤ ∑ i : Fin n, rr i := Finset.sum_nonneg (fun i _ => hrr_nn i)
  have hsqrt_bound : ∑ i : Fin n, Real.sqrt (rr i) ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw := by
    have h1 : ∑ i : Fin n, Real.sqrt (rr i) ≤ Real.sqrt ((n : ℝ) * ∑ i : Fin n, rr i) := by
      rw [← Real.sqrt_sq hsum_sqrt_nn]
      exact Real.sqrt_le_sqrt hdiscrete
    have h2 : Real.sqrt ((n : ℝ) * ∑ i : Fin n, rr i) ≤ Real.sqrt ((n : ℝ) * cw) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdiag hn_nn)
    have h3 : Real.sqrt ((n : ℝ) * cw) = Real.sqrt (n : ℝ) * Real.sqrt cw :=
      Real.sqrt_mul hn_nn cw
    calc ∑ i : Fin n, Real.sqrt (rr i)
        ≤ Real.sqrt ((n : ℝ) * ∑ i : Fin n, rr i) := h1
      _ ≤ Real.sqrt ((n : ℝ) * cw) := h2
      _ = Real.sqrt (n : ℝ) * Real.sqrt cw := h3
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw := by rw [hn_def]
  calc |∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
          (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)|
      ≤ ∑ i : Fin n, Real.sqrt (rr i) * Real.sqrt aw := hstep1
    _ = (∑ i : Fin n, Real.sqrt (rr i)) * Real.sqrt aw := by rw [← Finset.sum_mul]
    _ ≤ (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw) * Real.sqrt aw := by
        exact mul_le_mul_of_nonneg_right hsqrt_bound (Real.sqrt_nonneg _)
    _ = Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt aw * Real.sqrt cw := by ring

set_option maxHeartbeats 1600000 in

omit [CompactSpace M] in
private theorem mfderiv_riemannianFiberNormSq_eq_two_mul_covDeriv_inner_rs
    (g : SmoothRiemannianMetric I M) (r p : ℕ)
    (Q : Integral.L2.SmoothCcTensor g r p) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I)
        (fun y : M => riemannianFiberNormSq (I := I) (M := M) g r p y (Q.toSection y)) x v =
      2 * Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p x
        (Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r p Q x v))
        (Q.toFun x) := by
  classical
  have hfun : (fun y : M => riemannianFiberNormSq (I := I) (M := M) g r p y (Q.toSection y)) =
      fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p y
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y)) := by
    funext y
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r p y (Q.toSection y)]
  rw [hfun]
  rw [show extDerivFun (I := I)
        (fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p y
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))) x v =
      mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p y
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))) x v from rfl]
  rw [Integral.Connection.tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (I := I) (M := M) g r p Q.toSection Q.toSection x v]
  have hbridge : Integral.L2.covariantTensorInnerPointwise (I := I) (M := M) (r + p) g x
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g r p Q.toSection x v))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.liftedTensorSection (I := I) (M := M) g r p Q.toSection x)) =
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p x
        (Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r p Q x v))
        (Q.toFun x) := by
    rw [show Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r p Q x v))
          (Q.toFun x) =
        Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r p Q x v))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) from rfl]
    unfold Integral.L2.tensorInnerPointwise
    rw [show Integral.L2.lowerAllUpperIndices (I := I) (M := M) g r p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r p Q x v)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g r p Q.toSection x v) from by
      rw [tensorCovDerivAt_def (I := I) (M := M) g r p Q x v]
      exact (Integral.Connection.loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs
        (I := I) (M := M) g r p Q.toSection x v).symm]
    rw [show Integral.L2.lowerAllUpperIndices (I := I) (M := M) g r p x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.liftedTensorSection (I := I) (M := M) g r p Q.toSection x) from
      (Integral.Connection.toModel_liftedTensorSection
        (I := I) (M := M) g r p Q.toSection x).symm]
  rw [hbridge]
  rw [Integral.L2.tensorInnerPointwise_0s_symm (I := I) (M := M) g x (r + p)
      (Tensor0SBundle.Tensor0SSpace.toModel
        (Integral.Connection.liftedTensorSection (I := I) (M := M) g r p Q.toSection x))
      (Tensor0SBundle.Tensor0SSpace.toModel
        (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g r p Q.toSection x v))]
  rw [hbridge]
  ring

set_option maxHeartbeats 1600000 in

theorem kato_mfderiv_riemannianFiberNormSq_frame_sum_le_rs
    (g : SmoothRiemannianMetric I M) (r p : ℕ)
    (Q : Integral.L2.SmoothCcTensor g r p) (x : M) :
    ∑ a : Fin (Module.finrank ℝ E),
        (extDerivFun (I := I)
          (fun y : M => riemannianFiberNormSq (I := I) (M := M) g r p y (Q.toSection y)) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g r p x (Q.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g r (p + 1) x
          ((covGrad (I := I) (M := M) g r p Q).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  set rQ : ℝ := riemannianFiberNormSq (I := I) (M := M) g r p x (Q.toSection x) with hrQ_def
  have hrQ_nn : 0 ≤ rQ := riemannianFiberNormSq_nonneg (I := I) (M := M) g r p x (Q.toSection x)

  set V : Fin n → Tensor0SBundle.TensorRSSpace r p I x :=
    fun a => tensorCovDerivAt (I := I) (M := M) g r p Q x (e a) with hV_def
  set ss : Fin n → ℝ := fun a => riemannianFiberNormSq (I := I) (M := M) g r p x (V a) with hss_def
  have hss_nn : ∀ a, 0 ≤ ss a := fun a =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r p x (V a)

  have hterm : ∀ a : Fin n,
      (extDerivFun (I := I)
        (fun y : M => riemannianFiberNormSq (I := I) (M := M) g r p y (Q.toSection y)) x (e a)) ^ 2 ≤
        4 * ss a * rQ := by
    intro a
    rw [mfderiv_riemannianFiberNormSq_eq_two_mul_covDeriv_inner_rs (I := I) (M := M) g r p Q x (e a)]
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r p x
      (Tensor0SBundle.TensorRSSpace.toModel (V a)) (Q.toFun x)
    have hVself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p x
        (Tensor0SBundle.TensorRSSpace.toModel (V a))
        (Tensor0SBundle.TensorRSSpace.toModel (V a)) = ss a := by
      rw [show ss a = riemannianFiberNormSq (I := I) (M := M) g r p x (V a) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r p x (V a)]
    have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r p x
        (Q.toFun x) (Q.toFun x) = rQ := by
      rw [show rQ = riemannianFiberNormSq (I := I) (M := M) g r p x (Q.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r p x (Q.toSection x)]
      rfl
    rw [hVself, hQself] at hsq
    have hVa_eq : Tensor0SBundle.TensorRSSpace.toModel (V a) =
        Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r p Q x (e a)) := by
      rw [hV_def]
    rw [hVa_eq] at hsq ⊢
    nlinarith [hsq]

  have hframe : ∑ a : Fin n, ss a =
      riemannianFiberNormSq (I := I) (M := M) g r (p + 1) x
        ((covGrad (I := I) (M := M) g r p Q).toSection x) := by
    rw [covGrad_toSection_apply (I := I) (M := M) g r p Q x]
    rw [riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame_rs (I := I) (M := M) g r p x
      (TensorRSNabla.tensorRSCovariantDerivative I M r p (LeviCivita (I := I) g)
        Q.toSection x) e hn_def horth]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hss_def, hV_def]
    rfl
  calc ∑ a : Fin n,
        (extDerivFun (I := I)
          (fun y : M => riemannianFiberNormSq (I := I) (M := M) g r p y (Q.toSection y)) x
          (e a)) ^ 2
      ≤ ∑ a : Fin n, 4 * ss a * rQ := Finset.sum_le_sum (fun a _ => hterm a)
    _ = 4 * (∑ a : Fin n, ss a) * rQ := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = 4 * rQ * riemannianFiberNormSq (I := I) (M := M) g r (p + 1) x
          ((covGrad (I := I) (M := M) g r p Q).toSection x) := by rw [hframe]; ring

set_option maxHeartbeats 1600000 in

omit [BoundarylessManifold I M] in
theorem prependCovGradSlot_fiberNormSq_frame_sum_rs
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (ζ : C^∞⟮I, M; ℝ⟯)
    (S : Integral.L2.SmoothCcTensor g r t) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (t + 1) x
        ((prependCovGradSlot (I := I) (M := M) g r t ζ S).toSection x) =
      (∑ a : Fin (Module.finrank ℝ E),
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
        riemannianFiberNormSq (I := I) (M := M) g r t x (S.toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b

  rw [prependCovGradSlot_toSection_apply (I := I) (M := M) g r t ζ S x]
  rw [riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame_rs (I := I) (M := M) g r t x
    ((extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)) e hn_def horth]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)

  rw [ContinuousLinearMap.smulRight_apply]
  rw [show ((extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x :
        Tensor0SBundle.TensorRSSpace r t I x) =
      (extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x from rfl]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r t x
    ((extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r t x (S.toSection x)]
  rw [Tensor0SBundle.TensorRSSpace.toModel_smul,
    Integral.L2.tensorInnerPointwise_smul_left, Integral.L2.tensorInnerPointwise_smul_right]
  rw [he_def]
  ring

end GeneralValenceRS

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
