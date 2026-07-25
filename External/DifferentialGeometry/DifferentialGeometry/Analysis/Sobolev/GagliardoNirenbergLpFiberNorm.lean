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
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormGeneralValence

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
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

private noncomputable def lpFiberJetLadder
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (u : Integral.L2.SmoothCcTensor g 0 s)
    (Λ₀ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then
    Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
  else if i = k then
    Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun
  else
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)) ^ ((k : ℝ) / i)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))

section SecondOrderInterpCore

private theorem secondCovDeriv_frame_diag_fiberNormSq_sum_le
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (w : Integral.L2.SmoothCcTensor g 0 m) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (m + 1)
            (covGrad (I := I) (M := M) g 0 m w)).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def

  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have hnTan : n = Module.finrank ℝ (TangentSpace I x) := hn_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀

  set T2 : Tensor0SBundle.TensorRSSpace 0 (m + 1 + 1) I x :=
    (covGrad (I := I) (M := M) g 0 (m + 1)
      (covGrad (I := I) (M := M) g 0 m w)).toSection x with hT2_def

  have hreprS : ∀ S : Tensor0SBundle.TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J :=
    fun S => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g m x S e hnTan horth
  have hreprT2 : ∀ S : Tensor0SBundle.TensorRSSpace 0 (m + 1 + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1 + 1) → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 (m + 1 + 1) S n e K J :=
    fun S => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g (m + 1 + 1) x S e hnTan horth

  have hcomp : ∀ (i : Fin n) (J : Fin m → Fin n),
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 m
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) n e K₀ J =
        Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons i (Fin.cons i J)) := by
    intro i J

    have hco : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
        unitZeroSec (I := I) (M := M) x := by
      rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
          Integral.Connection.coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
      exact Integral.Connection.coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀

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

    rw [Integral.Connection.fiberNormSqComponent, Integral.Connection.fiberNormSqComponent,
      hco, htuple]
    rw [he_def]
    exact (Integral.Connection.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
      (I := I) (M := M) g m w
      (X := Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (Y := Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame_smooth (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame_smooth (I := I) g x i) x
      (fun k : Fin m => e (J k))).symm

  have hdiag_term : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) =
        ∑ J : Fin m → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
            (Fin.cons i (Fin.cons i J))) ^ 2 := by
    intro i
    rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq
      (I := I) (M := M) g x m e hreprS _ K₀]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hcomp i J]

  have hfull : riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x T2 =
      ∑ a : Fin n, ∑ b : Fin n, ∑ J : Fin m → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons a (Fin.cons b J))) ^ 2 := by
    rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq
      (I := I) (M := M) g x (m + 1 + 1) e hreprT2 T2 K₀]
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin n))
          (fun pr : Fin n × (Fin (m + 1) → Fin n) =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              (Fin.cons pr.1 pr.2)) ^ 2)
          (fun J'' : Fin (m + 1 + 1) → Fin n =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              J'') ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n))
          (fun pr : Fin n × (Fin m → Fin n) =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              (Fin.cons a (Fin.cons pr.1 pr.2))) ^ 2)
          (fun J' : Fin (m + 1) → Fin n =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              (Fin.cons a J')) ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]

  rw [hfull]
  have hdiag_sum : ∑ i : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) =
      ∑ i : Fin n, ∑ J : Fin m → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons i (Fin.cons i J))) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => hdiag_term i)
  rw [hdiag_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)

  refine Finset.single_le_sum (f := fun b : Fin n =>
      ∑ J : Fin m → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons i (Fin.cons b J))) ^ 2)
    (fun b _ => Finset.sum_nonneg (fun J _ => sq_nonneg _)) (Finset.mem_univ i)

private theorem rawConnLap_innerWith_sqrt_finrank_bound
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (w : Integral.L2.SmoothCcTensor g 0 m) (x : M) :
    |Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        ((rawTensorConnLapSmooth (I := I) g 0 m w).toFun x) (w.toFun x)| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (m + 1)
            (covGrad (I := I) (M := M) g 0 m w)).toSection x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def

  set aw : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) with haw_def
  set cw : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (m + 1)
        (covGrad (I := I) (M := M) g 0 m w)).toSection x) with hcw_def
  have haw_nn : 0 ≤ aw := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x _
  have hcw_nn : 0 ≤ cw := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _

  set D : Fin n → Tensor0SBundle.TensorRSSpace 0 m I x :=
    fun i => Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
      (Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (fun y : M => w.toSection y) x with hD_def

  have htrace : (rawTensorConnLapSmooth (I := I) g 0 m w).toFun x =
      Tensor0SBundle.TensorRSSpace.toModel (∑ i : Fin n, D i) := by
    have h1 : (rawTensorConnLapSmooth (I := I) g 0 m w).toFun x =
        Tensor0SBundle.TensorRSSpace.toModel
          ((rawTensorConnLapSmooth (I := I) g 0 m w).toSection x) := rfl
    rw [h1, Integral.Connection.rawTensorConnLapSmooth_toSection_apply (I := I) (M := M) g 0 m w x,
      Integral.Connection.rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 m
        (fun y : M => w.toSection y) x]

  have hsum_aux : ∀ (s' : Finset (Fin n)),
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Tensor0SBundle.TensorRSSpace.toModel (∑ i ∈ s', D i)) (w.toFun x) =
        ∑ i ∈ s', Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x) := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, Tensor0SBundle.TensorRSSpace.toModel_zero]
        exact Integral.L2.tensorInnerPointwise_zero_left (I := I) (M := M) g 0 m x (w.toFun x)
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, Finset.sum_insert hi₀, Tensor0SBundle.TensorRSSpace.toModel_add,
          Integral.L2.tensorInnerPointwise_add_left, ih]

  have hsum : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        ((rawTensorConnLapSmooth (I := I) g 0 m w).toFun x) (w.toFun x) =
      ∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x) := by
    rw [htrace]
    exact hsum_aux Finset.univ

  set r : Fin n → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g 0 m x (D i) with hr_def
  have hr_nn : ∀ i, 0 ≤ r i := fun i =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x (D i)
  have hCSi : ∀ i, |Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤
      Real.sqrt (r i) * Real.sqrt aw := by
    intro i
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 m x
      (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)
    have hDi_self : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i))
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) = r i := by
      rw [show r i = riemannianFiberNormSq (I := I) (M := M) g 0 m x (D i) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 m x (D i)]
    have hw_self : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (w.toFun x) (w.toFun x) = aw := by
      rw [show aw = riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 m x (w.toSection x)]
      rfl
    rw [hDi_self, hw_self] at hsq
    have habs : |Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤ Real.sqrt (r i * aw) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (hr_nn i)] at habs
    exact habs

  rw [hsum]
  have hstep1 : |∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤
      ∑ i : Fin n, Real.sqrt (r i) * Real.sqrt aw := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun i _ => hCSi i)

  have hdiscrete : (∑ i : Fin n, Real.sqrt (r i)) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, r i := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ)) (fun i => Real.sqrt (r i))
    have hone : ∑ _i : Fin n, (1 : ℝ) ^ 2 = (n : ℝ) := by
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
    have hsqrt_sq : ∑ i : Fin n, Real.sqrt (r i) ^ 2 = ∑ i : Fin n, r i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.sq_sqrt (hr_nn i)]
    have hlhs : (∑ i : Fin n, (1 : ℝ) * Real.sqrt (r i)) = ∑ i : Fin n, Real.sqrt (r i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_mul]
    rw [hlhs, hone, hsqrt_sq] at hcs
    exact hcs

  have hdiag : ∑ i : Fin n, r i ≤ cw :=
    secondCovDeriv_frame_diag_fiberNormSq_sum_le (I := I) (M := M) g m w x

  have hsum_sqrt_nn : 0 ≤ ∑ i : Fin n, Real.sqrt (r i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsum_r_nn : 0 ≤ ∑ i : Fin n, r i := Finset.sum_nonneg (fun i _ => hr_nn i)
  have hsqrt_bound : ∑ i : Fin n, Real.sqrt (r i) ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw := by
    have h1 : ∑ i : Fin n, Real.sqrt (r i) ≤ Real.sqrt ((n : ℝ) * ∑ i : Fin n, r i) := by
      rw [← Real.sqrt_sq hsum_sqrt_nn]
      exact Real.sqrt_le_sqrt hdiscrete
    have h2 : Real.sqrt ((n : ℝ) * ∑ i : Fin n, r i) ≤ Real.sqrt ((n : ℝ) * cw) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdiag hn_nn)
    have h3 : Real.sqrt ((n : ℝ) * cw) = Real.sqrt (n : ℝ) * Real.sqrt cw :=
      Real.sqrt_mul hn_nn cw
    calc ∑ i : Fin n, Real.sqrt (r i)
        ≤ Real.sqrt ((n : ℝ) * ∑ i : Fin n, r i) := h1
      _ ≤ Real.sqrt ((n : ℝ) * cw) := h2
      _ = Real.sqrt (n : ℝ) * Real.sqrt cw := h3
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw := by rw [hn_def]
  calc |∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)|
      ≤ ∑ i : Fin n, Real.sqrt (r i) * Real.sqrt aw := hstep1
    _ = (∑ i : Fin n, Real.sqrt (r i)) * Real.sqrt aw := by rw [← Finset.sum_mul]
    _ ≤ (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw) * Real.sqrt aw := by
        exact mul_le_mul_of_nonneg_right hsqrt_bound (Real.sqrt_nonneg _)
    _ = Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt aw * Real.sqrt cw := by ring

omit [BoundarylessManifold I M] in
private theorem prependCovGradSlot_fiberNormSq_frame_sum
    (g : SmoothRiemannianMetric I M) (t : ℕ) (ζ : C^∞⟮I, M; ℝ⟯)
    (S : Integral.L2.SmoothCcTensor g 0 t) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x
        ((prependCovGradSlot (I := I) (M := M) g 0 t ζ S).toSection x) =
      (∑ a : Fin (Module.finrank ℝ E),
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (S.toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have hnTan : n = Module.finrank ℝ (TangentSpace I x) := hn_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hreprS : ∀ U : Tensor0SBundle.TensorRSSpace 0 t I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 t x U =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 t U n e K J :=
    fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g t x U e hnTan horth
  have hreprSucc : ∀ U : Tensor0SBundle.TensorRSSpace 0 (t + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x U =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (t + 1) → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 (t + 1) U n e K J :=
    fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g (t + 1) x U e hnTan horth

  rw [prependCovGradSlot_toSection_apply (I := I) (M := M) g 0 t ζ S x]
  rw [Integral.Connection.riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame
    (I := I) (M := M) g t x
    ((extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)) e K₀ hreprS hreprSucc]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)

  rw [ContinuousLinearMap.smulRight_apply]

  rw [show ((extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x :
        Tensor0SBundle.TensorRSSpace 0 t I x) =
      (extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x from rfl]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x
    ((extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x (S.toSection x)]
  rw [Tensor0SBundle.TensorRSSpace.toModel_smul,
    Integral.L2.tensorInnerPointwise_smul_left, Integral.L2.tensorInnerPointwise_smul_right]
  rw [he_def]
  ring

omit [CompactSpace M] in
private theorem mfderiv_riemannianFiberNormSq_eq_two_mul_covDeriv_inner
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (Q : Integral.L2.SmoothCcTensor g 0 p) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I)
        (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x v =
      2 * Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
        (Q.toFun x) := by
  classical

  have hfun : (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) =
      fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p y
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y)) := by
    funext y
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 p y (Q.toSection y)]
  rw [hfun]
  rw [show extDerivFun (I := I)
        (fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p y
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))) x v =
      mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p y
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))) x v from rfl]

  rw [Integral.Connection.tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (I := I) (M := M) g 0 p Q.toSection Q.toSection x v]

  have hbridge : Integral.L2.covariantTensorInnerPointwise (I := I) (M := M) (0 + p) g x
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g 0 p Q.toSection x v))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.liftedTensorSection (I := I) (M := M) g 0 p Q.toSection x)) =
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
        (Q.toFun x) := by
    rw [show Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
          (Q.toFun x) =
        Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) from rfl]
    unfold Integral.L2.tensorInnerPointwise
    rw [show Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g 0 p Q.toSection x v) from
      (Integral.Connection.loweredCovDerivAt_eq_lower_tensorCovDerivAt_gen
        (I := I) (M := M) g p Q.toSection x v).symm]
    rw [show Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.liftedTensorSection (I := I) (M := M) g 0 p Q.toSection x) from
      (Integral.Connection.toModel_liftedTensorSection
        (I := I) (M := M) g 0 p Q.toSection x).symm]
  rw [hbridge]

  rw [Integral.L2.tensorInnerPointwise_0s_symm (I := I) (M := M) g x (0 + p)
      (Tensor0SBundle.Tensor0SSpace.toModel
        (Integral.Connection.liftedTensorSection (I := I) (M := M) g 0 p Q.toSection x))
      (Tensor0SBundle.Tensor0SSpace.toModel
        (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g 0 p Q.toSection x v))]
  rw [hbridge]
  ring

private theorem kato_mfderiv_riemannianFiberNormSq_frame_sum_le
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (Q : Integral.L2.SmoothCcTensor g 0 p) (x : M) :
    ∑ a : Fin (Module.finrank ℝ E),
        (extDerivFun (I := I)
          (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g 0 p x (Q.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x
          ((covGrad (I := I) (M := M) g 0 p Q).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have hnTan : n = Module.finrank ℝ (TangentSpace I x) := hn_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  set rQ : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 p x (Q.toSection x) with hrQ_def
  have hrQ_nn : 0 ≤ rQ := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 p x (Q.toSection x)

  set V : Fin n → Tensor0SBundle.TensorRSSpace 0 p I x :=
    fun a => tensorCovDerivAt (I := I) (M := M) g 0 p Q x (e a) with hV_def
  set s : Fin n → ℝ := fun a => riemannianFiberNormSq (I := I) (M := M) g 0 p x (V a) with hs_def
  have hs_nn : ∀ a, 0 ≤ s a := fun a =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 p x (V a)

  have hterm : ∀ a : Fin n,
      (extDerivFun (I := I)
        (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x (e a)) ^ 2 ≤
        4 * s a * rQ := by
    intro a
    rw [mfderiv_riemannianFiberNormSq_eq_two_mul_covDeriv_inner (I := I) (M := M) g p Q x (e a)]
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 p x
      (Tensor0SBundle.TensorRSSpace.toModel (V a)) (Q.toFun x)
    have hVself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Tensor0SBundle.TensorRSSpace.toModel (V a))
        (Tensor0SBundle.TensorRSSpace.toModel (V a)) = s a := by
      rw [show s a = riemannianFiberNormSq (I := I) (M := M) g 0 p x (V a) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 p x (V a)]
    have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Q.toFun x) (Q.toFun x) = rQ := by
      rw [show rQ = riemannianFiberNormSq (I := I) (M := M) g 0 p x (Q.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 p x (Q.toSection x)]
      rfl
    rw [hVself, hQself] at hsq
    have hVa_eq : Tensor0SBundle.TensorRSSpace.toModel (V a) =
        Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 p Q x (e a)) := by
      rw [hV_def]
    rw [hVa_eq] at hsq ⊢
    nlinarith [hsq]

  have hframe : ∑ a : Fin n, s a =
      riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x
        ((covGrad (I := I) (M := M) g 0 p Q).toSection x) := by
    rw [covGrad_toSection_apply (I := I) (M := M) g 0 p Q x]
    have hreprS : ∀ U : Tensor0SBundle.TensorRSSpace 0 p I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 p x U =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin p → Fin n,
            Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 p U n e K J :=
      fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
        (I := I) (M := M) g p x U e hnTan horth
    have hreprSucc : ∀ U : Tensor0SBundle.TensorRSSpace 0 (p + 1) I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x U =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin (p + 1) → Fin n,
            Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 (p + 1) U n e K J :=
      fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
        (I := I) (M := M) g (p + 1) x U e hnTan horth
    rw [Integral.Connection.riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame
      (I := I) (M := M) g p x
      (TensorRSNabla.tensorRSCovariantDerivative I M 0 p (LeviCivita (I := I) g)
        Q.toSection x) e K₀ hreprS hreprSucc]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hs_def, hV_def]
    rfl

  calc ∑ a : Fin n,
        (extDerivFun (I := I)
          (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x
          (e a)) ^ 2
      ≤ ∑ a : Fin n, 4 * s a * rQ := Finset.sum_le_sum (fun a _ => hterm a)
    _ = 4 * (∑ a : Fin n, s a) * rQ := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = 4 * rQ * riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x
          ((covGrad (I := I) (M := M) g 0 p Q).toSection x) := by rw [hframe]; ring

set_option maxHeartbeats 1600000 in

private theorem covDerivCrossLeft_weight_bound
    (g : SmoothRiemannianMetric I M) (k m : ℕ) (_hk : 1 ≤ k)
    (w : Integral.L2.SmoothCcTensor g 0 m) (A : ℝ) (_hA : 0 ≤ A)
    (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2)
    (ζ : C^∞⟮I, M; ℝ⟯)
    (hζ : (ζ : M → ℝ) = fun y => (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y
        ((covGrad (I := I) (M := M) g 0 m w).toSection y)) ^ (k - 1))
    (x : M) :
    |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A *
        (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
          ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) - 1) *
        (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (m + 1)
            (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def

  set Q : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hQ_def
  set bfun : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (Q.toSection y) with hbfun_def
  set b : ℝ := bfun x with hb_def
  set c : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (m + 1) Q).toSection x) with hc_def
  have hb_nn : 0 ≤ b := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)
  have hc_nn : 0 ≤ c := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hAsq : riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2 := _hsup x

  set P : Integral.L2.SmoothCcTensor g 0 (m + 1) :=
    prependCovGradSlot (I := I) (M := M) g 0 m ζ w with hP_def
  have hcross_eq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x =
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) :=
    tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m ζ w w x

  set rP : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) with hrP_def
  have hrP_nn : 0 ≤ rP := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hCS2 : |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      Real.sqrt b * Real.sqrt rP := by
    rw [hcross_eq]
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 (m + 1) x
      (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
      (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
    have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) = b := by
      rw [show b = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (Q.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)]
    have hPself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) = rP := by
      rw [show rP = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (P.toSection x)]
    rw [hQself, hPself] at hsq
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hb_nn]
    exact Real.sqrt_le_sqrt hsq

  have hrP_eq : rP = (∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
        riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) :=
    prependCovGradSlot_fiberNormSq_frame_sum (I := I) (M := M) g m ζ w x

  have hbfun_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) bfun x := by
    have hb_eq_scalar : bfun = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
        Q.toSection Q.toSection := by
      funext y
      simp only [hbfun_def, Integral.Connection.tensorInnerScalar_apply]
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
        (Q.toSection y)]
    rw [hb_eq_scalar]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
      Q.toSection Q.toSection).mdifferentiableAt (by norm_num)
  have hchain : ∀ v : TangentSpace I x,
      extDerivFun (I := I) (ζ : M → ℝ) x v =
        ((k : ℝ) - 1) * b ^ (k - 2) * extDerivFun (I := I) bfun x v := by
    intro v
    have hinner : HasMFDerivAt I 𝓘(ℝ, ℝ) bfun x (mfderiv I 𝓘(ℝ, ℝ) bfun x) :=
      hbfun_mdiff.hasMFDerivAt
    have houter : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t ^ (k - 1)) (bfun x)
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)))) :=
      ((hasDerivAt_pow (k - 1) (bfun x)).hasFDerivAt).hasMFDerivAt
    have hcomp : HasMFDerivAt I 𝓘(ℝ, ℝ) ((fun t : ℝ => t ^ (k - 1)) ∘ bfun) x
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
            (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1))).comp
          (mfderiv I 𝓘(ℝ, ℝ) bfun x)) :=
      HasMFDerivAt.comp x houter hinner
    have hζeq : (ζ : M → ℝ) = (fun t : ℝ => t ^ (k - 1)) ∘ bfun := by
      rw [hζ]; rfl
    have hext : extDerivFun (I := I) (ζ : M → ℝ) x v = mfderiv I 𝓘(ℝ, ℝ) (ζ : M → ℝ) x v := rfl
    have hCLM : (mfderiv I 𝓘(ℝ, ℝ) ((fun t : ℝ => t ^ (k - 1)) ∘ bfun) x) v =
        (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) * extDerivFun (I := I) bfun x v := by
      rw [hcomp.mfderiv]
      change extDerivFun (I := I) bfun x v * (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) =
        (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) * extDerivFun (I := I) bfun x v
      ring
    have hmfζ : extDerivFun (I := I) (ζ : M → ℝ) x v =
        (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) * extDerivFun (I := I) bfun x v := by
      rw [hext, hζeq]
      exact hCLM
    rw [hmfζ]
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub _hk, Nat.cast_one]
    have hexp : k - 1 - 1 = k - 2 := by omega
    rw [show (bfun x) = b from rfl, hkcast, hexp]

  have hkato : ∑ a : Fin n,
      (extDerivFun (I := I) bfun x (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 ≤
        4 * b * c :=
    kato_mfderiv_riemannianFiberNormSq_frame_sum_le (I := I) (M := M) g (m + 1) Q x

  have hdζsum : (∑ a : Fin n,
      (extDerivFun (I := I) (ζ : M → ℝ) x
        (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) ≤
        ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) := by
    have hrw : (∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) =
        ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 *
          ∑ a : Fin n,
            (extDerivFun (I := I) bfun x
              (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hchain (Integral.Connection.smoothOrthoFrame (I := I) g x a x)]
      ring
    rw [hrw]
    have hcoeff_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hkato hcoeff_nn

  have hrP_bound : rP ≤ ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) * A ^ 2 := by
    rw [hrP_eq]
    have hrfnsw_le : riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2 := hAsq
    have hrfnsw_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x (w.toSection x)
    have hsum_nn : (0 : ℝ) ≤ ∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 :=
      Finset.sum_nonneg (fun a _ => sq_nonneg _)
    have hbound_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) := by
      have : (0 : ℝ) ≤ 4 * b * c := by positivity
      positivity
    calc (∑ a : Fin n,
            (extDerivFun (I := I) (ζ : M → ℝ) x
              (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)
        ≤ (((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c)) *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) :=
          mul_le_mul_of_nonneg_right hdζsum hrfnsw_nn
      _ ≤ (((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c)) * A ^ 2 :=
          mul_le_mul_of_nonneg_left hrfnsw_le hbound_nn
      _ = ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) * A ^ 2 := by ring

  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk
    linarith

  have hbnat_rpow : b ^ (k - 1) = b ^ ((k : ℝ) - 1) := by
    rw [← Real.rpow_natCast b (k - 1)]
    congr 1
    rw [Nat.cast_sub _hk, Nat.cast_one]

  change |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ)
  have hRHS_nn : (0 : ℝ) ≤ 2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ) := by
    have hbrpow : (0 : ℝ) ≤ b ^ ((k : ℝ) - 1) := Real.rpow_nonneg hb_nn _
    have hcrpow : (0 : ℝ) ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc_nn _
    positivity

  refine le_trans hCS2 ?_
  rw [← Real.sqrt_mul hb_nn rP,
    show 2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ) =
      Real.sqrt ((2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ)) ^ 2) from
    (Real.sqrt_sq hRHS_nn).symm]
  refine Real.sqrt_le_sqrt ?_

  have hcrpow_sq : (c ^ (1 / 2 : ℝ)) ^ 2 = c := by
    rw [← Real.rpow_natCast (c ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hc_nn]
    norm_num
  have htarget_eq : (2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ)) ^ 2 =
      ((k : ℝ) - 1) ^ 2 * (4 * A ^ 2) * (b ^ (k - 1) * b ^ (k - 1)) * c := by
    rw [hbnat_rpow]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hcrpow_sq]
    ring
  rw [htarget_eq]

  have hb_core : ((k : ℝ) - 1) ^ 2 * (b * (b ^ (k - 2)) ^ 2 * b) =
      ((k : ℝ) - 1) ^ 2 * (b ^ (k - 1) * b ^ (k - 1)) := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1' : k = 1 := by omega
      subst hk1'
      norm_num
    · have hbk1 : b ^ (k - 1) = b ^ (k - 2) * b := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hbk1, sq]
      ring
  calc b * rP
      ≤ b * (((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) * A ^ 2) :=
        mul_le_mul_of_nonneg_left hrP_bound hb_nn
    _ = (4 * A ^ 2) * c * (((k : ℝ) - 1) ^ 2 * (b * (b ^ (k - 2)) ^ 2 * b)) := by ring
    _ = (4 * A ^ 2) * c * (((k : ℝ) - 1) ^ 2 * (b ^ (k - 1) * b ^ (k - 1))) := by rw [hb_core]
    _ = ((k : ℝ) - 1) ^ 2 * (4 * A ^ 2) * (b ^ (k - 1) * b ^ (k - 1)) * c := by ring

set_option maxHeartbeats 2000000 in

private theorem weightedCovIBP_lpFiberJet_fin_regIneq
    (g : SmoothRiemannianMetric I M) (k m i : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g 0 m) (ε : ℝ) (_hε : 0 < ε) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) *
          ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + ε) ^ ((k : ℝ) / (i + 1) - 1)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + ε) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  set n : ℕ := Module.finrank ℝ E with hn_def

  set p : ℝ := (k : ℝ) / (i + 1) with hp_def
  set pm1 : ℝ := p - 1 with hpm1_def
  have hi1R : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hp1 : 1 < p := by
    rw [hp_def, lt_div_iff₀ hi1R, one_mul]; exact_mod_cast _hik
  have hpm1_pos : 0 < pm1 := by rw [hpm1_def]; linarith
  have hpm1_nn : 0 ≤ pm1 := le_of_lt hpm1_pos

  set gw : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hgw
  set ggw : Integral.L2.SmoothCcTensor g 0 (m + 1 + 1) :=
    covGrad (I := I) (M := M) g 0 (m + 1) gw with hggw
  set Lw : Integral.L2.SmoothCcTensor g 0 m :=
    rawTensorConnLapSmooth (I := I) g 0 m w with hLw

  set a : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g 0 m y (w.toSection y) with ha
  set b : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
    with hb
  set c : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y) with hc
  have ha_nonneg : ∀ y, 0 ≤ a y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m y (w.toSection y)
  have hb_nonneg : ∀ y, 0 ≤ b y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
  have hc_nonneg : ∀ y, 0 ≤ c y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y)

  have hb_eq_scalar : b = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection := by
    funext y
    simp only [hb, Integral.Connection.tensorInnerScalar_apply]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
      (gw.toSection y)]
  have hb_smooth : ContMDiff I 𝓘(ℝ) ∞ b := by
    rw [hb_eq_scalar]
    exact Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection

  set bε : M → ℝ := fun y => b y + ε with hbε
  have hbε_smooth : ContMDiff I 𝓘(ℝ) ∞ bε := hb_smooth.add contMDiff_const
  have hbε_pos : ∀ y, 0 < bε y := fun y => by rw [hbε]; linarith [hb_nonneg y]
  have hbε_ne : ∀ y, bε y ≠ 0 := fun y => ne_of_gt (hbε_pos y)
  have hbε_nonneg : ∀ y, 0 ≤ bε y := fun y => le_of_lt (hbε_pos y)

  have hζ_smooth : ContMDiff I 𝓘(ℝ) ∞ (fun y => bε y ^ pm1) := by
    intro y
    exact (Real.contDiffAt_rpow_const_of_ne (p := pm1) (hbε_ne y)).comp_contMDiffAt
      hbε_smooth.contMDiffAt
  set ζ : C^∞⟮I, M; ℝ⟯ := ⟨fun y => bε y ^ pm1, hζ_smooth⟩ with hζ
  have hζ_apply : (ζ : M → ℝ) = fun y => bε y ^ pm1 := rfl
  have hζ_nonneg : ∀ y, 0 ≤ (ζ : M → ℝ) y := by
    intro y; rw [hζ_apply]; exact Real.rpow_nonneg (hbε_nonneg y) _

  set v : Integral.L2.SmoothCcTensor g 0 m :=
    scalarSmul (I := I) (M := M) g 0 m ζ w with hv

  have hdiag : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w w x = b x := by
    intro x
    rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m w w x,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        ((covGrad (I := I) (M := M) g 0 m w).toSection x)]

  have hsplit : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x =
      (ζ : M → ℝ) x * b x + tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x := by
    intro x
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def, ← hdiag,
      tensorCovDerivPointwiseInner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv, tensorCovDerivAt_scalarSmul (I := I) (M := M) g 0 m ζ w x
      ((Integral.Measure.chartModelBasis E) j)]
    have hwx : Tensor0SBundle.TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
    simp only [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_smul,
      hwx, Integral.L2.tensorInnerPointwise_add_right, Integral.L2.tensorInnerPointwise_smul_right]
    ring

  have hpull : ∀ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) =
      (ζ : M → ℝ) x * Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (w.toFun x) := by
    intro x
    rw [hv, scalarSmul_toFun_apply, Integral.L2.tensorInnerPointwise_smul_right]

  have hcentral : ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ =
      - ∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Lw.toFun x) (v.toFun x) ∂μ := by
    have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
      (I := I) (M := M) g m w v
    have hdir := tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 m w v
    rw [hdir] at hgreen
    rw [hgreen, Integral.L2.tensorL2Inner, hLw]

  have hb_cont : Continuous b := hb_smooth.continuous
  have ha_cont : Continuous a := continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 m w
  have hc_cont : Continuous c := continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1 + 1) ggw
  have hbε_cont : Continuous bε := hbε_smooth.continuous
  have hζ_cont : Continuous (ζ : M → ℝ) := by
    rw [hζ_apply]; exact hbε_cont.rpow_const (fun y => Or.inl (hbε_ne y))
  have htcdpi_cont : Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g 0 m w v
  have hζb_cont : Continuous (fun x => (ζ : M → ℝ) x * b x) := hζ_cont.mul hb_cont
  have hcrossL_cont : Continuous (tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w) := by
    have heq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w =
        fun x => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x -
          (ζ : M → ℝ) x * b x := by
      funext x; rw [hsplit x]; ring
    rw [heq]; exact htcdpi_cont.sub hζb_cont

  set dw : M → ℝ := fun x => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
    (Lw.toFun x) (w.toFun x) with hdw
  have hdw_eq : dw = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 m
      Lw.toSection w.toSection := by
    funext x
    simp only [hdw, Integral.Connection.tensorInnerScalar_apply]
    rfl
  have hdw_cont : Continuous dw := by
    rw [hdw_eq]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 m
      Lw.toSection w.toSection).continuous
  have hζdw_cont : Continuous (fun x => (ζ : M → ℝ) x * dw x) := hζ_cont.mul hdw_cont

  have hint : ∀ f : M → ℝ, Continuous f → MeasureTheory.Integrable f μ := by
    intro f hf
    exact (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable
      (le_refl 1)

  set F : M → ℝ := fun x => (a x) ^ (1 / 2 : ℝ) * (ζ : M → ℝ) x * (c x) ^ (1 / 2 : ℝ) with hF
  have hF_nonneg : ∀ x, 0 ≤ F x := fun x => by
    rw [hF]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (ha_nonneg x) _) (hζ_nonneg x))
      (Real.rpow_nonneg (hc_nonneg x) _)
  have hF_cont : Continuous F := by
    rw [hF]
    exact ((ha_cont.rpow_const (fun x => Or.inr (by norm_num))).mul hζ_cont).mul
      (hc_cont.rpow_const (fun x => Or.inr (by norm_num)))

  have hLHS_eq : (∫ x, b x * (b x + ε) ^ pm1 ∂μ) = ∫ x, (ζ : M → ℝ) x * b x ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hζ_apply, hbε]; ring

  have hLHS_split : (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ) =
      (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
        ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ := by
    rw [← MeasureTheory.integral_add (hint _ hζb_cont) (hint _ hcrossL_cont)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hRHS_pull : (∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) ∂μ) = ∫ x, (ζ : M → ℝ) x * dw x ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpull)
  have hmaster : (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) =
      - ∫ x, (ζ : M → ℝ) x * dw x ∂μ := by
    rw [← hLHS_split, ← hRHS_pull]; exact hcentral

  have hcrossB : ∀ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * pm1 * F x := by
    intro x

    set Q : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hQ_def
    set bfun : M → ℝ := fun y =>
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (Q.toSection y) with hbfun_def
    set bv : ℝ := bfun x with hbv_def
    set cv : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (m + 1) Q).toSection x) with hcv_def
    set av : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) with hav_def
    have hbv_nn : 0 ≤ bv := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)
    have hcv_nn : 0 ≤ cv := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
    have hav_nn : 0 ≤ av := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x (w.toSection x)
    have hbεx_pos : 0 < bv + ε := by linarith

    have hFx : F x = av ^ (1 / 2 : ℝ) * (bv + ε) ^ pm1 * cv ^ (1 / 2 : ℝ) := rfl

    set P : Integral.L2.SmoothCcTensor g 0 (m + 1) :=
      prependCovGradSlot (I := I) (M := M) g 0 m ζ w with hP_def
    have hcross_eq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x =
        Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) :=
      tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m ζ w w x
    set rP : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) with hrP_def
    have hrP_nn : 0 ≤ rP := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
    have hCS2 : |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
        Real.sqrt bv * Real.sqrt rP := by
      rw [hcross_eq]
      have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
      have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) = bv := by
        rw [show bv = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (Q.toSection x) from rfl,
          riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)]
      have hPself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) = rP := by
        rw [show rP = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) from rfl,
          riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (P.toSection x)]
      rw [hQself, hPself] at hsq
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hbv_nn]
      exact Real.sqrt_le_sqrt hsq

    have hrP_eq : rP = (∑ a : Fin n,
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) * av :=
      prependCovGradSlot_fiberNormSq_frame_sum (I := I) (M := M) g m ζ w x

    have hbfun_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) bfun x := by
      have hb_eq_scalar : bfun = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
          Q.toSection Q.toSection := by
        funext y
        simp only [hbfun_def, Integral.Connection.tensorInnerScalar_apply]
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
          (Q.toSection y)]
      rw [hb_eq_scalar]
      exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
        Q.toSection Q.toSection).mdifferentiableAt (by norm_num)

    have hbεbfun_ne : bfun x + ε ≠ 0 := ne_of_gt hbεx_pos
    have hchain : ∀ v : TangentSpace I x,
        extDerivFun (I := I) (ζ : M → ℝ) x v =
          (pm1 * (bv + ε) ^ (pm1 - 1)) * extDerivFun (I := I) bfun x v := by
      intro v

      have hshift : HasDerivAt (fun t : ℝ => t + ε) 1 (bfun x) :=
        (hasDerivAt_id' (bfun x)).add_const ε
      have houterReal : HasDerivAt (fun t : ℝ => (t + ε) ^ pm1)
          (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) (bfun x) :=
        hshift.rpow_const (Or.inl hbεbfun_ne)
      have houter : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t + ε) ^ pm1) (bfun x)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
            (1 * pm1 * (bfun x + ε) ^ (pm1 - 1))) :=
        houterReal.hasFDerivAt.hasMFDerivAt
      have hcomp : HasMFDerivAt I 𝓘(ℝ, ℝ) ((fun t : ℝ => (t + ε) ^ pm1) ∘ bfun) x
          ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
              (1 * pm1 * (bfun x + ε) ^ (pm1 - 1))).comp (mfderiv I 𝓘(ℝ, ℝ) bfun x)) :=
        HasMFDerivAt.comp x houter hbfun_mdiff.hasMFDerivAt
      have hζeq : (ζ : M → ℝ) = (fun t : ℝ => (t + ε) ^ pm1) ∘ bfun := rfl
      have hext : extDerivFun (I := I) (ζ : M → ℝ) x v = mfderiv I 𝓘(ℝ, ℝ) (ζ : M → ℝ) x v := rfl
      have hCLM : (mfderiv I 𝓘(ℝ, ℝ) ((fun t : ℝ => (t + ε) ^ pm1) ∘ bfun) x) v =
          (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) * extDerivFun (I := I) bfun x v := by
        rw [hcomp.mfderiv]
        change extDerivFun (I := I) bfun x v * (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) =
          (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) * extDerivFun (I := I) bfun x v
        ring
      rw [hext, hζeq, hCLM, one_mul, hbv_def]

    have hkato : ∑ a : Fin n,
        (extDerivFun (I := I) bfun x (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 ≤
          4 * bv * cv :=
      kato_mfderiv_riemannianFiberNormSq_frame_sum_le (I := I) (M := M) g (m + 1) Q x

    have hdζsum : (∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) ≤
          pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) := by
      have hrw : (∑ a : Fin n,
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) =
          (pm1 * (bv + ε) ^ (pm1 - 1)) ^ 2 *
            ∑ a : Fin n,
              (extDerivFun (I := I) bfun x
                (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hchain (Integral.Connection.smoothOrthoFrame (I := I) g x a x), mul_pow]
      rw [hrw, mul_pow]
      exact mul_le_mul_of_nonneg_left hkato (by positivity)
    have hrP_bound : rP ≤ pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) * av := by
      rw [hrP_eq]
      calc (∑ a : Fin n,
              (extDerivFun (I := I) (ζ : M → ℝ) x
                (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) * av
          ≤ (pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv)) * av :=
            mul_le_mul_of_nonneg_right hdζsum hav_nn
        _ = pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) * av := by ring

    have hRHS_nn : (0 : ℝ) ≤ 2 * pm1 * F x := by
      have := hF_nonneg x; positivity
    refine le_trans hCS2 ?_
    rw [← Real.sqrt_mul hbv_nn rP,
      show 2 * pm1 * F x = Real.sqrt ((2 * pm1 * F x) ^ 2) from (Real.sqrt_sq hRHS_nn).symm]
    refine Real.sqrt_le_sqrt ?_
    have htarget_eq : (2 * pm1 * F x) ^ 2 =
        pm1 ^ 2 * (4 * av * cv) * ((bv + ε) ^ pm1) ^ 2 := by
      have hsa : (av ^ (1 / 2 : ℝ)) ^ 2 = av := by
        rw [← Real.rpow_natCast (av ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hav_nn]; norm_num
      have hsc : (cv ^ (1 / 2 : ℝ)) ^ 2 = cv := by
        rw [← Real.rpow_natCast (cv ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hcv_nn]; norm_num
      rw [hFx]
      have hexpand : (2 * pm1 * (av ^ (1 / 2 : ℝ) * (bv + ε) ^ pm1 * cv ^ (1 / 2 : ℝ))) ^ 2 =
          (2 * pm1) ^ 2 * (av ^ (1 / 2 : ℝ)) ^ 2 * ((bv + ε) ^ pm1) ^ 2 *
            (cv ^ (1 / 2 : ℝ)) ^ 2 := by ring
      rw [hexpand, hsa, hsc]; ring
    rw [htarget_eq]
    have hp2_nn : (0 : ℝ) ≤ (bv + ε) ^ (pm1 - 1) := Real.rpow_nonneg hbεx_pos.le _
    have hfac1 : bv * (bv + ε) ^ (pm1 - 1) ≤ (bv + ε) ^ pm1 := by
      have habsorb : (bv + ε) ^ pm1 = (bv + ε) * (bv + ε) ^ (pm1 - 1) := by
        rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hbεx_pos) (pm1 - 1)]
        congr 1; ring
      rw [habsorb]
      exact mul_le_mul_of_nonneg_right (by linarith) hp2_nn
    have hfac0_nn : (0 : ℝ) ≤ bv * (bv + ε) ^ (pm1 - 1) := mul_nonneg hbv_nn hp2_nn
    calc bv * rP
        ≤ bv * (pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) * av) :=
          mul_le_mul_of_nonneg_left hrP_bound hbv_nn
      _ = pm1 ^ 2 * (4 * av * cv) * (bv * (bv + ε) ^ (pm1 - 1)) ^ 2 := by ring
      _ ≤ pm1 ^ 2 * (4 * av * cv) * ((bv + ε) ^ pm1) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hfac0_nn hfac1 2

  have hA_bound : ∀ x, (ζ : M → ℝ) x * |dw x| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * F x := by
    intro x
    have hcA : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (a x) * Real.sqrt (c x) :=
      rawConnLap_innerWith_sqrt_finrank_bound (I := I) (M := M) g m w x
    have hζF : (ζ : M → ℝ) x * (Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (a x) * Real.sqrt (c x)) = Real.sqrt (Module.finrank ℝ E : ℝ) * F x := by
      rw [hF, Real.sqrt_eq_rpow (a x), Real.sqrt_eq_rpow (c x)]; ring
    calc (ζ : M → ℝ) x * |dw x|
        ≤ (ζ : M → ℝ) x * (Real.sqrt (Module.finrank ℝ E : ℝ) *
            Real.sqrt (a x) * Real.sqrt (c x)) :=
          mul_le_mul_of_nonneg_left hcA (hζ_nonneg x)
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * F x := hζF

  have hintF : MeasureTheory.Integrable F μ := hint _ hF_cont
  have hcrossL_int_bound_neg :
      -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) ≤
        2 * pm1 * ∫ x, F x ∂μ := by
    calc -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ |∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ∂μ :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, 2 * pm1 * F x ∂μ :=
          MeasureTheory.integral_mono (hint _ hcrossL_cont.abs)
            ((hintF.const_mul _)) hcrossB
      _ = 2 * pm1 * ∫ x, F x ∂μ := MeasureTheory.integral_const_mul _ _
  have hLap_int_bound :
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) ≤
        Real.sqrt (Module.finrank ℝ E : ℝ) * ∫ x, F x ∂μ := by
    calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ)
        ≤ |∫ x, (ζ : M → ℝ) x * dw x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |(ζ : M → ℝ) x * dw x| ∂μ := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, Real.sqrt (Module.finrank ℝ E : ℝ) * F x ∂μ := by
          refine MeasureTheory.integral_mono (hint _ hζdw_cont.abs) ((hintF.const_mul _))
            (fun x => ?_)
          rw [abs_mul, abs_of_nonneg (hζ_nonneg x)]
          exact hA_bound x
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * ∫ x, F x ∂μ :=
          MeasureTheory.integral_const_mul _ _

  have hζb_eq : (∫ x, (ζ : M → ℝ) x * b x ∂μ) =
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) := by
    have := hmaster; linarith [this]

  have hassembled : (∫ x, (ζ : M → ℝ) x * b x ∂μ) ≤
      (2 * pm1 + Real.sqrt (Module.finrank ℝ E : ℝ)) * ∫ x, F x ∂μ := by
    rw [hζb_eq]
    calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
            (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * (∫ x, F x ∂μ) +
            2 * pm1 * (∫ x, F x ∂μ) := by
          have h1 := hLap_int_bound
          have h2 := hcrossL_int_bound_neg
          linarith [h1, h2]
      _ = (2 * pm1 + Real.sqrt (Module.finrank ℝ E : ℝ)) * (∫ x, F x ∂μ) := by ring

  change (∫ x, b x * (b x + ε) ^ pm1 ∂μ) ≤
      (2 * pm1 + Real.sqrt (Module.finrank ℝ E : ℝ)) * ∫ x, F x ∂μ
  rw [hLHS_eq]
  exact hassembled

set_option maxHeartbeats 1200000 in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem weightedCovIBP_lpFiberJet_fin_regLimit
    (g : SmoothRiemannianMetric I M) (k m i : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g 0 m) :
    Filter.Tendsto
        (fun n : ℕ => ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))
        Filter.atTop
        (𝓝 (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))) ∧
      Filter.Tendsto
        (fun n : ℕ => ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x))
              ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))
        Filter.atTop
        (𝓝 (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  set p : ℝ := (k : ℝ) / (i + 1) with hp_def
  have hi1R : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hp1 : 1 < p := by
    rw [hp_def, lt_div_iff₀ hi1R, one_mul]; exact_mod_cast _hik
  have hp0 : 0 < p := lt_trans one_pos hp1
  have hpm1_pos : (0 : ℝ) < p - 1 := by linarith
  have hpm1_nn : (0 : ℝ) ≤ p - 1 := le_of_lt hpm1_pos

  set a : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) with ha
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
    ((covGrad (I := I) (M := M) g 0 m w).toSection x) with hb
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)).toSection x)
    with hc
  have ha0 : ∀ x, 0 ≤ a x := fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x _
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hac : Continuous a := continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 m w
  have hbc : Continuous b :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)
  have hcc : Continuous c :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1 + 1)
      (covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w))

  have hε_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hε_le_one : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hε_tendsto : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat

  have hrpow_lim : ∀ x : M, Filter.Tendsto
      (fun n : ℕ => (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1)) Filter.atTop (𝓝 ((b x) ^ (p - 1))) := by
    intro x
    have hbase : Filter.Tendsto (fun n : ℕ => b x + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (b x)) := by
      have := hε_tendsto
      simpa using (tendsto_const_nhds.add this)
    exact hbase.rpow_const (Or.inr hpm1_nn)

  have hbεn_base_nn : ∀ (n : ℕ) (x : M), 0 ≤ b x + 1 / ((n : ℝ) + 1) := fun n x => by
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith [hb0 x]
  have hdom_rpow : ∀ (n : ℕ) (x : M),
      (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1) ≤ (b x + 1) ^ (p - 1) := by
    intro n x
    apply Real.rpow_le_rpow (hbεn_base_nn n x) _ hpm1_nn
    linarith [hε_le_one n]
  have hbε1_nn : ∀ x : M, 0 ≤ (b x + 1) ^ (p - 1) := fun x =>
    Real.rpow_nonneg (by linarith [hb0 x]) _
  have hbεn_nn : ∀ (n : ℕ) (x : M), 0 ≤ (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1) := fun n x =>
    Real.rpow_nonneg (hbεn_base_nn n x) _

  have hint : ∀ f : M → ℝ, Continuous f → MeasureTheory.Integrable f μ := by
    intro f hf
    exact (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable
      (le_refl 1)
  have hbε1_cont : Continuous (fun x => (b x + 1) ^ (p - 1)) :=
    (hbc.add continuous_const).rpow_const (fun x => Or.inr hpm1_nn)
  have ha12_cont : Continuous (fun x => (a x) ^ (1 / 2 : ℝ)) :=
    hac.rpow_const (fun x => Or.inr (by norm_num))
  have hc12_cont : Continuous (fun x => (c x) ^ (1 / 2 : ℝ)) :=
    hcc.rpow_const (fun x => Or.inr (by norm_num))
  have ha12_nn : ∀ x, 0 ≤ (a x) ^ (1 / 2 : ℝ) := fun x => Real.rpow_nonneg (ha0 x) _
  have hc12_nn : ∀ x, 0 ≤ (c x) ^ (1 / 2 : ℝ) := fun x => Real.rpow_nonneg (hc0 x) _

  have hbp : (∫ x, b x * (b x) ^ (p - 1) ∂μ) = ∫ x, (b x) ^ p ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hadd := Real.rpow_one_add' (hb0 x) (show (1 : ℝ) + (p - 1) ≠ 0 by linarith)
    rw [show (1 : ℝ) + (p - 1) = p from by ring] at hadd
    exact hadd.symm
  refine ⟨?_, ?_⟩
  · have hconv : Filter.Tendsto
        (fun n : ℕ => ∫ x, b x * (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1) ∂μ) Filter.atTop
        (𝓝 (∫ x, b x * (b x) ^ (p - 1) ∂μ)) :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun x => b x * (b x + 1) ^ (p - 1))
        (fun n => (hbc.mul ((hbc.add continuous_const).rpow_const
          (fun x => Or.inr hpm1_nn))).aestronglyMeasurable)
        (hint _ (hbc.mul hbε1_cont))
        (fun n => Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb0 x) (hbεn_nn n x))]
          exact mul_le_mul_of_nonneg_left (hdom_rpow n x) (hb0 x)))
        (Filter.Eventually.of_forall (fun x => tendsto_const_nhds.mul (hrpow_lim x)))
    rw [hbp] at hconv
    exact hconv
  · exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun x => (a x) ^ (1 / 2 : ℝ) * (b x + 1) ^ (p - 1) * (c x) ^ (1 / 2 : ℝ))
      (fun n => ((ha12_cont.mul ((hbc.add continuous_const).rpow_const
        (fun x => Or.inr hpm1_nn))).mul hc12_cont).aestronglyMeasurable)
      (hint _ ((ha12_cont.mul hbε1_cont).mul hc12_cont))
      (fun n => Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg (ha12_nn x) (hbεn_nn n x)) (hc12_nn x))]
        apply mul_le_mul_of_nonneg_right _ (hc12_nn x)
        exact mul_le_mul_of_nonneg_left (hdom_rpow n x) (ha12_nn x)))
      (Filter.Eventually.of_forall (fun x =>
        (tendsto_const_nhds.mul (hrpow_lim x)).mul tendsto_const_nhds))

private theorem weightedCovIBP_lpFiberJet_fin
    (g : SmoothRiemannianMetric I M) (k m i : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g 0 m) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by

  set D' : ℝ := 2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD'
  obtain ⟨hLlim, hRlim⟩ :=
    weightedCovIBP_lpFiberJet_fin_regLimit (I := I) (M := M) g k m i _hk _hi _hik w

  have hreg : ∀ n : ℕ, (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
        D' * ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
    intro n
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact weightedCovIBP_lpFiberJet_fin_regIneq (I := I) (M := M) g k m i _hk _hi _hik w
      (1 / ((n : ℝ) + 1)) hεpos

  exact le_of_tendsto_of_tendsto' hLlim (hRlim.const_mul D') hreg

private theorem weightedCovIBP_lpFiberJet_sup
    (g : SmoothRiemannianMetric I M) (k m : ℕ) (_hk : 1 ≤ k)
    (w : Integral.L2.SmoothCcTensor g 0 m) (A : ℝ) (_hA : 0 ≤ A)
    (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / 1)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ

  set gw : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hgw
  set ggw : Integral.L2.SmoothCcTensor g 0 (m + 1 + 1) :=
    covGrad (I := I) (M := M) g 0 (m + 1) gw with hggw
  set Lw : Integral.L2.SmoothCcTensor g 0 m :=
    rawTensorConnLapSmooth (I := I) g 0 m w with hLw

  set b : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
    with hb
  set c : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y) with hc
  have hb_nonneg : ∀ y, 0 ≤ b y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
  have hc_nonneg : ∀ y, 0 ≤ c y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y)

  have hb_eq_scalar : b = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection := by
    funext y
    simp only [hb, Integral.Connection.tensorInnerScalar_apply]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
      (gw.toSection y)]
  have hb_smooth : ContMDiff I 𝓘(ℝ) ∞ b := by
    rw [hb_eq_scalar]
    exact Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection

  set ζ : C^∞⟮I, M; ℝ⟯ := ⟨fun y => b y ^ (k - 1), hb_smooth.pow (k - 1)⟩ with hζ
  have hζ_apply : (ζ : M → ℝ) = fun y => b y ^ (k - 1) := rfl
  have hζ_nonneg : ∀ y, 0 ≤ (ζ : M → ℝ) y := by
    intro y; rw [hζ_apply]; exact pow_nonneg (hb_nonneg y) _

  have hζ_rpow : ∀ y, (ζ : M → ℝ) y = (b y) ^ ((k : ℝ) - 1) := by
    intro y
    simp only [hζ_apply]
    rw [← Real.rpow_natCast (b y) (k - 1)]
    congr 1
    rw [Nat.cast_sub _hk, Nat.cast_one]

  set v : Integral.L2.SmoothCcTensor g 0 m :=
    scalarSmul (I := I) (M := M) g 0 m ζ w with hv

  have hdiag : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w w x = b x := by
    intro x
    rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m w w x,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        ((covGrad (I := I) (M := M) g 0 m w).toSection x)]

  have hsplit : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x =
      (ζ : M → ℝ) x * b x + tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x := by
    intro x
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def, ← hdiag,
      tensorCovDerivPointwiseInner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv, tensorCovDerivAt_scalarSmul (I := I) (M := M) g 0 m ζ w x
      ((Integral.Measure.chartModelBasis E) j)]
    have hwx : Tensor0SBundle.TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
    simp only [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_smul,
      hwx, Integral.L2.tensorInnerPointwise_add_right, Integral.L2.tensorInnerPointwise_smul_right]
    ring

  have hpull : ∀ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) =
      (ζ : M → ℝ) x * Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (w.toFun x) := by
    intro x
    rw [hv, scalarSmul_toFun_apply, Integral.L2.tensorInnerPointwise_smul_right]

  have hcentral : ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ =
      - ∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Lw.toFun x) (v.toFun x) ∂μ := by
    have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
      (I := I) (M := M) g m w v
    have hdir := tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 m w v
    rw [hdir] at hgreen
    rw [hgreen, Integral.L2.tensorL2Inner, hLw]

  have hb_cont : Continuous b := hb_smooth.continuous
  have hc_cont : Continuous c := continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1 + 1) ggw
  have hζ_cont : Continuous (ζ : M → ℝ) := by
    simp only [hζ_apply]; exact hb_cont.pow (k - 1)
  have htcdpi_cont : Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g 0 m w v
  have hζb_cont : Continuous (fun x => (ζ : M → ℝ) x * b x) := hζ_cont.mul hb_cont

  have hcrossL_cont : Continuous (tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w) := by
    have heq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w =
        fun x => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x -
          (ζ : M → ℝ) x * b x := by
      funext x; rw [hsplit x]; ring
    rw [heq]; exact htcdpi_cont.sub hζb_cont

  set dw : M → ℝ := fun x => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
    (Lw.toFun x) (w.toFun x) with hdw
  have hdw_eq : dw = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 m
      Lw.toSection w.toSection := by
    funext x
    simp only [hdw, Integral.Connection.tensorInnerScalar_apply]
    rfl
  have hdw_cont : Continuous dw := by
    rw [hdw_eq]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 m
      Lw.toSection w.toSection).continuous
  have hζdw_cont : Continuous (fun x => (ζ : M → ℝ) x * dw x) := hζ_cont.mul hdw_cont

  have hint : ∀ f : M → ℝ, Continuous f → MeasureTheory.Integrable f μ := by
    intro f hf
    exact (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable
      (le_refl 1)

  set F : M → ℝ := fun x => (b x) ^ ((k : ℝ) - 1) * (c x) ^ (1 / 2 : ℝ) with hF
  have hF_nonneg : ∀ x, 0 ≤ F x := fun x =>
    mul_nonneg (Real.rpow_nonneg (hb_nonneg x) _) (Real.rpow_nonneg (hc_nonneg x) _)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk
    linarith
  have hF_cont : Continuous F :=
    (hb_cont.rpow_const (fun x => Or.inr hk1)).mul
      (hc_cont.rpow_const (fun x => Or.inr (by norm_num)))
  have hζsqrtc : ∀ x, (ζ : M → ℝ) x * Real.sqrt (c x) = F x := by
    intro x
    rw [hF, hζ_rpow x, Real.sqrt_eq_rpow]

  have hLHS_eq : (∫ x, (b x) ^ ((k : ℝ) / 1) ∂μ) = ∫ x, (ζ : M → ℝ) x * b x ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hζ_apply, div_one]
    rw [Real.rpow_natCast (b x) k]
    have hkpow : (b x) ^ (k - 1) * b x = (b x) ^ k := by
      rw [← pow_succ]; congr 1; omega
    rw [hkpow]

  have hLHS_split : (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ) =
      (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
        ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ := by
    rw [← MeasureTheory.integral_add (hint _ hζb_cont) (hint _ hcrossL_cont)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hRHS_pull : (∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) ∂μ) = ∫ x, (ζ : M → ℝ) x * dw x ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpull)
  have hmaster : (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) =
      - ∫ x, (ζ : M → ℝ) x * dw x ∂μ := by
    rw [← hLHS_split, ← hRHS_pull]; exact hcentral

  have hA_nonneg : (0 : ℝ) ≤ A := _hA

  have hcrossB : ∀ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A * F x := by
    intro x
    have hb' := covDerivCrossLeft_weight_bound (I := I) (M := M) g k m _hk w A _hA _hsup ζ
      (by simp only [hζ_apply, hb, hgw]) x
    calc |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x|
        ≤ 2 * ((k : ℝ) - 1) * A *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (gw.toSection x))
              ^ ((k : ℝ) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x (ggw.toSection x))
              ^ (1 / 2 : ℝ) := hb'
      _ = 2 * ((k : ℝ) - 1) * A * F x := by simp only [hF]; ring

  have hsqrt_a_le : ∀ x, Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x
      (w.toSection x)) ≤ A := by
    intro x
    rw [← Real.sqrt_sq _hA]
    exact Real.sqrt_le_sqrt (_hsup x)
  have hA_bound : ∀ x, (ζ : M → ℝ) x * |dw x| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * A * F x := by
    intro x
    have hcA : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) *
        Real.sqrt (c x) :=
      rawConnLap_innerWith_sqrt_finrank_bound (I := I) (M := M) g m w x
    have hsqc_nonneg : (0 : ℝ) ≤ Real.sqrt (c x) := Real.sqrt_nonneg _
    have hkey : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * Real.sqrt (c x) := by
      calc |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
              Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) *
              Real.sqrt (c x) := hcA
        _ ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * Real.sqrt (c x) := by
            apply mul_le_mul_of_nonneg_right _ hsqc_nonneg
            apply mul_le_mul_of_nonneg_left (hsqrt_a_le x) (Real.sqrt_nonneg _)
    calc (ζ : M → ℝ) x * |dw x|
        ≤ (ζ : M → ℝ) x * (Real.sqrt (Module.finrank ℝ E : ℝ) * A * Real.sqrt (c x)) :=
          mul_le_mul_of_nonneg_left hkey (hζ_nonneg x)
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * A * ((ζ : M → ℝ) x * Real.sqrt (c x)) := by ring
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * A * F x := by rw [hζsqrtc x]

  have hintF : MeasureTheory.Integrable F μ := hint _ hF_cont
  have hcrossL_int_bound :
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) ≤
        2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := by
    calc (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ ∫ x, 2 * ((k : ℝ) - 1) * A * F x ∂μ := by
          refine MeasureTheory.integral_mono (hint _ hcrossL_cont)
            ((hintF.const_mul _)) (fun x => ?_)
          exact le_trans (le_abs_self _) (hcrossB x)
      _ = 2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := MeasureTheory.integral_const_mul _ _
  have hcrossL_int_bound_neg :
      -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) ≤
        2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := by
    calc -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ |∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ∂μ :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, 2 * ((k : ℝ) - 1) * A * F x ∂μ :=
          MeasureTheory.integral_mono (hint _ hcrossL_cont.abs)
            ((hintF.const_mul _)) hcrossB
      _ = 2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := MeasureTheory.integral_const_mul _ _
  have hLap_int_bound :
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) ≤
        Real.sqrt (Module.finrank ℝ E : ℝ) * A * ∫ x, F x ∂μ := by
    calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ)
        ≤ |∫ x, (ζ : M → ℝ) x * dw x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |(ζ : M → ℝ) x * dw x| ∂μ := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, Real.sqrt (Module.finrank ℝ E : ℝ) * A * F x ∂μ := by
          refine MeasureTheory.integral_mono (hint _ hζdw_cont.abs) ((hintF.const_mul _))
            (fun x => ?_)
          rw [abs_mul, abs_of_nonneg (hζ_nonneg x)]
          exact hA_bound x
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * A * ∫ x, F x ∂μ :=
          MeasureTheory.integral_const_mul _ _

  rw [show (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (gw.toSection x))
          ^ ((k : ℝ) / 1) ∂μ) = ∫ x, (b x) ^ ((k : ℝ) / 1) ∂μ from rfl, hLHS_eq]
  have hζb_eq : (∫ x, (ζ : M → ℝ) x * b x ∂μ) =
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) := by
    have := hmaster; linarith [this]
  rw [hζb_eq]
  have hRHS_eq : (∫ x, (b x) ^ ((k : ℝ) - 1) *
        (c x) ^ (1 / 2 : ℝ) ∂μ) = ∫ x, F x ∂μ := rfl
  calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
          (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
      ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * (∫ x, F x ∂μ) +
          2 * ((k : ℝ) - 1) * A * (∫ x, F x ∂μ) := by
        have h1 := hLap_int_bound
        have h2 := hcrossL_int_bound_neg
        linarith [h1, h2]
    _ = (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A * (∫ x, F x ∂μ) := by ring
    _ = (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A *
          ∫ x, (b x) ^ ((k : ℝ) - 1) * (c x) ^ (1 / 2 : ℝ) ∂μ := by rw [hRHS_eq]

end SecondOrderInterpCore

set_option maxHeartbeats 1600000 in

private theorem secondOrderInterp_lpFiberJet_fin
    (g : SmoothRiemannianMetric I M) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ K' : ℝ, 1 ≤ K' ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g 0 m) (i : ℕ), 1 ≤ i → i + 1 < k →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 ≤
          K' *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ ((k : ℝ) / i)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))) *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / (i + 2))
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 2) / (2 * k))) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hk)

  refine ⟨max (max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1) 1, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro m w i hi1 hreg_lt
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set K' : ℝ := max (max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1) 1
    with hK'def

  set a : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)
    with ha_def
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
    ((covGrad (I := I) (M := M) g 0 m w).toSection x) with hb_def
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)).toSection x)
    with hc_def
  have ha0 : ∀ x, 0 ≤ a x := fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x _
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hac : Continuous a := continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 m w
  have hbc : Continuous b :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)
  have hcc : Continuous c :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1 + 1)
      (covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w))
  rcases lt_or_ge (i + 1) k with hreg | hreg
  · have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    have hi1R : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hi2R : (0 : ℝ) < (i : ℝ) + 2 := by positivity

    set p : ℝ := (k : ℝ) / (i + 1) with hp_def
    have hp1 : 1 < p := by
      rw [hp_def, lt_div_iff₀ hi1R, one_mul]; exact_mod_cast hreg
    have hp0 : 0 < p := lt_trans one_pos hp1
    have hp1m : 0 < p - 1 := by linarith

    set α : ℝ := 2 * (k : ℝ) / i with hα_def
    set β : ℝ := (k : ℝ) / ((k : ℝ) - ((i : ℝ) + 1)) with hβ_def
    set γ : ℝ := 2 * (k : ℝ) / (i + 2) with hγ_def
    have hkmi : 0 < (k : ℝ) - ((i : ℝ) + 1) := by
      have : ((i : ℝ) + 1) < (k : ℝ) := by exact_mod_cast hreg
      linarith
    have hα0 : 0 < α := by rw [hα_def]; positivity
    have hβ0 : 0 < β := by rw [hβ_def]; positivity
    have hγ0 : 0 < γ := by rw [hγ_def]; positivity

    have hbalance : α⁻¹ + β⁻¹ + γ⁻¹ = 1 := by
      rw [hα_def, hβ_def, hγ_def]
      rw [inv_div, inv_div, inv_div]
      field_simp
      ring

    set f₁ : M → ℝ := fun x => a x ^ (1 / 2 : ℝ) with hf₁_def
    set f₂ : M → ℝ := fun x => b x ^ (p - 1) with hf₂_def
    set f₃ : M → ℝ := fun x => c x ^ (1 / 2 : ℝ) with hf₃_def
    have hf₁c : Continuous f₁ := hac.rpow_const (fun _ => Or.inr (by norm_num))
    have hf₂c : Continuous f₂ := hbc.rpow_const (fun _ => Or.inr (le_of_lt hp1m))
    have hf₃c : Continuous f₃ := hcc.rpow_const (fun _ => Or.inr (by norm_num))
    have hf₁0 : ∀ x, 0 ≤ f₁ x := fun x => Real.rpow_nonneg (ha0 x) _
    have hf₂0 : ∀ x, 0 ≤ f₂ x := fun x => Real.rpow_nonneg (hb0 x) _
    have hf₃0 : ∀ x, 0 ≤ f₃ x := fun x => Real.rpow_nonneg (hc0 x) _

    have hHolder := real_holder_three_nonneg (I := I) (M := M) g f₁ f₂ f₃
      hf₁c hf₂c hf₃c hf₁0 hf₂0 hf₃0 hα0 hβ0 hγ0 hbalance

    have hαexp : (1 / 2 : ℝ) * α = (k : ℝ) / i := by
      rw [hα_def]; field_simp
    have he1 : ∀ x, f₁ x ^ α = a x ^ ((k : ℝ) / i) := by
      intro x; rw [hf₁_def, ← Real.rpow_mul (ha0 x), hαexp]

    have hγexp : (1 / 2 : ℝ) * γ = (k : ℝ) / (i + 2) := by
      rw [hγ_def]; field_simp
    have he3 : ∀ x, f₃ x ^ γ = c x ^ ((k : ℝ) / (i + 2)) := by
      intro x; rw [hf₃_def, ← Real.rpow_mul (hc0 x), hγexp]

    have hβexp : (p - 1) * β = p := by
      have hpm1 : p - 1 = ((k : ℝ) - ((i : ℝ) + 1)) / ((i : ℝ) + 1) := by
        rw [hp_def, div_sub_one (ne_of_gt hi1R)]
      rw [hpm1, hβ_def, hp_def, div_mul_div_comm, mul_comm ((k : ℝ) - ((i : ℝ) + 1)) (k : ℝ),
        mul_div_mul_right _ _ (ne_of_gt hkmi)]
    have he2 : ∀ x, f₂ x ^ β = b x ^ p := by
      intro x; rw [hf₂_def, ← Real.rpow_mul (hb0 x), hβexp]
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he1),
        MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he2),
        MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he3)] at hHolder

    have hprod_pt : ∀ x, a x ^ (1 / 2 : ℝ) * b x ^ (p - 1) * c x ^ (1 / 2 : ℝ)
        = f₁ x * f₂ x * f₃ x := fun x => by rw [hf₁_def, hf₂_def, hf₃_def]

    have hIBP := weightedCovIBP_lpFiberJet_fin (I := I) (M := M) g k m i _hk hi1 hreg w

    rw [show (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
                ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (m + 1)
                  (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ) ∂μ)
            = ∫ x, f₁ x * f₂ x * f₃ x ∂μ from by
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun x => ?_))
        rw [hf₁_def, hf₂_def, hf₃_def, ha_def, hb_def, hc_def, hp_def]] at hIBP

    set Ia : ℝ := ∫ x, a x ^ ((k : ℝ) / i) ∂μ with hIa_def
    set Ib : ℝ := ∫ x, b x ^ p ∂μ with hIb_def
    set Ic : ℝ := ∫ x, c x ^ ((k : ℝ) / (i + 2)) ∂μ with hIc_def
    have hIa_nn : 0 ≤ Ia := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (ha0 x) _)
    have hIb_nn : 0 ≤ Ib := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hb0 x) _)
    have hIc_nn : 0 ≤ Ic := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hc0 x) _)
    set Aw : ℝ := Ia ^ ((i : ℝ) / (2 * k)) with hAw_def
    set C : ℝ := Ic ^ (((i : ℝ) + 2) / (2 * k)) with hC_def
    have hAw_nn : 0 ≤ Aw := Real.rpow_nonneg hIa_nn _
    have hC_nn : 0 ≤ C := Real.rpow_nonneg hIc_nn _

    have hinvα : (1 : ℝ) / α = (i : ℝ) / (2 * k) := by rw [hα_def]; rw [one_div_div]
    have hinvγ : (1 : ℝ) / γ = ((i : ℝ) + 2) / (2 * k) := by rw [hγ_def]; rw [one_div_div]

    set D : ℝ := 2 * (p - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD_def
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _

    have hIb_bound : Ib ≤ D * (Aw * (Ib ^ (1 / β) * C)) := by
      have hcoef_nn : 0 ≤ D := by rw [hD_def]; nlinarith [hp1m, hsqrt_nn]
      have hstep : Ib ≤ D * (∫ x, f₁ x * f₂ x * f₃ x ∂μ) := hIBP
      refine le_trans hstep ?_
      apply mul_le_mul_of_nonneg_left _ hcoef_nn
      rw [hinvα, hinvγ] at hHolder
      rw [hAw_def, hC_def]
      exact hHolder

    have hinvp : (1 : ℝ) / p = ((i : ℝ) + 1) / k := by
      rw [hp_def, one_div_div]
    have hinvβ : (1 : ℝ) / β = ((k : ℝ) - ((i : ℝ) + 1)) / k := by
      rw [hβ_def, one_div_div]
    have hsum_pβ : (1 : ℝ) / p + 1 / β = 1 := by
      rw [hinvp, hinvβ, ← add_div]
      rw [show ((i : ℝ) + 1) + ((k : ℝ) - ((i : ℝ) + 1)) = (k : ℝ) from by ring,
        div_self (ne_of_gt hkR)]

    have hLHS_sq : (Ib ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 = Ib ^ ((1 : ℝ) / p) := by
      have hexp : ((i : ℝ) + 1) / (2 * k) * ((2 : ℕ) : ℝ) = (1 : ℝ) / p := by
        rw [hinvp]; push_cast; ring
      rw [← Real.rpow_natCast (Ib ^ (((i : ℝ) + 1) / (2 * k))) 2, ← Real.rpow_mul hIb_nn, hexp]

    have hcoef_le : D ≤ K' := by
      have hp_le_k : p ≤ (k : ℝ) := by
        rw [hp_def, div_le_iff₀ hi1R]
        nlinarith [hkR, hiR]
      have hDk : D ≤ 2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) := by
        rw [hD_def]; linarith
      exact le_trans hDk (le_trans (le_max_left _ _) (le_max_left _ _))

    rw [hLHS_sq]
    rcases eq_or_lt_of_le hIb_nn with hIb0 | hIbpos
    · rw [← hIb0, Real.zero_rpow (by rw [hinvp]; positivity)]
      positivity
    · have hIbβ_pos : 0 < Ib ^ (1 / β) := Real.rpow_pos_of_pos hIbpos _

      have hIb_split : Ib = Ib ^ ((1 : ℝ) / p) * Ib ^ (1 / β) := by
        rw [← Real.rpow_add hIbpos, hsum_pβ, Real.rpow_one]

      have hkey : Ib ^ ((1 : ℝ) / p) * Ib ^ (1 / β) ≤ (D * (Aw * C)) * Ib ^ (1 / β) := by
        rw [← hIb_split]
        calc Ib ≤ D * (Aw * (Ib ^ (1 / β) * C)) := hIb_bound
          _ = (D * (Aw * C)) * Ib ^ (1 / β) := by ring
      have hcancel : Ib ^ ((1 : ℝ) / p) ≤ D * (Aw * C) :=
        le_of_mul_le_mul_right hkey hIbβ_pos
      calc Ib ^ ((1 : ℝ) / p) ≤ D * (Aw * C) := hcancel
        _ ≤ K' * (Aw * C) := by
            apply mul_le_mul_of_nonneg_right hcoef_le (mul_nonneg hAw_nn hC_nn)
        _ = K' * Aw * C := by ring
  · exfalso; omega

set_option maxHeartbeats 1600000 in

private theorem secondOrderInterp_lpFiberJet_sup
    (g : SmoothRiemannianMetric I M) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ K' : ℝ, 1 ≤ K' ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g 0 m) (A : ℝ), 0 ≤ A →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2) →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / 1)
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((1 : ℝ) / (2 * k))) ^ 2 ≤
          K' * A *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / 2)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((2 : ℝ) / (2 * k))) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hk)
  refine ⟨max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1, le_max_right _ _, ?_⟩
  intro m w A hA hsup
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set K' : ℝ := max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1 with hK'def
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
    ((covGrad (I := I) (M := M) g 0 m w).toSection x) with hb_def
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)).toSection x)
    with hc_def
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hbc : Continuous b :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)
  have hcc : Continuous c :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g 0 (m + 1 + 1)
      (covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w))
  set Ib : ℝ := ∫ x, b x ^ ((k : ℝ) / 1) ∂μ with hIb_def
  set Ic : ℝ := ∫ x, c x ^ ((k : ℝ) / 2) ∂μ with hIc_def
  have hIb_nn : 0 ≤ Ib := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hb0 x) _)
  have hIc_nn : 0 ≤ Ic := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hc0 x) _)
  set C : ℝ := Ic ^ ((2 : ℝ) / (2 * k)) with hC_def
  have hC_nn : 0 ≤ C := Real.rpow_nonneg hIc_nn _

  have hIBP := weightedCovIBP_lpFiberJet_sup (I := I) (M := M) g k m _hk w A hA hsup

  have hk1 : (k : ℝ) / 1 = (k : ℝ) := by norm_num
  have hLHS_sq : (Ib ^ ((1 : ℝ) / (2 * k))) ^ 2 = Ib ^ ((1 : ℝ) / k) := by
    have hexp : (1 : ℝ) / (2 * k) * ((2 : ℕ) : ℝ) = (1 : ℝ) / k := by push_cast; ring
    rw [← Real.rpow_natCast (Ib ^ ((1 : ℝ) / (2 * k))) 2, ← Real.rpow_mul hIb_nn, hexp]

  have hC_eq : C = Ic ^ ((1 : ℝ) / k) := by
    rw [hC_def]; congr 1; rw [eq_div_iff (by positivity)]; field_simp
  rw [hLHS_sq]

  set J : ℝ := ∫ x, b x ^ ((k : ℝ) - 1) * c x ^ (1 / 2 : ℝ) ∂μ with hJ_def
  have hJ_nn : 0 ≤ J := MeasureTheory.integral_nonneg (fun x =>
    mul_nonneg (Real.rpow_nonneg (hb0 x) _) (Real.rpow_nonneg (hc0 x) _))

  set D : ℝ := 2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD_def
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _
  have hkm1_nn : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk
    linarith
  have hD_nn : 0 ≤ D := by rw [hD_def]; nlinarith [hkm1_nn, hsqrt_nn]

  have hIBP' : Ib ≤ D * A * J := by
    rw [hIb_def, hJ_def, hD_def]; exact hIBP

  have hJ_bound : J ≤ Ib ^ (((k : ℝ) - 1) / k) * C := by
    rcases eq_or_lt_of_le _hk with hk_eq | hk_gt
    · have hk1' : (k : ℝ) = 1 := by exact_mod_cast hk_eq.symm
      have hb0pow : ∀ x, b x ^ ((k : ℝ) - 1) = 1 := by
        intro x; rw [hk1']; norm_num
      rw [hJ_def]
      simp_rw [hb0pow, one_mul]
      rw [hk1']
      simp only [sub_self, zero_div, Real.rpow_zero, one_mul]

      have hCeq1 : C = ∫ x, c x ^ (1 / 2 : ℝ) ∂μ := by
        rw [hC_def, hIc_def, hk1']
        norm_num
      rw [hCeq1]
    · have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_gt
      have hkm1 : 0 < (k : ℝ) - 1 := by linarith
      set β : ℝ := (k : ℝ) / ((k : ℝ) - 1) with hβ_def
      have hβ0 : 0 < β := by rw [hβ_def]; positivity
      have hconj : β.HolderConjugate (k : ℝ) := by
        refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
        · rw [hβ_def, one_lt_div hkm1]; linarith
        · rw [hβ_def, inv_div, inv_eq_one_div, div_add_div _ _ (ne_of_gt hkR) (ne_of_gt hkR),
            div_eq_one_iff_eq (by positivity)]
          ring

      have hf2c : Continuous (fun x => b x ^ ((k : ℝ) - 1)) :=
        hbc.rpow_const (fun _ => Or.inr (le_of_lt hkm1))
      have hf3c : Continuous (fun x => c x ^ (1 / 2 : ℝ)) :=
        hcc.rpow_const (fun _ => Or.inr (by norm_num))
      have hf2mem : MeasureTheory.MemLp (fun x => b x ^ ((k : ℝ) - 1)) (ENNReal.ofReal β) μ :=
        hf2c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hf3mem : MeasureTheory.MemLp (fun x => c x ^ (1 / 2 : ℝ)) (ENNReal.ofReal (k : ℝ)) μ :=
        hf3c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hH := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj
        (f := fun x => b x ^ ((k : ℝ) - 1)) (g := fun x => c x ^ (1 / 2 : ℝ))
        (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hb0 x) _))
        (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hc0 x) _)) hf2mem hf3mem

      have hβcancel : ((k : ℝ) - 1) * β = (k : ℝ) := by
        rw [hβ_def, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self (ne_of_gt hkm1), mul_one]
      have hpow2 : ∀ x, (b x ^ ((k : ℝ) - 1)) ^ β = b x ^ ((k : ℝ) / 1) := by
        intro x; rw [← Real.rpow_mul (hb0 x), hβcancel, hk1]
      have hpow3 : ∀ x, (c x ^ (1 / 2 : ℝ)) ^ (k : ℝ) = c x ^ ((k : ℝ) / 2) := by
        intro x; rw [← Real.rpow_mul (hc0 x)]; congr 1; ring
      rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow2),
          MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow3)] at hH

      have hinvβ : (1 : ℝ) / β = ((k : ℝ) - 1) / k := by rw [hβ_def, one_div_div]
      have hinvk : (1 : ℝ) / (k : ℝ) = (2 : ℝ) / (2 * k) := by
        rw [eq_div_iff (by positivity)]; field_simp
      rw [hinvβ, hinvk] at hH

      rw [show (∫ x, b x ^ ((k : ℝ) / 1) ∂μ) = Ib from hIb_def.symm,
          show (∫ x, c x ^ ((k : ℝ) / 2) ∂μ) = Ic from hIc_def.symm,
          ← hC_def] at hH
      rw [hJ_def]
      exact hH

  have hcoef_le : D ≤ K' := by rw [hD_def]; exact le_max_left _ _
  have hAC_nn : 0 ≤ A * C := mul_nonneg hA hC_nn

  have hsum_k : (1 : ℝ) / k + ((k : ℝ) - 1) / k = 1 := by
    rw [← add_div, show (1 : ℝ) + ((k : ℝ) - 1) = (k : ℝ) from by ring, div_self (ne_of_gt hkR)]
  rcases eq_or_lt_of_le hIb_nn with hIb0 | hIbpos
  · rw [← hIb0, Real.zero_rpow (by positivity)]
    positivity
  · have hIbβ_pos : 0 < Ib ^ (((k : ℝ) - 1) / k) := Real.rpow_pos_of_pos hIbpos _
    have hIb_split : Ib = Ib ^ ((1 : ℝ) / k) * Ib ^ (((k : ℝ) - 1) / k) := by
      rw [← Real.rpow_add hIbpos, hsum_k, Real.rpow_one]
    have hchain : Ib ^ ((1 : ℝ) / k) * Ib ^ (((k : ℝ) - 1) / k)
        ≤ (D * (A * C)) * Ib ^ (((k : ℝ) - 1) / k) := by
      rw [← hIb_split]
      calc Ib ≤ D * A * J := hIBP'
        _ ≤ D * A * (Ib ^ (((k : ℝ) - 1) / k) * C) := by
            apply mul_le_mul_of_nonneg_left hJ_bound
            exact mul_nonneg hD_nn hA
        _ = (D * (A * C)) * Ib ^ (((k : ℝ) - 1) / k) := by ring
    have hcancel : Ib ^ ((1 : ℝ) / k) ≤ D * (A * C) :=
      le_of_mul_le_mul_right hchain hIbβ_pos
    calc Ib ^ ((1 : ℝ) / k) ≤ D * (A * C) := hcancel
      _ ≤ K' * (A * C) := mul_le_mul_of_nonneg_right hcoef_le hAC_nn
      _ = K' * A * C := by ring

private theorem lpFiberJet_logConvex_iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ i : ℕ, i + 1 < k →
          (lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 1)) ^ 2 ≤
            K * lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i *
              lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 2) := by
  classical
  obtain ⟨Kf, hKf1, hfin⟩ := secondOrderInterp_lpFiberJet_fin (I := I) (M := M) g k hk
  obtain ⟨Ks, hKs1, hsupc⟩ := secondOrderInterp_lpFiberJet_sup (I := I) (M := M) g k hk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hkRpos : (0 : ℝ) < (k : ℝ) := by positivity
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _

  refine ⟨max (max Kf 1) (Ks * (1 / V) + Ks), ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro u Λ₀ hΛ₀ hsup
  set K : ℝ := max (max Kf 1) (Ks * (1 / V) + Ks) with hKdef
  have hKf_le : Kf ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKsV_le : Ks * (1 / V) + Ks ≤ K := le_max_right _ _

  set J : ℕ → ℝ := fun i =>
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)) ^ ((k : ℝ) / i)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k)) with hJdef
  have hJnn : ∀ i, 0 ≤ J i := by
    intro i; rw [hJdef]
    exact Real.rpow_nonneg (integral_nonneg (fun x =>
      Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + i) x _) _)) _

  have hread : ∀ i, 1 ≤ i → lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i = J i := by
    intro i hi1
    rcases eq_or_ne i k with hik | hik
    · subst hik
      rw [hJdef]
      simp only [lpFiberJetLadder, if_neg (show i ≠ 0 by omega), if_true]
      set t : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toFun with ht
      have htnn : 0 ≤ t := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + i) _
      have hbridge : (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) = t ^ 2 := by
        rw [ht, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (s + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u)]
      have hii : (i : ℝ) / i = 1 := by
        rw [div_self]; exact_mod_cast (show i ≠ 0 by omega)
      symm
      calc (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)) ^ ((i : ℝ) / i)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * i))
          = (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((1 : ℝ) / 2) := by
              rw [hii]
              simp only [Real.rpow_one]
              rw [show (i : ℝ) / (2 * i) = 1 / 2 by field_simp]
        _ = (t ^ 2) ^ ((1 : ℝ) / 2) := by rw [hbridge]
        _ = t := by
              rw [← Real.rpow_natCast t 2, ← Real.rpow_mul htnn]
              norm_num
    · rw [hJdef]
      simp only [lpFiberJetLadder, if_neg (show i ≠ 0 by omega), if_neg hik]

  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · have hmuzero : (Integral.Measure.riemannianVolumeMeasure I M g) = 0 := by
      have hfin : (Integral.Measure.riemannianVolumeMeasure I M g) Set.univ ≠ ⊤ := by
        haveI := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
          (I := I) (M := M) g
        exact (MeasureTheory.measure_ne_top _ _)
      have htoReal0 : ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal = 0 := by
        have hsqrt0 : Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
            = 0 := by rw [← hV]; exact hV0.symm
        have hle := Real.sqrt_eq_zero'.mp hsqrt0
        exact le_antisymm hle ENNReal.toReal_nonneg
      have huniv0 : (Integral.Measure.riemannianVolumeMeasure I M g) Set.univ = 0 := by
        rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at htoReal0
      exact MeasureTheory.Measure.measure_univ_eq_zero.mp huniv0
    have hJ0 : ∀ i, 1 ≤ i → J i = 0 := by
      intro i hi
      simp only [hJdef, hmuzero, MeasureTheory.integral_zero_measure]
      apply Real.zero_rpow
      have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      positivity
    intro i _hik
    have h1 : lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 1) = 0 := by
      rw [hread (i + 1) (by omega), hJ0 (i + 1) (by omega)]
    have h3 : lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 2) = 0 := by
      rw [hread (i + 2) (by omega), hJ0 (i + 2) (by omega)]
    rw [h1, h3]; ring_nf
    positivity
  · have hVne : V ≠ 0 := ne_of_gt hVpos
    intro i hik
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [hread 1 (by omega), hread 2 (by omega)]
      have hc0eq : lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ 0 = Λ₀ * V := by
        rw [show lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ 0
              = Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
            from by unfold lpFiberJetLadder; rw [if_pos rfl], ← hV]
      rw [hc0eq]

      have hstep := hsupc s u Λ₀ hΛ₀ hsup

      have e1 : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
      have e2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [show ((k : ℝ) / 1) = ((k : ℝ) / ((1 : ℕ) : ℝ)) by norm_num,
          show ((1 : ℝ) / (2 * k)) = (((1 : ℕ) : ℝ) / (2 * k)) by norm_num,
          show ((k : ℝ) / 2) = ((k : ℝ) / ((2 : ℕ) : ℝ)) by norm_num,
          show ((2 : ℝ) / (2 * k)) = (((2 : ℕ) : ℝ) / (2 * k)) by norm_num] at hstep

      have hstep' : (J 1) ^ 2 ≤ Ks * Λ₀ * J 2 := hstep
      refine le_trans hstep' ?_
      have hJ2nn : 0 ≤ J 2 := hJnn 2
      have hreconc : Ks * Λ₀ ≤ K * (Λ₀ * V) := by
        have hKsKV : Ks ≤ K * V := by
          have hKsdivV : Ks / V ≤ K := by
            have hKsle : Ks ≤ Ks * (1 / V) + Ks := by
              have : 0 ≤ Ks * (1 / V) := by positivity
              linarith
            have : Ks * (1 / V) ≤ K := le_trans (by linarith) hKsV_le
            rw [div_eq_mul_one_div]; exact le_trans this (le_refl _)
          calc Ks = (Ks / V) * V := by field_simp
            _ ≤ K * V := mul_le_mul_of_nonneg_right hKsdivV hVnn
        nlinarith [hKsKV, hΛ₀, mul_nonneg (le_trans zero_le_one hKs1) hΛ₀]
      exact mul_le_mul_of_nonneg_right hreconc hJ2nn
    · rw [hread (i + 1) (by omega), hread i hipos, hread (i + 2) (by omega)]
      have hstep := hfin (s + i) (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u) i hipos hik

      have e1 : ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      have e2 : ((i : ℝ) + 2) = ((i + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [e1, e2] at hstep

      refine le_trans hstep ?_
      have hJinn : 0 ≤ J i := hJnn i
      have hJi2nn : 0 ≤ J (i + 2) := hJnn (i + 2)
      have hbase : Kf * J i * J (i + 2) ≤ K * J i * J (i + 2) := by
        apply mul_le_mul_of_nonneg_right _ hJi2nn
        apply mul_le_mul_of_nonneg_right hKf_le hJinn
      exact le_trans (le_of_eq (by rfl)) hbase

theorem exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) ≤
            C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ (2 * (j : ℝ) / k) := by
  classical
  obtain ⟨K, hK1, hlc⟩ := lpFiberJet_logConvex_iteratedCovGrad (I := I) (M := M) g s k _hk
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _
  have hmax1 : (1 : ℝ) ≤ max 1 V := le_max_left _ _
  have hmaxV : V ≤ max 1 V := le_max_right _ _
  have hmax_nn : 0 ≤ max 1 V := le_trans zero_le_one hmax1

  set C : ℝ := K ^ (2 * k ^ 2) * (max 1 V) ^ 2 with hC
  have hKnn : 0 ≤ K := le_trans zero_le_one hK1
  have hC_nn : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro u Λ₀ hΛ₀ hsup j hj0 hjk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hkRpos : (0 : ℝ) < (k : ℝ) := by positivity

  set c : ℕ → ℝ := fun i => lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i with hc_def

  have hc_nn : ∀ i, 0 ≤ c i := by
    intro i
    rw [hc_def]
    simp only [lpFiberJetLadder]
    split_ifs with hi0 hik
    · exact mul_nonneg hΛ₀ hVnn
    · exact Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _
    · exact Real.rpow_nonneg (integral_nonneg (fun x =>
        Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + i) x _) _)) _

  have hc_lc : ∀ i, i + 1 < k → (c (i + 1)) ^ 2 ≤ K * c i * c (i + 2) := by
    intro i hik; rw [hc_def]; exact hlc u Λ₀ hΛ₀ hsup i hik

  have hpow : (c j) ^ k ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j :=
    discrete_log_convex_power_interpolation c hc_nn K hK1 j k hc_lc hj0 hjk

  have hc0_eq : c 0 = Λ₀ * V := by
    simp only [hc_def, lpFiberJetLadder, if_pos rfl]
    rw [hV]
  have hck_eq : c k = Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun := by
    simp only [hc_def, lpFiberJetLadder, if_neg (show k ≠ 0 by omega), if_true]
  have hcj_sq : (c j) ^ 2 =
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) := by
    simp only [hc_def, lpFiberJetLadder, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ k by omega)]
    set Iint : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g) with hIint
    have hIint_nn : 0 ≤ Iint := integral_nonneg (fun x =>
      Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + j) x _) _)
    have hexp : (j : ℝ) / (2 * k) * ((2 : ℕ) : ℝ) = (j : ℝ) / k := by
      push_cast
      rw [mul_comm, ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.rpow_natCast (Iint ^ ((j : ℝ) / (2 * k))) 2,
        ← Real.rpow_mul hIint_nn, hexp]

  have hc0_nn : 0 ≤ c 0 := hc_nn 0
  have hck_nn : 0 ≤ c k := hc_nn k
  have hcj_nn : 0 ≤ c j := hc_nn j

  have hpow_sq : ((c j) ^ 2) ^ k ≤
      (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
    have hrw : ((c j) ^ 2) ^ k = ((c j) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hrw]
    have hbase_nn : 0 ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j := by positivity
    calc ((c j) ^ k) ^ 2 ≤ (K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hpow 2
      _ = (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf

  have hcj2_nn : 0 ≤ (c j) ^ 2 := by positivity
  have hmono : (((c j) ^ 2) ^ k) ^ ((k : ℝ)⁻¹) ≤
      ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hpow_sq (by positivity)
  rw [Real.pow_rpow_inv_natCast hcj2_nn hk0] at hmono

  have hcast_sub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (le_of_lt hjk)]
  have hrhs : ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) =
      (K ^ (2 * k ^ 2)) * ((c 0) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * ((c k) ^ 2) ^ ((j : ℝ) / k) := by
    have hKpow_nn : 0 ≤ (K ^ (k ^ 3)) ^ 2 := by positivity
    have hc02_nn : 0 ≤ ((c 0) ^ 2) ^ (k - j) := by positivity
    have hck2_nn : 0 ≤ ((c k) ^ 2) ^ j := by positivity
    rw [Real.mul_rpow (by positivity) hck2_nn, Real.mul_rpow hKpow_nn hc02_nn]
    congr 1
    · congr 1
      · have hexpK : ((k ^ 3 * 2 : ℕ) : ℝ) * (k : ℝ)⁻¹ = ((2 * k ^ 2 : ℕ) : ℝ) := by
          push_cast
          field_simp
        rw [← pow_mul, ← Real.rpow_natCast K (k ^ 3 * 2), ← Real.rpow_mul hKnn, hexpK,
          Real.rpow_natCast K (2 * k ^ 2)]
      · have hexp0 : ((k - j : ℕ) : ℝ) * (k : ℝ)⁻¹ = (1 : ℝ) - (j : ℝ) / k := by
          rw [hcast_sub]
          field_simp
        rw [← Real.rpow_natCast ((c 0) ^ 2) (k - j), ← Real.rpow_mul (by positivity), hexp0]
    · rw [← Real.rpow_natCast ((c k) ^ 2) j, ← Real.rpow_mul (by positivity), div_eq_mul_inv]
  rw [hrhs] at hmono

  rw [hcj_sq] at hmono
  rw [hc0_eq, hck_eq] at hmono

  set ak : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun with hak_def
  have hak_nn : 0 ≤ ak := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _

  have hak_pow : (ak ^ 2) ^ ((j : ℝ) / k) = ak ^ (2 * (j : ℝ) / k) := by
    rw [← Real.rpow_natCast ak 2, ← Real.rpow_mul hak_nn]
    congr 1
    push_cast; ring

  have hweight_nn : 0 ≤ (1 : ℝ) - (j : ℝ) / k := by
    have : (j : ℝ) / k ≤ 1 := by
      rw [div_le_one hkRpos]; exact_mod_cast le_of_lt hjk
    linarith
  have hweight_le1 : (1 : ℝ) - (j : ℝ) / k ≤ 1 := by
    have : 0 ≤ (j : ℝ) / k := by positivity
    linarith
  have hLV_pow : ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) =
      Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) := by
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast Λ₀ 2, ← Real.rpow_mul hΛ₀]
    norm_num

  have hV2_le : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (max 1 V) ^ 2 := by
    have hV2_nn : 0 ≤ V ^ 2 := by positivity
    have h2max : (1 : ℝ) ≤ (max 1 V) ^ 2 := by
      have := pow_le_pow_left₀ (zero_le_one) hmax1 2
      rwa [one_pow] at this
    rcases le_total (V ^ 2) 1 with hle | hge
    · have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ 1 :=
        Real.rpow_le_one hV2_nn hle hweight_nn
      linarith
    · have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (V ^ 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hge hweight_le1
      rw [Real.rpow_one] at h1
      have hV2_le_max : V ^ 2 ≤ (max 1 V) ^ 2 := pow_le_pow_left₀ hVnn hmaxV 2
      linarith

  calc (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k)
      ≤ K ^ (2 * k ^ 2) * ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * (ak ^ 2) ^ ((j : ℝ) / k) :=
        hmono
    _ = K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by rw [hLV_pow, hak_pow]
    _ ≤ K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (max 1 V) ^ 2) *
          ak ^ (2 * (j : ℝ) / k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hV2_le (by positivity)
    _ = (K ^ (2 * k ^ 2) * (max 1 V) ^ 2) * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by ring
    _ = C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) * ak ^ (2 * (j : ℝ) / k) := by rw [hC]

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
