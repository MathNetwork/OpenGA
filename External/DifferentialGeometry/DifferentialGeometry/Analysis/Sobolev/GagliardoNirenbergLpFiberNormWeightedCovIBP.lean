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
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormKatoSecondCovDerivBound

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

set_option maxHeartbeats 2000000 in

private theorem covDerivCrossLeft_weight_bound_rs
    (g : SmoothRiemannianMetric I M) (k m r : ℕ) (_hk : 1 ≤ k)
    (w : Integral.L2.SmoothCcTensor g r m) (A : ℝ) (_hA : 0 ≤ A)
    (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) ≤ A ^ 2)
    (ζ : C^∞⟮I, M; ℝ⟯)
    (hζ : (ζ : M → ℝ) = fun y => (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) y
        ((covGrad (I := I) (M := M) g r m w).toSection y)) ^ (k - 1))
    (x : M) :
    |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A *
        (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
          ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) - 1) *
        (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
          ((covGrad (I := I) (M := M) g r (m + 1)
            (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set Q : Integral.L2.SmoothCcTensor g r (m + 1) := covGrad (I := I) (M := M) g r m w with hQ_def
  set bfun : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g r (m + 1) y (Q.toSection y) with hbfun_def
  set b : ℝ := bfun x with hb_def
  set c : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
      ((covGrad (I := I) (M := M) g r (m + 1) Q).toSection x) with hc_def
  have hb_nn : 0 ≤ b := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x (Q.toSection x)
  have hc_nn : 0 ≤ c := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) x _
  have hAsq : riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) ≤ A ^ 2 := _hsup x

  set P : Integral.L2.SmoothCcTensor g r (m + 1) :=
    prependCovGradSlot (I := I) (M := M) g r m ζ w with hP_def
  have hcross_eq : tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x =
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) :=
    tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M) g r m ζ w w x

  set rP : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (P.toSection x) with hrP_def
  have hrP_nn : 0 ≤ rP := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x _
  have hCS2 : |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ≤
      Real.sqrt b * Real.sqrt rP := by
    rw [hcross_eq]
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r (m + 1) x
      (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
      (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
    have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) = b := by
      rw [show b = riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (Q.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) x (Q.toSection x)]
    have hPself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) = rP := by
      rw [show rP = riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (P.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) x (P.toSection x)]
    rw [hQself, hPself] at hsq
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hb_nn]
    exact Real.sqrt_le_sqrt hsq

  have hrP_eq : rP = (∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
        riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) :=
    prependCovGradSlot_fiberNormSq_frame_sum_rs (I := I) (M := M) g r m ζ w x

  have hbfun_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) bfun x := by
    have hb_eq_scalar : bfun = Integral.Connection.tensorInnerScalar (I := I) (M := M) g r (m + 1)
        Q.toSection Q.toSection := by
      funext y
      simp only [hbfun_def, Integral.Connection.tensorInnerScalar_apply]
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) y
        (Q.toSection y)]
    rw [hb_eq_scalar]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g r (m + 1)
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
    kato_mfderiv_riemannianFiberNormSq_frame_sum_le_rs (I := I) (M := M) g r (m + 1) Q x

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
    have hrfnsw_le : riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) ≤ A ^ 2 := hAsq
    have hrfnsw_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r m x (w.toSection x)
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
            riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)
        ≤ (((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c)) *
            riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) :=
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
  change |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ≤
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

theorem weightedCovIBP_lpFiberJet_sup_rs
    (g : SmoothRiemannianMetric I M) (k m r : ℕ) (_hk : 1 ≤ k)
    (w : Integral.L2.SmoothCcTensor g r m) (A : ℝ) (_hA : 0 ≤ A)
    (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) ≤ A ^ 2) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
            ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / 1)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g r (m + 1)
                (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  set gw : Integral.L2.SmoothCcTensor g r (m + 1) := covGrad (I := I) (M := M) g r m w with hgw
  set ggw : Integral.L2.SmoothCcTensor g r (m + 1 + 1) :=
    covGrad (I := I) (M := M) g r (m + 1) gw with hggw
  set Lw : Integral.L2.SmoothCcTensor g r m :=
    rawTensorConnLapSmooth (I := I) g r m w with hLw
  set b : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g r (m + 1) y (gw.toSection y)
    with hb
  set c : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) y (ggw.toSection y) with hc
  have hb_nonneg : ∀ y, 0 ≤ b y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) y (gw.toSection y)
  have hc_nonneg : ∀ y, 0 ≤ c y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) y (ggw.toSection y)
  have hb_eq_scalar : b = Integral.Connection.tensorInnerScalar (I := I) (M := M) g r (m + 1)
      gw.toSection gw.toSection := by
    funext y
    simp only [hb, Integral.Connection.tensorInnerScalar_apply]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) y
      (gw.toSection y)]
  have hb_smooth : ContMDiff I 𝓘(ℝ) ∞ b := by
    rw [hb_eq_scalar]
    exact Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g r (m + 1)
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
  set v : Integral.L2.SmoothCcTensor g r m :=
    scalarSmul (I := I) (M := M) g r m ζ w with hv
  have hdiag : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w w x = b x := by
    intro x
    rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad (I := I) (M := M) g r m w w x,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
        ((covGrad (I := I) (M := M) g r m w).toSection x)]
  have hsplit : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x =
      (ζ : M → ℝ) x * b x + tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x := by
    intro x
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def, ← hdiag,
      tensorCovDerivPointwiseInner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv, tensorCovDerivAt_scalarSmul (I := I) (M := M) g r m ζ w x
      ((Integral.Measure.chartModelBasis E) j)]
    have hwx : Tensor0SBundle.TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
    simp only [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_smul,
      hwx, Integral.L2.tensorInnerPointwise_add_right, Integral.L2.tensorInnerPointwise_smul_right]
    ring
  have hpull : ∀ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Lw.toFun x) (v.toFun x) =
      (ζ : M → ℝ) x * Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Lw.toFun x) (w.toFun x) := by
    intro x
    rw [hv, scalarSmul_toFun_apply, Integral.L2.tensorInnerPointwise_smul_right]
  have hcentral : ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x ∂μ =
      - ∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
          (Lw.toFun x) (v.toFun x) ∂μ := by
    have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
      (I := I) (M := M) g r m w v
    have hdir := tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g r m w v
    rw [hdir] at hgreen
    rw [hgreen, Integral.L2.tensorL2Inner, hLw]
  have hb_cont : Continuous b := hb_smooth.continuous
  have hc_cont : Continuous c := continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1 + 1) ggw
  have hζ_cont : Continuous (ζ : M → ℝ) := by
    simp only [hζ_apply]; exact hb_cont.pow (k - 1)
  have htcdpi_cont : Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g r m w v
  have hζb_cont : Continuous (fun x => (ζ : M → ℝ) x * b x) := hζ_cont.mul hb_cont
  have hcrossL_cont : Continuous (tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w) := by
    have heq : tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w =
        fun x => tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x -
          (ζ : M → ℝ) x * b x := by
      funext x; rw [hsplit x]; ring
    rw [heq]; exact htcdpi_cont.sub hζb_cont
  set dw : M → ℝ := fun x => Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
    (Lw.toFun x) (w.toFun x) with hdw
  have hdw_eq : dw = Integral.Connection.tensorInnerScalar (I := I) (M := M) g r m
      Lw.toSection w.toSection := by
    funext x
    simp only [hdw, Integral.Connection.tensorInnerScalar_apply]
    rfl
  have hdw_cont : Continuous dw := by
    rw [hdw_eq]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g r m
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
  have hLHS_split : (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x ∂μ) =
      (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
        ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ := by
    rw [← MeasureTheory.integral_add (hint _ hζb_cont) (hint _ hcrossL_cont)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hRHS_pull : (∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Lw.toFun x) (v.toFun x) ∂μ) = ∫ x, (ζ : M → ℝ) x * dw x ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpull)
  have hmaster : (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ) =
      - ∫ x, (ζ : M → ℝ) x * dw x ∂μ := by
    rw [← hLHS_split, ← hRHS_pull]; exact hcentral
  have hcrossB : ∀ x, |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A * F x := by
    intro x
    have hb' := covDerivCrossLeft_weight_bound_rs (I := I) (M := M) g k m r _hk w A _hA _hsup ζ
      (by simp only [hζ_apply, hb, hgw]) x
    calc |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x|
        ≤ 2 * ((k : ℝ) - 1) * A *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (gw.toSection x))
              ^ ((k : ℝ) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x (ggw.toSection x))
              ^ (1 / 2 : ℝ) := hb'
      _ = 2 * ((k : ℝ) - 1) * A * F x := by simp only [hF]; ring
  have hsqrt_a_le : ∀ x, Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r m x
      (w.toSection x)) ≤ A := by
    intro x
    rw [← Real.sqrt_sq _hA]
    exact Real.sqrt_le_sqrt (_hsup x)
  have hA_bound : ∀ x, (ζ : M → ℝ) x * |dw x| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * A * F x := by
    intro x
    have hcA : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) *
        Real.sqrt (c x) :=
      rawConnLap_innerWith_sqrt_finrank_bound_rs (I := I) (M := M) g r m w x
    have hsqc_nonneg : (0 : ℝ) ≤ Real.sqrt (c x) := Real.sqrt_nonneg _
    have hkey : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * Real.sqrt (c x) := by
      calc |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
              Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) *
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
  have hcrossL_int_bound_neg :
      -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ) ≤
        2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := by
    calc -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ)
        ≤ |∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ∂μ :=
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
  rw [show (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (gw.toSection x))
          ^ ((k : ℝ) / 1) ∂μ) = ∫ x, (b x) ^ ((k : ℝ) / 1) ∂μ from rfl, hLHS_eq]
  have hζb_eq : (∫ x, (ζ : M → ℝ) x * b x ∂μ) =
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ) := by
    have := hmaster; linarith [this]
  rw [hζb_eq]
  have hRHS_eq : (∫ x, (b x) ^ ((k : ℝ) - 1) *
        (c x) ^ (1 / 2 : ℝ) ∂μ) = ∫ x, F x ∂μ := rfl
  calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
          (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ)
      ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * (∫ x, F x ∂μ) +
          2 * ((k : ℝ) - 1) * A * (∫ x, F x ∂μ) := by
        have h1 := hLap_int_bound
        have h2 := hcrossL_int_bound_neg
        linarith [h1, h2]
    _ = (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A * (∫ x, F x ∂μ) := by ring
    _ = (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A *
          ∫ x, (b x) ^ ((k : ℝ) - 1) * (c x) ^ (1 / 2 : ℝ) ∂μ := by rw [hRHS_eq]

set_option maxHeartbeats 2000000 in

private theorem weightedCovIBP_lpFiberJet_fin_regIneq_rs
    (g : SmoothRiemannianMetric I M) (k m i r : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g r m) (ε : ℝ) (_hε : 0 < ε) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
            ((covGrad (I := I) (M := M) g r m w).toSection x)) *
          ((riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
            ((covGrad (I := I) (M := M) g r m w).toSection x)) + ε) ^ ((k : ℝ) / (i + 1) - 1)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) + ε) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g r (m + 1)
                (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ)
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

  set gw : Integral.L2.SmoothCcTensor g r (m + 1) := covGrad (I := I) (M := M) g r m w with hgw
  set ggw : Integral.L2.SmoothCcTensor g r (m + 1 + 1) :=
    covGrad (I := I) (M := M) g r (m + 1) gw with hggw
  set Lw : Integral.L2.SmoothCcTensor g r m :=
    rawTensorConnLapSmooth (I := I) g r m w with hLw

  set a : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g r m y (w.toSection y) with ha
  set b : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g r (m + 1) y (gw.toSection y)
    with hb
  set c : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) y (ggw.toSection y) with hc
  have ha_nonneg : ∀ y, 0 ≤ a y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r m y (w.toSection y)
  have hb_nonneg : ∀ y, 0 ≤ b y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) y (gw.toSection y)
  have hc_nonneg : ∀ y, 0 ≤ c y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) y (ggw.toSection y)

  have hb_eq_scalar : b = Integral.Connection.tensorInnerScalar (I := I) (M := M) g r (m + 1)
      gw.toSection gw.toSection := by
    funext y
    simp only [hb, Integral.Connection.tensorInnerScalar_apply]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) y
      (gw.toSection y)]
  have hb_smooth : ContMDiff I 𝓘(ℝ) ∞ b := by
    rw [hb_eq_scalar]
    exact Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g r (m + 1)
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

  set v : Integral.L2.SmoothCcTensor g r m :=
    scalarSmul (I := I) (M := M) g r m ζ w with hv

  have hdiag : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w w x = b x := by
    intro x
    rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad (I := I) (M := M) g r m w w x,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
        ((covGrad (I := I) (M := M) g r m w).toSection x)]

  have hsplit : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x =
      (ζ : M → ℝ) x * b x + tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x := by
    intro x
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def, ← hdiag,
      tensorCovDerivPointwiseInner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv, tensorCovDerivAt_scalarSmul (I := I) (M := M) g r m ζ w x
      ((Integral.Measure.chartModelBasis E) j)]
    have hwx : Tensor0SBundle.TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
    simp only [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_smul,
      hwx, Integral.L2.tensorInnerPointwise_add_right, Integral.L2.tensorInnerPointwise_smul_right]
    ring

  have hpull : ∀ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Lw.toFun x) (v.toFun x) =
      (ζ : M → ℝ) x * Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Lw.toFun x) (w.toFun x) := by
    intro x
    rw [hv, scalarSmul_toFun_apply, Integral.L2.tensorInnerPointwise_smul_right]

  have hcentral : ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x ∂μ =
      - ∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
          (Lw.toFun x) (v.toFun x) ∂μ := by
    have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
      (I := I) (M := M) g r m w v
    have hdir := tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g r m w v
    rw [hdir] at hgreen
    rw [hgreen, Integral.L2.tensorL2Inner, hLw]

  have hb_cont : Continuous b := hb_smooth.continuous
  have ha_cont : Continuous a := continuous_riemannianFiberNormSq_section (I := I) (M := M) g r m w
  have hc_cont : Continuous c := continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1 + 1) ggw
  have hbε_cont : Continuous bε := hbε_smooth.continuous
  have hζ_cont : Continuous (ζ : M → ℝ) := by
    rw [hζ_apply]; exact hbε_cont.rpow_const (fun y => Or.inl (hbε_ne y))
  have htcdpi_cont : Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g r m w v
  have hζb_cont : Continuous (fun x => (ζ : M → ℝ) x * b x) := hζ_cont.mul hb_cont
  have hcrossL_cont : Continuous (tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w) := by
    have heq : tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w =
        fun x => tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x -
          (ζ : M → ℝ) x * b x := by
      funext x; rw [hsplit x]; ring
    rw [heq]; exact htcdpi_cont.sub hζb_cont

  set dw : M → ℝ := fun x => Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
    (Lw.toFun x) (w.toFun x) with hdw
  have hdw_eq : dw = Integral.Connection.tensorInnerScalar (I := I) (M := M) g r m
      Lw.toSection w.toSection := by
    funext x
    simp only [hdw, Integral.Connection.tensorInnerScalar_apply]
    rfl
  have hdw_cont : Continuous dw := by
    rw [hdw_eq]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g r m
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

  have hLHS_split : (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r m w v x ∂μ) =
      (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
        ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ := by
    rw [← MeasureTheory.integral_add (hint _ hζb_cont) (hint _ hcrossL_cont)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hRHS_pull : (∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g r m x
        (Lw.toFun x) (v.toFun x) ∂μ) = ∫ x, (ζ : M → ℝ) x * dw x ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpull)
  have hmaster : (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ) =
      - ∫ x, (ζ : M → ℝ) x * dw x ∂μ := by
    rw [← hLHS_split, ← hRHS_pull]; exact hcentral

  have hcrossB : ∀ x, |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ≤
      2 * pm1 * F x := by
    intro x

    set Q : Integral.L2.SmoothCcTensor g r (m + 1) := covGrad (I := I) (M := M) g r m w with hQ_def
    set bfun : M → ℝ := fun y =>
      riemannianFiberNormSq (I := I) (M := M) g r (m + 1) y (Q.toSection y) with hbfun_def
    set bv : ℝ := bfun x with hbv_def
    set cv : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
        ((covGrad (I := I) (M := M) g r (m + 1) Q).toSection x) with hcv_def
    set av : ℝ := riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) with hav_def
    have hbv_nn : 0 ≤ bv := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x (Q.toSection x)
    have hcv_nn : 0 ≤ cv := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) x _
    have hav_nn : 0 ≤ av := riemannianFiberNormSq_nonneg (I := I) (M := M) g r m x (w.toSection x)
    have hbεx_pos : 0 < bv + ε := by linarith

    have hFx : F x = av ^ (1 / 2 : ℝ) * (bv + ε) ^ pm1 * cv ^ (1 / 2 : ℝ) := rfl

    set P : Integral.L2.SmoothCcTensor g r (m + 1) :=
      prependCovGradSlot (I := I) (M := M) g r m ζ w with hP_def
    have hcross_eq : tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x =
        Integral.L2.tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) :=
      tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M) g r m ζ w w x
    set rP : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (P.toSection x) with hrP_def
    have hrP_nn : 0 ≤ rP := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x _
    have hCS2 : |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ≤
        Real.sqrt bv * Real.sqrt rP := by
      rw [hcross_eq]
      have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
      have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) = bv := by
        rw [show bv = riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (Q.toSection x) from rfl,
          riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) x (Q.toSection x)]
      have hPself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g r (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) = rP := by
        rw [show rP = riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (P.toSection x) from rfl,
          riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) x (P.toSection x)]
      rw [hQself, hPself] at hsq
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hbv_nn]
      exact Real.sqrt_le_sqrt hsq

    have hrP_eq : rP = (∑ a : Fin n,
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) * av :=
      prependCovGradSlot_fiberNormSq_frame_sum_rs (I := I) (M := M) g r m ζ w x

    have hbfun_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) bfun x := by
      have hb_eq_scalar : bfun = Integral.Connection.tensorInnerScalar (I := I) (M := M) g r (m + 1)
          Q.toSection Q.toSection := by
        funext y
        simp only [hbfun_def, Integral.Connection.tensorInnerScalar_apply]
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (m + 1) y
          (Q.toSection y)]
      rw [hb_eq_scalar]
      exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g r (m + 1)
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
      kato_mfderiv_riemannianFiberNormSq_frame_sum_le_rs (I := I) (M := M) g r (m + 1) Q x

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
      rawConnLap_innerWith_sqrt_finrank_bound_rs (I := I) (M := M) g r m w x
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
      -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ) ≤
        2 * pm1 * ∫ x, F x ∂μ := by
    calc -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ)
        ≤ |∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x| ∂μ :=
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
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ) := by
    have := hmaster; linarith [this]

  have hassembled : (∫ x, (ζ : M → ℝ) x * b x ∂μ) ≤
      (2 * pm1 + Real.sqrt (Module.finrank ℝ E : ℝ)) * ∫ x, F x ∂μ := by
    rw [hζb_eq]
    calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
            (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r m ζ w w x ∂μ)
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
private theorem weightedCovIBP_lpFiberJet_fin_regLimit_rs
    (g : SmoothRiemannianMetric I M) (k m i r : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g r m) :
    Filter.Tendsto
        (fun n : ℕ => ∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) *
            ((riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))
        Filter.atTop
        (𝓝 (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / (i + 1))
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))) ∧
      Filter.Tendsto
        (fun n : ℕ => ∫ x, (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x))
              ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g r (m + 1)
                (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))
        Filter.atTop
        (𝓝 (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g r (m + 1)
                (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ)
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

  set a : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) with ha
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
    ((covGrad (I := I) (M := M) g r m w).toSection x) with hb
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w)).toSection x)
    with hc
  have ha0 : ∀ x, 0 ≤ a x := fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g r m x _
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) x _
  have hac : Continuous a := continuous_riemannianFiberNormSq_section (I := I) (M := M) g r m w
  have hbc : Continuous b :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w)
  have hcc : Continuous c :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1 + 1)
      (covGrad (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w))

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

theorem weightedCovIBP_lpFiberJet_fin_rs
    (g : SmoothRiemannianMetric I M) (k m i r : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g r m) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
            ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / (i + 1))
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g r (m + 1)
                (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by

  set D' : ℝ := 2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD'
  obtain ⟨hLlim, hRlim⟩ :=
    weightedCovIBP_lpFiberJet_fin_regLimit_rs (I := I) (M := M) g k m i r _hk _hi _hik w

  have hreg : ∀ n : ℕ, (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) *
            ((riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
        D' * ∫ x, (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g r (m + 1)
                (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
    intro n
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact weightedCovIBP_lpFiberJet_fin_regIneq_rs (I := I) (M := M) g k m i r _hk _hi _hik w
      (1 / ((n : ℝ) + 1)) hεpos

  exact le_of_tendsto_of_tendsto' hLlim (hRlim.const_mul D') hreg

end GeneralValenceRS

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
