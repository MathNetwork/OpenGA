import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.WeylEigenvalueCountingBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.BareLaplacianSpectralMatch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
























private noncomputable def eigenRealizeEval (g_bg : SmoothRiemannianMetric I M)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g_bg 0 2)
    (x : M) (v w : TangentSpace I x) : ℝ :=
  ccTensorBilinSymm (I := I) g_bg (eigenSmooth (I := I) (M := M) g_bg i) x v w














private theorem eigenRealizeEval_weight_summable
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (x : M) (v w : TangentSpace I x) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g_bg 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
        (eigenRealizeEval (I := I) (M := M) g_bg i x v w *
          (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) ^ 2) :=
  ((weyl_pointwise_diagonalKernel_bound_of_closed (I := I) (M := M) g_bg 0 2).2 a ha).1 x v w















private theorem ccTensorBilinSymm_hasSum_eigenRealizeEval
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (T : Integral.L2.SmoothCcTensor g_bg 0 2)
    (x : M) (v w : TangentSpace I x) :
    HasSum
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2 =>
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 T) i *
          eigenRealizeEval (I := I) (M := M) g_bg i x v w)
      (ccTensorBilinSymm (I := I) g_bg T x v w) :=
  ((weyl_pointwise_diagonalKernel_bound_of_closed (I := I) (M := M) g_bg 0 2).2 a ha).2 T x v w

set_option linter.unusedVariables false in
theorem realize_eval_carrier_factorization
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (x : M) (v w : TangentSpace I x) :
    ∃ ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ,
      ∀ (T_z : Integral.L2.SmoothCcTensor g_bg 0 2)
        (z : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)),
        (∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g_bg 0 2,
          z.coeff i
            = tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
                (Integral.L2.SmoothCcTensor.toL2 T_z) i) →
          ℓ_a z = ccTensorBilinSymm (I := I) g_bg T_z x v w := by
  classical
  set e : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g_bg 0 2 → ℝ :=
    fun i => eigenRealizeEval (I := I) (M := M) g_bg i x v w with he_def
  set w_rep : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    { coeff := fun i => e i * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹
      weighted_summable :=
        eigenRealizeEval_weight_summable (I := I) (M := M) g_bg a ha x v w } with hw_rep_def
  refine ⟨innerSL ℝ w_rep, ?_⟩
  intro T_z z hz
  have hval : (innerSL ℝ w_rep) z = ∑' i, e i * z.coeff i := by
    rw [innerSL_apply_apply, tensorHs.inner_def]
    refine tsum_congr (fun i => ?_)
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
      tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
    have hwcoeff : w_rep.coeff i
        = e i * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ := rfl
    rw [hwcoeff,
      show tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
          ((e i * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) * z.coeff i)
        = (tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) * (e i * z.coeff i) by ring,
      mul_inv_cancel₀ hw_pos.ne', one_mul]
  rw [hval]
  have hcoeff : (fun i => e i * z.coeff i)
      = (fun i => tensorL2Coeff (I := I) (M := M)
            (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 T_z) i * e i) := by
    funext i; rw [hz i]; ring
  rw [hcoeff]
  exact (ccTensorBilinSymm_hasSum_eigenRealizeEval
    (I := I) (M := M) g_bg a ha T_z x v w).tsum_eq

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem pointwise_deriv_through_realize
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (u_car : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (u_car' : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (x : M) (v w : TangentSpace I x)
    (ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ)
    (hreal : ∀ s : ℝ,
      (g_DT s).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s s) x v w)
    (hfactor : ∀ s : ℝ,
      ccTensorBilinSymm (I := I) g_bg (T_s s) x v w = ℓ_a (u_car s))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => u_car s) (u_car' t) (Set.Ici 0) t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT s).inner x v w)
        (ℓ_a (u_car' t)) (Set.Ici 0) t := by
  intro t ht
  have hval : ∀ s : ℝ,
      (g_DT s).inner x v w = g_bg.inner x v w + ℓ_a (u_car s) := by
    intro s
    rw [hreal s, hfactor s]
  have hℓderiv :
      HasDerivWithinAt (fun s : ℝ => ℓ_a (u_car s)) (ℓ_a (u_car' t))
        (Set.Ici 0) t :=
    ℓ_a.hasFDerivAt.comp_hasDerivWithinAt t (hderiv t ht)
  refine (hℓderiv.const_add (g_bg.inner x v w)).congr (fun s _ => ?_) ?_
  · exact hval s
  · exact hval t

set_option linter.unusedVariables false in



























theorem rhs_matches_deturck_at_solution
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (x : M) (v w : TangentSpace I x)
    (hreal : ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
      (g_DT s).inner x' v' w'
        = g_bg.inner x' v' w' + ccTensorBilinSymm (I := I) g_bg (T_s s) x' v' w')
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
          (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x' v' w' =
        ccTensorBilinSymm (I := I) g_bg (repr u) x' v' w')
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        metricCauchySchwarzBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hsmoothrepr : ∀ (s : ℝ)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g_bg 0 2),
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hℓ : ∀ (T_z : Integral.L2.SmoothCcTensor g_bg 0 2)
        (z : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)),
        (∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g_bg 0 2,
          z.coeff i
            = tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
                (Integral.L2.SmoothCcTensor.toL2 T_z) i) →
          ℓ_a z = ccTensorBilinSymm (I := I) g_bg T_z x v w)
    (hNsec_geom : ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g_bg
          (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g_bg
            (repr (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      ℓ_a (scaleLaplacianFun (I := I) (M := M) (u₂ t) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ t)))
        = deTurckRicciRHS (I := I) g_bg (g_DT t) x v w := by
  intro t _ht
  set uincl := tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ t) with huincl
  have hcoeff_lap : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g_bg 0 2,
      (scaleLaplacianFun (I := I) (M := M) (u₂ t)).coeff i =
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
          (Integral.L2.SmoothCcTensor.toL2
            (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s t))) i := by
    intro i
    rw [scaleLaplacianFun_coeff,
      bare_laplacian_spectral_match (I := I) (M := M) g_bg (T_s t) i,
      hsmoothrepr t i]
  have hlap : ℓ_a (scaleLaplacianFun (I := I) (M := M) (u₂ t)) =
      ccTensorBilinSymm (I := I) g_bg
        (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s t)) x v w :=
    hℓ (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s t))
      (scaleLaplacianFun (I := I) (M := M) (u₂ t)) hcoeff_lap
  have hcoeff_N : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g_bg 0 2,
      (N_cont uincl).coeff i =
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
          (Integral.L2.SmoothCcTensor.toL2 (Nsec uincl)) i := fun i => hN_coeff uincl i
  have hN : ℓ_a (N_cont uincl) =
      ccTensorBilinSymm (I := I) g_bg (repr uincl) x v w := by
    rw [hℓ (Nsec uincl) (N_cont uincl) hcoeff_N, hNsec_realize uincl x v w]
  rw [map_add, hlap, hN]
  exact hNsec_geom t x v w

end DifferentialGeometry.PDE.RicciFlow
