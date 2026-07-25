import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Geometry.Connection.LeviCivita.CorrectionContraction
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricKoszul
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false











noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

set_option synthInstance.maxHeartbeats 800000 in
omit [FiniteDimensional Real E] in
private theorem fderiv_eval2
    {B : E → E →L[Real] E →L[Real] Real} {z : E}
    (hB : DifferentiableAt Real B z) (u v w : E) :
    fderiv Real (fun y ↦ B y w u) z v = fderiv Real B z v w u := by
  have hw : HasFDerivAt (fun _ : E ↦ w) 0 z :=
    hasFDerivAt_const (𝕜 := Real) w z
  have hu : HasFDerivAt (fun _ : E ↦ u) 0 z :=
    hasFDerivAt_const (𝕜 := Real) u z
  have hfirst := hB.hasFDerivAt.clm_apply hw
  have hsecond := hfirst.clm_apply hu
  have hfd := hsecond.fderiv
  have happ := DFunLike.congr_fun hfd v
  simpa using happ

omit [FiniteDimensional Real E] in
private theorem dir_const_eval2
    {B : E → E →L[Real] E →L[Real] Real} {z : E}
    (hB : DifferentiableAt Real B z) (u v w : E) :
    directionalDerivAlong (I := 𝓘(Real, E)) (fun _ : E ↦ v)
        (fun y ↦ B y w u) z =
      fderiv Real B z v w u := by
  unfold directionalDerivAlong
  rw [extDerivFun_real_eq_mfderiv, mfderiv_eq_fderiv]
  exact fderiv_eval2 hB u v w

omit [FiniteDimensional Real E] in
private theorem bracket_const_eq_zero (z v w : E) :
    VectorField.mlieBracket 𝓘(Real, E)
        (fun _ : E ↦ v) (fun _ : E ↦ w) z = 0 := by
  rw [← VectorField.mlieBracketWithin_univ]
  rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
  simp [VectorField.lieBracketWithin]
  rfl

omit [FiniteDimensional Real E] in
private theorem tangentConst_model (z v : E) :
    (tangentConstAt (I := 𝓘(Real, E)) z v : E → E) =
      fun _ : E ↦ v := by
  funext y
  unfold tangentConstAt TensorLieDeriv.tangentConstInChart
  simp
  rfl



theorem const_flat_eq_koszul
    (g : Measure.SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real)
    (hB : ∀ y : E, g.inner y = B y) {z : E}
    (hBdiff : DifferentiableAt Real B z) (v w : E) :
    B z
        ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
          (fun _ : E ↦ w) z) v) =
      MetricKoszul.koszulCov (fderiv Real B z) v w := by
  apply ContinuousLinearMap.ext
  intro u
  have hv := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z v
  have hw := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z w
  have hu := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z u
  have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := 𝓘(Real, E)) g
      (tangentConstAt (I := 𝓘(Real, E)) z v)
      (tangentConstAt (I := 𝓘(Real, E)) z w)
      (tangentConstAt (I := 𝓘(Real, E)) z u) z hv hw hu
  rw [tangentConst_model z v, tangentConst_model z w,
    tangentConst_model z u] at hKos
  have hwu : (fun y : E ↦ g.inner y w u) = fun y ↦ B y w u := by
    funext y
    exact congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L w u) (hB y)
  have huv : (fun y : E ↦ g.inner y u v) = fun y ↦ B y v u := by
    funext y
    calc
      g.inner y u v = g.inner y v u := g.symm y u v
      _ = B y v u :=
        congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v u) (hB y)
  have hvw : (fun y : E ↦ g.inner y v w) = fun y ↦ B y v w := by
    funext y
    exact congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v w) (hB y)
  rw [hB z] at hKos
  unfold koszulScalar at hKos
  rw [hwu, huv, hvw, bracket_const_eq_zero, bracket_const_eq_zero,
    bracket_const_eq_zero] at hKos
  simp only [map_zero, sub_zero, add_zero] at hKos
  rw [dir_const_eval2 hBdiff u v w, dir_const_eval2 hBdiff u w v,
    dir_const_eval2 hBdiff w u v] at hKos
  rw [MetricKoszul.koszulCov_apply]
  exact hKos



theorem const_flat_eq_nhds
    (g : Measure.SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real) {z : E}
    (hB : (fun y : E ↦ g.inner y) =ᶠ[nhds z] B)
    (hBdiff : DifferentiableAt Real B z) (v w : E) :
    B z
        ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
          (fun _ : E ↦ w) z) v) =
      MetricKoszul.koszulCov (fderiv Real B z) v w := by
  apply ContinuousLinearMap.ext
  intro u
  have hv := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z v
  have hw := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z w
  have hu := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z u
  have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := 𝓘(Real, E)) g
      (tangentConstAt (I := 𝓘(Real, E)) z v)
      (tangentConstAt (I := 𝓘(Real, E)) z w)
      (tangentConstAt (I := 𝓘(Real, E)) z u) z hv hw hu
  rw [tangentConst_model z v, tangentConst_model z w,
    tangentConst_model z u] at hKos
  have hwu : (fun y : E ↦ g.inner y w u) =ᶠ[nhds z] fun y ↦ B y w u := by
    filter_upwards [hB] with y hy
    exact congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L w u) hy
  have huv : (fun y : E ↦ g.inner y u v) =ᶠ[nhds z] fun y ↦ B y v u := by
    filter_upwards [hB] with y hy
    calc
      g.inner y u v = g.inner y v u := g.symm y u v
      _ = B y v u :=
        congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v u) hy
  have hvw : (fun y : E ↦ g.inner y v w) =ᶠ[nhds z] fun y ↦ B y v w := by
    filter_upwards [hB] with y hy
    exact congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v w) hy
  have hdir_wu :
      directionalDerivAlong (I := 𝓘(Real, E)) (fun _ : E ↦ v)
          (fun y ↦ g.inner y w u) z =
        fderiv Real B z v w u := by
    unfold directionalDerivAlong
    rw [extDerivFun_real_eq_mfderiv, mfderiv_eq_fderiv, hwu.fderiv_eq]
    exact fderiv_eval2 hBdiff u v w
  have hdir_uv :
      directionalDerivAlong (I := 𝓘(Real, E)) (fun _ : E ↦ w)
          (fun y ↦ g.inner y u v) z =
        fderiv Real B z w v u := by
    unfold directionalDerivAlong
    rw [extDerivFun_real_eq_mfderiv, mfderiv_eq_fderiv, huv.fderiv_eq]
    exact fderiv_eval2 hBdiff u w v
  have hdir_vw :
      directionalDerivAlong (I := 𝓘(Real, E)) (fun _ : E ↦ u)
          (fun y ↦ g.inner y v w) z =
        fderiv Real B z u v w := by
    unfold directionalDerivAlong
    rw [extDerivFun_real_eq_mfderiv, mfderiv_eq_fderiv, hvw.fderiv_eq]
    exact fderiv_eval2 hBdiff w u v
  rw [hB.eq_of_nhds] at hKos
  unfold koszulScalar at hKos
  rw [bracket_const_eq_zero, bracket_const_eq_zero,
    bracket_const_eq_zero] at hKos
  simp only [map_zero, sub_zero, add_zero] at hKos
  rw [hdir_wu, hdir_uv, hdir_vw] at hKos
  rw [MetricKoszul.koszulCov_apply]
  exact hKos



theorem const_cov_eq_koszul
    (g : Measure.SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real)
    (hB : ∀ y : E, g.inner y = B y) {z : E}
    (hBdiff : DifferentiableAt Real B z)
    (hco : IsCoercive (B z)) (v w : E) :
    (leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
        (fun _ : E ↦ w) z) v =
      MetricKoszul.koszulVec hco (fderiv Real B z) v w := by
  calc
    (leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
        (fun _ : E ↦ w) z) v =
        hco.sharp (B z
          ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
            (fun _ : E ↦ w) z) v)) :=
      (hco.sharp_apply _).symm
    _ = hco.sharp (MetricKoszul.koszulCov (fderiv Real B z) v w) := by
      rw [const_flat_eq_koszul g B hB hBdiff v w]
    _ = MetricKoszul.koszulVec hco (fderiv Real B z) v w := rfl



theorem const_cov_eq_nhds
    (g : Measure.SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real) {z : E}
    (hB : (fun y : E ↦ g.inner y) =ᶠ[nhds z] B)
    (hBdiff : DifferentiableAt Real B z)
    (hco : IsCoercive (B z)) (v w : E) :
    (leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
        (fun _ : E ↦ w) z) v =
      MetricKoszul.koszulVec hco (fderiv Real B z) v w := by
  calc
    (leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
        (fun _ : E ↦ w) z) v =
        hco.sharp (B z
          ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
            (fun _ : E ↦ w) z) v)) :=
      (hco.sharp_apply _).symm
    _ = hco.sharp (MetricKoszul.koszulCov (fderiv Real B z) v w) := by
      rw [const_flat_eq_nhds g B hB hBdiff v w]
    _ = MetricKoszul.koszulVec hco (fderiv Real B z) v w := rfl




theorem cov_eq_fderiv_add
    [NeZero (Module.finrank Real E)]
    (g : Measure.SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real) {z : E}
    (hB : (fun y : E ↦ g.inner y) =ᶠ[nhds z] B)
    (hBdiff : DifferentiableAt Real B z)
    (hco : IsCoercive (B z)) (V : E → E)
    (hV : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E))
      (fun y : E ↦ (⟨y, V y⟩ : TangentBundle 𝓘(Real, E) E)) z)
    (v : E) :
    (leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g V z) v =
      fderiv Real V z v +
        MetricKoszul.koszulVec hco (fderiv Real B z) v (V z) := by
  have hzgood : z ∈ chartLeviCivitaGoodSet (I := 𝓘(Real, E)) z :=
    self_mem_chartLeviCivitaGoodSet (I := 𝓘(Real, E)) (α := z)
  have hrepr :
      chartE_section_repr (I := 𝓘(Real, E)) z V = V := by
    funext y
    rw [chartE_section_repr_eq_trivToE]
    change (trivializationAt E (TangentSpace 𝓘(Real, E)) z).continuousLinearMapAt
      Real y (V y) = V y
    rw [TangentBundle.continuousLinearMapAt_model_space]
    rfl
  have hcorr :
      Geometry.Riemannian.Geodesic.chartChristoffelContraction
          (I := 𝓘(Real, E)) g z v (V z) z =
        MetricKoszul.koszulVec hco (fderiv Real B z) v (V z) := by
    rw [← const_cov_eq_contr g z z v (V z)]
    exact const_cov_eq_nhds g B hB hBdiff hco v (V z)
  change (LeviCivita (I := 𝓘(Real, E)) g).toFun V z v = _
  rw [LeviCivita_chart_apply (I := 𝓘(Real, E)) g z hzgood hV v]
  rw [chartLeviCivita_apply (I := 𝓘(Real, E)) g z V hzgood v]
  rw [hrepr]
  rw [show (V ∘ (extChartAt 𝓘(Real, E) z).symm) = V by rfl]
  rw [correction_eq_contr]
  simp only [trivFromE, trivToE, TangentBundle.symmL_model_space,
    TangentBundle.continuousLinearMapAt_model_space,
    extChartAt_self_apply, modelWithCornersSelf_coe, id_eq]
  exact congrArg (fun w ↦ fderiv Real V z v + w) hcorr

end Connection
end Integral
end DifferentialGeometry
