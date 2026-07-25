import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciHessian
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Operator.CotangentSharpSmooth
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SBochnerProduct
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false










noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E


noncomputable def ricGradForm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  partialEval0SField (I := I) (metricRicci (I := I) (M := M) g)
    (grad_g (I := I) g hf)

omit [SigmaCompactSpace M] in
@[simp] theorem ricGradForm_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    ricGradForm (I := I) g hf x =
      tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
        (metricRicciAt (I := I) (M := M) g x) (grad_g (I := I) g hf x) := by
  simp [ricGradForm]


noncomputable def ricGradVec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
  ContMDiffSection.mk
    (fun x : M => cotangentSharp_gen (I := I) g x
      (ricGradForm (I := I) g hf x))
    (cotangentSharp_gen_contMDiff_total (I := I) g
      (fun a j => by
        simpa [Tensor0SSpace.toModel] using
          cotangentSection_chartComponent_contMDiffOn
            (I := I) (ricGradForm (I := I) g hf) a j))

omit [SigmaCompactSpace M] in
@[simp] theorem ricGradVec_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    ricGradVec (I := I) g hf x =
      cotangentSharp_gen (I := I) g x (ricGradForm (I := I) g hf x) :=
  rfl


noncomputable def ricDriftVec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
  ContMDiffSection.mk
    (fun x : M => ricGradVec (I := I) g hf x -
      ((1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x) •
        grad_g (I := I) g hf x)
    ((ricGradVec (I := I) g hf).contMDiff.sub_section
      ((contMDiff_const.mul (metricScalar_smooth (I := I) (M := M) g)).smul_section
        (grad_g (I := I) g hf).contMDiff))

omit [SigmaCompactSpace M] in
@[simp] theorem ricDriftVec_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    ricDriftVec (I := I) g hf x = ricGradVec (I := I) g hf x -
      ((1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x) •
        grad_g (I := I) g hf x :=
  rfl

private theorem div_ricGrad [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    divergence (I := I) (metricCov (I := I) (M := M) g)
        (fun y : M => ricGradVec (I := I) g hf y) x =
      (1 / 2 : Real) *
          extDerivFun (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x
            (grad_g (I := I) g hf x) +
        inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
          (hessianSec (I := I) (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g) f hf x) := by
  classical
  let cov := LeviCivita (I := I) g
  let hcov := metricCov_smooth (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let G := grad_g (I := I) g hf
  let beta := ricGradForm (I := I) g hf
  let hRicReg := totalNabla0S_reg (I := I) 2 cov hcov Ric
  let nRic := totalNabla0S (I := I) 2 cov Ric hRicReg
  let hBetaReg := totalNabla0S_reg (I := I) 1 cov hcov beta
  let nBeta := totalNabla0S (I := I) 1 cov beta hBetaReg
  have hRicReal : TotalNabla0SRealizes (I := I) 2 cov Ric nRic := by
    exact totalNabla0S_realizes (I := I) 2 cov Ric hRicReg
  have hBetaReal : TotalNabla0SRealizes (I := I) 1 cov beta nBeta := by
    exact totalNabla0S_realizes (I := I) 1 cov beta hBetaReg
  have hmc : IsMetricCompatible_gen (I := I) cov g := by
    simpa [cov, metricCov] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  let delta : Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real :=
    fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis_gen (I := I) g x basis delta :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let X : Fin (Module.finrank Real (TangentSpace I x)) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun i => (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (basis i)).choose
  have hX (i : Fin (Module.finrank Real (TangentSpace I x))) :
      X i x = basis i :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (basis i)).choose_spec
  have hsharp (i : Fin (Module.finrank Real (TangentSpace I x))) :
      cov (fun y : M => ricGradVec (I := I) g hf y) x (basis i) =
        cotangentSharp_gen (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
            (nBeta x) (basis i)) := by
    have h0 := cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
      (I := I) cov g hmc beta nBeta hBetaReal (X i) x
      ((ricGradVec (I := I) g hf).contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
    simpa only [ricGradVec_apply, hX] using h0
  have hcomp (i : Fin (Module.finrank Real (TangentSpace I x))) :
      g.inner x
          (cov (fun y : M => ricGradVec (I := I) g hf y) x (basis i))
          (basis i) =
        nRic x (vec3 (I := I) (basis i) (G x) (basis i)) +
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
    rw [hsharp i, cotangentSharp_inner_eval,
      tensor0S_curry_apply_cons]
    calc
      nBeta x (Fin.cons (basis i) (fun _ : Fin 1 => basis i)) =
          nabla0SFun (I := I) 1 cov (X i) beta x
            (fun _ : Fin 1 => basis i) := by
        simpa only [hX] using
          (TotalNabla0SRealizes.apply hBetaReal (X i) x
            (fun _ : Fin 1 => basis i))
      _ =
          (freezeFirstTwoArgs0S (I := I) (nRic x) (basis i) (G x) +
            tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x (Ric x)
              (cov (fun y : M => G y) x (basis i)))
            (fun _ : Fin 1 => basis i) := by
        rw [show beta = partialEval0SField (I := I) Ric G by rfl]
        rw [nabla_partialEval0S (I := I) cov Ric nRic hRicReal (X i) G x]
        rw [hX]
      _ =
          nRic x (vec3 (I := I) (basis i) (G x) (basis i)) +
            metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
        rw [Tensor0SSpace.add_apply, freezeFirstTwoArgs0S_apply,
          tensor0S_curry_one_apply]
        rw [metricTraceInput_one_eq_vec3]
        simp only [Ric, metricRicci_apply]
        rfl
  let nRic0 := totalNabla0SFun (I := I) 2 cov Ric x
  let dR := differential1FormFun (I := I)
    (fun y : M => metricScalarAt (I := I) (M := M) g y) x
  have hpack :
      ∃ nablaRm04 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 5 x,
        SecondBianchiAt (I := I) nablaRm04 ∧
          NablaRmSymmAt (I := I) nablaRm04 ∧
            NablaRicTraceAt (I := I) basis delta nablaRm04 nRic0 ∧
              DScalarTraceAt (I := I) basis delta nRic0 dR := by
    simpa [cov, Ric, nRic0, dR, metricCov, metricRicci, metricScalarAt] using
      (metricBianchiAt (I := I) (M := M) g basis delta hinv)
  obtain ⟨nablaRm04, hsecond, hRmSymm, hRicTrace, hScalar⟩ := hpack
  have hNablaSymm : NablaRicSymmAt (I := I) nRic0 := by
    simpa [nRic0, cov, Ric] using metricNablaSymm (I := I) (M := M) g x
  have hInv : ∀ i j, delta i j = delta j i := by
    intro i j
    simp [delta, eq_comm]
  have hcontract :
      ContractedBianchiOfSecondAt (I := I) basis delta nablaRm04 nRic0 dR :=
    contractOfSecond (I := I) basis delta nablaRm04 nRic0 dR
      hRmSymm hRicTrace hScalar hNablaSymm hInv
  have hBianchi : ContractedBianchiAt (I := I) basis delta nRic0 dR :=
    contracted_bianchi_of_second (I := I) basis delta nablaRm04 nRic0 dR
      hcontract hsecond
  have hRicPart :
      (∑ i, nRic x (vec3 (I := I) (basis i) (G x) (basis i))) =
        (1 / 2 : Real) *
          extDerivFun (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) := by
    calc
      (∑ i, nRic x (vec3 (I := I) (basis i) (G x) (basis i))) =
          ∑ i, nRic0 (vec3 (I := I) (basis i) (basis i) (G x)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show nRic x = nRic0 by rfl]
        exact hNablaSymm (basis i) (G x) (basis i)
      _ = (1 / 2 : Real) * dR (fun _ : Fin 1 => G x) := by
        simpa [delta] using hBianchi (G x)
      _ = (1 / 2 : Real) *
          extDerivFun (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) := by
        rw [differential1FormFun_apply_eq_extDerivFun]
  have hHessPart :
      (∑ i, metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i))) =
        inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
          (hessianSec (I := I) cov hcov f hf x) := by
    have htrace :
        LinearMap.trace Real (TangentSpace I x)
            ((cotangentSharpLinear_gen (I := I) g x).comp
              ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
                  (metricRicciAt (I := I) (M := M) g x)).toLinearMap.comp
                (cov (fun y : M => G y) x).toLinearMap)) =
          ∑ i, metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
      rw [trace_eq_ortho_sum (I := I) g x _ basis hON]
      apply Finset.sum_congr rfl
      intro i _
      simp only [LinearMap.comp_apply]
      change g.inner x
          (cotangentSharp_gen (I := I) g x
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
              (metricRicciAt (I := I) (M := M) g x)
              (cov (fun y : M => G y) x (basis i))))
          (basis i) = _
      rw [cotangentSharp_inner_eval, tensor0S_curry_one_apply]
      rfl
    rw [← htrace]
    simpa [cov, hcov, G] using
      (ricHess_eq_inner (I := I) cov hcov g hmc f hf x)
  rw [divergence_eq]
  rw [trace_eq_ortho_sum (I := I) g x _ basis hON]
  calc
    (∑ i, g.inner x
        (cov (fun y : M => ricGradVec (I := I) g hf y) x (basis i))
        (basis i)) =
        ∑ i, (nRic x (vec3 (I := I) (basis i) (G x) (basis i)) +
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hcomp i
    _ =
        (∑ i, nRic x (vec3 (I := I) (basis i) (G x) (basis i))) +
          ∑ i, metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
      rw [Finset.sum_add_distrib]
    _ =
        (1 / 2 : Real) *
            extDerivFun (I := I)
              (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) +
          inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
            (hessianSec (I := I) cov hcov f hf x) := by
      rw [hRicPart, hHessPart]
    _ = _ := by rfl



theorem ricDriftDiv [I.Boundaryless] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    divergence_g (I := I) g (ricDriftVec (I := I) g hf) x =
      inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
          (hessianSec (I := I) (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g) f hf x) -
        (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x *
          Δ_g (I := I) g hf x := by
  let cov := metricCov (I := I) (M := M) g
  let G := grad_g (I := I) g hf
  let RG := ricGradVec (I := I) g hf
  let a : M -> Real := fun y =>
    (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g y
  have ha : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) a := by
    exact contMDiff_const.mul (metricScalar_smooth (I := I) (M := M) g)
  have haMD : MDifferentiableAt I 𝓘(Real, Real) a x :=
    ha.contMDiffAt.mdifferentiableAt (by simp)
  have hbridge :
      divergence (I := I) cov (fun y : M => ricDriftVec (I := I) g hf y) x =
        divergence_g (I := I) g (ricDriftVec (I := I) g hf) x := by
    simpa only [cov] using
      (divergence_levi_eq (I := I) g (ricDriftVec (I := I) g hf) x)
  have hdivRG :
      divergence (I := I) cov (fun y : M => RG y) x =
        (1 / 2 : Real) *
            extDerivFun (I := I)
              (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) +
          inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
            (hessianSec (I := I) cov
              (metricCov_smooth (I := I) (M := M) g) f hf x) := by
    simpa only [cov, LeviCivita, metricCov, RG, G] using
      div_ricGrad (I := I) g hf x
  have hdivaG :
      divergence (I := I) cov (fun y : M => a y • G y) x =
        a x * divergence (I := I) cov (fun y : M => G y) x +
          extDerivFun (I := I) a x (G x) := by
    simpa only [Pi.smul_apply] using
      (divergence_smul (I := I) (X := fun y : M => G y) (x := x) cov inferInstance haMD
        (G.contMDiff.contMDiffAt.mdifferentiableAt (by simp)))
  have hLap :
      divergence (I := I) cov (fun y : M => G y) x = Δ_g (I := I) g hf x := by
    simpa only [cov, G, laplacian_eq, grad_g_apply] using
      (laplacian_levi_eq (I := I) g hf x)
  have hda :
      extDerivFun (I := I) a x (G x) =
        (1 / 2 : Real) *
          extDerivFun (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) := by
    exact extDerivFun_const_mul_apply (I := I) (1 / 2 : Real) (G x)
      ((metricScalar_smooth (I := I) (M := M) g).contMDiffAt.mdifferentiableAt
        (by simp))
  rw [← hbridge]
  change divergence (I := I) cov
      (fun y : M => RG y - a y • G y) x = _
  calc
    divergence (I := I) cov (fun y : M => RG y - a y • G y) x =
        divergence (I := I) cov (fun y : M => RG y) x -
          divergence (I := I) cov (fun y : M => a y • G y) x := by
      simpa only [Pi.sub_apply] using
        (divergence_sub (I := I)
          (X := fun y : M => RG y) (Y := fun y : M => a y • G y) (x := x) cov
          (RG.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          ((ha.smul_section G.contMDiff).contMDiffAt.mdifferentiableAt (by simp)))
    _ = _ := by
      rw [hdivRG, hdivaG, hLap, hda]
      dsimp only [a]
      ring



omit [SigmaCompactSpace M] in
theorem ricDriftAct [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    tangentSectionAction (I := I) (ricDriftVec (I := I) g hf) f x =
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (grad_g (I := I) g hf x)
            (grad_g (I := I) g hf x)) -
        (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x *
          g.inner x (grad_g (I := I) g hf x) (grad_g (I := I) g hf x) := by
  rw [tangentSectionAction_eq_inner_grad_g (I := I) g hf
    (ricDriftVec (I := I) g hf) x]
  simp only [ricDriftVec_apply, map_sub, map_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ricGradVec_apply, cotangentSharp_inner_eval, ricGradForm_apply,
    tensor0S_curry_one_apply, smul_eq_mul]
  rfl

end DifferentialGeometry.Integral.Connection

end
