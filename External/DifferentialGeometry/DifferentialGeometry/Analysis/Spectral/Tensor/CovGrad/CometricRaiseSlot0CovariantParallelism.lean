import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCometricRaise
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentCovDerivIdentification


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
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interior_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interior_product_eq_tensor0S_curry (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) :
    Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) s x D v := by
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  rw [interior_toModel_eval (I := I) (M := M) s x v D (fun k => w k)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := D) (v0 := (show E from v)) (vs := fun k => (show E from w k))]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDeriv_one_eq_dualToCotangent_cotangentCov
    (g₀ : SmoothRiemannianMetric I M)
    (w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞ (fun y : M => Tensor0SSpace 1 I y))
    (x : M) (v0 : TangentSpace I x) :
    Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
        (fun y : M => w y) x v0 =
      dualToCotangent (I := I)
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b : M => cotangentToCLM (I := I) (w b)) x v0) := by
  classical
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro u
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent]
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x u
  have hDmd : TensorSectionMDiffAt (I := I) 1 (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  have hbridge := tensor0SCovariantDerivative_one_cotangentToCLM
    (I := I) g₀ (fun y : M => w y) hDmd Y v0
  have hθmd : MDiffAtCotangent (I := I) (fun b : M => cotangentToCLM (I := I) (w b)) x := by
    have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M => TangentSpace I z →L[ℝ] ℝ) b
          (cotangentToCLM (I := I) (w b))) :=
      cotangentToCLMField_contMDiff (I := I) w
    exact (h1 x).mdifferentiableAt (by norm_num)
  have hYmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g₀)
    (θ := fun b : M => cotangentToCLM (I := I) (w b)) hθmd (Y := fun b : M => Y b) hYmd v0
  rw [show cotangentToDual (I := I)
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => w y) x v0) u
      = cotangentToCLM (I := I)
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => w y) x v0) u from rfl]
  rw [← hYx]
  rw [hbridge, hpair]
  simp only [add_sub_cancel_right, ContinuousLinearMap.coe_coe]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDeriv_sharp_field_eq (g₀ : SmoothRiemannianMetric I M)
    (w : ContMDiffSection I (Tensor0SModel 1 ℝ E) ∞ (fun y : M => Tensor0SSpace 1 I y))
    {x : M} (v0 : TangentSpace I x)
    (hsharp : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (inverseMetricSharpFib (I := I) g₀ y (w y))) x) :
    (LeviCivita (I := I) g₀).toFun
        (fun y : M => inverseMetricSharpFib (I := I) g₀ y (w y)) x v0 =
      inverseMetricSharpFib (I := I) g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => w y) x v0) := by
  rw [inverseMetricSharpField_covGrad_eq_zero (I := I) g₀ (fun y : M => w y) hsharp v0]
  rw [covDeriv_one_eq_dualToCotangent_cotangentCov (I := I) (M := M) g₀ w x v0]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_cometricRaiseSlot0Field_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g₀ 1 (s + 1)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S) x v =
      cometricRaiseSlot0Fib (I := I) g₀ s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 2) S x v)
          (unitTensor (I := I) (M := M) x)) := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) (n := (⊤ : ℕ∞)) x D
  set Wsec : Π y : M, Tensor0SSpace (s + 2) I y :=
    fun y => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 2) I y from S.toSection y)
      (unitTensor (I := I) (M := M) y) with hWsec
  have hYsharp_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (inverseMetricSharpFib (I := I) g₀ y (w y))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₀) w.contMDiff
  set Ysharp : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y => inverseMetricSharpFib (I := I) g₀ y (w y), hYsharp_smooth⟩ with hYsharp_def
  have hYsharp_app : ∀ y : M, Ysharp y = inverseMetricSharpFib (I := I) g₀ y (w y) :=
    fun _ => rfl
  have hraiseToSection : ∀ y : M,
      (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection y) =
        cometricRaiseSlot0Fib (I := I) g₀ s y (Wsec y) := fun y =>
    cometricRaiseSlot0Field_toSection (I := I) (M := M) g₀ s S y
  have hWsec_at : TensorSectionMDiffAt (I := I) (s + 2) Wsec x :=
    (contMDiff_unitEvalSection (I := I) (M := M) g₀ (s + 2) S x).mdifferentiableAt (by norm_num)
  have hDderiv : Tensor0SNabla.tensor0SCovariantDerivative I M (s + 2)
      (LeviCivita (I := I) g₀) Wsec x v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 2) S x v)
        (unitTensor (I := I) (M := M) x) := by
    rw [tensorCovDerivAt_def]
    exact (tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g₀ (s + 2)
      S.toSection x v).symm
  rw [← hw]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x _ (w x)]
  rw [interior_product_eq_tensor0S_curry (I := I) (M := M) (s + 1) x
    (inverseMetricSharpFib (I := I) g₀ x (w x)) _]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 1 (s + 1)
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S) x v]
  have hHL := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) 1 (s + 1)
    (LeviCivita (I := I) g₀) (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection w x v
  rw [hHL]
  have hfun : (fun y : M => (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection y) (w y)) =
      (fun y : M => Tensor0SNabla.curriedSection I M Wsec y (Ysharp y)) := by
    funext y
    rw [hraiseToSection y]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s y (Wsec y) (w y)]
    rw [interior_product_eq_tensor0S_curry (I := I) (M := M) (s + 1) y
      (inverseMetricSharpFib (I := I) g₀ y (w y)) (Wsec y)]
    rw [Tensor0SNabla.curriedSection_apply, hYsharp_app y]
  have hτD : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x)
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => w y) x v) =
      Tensor0SNabla.curriedSection I M Wsec x
        (inverseMetricSharpFib (I := I) g₀ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => w y) x v)) := by
    rw [hraiseToSection x]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x (Wsec x)
      (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
        (fun y : M => w y) x v)]
    rw [interior_product_eq_tensor0S_curry (I := I) (M := M) (s + 1) x
      (inverseMetricSharpFib (I := I) g₀ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
          (fun y : M => w y) x v)) (Wsec x)]
    rw [Tensor0SNabla.curriedSection_apply]
  rw [hfun]
  rw [tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g₀ (s + 1)
    Wsec hWsec_at Ysharp v]
  rw [hτD]
  rw [show (fun y : M => Ysharp y) =
      (fun y : M => inverseMetricSharpFib (I := I) g₀ y (w y)) from funext hYsharp_app]
  rw [covDeriv_sharp_field_eq (I := I) (M := M) g₀ w v
    (hYsharp_smooth.contMDiffAt.mdifferentiableAt (by simp))]
  rw [add_sub_cancel_right, hDderiv, hYsharp_app x]

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_cometricRaiseSlot0Field_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) :
    covGrad (I := I) (M := M) g₀ 1 (s + 1) (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ (s + 1)
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin (s + 2 + 1)) 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + 2) S)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  set W' : SmoothCcTensor g₀ 0 (s + 2 + 1) :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin (s + 2 + 1)) 1)
      (covGrad (I := I) (M := M) g₀ 0 (s + 2) S) with hW'
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 (s + 1)
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S) x D m]
  rw [tensorCovDerivAt_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ s S x (m 0)]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 2) S x (m 0))
      (unitTensor (I := I) (M := M) x)) D]
  rw [interior_toModel_eval (I := I) (M := M) (s + 1) x (inverseMetricSharpFib (I := I) g₀ x D)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 2) S x (m 0))
      (unitTensor (I := I) (M := M) x)) (Matrix.vecTail m)]
  rw [cometricRaiseSlot0Field_toSection (I := I) (M := M) g₀ (s + 1) W' x]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ (s + 1) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2 + 1) I x from W'.toSection x)
      (unitTensor (I := I) (M := M) x)) D]
  rw [interior_toModel_eval (I := I) (M := M) (s + 2) x (inverseMetricSharpFib (I := I) g₀ x D)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2 + 1) I x from W'.toSection x)
      (unitTensor (I := I) (M := M) x)) m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2 + 1) I x from W'.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ (s + 2 + 1) W' x from rfl]
  rw [hW', domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin (s + 2 + 1)) 1)
    (covGrad (I := I) (M := M) g₀ 0 (s + 2) S) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show unitModel (I := I) (M := M) g₀ (s + 2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 (s + 2) S) x =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2 + 1) I x from
            (covGrad (I := I) (M := M) g₀ 0 (s + 2) S).toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  have harg : (fun i : Fin (s + 2 + 1) =>
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x D)
            (fun k => (show E from m k)) : Fin (s + 2 + 1) → E)
          ((Equiv.swap (0 : Fin (s + 2 + 1)) 1) i)) =
      Fin.cons (show E from m 0)
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x D)
          (fun k => (show E from (Matrix.vecTail m) k))) := by
    have h1eq : (1 : Fin (s + 2 + 1)) = Fin.succ (0 : Fin (s + 2)) := by
      apply Fin.ext
      simp
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Equiv.swap_apply_left, h1eq, Fin.cons_succ, Fin.cons_zero]
    · refine Fin.cases ?_ (fun k => ?_) j
      · rw [h1eq]
        simp only [Equiv.swap_apply_right, Fin.cons_zero, Fin.cons_succ]
      · have hne0 : (Fin.succ (Fin.succ k) : Fin (s + 2 + 1)) ≠ 0 := Fin.succ_ne_zero _
        have hne1 : (Fin.succ (Fin.succ k) : Fin (s + 2 + 1)) ≠ 1 := by
          rw [h1eq]
          exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
        rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
        simp only [Fin.cons_succ, Matrix.vecTail, Function.comp_apply]
  rw [harg]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 (s + 2) S x
    (unitTensor (I := I) (M := M) x)
    (Fin.cons (show E from m 0)
      (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x D)
        (fun k => (show E from (Matrix.vecTail m) k))))]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
