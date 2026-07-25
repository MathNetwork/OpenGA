import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantLeibniz
import DifferentialGeometry.Tensor.RSTensor.Derivation.GradientBundleEquiv


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private noncomputable def covGradGradSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  fun x => tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => w.toSection y) x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradGradSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) (v : E) :
    covGradGradSection (I := I) (M := M) g r s w x v =
      tensorCovDerivAt (I := I) (M := M) g r s w x v := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradGradSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, covGradGradSection (I := I) (M := M) g r s w x⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) with hcovLC
  haveI hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => (⟨x, covLC.toFun (fun y : M => w.toSection y) x⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => w.toSection y)
      (w.toSection.contMDiff.contMDiffOn)
  rw [← contMDiffOn_univ]
  exact hop

private noncomputable def covGradSmoothSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :=
  letI : NormedAddCommGroup (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (s + 1)
  letI : NormedSpace ℝ (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedSpace r (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_vector r (s + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) I :=
    tensorRSBundle_smooth ∞ r (s + 1)
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph ∘
          (fun x : M =>
            (⟨x, covGradGradSection (I := I) (M := M) g r s w x⟩ :
              TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
                fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph.contMDiff.comp
      (covGradGradSection_contMDiff (I := I) (M := M) g r s w)
  have hsmooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
        (fun x : M =>
          (⟨x, covGradBundleEquiv (I := I) (M := M) r s x
              (covGradGradSection (I := I) (M := M) g r s w x)⟩ :
            TotalSpace (TensorRSModel r (s + 1) ℝ E)
              fun y : M => TensorRSSpace r (s + 1) I y)) := by
    refine hcomp.congr ?_
    intro x
    rw [Function.comp_apply,
      covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x)]
  (ContMDiffSection.mk
      (fun x : M => covGradBundleEquiv (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x))
      hsmooth :
    Cₛ^∞⟮I; TensorRSModel r (s + 1) ℝ E,
      (fun x : M => TensorRSSpace r (s + 1) I x)⟯)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradSmoothSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) :
    covGradSmoothSection (I := I) (M := M) g r s w x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradSmoothSection_toModel_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport w.toFun) :
    TensorRSSpace.toModel
      (covGradSmoothSection (I := I) (M := M) g r s w x) = 0 := by
  have hgrad_zero : covGradGradSection (I := I) (M := M) g r s w x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.zero_apply, covGradGradSection_apply]
    exact tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s w hx v
  rw [covGradSmoothSection_apply, hgrad_zero, map_zero, TensorRSSpace.toModel_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradSmoothSection_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        (covGradSmoothSection (I := I) (M := M) g r s w x)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact w.hasCompactSupport ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  exact hx (covGradSmoothSection_toModel_eq_zero_off_tsupport
    (I := I) (M := M) g r s w hxnot)

noncomputable def covGrad (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s → SmoothCcTensor g r (s + 1) :=
  fun w =>
    { toSection := covGradSmoothSection (I := I) (M := M) g r s w
      hasCompactSupport :=
        covGradSmoothSection_hasCompactSupport (I := I) (M := M) g r s w }

omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    (covGrad (I := I) (M := M) g r s w).toSection =
      covGradSmoothSection (I := I) (M := M) g r s w := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g r s w).toSection x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => w.toSection y) x) := by
  rw [covGrad_toSection, covGradSmoothSection_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_toSection_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s w).toSection x) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s w x (v 0)) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply]
  exact covGradBundleEquiv_apply_eval (I := I) (M := M) r s x
    (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun y : M => w.toSection y) x) D v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradGradSection_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : SmoothCcTensor g r s) (x : M) :
    covGradGradSection (I := I) (M := M) g r s (w₁ + w₂) x =
      covGradGradSection (I := I) (M := M) g r s w₁ x +
        covGradGradSection (I := I) (M := M) g r s w₂ x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.add_apply, covGradGradSection_apply,
    covGradGradSection_apply, covGradGradSection_apply]
  exact tensorCovDerivAt_add (I := I) (M := M) g r s w₁ w₂ x v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradGradSection_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) (x : M) :
    covGradGradSection (I := I) (M := M) g r s (c • w) x =
      c • covGradGradSection (I := I) (M := M) g r s w x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.smul_apply, covGradGradSection_apply,
    covGradGradSection_apply]
  exact tensorCovDerivAt_smul (I := I) (M := M) g r s c w x v

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (w₁ + w₂) =
      covGrad (I := I) (M := M) g r s w₁ +
        covGrad (I := I) (M := M) g r s w₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((covGrad (I := I) (M := M) g r s w₁ +
        covGrad (I := I) (M := M) g r s w₂).toSection x) =
      (covGrad (I := I) (M := M) g r s w₁).toSection x +
        (covGrad (I := I) (M := M) g r s w₂).toSection x from rfl]
  rw [covGrad_toSection_apply, covGrad_toSection_apply, covGrad_toSection_apply]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => (w₁ + w₂).toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s (w₁ + w₂) x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w₁.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w₁ x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w₂.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w₂ x from rfl,
    covGradGradSection_add (I := I) (M := M) g r s w₁ w₂ x, map_add]

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (c • w) =
      c • covGrad (I := I) (M := M) g r s w := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • covGrad (I := I) (M := M) g r s w).toSection x) =
      c • (covGrad (I := I) (M := M) g r s w).toSection x from rfl]
  rw [covGrad_toSection_apply, covGrad_toSection_apply]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => (c • w).toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s (c • w) x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w x from rfl,
    covGradGradSection_smul (I := I) (M := M) g r s c w x, map_smul]

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem covGrad_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    covGrad (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  have h := covGrad_smul (I := I) (M := M) g r s (0 : ℝ) 0
  rwa [zero_smul, zero_smul] at h

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
