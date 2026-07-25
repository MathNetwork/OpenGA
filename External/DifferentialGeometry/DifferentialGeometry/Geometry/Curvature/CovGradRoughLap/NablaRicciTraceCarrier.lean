import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculus


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle Tensor0SNabla

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaRicci_contMDiff
    (g : SmoothRiemannianMetric I M)
    (X V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => V c) (fun c => W c) b) := by
  classical
  have hfun : (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => V c) (fun c => W c) b) =
      (fun b : M =>
        extDerivFun (I := I) (fun c => ricciTensor (I := I) g c (V c) (W c)) b (X b)
        - ricciTensor (I := I) g b ((LeviCivita (I := I) g).toFun (fun c => V c) b (X b)) (W b)
        - ricciTensor (I := I) g b (V b) ((LeviCivita (I := I) g).toFun (fun c => W c) b (X b))) := by
    funext b; rw [nablaRicci_def]
  rw [hfun]
  have hricVW : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun c : M => ricciTensor (I := I) g c (V c) (W c)) :=
    ricciTensor_pairing_contMDiff (I := I) g V.contMDiff W.contMDiff
  have hterm1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => extDerivFun (I := I) (fun c => ricciTensor (I := I) g c (V c) (W c)) b (X b)) :=
    extDerivFunApply_contMDiff (I := I) hricVW X.contMDiff
  have hcovV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (fun c => X c) (fun c => V c))) := by
    have hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun c => V c)) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact V.contMDiff
    exact contMDiffOn_univ.mp (covApply_contMDiffOn (I := I) (cov := LeviCivita (I := I) g)
      (X := fun c => X c) (Z := fun c => V c) X.contMDiff hZ)
  have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (fun c => X c) (fun c => W c))) := by
    have hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun c => W c)) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact W.contMDiff
    exact contMDiffOn_univ.mp (covApply_contMDiffOn (I := I) (cov := LeviCivita (I := I) g)
      (X := fun c => X c) (Z := fun c => W c) X.contMDiff hZ)
  have hterm2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b
        ((LeviCivita (I := I) g).toFun (fun c => V c) b (X b)) (W b)) :=
    ricciTensor_pairing_contMDiff (I := I) g hcovV W.contMDiff
  have hterm3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b (V b)
        ((LeviCivita (I := I) g).toFun (fun c => W c) b (X b))) :=
    ricciTensor_pairing_contMDiff (I := I) g V.contMDiff hcovW
  exact (hterm1.sub hterm2).sub hterm3


omit [CompactSpace M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRicciBilin_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicciBilin (I := I) g X b (Y b) (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have hbasis_src : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) α j)
      (chartAt H α).source := by
    have h := chartBasisVec_contMDiffOn (I := I) α j
    rwa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] at h
  obtain ⟨s', hs'_eq⟩ := exists_contMDiffSection_eqOn_nhd (I := I)
    (F := E) (V := fun b : M => TangentSpace I b) (n := (⊤ : ℕ∞))
    (s := fun _ : Unit => fun b : M => chartBasisVecFiber (I := I) α j b)
    (u := (chartAt H α).source) (p := x₀)
    (fun _ => hbasis_src) ((chartAt H α).open_source) hx₀
  set Yext : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := s' () with hYext_def
  have hYext_eq : ∀ᶠ b in 𝓝 x₀, Yext b = chartBasisVecFiber (I := I) α j b := by
    filter_upwards [hs'_eq] with b hb using hb ()
  have hrw : (fun b : M => nablaRicciBilin (I := I) g X b (Y b)
        (chartBasisVecFiber (I := I) α j b)) =ᶠ[𝓝 x₀]
      (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => Y c) (fun c => Yext c) b) := by
    filter_upwards [hYext_eq] with b hb
    change nablaRicci (I := I) g (fun c => X c)
          (fun c => smoothExtensionTangent (I := I) b (Y b) c)
          (fun c => smoothExtensionTangent (I := I) b (chartBasisVecFiber (I := I) α j b) c) b =
        nablaRicci (I := I) g (fun c => X c) (fun c => Y c) (fun c => Yext c) b
    refine nablaRicci_eq_of_VW_eq (g := g) X
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) b (Y b))
        (smoothExtensionTangent_contMDiff (I := I) b (Y b))) Y
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) b (chartBasisVecFiber (I := I) α j b))
        (smoothExtensionTangent_contMDiff (I := I) b (chartBasisVecFiber (I := I) α j b))) Yext b
      ?_ ?_
    · change smoothExtensionTangent (I := I) b (Y b) b = Y b
      exact smoothExtensionTangent_eq (I := I) b (Y b)
    · change smoothExtensionTangent (I := I) b (chartBasisVecFiber (I := I) α j b) b = Yext b
      rw [smoothExtensionTangent_eq (I := I) b (chartBasisVecFiber (I := I) α j b), hb]
  have hsmooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => Y c) (fun c => Yext c) b) x₀ :=
    (nablaRicci_contMDiff (I := I) g X Y Yext).contMDiffAt
  have hAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicciBilin (I := I) g X b (Y b) (chartBasisVecFiber (I := I) α j b)) x₀ :=
    hsmooth.congr_of_eventuallyEq hrw
  exact hAt.contMDiffWithinAt


omit [CompactSpace M] in
theorem nablaRicciEndo_contMDiff
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (nablaRicciEndo (I := I) g X x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => nablaRicciEndo (I := I) g X x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (nablaRicciBilin (I := I) g X b (Y b))
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source :=
    fun α j => nablaRicciBilin_chartBasis_contMDiffOn (I := I) g X Y α j
  have hsmooth := metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => nablaRicciBilin (I := I) g X b (Y b)) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x (nablaRicciBilin (I := I) g X x (Y x))) =
    TotalSpace.mk' E x (nablaRicciEndo (I := I) g X x (Y x))
  congr 1

set_option backward.isDefEq.respectTransparency false in

def nablaRicSlotOpFib (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
            (nablaRicciEndo (I := I) g X x))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_comp,
          map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_comp,
          map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] lemma nablaRicSlotOpFib_apply (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) :
    nablaRicSlotOpFib (I := I) (M := M) g X s x D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
          (nablaRicciEndo (I := I) g X x)) := by
  rw [nablaRicSlotOpFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma nablaRicSlotOpFib_apply_eval (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (nablaRicSlotOpFib (I := I) (M := M) g X s x D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D
          (nablaRicciEndo (I := I) g X x v0)) vs := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (nablaRicSlotOpFib (I := I) (M := M) g X s x D) v0 vs]
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (nablaRicSlotOpFib (I := I) (M := M) g X s x D) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
        (nablaRicciEndo (I := I) g X x) := by
    rw [nablaRicSlotOpFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
theorem nablaRicSlotOpFib_contMDiff (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (s + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (s + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) (s + 1) I z) x
        (nablaRicSlotOpFib (I := I) (M := M) g X s x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (s + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => nablaRicSlotOpFib (I := I) (M := M) g X s x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (nablaRicSlotOpFib (I := I) (M := M) g X s x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (nablaRicciEndo (I := I) g X x)))) := by
    funext x
    rw [nablaRicSlotOpFib_apply]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x))) :=
    fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (nablaRicciEndo (I := I) g X x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
        (nablaRicciEndo (I := I) g X x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (nablaRicciEndo (I := I) g X x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)
          (nablaRicciEndo (I := I) g X x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (nablaRicciEndo (I := I) g X x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) (nablaRicciEndo_contMDiff (I := I) g X) Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
      (nablaRicciEndo (I := I) g X x)) hG

set_option backward.isDefEq.respectTransparency false in

def nablaRicSlotOpField (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) :
    SmoothCcTensor g (s + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 1) (s + 1) I x from nablaRicSlotOpFib (I := I) (M := M) g X s x)
      contMDiff_toFun := nablaRicSlotOpFib_contMDiff (I := I) (M := M) g X s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

@[simp] lemma nablaRicSlotOpField_toSection (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M) :
    (nablaRicSlotOpField (I := I) (M := M) g X s).toSection x =
      (show TensorRSSpace (s + 1) (s + 1) I x from
        nablaRicSlotOpFib (I := I) (M := M) g X s x) := rfl

def nablaRicTraceSection (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  operatorFieldApply (I := I) (M := M) g (s + 1) (s + 1)
    (nablaRicSlotOpField (I := I) (M := M) g X s) (covGrad (I := I) (M := M) g 0 s S)


@[simp] lemma nablaRicTraceSection_toSection (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) :
    (nablaRicTraceSection (I := I) (M := M) g X s S).toSection x =
      (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (nablaRicSlotOpField (I := I) (M := M) g X s).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  rw [nablaRicTraceSection,
    appCc_toSection (I := I) (M := M) g (s + 1) (s + 1)
      (nablaRicSlotOpField (I := I) (M := M) g X s) (covGrad (I := I) (M := M) g 0 s S) x]

set_option backward.isDefEq.respectTransparency false in

theorem nablaRicTraceSection_apply_leadingSlot
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v0 : E) (vs : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (nablaRicTraceSection (I := I) (M := M) g X s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (nablaRicciEndo (I := I) g X x v0) vs) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (nablaRicTraceSection (I := I) (M := M) g X s S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      nablaRicSlotOpFib (I := I) (M := M) g X s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [nablaRicTraceSection_toSection, nablaRicSlotOpField_toSection]
    rfl
  rw [hval]
  rw [nablaRicSlotOpFib_apply_eval (I := I) (M := M) g X s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v0 vs]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (nablaRicciEndo (I := I) g X x v0) vs]


omit [CompactSpace M] in
theorem leviCivita_covDeriv_ricEndoRaisedFib (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (LeviCivita (I := I) g).toFun (fun y : M => ricEndoRaisedFib (I := I) g y (Y y)) x (X x) =
      nablaRicciEndo (I := I) g X x (Y x) +
        ricEndoRaisedFib (I := I) g x ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)) := by
  classical
  refine SmoothRiemannianMetric.eq_of_inner_eq g (fun ζ => ?_)
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x ζ)
      (smoothExtensionTangent_contMDiff (I := I) x ζ) with hWdef
  have hWx : W x = ζ := smoothExtensionTangent_eq (I := I) x ζ
  have hZ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (ricEndoRaisedFib (I := I) g y (Y y))) :=
    ContMDiff.clm_bundle_apply (b := id) (ricEndoRaisedFib_contMDiff (I := I) g) Y.contMDiff
  have hZ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (ricEndoRaisedFib (I := I) g y (Y y))) x :=
    (hZ_smooth x).mdifferentiableAt (by simp)
  have hW_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (W y)) x :=
    (W.contMDiff x).mdifferentiableAt (by simp)
  have hcomp : (mfderiv I 𝓘(ℝ)
        (fun b : M => g.inner b (ricEndoRaisedFib (I := I) g b (Y b)) (W b)) x) (X x) =
      g.inner x ((LeviCivita (I := I) g).toFun
          (fun y : M => ricEndoRaisedFib (I := I) g y (Y y)) x (X x)) (W x) +
        g.inner x (ricEndoRaisedFib (I := I) g x (Y x))
          ((LeviCivita (I := I) g).toFun (fun y : M => W y) x (X x)) :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hZ_at hW_at (X x)
  have hfun : (fun b : M => g.inner b (ricEndoRaisedFib (I := I) g b (Y b)) (W b)) =
      (fun b : M => ricciTensor (I := I) g b (Y b) (W b)) := by
    funext b
    exact inner_ricEndoRaisedFib (I := I) g b (Y b) (W b)
  rw [hfun] at hcomp
  have hnabla : g.inner x (nablaRicciEndo (I := I) g X x (Y x)) (W x) =
      nablaRicci (I := I) g X Y W x :=
    inner_nablaRicciEndo_smooth (I := I) g X Y W x
  rw [nablaRicci_def] at hnabla
  have hnabla' : g.inner x (nablaRicciEndo (I := I) g X x (Y x)) (W x) =
      extDerivFun (I := I) (fun b : M => ricciTensor (I := I) g b (Y b) (W b)) x (X x)
        - ricciTensor (I := I) g x
            ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)) (W x)
        - ricciTensor (I := I) g x (Y x)
            ((LeviCivita (I := I) g).toFun (fun y : M => W y) x (X x)) := hnabla
  have hcomp' : extDerivFun (I := I)
        (fun b : M => ricciTensor (I := I) g b (Y b) (W b)) x (X x) =
      g.inner x ((LeviCivita (I := I) g).toFun
          (fun y : M => ricEndoRaisedFib (I := I) g y (Y y)) x (X x)) (W x) +
        g.inner x (ricEndoRaisedFib (I := I) g x (Y x))
          ((LeviCivita (I := I) g).toFun (fun y : M => W y) x (X x)) := hcomp
  have hcorr : g.inner x (ricEndoRaisedFib (I := I) g x (Y x))
      ((LeviCivita (I := I) g).toFun (fun y : M => W y) x (X x)) =
      ricciTensor (I := I) g x (Y x)
        ((LeviCivita (I := I) g).toFun (fun y : M => W y) x (X x)) :=
    inner_ricEndoRaisedFib (I := I) g x (Y x) _
  have hraise : g.inner x (ricEndoRaisedFib (I := I) g x
        ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x))) (W x) =
      ricciTensor (I := I) g x
        ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)) (W x) :=
    inner_ricEndoRaisedFib (I := I) g x _ (W x)
  have hsplit : g.inner x (nablaRicciEndo (I := I) g X x (Y x) +
        ricEndoRaisedFib (I := I) g x
          ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x))) ζ =
      g.inner x (nablaRicciEndo (I := I) g X x (Y x)) ζ +
        g.inner x (ricEndoRaisedFib (I := I) g x
          ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x))) ζ := by
    simp [map_add, ContinuousLinearMap.add_apply]
  rw [hsplit, ← hWx]
  linarith [hcomp', hnabla', hcorr, hraise]

set_option backward.isDefEq.respectTransparency false in

private theorem ricSlotOp_core_curry_reading (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
            (ricSlotOpField (I := I) (M := M) g s) x (X x)) D)) v0 =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x D)
        (nablaRicciEndo (I := I) g X x v0) := by
  classical
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  have hZ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (ricEndoRaisedFib (I := I) g y (Y y))) :=
    ContMDiff.clm_bundle_apply (b := id) (ricEndoRaisedFib_contMDiff (I := I) g) Y.contMDiff
  let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => ricEndoRaisedFib (I := I) g y (Y y), hZ_smooth⟩
  set Φ := ricSlotOpField (I := I) (M := M) g s with hΦ
  have hU_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Φ.toSection y) (w y))) :=
    ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff w.contMDiff
  have hU_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        Φ.toSection y) (w y)) x :=
    (hU_smooth x).mdifferentiableAt (by norm_num)
  have hw_at : TensorSectionMDiffAt (I := I) (s + 1) (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  have hCL_U := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g s
    (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
      Φ.toSection y) (w y)) (x := x) hU_at Y (X x)
  have hCL_w := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g s
    (fun y : M => w y) (x := x) hw_at Z (X x)
  have hHL := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (s + 1) (s + 1)
    (LeviCivita (I := I) g) Φ.toSection w x (X x)
  have hfun : (fun y : M =>
        (Tensor0SNabla.curriedSection I M
            (fun y' : M => (show Tensor0SSpace (s + 1) I y' →L[ℝ] Tensor0SSpace (s + 1) I y' from
              Φ.toSection y') (w y')) y) (Y y)) =
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun y' : M => w y') y) (Z y)) := by
    funext y
    change (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Φ.toSection y) (w y))) (Y y) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y (w y))
        (ricEndoRaisedFib (I := I) g y (Y y))
    rw [hΦ, ricSlotOpField_toSection, ricSlotOpFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rw [← hw, ← hY,
    tensorCovDerivAt_def (I := I) (M := M) g (s + 1) (s + 1) Φ x (X x)]
  rw [hHL, map_sub, ContinuousLinearMap.sub_apply]
  rw [eq_sub_of_add_eq hCL_U.symm]
  rw [hfun]
  rw [show (fun y : M => Z y) = (fun y : M => ricEndoRaisedFib (I := I) g y (Y y)) from rfl] at hCL_w
  rw [hCL_w]
  have hEndo := leviCivita_covDeriv_ricEndoRaisedFib (I := I) (M := M) g X Y x
  have hcurU : (Tensor0SNabla.curriedSection I M
        (fun y' : M => (show Tensor0SSpace (s + 1) I y' →L[ℝ] Tensor0SSpace (s + 1) I y' from
          Φ.toSection y') (w y')) x)
        ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x (w x))
        (ricEndoRaisedFib (I := I) g x
          ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x))) := by
    change (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          Φ.toSection x) (w x)))
        ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)) = _
    rw [hΦ, ricSlotOpField_toSection, ricSlotOpFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  have hΦgrad : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from Φ.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
            (fun y : M => w y) x (X x)))) (Y x) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
            (fun y : M => w y) x (X x)))
        (ricEndoRaisedFib (I := I) g x (Y x)) := by
    rw [hΦ, ricSlotOpField_toSection, ricSlotOpFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  have hZx : Z x = ricEndoRaisedFib (I := I) g x (Y x) := rfl
  have hcurW : (Tensor0SNabla.curriedSection I M (fun y' : M => w y') x) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x (w x)) := rfl
  rw [hcurU, hΦgrad, hZx, hcurW]
  rw [hEndo, map_add]
  abel

set_option backward.isDefEq.respectTransparency false in

theorem tensorCovDerivAt_ricSlotOpField_eq_nablaRicSlotOpFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
        (ricSlotOpField (I := I) (M := M) g s) x (X x) =
      (show TensorRSSpace (s + 1) (s + 1) I x from
        nablaRicSlotOpFib (I := I) (M := M) g X s x) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          nablaRicSlotOpFib (I := I) (M := M) g X s x) D)
        (Fin.cons (m 0) (Matrix.vecTail m)) =
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D
          (nablaRicciEndo (I := I) g X x (m 0))) (Matrix.vecTail m) from
    nablaRicSlotOpFib_apply_eval (I := I) (M := M) g X s x D (m 0) (Matrix.vecTail m)]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
        (ricSlotOpField (I := I) (M := M) g s) x (X x)) D) (m 0) (Matrix.vecTail m)]
  congr 1
  exact ricSlotOp_core_curry_reading (I := I) (M := M) g s X x D (m 0)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_ricTraceSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 (s + 1) (ricTraceSection (I := I) (M := M) g s S) =
      operatorFieldApply (I := I) (M := M) g (s + 1) (s + 2)
          (covGrad (I := I) (M := M) g (s + 1) (s + 1) (ricSlotOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 s S) +
        operatorFieldApply (I := I) (M := M) g (s + 2) (s + 2)
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1) (ricSlotOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)) :=
  covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 1) (s + 1)
    (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S)

set_option backward.isDefEq.respectTransparency false in

theorem tensorCovDerivAt_ricTraceSection_eq_nablaRicTrace_add
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (S : SmoothCcTensor g 0 s) (x : M) :
    (show TensorRSSpace 0 (s + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S) x (X x)) =
      (show TensorRSSpace 0 (s + 1) I x from
          (nablaRicTraceSection (I := I) (M := M) g X s S).toSection x) +
        (show TensorRSSpace 0 (s + 1) I x from
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (ricSlotOpField (I := I) (M := M) g s).toSection x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S) x (X x))) := by
  rw [show ricTraceSection (I := I) (M := M) g s S =
      operatorFieldApply (I := I) (M := M) g (s + 1) (s + 1) (ricSlotOpField (I := I) (M := M) g s)
        (covGrad (I := I) (M := M) g 0 s S) from rfl]
  rw [tensorCovDerivAt_appCc_eq (I := I) (M := M) g (s + 1) (s + 1)
    (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S) x (X x)]
  congr 1
  rw [nablaRicTraceSection_toSection (I := I) (M := M) g X s S x,
    nablaRicSlotOpField_toSection (I := I) (M := M) g X s x]
  congr 1
  exact congrArg (fun (T : Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x) => T)
    (tensorCovDerivAt_ricSlotOpField_eq_nablaRicSlotOpFib (I := I) (M := M) g s X x)

end Connection
end Integral
end DifferentialGeometry

end
