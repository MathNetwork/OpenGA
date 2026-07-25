import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Connection.ParsevalFrameField


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev TensorSmooth (s : ℕ) (A : Π b : M, Tensor0SSpace s I b) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
    (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) b (A b))

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_add_left
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => (X + X') b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
          (fun b => W b) x
        + nablaCurvSec (LeviCivita (I := I) g) (fun b => X' b) (fun b => Y b) (fun b => Z b)
            (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hX' := X'.contMDiff; have hY := Y.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  have hXX' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => (X + X') b)) := (X + X').contMDiff
  rw [nablaCurvSec_def, nablaCurvSec_def, nablaCurvSec_def]

  have h1 : cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
        ((fun b => (X + X') b) x) =
      cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x (X x)
        + cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
            (X' x) := by
    have : ((fun b => (X + X') b) x) = X x + X' x := by
      simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [this, map_add]

  have hcovT2 : covApply cov (fun b => (X + X') b) (fun b => Y b) =
      covApply cov (fun b => X b) (fun b => Y b) + covApply cov (fun b => X' b) (fun b => Y b) := by
    funext b
    simp only [covApply, ContMDiffSection.coe_add, Pi.add_apply, map_add]
  have h2 : riemannSec cov (covApply cov (fun b => (X + X') b) (fun b => Y b)) (fun b => Z b)
        (fun b => W b) x =
      riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b) (fun b => W b) x
        + riemannSec cov (covApply cov (fun b => X' b) (fun b => Y b)) (fun b => Z b)
            (fun b => W b) x := by
    rw [hcovT2]
    exact riemannSec_add_left (cov := cov)
      ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hX' hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX' hY) hW x).mdifferentiableAt (by simp))

  have hcovT3 : covApply cov (fun b => (X + X') b) (fun b => Z b) =
      covApply cov (fun b => X b) (fun b => Z b) + covApply cov (fun b => X' b) (fun b => Z b) := by
    funext b
    simp only [covApply, ContMDiffSection.coe_add, Pi.add_apply, map_add]
  have h3 : riemannSec cov (fun b => Y b) (covApply cov (fun b => (X + X') b) (fun b => Z b))
        (fun b => W b) x =
      riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b)) (fun b => W b) x
        + riemannSec cov (fun b => Y b) (covApply cov (fun b => X' b) (fun b => Z b))
            (fun b => W b) x := by
    rw [hcovT3]
    exact riemannSec_add_right (cov := cov)
      ((covApply_contMDiff (cov := cov) hX hZ x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hX' hZ x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hZ) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX' hZ) hW x).mdifferentiableAt (by simp))

  have hcovT4 : covApply cov (fun b => (X + X') b) (fun b => W b) =
      covApply cov (fun b => X b) (fun b => W b) + covApply cov (fun b => X' b) (fun b => W b) := by
    funext b
    simp only [covApply, ContMDiffSection.coe_add, Pi.add_apply, map_add]
  have hcXW := covApply_contMDiff (cov := cov) hX hW
  have hcX'W := covApply_contMDiff (cov := cov) hX' hW
  have h4 : riemannSec cov (fun b => Y b) (fun b => Z b)
        (covApply cov (fun b => (X + X') b) (fun b => W b)) x =
      riemannSec cov (fun b => Y b) (fun b => Z b) (covApply cov (fun b => X b) (fun b => W b)) x
        + riemannSec cov (fun b => Y b) (fun b => Z b)
            (covApply cov (fun b => X' b) (fun b => W b)) x := by
    rw [hcovT4]
    exact riemannSec_add_third (cov := cov)
      (Filter.Eventually.of_forall (fun b => (hcXW b).mdifferentiableAt (by simp)))
      (Filter.Eventually.of_forall (fun b => (hcX'W b).mdifferentiableAt (by simp)))
      ((covApply_contMDiff (cov := cov) hZ hcXW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hZ hcX'W x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hZ (hcXW.add_section hcX'W) x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcXW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcX'W x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY (hcXW.add_section hcX'W) x).mdifferentiableAt (by simp))
  rw [h1, h2, h3, h4]
  abel

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_smul_left
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (f • fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      f x • nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  rw [nablaCurvSec_def, nablaCurvSec_def]

  have h1 : cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
        ((f • fun b => X b) x) =
      f x • cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
            (X x) := by
    have hval : (f • fun b => X b) x = f x • X x := rfl
    rw [hval, map_smul]

  have hcovT2 : covApply cov (f • fun b => X b) (fun b => Y b) =
      f • covApply cov (fun b => X b) (fun b => Y b) := by
    funext b
    change cov.toFun (fun b => Y b) b ((f • fun b => X b) b) =
      f b • cov.toFun (fun b => Y b) b (X b)
    rw [show (f • fun b => X b) b = f b • X b from rfl, map_smul]
  have hcovT3 : covApply cov (f • fun b => X b) (fun b => Z b) =
      f • covApply cov (fun b => X b) (fun b => Z b) := by
    funext b
    change cov.toFun (fun b => Z b) b ((f • fun b => X b) b) =
      f b • cov.toFun (fun b => Z b) b (X b)
    rw [show (f • fun b => X b) b = f b • X b from rfl, map_smul]
  have hcovT4 : covApply cov (f • fun b => X b) (fun b => W b) =
      f • covApply cov (fun b => X b) (fun b => W b) := by
    funext b
    change cov.toFun (fun b => W b) b ((f • fun b => X b) b) =
      f b • cov.toFun (fun b => W b) b (X b)
    rw [show (f • fun b => X b) b = f b • X b from rfl, map_smul]

  have h2 : riemannSec cov (covApply cov (f • fun b => X b) (fun b => Y b)) (fun b => Z b)
        (fun b => W b) x =
      f x • riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
            (fun b => W b) x := by
    rw [hcovT2]
    exact riemannSec_smul_left (cov := cov) hfx
      ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))

  have h3 : riemannSec cov (fun b => Y b) (covApply cov (f • fun b => X b) (fun b => Z b))
        (fun b => W b) x =
      f x • riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
            (fun b => W b) x := by
    rw [hcovT3]
    exact riemannSec_smul_right (cov := cov) hfx
      ((covApply_contMDiff (cov := cov) hX hZ x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hZ) hW x).mdifferentiableAt (by simp))

  have hcXW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov (fun b => X b) (fun b => W b))) :=
    covApply_contMDiff (cov := cov) hX hW
  have hfcXW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (f • covApply cov (fun b => X b) (fun b => W b))) :=
    hf.smul_section hcXW
  have h4 : riemannSec cov (fun b => Y b) (fun b => Z b)
        (covApply cov (f • fun b => X b) (fun b => W b)) x =
      f x • riemannSec cov (fun b => Y b) (fun b => Z b)
            (covApply cov (fun b => X b) (fun b => W b)) x := by
    rw [hcovT4]
    rw [← riemannOp_apply_smooth (cov := cov) hY hZ hfcXW,
        ← riemannOp_apply_smooth (cov := cov) hY hZ hcXW]
    rw [show (f • covApply cov (fun b => X b) (fun b => W b)) x =
        f x • (covApply cov (fun b => X b) (fun b => W b)) x from rfl]
    rw [map_smul]
  rw [h1, h2, h3, h4]
  simp only [smul_sub]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_add_right
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => (Y + Y') b) (fun b => Z b)
        (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
          (fun b => W b) x
        + nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y' b) (fun b => Z b)
            (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff; have hY' := Y'.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  rw [nablaCurvSec_def, nablaCurvSec_def, nablaCurvSec_def]

  have hsecYY' : (fun b => riemannSec cov (fun b => (Y + Y') b) (fun b => Z b) (fun b => W b) b) =
      (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b)
        + (fun b => riemannSec cov (fun b => Y' b) (fun b => Z b) (fun b => W b) b) := by
    funext b
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq]
    simp only [Pi.add_apply]
    exact riemannSec_add_left (cov := cov) ((hY b).mdifferentiableAt (by simp))
      ((hY' b).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW b).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY' hW b).mdifferentiableAt (by simp))
  have hRYsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b)) :=
    riemannSec_contMDiff (cov := cov) hY hZ hW
  have hRY'sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => riemannSec cov (fun b => Y' b) (fun b => Z b) (fun b => W b) b)) :=
    riemannSec_contMDiff (cov := cov) hY' hZ hW
  have h1 : cov.toFun (fun b => riemannSec cov (fun b => (Y + Y') b) (fun b => Z b) (fun b => W b) b)
        x (X x) =
      cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x (X x)
        + cov.toFun (fun b => riemannSec cov (fun b => Y' b) (fun b => Z b) (fun b => W b) b) x
            (X x) := by
    rw [hsecYY', cov.isCovariantDerivativeOnUniv.add (hRYsm.mdifferentiableAt (by simp))
      (hRY'sm.mdifferentiableAt (by simp))]
    rfl

  have hcovT2 : covApply cov (fun b => X b) (fun b => (Y + Y') b) =
      covApply cov (fun b => X b) (fun b => Y b) + covApply cov (fun b => X b) (fun b => Y' b) := by
    funext b
    change cov.toFun (fun b => (Y + Y') b) b (X b) =
      cov.toFun (fun b => Y b) b (X b) + cov.toFun (fun b => Y' b) b (X b)
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq, cov.isCovariantDerivativeOnUniv.add ((hY b).mdifferentiableAt (by simp))
      ((hY' b).mdifferentiableAt (by simp))]
    rfl
  have h2 : riemannSec cov (covApply cov (fun b => X b) (fun b => (Y + Y') b)) (fun b => Z b)
        (fun b => W b) x =
      riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b) (fun b => W b) x
        + riemannSec cov (covApply cov (fun b => X b) (fun b => Y' b)) (fun b => Z b)
            (fun b => W b) x := by
    rw [hcovT2]
    exact riemannSec_add_left (cov := cov)
      ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hX hY' x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY') hW x).mdifferentiableAt (by simp))

  have h3 : riemannSec cov (fun b => (Y + Y') b) (covApply cov (fun b => X b) (fun b => Z b))
        (fun b => W b) x =
      riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b)) (fun b => W b) x
        + riemannSec cov (fun b => Y' b) (covApply cov (fun b => X b) (fun b => Z b))
            (fun b => W b) x := by
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq]
    exact riemannSec_add_left (cov := cov) ((hY x).mdifferentiableAt (by simp))
      ((hY' x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY' hW x).mdifferentiableAt (by simp))

  have hcXZ := covApply_contMDiff (cov := cov) hX hZ
  have h4 : riemannSec cov (fun b => (Y + Y') b) (fun b => Z b)
        (covApply cov (fun b => X b) (fun b => W b)) x =
      riemannSec cov (fun b => Y b) (fun b => Z b) (covApply cov (fun b => X b) (fun b => W b)) x
        + riemannSec cov (fun b => Y' b) (fun b => Z b)
            (covApply cov (fun b => X b) (fun b => W b)) x := by
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    have hcXW := covApply_contMDiff (cov := cov) hX hW
    rw [heq]
    exact riemannSec_add_left (cov := cov) ((hY x).mdifferentiableAt (by simp))
      ((hY' x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcXW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY' hcXW x).mdifferentiableAt (by simp))
  rw [h1, h2, h3, h4]
  abel

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma extDerivFun_apply_smooth_aux
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X : Π b : M, TangentSpace I b} (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun f b (X b)) := by
  classical
  have htan : ContMDiff I.tangent (𝓘(ℝ, ℝ).tangent) ∞ (tangentMap I 𝓘(ℝ, ℝ) f) := by
    have h₁ : ContMDiff I 𝓘(ℝ, ℝ) ((∞ : WithTop ℕ∞) + 1) f := by simpa using hf
    exact h₁.contMDiff_tangentMap (le_refl _)
  have hXsec : ContMDiff I I.tangent ∞
      (fun b => (TotalSpace.mk' E b (X b) : TangentBundle I M)) := hX
  have hcomp : ContMDiff I (𝓘(ℝ, ℝ).tangent) ∞
      (fun b => tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (X b))) :=
    htan.comp hXsec
  have hsnd : ContMDiff (𝓘(ℝ, ℝ).tangent) 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2) := contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)
  have hresult : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b => (tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (X b))).2) :=
    hsnd.comp hcomp
  refine hresult.congr fun b => ?_
  simp [extDerivFun, tangentMap_snd, NormedSpace.fromTangentSpace]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_smul_right
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (f • fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      f x • nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  set R : Π b : M, TangentSpace I b :=
    fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b with hR
  have hRsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% R) :=
    riemannSec_contMDiff (cov := cov) hY hZ hW
  rw [nablaCurvSec_def, nablaCurvSec_def]

  have hsecfY : (fun b => riemannSec cov (f • fun b => Y b) (fun b => Z b) (fun b => W b) b) =
      f • R := by
    funext b
    change riemannSec cov (f • fun b => Y b) (fun b => Z b) (fun b => W b) b =
      f b • riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b
    exact riemannSec_smul_left (cov := cov) ((hf b).mdifferentiableAt (by simp))
      ((hY b).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW b).mdifferentiableAt (by simp))
  have h1 : cov.toFun (fun b => riemannSec cov (f • fun b => Y b) (fun b => Z b) (fun b => W b) b)
        x (X x) =
      f x • cov.toFun R x (X x) + extDerivFun f x (X x) • R x := by
    rw [hsecfY, cov.isCovariantDerivativeOnUniv.leibniz (hRsm.mdifferentiableAt (by simp)) hfx]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]

  set Xf : M → ℝ := fun b => extDerivFun f b (X b) with hXf
  have hcovfY : covApply cov (fun b => X b) (f • fun b => Y b) =
      f • covApply cov (fun b => X b) (fun b => Y b) + Xf • (fun b => Y b) := by
    funext b
    change cov.toFun (f • fun b => Y b) b (X b) =
      (f • covApply cov (fun b => X b) (fun b => Y b)) b + (Xf • fun b => Y b) b
    rw [cov.isCovariantDerivativeOnUniv.leibniz ((hY b).mdifferentiableAt (by simp))
      ((hf b).mdifferentiableAt (by simp))]
    simp [covApply, Xf, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hXfsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ Xf := extDerivFun_apply_smooth_aux hf hX
  have hcXY := covApply_contMDiff (cov := cov) hX hY
  have h2 : riemannSec cov (covApply cov (fun b => X b) (f • fun b => Y b)) (fun b => Z b)
        (fun b => W b) x =
      f x • riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
            (fun b => W b) x
        + extDerivFun f x (X x) • R x := by
    rw [hcovfY]
    rw [riemannSec_add_left (cov := cov)
      ((hf.smul_section hcXY x).mdifferentiableAt (by simp))
      ((hXfsm.smul_section hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) (hf.smul_section hcXY) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) (hXfsm.smul_section hY) hW x).mdifferentiableAt (by simp))]
    rw [show (f • covApply cov (fun b => X b) (fun b => Y b)) =
        f • covApply cov (fun b => X b) (fun b => Y b) from rfl]
    rw [riemannSec_smul_left (cov := cov) hfx
        ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
        ((covApply_contMDiff (cov := cov)
          (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))]
    rw [riemannSec_smul_left (cov := cov) ((hXfsm x).mdifferentiableAt (by simp))
        ((hY x).mdifferentiableAt (by simp))
        ((covApply_contMDiff (cov := cov) hY hW x).mdifferentiableAt (by simp))]

  have h3 : riemannSec cov (f • fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
        (fun b => W b) x =
      f x • riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
            (fun b => W b) x :=
    riemannSec_smul_left (cov := cov) hfx ((hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW x).mdifferentiableAt (by simp))
  have hcXW := covApply_contMDiff (cov := cov) hX hW
  have h4 : riemannSec cov (f • fun b => Y b) (fun b => Z b)
        (covApply cov (fun b => X b) (fun b => W b)) x =
      f x • riemannSec cov (fun b => Y b) (fun b => Z b)
            (covApply cov (fun b => X b) (fun b => W b)) x :=
    riemannSec_smul_left (cov := cov) hfx ((hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcXW x).mdifferentiableAt (by simp))
  rw [h1, h2, h3, h4]
  simp only [hR]
  module

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaBaseSlotCurv_add_left
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g (X + X') Y Z x u =
      nablaBaseSlotCurv (I := I) g X Y Z x u + nablaBaseSlotCurv (I := I) g X' Y Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec,
      nablaBaseSlotCurv_eq_nablaCurvSec]
  exact nablaCurvSec_add_left (g := g) X X' Y Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaBaseSlotCurv_smul_left
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g (c • X) Y Z x u =
      c • nablaBaseSlotCurv (I := I) g X Y Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hsmul := nablaCurvSec_smul_left (g := g) hconst X Y Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x
  have hcoe : ((fun _ : M => c) • fun b => X b) = (fun b => (c • X) b) := rfl
  rw [hcoe] at hsmul
  exact hsmul

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaBaseSlotCurv_smul_right
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X (c • Y) Z x u =
      c • nablaBaseSlotCurv (I := I) g X Y Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hsmul := nablaCurvSec_smul_right (g := g) hconst X Y Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x
  have hcoe : ((fun _ : M => c) • fun b => Y b) = (fun b => (c • Y) b) := rfl
  rw [hcoe] at hsmul
  exact hsmul

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaBaseSlotCurv_add_right
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X (Y + Y') Z x u =
      nablaBaseSlotCurv (I := I) g X Y Z x u + nablaBaseSlotCurv (I := I) g X Y' Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec,
      nablaBaseSlotCurv_eq_nablaCurvSec]
  exact nablaCurvSec_add_right (g := g) X Y Y' Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_zero_right
    (g : SmoothRiemannianMetric I M)
    (X Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
        (fun b => (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) (fun b => Z b)
        (fun b => W b) x = 0 := by
  have h := nablaCurvSec_add_right (g := g) X
    (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) Z W x
  have hfun : (fun b => ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        + (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) b) =
      (fun b => (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) := by
    funext b; simp
  rw [hfun] at h
  exact add_eq_left.mp h.symm

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaCurvSec_finsetSum_right
    (g : SmoothRiemannianMetric I M) {ι : Type*} (s : Finset ι)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
        (fun b => (∑ i ∈ s, Y i) b) (fun b => Z b) (fun b => W b) x =
      ∑ i ∈ s, nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
        (fun b => Y i b) (fun b => Z b) (fun b => W b) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact nablaCurvSec_zero_right (g := g) X Z W x
  | insert a t ha ih =>
      have hfun : (fun b => (∑ i ∈ insert a t, Y i) b) =
          (fun b => (Y a + ∑ i ∈ t, Y i) b) := by
        funext b
        rw [ContMDiffSection.finset_sum_apply, Finset.sum_insert ha,
          ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.finset_sum_apply]
      rw [hfun, nablaCurvSec_add_right (g := g) X (Y a) (∑ i ∈ t, Y i) Z W x, ih,
        Finset.sum_insert ha]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannSec_eq_of_X_eventuallyEq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    (cov : CovariantDerivative I F V) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X X' Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X'))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z))
    (hXX' : ∀ᶠ b in 𝓝 x, X b = X' b) :
    riemannSec cov X Y Z x = riemannSec cov X' Y Z x := by
  classical
  have hXx : X x = X' x := hXX'.self_of_nhds
  unfold riemannSec

  rw [hXx]

  have hev_cXZ : ∀ᶠ b in 𝓝 x, covApply cov X Z b = covApply cov X' Z b := by
    filter_upwards [hXX'] with b hb
    simp only [covApply_apply, hb]
  have hcXZ_at : MDiffAt (T% (covApply cov X Z)) x :=
    covApply_mdifferentiableAt (cov := cov) hX (by
      rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]; exact hZ)
  have hcX'Z_at : MDiffAt (T% (covApply cov X' Z)) x :=
    covApply_mdifferentiableAt (cov := cov) hX' (by
      rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]; exact hZ)
  have hT2 : cov.toFun (covApply cov X Z) x = cov.toFun (covApply cov X' Z) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hcXZ_at hcX'Z_at Filter.univ_mem hev_cXZ
  rw [hT2]

  have hbr_x : VectorField.mlieBracket I X Y x = VectorField.mlieBracket I X' Y x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq hXX' (Filter.EventuallyEq.refl _ Y)
  rw [hbr_x]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_eq_of_Y_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    {X Y Y' Z W : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y'))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hYY' : ∀ᶠ b in 𝓝 x, Y b = Y' b) :
    nablaCurvSec (LeviCivita (I := I) g) X Y Z W x =
      nablaCurvSec (LeviCivita (I := I) g) X Y' Z W x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  rw [nablaCurvSec_def, nablaCurvSec_def]

  have hsec_ev : ∀ᶠ b in 𝓝 x,
      riemannSec cov Y Z W b = riemannSec cov Y' Z W b := by

    rw [Filter.eventually_iff_exists_mem] at hYY' ⊢
    obtain ⟨U, hU, hYeq⟩ := hYY'
    obtain ⟨V', hV'U, hV'_open, hpV'⟩ := mem_nhds_iff.mp hU
    refine ⟨V', hV'_open.mem_nhds hpV', fun b hbV' => ?_⟩
    refine riemannSec_eq_of_X_eventuallyEq (cov := cov) hY hY' hW ?_
    exact Filter.eventually_of_mem (hV'_open.mem_nhds hbV')
      (fun b' hb'V' => hYeq b' (hV'U hb'V'))
  have hRYZW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y Z W b)) :=
    riemannSec_contMDiff cov hY hZ hW
  have hRY'ZW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y' Z W b)) :=
    riemannSec_contMDiff cov hY' hZ hW
  have hT1 : cov.toFun (fun b => riemannSec cov Y Z W b) x =
      cov.toFun (fun b => riemannSec cov Y' Z W b) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hRYZW_sm.mdifferentiableAt (by simp)) (hRY'ZW_sm.mdifferentiableAt (by simp))
      Filter.univ_mem hsec_ev
  rw [hT1]

  have hcXY := covApply_contMDiff (cov := cov) hX hY
  have hcXY' := covApply_contMDiff (cov := cov) hX hY'
  have hev_cXY : ∀ᶠ b in 𝓝 x, covApply cov X Y b = covApply cov X Y' b := by

    rw [Filter.eventually_iff_exists_mem] at hYY' ⊢
    obtain ⟨U, hU, hYeq⟩ := hYY'
    obtain ⟨V', hV'U, hV'_open, hpV'⟩ := mem_nhds_iff.mp hU
    refine ⟨V', hV'_open.mem_nhds hpV', fun b hbV' => ?_⟩
    have hYeq_b : ∀ᶠ b' in 𝓝 b, Y b' = Y' b' :=
      Filter.eventually_of_mem (hV'_open.mem_nhds hbV') (fun b' hb'V' => hYeq b' (hV'U hb'V'))
    have hcov_b : cov.toFun Y b = cov.toFun Y' b :=
      cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((hY b).mdifferentiableAt (by simp)) ((hY' b).mdifferentiableAt (by simp))
        Filter.univ_mem hYeq_b
    simp only [covApply_apply, hcov_b]
  have hT2 : riemannSec cov (covApply cov X Y) Z W x =
      riemannSec cov (covApply cov X Y') Z W x :=
    riemannSec_eq_of_X_eventuallyEq (cov := cov) hcXY hcXY' hW hev_cXY
  rw [hT2]

  have hT3 : riemannSec cov Y (covApply cov X Z) W x =
      riemannSec cov Y' (covApply cov X Z) W x :=
    riemannSec_eq_of_X_eventuallyEq (cov := cov) hY hY' hW hYY'
  rw [hT3]

  have hT4 : riemannSec cov Y Z (covApply cov X W) x =
      riemannSec cov Y' Z (covApply cov X W) x :=
    riemannSec_eq_of_X_eventuallyEq (cov := cov) hY hY'
      (covApply_contMDiff (cov := cov) hX hW) hYY'
  rw [hT4]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma exists_global_smooth_eqOn_nhd_scalar
    {f : M → ℝ} {U : Set M} {x : M} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hU.mem_nhds hxU)
  refine ⟨fun b => χ b * f b, ?_, ?_⟩
  · have hχ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => (χ : M → ℝ) b) :=
      χ.contMDiff.of_le (by exact_mod_cast le_top)
    have hU_part : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b => χ b * f b) U :=
      (hχ_smooth.contMDiffOn).mul hf
    have hcompl_part : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b => χ b * f b) (tsupport χ)ᶜ := by
      apply (contMDiffOn_const (c := (0 : ℝ))).congr
      intro b hb
      rw [image_eq_zero_of_notMem_tsupport hb, zero_mul]
    refine contMDiff_of_contMDiffOn_union_of_isOpen hU_part hcompl_part ?_ hU
      (isOpen_compl_iff.mpr (isClosed_tsupport χ))
    rw [Set.eq_univ_iff_forall]
    intro b
    by_cases hb : b ∈ tsupport χ
    · exact Or.inl (hχ hb)
    · exact Or.inr hb
  · filter_upwards [χ.eventuallyEq_one] with b hb
    rw [hb, Pi.one_apply, one_mul]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_vanish_secondSlot
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {Δ : Π b : M, TangentSpace I b}
    (Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hΔ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Δ)) (hΔx : Δ x = 0) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) Δ (fun b => Z b) (fun b => W b) x = 0 := by
  classical
  set e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M) :=
    trivializationAt E (TangentSpace I) x with he_def
  have hx_base : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hbase_open : IsOpen e.baseSet := e.open_baseSet
  set bE : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ E) ℝ E := Module.Basis.ofVectorSpace ℝ E with hbE_def

  set sLoc : Module.Basis.ofVectorSpaceIndex ℝ E → Π b : M, TangentSpace I b :=
    fun i => e.localFrame bE i with hsLoc_def
  set cLoc : Module.Basis.ofVectorSpaceIndex ℝ E → M → ℝ :=
    fun i b => e.localFrame_coeff I bE i b (Δ b) with hcLoc_def
  have hexpand : ∀ᶠ b in 𝓝 x, Δ b = ∑ i, cLoc i b • sLoc i b :=
    e.eventually_eq_localFrame_sum_coeff_smul bE hx_base

  have hsLoc_on : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (sLoc i)) e.baseSet :=
    fun i => e.contMDiffOn_localFrame_baseSet (n := ∞) (b := bE) i
  have hcLoc_on : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (cLoc i) e.baseSet := by
    intro i b hb
    exact (contMDiffAt_localFrame_coeff bE hb (hΔ b) i).contMDiffWithinAt

  obtain ⟨Sglob, hSglob_eq⟩ := exists_contMDiffSection_eqOn_nhd (I := I)
    (V := fun z : M => TangentSpace I z) (n := (⊤ : ℕ∞)) (s := sLoc)
    (fun i => (hsLoc_on i).of_le (by exact_mod_cast le_top)) hbase_open hx_base

  have hfglob : ∀ i, ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] cLoc i :=
    fun i => exists_global_smooth_eqOn_nhd_scalar hbase_open hx_base (hcLoc_on i)
  choose fglob hfglob_smooth hfglob_eq using hfglob

  set Ssec : Module.Basis.ofVectorSpaceIndex ℝ E → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    fun i => Sglob i with hSsec_def
  set fbun : Module.Basis.ofVectorSpaceIndex ℝ E → C^∞⟮I, M; ℝ⟯ :=
    fun i => ⟨fglob i, hfglob_smooth i⟩ with hfbun_def
  have hfbun_coe : ∀ i, (fbun i : M → ℝ) = fglob i := fun i => rfl

  have hYY' : ∀ᶠ b in 𝓝 x, Δ b = (∑ i, fbun i • Ssec i) b := by
    filter_upwards [hexpand, hSglob_eq, Filter.eventually_all.mpr hfglob_eq] with b hbexp hbS hbf
    rw [hbexp, ContMDiffSection.finset_sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hval : (fbun i • Ssec i) b = fglob i b • (Ssec i : Π z : M, TangentSpace I z) b := rfl
    rw [hval, hbf i]
    have hSb : (Ssec i : Π z : M, TangentSpace I z) b = sLoc i b := hbS i
    rw [hSb]

  have hcomb_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% ((∑ i, fbun i • Ssec i :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : Π b : M, TangentSpace I b)) :=
    (∑ i, fbun i • Ssec i).contMDiff

  rw [nablaCurvSec_eq_of_Y_eventuallyEq (g := g) X.contMDiff hΔ hcomb_smooth
    Z.contMDiff W.contMDiff hYY']

  rw [nablaCurvSec_finsetSum_right (g := g) Finset.univ X
    (fun i => fbun i • Ssec i) Z W x]
  apply Finset.sum_eq_zero
  intro i _
  rw [show (fun b => (fbun i • Ssec i) b) =
      ((fbun i : M → ℝ) • fun b => (Ssec i : Π z : M, TangentSpace I z) b) from rfl,
    nablaCurvSec_smul_right (g := g) (by rw [hfbun_coe]; exact hfglob_smooth i) X (Ssec i) Z W x]
  have hfix : (fbun i : M → ℝ) x = 0 := by
    rw [hfbun_coe, (hfglob_eq i).self_of_nhds, hcLoc_def]
    simp only [hΔx, map_zero]
  rw [hfix, zero_smul]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_eq_of_secondSlot_eq
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hYY' : (Y : Π b : M, TangentSpace I b) x = Y' x) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y' b) (fun b => Z b)
        (fun b => W b) x := by
  classical
  have hsplit := nablaCurvSec_add_right (g := g) X Y' (Y - Y') Z W x
  have hfun : (fun b => (Y' + (Y - Y')) b) = (fun b => Y b) := by
    funext b
    simp only [ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply]
    abel
  rw [hfun] at hsplit
  have hvanish : nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => (Y - Y') b)
      (fun b => Z b) (fun b => W b) x = 0 := by
    refine nablaCurvSec_vanish_secondSlot (g := g) X Z W (Δ := fun b => (Y - Y') b)
      (Y - Y').contMDiff ?_
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, hYY', sub_self]
  rw [hsplit, hvanish, add_zero]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_eq_of_firstSlot_eq
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hXX' : (X : Π b : M, TangentSpace I b) x = X' x) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X' b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  rw [nablaCurvSec_def, nablaCurvSec_def]

  rw [show (X : Π b : M, TangentSpace I b) x = X' x from hXX']

  have hcov_eq : ∀ (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      (covApply cov (fun b => X b) (fun b => V b)) x =
        (covApply cov (fun b => X' b) (fun b => V b)) x := by
    intro V
    simp only [covApply_apply, hXX']

  have hT2 : riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
        (fun b => W b) x =
      riemannSec cov (covApply cov (fun b => X' b) (fun b => Y b)) (fun b => Z b)
        (fun b => W b) x := by
    rw [← riemannOp_apply_smooth (cov := cov)
        (covApply_contMDiff (cov := cov) X.contMDiff Y.contMDiff) Z.contMDiff W.contMDiff,
      ← riemannOp_apply_smooth (cov := cov)
        (covApply_contMDiff (cov := cov) X'.contMDiff Y.contMDiff) Z.contMDiff W.contMDiff,
      hcov_eq Y]

  have hT3 : riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
        (fun b => W b) x =
      riemannSec cov (fun b => Y b) (covApply cov (fun b => X' b) (fun b => Z b))
        (fun b => W b) x := by
    rw [← riemannOp_apply_smooth (cov := cov) Y.contMDiff
        (covApply_contMDiff (cov := cov) X.contMDiff Z.contMDiff) W.contMDiff,
      ← riemannOp_apply_smooth (cov := cov) Y.contMDiff
        (covApply_contMDiff (cov := cov) X'.contMDiff Z.contMDiff) W.contMDiff,
      hcov_eq Z]

  have hT4 : riemannSec cov (fun b => Y b) (fun b => Z b) (covApply cov (fun b => X b) (fun b => W b)) x =
      riemannSec cov (fun b => Y b) (fun b => Z b) (covApply cov (fun b => X' b) (fun b => W b)) x := by
    rw [← riemannOp_apply_smooth (cov := cov) Y.contMDiff Z.contMDiff
        (covApply_contMDiff (cov := cov) X.contMDiff W.contMDiff),
      ← riemannOp_apply_smooth (cov := cov) Y.contMDiff Z.contMDiff
        (covApply_contMDiff (cov := cov) X'.contMDiff W.contMDiff),
      hcov_eq W]
  rw [hT2, hT3, hT4]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaBaseSlotCurv_eq_of_leftMid
    (g : SmoothRiemannianMetric I M)
    (X X' Y Y' Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hXX' : (X : Π b : M, TangentSpace I b) x = X' x)
    (hYY' : (Y : Π b : M, TangentSpace I b) x = Y' x) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x u = nablaBaseSlotCurv (I := I) g X' Y' Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
  exact (nablaCurvSec_eq_of_firstSlot_eq (g := g) X X' Y Z
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
        (smoothExtensionTangent_contMDiff (I := I) x u)) x hXX').trans
    (nablaCurvSec_eq_of_secondSlot_eq (g := g) X' Y Y' Z
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
        (smoothExtensionTangent_contMDiff (I := I) x u)) x hYY')

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_eq_of_pointwise_eq_leftMid
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X X' Y Y' Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (hX_eq : X x = X' x) (hY_eq : Y x = Y' x) :
    nablaTensor0SCurv (I := I) g s X Y Z A x = nablaTensor0SCurv (I := I) g s X' Y' Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro u
  rw [nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X' Y' Z A hA x u]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun k _ => ?_))
  rw [nablaBaseSlotCurv_eq_of_leftMid (I := I) g X X' Y Y' Z x hX_eq hY_eq (u k)]

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_add_left
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X X' Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        (X + X') Y Z A x =
      nablaTensor0SCurv (I := I) g s X Y Z A x + nablaTensor0SCurv (I := I) g s X' Y Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_add]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.add_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s (X + X') Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X' Y Z A hA x u]
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_add_left (I := I) g X X' Y Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_add u k
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))
    (nablaBaseSlotCurv (I := I) g X' Y Z x (u k))

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_smul_left
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        (c • X) Y Z A x =
      c • nablaTensor0SCurv (I := I) g s X Y Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.smul_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s (c • X) Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u]
  rw [smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_smul_left (I := I) g c X Y Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_smul u k c
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_add_mid
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Y' Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        X (Y + Y') Z A x =
      nablaTensor0SCurv (I := I) g s X Y Z A x + nablaTensor0SCurv (I := I) g s X Y' Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_add]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.add_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s X (Y + Y') Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y' Z A hA x u]
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_add_right (I := I) g X Y Y' Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_add u k
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))
    (nablaBaseSlotCurv (I := I) g X Y' Z x (u k))

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_smul_mid
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        X (c • Y) Z A x =
      c • nablaTensor0SCurv (I := I) g s X Y Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.smul_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s X (c • Y) Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u]
  rw [smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_smul_right (I := I) g c X Y Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_smul u k c
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))

def nablaTensor0SCurvBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] Tensor0SSpace s I x :=
  LinearMap.mk₂ ℝ
    (fun v w => nablaTensor0SCurv (I := I) g s
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent_contMDiff (I := I) x v))
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
        (smoothExtensionTangent_contMDiff (I := I) x w)) Z A x)
    (fun v v' w => by
      dsimp only
      have hadd : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (v + v'))
            (smoothExtensionTangent_contMDiff (I := I) x (v + v'))) x =
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x v')
              (smoothExtensionTangent_contMDiff (I := I) x v')) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add, Pi.add_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (v + v'))
            (smoothExtensionTangent_contMDiff (I := I) x (v + v')))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x v')
              (smoothExtensionTangent_contMDiff (I := I) x v'))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) Z A hA x hadd rfl]
      exact nablaTensor0SCurv_add_left (I := I) g s _ _ _ Z A hA x)
    (fun c v w => by
      dsimp only
      have hsmul : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • v))
            (smoothExtensionTangent_contMDiff (I := I) x (c • v))) x =
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v)) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_smul, Pi.smul_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • v))
            (smoothExtensionTangent_contMDiff (I := I) x (c • v)))
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) Z A hA x hsmul rfl]
      exact nablaTensor0SCurv_smul_left (I := I) g s c _ _ Z A hA x)
    (fun v w w' => by
      dsimp only
      have hadd : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (w + w'))
            (smoothExtensionTangent_contMDiff (I := I) x (w + w'))) x =
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x w')
              (smoothExtensionTangent_contMDiff (I := I) x w')) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add, Pi.add_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (w + w'))
            (smoothExtensionTangent_contMDiff (I := I) x (w + w')))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x w')
              (smoothExtensionTangent_contMDiff (I := I) x w')) Z A hA x rfl hadd]
      exact nablaTensor0SCurv_add_mid (I := I) g s _ _ _ Z A hA x)
    (fun c v w => by
      dsimp only
      have hsmul : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • w))
            (smoothExtensionTangent_contMDiff (I := I) x (c • w))) x =
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_smul, Pi.smul_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • w))
            (smoothExtensionTangent_contMDiff (I := I) x (c • w)))
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) Z A hA x rfl hsmul]
      exact nablaTensor0SCurv_smul_mid (I := I) g s c _ _ Z A hA x)

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurvBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M)
    (v w : TangentSpace I x) :
    nablaTensor0SCurvBilin (I := I) g s Z A hA x v w =
      nablaTensor0SCurv (I := I) g s
        (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent_contMDiff (I := I) x v))
        (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent_contMDiff (I := I) x w)) Z A x := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurvBilin_apply_smooth
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurvBilin (I := I) g s Z A hA x (X x) (Y x) =
      nablaTensor0SCurv (I := I) g s X Y Z A x := by
  rw [nablaTensor0SCurvBilin_apply]
  refine nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (X x))
      (smoothExtensionTangent_contMDiff (I := I) x (X x)))
    X
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (Y x))
      (smoothExtensionTangent_contMDiff (I := I) x (Y x)))
    Y Z A hA x ?_ ?_
  · simp only [ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]
  · simp only [ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]

theorem parsevalFrame_eq_orthoFrame_diag_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x), (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (x : M) :
    (∑ a : Fin N, nablaTensor0SCurv (I := I) g s
        (ContMDiffSection.mk (V a) (hV a)) (ContMDiffSection.mk (V a) (hV a)) Z A x) =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Z A x := by
  classical
  have hconv := parseval_family_sum_bilin_eq (I := I) (M := M) g x
    (W := fun a : Fin N => V a x) (hW := fun u => hPar x u)
    (e := fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g x i x)
    (horth := fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
    (B := nablaTensor0SCurvBilin (I := I) g s Z A hA x)
  rw [Finset.sum_congr rfl (fun a _ =>
        (nablaTensor0SCurvBilin_apply_smooth (I := I) g s
          (ContMDiffSection.mk (V a) (hV a)) (ContMDiffSection.mk (V a) (hV a)) Z A hA x).symm),
      Finset.sum_congr rfl (fun i _ =>
        (nablaTensor0SCurvBilin_apply_smooth (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Z A hA x).symm)]
  simp only [ContMDiffSection.coeFn_mk]
  exact hconv

end Connection
end Integral
end DifferentialGeometry

end
