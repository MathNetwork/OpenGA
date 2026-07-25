import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantLeibniz
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic


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

noncomputable def prependCovGradSlot (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) : SmoothCcTensor g r (s + 1) :=
  covGrad (I := I) (M := M) g r s (scalarSmul (I := I) (M := M) g r s ζ S) -
    scalarSmul (I := I) (M := M) g r (s + 1) ζ
      (covGrad (I := I) (M := M) g r s S)

omit [NeZero (Module.finrank ℝ E)] in
lemma prependCovGradSlot_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) :
    (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection =
      (covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toSection -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toSection := rfl

private noncomputable def prependGradCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  (extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma prependGradCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) (v : E) :
    prependGradCLM (I := I) (M := M) g r s ζ S x v =
      (extDerivFun (I := I) (ζ : M → ℝ) x v) • S.toSection x := by
  rw [prependGradCLM, ContinuousLinearMap.smulRight_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smulRight_add_right (r s : ℕ) {x : M}
    (φ : TangentSpace I x →L[ℝ] ℝ) (t₁ t₂ : TensorRSSpace r s I x) :
    φ.smulRight (t₁ + t₂) = φ.smulRight t₁ + φ.smulRight t₂ := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    smul_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smulRight_smul_right (r s : ℕ) {x : M}
    (φ : TangentSpace I x →L[ℝ] ℝ) (c : ℝ) (t : TensorRSSpace r s I x) :
    φ.smulRight (c • t) = c • φ.smulRight t := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, smul_comm]

omit [NeZero (Module.finrank ℝ E)] in
private lemma prependGradCLM_eq_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    prependGradCLM (I := I) (M := M) g r s ζ S x =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => (scalarSmul (I := I) (M := M) g r s ζ S).toSection y) x -
        (ζ : M → ℝ) x •
          tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
            (fun y : M => S.toSection y) x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    prependGradCLM_apply]
  have hweighted :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => (scalarSmul (I := I) (M := M) g r s ζ S).toSection y) x v =
        tensorCovDerivAt (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S) x v := rfl
  have hplain :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => S.toSection y) x v =
        tensorCovDerivAt (I := I) (M := M) g r s S x v := rfl
  rw [hweighted, hplain]
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ S x v]
  rw [add_sub_cancel_left]

omit [NeZero (Module.finrank ℝ E)] in
theorem prependCovGradSlot_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x =
      covGradBundleEquiv (I := I) (M := M) r s x
        ((extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)) := by
  rw [prependCovGradSlot_toSection]
  rw [show ((covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toSection -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toSection) x =
      (covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toSection x -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toSection x from rfl]
  rw [covGrad_toSection_apply, scalarSmul_toSection_apply, covGrad_toSection_apply]
  rw [← map_smul (covGradBundleEquiv (I := I) (M := M) r s x), ← map_sub]
  rw [← prependGradCLM_eq_sub (I := I) (M := M) g r s ζ S x]
  rw [prependGradCLM]

omit [NeZero (Module.finrank ℝ E)] in
theorem prependCovGradSlot_toSection_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) • S.toSection x) D)
        (Matrix.vecTail v) := by
  rw [prependCovGradSlot_toSection_apply]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r s x
    ((extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)) D v]
  rw [ContinuousLinearMap.smulRight_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem prependCovGradSlot_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S₁ S₂ : SmoothCcTensor g r s) :
    prependCovGradSlot (I := I) (M := M) g r s ζ (S₁ + S₂) =
      prependCovGradSlot (I := I) (M := M) g r s ζ S₁ +
        prependCovGradSlot (I := I) (M := M) g r s ζ S₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((prependCovGradSlot (I := I) (M := M) g r s ζ S₁ +
        prependCovGradSlot (I := I) (M := M) g r s ζ S₂).toSection x) =
      (prependCovGradSlot (I := I) (M := M) g r s ζ S₁).toSection x +
        (prependCovGradSlot (I := I) (M := M) g r s ζ S₂).toSection x from rfl]
  rw [prependCovGradSlot_toSection_apply, prependCovGradSlot_toSection_apply,
    prependCovGradSlot_toSection_apply]
  rw [show ((S₁ + S₂).toSection x) = S₁.toSection x + S₂.toSection x from rfl,
    smulRight_add_right (I := I) r s, map_add]

omit [NeZero (Module.finrank ℝ E)] in
theorem prependCovGradSlot_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (c : ℝ) (S : SmoothCcTensor g r s) :
    prependCovGradSlot (I := I) (M := M) g r s ζ (c • S) =
      c • prependCovGradSlot (I := I) (M := M) g r s ζ S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x) =
      c • (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x from rfl]
  rw [prependCovGradSlot_toSection_apply, prependCovGradSlot_toSection_apply]
  rw [show ((c • S).toSection x) = c • S.toSection x from rfl,
    smulRight_smul_right (I := I) r s, map_smul]

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem prependCovGradSlot_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) :
    prependCovGradSlot (I := I) (M := M) g r s ζ (0 : SmoothCcTensor g r s) = 0 := by
  have h := prependCovGradSlot_smul (I := I) (M := M) g r s ζ (0 : ℝ) 0
  rwa [zero_smul, zero_smul] at h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma crossLeft_tensorRSSpace_toModel_apply
    (r s : ℕ) (x : M) (T : TensorRSSpace r s I x)
    (Dm : Tensor0SModel r ℝ E) :
    (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E from
        TensorRSSpace.toModel T) Dm =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T)
          (Tensor0SSpace.ofModel Dm)) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma crossLeft_covGrad_toModel_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (Dm : Tensor0SModel r ℝ E) (v : Fin (s + 1) → E) :
    (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s w).toSection x)) Dm v =
      (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s w x (v 0)))
        Dm (Matrix.vecTail v) := by
  change (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E from
      TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s w).toSection x)) Dm v = _
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r (s + 1) x
        ((covGrad (I := I) (M := M) g r s w).toSection x) Dm]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s w x
        (Tensor0SSpace.ofModel Dm) v]
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r s x
        (tensorCovDerivAt (I := I) (M := M) g r s w x (v 0)) Dm]

omit [NeZero (Module.finrank ℝ E)] in
private lemma crossLeft_prependCovGradSlot_toModel_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M)
    (Dm : Tensor0SModel r ℝ E) (v : Fin (s + 1) → E) :
    (TensorRSSpace.toModel
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) Dm v =
      (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) •
        ((TensorRSSpace.toModel (S.toSection x)) Dm (Matrix.vecTail v)) := by
  change (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E from
      TensorRSSpace.toModel
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) Dm v = _
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r (s + 1) x
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x) Dm]
  rw [prependCovGradSlot_toSection_apply_eval (I := I) (M := M) g r s ζ S x
        (Tensor0SSpace.ofModel Dm) v]
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) • S.toSection x)
          (Tensor0SSpace.ofModel Dm) =
      (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) •
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            S.toSection x) (Tensor0SSpace.ofModel Dm)) from rfl]
  rw [Tensor0SSpace.toModel_smul]
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r s x (S.toSection x) Dm]
  rfl

private def crossDiffSlot (r s : ℕ) : Fin (r + (s + 1)) :=
  ⟨r, by omega⟩

private lemma crossLeft_natAdd_zero_eq_diffSlot (r s : ℕ) :
    (Fin.natAdd r (0 : Fin (s + 1)) : Fin (r + (s + 1))) = crossDiffSlot r s := by
  apply Fin.ext
  simp [crossDiffSlot, Fin.natAdd]

private lemma crossDiffSlot_succAbove_castAdd (r s : ℕ) (a : Fin r) :
    (crossDiffSlot r s).succAbove (Fin.castAdd s a) = Fin.castAdd (s + 1) a := by
  apply Fin.ext
  have hcond : (Fin.castSucc (Fin.castAdd s a) : Fin (r + (s + 1)))
      < crossDiffSlot r s := by
    rw [Fin.lt_def]
    simp only [Fin.val_castSucc, Fin.val_castAdd, crossDiffSlot]
    exact a.isLt
  rw [Fin.succAbove, if_pos hcond]
  simp only [Fin.val_castSucc, Fin.val_castAdd]

private lemma crossDiffSlot_succAbove_natAdd (r s : ℕ) (a : Fin s) :
    (crossDiffSlot r s).succAbove (Fin.natAdd r a) =
      Fin.natAdd r (Fin.succ a) := by
  apply Fin.ext
  have hcond : ¬ (Fin.castSucc (Fin.natAdd r a) : Fin (r + (s + 1)))
      < crossDiffSlot r s := by
    rw [Fin.lt_def, not_lt]
    simp only [Fin.val_castSucc, Fin.val_natAdd, crossDiffSlot]
    omega
  rw [Fin.succAbove, if_neg hcond]
  simp only [Fin.val_succ, Fin.val_natAdd]
  omega

omit [NeZero (Module.finrank ℝ E)] in
private lemma crossLeft_lower_covGrad_insertNth_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (i : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s w).toSection x))
        (fun a : Fin (r + (s + 1)) => (chartModelBasis E)
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s w x
            ((chartModelBasis E) k)))
        (fun a : Fin (r + s) => (chartModelBasis E) (i a)) := by
  classical
  set I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E) :=
    Fin.insertNth (crossDiffSlot r s) k i with hI'
  rw [lowerAllUpperIndices_apply, lowerAllUpperIndices_apply]
  have hdir : (chartModelBasis E) (I' (Fin.natAdd r (0 : Fin (s + 1)))) =
      (chartModelBasis E) k := by
    rw [crossLeft_natAdd_zero_eq_diffSlot, hI', Fin.insertNth_apply_same]
  have hupper : (fun a : Fin r =>
        (chartModelBasis E) (I' (Fin.castAdd (s + 1) a))) =
      (fun a : Fin r => (chartModelBasis E) (i (Fin.castAdd s a))) := by
    funext a
    show (chartModelBasis E) (I' (Fin.castAdd (s + 1) a)) =
      (chartModelBasis E) (i (Fin.castAdd s a))
    rw [← crossDiffSlot_succAbove_castAdd r s a, hI',
      Fin.insertNth_apply_succAbove]
  have hcov : Matrix.vecTail
        (fun j : Fin (s + 1) => (chartModelBasis E) (I' (Fin.natAdd r j))) =
      (fun a : Fin s => (chartModelBasis E) (i (Fin.natAdd r a))) := by
    funext a
    change (chartModelBasis E) (I' (Fin.natAdd r (Fin.succ a))) =
      (chartModelBasis E) (i (Fin.natAdd r a))
    rw [← crossDiffSlot_succAbove_natAdd r s a, hI',
      Fin.insertNth_apply_succAbove]
  rw [crossLeft_covGrad_toModel_apply (I := I) (M := M) g r s w x
        (separableFormAt (I := I) (M := M) g x r
          (fun a : Fin r => (chartModelBasis E) (I' (Fin.castAdd (s + 1) a))))
        (fun j : Fin (s + 1) => (chartModelBasis E) (I' (Fin.natAdd r j)))]
  rw [hdir, hupper, hcov]

omit [NeZero (Module.finrank ℝ E)] in
private lemma crossLeft_lower_prependCovGradSlot_insertNth_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M)
    (l : Fin (Module.finrank ℝ E))
    (j : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x))
        (fun a : Fin (r + (s + 1)) => (chartModelBasis E)
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) l)) *
        lowerAllUpperIndices (I := I) (M := M) g r s x
          (TensorRSSpace.toModel (S.toSection x))
          (fun a : Fin (r + s) => (chartModelBasis E) (j a)) := by
  classical
  set J' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E) :=
    Fin.insertNth (crossDiffSlot r s) l j with hJ'
  rw [lowerAllUpperIndices_apply, lowerAllUpperIndices_apply]
  have hdir : (chartModelBasis E) (J' (Fin.natAdd r (0 : Fin (s + 1)))) =
      (chartModelBasis E) l := by
    rw [crossLeft_natAdd_zero_eq_diffSlot, hJ', Fin.insertNth_apply_same]
  have hupper : (fun a : Fin r =>
        (chartModelBasis E) (J' (Fin.castAdd (s + 1) a))) =
      (fun a : Fin r => (chartModelBasis E) (j (Fin.castAdd s a))) := by
    funext a
    show (chartModelBasis E) (J' (Fin.castAdd (s + 1) a)) =
      (chartModelBasis E) (j (Fin.castAdd s a))
    rw [← crossDiffSlot_succAbove_castAdd r s a, hJ',
      Fin.insertNth_apply_succAbove]
  have hcov : Matrix.vecTail
        (fun a : Fin (s + 1) => (chartModelBasis E) (J' (Fin.natAdd r a))) =
      (fun a : Fin s => (chartModelBasis E) (j (Fin.natAdd r a))) := by
    funext a
    change (chartModelBasis E) (J' (Fin.natAdd r (Fin.succ a))) =
      (chartModelBasis E) (j (Fin.natAdd r a))
    rw [← crossDiffSlot_succAbove_natAdd r s a, hJ',
      Fin.insertNth_apply_succAbove]
  rw [crossLeft_prependCovGradSlot_toModel_apply (I := I) (M := M) g r s ζ S x
        (separableFormAt (I := I) (M := M) g x r
          (fun a : Fin r => (chartModelBasis E) (J' (Fin.castAdd (s + 1) a))))
        (fun a : Fin (s + 1) => (chartModelBasis E) (J' (Fin.natAdd r a)))]
  rw [hdir, hupper, hcov, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma crossLeft_gramInv_prod_insertNth_split
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    (k l : Fin (Module.finrank ℝ E))
    (i j : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    (∏ a : Fin (r + (s + 1)),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ k l *
        ∏ a : Fin (r + s),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a) := by
  rw [show (∏ a : Fin (r + (s + 1)),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) (crossDiffSlot r s))
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) (crossDiffSlot r s)) *
        ∏ a : Fin (r + s),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹
            ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
              Fin (Module.finrank ℝ E)) ((crossDiffSlot r s).succAbove a))
            ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
              Fin (Module.finrank ℝ E)) ((crossDiffSlot r s).succAbove a))
      from Fin.prod_univ_succAbove _ (crossDiffSlot r s)]
  rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma crossLeft_sum_reindex_diffSlot (r s : ℕ)
    (F : (Fin (r + (s + 1)) → Fin (Module.finrank ℝ E)) → ℝ) :
    ∑ I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E), F I' =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
          F (Fin.insertNth (crossDiffSlot r s) k i) := by
  have h1 : ∑ I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E), F I' =
      ∑ ki : Fin (Module.finrank ℝ E) ×
          (Fin (r + s) → Fin (Module.finrank ℝ E)),
        F (Fin.insertNth (crossDiffSlot r s) ki.1 ki.2) :=
    (Equiv.sum_comp
      (Fin.insertNthEquiv (fun _ : Fin (r + (s + 1)) => Fin (Module.finrank ℝ E))
        (crossDiffSlot r s)) F).symm
  rw [h1, Fintype.sum_prod_type]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x =
      tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s w).toSection x))
        (TensorRSSpace.toModel
          ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) := by
  classical
  set Ginv := (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv_def
  set lowW : Fin (Module.finrank ℝ E) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
    fun k => lowerAllUpperIndices (I := I) (M := M) g r s x
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s w x ((chartModelBasis E) k)))
    with hlowW_def
  set lowS : ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
    lowerAllUpperIndices (I := I) (M := M) g r s x
      (TensorRSSpace.toModel (S.toSection x))
    with hlowS_def
  set common : ℝ :=
    ∑ k : Fin (Module.finrank ℝ E),
      ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ j : Fin (r + s) → Fin (Module.finrank ℝ E),
            Ginv k l *
              ((∏ a : Fin (r + s), Ginv (i a) (j a)) *
                (lowW k) (fun a => (chartModelBasis E) (i a)) *
                  ((extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) l)) *
                    lowS (fun a => (chartModelBasis E) (j a))))
    with hcommon_def
  have hLHS : tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x =
      common := by
    rw [tensorCovDerivCrossLeft_def]
    have hexpand : ∀ k l : Fin (Module.finrank ℝ E),
        Ginv k l *
            (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) l) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s w x
                    ((chartModelBasis E) k)))
                (S.toFun x)) =
          ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
            ∑ j : Fin (r + s) → Fin (Module.finrank ℝ E),
              Ginv k l *
                ((∏ a : Fin (r + s), Ginv (i a) (j a)) *
                  (lowW k) (fun a => (chartModelBasis E) (i a)) *
                    ((extDerivFun (I := I) (ζ : M → ℝ) x
                        ((chartModelBasis E) l)) *
                      lowS (fun a => (chartModelBasis E) (j a)))) := by
      intro k l
      rw [show tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) k)))
              (S.toFun x) =
            covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (lowW k) lowS from by
        rw [hlowW_def, hlowS_def]
        rfl]
      rw [tensorInnerPointwise_0s_eq_sum]
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun l _ => hexpand k l))]
    rw [hcommon_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
  have hRHS : tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s w).toSection x))
        (TensorRSSpace.toModel
          ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) =
      common := by
    rw [show tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
            (TensorRSSpace.toModel
              ((covGrad (I := I) (M := M) g r s w).toSection x))
            (TensorRSSpace.toModel
              ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) =
          covariantTensorInnerPointwise (I := I) (M := M) (r + (s + 1)) g x
            (lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel
                ((covGrad (I := I) (M := M) g r s w).toSection x)))
            (lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel
                ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)))
        from rfl]
    rw [tensorInnerPointwise_0s_eq_sum]
    rw [crossLeft_sum_reindex_diffSlot]
    rw [hcommon_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [crossLeft_sum_reindex_diffSlot]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [crossLeft_gramInv_prod_insertNth_split (I := I) (M := M) g x r s k l i j]
    rw [crossLeft_lower_covGrad_insertNth_basis (I := I) (M := M) g r s w x k i]
    rw [crossLeft_lower_prependCovGradSlot_insertNth_basis
          (I := I) (M := M) g r s ζ S x l j]
    rw [hlowW_def, hlowS_def]
    ring
  rw [hLHS, hRHS]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
