import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensorRS_eq_of_toModel_eval_eq {r a : ℕ} {x : M}
    {T T' : TensorRSSpace r a I x}
    (h : ∀ (D : Tensor0SSpace r I x) (v : Fin a → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x from T) D) v =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x from T') D) v) :
    T = T' := by
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  exact ContinuousMultilinearMap.ext (fun v => h D v)

private lemma vecTail_cons' {n : ℕ} {α : Type*} (a : α) (v : Fin n → α) :
    Matrix.vecTail (Fin.cons a v) = v := by
  funext j
  simp [Matrix.vecTail, Fin.cons_succ]

set_option backward.isDefEq.respectTransparency false in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_sum_eval {a : ℕ} {x : M} {ι : Type*} (t : Finset ι)
    (f : ι → Tensor0SSpace a I x) (v : Fin a → TangentSpace I x) :
    Tensor0SSpace.toModel (∑ i ∈ t, f i) v = ∑ i ∈ t, Tensor0SSpace.toModel (f i) v := by
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [Tensor0SSpace.toModelL_apply])

set_option backward.isDefEq.respectTransparency false in

private noncomputable def chooseCcThrough (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M)
    (T : TensorRSSpace r a I x) : SmoothCcTensor g r a where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
      Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
    letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
      (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma chooseCcThrough_eq (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M)
    (T : TensorRSSpace r a I x) :
    (chooseCcThrough (I := I) (M := M) g r a x T).toSection x = T :=
  letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
  letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
    (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x T)

set_option backward.isDefEq.respectTransparency false in

private noncomputable def curryLastTwoTensorSlots (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x :=
  (((covGradBundleEquiv (I := I) (M := M) r t x).symm :
      TensorRSSpace r (t + 1) I x ≃L[ℝ] (TangentSpace I x →L[ℝ] TensorRSSpace r t I x))
        : TensorRSSpace r (t + 1) I x →L[ℝ] (TangentSpace I x →L[ℝ] TensorRSSpace r t I x)).comp
    ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma twoSlotPeel_eval (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x)
    (u w : TangentSpace I x) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          curryLastTwoTensorSlots (I := I) (M := M) r t x T u w) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
        (Fin.cons u (Fin.cons w m)) := by
  have h1 : curryLastTwoTensorSlots (I := I) (M := M) r t x T u w =
      (covGradBundleEquiv (I := I) (M := M) r t x).symm
        ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T u) w := by
    rw [curryLastTwoTensorSlots, ContinuousLinearMap.comp_apply]
    rfl
  rw [h1]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r t x
    ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T u) w D m]
  exact covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r (t + 1) x T u D (Fin.cons w m)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma twoSlotPeel_add (r t : ℕ) (x : M) (T T' : TensorRSSpace r (t + 2) I x) :
    curryLastTwoTensorSlots (I := I) (M := M) r t x (T + T') =
      curryLastTwoTensorSlots (I := I) (M := M) r t x T + curryLastTwoTensorSlots (I := I) (M := M) r t x T' := by
  rw [curryLastTwoTensorSlots, curryLastTwoTensorSlots, curryLastTwoTensorSlots,
    map_add ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm) T T',
    ContinuousLinearMap.comp_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma twoSlotPeel_smul (r t : ℕ) (x : M) (c : ℝ) (T : TensorRSSpace r (t + 2) I x) :
    curryLastTwoTensorSlots (I := I) (M := M) r t x (c • T) =
      c • curryLastTwoTensorSlots (I := I) (M := M) r t x T := by
  rw [curryLastTwoTensorSlots, curryLastTwoTensorSlots,
    map_smul ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm) c T,
    ContinuousLinearMap.comp_smul]

section Bridge

variable (g : SmoothRiemannianMetric I M)

set_option backward.isDefEq.respectTransparency false in

private noncomputable def covApplyCcSec (r t : ℕ) (W : SmoothCcTensor g r t)
    {Y : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    Cₛ^∞⟮I; TensorRSModel r t ℝ E, (fun x : M => TensorRSSpace r t I x)⟯ where
  toFun := fun y : M =>
    covApply (tensorCov (I := I) g r t) Y (fun z : M => W.toSection z) y
  contMDiff_toFun :=
    covApplyRS_contMDiff (I := I) g r t W.toSection.contMDiff_toFun hY
set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem secondCovGrad_eval_eq_tensorSecondCovDeriv (r t : ℕ)
    (W : SmoothCcTensor g r t)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (x : M) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
          (covGrad (I := I) (M := M) g r (t + 1)
            (covGrad (I := I) (M := M) g r t W)).toSection x) D)
        (Fin.cons (X x) (Fin.cons (Y x) m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g r t X Y (fun y : M => W.toSection y) x) D) m := by
  classical
  obtain ⟨w, hwx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := Tensor0SModel r ℝ E)
    (V := fun z : M => Tensor0SSpace r I z) (n := (⊤ : ℕ∞)) x D
  subst hwx
  set GW : SmoothCcTensor g r (t + 1) := covGrad (I := I) (M := M) g r t W with hGW_def

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r (t + 1) GW x (w x)
    (Fin.cons (X x) (Fin.cons (Y x) m))]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' (X x) (Fin.cons (Y x) m)]

  have happly₁ : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g r (t + 1) GW x (X x)) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
          (fun y : M =>
            (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
              GW.toSection y) (w y)) x (X x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from GW.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w x (X x)) :=
    TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r (t + 1)
      (LeviCivita (I := I) g) GW.toSection w x (X x)
  rw [happly₁, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

  have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (t + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (t + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (t + 1) I z) y
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y))) :=
    ContMDiff.clm_bundle_apply (b := id) GW.toSection.contMDiff w.contMDiff
  have hP_curried : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel t ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace t I z) y
        (Tensor0SNabla.curriedSection I M
          (fun y' : M =>
            (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
              GW.toSection y') (w y')) y)) x :=
    TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y)) x (hP_smooth x)

  rw [show Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
            GW.toSection y) (w y)) x (X x))
      (Fin.cons (Y x) m) =
    Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
        (Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
          (fun y : M =>
            (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
              GW.toSection y) (w y)) x (X x)) (Y x)) m from
    (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
            GW.toSection y) (w y)) x (X x)) (v0 := Y x) (vs := m)).symm]
  have habs : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
      (Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
            GW.toSection y) (w y)) x (X x))) (Y x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun y' : M =>
              (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
                GW.toSection y') (w y')) y (Y y)) x (X x) -
        Tensor0SNabla.curriedSection I M
          (fun y' : M =>
            (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
              GW.toSection y') (w y')) x ((LeviCivita (I := I) g).toFun Y x (X x)) :=
    curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g t
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y))
      (Vfield := X) (Y := Y) (x := x)
      (hP_curried.mdifferentiableAt (by simp))
      ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))
  rw [habs, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

  have hsec : (fun y : M => Tensor0SNabla.curriedSection I M
      (fun y' : M =>
        (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
          GW.toSection y') (w y')) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          covApply (tensorCov (I := I) g r t) Y (fun z : M => W.toSection z) y) (w y)) := by
    funext y
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m'
    rw [show Tensor0SNabla.curriedSection I M
        (fun y' : M =>
          (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
            GW.toSection y') (w y')) y =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t y
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y)) from rfl]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
        GW.toSection y) (w y)) (v0 := Y y) (vs := m')]
    have hgw := covGrad_toSection_apply_eval (I := I) (M := M) g r t W y (w y)
      (Fin.cons (Y y) m')
    rw [hGW_def]
    rw [hgw]
    simp only [Fin.cons_zero]
    rw [vecTail_cons' (Y y) m']
    rfl
  rw [hsec]

  have happly₂ : Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          covApply (tensorCov (I := I) g r t) Y (fun z : M => W.toSection z) y) (w y)) x (X x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
          (covApplyCcSec (I := I) (M := M) g r t W hY) x (X x)) (w x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          tensorCovDerivAt (I := I) (M := M) g r t W x (Y x))
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w x (X x)) := by
    have h : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
          (covApplyCcSec (I := I) (M := M) g r t W hY) x (X x)) (w x) =
        Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)
          (fun y : M =>
            (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
              covApply (tensorCov (I := I) g r t) Y (fun z : M => W.toSection z) y) (w y))
          x (X x) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
            tensorCovDerivAt (I := I) (M := M) g r t W x (Y x))
            (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              w x (X x)) :=
      TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r t
        (LeviCivita (I := I) g) (covApplyCcSec (I := I) (M := M) g r t W hY) w x (X x)
    exact sub_eq_iff_eq_add.mp h.symm
  rw [happly₂, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

  have hPb : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from GW.toSection x)
        (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w x (X x)))
      (Fin.cons (Y x) m) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          tensorCovDerivAt (I := I) (M := M) g r t W x (Y x))
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
            w x (X x))) m := by
    have hgw := covGrad_toSection_apply_eval (I := I) (M := M) g r t W x
      (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w x (X x))
      (Fin.cons (Y x) m)
    rw [hGW_def]
    rw [hgw]
    simp only [Fin.cons_zero]
    rw [vecTail_cons' (Y x) m]
  rw [hPb]

  have hC₁ : Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M
        (fun y' : M =>
          (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
            GW.toSection y') (w y')) x ((LeviCivita (I := I) g).toFun Y x (X x))) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          tensorCovDerivAt (I := I) (M := M) g r t W x
            ((LeviCivita (I := I) g).toFun Y x (X x))) (w x)) m := by
    rw [show Tensor0SNabla.curriedSection I M
        (fun y' : M =>
          (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
            GW.toSection y') (w y')) x =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from
          GW.toSection x) (w x)) from rfl]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from
        GW.toSection x) (w x)) (v0 := (LeviCivita (I := I) g).toFun Y x (X x)) (vs := m)]
    have hgw := covGrad_toSection_apply_eval (I := I) (M := M) g r t W x (w x)
      (Fin.cons ((LeviCivita (I := I) g).toFun Y x (X x)) m)
    rw [hGW_def]
    rw [hgw]
    simp only [Fin.cons_zero]
    rw [vecTail_cons' ((LeviCivita (I := I) g).toFun Y x (X x)) m]
  rw [hC₁]

  have hSCD : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
      tensorSecondCovDeriv (I := I) g r t X Y (fun y : M => W.toSection y) x) (w x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
          (covApplyCcSec (I := I) (M := M) g r t W hY) x (X x)) (w x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          tensorCovDerivAt (I := I) (M := M) g r t W x
            ((LeviCivita (I := I) g).toFun Y x (X x))) (w x) := rfl
  rw [hSCD, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  ring

end Bridge

set_option backward.isDefEq.respectTransparency false in

private noncomputable def tangentBilinFlip {r t : ℕ} {x : M}
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : T2Space (TensorRSSpace r t I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun a => LinearMap.toContinuousLinearMap
        { toFun := fun b => P b a
          map_add' := fun b b' => by rw [map_add, ContinuousLinearMap.add_apply]
          map_smul' := fun c b => by rw [map_smul, ContinuousLinearMap.smul_apply]; rfl }
      map_add' := fun a a' => by
        refine ContinuousLinearMap.ext (fun b => ?_)
        change P b (a + a') = _
        rw [map_add (P b), ContinuousLinearMap.add_apply]
        rfl
      map_smul' := fun c a => by
        refine ContinuousLinearMap.ext (fun b => ?_)
        change P b (c • a) = _
        rw [map_smul (P b), ContinuousLinearMap.smul_apply]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tangentBilinFlip_apply {r t : ℕ} {x : M}
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x)
    (a b : TangentSpace I x) :
    tangentBilinFlip (I := I) (M := M) P a b = P b a := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tangentBilinFlip_add {r t : ℕ} {x : M}
    (P P' : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    tangentBilinFlip (I := I) (M := M) (P + P') =
      tangentBilinFlip (I := I) (M := M) P + tangentBilinFlip (I := I) (M := M) P' := by
  refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
  have h1 : tangentBilinFlip (I := I) (M := M) (P + P') a b = (P + P') b a :=
    tangentBilinFlip_apply (P + P') a b
  have h2 : ((tangentBilinFlip (I := I) (M := M) P +
      tangentBilinFlip (I := I) (M := M) P') a) b = P b a + P' b a := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      tangentBilinFlip_apply, tangentBilinFlip_apply]
  rw [h1, h2, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tangentBilinFlip_smul {r t : ℕ} {x : M} (c : ℝ)
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    tangentBilinFlip (I := I) (M := M) (c • P) =
      c • tangentBilinFlip (I := I) (M := M) P := by
  refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
  have h1 : tangentBilinFlip (I := I) (M := M) (c • P) a b = (c • P) b a :=
    tangentBilinFlip_apply (c • P) a b
  have h2 : ((c • tangentBilinFlip (I := I) (M := M) P) a) b = c • P b a := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      tangentBilinFlip_apply]
  rw [h1, h2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in

private noncomputable def swapTwoFib (r t : ℕ) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun T =>
        covGradBundleEquiv (I := I) (M := M) r (t + 1) x
          ((((covGradBundleEquiv (I := I) (M := M) r t x) :
              (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x)
                : (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
                  TensorRSSpace r (t + 1) I x).comp
            (tangentBilinFlip (I := I) (M := M) (curryLastTwoTensorSlots (I := I) (M := M) r t x T)))
      map_add' := fun T T' => by
        rw [twoSlotPeel_add, tangentBilinFlip_add, ContinuousLinearMap.comp_add,
          map_add (covGradBundleEquiv (I := I) (M := M) r (t + 1) x)]
      map_smul' := fun c T => by
        rw [twoSlotPeel_smul, tangentBilinFlip_smul, ContinuousLinearMap.comp_smul,
          map_smul (covGradBundleEquiv (I := I) (M := M) r (t + 1) x)]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma swapTwoFib_apply (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x) :
    swapTwoFib (I := I) (M := M) r t x T =
      covGradBundleEquiv (I := I) (M := M) r (t + 1) x
        ((((covGradBundleEquiv (I := I) (M := M) r t x) :
            (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x)
              : (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
                TensorRSSpace r (t + 1) I x).comp
          (tangentBilinFlip (I := I) (M := M) (curryLastTwoTensorSlots (I := I) (M := M) r t x T))) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma swapTwoFib_eval (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x)
    (a b : TangentSpace I x) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
          swapTwoFib (I := I) (M := M) r t x T) D) (Fin.cons a (Fin.cons b m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
        (Fin.cons b (Fin.cons a m)) := by
  rw [swapTwoFib_apply]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r (t + 1) x _ D
    (Fin.cons a (Fin.cons b m))]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' a (Fin.cons b m)]
  rw [show ((((covGradBundleEquiv (I := I) (M := M) r t x) :
      (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x)
        : (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
          TensorRSSpace r (t + 1) I x).comp
      (tangentBilinFlip (I := I) (M := M) (curryLastTwoTensorSlots (I := I) (M := M) r t x T))) a =
    covGradBundleEquiv (I := I) (M := M) r t x
      (tangentBilinFlip (I := I) (M := M) (curryLastTwoTensorSlots (I := I) (M := M) r t x T) a)
    from rfl]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r t x _ D (Fin.cons b m)]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' b m]
  rw [tangentBilinFlip_apply]
  exact twoSlotPeel_eval (I := I) (M := M) r t x T b a D m

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem swapTwoFib_contMDiff (r t : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r (t + 2) I z) x
        (swapTwoFib (I := I) (M := M) r t x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (t + 2) I z)
    (V₂ := fun z : M => TensorRSSpace r (t + 2) I z)
    (φ := fun x => swapTwoFib (I := I) (M := M) r t x)
  intro Z
  have hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r (t + 1) I z) x
        ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x))) :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r (t + 1)).comp Z.contMDiff
  have hΨ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r (t + 1) I z) x
        ((((covGradBundleEquiv (I := I) (M := M) r t x) :
            (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x)
              : (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
                TensorRSSpace r (t + 1) I x).comp
          (tangentBilinFlip (I := I) (M := M)
            (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x))))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r (t + 1) I z)
      (φ := fun x =>
        ((((covGradBundleEquiv (I := I) (M := M) r t x) :
            (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x)
              : (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
                TensorRSSpace r (t + 1) I x).comp
          (tangentBilinFlip (I := I) (M := M)
            (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)))))
    intro Yv
    have hflip : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r t ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r t ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r t I z) x
          (tangentBilinFlip (I := I) (M := M)
            (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))) := by
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r t I z)
        (φ := fun x => tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))
      intro Yu
      have h1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 1) ℝ E)
            (E := fun z : M => TensorRSSpace r (t + 1) I z) x
            ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x) (Yu x))) :=
        ContMDiff.clm_bundle_apply (b := id) hA Yu.contMDiff
      have h2 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r t ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r t ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r t I z) x
            ((covGradBundleEquiv (I := I) (M := M) r t x).symm
              ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x) (Yu x)))) :=
        (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r t).comp h1
      have h3 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
            (E := fun z : M => TensorRSSpace r t I z) x
            ((covGradBundleEquiv (I := I) (M := M) r t x).symm
              ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x) (Yu x)) (Yv x))) :=
        ContMDiff.clm_bundle_apply (b := id) h2 Yv.contMDiff
      refine h3.congr ?_
      intro x
      rfl
    letI : NormedAddCommGroup (TensorRSModel r (t + 1) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 1)
    letI : NormedSpace ℝ (TensorRSModel r (t + 1) ℝ E) :=
      tensorRSModel_normedSpace r (t + 1)
    letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 1) ℝ E)
        (fun y : M => TensorRSSpace r (t + 1) I y)) :=
      tensorRSBundle_topology r (t + 1)
    letI : FiberBundle (TensorRSModel r (t + 1) ℝ E)
        (fun y : M => TensorRSSpace r (t + 1) I y) :=
      tensorRSBundle_fiber r (t + 1)
    letI : VectorBundle ℝ (TensorRSModel r (t + 1) ℝ E)
        (fun y : M => TensorRSSpace r (t + 1) I y) :=
      tensorRSBundle_vector r (t + 1)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 1) ℝ E)
        (fun y : M => TensorRSSpace r (t + 1) I y) I := tensorRSBundle_smooth ∞ r (t + 1)
    have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph ∘
          (fun x : M => (⟨x, tangentBilinFlip (I := I) (M := M)
            (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x)⟩ :
            TotalSpace (E →L[ℝ] TensorRSModel r t ℝ E)
              fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r t I y))) :=
      (covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph.contMDiff.comp hflip
    refine hcomp.congr ?_
    intro x
    rw [Function.comp_apply,
      covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r t x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))]
    rfl
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E)) ∞
      ((covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph ∘
        (fun x : M => (⟨x,
          ((((covGradBundleEquiv (I := I) (M := M) r t x) :
              (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x)
                : (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
                  TensorRSSpace r (t + 1) I x).comp
            (tangentBilinFlip (I := I) (M := M)
              (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x))))⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r (t + 1) I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph.contMDiff.comp hΨ
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r (t + 1) x _]
  exact congrArg (TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E) x)
    (swapTwoFib_apply (I := I) (M := M) r t x (Z x)).symm

set_option backward.isDefEq.respectTransparency false in

private noncomputable def swapTwoSec (r t : ℕ) :
    HomTensorRSField (E := E) (M := M) r (t + 2) (t + 2) I where
  toFun := fun x : M => swapTwoFib (I := I) (M := M) r t x
  contMDiff_toFun := swapTwoFib_contMDiff (I := I) (M := M) r t

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma swapTwoSec_apply (r t : ℕ) (x : M) :
    (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
      swapTwoSec (I := I) (M := M) (E := E) r t x) = swapTwoFib (I := I) (M := M) r t x := rfl

set_option backward.isDefEq.respectTransparency false in

private noncomputable def metricDoubleTraceFib (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r t I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun V =>
        ∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x V
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)
      map_add' := fun V V' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
      map_smul' := fun c V => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply] }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricDoubleTraceFib_apply (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M)
    (V : TensorRSSpace r (t + 2) I x) :
    metricDoubleTraceFib (I := I) (M := M) g r t x V =
      ∑ i : Fin (Module.finrank ℝ E),
        curryLastTwoTensorSlots (I := I) (M := M) r t x V
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r t I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x))
  rw [metricDoubleTraceFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in

private noncomputable def metricDoubleTraceFibFixedFrame (r t : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r t I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun V =>
        ∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x V (B i x) (B i x)
      map_add' := fun V V' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
      map_smul' := fun c V => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply] }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricDoubleTraceFibFixedFrame_apply (r t : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (V : TensorRSSpace r (t + 2) I x) :
    metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x V =
      ∑ i : Fin (Module.finrank ℝ E),
        curryLastTwoTensorSlots (I := I) (M := M) r t x V (B i x) (B i x) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r (t + 2) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x))
  haveI : T2Space (TensorRSSpace r t I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x))
  rw [metricDoubleTraceFibFixedFrame, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricDoubleTraceFib_eq_fixedFrame_moving (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (x : M) :
    metricDoubleTraceFib (I := I) (M := M) g r t x =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t (smoothOrthoFrame (I := I) g x) x := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem metricDoubleTraceFibFixedFrame_contMDiff (r t : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (t + 2) I z)
    (V₂ := fun z : M => TensorRSSpace r t I z)
    (φ := fun x => metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x)
  intro Z
  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r t I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x) (B i x) (B i x))) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)

    have hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r (t + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r (t + 1) I z) x
          ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x))) :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r (t + 1)).comp Z.contMDiff
    have h1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r (t + 1) I z) x
          ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x) (B i x))) :=
      ContMDiff.clm_bundle_apply (b := id) hA (hB i)
    have h2 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r t ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r t ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r t I z) x
          ((covGradBundleEquiv (I := I) (M := M) r t x).symm
            ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x) (B i x)))) :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r t).comp h1
    have h3 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
          (E := fun z : M => TensorRSSpace r t I z) x
          ((covGradBundleEquiv (I := I) (M := M) r t x).symm
            ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm (Z x) (B i x)) (B i x))) :=
      ContMDiff.clm_bundle_apply (b := id) h2 (hB i)
    refine h3.congr ?_
    intro x
    rfl
  refine hsum.congr ?_
  intro x
  exact congrArg (TotalSpace.mk' (TensorRSModel r t ℝ E)
    (E := fun z : M => TensorRSSpace r t I z) x)
    (metricDoubleTraceFibFixedFrame_apply (I := I) (M := M) r t B x (Z x)).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem metricDoubleTraceFibFixedFrame_frame_independent (g : SmoothRiemannianMetric I M)
    (r t : ℕ)
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b} (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B y =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t C y := by
  classical
  refine ContinuousLinearMap.ext (fun V => ?_)
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D m
  have hexpand : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            metricDoubleTraceFibFixedFrame (I := I) (M := M) r t F y V) D) m =
        ∑ i : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
              curryLastTwoTensorSlots (I := I) (M := M) r t y V (F i y) (F i y)) D) m := by
    intro F
    rw [show (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          metricDoubleTraceFibFixedFrame (I := I) (M := M) r t F y V) =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (F i y) (F i y)) from
      metricDoubleTraceFibFixedFrame_apply (I := I) (M := M) r t F y V]
    rw [ContinuousLinearMap.sum_apply, toModel_sum_eval]
  rw [hexpand B, hexpand C]
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun u =>
          LinearMap.toContinuousLinearMap
            { toFun := fun w => Tensor0SSpace.toModel
                ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
                  curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m
              map_add' := fun w w' => by
                rw [map_add (curryLastTwoTensorSlots (I := I) (M := M) r t y V u), ContinuousLinearMap.add_apply,
                  Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
              map_smul' := fun c w => by
                rw [map_smul (curryLastTwoTensorSlots (I := I) (M := M) r t y V u),
                  ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
                  ContinuousMultilinearMap.smul_apply]; rfl }
        map_add' := fun u u' => by
          refine ContinuousLinearMap.ext (fun w => ?_)
          change Tensor0SSpace.toModel
              ((curryLastTwoTensorSlots (I := I) (M := M) r t y V (u + u') w) D) m =
            Tensor0SSpace.toModel ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m +
              Tensor0SSpace.toModel ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u' w) D) m
          rw [map_add (curryLastTwoTensorSlots (I := I) (M := M) r t y V), ContinuousLinearMap.add_apply,
            ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c u => by
          refine ContinuousLinearMap.ext (fun w => ?_)
          change Tensor0SSpace.toModel
              ((curryLastTwoTensorSlots (I := I) (M := M) r t y V (c • u) w) D) m =
            c • Tensor0SSpace.toModel ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m
          rw [map_smul (curryLastTwoTensorSlots (I := I) (M := M) r t y V), ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hHb_def
  have hHb_apply : ∀ u w : TangentSpace I y,
      Hb u w = Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m := by
    intro u w
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (B i y) (B i y)) D) m) =
      ∑ i : Fin (Module.finrank ℝ E), Hb (B i y) (B i y) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (B i y) (B i y)).symm)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (C i y) (C i y)) D) m) =
      ∑ i : Fin (Module.finrank ℝ E), Hb (C i y) (C i y) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (C i y) (C i y)).symm)]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    metricDoubleTraceFib (I := I) (M := M) g r t y =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t (smoothOrthoFrame (I := I) g x₀) y := by
  rw [metricDoubleTraceFib_eq_fixedFrame_moving]
  exact metricDoubleTraceFibFixedFrame_frame_independent (I := I) (M := M) g r t y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem metricDoubleTraceFib_contMDiff (g : SmoothRiemannianMetric I M) (r t : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFib (I := I) (M := M) g r t x)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I
      (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFibFixedFrame (I := I) (M := M) r t
          (smoothOrthoFrame (I := I) g x₀) x)) x₀ :=
    metricDoubleTraceFibFixedFrame_contMDiff (I := I) (M := M) r t
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
    (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) y)
    (metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd (I := I) (M := M) g r t x₀ hy)

set_option backward.isDefEq.respectTransparency false in

private noncomputable def metricDoubleTraceField (g : SmoothRiemannianMetric I M) (r : ℕ) :
    (t : ℕ) → HomTensorRSField (E := E) (M := M) r (t + 2) t I :=
  fun t =>
    { toFun := fun x : M => metricDoubleTraceFib (I := I) (M := M) g r t x
      contMDiff_toFun := metricDoubleTraceFib_contMDiff (I := I) (M := M) g r t }

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma metricDoubleTraceField_apply (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M) :
    (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x from
        metricDoubleTraceField (I := I) (M := M) (E := E) g r t x) =
      metricDoubleTraceFib (I := I) (M := M) g r t x := rfl

set_option backward.isDefEq.respectTransparency false in

private theorem roughLap_eq_metricDoubleTrace (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W : SmoothCcTensor g r t) :
    rawTensorConnLapSmooth (I := I) g r t W =
      homTensorRSFieldApply (I := I) (M := M) g r (t + 2) t (metricDoubleTraceField (I := I) (M := M) (E := E) g r t)
        (iteratedCovGrad g r t 2 W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [rawTensorConnLapSmooth_toSection_apply, appFullSec_toSection, metricDoubleTraceField_apply,
    metricDoubleTraceFib_apply]
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r t (fun z : M => W.toSection z) x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D m
  rw [twoSlotPeel_eval (I := I) (M := M) r t x ((iteratedCovGrad g r t 2 W).toSection x)
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) D m]
  rw [show (iteratedCovGrad g r t 2 W).toSection x =
      (covGrad (I := I) (M := M) g r (t + 1)
        (covGrad (I := I) (M := M) g r t W)).toSection x from rfl]
  exact (secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r t W
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i) x D m).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciDefect_eval (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W : SmoothCcTensor g r t) (x : M) (D : Tensor0SSpace r I x)
    (v0 v1 : TangentSpace I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
          (iteratedCovGrad g r t 2 W -
            homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r t)
              (iteratedCovGrad g r t 2 W)).toSection x) D)
        (Fin.cons v0 (Fin.cons v1 m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          riemannOp (tensorCov (I := I) g r t) x v0 v1 (W.toSection x)) D) m := by
  classical
  set X : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v0 with hX_def
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v1 with hY_def
  have hXx : X x = v0 := smoothExtensionTangent_eq (I := I) x v0
  have hYx : Y x = v1 := smoothExtensionTangent_eq (I := I) x v1
  have hXsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v0
  have hYsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x v1

  have hfib : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (iteratedCovGrad g r t 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t)
            (iteratedCovGrad g r t 2 W)).toSection x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (iteratedCovGrad g r t 2 W).toSection x) -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t)
          (iteratedCovGrad g r t 2 W)).toSection x) := by
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hfib, ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]

  rw [appFullSec_toSection, swapTwoSec_apply,
    swapTwoFib_eval (I := I) (M := M) r t x ((iteratedCovGrad g r t 2 W).toSection x) v0 v1 D m]

  rw [show (iteratedCovGrad g r t 2 W).toSection x =
      (covGrad (I := I) (M := M) g r (t + 1)
        (covGrad (I := I) (M := M) g r t W)).toSection x from rfl]
  rw [show v0 = X x from hXx.symm, show v1 = Y x from hYx.symm]
  rw [secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r t W hXsm hYsm x D m,
    secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r t W hYsm hXsm x D m]

  rw [← ContinuousMultilinearMap.sub_apply, ← Tensor0SSpace.toModel_sub,
    ← ContinuousLinearMap.sub_apply]
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        tensorSecondCovDeriv (I := I) g r t X Y (fun y : M => W.toSection y) x) -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        tensorSecondCovDeriv (I := I) g r t Y X (fun y : M => W.toSection y) x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        riemannOp (tensorCov (I := I) g r t) x (X x) (Y x) (W.toSection x)) from
    tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g r t hXsm hYsm
      W.toSection.contMDiff]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciDefect_value_local (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W₁ W₂ : SmoothCcTensor g r t) (x : M)
    (hW : W₁.toSection x = W₂.toSection x) :
    (iteratedCovGrad g r t 2 W₁ -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W₁)).toSection x =
      (iteratedCovGrad g r t 2 W₂ -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W₂)).toSection x := by
  classical
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D v
  rw [show v = Fin.cons (v 0) (Fin.cons (Matrix.vecTail v 0) (Matrix.vecTail (Matrix.vecTail v)))
      from by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Fin.cons_zero]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [Matrix.vecTail, Function.comp]
      · simp [Fin.cons_succ, Matrix.vecTail, Function.comp]]
  rw [ricciDefect_eval (I := I) (M := M) g r t W₁ x D (v 0) (Matrix.vecTail v 0)
      (Matrix.vecTail (Matrix.vecTail v)),
    ricciDefect_eval (I := I) (M := M) g r t W₂ x D (v 0) (Matrix.vecTail v 0)
      (Matrix.vecTail (Matrix.vecTail v))]
  rw [hW]

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciDefect_toSection_add (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W₁ W₂ : SmoothCcTensor g r t) (x : M) :
    (iteratedCovGrad g r t 2 (W₁ + W₂) -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t)
          (iteratedCovGrad g r t 2 (W₁ + W₂))).toSection x =
      (iteratedCovGrad g r t 2 W₁ -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W₁)).toSection x +
        (iteratedCovGrad g r t 2 W₂ -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t)
            (iteratedCovGrad g r t 2 W₂)).toSection x := by
  simp only [iteratedCovGrad_add]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((iteratedCovGrad g r t 2 W₁ + iteratedCovGrad g r t 2 W₂).toSection x
        : TensorRSSpace r (t + 2) I x) =
      (iteratedCovGrad g r t 2 W₁).toSection x + (iteratedCovGrad g r t 2 W₂).toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
  rw [map_add (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
    swapTwoSec (I := I) (M := M) (E := E) r t x)]
  abel

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciDefect_toSection_smul (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (k : ℝ) (W : SmoothCcTensor g r t) (x : M) :
    (iteratedCovGrad g r t 2 (k • W) -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t)
          (iteratedCovGrad g r t 2 (k • W))).toSection x =
      k • (iteratedCovGrad g r t 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t)
            (iteratedCovGrad g r t 2 W)).toSection x := by
  have hsmul2 : iteratedCovGrad g r t 2 (k • W) = k • iteratedCovGrad g r t 2 W := by
    change covGrad (I := I) (M := M) g r (t + 1) (covGrad (I := I) (M := M) g r t (k • W)) =
      k • covGrad (I := I) (M := M) g r (t + 1) (covGrad (I := I) (M := M) g r t W)
    rw [covGrad_smul, covGrad_smul]
  rw [hsmul2]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [appFullSec_toSection, appFullSec_toSection]
  rw [show ((k • iteratedCovGrad g r t 2 W).toSection x : TensorRSSpace r (t + 2) I x) =
      k • (iteratedCovGrad g r t 2 W).toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
  rw [map_smul (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
    swapTwoSec (I := I) (M := M) (E := E) r t x)]
  rw [smul_sub]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_ricciDefect_homField (g : SmoothRiemannianMetric I M) (r t : ℕ) :
    ∃ RActF : HomTensorRSField (E := E) (M := M) r t (t + 2) I,
      ∀ W : SmoothCcTensor g r t,
        iteratedCovGrad g r t 2 W -
            homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W) =
          homTensorRSFieldApply (I := I) (M := M) g r t (t + 2) RActF W :=
  exists_value_local_appFullSec (I := I) (M := M) g r t (t + 2)
    (fun W => iteratedCovGrad g r t 2 W -
      homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
        (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W))
    (fun W₁ W₂ x => ricciDefect_toSection_add (I := I) (M := M) g r t W₁ W₂ x)
    (fun k W x => ricciDefect_toSection_smul (I := I) (M := M) g r t k W x)
    (fun W₁ W₂ x hW => ricciDefect_value_local (I := I) (M := M) g r t W₁ W₂ x hW)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotExtTrace_eval (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (V : TensorRSSpace r (s + 1 + 2) I x) (D : Tensor0SSpace r I x)
    (v0 : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) s x
            (metricDoubleTraceFib (I := I) (M := M) g r s x) V) D) (Fin.cons v0 m) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1 + 2) I x from V) D)
          (Fin.cons v0 (Fin.cons (smoothOrthoFrame (I := I) g x i x)
            (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))) := by
  classical
  rw [slotExtendFullFib_apply_eval (I := I) (M := M) g r (s + 2) s x
    (metricDoubleTraceFib (I := I) (M := M) g r s x) V D v0 m]
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        metricDoubleTraceFib (I := I) (M := M) g r s x
          ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          curryLastTwoTensorSlots (I := I) (M := M) r s x
            ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)) from
    metricDoubleTraceFib_apply (I := I) (M := M) g r s x
      ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)]
  rw [ContinuousLinearMap.sum_apply, toModel_sum_eval]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [twoSlotPeel_eval (I := I) (M := M) r s x
    ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) D m]
  exact covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r (s + 2) x V v0 D
    (Fin.cons (smoothOrthoFrame (I := I) g x i x)
      (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma traceConj_eval (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (V : TensorRSSpace r (s + 1 + 2) I x) (D : Tensor0SSpace r I x)
    (v0 : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          metricDoubleTraceFib (I := I) (M := M) g r (s + 1) x
            (slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) (s + 2) x
              (swapTwoFib (I := I) (M := M) r s x)
              (swapTwoFib (I := I) (M := M) r (s + 1) x V))) D) (Fin.cons v0 m) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1 + 2) I x from V) D)
          (Fin.cons v0 (Fin.cons (smoothOrthoFrame (I := I) g x i x)
            (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))) := by
  classical
  set W : TensorRSSpace r (s + 1 + 2) I x :=
    slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) (s + 2) x
      (swapTwoFib (I := I) (M := M) r s x) (swapTwoFib (I := I) (M := M) r (s + 1) x V) with hW_def
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        metricDoubleTraceFib (I := I) (M := M) g r (s + 1) x W) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          curryLastTwoTensorSlots (I := I) (M := M) r (s + 1) x W
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)) from
    metricDoubleTraceFib_apply (I := I) (M := M) g r (s + 1) x W]
  rw [ContinuousLinearMap.sum_apply, toModel_sum_eval]
  refine Finset.sum_congr rfl (fun i _ => ?_)

  rw [twoSlotPeel_eval (I := I) (M := M) r (s + 1) x W
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) D
    (Fin.cons v0 m)]

  rw [hW_def]
  rw [slotExtendFullFib_apply_eval (I := I) (M := M) g r (s + 2) (s + 2) x
    (swapTwoFib (I := I) (M := M) r s x) (swapTwoFib (I := I) (M := M) r (s + 1) x V) D
    (smoothOrthoFrame (I := I) g x i x)
    (Fin.cons (smoothOrthoFrame (I := I) g x i x) (Fin.cons v0 m))]

  rw [swapTwoFib_eval (I := I) (M := M) r s x
    ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm
      (swapTwoFib (I := I) (M := M) r (s + 1) x V) (smoothOrthoFrame (I := I) g x i x))
    (smoothOrthoFrame (I := I) g x i x) v0 D m]

  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r (s + 2) x
    (swapTwoFib (I := I) (M := M) r (s + 1) x V) (smoothOrthoFrame (I := I) g x i x) D
    (Fin.cons v0 (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))]

  rw [swapTwoFib_eval (I := I) (M := M) r (s + 1) x V
    (smoothOrthoFrame (I := I) g x i x) v0
    D (Fin.cons (smoothOrthoFrame (I := I) g x i x) m)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotExtTrace_eq_traceConj (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (V : TensorRSSpace r (s + 1 + 2) I x) :
    (show TensorRSSpace r (s + 1 + 2) I x →L[ℝ] TensorRSSpace r (s + 1) I x from
        slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) s x
          (metricDoubleTraceFib (I := I) (M := M) g r s x)) V =
      metricDoubleTraceFib (I := I) (M := M) g r (s + 1) x
        (slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) (s + 2) x
          (swapTwoFib (I := I) (M := M) r s x)
          (swapTwoFib (I := I) (M := M) r (s + 1) x V)) := by
  classical
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D v
  rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from by
    funext j; refine Fin.cases ?_ (fun k => ?_) j
    · simp [Fin.cons_zero]
    · simp [Fin.cons_succ, Matrix.vecTail, Function.comp]]
  rw [slotExtTrace_eval (I := I) (M := M) g r s x V D (v 0) (Matrix.vecTail v),
    traceConj_eval (I := I) (M := M) g r s x V D (v 0) (Matrix.vecTail v)]

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem appFullSec_slotExtTrace_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (V : SmoothCcTensor g r (s + 1 + 2)) :
    homTensorRSFieldApply (I := I) (M := M) g r (s + 2 + 1) (s + 1)
        (slotExtendFullSec (I := I) g r (s + 2) s
          (metricDoubleTraceField (I := I) (M := M) (E := E) g r s)) V =
      homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1)
        (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1 + 2)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1 + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) V)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  simp only [slotExtendFullSec_apply, metricDoubleTraceField_apply, swapTwoSec_apply]
  exact slotExtTrace_eq_traceConj (I := I) (M := M) g r s x (V.toSection x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem exists_appFullSec_comp (g : SmoothRiemannianMetric I M) (r a b c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r b c I)
    (Q' : HomTensorRSField (E := E) (M := M) r a b I) :
    ∃ QQ' : HomTensorRSField (E := E) (M := M) r a c I,
      ∀ W : SmoothCcTensor g r a,
        homTensorRSFieldApply (I := I) (M := M) g r b c Q (homTensorRSFieldApply (I := I) (M := M) g r a b Q' W) =
          homTensorRSFieldApply (I := I) (M := M) g r a c QQ' W :=
  exists_value_local_appFullSec (I := I) (M := M) g r a c
    (fun W => homTensorRSFieldApply (I := I) (M := M) g r b c Q (homTensorRSFieldApply (I := I) (M := M) g r a b Q' W))
    (fun W₁ W₂ x => by
      simp only [appFullSec_toSection]
      rw [show ((W₁ + W₂).toSection x : TensorRSSpace r a I x) =
          W₁.toSection x + W₂.toSection x from by
        rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
      rw [map_add (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x from Q' x),
        map_add (show TensorRSSpace r b I x →L[ℝ] TensorRSSpace r c I x from Q x)])
    (fun k W x => by
      simp only [appFullSec_toSection]
      rw [show ((k • W).toSection x : TensorRSSpace r a I x) = k • W.toSection x from by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
      rw [map_smul (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x from Q' x),
        map_smul (show TensorRSSpace r b I x →L[ℝ] TensorRSSpace r c I x from Q x)])
    (fun W₁ W₂ x hW => by
      simp only [appFullSec_toSection]
      rw [hW])

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem appFullSec_sub_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W₁ W₂ : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c Q (W₁ - W₂) =
      homTensorRSFieldApply (I := I) (M := M) g r a c Q W₁ - homTensorRSFieldApply (I := I) (M := M) g r a c Q W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((W₁ - W₂).toSection x : TensorRSSpace r a I x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]]
  rw [map_sub (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Q x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem appFullSec_add_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W₁ W₂ : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c Q (W₁ + W₂) =
      homTensorRSFieldApply (I := I) (M := M) g r a c Q W₁ + homTensorRSFieldApply (I := I) (M := M) g r a c Q W₂ :=
  appFullRS_add_right (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff W₁ W₂

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 6400000 in

omit [NeZero (Module.finrank ℝ E)] in
private theorem headDifferenceDrop_bracket (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (RA_s : HomTensorRSField (E := E) (M := M) r s (s + 2) I)
    (RA_s1 : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 3) I)
    (hRA_s : ∀ W : SmoothCcTensor g r s,
      iteratedCovGrad g r s 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 W) =
        homTensorRSFieldApply (I := I) (M := M) g r s (s + 2) RA_s W)
    (hRA_s1 : ∀ W : SmoothCcTensor g r (s + 1),
      iteratedCovGrad g r (s + 1) 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) (iteratedCovGrad g r (s + 1) 2 W) =
        homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3) RA_s1 W)
    (S : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) -
        homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (swapTwoSec (I := I) (M := M) (E := E) r (s + 1))
            (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S))) =
      (homTensorRSFieldApply (I := I) (M := M) g r s (s + 3)
            (homTensorRSCovGradSec (I := I) g r s (s + 2) RA_s) S +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3)
            (slotExtendFullSec (I := I) g r s (s + 2) RA_s)
            (covGrad (I := I) (M := M) g r s S) +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
            (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s))
            (iteratedCovGrad g r s 2 S)) +
        homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3) RA_s1
            (covGrad (I := I) (M := M) g r s S)) := by

  have hT3 : iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S) =
      covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) := rfl

  have hR1 := hRA_s1 (covGrad (I := I) (M := M) g r s S)
  rw [hT3] at hR1

  have hcg1 := covGrad_appFullSec_eq (I := I) (M := M) g r (s + 2) (s + 2)
    (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)

  have hR0 := hRA_s S

  have hcg2 := covGrad_appFullSec_eq (I := I) (M := M) g r s (s + 2) RA_s S

  have hsplit : ∀ A C : SmoothCcTensor g r (s + 3),
      A - homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s)) A =
        C →
      A - homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s))
            (homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
              (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) A) =
        C + homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
              (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
                (swapTwoSec (I := I) (M := M) (E := E) r s))
              (A - homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
                (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) A) := by
    intro A C hC
    rw [appFullSec_sub_right, ← hC]
    abel

  have hT3sub : covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) -
      homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
        (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r s))
        (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
      homTensorRSFieldApply (I := I) (M := M) g r s (s + 3)
          (homTensorRSCovGradSec (I := I) g r s (s + 2) RA_s) S +
        homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3)
          (slotExtendFullSec (I := I) g r s (s + 2) RA_s)
          (covGrad (I := I) (M := M) g r s S) +
        homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
          (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (iteratedCovGrad g r s 2 S) := by

    have hσ₂₃T3 : homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
        covGrad (I := I) (M := M) g r (s + 2)
            (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)) -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
            (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s)) (iteratedCovGrad g r s 2 S) := by
      rw [hcg1]; abel
    rw [hσ₂₃T3]
    rw [show covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) -
          (covGrad (I := I) (M := M) g r (s + 2)
            (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)) -
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
              (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
                (swapTwoSec (I := I) (M := M) (E := E) r s)) (iteratedCovGrad g r s 2 S)) =
        covGrad (I := I) (M := M) g r (s + 2)
            (iteratedCovGrad g r s 2 S -
              homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
                (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)) +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
            (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s)) (iteratedCovGrad g r s 2 S) from by
      rw [covGrad_sub]; abel]
    rw [hR0, hcg2]

  rw [hsplit (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) _ hT3sub]
  rw [hR1]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 6400000 in

private theorem exists_headDifferenceDrop_metricDoubleTrace (g : SmoothRiemannianMetric I M)
    (r s : ℕ) :
    ∃ (P₀ : HomTensorRSField (E := E) (M := M) r s (s + 1) I)
      (P₁ : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 1) I)
      (P₂ : HomTensorRSField (E := E) (M := M) r (s + 2) (s + 1) I),
      ∀ S : SmoothCcTensor g r s,
        homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1)
            (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
            (iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S)) -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2 + 1) (s + 1)
            (slotExtendFullSec (I := I) g r (s + 2) s
              (metricDoubleTraceField (I := I) (M := M) (E := E) g r s))
            (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
        homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) P₀ S +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) P₁
            (covGrad (I := I) (M := M) g r s S) +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) P₂
            (iteratedCovGrad g r s 2 S) := by
  classical

  obtain ⟨RA_s, hRA_s⟩ := exists_ricciDefect_homField (I := I) (M := M) (E := E) g r s
  obtain ⟨RA_s1, hRA_s1⟩ := exists_ricciDefect_homField (I := I) (M := M) (E := E) g r (s + 1)

  obtain ⟨P₀, hP₀⟩ := exists_appFullSec_comp (I := I) (M := M) g r s (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (homTensorRSCovGradSec (I := I) g r s (s + 2) RA_s)
  obtain ⟨P₂, hP₂⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 2) (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
      (swapTwoSec (I := I) (M := M) (E := E) r s))
  obtain ⟨PA, hPA⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 1) (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (slotExtendFullSec (I := I) g r s (s + 2) RA_s)
  obtain ⟨Tσ₂₃, hTσ₂₃⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 3) (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
      (swapTwoSec (I := I) (M := M) (E := E) r s))
  obtain ⟨PB, hPB⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 1) (s + 3) (s + 1)
    Tσ₂₃ RA_s1
  refine ⟨P₀, PA + PB, P₂, fun S => ?_⟩

  rw [show iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S) =
      covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) from rfl]
  rw [appFullSec_slotExtTrace_eq (I := I) (M := M) (E := E) g r s
    (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S))]
  rw [← appFullSec_sub_right (I := I) (M := M) g r (s + 1 + 2) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S))]

  rw [headDifferenceDrop_bracket (I := I) (M := M) (E := E) g r s RA_s RA_s1 hRA_s hRA_s1 S]

  rw [appFullSec_add_right, appFullSec_add_right, appFullSec_add_right]
  rw [hP₀ S, hP₂ (iteratedCovGrad g r s 2 S), hPA (covGrad (I := I) (M := M) g r s S)]
  rw [hTσ₂₃ (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3) RA_s1
    (covGrad (I := I) (M := M) g r s S))]
  rw [hPB (covGrad (I := I) (M := M) g r s S)]
  rw [appFullSec_add_left (I := I) (M := M) g r (s + 1) (s + 1) PA PB
    (covGrad (I := I) (M := M) g r s S)]
  abel

set_option backward.isDefEq.respectTransparency false in

private theorem exists_roughLapCommutatorTrace_homField
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ (Tr : (t : ℕ) → HomTensorRSField (E := E) (M := M) r (t + 2) t I)
      (P₀ : HomTensorRSField (E := E) (M := M) r s (s + 1) I)
      (P₁ : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 1) I)
      (P₂ : HomTensorRSField (E := E) (M := M) r (s + 2) (s + 1) I),
      (∀ (t : ℕ) (W : SmoothCcTensor g r t),
          rawTensorConnLapSmooth (I := I) g r t W =
            homTensorRSFieldApply (I := I) (M := M) g r (t + 2) t (Tr t)
              (iteratedCovGrad g r t 2 W)) ∧
        ∀ S : SmoothCcTensor g r s,
          homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1) (Tr (s + 1))
              (iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S)) -
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2 + 1) (s + 1)
              (slotExtendFullSec (I := I) g r (s + 2) s (Tr s))
              (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
          homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) P₀ S +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) P₁
              (covGrad (I := I) (M := M) g r s S) +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) P₂
              (iteratedCovGrad g r s 2 S) := by
  obtain ⟨P₀, P₁, P₂, hdrop⟩ :=
    exists_headDifferenceDrop_metricDoubleTrace (I := I) (M := M) (E := E) g r s
  refine ⟨metricDoubleTraceField (I := I) (M := M) (E := E) g r, P₀, P₁, P₂, ?_, hdrop⟩
  intro t W
  exact roughLap_eq_metricDoubleTrace (I := I) (M := M) (E := E) g r t W

set_option backward.isDefEq.respectTransparency false in

theorem exists_pointwiseTensorCurvRS_homField_jetDecomposition
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ (Q₀ : HomTensorRSField (E := E) (M := M) r s (s + 1) I)
      (Q₁ : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 1) I)
      (Q₂ : HomTensorRSField (E := E) (M := M) r (s + 2) (s + 1) I),
      ∀ S : SmoothCcTensor g r s,
        pointwiseTensorCurvRS (I := I) (M := M) g r s S =
          homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) Q₀ S +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) Q₁
              (covGrad (I := I) (M := M) g r s S) +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) Q₂
              (iteratedCovGrad g r s 2 S) := by
  obtain ⟨Tr, P₀, P₁, P₂, hfac, hhead⟩ :=
    exists_roughLapCommutatorTrace_homField (I := I) (M := M) (E := E) g r s
  refine ⟨P₀, P₁,
    P₂ - homTensorRSCovGradSec (I := I) g r (s + 2) s (Tr s), fun S => ?_⟩
  have hdef : pointwiseTensorCurvRS (I := I) (M := M) g r s S =
      rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
        covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) := rfl
  rw [hdef]

  rw [hfac (s + 1) (covGrad (I := I) (M := M) g r s S)]

  rw [show covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) =
      covGrad (I := I) (M := M) g r s
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) s (Tr s) (iteratedCovGrad g r s 2 S)) from
    congrArg (covGrad (I := I) (M := M) g r s) (hfac s S)]
  rw [covGrad_appFullSec_eq (I := I) (M := M) g r (s + 2) s (Tr s) (iteratedCovGrad g r s 2 S)]

  rw [appFullSec_sub_left (I := I) (M := M) g r (s + 2) (s + 1) P₂
    (homTensorRSCovGradSec (I := I) g r (s + 2) s (Tr s)) (iteratedCovGrad g r s 2 S)]

  rw [sub_add_eq_sub_sub, sub_right_comm, hhead S]
  abel

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_secondCovGrad_swap_ricciDefect_homField (g : SmoothRiemannianMetric I M)
    (r t : ℕ) :
    ∃ (F : HomTensorRSField (E := E) (M := M) r (t + 2) (t + 2) I)
      (R : HomTensorRSField (E := E) (M := M) r t (t + 2) I),
      (∀ (x : M) (T : TensorRSSpace r (t + 2) I x) (D : Tensor0SSpace r I x)
        (a b : TangentSpace I x) (m : Fin t → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
              (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from F x) T) D)
            (Fin.cons a (Fin.cons b m)) =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
            (Fin.cons b (Fin.cons a m))) ∧
      ∀ W : SmoothCcTensor g r t,
        iteratedCovGrad g r t 2 W =
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2) F (iteratedCovGrad g r t 2 W) +
            homTensorRSFieldApply (I := I) (M := M) g r t (t + 2) R W := by
  classical
  obtain ⟨R, hR⟩ := exists_ricciDefect_homField (I := I) (M := M) g r t
  refine ⟨swapTwoSec (I := I) (M := M) (E := E) r t, R, ?_, fun W => ?_⟩
  · intro x T D a b m
    rw [show (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
        swapTwoSec (I := I) (M := M) (E := E) r t x) = swapTwoFib (I := I) (M := M) r t x from
      swapTwoSec_apply (I := I) (M := M) (E := E) r t x]
    exact swapTwoFib_eval (I := I) (M := M) r t x T a b D m
  · have h := hR W
    exact sub_eq_iff_eq_add'.mp h

end Connection
end Integral
end DifferentialGeometry

end
