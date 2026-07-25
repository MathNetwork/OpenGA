import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.TensorSectionMDifferentiability
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma scalarFn_eq_toModel_elim0
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    scalarFn I M T x = (Tensor0SSpace.toModel (T x)) (fun i => Fin.elim0 i) := by
  change tensor0Iso I M x (T x) = (Tensor0SSpace.toModel (T x)) (fun i => Fin.elim0 i)
  rw [tensor0Iso]
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
      ((tensor0SSpace_continuousLinearEquiv (I := I) 0 x) (T x)) =
    (Tensor0SSpace.toModel (T x)) (fun i => Fin.elim0 i)
  rw [continuousMultilinearCurryFin0_apply]
  change (tensor0SSpace_continuousLinearEquiv (I := I) 0 x) (T x) (0 : Fin 0 → E) =
    (tensor0SSpace_continuousLinearEquiv (I := I) 0 x) (T x) (fun i => Fin.elim0 i)
  congr 1
  exact Subsingleton.elim _ _

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor0SCovariantDerivative_zero_toModel_apply
    (g : SmoothRiemannianMetric I M)
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    (Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v))
      (fun i => Fin.elim0 i) =
      mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) x v := by
  rw [tensor0SCovariantDerivative_apply_zero (I := I) (M := M)
    (LeviCivita (I := I) g) T x v]
  have hcoe : (Tensor0SSpace.toModel
        ((tensor0Iso I M x).symm
          (extDerivFun (I := I) (scalarFn I M T) x v)))
        (fun i => Fin.elim0 i) =
      tensor0Iso I M x
        ((tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T) x v)) :=
    (scalarFn_eq_toModel_elim0 (I := I) (M := M)
      (fun _ : M => (tensor0Iso I M x).symm
        (extDerivFun (I := I) (scalarFn I M T) x v)) x).symm
  rw [hcoe, ContinuousLinearEquiv.apply_symm_apply]
  change (NormedSpace.fromTangentSpace ((scalarFn I M T) x)).toContinuousLinearMap
      ((mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) x) v) =
    mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) x v
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensorInnerPointwise_0s_zero_eq_scalarFn_mul
    (g : SmoothRiemannianMetric I M)
    (W T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    covariantTensorInnerPointwise (I := I) (M := M) 0 g x
        (Tensor0SSpace.toModel (W x)) (Tensor0SSpace.toModel (T x)) =
      scalarFn I M W x * scalarFn I M T x := by
  rw [tensorInnerPointwise_0s_zero_arity, scalarFn_eq_toModel_elim0 (I := I) (M := M) W x,
    scalarFn_eq_toModel_elim0 (I := I) (M := M) T x]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_zero
    (g : SmoothRiemannianMetric I M)
    (W T : Π x : M, Tensor0SSpace 0 I x) {x : M}
    (hW : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M W) x)
    (hT : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => covariantTensorInnerPointwise (I := I) (M := M) 0 g y
          (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) x v =
      covariantTensorInnerPointwise (I := I) (M := M) 0 g x
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v))
          (Tensor0SSpace.toModel (T x))
        + covariantTensorInnerPointwise (I := I) (M := M) 0 g x
          (Tensor0SSpace.toModel (W x))
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v)) := by
  classical
  set f : M → ℝ := scalarFn I M W with hf_def
  set h : M → ℝ := scalarFn I M T with hh_def
  have hintegrand : (fun y : M => covariantTensorInnerPointwise (I := I) (M := M) 0 g y
        (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) =
      fun y : M => f y * h y := by
    funext y
    rw [tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g W T y]
  rw [hintegrand]
  change extDerivFun (I := I) (fun y : M => f y * h y) x v =
    covariantTensorInnerPointwise (I := I) (M := M) 0 g x
        (Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v))
        (Tensor0SSpace.toModel (T x))
      + covariantTensorInnerPointwise (I := I) (M := M) 0 g x
        (Tensor0SSpace.toModel (W x))
        (Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v))
  rw [extDerivFun_mul_apply (I := I) (p := f) (q := h) hW hT v]
  rw [tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g
    (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v) T x,
    tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g
    W (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v) x]
  have hWcov : scalarFn I M
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v) x =
      extDerivFun (I := I) f x v := by
    rw [hf_def,
      scalarFn_eq_toModel_elim0 (I := I) (M := M)
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v) x,
      tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g W x v]
    rfl
  have hTcov : scalarFn I M
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v) x =
      extDerivFun (I := I) h x v := by
    rw [hh_def,
      scalarFn_eq_toModel_elim0 (I := I) (M := M)
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v) x,
      tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g T x v]
    rfl
  rw [hWcov, hTcov]
  change f x * extDerivFun (I := I) h x v + h x * extDerivFun (I := I) f x v =
    extDerivFun (I := I) f x v * h x + f x * extDerivFun (I := I) h x v
  ring

open Tensor0SBundle in

omit [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma toModel_tensor0S_curry_eq_curryLeft {s : ℕ} {x : M}
    (A : Tensor0SSpace (s + 1) I x) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (tensor0S_curry (I := I) (M := M) s x A v) =
      (Tensor0SSpace.toModel A).curryLeft v := by
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [ContinuousMultilinearMap.curryLeft_apply]
  exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := A) (v0 := v) (vs := m)

private noncomputable def mixedGramMatrix
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i a => g.inner x ((chartModelBasis E) i) (frame a)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mixedGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i a : Fin (Module.finrank ℝ E)) :
    mixedGramMatrix (I := I) (M := M) g x frame i a =
      g.inner x ((chartModelBasis E) i) (frame a) := rfl

omit [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma orthonormal_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (v : TangentSpace I x) :
    v = ∑ a : Fin (Module.finrank ℝ E), g.inner x v (frame a) • frame a := by
  classical
  conv_lhs => rw [← frame.sum_repr v]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have hv : g.inner x v (frame a) =
      ∑ b : Fin (Module.finrank ℝ E),
        frame.repr v b * g.inner x (frame b) (frame a) := by
    conv_lhs => rw [show v = ∑ b : Fin (Module.finrank ℝ E),
      frame.repr v b • frame b from (frame.sum_repr v).symm]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hv]
  rw [Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba
    rw [horth b a, if_neg (by simpa [eq_comm] using hba), mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ a) hb

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma gramMatrixAt_eq_mixed_mul_transpose
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    gramMatrixAt (I := I) (M := M) g x =
      mixedGramMatrix (I := I) (M := M) g x frame *
        (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ := by
  classical
  ext i j
  rw [gramMatrixAt_apply, Matrix.mul_apply]
  have hexp : (chartModelBasis E) j =
      ∑ a : Fin (Module.finrank ℝ E),
        g.inner x ((chartModelBasis E) j) (frame a) • frame a :=
    orthonormal_expansion (I := I) (M := M) g x frame horth ((chartModelBasis E) j)
  calc g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j)
      = g.inner x ((chartModelBasis E) i)
          (∑ a : Fin (Module.finrank ℝ E),
            g.inner x ((chartModelBasis E) j) (frame a) • frame a) := by
        rw [← hexp]
    _ = ∑ a : Fin (Module.finrank ℝ E),
          mixedGramMatrix (I := I) (M := M) g x frame i a *
            (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a j := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul,
          mixedGramMatrix_apply, Matrix.transpose_apply, mixedGramMatrix_apply]
        ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mixedGramMatrix_isUnit
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    IsUnit (mixedGramMatrix (I := I) (M := M) g x frame) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det]
  have hG := gramMatrixAt_eq_mixed_mul_transpose (I := I) (M := M) g x frame horth
  have hdetG : (gramMatrixAt (I := I) (M := M) g x).det ≠ 0 := by
    have := gramMatrixAt_isUnit (I := I) (M := M) g x
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
  rw [hG, Matrix.det_mul, Matrix.det_transpose] at hdetG
  rw [isUnit_iff_ne_zero]
  intro h
  rw [h] at hdetG
  simp at hdetG

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mixedGram_transpose_mul_inv_mul
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ *
        ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
          mixedGramMatrix (I := I) (M := M) g x frame) = 1 := by
  classical
  set S := mixedGramMatrix (I := I) (M := M) g x frame with hS_def
  have hS_unit : IsUnit S := mixedGramMatrix_isUnit (I := I) (M := M) g x frame horth
  have hG : gramMatrixAt (I := I) (M := M) g x = S * Sᵀ :=
    gramMatrixAt_eq_mixed_mul_transpose (I := I) (M := M) g x frame horth
  have hGinv : (gramMatrixAt (I := I) (M := M) g x)⁻¹ = Sᵀ⁻¹ * S⁻¹ := by
    rw [hG, Matrix.mul_inv_rev]
  rw [hGinv]
  have hSdet : IsUnit S.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hS_unit
  have hSTdet : IsUnit Sᵀ.det := by
    rw [Matrix.det_transpose]; exact hSdet
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Sᵀ hSTdet,
    Matrix.one_mul, Matrix.nonsing_inv_mul S hSdet]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensorInnerPointwise_0s_sum_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x (∑ i ∈ A, a i • ψ i) T =
      ∑ i ∈ A, a i *
        covariantTensorInnerPointwise (I := I) (M := M) s g x (ψ i) T := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_left]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_left,
        tensorInnerPointwise_0s_smul_left, ih, Finset.sum_insert hi]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensorInnerPointwise_0s_sum_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x S (∑ i ∈ A, a i • ψ i) =
      ∑ i ∈ A, a i *
        covariantTensorInnerPointwise (I := I) (M := M) s g x S (ψ i) := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_right]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_right,
        tensorInnerPointwise_0s_smul_right, ih, Finset.sum_insert hi]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensorInnerPointwise_0s_bisum
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (c d : ι → ℝ)
    (ψ φ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x
        (∑ a ∈ A, c a • ψ a) (∑ b ∈ A, d b • φ b) =
      ∑ a ∈ A, ∑ b ∈ A,
        (c a * d b) *
          covariantTensorInnerPointwise (I := I) (M := M) s g x (ψ a) (φ b) := by
  classical
  rw [tensorInnerPointwise_0s_sum_smul_left]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [tensorInnerPointwise_0s_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  ring

omit [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma curryLeft_sum_smul {s : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    {ι : Type*} (A : Finset ι) (c : ι → ℝ) (w : ι → E) :
    P.curryLeft (∑ a ∈ A, c a • w a) =
      ∑ a ∈ A, c a • P.curryLeft (w a) := by
  classical
  induction A using Finset.induction with
  | empty => simp
  | insert a A ha ih =>
      rw [Finset.sum_insert ha, map_add, map_smul, ih, Finset.sum_insert ha]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensorInnerPointwise_0s_succ_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x S T =
      ∑ a : Fin (Module.finrank ℝ E),
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a)) := by
  classical
  rw [tensorInnerPointwise_0s_succ]
  have hmodel_exp : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E) i =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGramMatrix (I := I) (M := M) g x frame i a • frame a := by
    intro i
    have hexp := orthonormal_expansion (I := I) (M := M) g x frame horth
      ((chartModelBasis E) i)
    rw [hexp]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [mixedGramMatrix_apply]
  have hcurry_exp : ∀ (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
      (i : Fin (Module.finrank ℝ E)),
      P.curryLeft ((chartModelBasis E) i) =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGramMatrix (I := I) (M := M) g x frame i a • P.curryLeft (frame a) := by
    intro P i
    rw [hmodel_exp i]
    exact curryLeft_sum_smul (E := E) P Finset.univ _ _
  have hstep : ∀ i j : Fin (Module.finrank ℝ E),
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (mixedGramMatrix (I := I) (M := M) g x frame i a *
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              mixedGramMatrix (I := I) (M := M) g x frame j b) *
            covariantTensorInnerPointwise (I := I) (M := M) s g x
              (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro i j
    rw [hcurry_exp S i, hcurry_exp T j]
    rw [tensorInnerPointwise_0s_bisum (I := I) (M := M) g x s
      (A := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    ring
  rw [show (∑ i, ∑ j,
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))) =
      ∑ i, ∑ j, ∑ a, ∑ b,
        (mixedGramMatrix (I := I) (M := M) g x frame i a *
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGramMatrix (I := I) (M := M) g x frame j b) *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b))
    from by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact hstep i j]
  have hkey := mixedGram_transpose_mul_inv_mul (I := I) (M := M) g x frame horth
  set F := fun (i j a b : Fin (Module.finrank ℝ E)) =>
    (mixedGramMatrix (I := I) (M := M) g x frame i a *
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        mixedGramMatrix (I := I) (M := M) g x frame j b) *
      covariantTensorInnerPointwise (I := I) (M := M) s g x
        (S.curryLeft (frame a)) (T.curryLeft (frame b)) with hF_def
  have hreindex :
      ∑ i, ∑ j, ∑ a, ∑ b, F i j a b =
        ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j a => ∑ b, F i j a b))]
    rw [Finset.sum_comm (f := fun i a => ∑ j, ∑ b, F i j a b)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j b => F i j a b))]
    rw [Finset.sum_comm (f := fun i b => ∑ j, F i j a b)]
  rw [hreindex]
  have hcollapse : ∀ a b : Fin (Module.finrank ℝ E),
      ∑ i, ∑ j, F i j a b =
        ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ *
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
              mixedGramMatrix (I := I) (M := M) g x frame)) a b *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro a b
    rw [Matrix.mul_apply]
    rw [show (∑ i, (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGramMatrix (I := I) (M := M) g x frame) i b) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ i, ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGramMatrix (I := I) (M := M) g x frame) i b) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply]
    rw [show ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ∑ j, (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGramMatrix (I := I) (M := M) g x frame j b) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ j, ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGramMatrix (I := I) (M := M) g x frame j b)) *
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.transpose_apply, hF_def]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hcollapse a b))]
  rw [hkey]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro b _ hba
    rw [Matrix.one_apply_ne (Ne.symm hba), zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

omit [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma linearIndependent_of_orthonormal
    (g : SmoothRiemannianMetric I M) {y : M}
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (horth : ∀ a b, g.inner y (frame a) (frame b) = if a = b then 1 else 0) :
    LinearIndependent ℝ frame := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have hpair : g.inner y (∑ a, c a • frame a) (frame b) = 0 := by
    rw [hc]; simp
  rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
  rw [Finset.sum_eq_single b] at hpair
  · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth b b,
      if_pos rfl, smul_eq_mul, mul_one] at hpair
    exact hpair
  · intro a _ hab
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth a b,
      if_neg (by simpa using hab), smul_zero]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

private noncomputable def smoothOrthoBasis
    (g : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun a : Fin (Module.finrank ℝ E) =>
      smoothOrthoFrame (I := I) g x a y)
    (linearIndependent_of_orthonormal (I := I) (M := M) g
      (fun a => smoothOrthoFrame (I := I) g x a y)
      (fun a b => smoothOrthoFrame_orthonormal (I := I) g x hy a b))
    (by
      rw [Fintype.card_fin]
      rfl)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
private lemma smoothOrthoBasis_apply
    (g : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (a : Fin (Module.finrank ℝ E)) :
    smoothOrthoBasis (I := I) (M := M) g x hy a =
      smoothOrthoFrame (I := I) g x a y := by
  unfold smoothOrthoBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

open Tensor0SNabla in

noncomputable def tensorMetricCompatDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace s I x) (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  ((DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM (I := I) (M := M) g s x).flip
        (Tensor0SSpace.toModel (T x))).comp
      ((Tensor0SSpace.toModelL s x).comp
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) W x)) +
    ((DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM (I := I) (M := M) g s x)
        (Tensor0SSpace.toModel (W x))).comp
      ((Tensor0SSpace.toModelL s x).comp
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) T x))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp]
lemma tensorMetricCompatDiff_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace s I x) (x : M) (v : TangentSpace I x) :
    tensorMetricCompatDiff (I := I) (M := M) g s W T x v =
      covariantTensorInnerPointwise (I := I) (M := M) s g x
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) W x v))
          (Tensor0SSpace.toModel (T x))
        + covariantTensorInnerPointwise (I := I) (M := M) s g x
          (Tensor0SSpace.toModel (W x))
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) T x v)) := by
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Tensor0SNabla HomConnection in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor0SCovariantDerivative_curriedSection_hom_leibniz
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M => curriedSection I M W y (Y y)) x v =
      tensor0S_curry (I := I) (M := M) s x
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v)
          (Y x) +
        curriedSection I M W x
          ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) := by
  classical
  have hC := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  obtain ⟨Vfield, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x :=
    Vfield.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (F := Tensor0SModel s ℝ E)
    (V := fun x : M => Tensor0SSpace s I x)
    (cov_TM := LeviCivita (I := I) g)
    (cov_V := tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (τ := curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  have hsucc : tensor0S_curry (I := I) (M := M) s x
      (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M)
        (F := Tensor0SModel s ℝ E)
        (V := fun x : M => Tensor0SSpace s I x)
        (cov_TM := LeviCivita (I := I) g)
        (cov_V := tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (τ := curriedSection I M W) x v := by
    rw [tensor0SCovariantDerivative_succ_eq, tensor0SCovariantDerivative_succ_apply]
    exact (tensor0S_curry (I := I) (M := M) s x).apply_symm_apply _
  rw [hsucc]
  rw [show v = Vfield x from hVx.symm]
  rw [hHom]
  abel

open Tensor0SNabla HomConnection in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor0SCovariantDerivative_succ_consEval_peel
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x)
    (m : Fin s → E) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v)
        (Fin.cons (Y x) m) =
      Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M => curriedSection I M W y (Y y)) x v) m
        - Tensor0SSpace.toModel (W x)
            (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) m) := by
  classical
  have hleib := tensor0SCovariantDerivative_curriedSection_hom_leibniz
    (I := I) (M := M) g s W hW Y v

  have hterm1 : Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v) (Y x)) m =
      Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v)
        (Fin.cons (Y x) m) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v)
      (v0 := Y x) (vs := m)

  have hterm2 : Tensor0SSpace.toModel
        (curriedSection I M W x ((LeviCivita (I := I) g).toFun (fun y => Y y) x v)) m =
      Tensor0SSpace.toModel (W x)
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) m) := by
    rw [curriedSection_apply]
    exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W x) (v0 := (LeviCivita (I := I) g).toFun (fun y => Y y) x v) (vs := m)
  rw [← hterm1, hleib, Tensor0SBundle.Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply, hterm2]
  ring

open TensorRSNabla in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor0SCovariantDerivative_apply_eq_of_vanishing
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯)
    {x : M} (hw0 : w x = 0) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from S y) (w y)) x v =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S x)
        (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w x v) := by
  have hrs := tensorRSCovariantDerivative_apply (I := I) M r s
    (LeviCivita (I := I) g) S w x v
  rw [hw0, map_zero] at hrs
  exact sub_eq_zero.mp hrs.symm

omit [CompleteSpace E] in
omit [SigmaCompactSpace M] in
private lemma smoothOrthoFrame_connection_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) (v : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x a) x v)
        (smoothOrthoFrame (I := I) g x b x)
      + g.inner x
        (smoothOrthoFrame (I := I) g x a x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x b) x v) = 0 := by
  classical
  have hEa : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x a y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x a).contMDiffAt.mdifferentiableAt (by simp)
  have hEb : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x b y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x b).contMDiffAt.mdifferentiableAt (by simp)
  have hconst : (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x a y)
        (smoothOrthoFrame (I := I) g x b y)) =ᶠ[nhds x]
      (fun _ : M => (if a = b then (1 : ℝ) else 0)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
    exact smoothOrthoFrame_orthonormal (I := I) g x hy a b
  have hmfderiv0 : mfderiv I 𝓘(ℝ) (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x a y)
        (smoothOrthoFrame (I := I) g x b y)) x v = 0 := by
    rw [hconst.mfderiv_eq, mfderiv_const]
    rfl
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply
    (Y := fun y => smoothOrthoFrame (I := I) g x a y)
    (Z := fun y => smoothOrthoFrame (I := I) g x b y)
    (x := x) hEa hEb v
  rw [hmfderiv0] at hmc
  exact hmc.symm

open Tensor0SNabla in

private noncomputable def smoothOrthoFrameSection
    (g : SmoothRiemannianMetric I M) (x : M) (a : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨smoothOrthoFrame (I := I) g x a, smoothOrthoFrame_smooth (I := I) g x a⟩

omit [CompleteSpace E] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp]
private lemma smoothOrthoFrameSection_apply
    (g : SmoothRiemannianMetric I M) (x : M) (a : Fin (Module.finrank ℝ E)) (y : M) :
    smoothOrthoFrameSection (I := I) (M := M) g x a y =
      smoothOrthoFrame (I := I) g x a y := rfl

open Tensor0SNabla in

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensorSectionMDiffAt_curriedSection_apply
    (s : ℕ) (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

open Tensor0SNabla in

omit [CompleteSpace E] in
private lemma tensorMetricCompatDiff_succ_eq_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (hT : TensorSectionMDiffAt (I := I) (s + 1) T x) :
    ∑ a : Fin (Module.finrank ℝ E),
        tensorMetricCompatDiff (I := I) (M := M) g s
          (fun y : M => curriedSection I M W y
            (smoothOrthoFrameSection (I := I) (M := M) g x a y))
          (fun y : M => curriedSection I M T y
            (smoothOrthoFrameSection (I := I) (M := M) g x a y)) x =
      tensorMetricCompatDiff (I := I) (M := M) g (s + 1) W T x := by
  classical
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.sum_apply, tensorMetricCompatDiff_apply]
  set n := Module.finrank ℝ E with hn_def
  set E_ := fun a : Fin n => smoothOrthoFrameSection (I := I) (M := M) g x a with hE_def
  set WC := fun a : Fin n => fun y : M => curriedSection I M W y (E_ a y) with hWC_def
  set TC := fun a : Fin n => fun y : M => curriedSection I M T y (E_ a y) with hTC_def
  have hx_mem : x ∈ smoothOrthoFrameNbhd (I := I) (M := M) x :=
    mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x
  set frameB := smoothOrthoBasis (I := I) (M := M) g x hx_mem with hframeB_def
  have hframeB_orth : ∀ a b, g.inner x (frameB a) (frameB b) = if a = b then 1 else 0 := by
    intro a b
    rw [hframeB_def, smoothOrthoBasis_apply, smoothOrthoBasis_apply]
    exact smoothOrthoFrame_orthonormal (I := I) g x hx_mem a b
  have hframeB_apply : ∀ a, frameB a = smoothOrthoFrame (I := I) g x a x := by
    intro a; rw [hframeB_def, smoothOrthoBasis_apply]
  have hframeB_E : ∀ a : Fin n, frameB a = E_ a x := by
    intro a; rw [hframeB_apply a, hE_def]; rfl
  set Pw := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v
    with hPw_def
  set Pt := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) T x v
    with hPt_def
  set omgW := fun a : Fin n =>
    (LeviCivita (I := I) g).toFun (fun y => E_ a y) x v with homgW_def
  have hWleib : ∀ a : Fin n,
      tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) (WC a) x v =
        tensor0S_curry (I := I) (M := M) s x Pw (E_ a x) +
          curriedSection I M W x (omgW a) := by
    intro a
    exact tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g s W hW (E_ a) v
  have hTleib : ∀ a : Fin n,
      tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) (TC a) x v =
        tensor0S_curry (I := I) (M := M) s x Pt (E_ a x) +
          curriedSection I M T x (omgW a) := by
    intro a
    exact tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g s T hT (E_ a) v
  have hcurryW : ∀ a : Fin n, Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x Pw (E_ a x)) =
      (Tensor0SSpace.toModel Pw).curryLeft (E_ a x) := fun a =>
    toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) Pw (E_ a x)
  have hcurryT : ∀ a : Fin n, Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x Pt (E_ a x)) =
      (Tensor0SSpace.toModel Pt).curryLeft (E_ a x) := fun a =>
    toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) Pt (E_ a x)
  have hWCmodel : ∀ a : Fin n,
      Tensor0SSpace.toModel (WC a x) =
        (Tensor0SSpace.toModel (W x)).curryLeft (E_ a x) := by
    intro a
    rw [hWC_def]
    exact toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (W x) (E_ a x)
  have hTCmodel : ∀ a : Fin n,
      Tensor0SSpace.toModel (TC a x) =
        (Tensor0SSpace.toModel (T x)).curryLeft (E_ a x) := by
    intro a
    rw [hTC_def]
    exact toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (T x) (E_ a x)
  have hsummand : ∀ a : Fin n,
      tensorMetricCompatDiff (I := I) (M := M) g s (WC a) (TC a) x v =
        (covariantTensorInnerPointwise (I := I) (M := M) s g x
            ((Tensor0SSpace.toModel Pw).curryLeft (E_ a x))
            (Tensor0SSpace.toModel (TC a x)) +
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (WC a x))
            ((Tensor0SSpace.toModel Pt).curryLeft (E_ a x))) +
        (covariantTensorInnerPointwise (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (curriedSection I M W x (omgW a)))
            (Tensor0SSpace.toModel (TC a x)) +
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (WC a x))
            (Tensor0SSpace.toModel (curriedSection I M T x (omgW a)))) := by
    intro a
    rw [tensorMetricCompatDiff_apply]
    rw [hWleib a, hTleib a]
    rw [Tensor0SBundle.Tensor0SSpace.toModel_add,
      Tensor0SBundle.Tensor0SSpace.toModel_add]
    rw [tensorInnerPointwise_0s_add_left, tensorInnerPointwise_0s_add_right]
    rw [hcurryW a, hcurryT a]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hsummand a)]
  rw [Finset.sum_add_distrib]
  have hmain :
      ∑ a : Fin n,
          (covariantTensorInnerPointwise (I := I) (M := M) s g x
              ((Tensor0SSpace.toModel Pw).curryLeft (E_ a x))
              (Tensor0SSpace.toModel (TC a x)) +
            covariantTensorInnerPointwise (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC a x))
              ((Tensor0SSpace.toModel Pt).curryLeft (E_ a x))) =
        covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
            (Tensor0SSpace.toModel Pw) (Tensor0SSpace.toModel (T x)) +
          covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
            (Tensor0SSpace.toModel (W x)) (Tensor0SSpace.toModel Pt) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g x s frameB
        hframeB_orth]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hframeB_E a, hTCmodel a]
    · rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g x s frameB
        hframeB_orth]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hframeB_E a, hWCmodel a]
  have herror :
      ∑ a : Fin n,
          (covariantTensorInnerPointwise (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (curriedSection I M W x (omgW a)))
              (Tensor0SSpace.toModel (TC a x)) +
            covariantTensorInnerPointwise (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC a x))
              (Tensor0SSpace.toModel (curriedSection I M T x (omgW a)))) = 0 := by
    set omg := fun a b : Fin n => g.inner x (omgW a) (frameB b) with homg_def
    have homgexp : ∀ a : Fin n, omgW a = ∑ b : Fin n, omg a b • frameB b := by
      intro a
      rw [homg_def]
      exact orthonormal_expansion (I := I) (M := M) g x frameB hframeB_orth (omgW a)
    have hWcurried : ∀ a : Fin n,
        Tensor0SSpace.toModel (curriedSection I M W x (omgW a)) =
          ∑ b : Fin n, omg a b • Tensor0SSpace.toModel (WC b x) := by
      intro a
      have htensor : curriedSection I M W x (omgW a) =
          ∑ b : Fin n, omg a b • WC b x := by
        rw [homgexp a, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul]
        congr 1
        rw [hWC_def, hframeB_E b]
      rw [htensor]
      rw [← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [map_smul, Tensor0SBundle.Tensor0SSpace.toModelL_apply]
    have hTcurried : ∀ a : Fin n,
        Tensor0SSpace.toModel (curriedSection I M T x (omgW a)) =
          ∑ b : Fin n, omg a b • Tensor0SSpace.toModel (TC b x) := by
      intro a
      have htensor : curriedSection I M T x (omgW a) =
          ∑ b : Fin n, omg a b • TC b x := by
        rw [homgexp a, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul]
        congr 1
        rw [hTC_def, hframeB_E b]
      rw [htensor]
      rw [← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [map_smul, Tensor0SBundle.Tensor0SSpace.toModelL_apply]
    have hexpand : ∀ a : Fin n,
        covariantTensorInnerPointwise (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (curriedSection I M W x (omgW a)))
            (Tensor0SSpace.toModel (TC a x)) +
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (WC a x))
            (Tensor0SSpace.toModel (curriedSection I M T x (omgW a))) =
        ∑ b : Fin n,
          (omg a b * covariantTensorInnerPointwise (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC b x)) (Tensor0SSpace.toModel (TC a x)) +
            omg a b * covariantTensorInnerPointwise (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC a x)) (Tensor0SSpace.toModel (TC b x))) := by
      intro a
      rw [hWcurried a, hTcurried a]
      rw [tensorInnerPointwise_0s_sum_smul_left (I := I) (M := M) g x s
        (A := (Finset.univ : Finset (Fin n)))]
      rw [tensorInnerPointwise_0s_sum_smul_right (I := I) (M := M) g x s
        (A := (Finset.univ : Finset (Fin n)))]
      rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hexpand a)]
    have hsplit :
        ∑ a : Fin n, ∑ b : Fin n,
            (omg a b * covariantTensorInnerPointwise (I := I) (M := M) s g x
                (Tensor0SSpace.toModel (WC b x)) (Tensor0SSpace.toModel (TC a x)) +
              omg a b * covariantTensorInnerPointwise (I := I) (M := M) s g x
                (Tensor0SSpace.toModel (WC a x)) (Tensor0SSpace.toModel (TC b x))) =
          ∑ a : Fin n, ∑ b : Fin n,
            (omg a b + omg b a) * covariantTensorInnerPointwise (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC b x)) (Tensor0SSpace.toModel (TC a x)) := by
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib)]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm
        (f := fun a b => omg a b * covariantTensorInnerPointwise (I := I) (M := M) s g x
          (Tensor0SSpace.toModel (WC a x)) (Tensor0SSpace.toModel (TC b x)))]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [add_mul]
    rw [hsplit]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    have hskew : omg a b + omg b a = 0 := by
      have homg_ab : omg a b =
          g.inner x
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x a) x v)
            (smoothOrthoFrame (I := I) g x b x) := by
        simp only [homg_def, homgW_def, hE_def, smoothOrthoFrameSection_apply]
        rw [hframeB_apply b]
      have homg_ba : omg b a =
          g.inner x
            (smoothOrthoFrame (I := I) g x a x)
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x b) x v) := by
        simp only [homg_def, homgW_def, hE_def, smoothOrthoFrameSection_apply]
        rw [hframeB_apply a]
        exact g.symm x _ _
      rw [homg_ab, homg_ba]
      exact smoothOrthoFrame_connection_skew (I := I) (M := M) g x a b v
    rw [hskew, zero_mul]
  rw [hmain, herror, add_zero]

open Tensor0SNabla in

omit [CompleteSpace E] in
theorem tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_aux
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∀ (W T : Π x : M, Tensor0SSpace s I x) {x : M},
      TensorSectionMDiffAt (I := I) s W x → TensorSectionMDiffAt (I := I) s T x →
      HasMFDerivAt I 𝓘(ℝ, ℝ)
        (fun y : M => covariantTensorInnerPointwise (I := I) (M := M) s g y
          (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) x
        (tensorMetricCompatDiff (I := I) (M := M) g s W T x) := by
  classical
  induction s with
  | zero =>
      intro W T x hW hT
      have hW' : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M W) x :=
        (mdifferentiableAt_scalarFn_iff_section (I := I) (M := M) W).mpr hW
      have hT' : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x :=
        (mdifferentiableAt_scalarFn_iff_section (I := I) (M := M) T).mpr hT
      have hfun : (fun y : M => covariantTensorInnerPointwise (I := I) (M := M) 0 g y
            (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) =
          fun y : M => scalarFn I M W y * scalarFn I M T y := by
        funext y
        rw [tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g W T y]
      rw [hfun]
      have hmdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y : M => scalarFn I M W y * scalarFn I M T y) x :=
        (hW'.hasMFDerivAt.mul hT'.hasMFDerivAt).mdifferentiableAt
      refine hmdiff.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext (fun v => ?_))
      have hzero := tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_zero
        (I := I) (M := M) g W T hW' hT' v
      rw [hfun] at hzero
      exact hzero.trans (tensorMetricCompatDiff_apply (I := I) (M := M) g 0 W T x v).symm
  | succ s ih =>
      intro W T x hW hT
      set WC := fun a : Fin (Module.finrank ℝ E) => fun y : M =>
        curriedSection I M W y
          (smoothOrthoFrameSection (I := I) (M := M) g x a y) with hWC_def
      set TC := fun a : Fin (Module.finrank ℝ E) => fun y : M =>
        curriedSection I M T y
          (smoothOrthoFrameSection (I := I) (M := M) g x a y) with hTC_def
      have hWCdiff : ∀ a, TensorSectionMDiffAt (I := I) s (WC a) x := fun a =>
        tensorSectionMDiffAt_curriedSection_apply (I := I) (M := M) s W hW
          (smoothOrthoFrameSection (I := I) (M := M) g x a)
      have hTCdiff : ∀ a, TensorSectionMDiffAt (I := I) s (TC a) x := fun a =>
        tensorSectionMDiffAt_curriedSection_apply (I := I) (M := M) s T hT
          (smoothOrthoFrameSection (I := I) (M := M) g x a)
      have hIH : ∀ a, HasMFDerivAt I 𝓘(ℝ, ℝ)
          (fun y : M => covariantTensorInnerPointwise (I := I) (M := M) s g y
            (Tensor0SSpace.toModel (WC a y)) (Tensor0SSpace.toModel (TC a y))) x
          (tensorMetricCompatDiff (I := I) (M := M) g s (WC a) (TC a) x) := fun a =>
        ih (WC a) (TC a) (hWCdiff a) (hTCdiff a)
      have hSum := HasMFDerivAt.sum (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (f := fun a => fun y : M => covariantTensorInnerPointwise (I := I) (M := M) s g y
          (Tensor0SSpace.toModel (WC a y)) (Tensor0SSpace.toModel (TC a y)))
        (f' := fun a => tensorMetricCompatDiff (I := I) (M := M) g s (WC a) (TC a) x)
        (fun a _ => hIH a)
      have hEq : (fun y : M => covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g y
            (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) =ᶠ[nhds x]
          (∑ a : Fin (Module.finrank ℝ E),
            fun y : M => covariantTensorInnerPointwise (I := I) (M := M) s g y
              (Tensor0SSpace.toModel (WC a y)) (Tensor0SSpace.toModel (TC a y))) := by
        filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
        rw [Finset.sum_apply]
        rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g y s
          (smoothOrthoBasis (I := I) (M := M) g x hy)
          (fun a b => by
            rw [smoothOrthoBasis_apply, smoothOrthoBasis_apply]
            exact smoothOrthoFrame_orthonormal (I := I) g x hy a b)]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hWC_def, hTC_def]
        rw [show smoothOrthoBasis (I := I) (M := M) g x hy a =
            smoothOrthoFrameSection (I := I) (M := M) g x a y from by
          rw [smoothOrthoBasis_apply]; rfl]
        rw [← toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (W y),
          ← toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (T y)]
        rfl
      have hSum' := hSum.congr_of_eventuallyEq hEq
      rwa [tensorMetricCompatDiff_succ_eq_sum (I := I) (M := M) g s W T hW hT] at hSum'

open Tensor0SNabla in

omit [CompleteSpace E] in
theorem tensorInnerPointwise_0s_mfderiv_metricCompatible
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace s I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) s W x)
    (hT : TensorSectionMDiffAt (I := I) s T x)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => covariantTensorInnerPointwise (I := I) (M := M) s g y
          (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) x v =
      covariantTensorInnerPointwise (I := I) (M := M) s g x
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) W x v))
          (Tensor0SSpace.toModel (T x))
        + covariantTensorInnerPointwise (I := I) (M := M) s g x
          (Tensor0SSpace.toModel (W x))
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) T x v)) := by
  have hmf := (tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_aux
    (I := I) (M := M) g s W T hW hT).mfderiv
  rw [hmf]
  exact tensorMetricCompatDiff_apply (I := I) (M := M) g s W T x v

end Connection
end Integral
end DifferentialGeometry

end
