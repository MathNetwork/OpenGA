import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def rawTensorConnLap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rawTensorConnLap_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) T) x
            (smoothOrthoFrame (I := I) g x i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem rawTensorConnLap_zero [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    rawTensorConnLap (I := I) g r s
        (fun _ : M => (0 : TensorRSSpace r s I _)) x = 0 := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have h_zero_cov : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) =
      fun _ : M => (0 : TangentSpace I _ →L[ℝ] TensorRSSpace r s I _) := cov.zero
  unfold rawTensorConnLap
  refine Finset.sum_eq_zero ?_
  intro i _
  have h_covApply_zero : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun _ : M => (0 : TensorRSSpace r s I _)) =
      fun y : M => (0 : TensorRSSpace r s I y) := by
    funext y
    have : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) y = 0 :=
      congrArg (fun φ => φ y) h_zero_cov
    change (cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) y)
        (smoothOrthoFrame (I := I) g x i y) = 0
    rw [this]
    rfl
  rw [h_covApply_zero]
  have h_first_zero : cov.toFun (fun y : M => (0 : TensorRSSpace r s I y)) x
      (smoothOrthoFrame (I := I) g x i x) = 0 := by
    have : cov.toFun (fun y : M => (0 : TensorRSSpace r s I y)) x = 0 :=
      congrArg (fun φ => φ x) h_zero_cov
    rw [this]; rfl
  have h_second_zero : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) x
      ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) = 0 := by
    have : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) x = 0 :=
      congrArg (fun φ => φ x) h_zero_cov
    rw [this]; rfl
  rw [h_first_zero, h_second_zero]
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_add [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T T' : Π b : M, TensorRSSpace r s I b}
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hT' : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (hcovT' : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T' y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (T + T') x =
      rawTensorConnLap (I := I) g r s T x +
        rawTensorConnLap (I := I) g r s T' x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  unfold rawTensorConnLap
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  have h_addT : cov.toFun (fun y => T y + T' y) x =
      cov.toFun T x + cov.toFun T' x := by
    have h_add := hcov_loc.add (σ := T) (σ' := T') (hT x) (hT' x)
    convert h_add using 1
  have h_covApply_add : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun y => T y + T' y) =
      covApply cov (smoothOrthoFrame (I := I) g x i) T +
        covApply cov (smoothOrthoFrame (I := I) g x i) T' := by
    funext y
    have h_add_at_y : cov.toFun (fun y => T y + T' y) y =
        cov.toFun T y + cov.toFun T' y := by
      change cov.toFun (T + T') y = cov.toFun T y + cov.toFun T' y
      exact hcov_loc.add (σ := T) (σ' := T') (hT y) (hT' y)
    change cov.toFun (fun y => T y + T' y) y (smoothOrthoFrame (I := I) g x i y) =
      covApply cov (smoothOrthoFrame (I := I) g x i) T y +
        covApply cov (smoothOrthoFrame (I := I) g x i) T' y
    rw [h_add_at_y]
    rfl
  have h_second_deriv_add : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) (fun y => T y + T' y)) x =
      cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x +
        cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T') x := by
    rw [h_covApply_add]
    exact hcov_loc.add (σ := covApply cov (smoothOrthoFrame (I := I) g x i) T)
      (σ' := covApply cov (smoothOrthoFrame (I := I) g x i) T')
      (hcovT x i) (hcovT' x i)
  change
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i)
        (fun y => T y + T' y)) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun (fun y => T y + T' y) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) =
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) +
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T') x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T' x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))
  rw [h_second_deriv_add, h_addT]
  simp only [ContinuousLinearMap.add_apply]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_smul [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b} (c : ℝ)
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (fun y => c • T y) x =
      c • rawTensorConnLap (I := I) g r s T x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  unfold rawTensorConnLap
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  have h_smulT : cov.toFun (fun y => c • T y) x = c • cov.toFun T x := by
    change cov.toFun (c • T) x = c • cov.toFun T x
    exact hcov_loc.smul_const (σ := T) c (hT x)
  have h_covApply_smul : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun y => c • T y) =
      fun y => c • covApply cov (smoothOrthoFrame (I := I) g x i) T y := by
    funext y
    have h_smul_at_y : cov.toFun (fun y => c • T y) y = c • cov.toFun T y := by
      change cov.toFun (c • T) y = c • cov.toFun T y
      exact hcov_loc.smul_const (σ := T) c (hT y)
    change cov.toFun (fun y => c • T y) y (smoothOrthoFrame (I := I) g x i y) =
      c • covApply cov (smoothOrthoFrame (I := I) g x i) T y
    rw [h_smul_at_y]
    rfl
  have h_second_smul : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) (fun y => c • T y)) x =
      c • cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x := by
    rw [h_covApply_smul]
    exact hcov_loc.smul_const
      (σ := covApply cov (smoothOrthoFrame (I := I) g x i) T) c (hcovT x i)
  change
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i)
        (fun y => c • T y)) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun (fun y => c • T y) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) =
    c • (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))
  rw [h_second_smul, h_smulT]
  simp only [ContinuousLinearMap.smul_apply, smul_sub]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma cov_eq_zero_of_eventually_zero_on_open
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (cov : CovariantDerivative I F V)
    {T : Π y : M, V y} {U : Set M}
    (hU_open : IsOpen U)
    (hT_zero : ∀ y ∈ U, T y = 0)
    {y : M} (hyU : y ∈ U)
    (hT_diff_y : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun z : M => TotalSpace.mk' F (E := V) z (T z)) y) :
    cov.toFun T y = 0 := by
  classical
  have hU_nhds : U ∈ 𝓝 y := hU_open.mem_nhds hyU
  have hT_eq : ∀ᶠ y' in 𝓝 y, T y' = (fun y'' : M => (0 : V y'')) y' :=
    Filter.Eventually.mono (Filter.eventually_of_mem hU_nhds (fun y' hy' => hy'))
      (fun y' hy' => hT_zero y' hy')
  have hzero_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y' : M => TotalSpace.mk' F (E := V) y' (0 : V y')) y :=
    mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := F) (E := V) (IB := I)
  have huniv : (Set.univ : Set M) ∈ 𝓝 y := Filter.univ_mem
  have h_eq : cov.toFun T y =
      cov.toFun (fun y' : M => (0 : V y')) y :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hT_diff_y hzero_diff
      huniv hT_eq
  rw [h_eq]
  exact congrArg (fun φ => φ y) cov.zero

omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_eq_zero_of_eventually_zero [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {x : M} {U : Set M} (hU_open : IsOpen U) (hxU : x ∈ U)
    (hT_zero : ∀ y ∈ U, T y = 0)
    (hT_diff_x : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z)) x)
    (hcovT_diff_x : ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T z)) x) :
    rawTensorConnLap (I := I) g r s T x = 0 := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  unfold rawTensorConnLap
  refine Finset.sum_eq_zero ?_
  intro i _
  have h_second_zero : cov.toFun T x = 0 :=
    cov_eq_zero_of_eventually_zero_on_open (I := I)
      (V := fun w : M => TensorRSSpace r s I w)
      cov hU_open hT_zero hxU hT_diff_x
  have h_T_diff_on_U : ∀ y ∈ U, MDifferentiableAt I
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z)) y := by
    intro y hyU
    have hU_nhds_y : U ∈ 𝓝 y := hU_open.mem_nhds hyU
    have hzero_total_diff_y : MDifferentiableAt I
        (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (0 : TensorRSSpace r s I z)) y :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ)
        (F := TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) (IB := I)
    apply hzero_total_diff_y.congr_of_eventuallyEq
    filter_upwards [hU_nhds_y] with z hzU
    change TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z) =
      TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (0 : TensorRSSpace r s I z)
    rw [hT_zero z hzU]
  have h_covApply_zero : ∀ y ∈ U,
      covApply cov (smoothOrthoFrame (I := I) g x i) T y = 0 := by
    intro y hyU
    have h_cov_T_zero_y : cov.toFun T y = 0 :=
      cov_eq_zero_of_eventually_zero_on_open (I := I)
        (V := fun w : M => TensorRSSpace r s I w)
        cov hU_open hT_zero hyU (h_T_diff_on_U y hyU)
    change cov.toFun T y (smoothOrthoFrame (I := I) g x i y) = 0
    rw [h_cov_T_zero_y]
    rfl
  have h_first_zero : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) T) x = 0 :=
    cov_eq_zero_of_eventually_zero_on_open (I := I)
      (V := fun w : M => TensorRSSpace r s I w)
      cov hU_open
      (T := fun y : M => covApply cov (smoothOrthoFrame (I := I) g x i) T y)
      (U := U) h_covApply_zero hxU (hcovT_diff_x i)
  change cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
      (smoothOrthoFrame (I := I) g x i x) -
    cov.toFun T x ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) = 0
  rw [h_first_zero, h_second_zero]
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_neg [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (fun y => -T y) x =
      - rawTensorConnLap (I := I) g r s T x := by
  classical
  have h := rawTensorConnLap_smul (I := I) g r s (T := T) (c := -1) hT hcovT x
  simp only [neg_smul, one_smul, neg_smul] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_frame_trace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) T) x
            (smoothOrthoFrame (I := I) g x i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

section CompactSupport

variable [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompleteSpace E] in
private lemma rawTensorConnLap_T_mdiff_at (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x := by
  classical
  exact (T.contMDiff x).mdifferentiableAt (by simp)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rawTensorConnLap_covApply_mdiff_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Π b : M, TangentSpace I b)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (B b)))
    (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
          B (fun y : M => T y) y)) x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := T.contMDiff
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have h_covApply :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply cov B (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT_plus
  have h_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov B (fun y : M => T y) y)) x :=
    h_covApply.contMDiffAt (Filter.univ_mem)
  exact h_at.mdifferentiableAt (by simp)

theorem rawTensorConnLap_eq_zero_of_not_mem_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    {x : M}
    (hx : x ∉ tsupport (fun b : M => TensorRSSpace.toModel (T b))) :
    rawTensorConnLap (I := I) g r s (fun y : M => T y) x = 0 := by
  classical
  have hT_eq : (fun b : M => TensorRSSpace.toModel (T b)) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  rw [Filter.eventuallyEq_iff_exists_mem] at hT_eq
  obtain ⟨V, hV_nhds, hV_eq⟩ := hT_eq
  obtain ⟨U, hUV, hU_open, hxU⟩ := mem_nhds_iff.mp hV_nhds
  have hT_zero_U : ∀ b ∈ U, (fun y : M => T y) b = 0 := by
    intro b hbU
    have h_model_zero : TensorRSSpace.toModel (T b) = 0 := by
      have := hV_eq (hUV hbU)
      simpa using this
    have h_model_zero' : TensorRSSpace.toModel (T b) =
        TensorRSSpace.toModel (0 : TensorRSSpace r s I b) := by
      rw [h_model_zero, TensorRSSpace.toModel_zero]
    exact TensorRSSpace.toModel_injective h_model_zero'
  apply rawTensorConnLap_eq_zero_of_eventually_zero (I := I) g r s
    (T := fun y : M => T y) (U := U) hU_open hxU hT_zero_U
  · exact rawTensorConnLap_T_mdiff_at (I := I) r s T x
  · intro i
    exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T
      (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i) x

theorem rawTensorConnLap_support_subset_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯) :
    Function.support
        (fun b : M => TensorRSSpace.toModel
          (rawTensorConnLap (I := I) g r s (fun y : M => T y) b)) ⊆
      tsupport (fun b : M => TensorRSSpace.toModel (T b)) := by
  classical
  intro x hx
  by_contra hxnot
  apply hx
  have h_zero : rawTensorConnLap (I := I) g r s
      (fun y : M => T y) x = 0 :=
    rawTensorConnLap_eq_zero_of_not_mem_tsupport (I := I) g r s T hxnot
  change TensorRSSpace.toModel
    (rawTensorConnLap (I := I) g r s (fun y : M => T y) x) = 0
  rw [h_zero, TensorRSSpace.toModel_zero]

theorem rawTensorConnLap_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    (hT_cc : HasCompactSupport (fun b : M => TensorRSSpace.toModel (T b))) :
    HasCompactSupport (fun b : M =>
      TensorRSSpace.toModel
        (rawTensorConnLap (I := I) g r s (fun y : M => T y) b)) := by
  classical
  refine HasCompactSupport.mono'
    (f := fun b : M => TensorRSSpace.toModel (T b)) hT_cc ?_
  exact rawTensorConnLap_support_subset_tsupport (I := I) g r s T

end CompactSupport

section BundledOperator

open DifferentialGeometry.Integral.L2

variable [CompleteSpace E]

noncomputable def tensorConnLaplacian_of_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hSmooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y))) :
    SmoothCcTensor g r s where
  toSection :=
    { toFun := fun b : M =>
        rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) b
      contMDiff_toFun := hSmooth }
  hasCompactSupport :=
    rawTensorConnLap_hasCompactSupport (I := I) g r s T.toSection
      T.hasCompactSupport

@[simp] lemma tensorConnLaplacian_of_contMDiff_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hSmooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)))
    (x : M) :
    (tensorConnLaplacian_of_contMDiff (I := I) g r s T hSmooth).toSection x =
      rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := rfl

theorem tensorConnLaplacian_of_contMDiff_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T T' : SmoothCcTensor g r s)
    (hSmooth_T : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)))
    (hSmooth_T' : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T'.toSection z) y)))
    (hSmooth_sum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s
          (fun z : M => (T + T').toSection z) y)))
    (x : M) :
    (tensorConnLaplacian_of_contMDiff (I := I) g r s (T + T')
        hSmooth_sum).toSection x =
      (tensorConnLaplacian_of_contMDiff (I := I) g r s T hSmooth_T).toSection x +
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T'
          hSmooth_T').toSection x := by
  classical
  rw [tensorConnLaplacian_of_contMDiff_toFun,
      tensorConnLaplacian_of_contMDiff_toFun,
      tensorConnLaplacian_of_contMDiff_toFun]
  have h_add_fun : (fun z : M => (T + T').toSection z) =
      (fun z : M => T.toSection z + T'.toSection z) := by
    funext z
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]
    rfl
  rw [h_add_fun]
  refine rawTensorConnLap_add (I := I) g r s
    (T := fun z : M => T.toSection z) (T' := fun z : M => T'.toSection z)
    (fun y => ?_) (fun y => ?_) (fun y i => ?_) (fun y i => ?_) x
  · exact rawTensorConnLap_T_mdiff_at (I := I) r s T.toSection y
  · exact rawTensorConnLap_T_mdiff_at (I := I) r s T'.toSection y
  · exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T.toSection
      (smoothOrthoFrame (I := I) g y i)
      (smoothOrthoFrame_smooth (I := I) g y i) y
  · exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T'.toSection
      (smoothOrthoFrame (I := I) g y i)
      (smoothOrthoFrame_smooth (I := I) g y i) y

theorem tensorConnLaplacian_of_contMDiff_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g r s)
    (hSmooth_T : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)))
    (hSmooth_cT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s
          (fun z : M => (c • T).toSection z) y)))
    (x : M) :
    (tensorConnLaplacian_of_contMDiff (I := I) g r s (c • T)
        hSmooth_cT).toSection x =
      c • (tensorConnLaplacian_of_contMDiff (I := I) g r s T
        hSmooth_T).toSection x := by
  classical
  rw [tensorConnLaplacian_of_contMDiff_toFun,
      tensorConnLaplacian_of_contMDiff_toFun]
  have h_smul_fun : (fun z : M => (c • T).toSection z) =
      (fun z : M => c • T.toSection z) := by
    funext z
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]
    rfl
  rw [h_smul_fun]
  refine rawTensorConnLap_smul (I := I) g r s
    (T := fun z : M => T.toSection z) c
    (fun y => ?_) (fun y i => ?_) x
  · exact rawTensorConnLap_T_mdiff_at (I := I) r s T.toSection y
  · exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T.toSection
      (smoothOrthoFrame (I := I) g y i)
      (smoothOrthoFrame_smooth (I := I) g y i) y

theorem tensorConnLaplacian_of_contMDiff_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hSmooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s
          (fun z : M => (0 : SmoothCcTensor g r s).toSection z) y))) :
    tensorConnLaplacian_of_contMDiff (I := I) g r s
        (0 : SmoothCcTensor g r s) hSmooth =
      (0 : SmoothCcTensor g r s) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.coe_inj
  funext x
  have h_zero_fun : (fun z : M => (0 : SmoothCcTensor g r s).toSection z) =
      (fun _ : M => (0 : TensorRSSpace r s I _)) := by
    funext z
    have h_sec_zero : (0 : SmoothCcTensor g r s).toSection =
        (0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) :=
      SmoothCcTensor.toSection_zero
    rw [h_sec_zero, ContMDiffSection.coe_zero]
    rfl
  have h_rawConnLap_zero :
      rawTensorConnLap (I := I) g r s
        (fun z : M => (0 : SmoothCcTensor g r s).toSection z) x = 0 := by
    rw [h_zero_fun]
    exact rawTensorConnLap_zero (I := I) g r s x
  change rawTensorConnLap (I := I) g r s
      (fun z : M => (0 : SmoothCcTensor g r s).toSection z) x =
    ((0 : SmoothCcTensor g r s).toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) x
  rw [h_rawConnLap_zero]
  have h_sec_zero : (0 : SmoothCcTensor g r s).toSection =
      (0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯) :=
    SmoothCcTensor.toSection_zero
  rw [h_sec_zero, ContMDiffSection.coe_zero]
  rfl

end BundledOperator

section FixedFrame

variable [CompleteSpace E]

noncomputable def rawTensorConnLap_fixedFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (B i) T) x (B i x) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        T x
        ((LeviCivita (I := I) g).toFun (B i) x (B i x)))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rawTensorConnLap_fixedFrame_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap_fixedFrame (I := I) g r s B T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (B i) T) x (B i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun (B i) x (B i x))) := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rawTensorConnLap_fixedFrame_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap_fixedFrame (I := I) g r s
        (smoothOrthoFrame (I := I) g x) T x =
      rawTensorConnLap (I := I) g r s T x := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rawTensorConnLap_fixedFrame_covApply_T_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) (B i) T y)) := by
  classical
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T y)) Set.univ :=
    covApply_contMDiffOn
      (cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) (hB i) hT_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rawTensorConnLap_fixedFrame_firstSummand_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) (B i) T) y (B i y))) := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (B i) T y)) :=
    rawTensorConnLap_fixedFrame_covApply_T_contMDiff (I := I) g r s hT_total hB i
  have h1_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (B i) T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact h1
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply cov (B i)
            (fun z : M => covApply cov (B i) T z) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) (hB i) h1_plus
  intro b
  have hAt : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (B i)
          (fun z : M => covApply cov (B i) T z) y)) b :=
    hOn.contMDiffAt (Filter.univ_mem)
  convert hAt

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma rawTensorConnLap_fixedFrame_covBB_contMDiff
    (g : SmoothRiemannianMetric I M)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        ((LeviCivita (I := I) g).toFun (B i) y (B i y))) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hB_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (B i)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hB i
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
          (covApply cov (B i) (B i) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) (hB i) hB_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rawTensorConnLap_fixedFrame_secondSummand_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T y
          ((LeviCivita (I := I) g).toFun (B i) y (B i y)))) := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  set W : Π b : M, TangentSpace I b :=
    fun y => (LeviCivita (I := I) g).toFun (B i) y (B i y) with hW_def
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y (W y)) :=
    rawTensorConnLap_fixedFrame_covBB_contMDiff (I := I) g hB i
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply cov W T y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hW_smooth hT_plus
  intro b
  have hAt : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov W T y)) b :=
    hOn.contMDiffAt (Filter.univ_mem)
  convert hAt

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_fixedFrame_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s B T y)) := by
  classical
  have h_per_index_smooth : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T) y (B i y) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T y
              ((LeviCivita (I := I) g).toFun (B i) y (B i y)))) := by
    intro i
    have h_first := rawTensorConnLap_fixedFrame_firstSummand_contMDiff
      (I := I) g r s hT_total hB i
    have h_second := rawTensorConnLap_fixedFrame_secondSummand_contMDiff
      (I := I) g r s hT_total hB i
    exact h_first.sub_section h_second
  have h_sum_smooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T) y (B i y) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T y
              ((LeviCivita (I := I) g).toFun (B i) y (B i y))))) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact h_per_index_smooth i
  exact h_sum_smooth

end FixedFrame

section RawPsiTensorial

variable [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covRS_T_mdiff_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ]
          TensorRSSpace r s I x) b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T b)) y := by
  classical
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hcov_sec :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
        (fun b : M => (⟨b,
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T b⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            (fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)))
        Set.univ :=
    (TensorRSNabla.tensorRSCovariantDerivative_contMDiff
      (I := I) (M := M) r s (LeviCivita (I := I) g)).contMDiff.contMDiff
      (σ := T) hT_plus.contMDiffOn
  exact ((hcov_sec.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covApply_covRS_X_T_mdiff_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {X : Π b : M, TangentSpace I b} {y : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z (X z)) y) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T z)) y := by
  classical
  have hHom := covRS_T_mdiff_at (I := I) g r s hT_total y
  have := MDifferentiableAt.clm_bundle_apply (b := id) hHom hX
  exact this

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rawTensorConnLap_psi_tensorialAt_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M)
    {Y : Π b : M, TangentSpace I b}
    (_hY_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (Y z)) y) :
    TensorialAt I E
      (fun (X : Π b : M, TangentSpace I b) =>
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T) y (Y y) -
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T y
          ((LeviCivita (I := I) g).toFun X y (Y y)))
      y where
  smul := by
    intro f X hf hX
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    have h_covApply_smul :
        covApply cov_RS (f • X) T = f • (covApply cov_RS X T) := by
      funext z
      change cov_RS.toFun T z ((f • X) z) = f z • (cov_RS.toFun T z (X z))
      have h_smul_pi : (f • X : Π b : M, TangentSpace I b) z = f z • X z := rfl
      rw [h_smul_pi, ContinuousLinearMap.map_smul]
    have hAppX : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply cov_RS X T z)) y :=
      covApply_covRS_X_T_mdiff_at (I := I) g r s hT_total hX
    have h_leib_RS := cov_RS.isCovariantDerivativeOn.leibniz
      (σ := covApply cov_RS X T) (g := f) hAppX hf
    have h_leib_TM := cov_TM.isCovariantDerivativeOn.leibniz
      (σ := X) (g := f) hX hf
    change cov_RS.toFun (covApply cov_RS (f • X) T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun (f • X) y (Y y)) =
      f y • (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y)))
    rw [h_covApply_smul, h_leib_RS, h_leib_TM]
    have h_covApply_pt : covApply cov_RS X T y = cov_RS.toFun T y (X y) := rfl
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_sub, h_covApply_pt]
    abel
  add := by
    intro X X' hX hX'
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    have h_covApply_add :
        covApply cov_RS (X + X') T =
          covApply cov_RS X T + covApply cov_RS X' T := by
      funext z
      change cov_RS.toFun T z ((X + X') z) =
        cov_RS.toFun T z (X z) + cov_RS.toFun T z (X' z)
      have : (X + X' : Π b : M, TangentSpace I b) z = X z + X' z := rfl
      rw [this, ContinuousLinearMap.map_add]
    have hAppX : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply cov_RS X T z)) y :=
      covApply_covRS_X_T_mdiff_at (I := I) g r s hT_total hX
    have hAppX' : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply cov_RS X' T z)) y :=
      covApply_covRS_X_T_mdiff_at (I := I) g r s hT_total hX'
    have h_add_RS : cov_RS.toFun (covApply cov_RS X T +
        covApply cov_RS X' T) y =
      cov_RS.toFun (covApply cov_RS X T) y +
        cov_RS.toFun (covApply cov_RS X' T) y :=
      cov_RS.isCovariantDerivativeOn.add hAppX hAppX'
    have h_add_TM : cov_TM.toFun (X + X') y =
        cov_TM.toFun X y + cov_TM.toFun X' y :=
      cov_TM.isCovariantDerivativeOn.add hX hX'
    change cov_RS.toFun (covApply cov_RS (X + X') T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun (X + X') y (Y y)) =
      (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y))) +
      (cov_RS.toFun (covApply cov_RS X' T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X' y (Y y)))
    rw [h_covApply_add, h_add_RS, h_add_TM]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rawTensorConnLap_psi_tensorialAt_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (_hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M)
    {X : Π b : M, TangentSpace I b}
    (_hX_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (X z)) y) :
    TensorialAt I E
      (fun (Y : Π b : M, TangentSpace I b) =>
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T) y (Y y) -
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T y
          ((LeviCivita (I := I) g).toFun X y (Y y)))
      y where
  smul := by
    intro f Y _hf _hY
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    have h_smul_at : (f • Y : Π b : M, TangentSpace I b) y = f y • Y y := rfl
    change cov_RS.toFun (covApply cov_RS X T) y ((f • Y) y) -
        cov_RS.toFun T y (cov_TM.toFun X y ((f • Y) y)) =
      f y • (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y)))
    rw [h_smul_at]
    simp only [ContinuousLinearMap.map_smul, smul_sub]
  add := by
    intro Y Y' _hY _hY'
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    have h_add_at : (Y + Y' : Π b : M, TangentSpace I b) y = Y y + Y' y := rfl
    change cov_RS.toFun (covApply cov_RS X T) y ((Y + Y') y) -
        cov_RS.toFun T y (cov_TM.toFun X y ((Y + Y') y)) =
      (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y))) +
      (cov_RS.toFun (covApply cov_RS X T) y (Y' y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y' y)))
    rw [h_add_at]
    simp only [ContinuousLinearMap.map_add]
    abel

noncomputable def tensorHessianBilinAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace r s I y :=
  TensorialAt.mkHom₂
    (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _))
    (V' := (TangentSpace I : M → Type _))
    (A := TensorRSSpace r s I y)
    (Φ := fun (X Y : Π b : M, TangentSpace I b) =>
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) X T) y (Y y) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun T y
        ((LeviCivita (I := I) g).toFun X y (Y y)))
    y
    (fun Y hY =>
      rawTensorConnLap_psi_tensorialAt_left g r s T hT_total y (Y := Y) hY)
    (fun X hX =>
      rawTensorConnLap_psi_tensorialAt_right g r s T hT_total y (X := X) hX)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHessianBilinAt_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {y : M}
    {X Y : Π b : M, TangentSpace I b}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (X z)) y)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (Y z)) y) :
    tensorHessianBilinAt g r s T hT_total y (X y) (Y y) =
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) X T) y (Y y) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun T y
        ((LeviCivita (I := I) g).toFun X y (Y y)) := by
  classical
  unfold tensorHessianBilinAt
  exact TensorialAt.mkHom₂_apply _ _ hX hY

omit [CompleteSpace E] in
theorem rawTensorConnLap_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hB_orthonormal : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    rawTensorConnLap (I := I) g r s T y =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorHessianBilinAt g r s T hT_total y (B i) (B i) := by
  classical
  have h_LHS_via_smoothFrame :
      rawTensorConnLap (I := I) g r s T y =
        ∑ i : Fin (Module.finrank ℝ E),
          tensorHessianBilinAt g r s T hT_total y
            (smoothOrthoFrame (I := I) g y i y)
            (smoothOrthoFrame (I := I) g y i y) := by
    rw [rawTensorConnLap_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun z : M => TotalSpace.mk' E
          (E := fun w : M => TangentSpace I w) z
          (smoothOrthoFrame (I := I) g y i z)) y :=
      (smoothOrthoFrame_smooth (I := I) g y i).contMDiffAt.mdifferentiableAt
        (by simp)
    have happly := tensorHessianBilinAt_apply (I := I) g r s T hT_total
      (X := smoothOrthoFrame (I := I) g y i)
      (Y := smoothOrthoFrame (I := I) g y i)
      hSmooth_at hSmooth_at
    exact happly.symm
  rw [h_LHS_via_smoothFrame]
  set Ψ : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace r s I y :=
    tensorHessianBilinAt g r s T hT_total y with hΨ_def
  set C : Fin (Module.finrank ℝ E) → TangentSpace I y :=
    fun i => smoothOrthoFrame (I := I) g y i y with hC_def
  have hC_orthonormal :
      ∀ i j : Fin (Module.finrank ℝ E),
        g.inner y (C i) (C j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j
  have hRieszB : ∀ i : Fin (Module.finrank ℝ E),
      B i = ∑ j : Fin (Module.finrank ℝ E),
        g.inner y (B i) (C j) • C j := by
    intro i
    apply (vector_eq_iff_inner_eq (I := I) g y _ _).mpr
    intro w
    rw [show g.inner y
            (∑ j : Fin (Module.finrank ℝ E), g.inner y (B i) (C j) • C j) w =
          ∑ j : Fin (Module.finrank ℝ E),
            g.inner y (B i) (C j) * g.inner y (C j) w from by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [show ((g.inner y) (g.inner y (B i) (C j) • C j)) w =
            g.inner y (B i) (C j) • ((g.inner y) (C j)) w from by
        rw [ContinuousLinearMap.map_smul]; rfl]
      rw [smul_eq_mul]]
    exact g_inner_eq_orthonormal_parseval_sum (I := I) g y (B i) w C hC_orthonormal
  have hΨB_expand : ∀ i : Fin (Module.finrank ℝ E),
      Ψ (B i) (B i) =
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) •
              Ψ (C j) (C k) := by
    intro i
    set aB : Fin (Module.finrank ℝ E) → ℝ :=
      fun j => g.inner y (B i) (C j) with haB_def
    have hRieszBi : B i = ∑ j : Fin (Module.finrank ℝ E), aB j • C j := by
      simpa [aB] using hRieszB i
    conv_lhs => rw [hRieszBi]
    rw [show Ψ (∑ j : Fin (Module.finrank ℝ E), aB j • C j) =
          ∑ j : Fin (Module.finrank ℝ E), aB j • Ψ (C j) from by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      exact Ψ.map_smul (aB j) (C j)]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ContinuousLinearMap.smul_apply]
    rw [show Ψ (C j) (∑ k : Fin (Module.finrank ℝ E), aB k • C k) =
          ∑ k : Fin (Module.finrank ℝ E), aB k • Ψ (C j) (C k) from by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      exact (Ψ (C j)).map_smul (aB k) (C k)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [smul_smul]
  have hLHS_eq_C :
      (∑ i : Fin (Module.finrank ℝ E),
        Ψ (smoothOrthoFrame (I := I) g y i y)
          (smoothOrthoFrame (I := I) g y i y)) =
      ∑ i : Fin (Module.finrank ℝ E), Ψ (C i) (C i) := rfl
  rw [hLHS_eq_C]
  rw [show (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (g.inner y (B i) (C j) * g.inner y (B i) (C k)) •
                Ψ (C j) (C k) from
    Finset.sum_congr rfl (fun i _ => hΨB_expand i)]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun i j => ∑ k : Fin (Module.finrank ℝ E),
          (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k))]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k) from
    Finset.sum_comm]
  have h_inner_per_k : ∀ k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k)) =
      (if j = k then (1 : ℝ) else 0) • Ψ (C j) (C k) := by
    intro k
    rw [show (∑ i : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k)) =
          (∑ i : Fin (Module.finrank ℝ E),
            g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k) from
      (Finset.sum_smul
        (f := fun i : Fin (Module.finrank ℝ E) =>
          g.inner y (B i) (C j) * g.inner y (B i) (C k))
        (s := Finset.univ)
        (x := Ψ (C j) (C k))).symm]
    have hParseval := g_inner_eq_orthonormal_parseval_sum (I := I) g y
      (C j) (C k) B hB_orthonormal
    have h_sum_eq : (∑ i : Fin (Module.finrank ℝ E),
          g.inner y (B i) (C j) * g.inner y (B i) (C k)) =
        g.inner y (C j) (C k) := by
      rw [hParseval]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [g.symm y (C j) (B i)]
    rw [h_sum_eq]
    rw [hC_orthonormal j k]
  rw [Finset.sum_congr rfl (fun k _ => h_inner_per_k k)]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, one_smul]
  · intro k _ hkne
    rw [if_neg (Ne.symm hkne), zero_smul]
  · intro h_notin
    exact absurd (Finset.mem_univ j) h_notin

end RawPsiTensorial

section UnconditionalSmoothness

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem rawTensorConnLap_eq_fixedFrame_of_orthonormal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB_smooth : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0) :
    rawTensorConnLap (I := I) g r s T y =
      rawTensorConnLap_fixedFrame (I := I) g r s B T y := by
  classical
  have h_frame_trace :
      rawTensorConnLap (I := I) g r s T y =
        ∑ i : Fin (Module.finrank ℝ E),
          tensorHessianBilinAt g r s T hT_total y (B i y) (B i y) :=
    rawTensorConnLap_eq_frame_trace (I := I) g r s T hT_total y
      (fun i => B i y) hB_orth
  have h_summand_eq : ∀ i : Fin (Module.finrank ℝ E),
      tensorHessianBilinAt g r s T hT_total y (B i y) (B i y) =
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T) y (B i y) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T y
            ((LeviCivita (I := I) g).toFun (B i) y (B i y)) := by
    intro i
    have hBi_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun z : M => TotalSpace.mk' E
          (E := fun w : M => TangentSpace I w) z (B i z)) y :=
      (hB_smooth i).contMDiffAt.mdifferentiableAt (by simp)
    exact tensorHessianBilinAt_apply (I := I) g r s T hT_total
      (X := B i) (Y := B i) hBi_mdiff hBi_mdiff
  rw [h_frame_trace]
  rw [Finset.sum_congr rfl (fun i _ => h_summand_eq i)]
  rfl

omit [CompleteSpace E] in
private theorem rawTensorConnLap_eq_fixedFrame_smoothOrthoFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    rawTensorConnLap (I := I) g r s T y =
      rawTensorConnLap_fixedFrame (I := I) g r s
        (smoothOrthoFrame (I := I) g x₀) T y :=
  rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s T hT_total
    (B := smoothOrthoFrame (I := I) g x₀)
    (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

omit [CompleteSpace E] in
theorem rawTensorConnLap_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s T y)) := by
  classical
  intro x₀
  have h_fixed : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y)) :=
    rawTensorConnLap_fixedFrame_contMDiff (I := I) g r s hT_total
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i)
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y)) x₀ :=
    h_fixed x₀
  have h_eventuallyEq :
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s T y)) =ᶠ[𝓝 x₀]
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
    have h_fib : rawTensorConnLap (I := I) g r s T y =
        rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y :=
      rawTensorConnLap_eq_fixedFrame_smoothOrthoFrame_on_nbhd (I := I)
        g r s T hT_total x₀ hy
    exact congrArg (TotalSpace.mk' (TensorRSModel r s ℝ E)
      (E := fun z : M => TensorRSSpace r s I z) y) h_fib
  exact h_fixed_at.congr_of_eventuallyEq h_eventuallyEq

end UnconditionalSmoothness

end Connection
end Integral
end DifferentialGeometry

end
