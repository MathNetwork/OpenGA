import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open Tensor0SBundle

namespace Tensor0SNabla

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def tensor0Iso (x : M) :
    Tensor0SSpace 0 I x ≃L[ℝ] ℝ :=
  (tensor0SSpace_continuousLinearEquiv (I := I) 0 x).trans
    (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv

noncomputable def scalarFn (T : Π x : M, Tensor0SSpace 0 I x) : M → ℝ :=
  fun x => tensor0Iso I M x (T x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem scalarFn_apply (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    scalarFn I M T x = tensor0Iso I M x (T x) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalarFn_add (T₁ T₂ : Π x : M, Tensor0SSpace 0 I x) :
    scalarFn I M (T₁ + T₂) = scalarFn I M T₁ + scalarFn I M T₂ := by
  funext x
  change tensor0Iso I M x ((T₁ + T₂) x) =
    tensor0Iso I M x (T₁ x) + tensor0Iso I M x (T₂ x)
  change tensor0Iso I M x (T₁ x + T₂ x) = _
  exact map_add (tensor0Iso I M x) (T₁ x) (T₂ x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalarFn_smul (g : M → ℝ) (T : Π x : M, Tensor0SSpace 0 I x) :
    scalarFn I M (g • T) = g • scalarFn I M T := by
  funext x
  change tensor0Iso I M x ((g • T) x) = g x • tensor0Iso I M x (T x)
  change tensor0Iso I M x (g x • T x) = _
  exact map_smul (tensor0Iso I M x) (g x) (T x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalarFn_zero :
    scalarFn I M (0 : Π x : M, Tensor0SSpace 0 I x) = 0 := by
  funext x
  change tensor0Iso I M x ((0 : Π x : M, Tensor0SSpace 0 I x) x) = 0
  change tensor0Iso I M x (0 : Tensor0SSpace 0 I x) = 0
  exact map_zero (tensor0Iso I M x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tensor0Iso_symm_scalarFn (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    (tensor0Iso I M x).symm ((scalarFn I M T) x) = T x := by
  change (tensor0Iso I M x).symm (tensor0Iso I M x (T x)) = T x
  exact (tensor0Iso I M x).symm_apply_apply (T x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0Iso_symm_smul (T : Π x : M, Tensor0SSpace 0 I x)
    (a : ℝ) (x : M) :
    (tensor0Iso I M x).symm (a • scalarFn I M T x) = a • T x := by
  rw [map_smul]
  exact congr_arg (a • ·) (tensor0Iso_symm_scalarFn I M T x)

noncomputable def curriedSection {s : ℕ} (T : Π x : M, Tensor0SSpace (s+1) I x) :
    Π x : M, TangentSpace I x →L[ℝ] Tensor0SSpace s I x :=
  fun x => tensor0S_curry (I := I) (M := M) s x (T x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem curriedSection_apply {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) :
    curriedSection I M T x = tensor0S_curry (I := I) (M := M) s x (T x) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curriedSection_add {s : ℕ} (T₁ T₂ : Π x : M, Tensor0SSpace (s+1) I x) :
    curriedSection I M (T₁ + T₂) = curriedSection I M T₁ + curriedSection I M T₂ := by
  funext x
  change tensor0S_curry (I := I) (M := M) s x ((T₁ + T₂) x) =
    tensor0S_curry (I := I) (M := M) s x (T₁ x) +
    tensor0S_curry (I := I) (M := M) s x (T₂ x)
  change tensor0S_curry (I := I) (M := M) s x (T₁ x + T₂ x) = _
  exact map_add (tensor0S_curry (I := I) (M := M) s x) (T₁ x) (T₂ x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curriedSection_smul {s : ℕ} (g : M → ℝ) (T : Π x : M, Tensor0SSpace (s+1) I x) :
    curriedSection I M (g • T) = g • curriedSection I M T := by
  funext x
  change tensor0S_curry (I := I) (M := M) s x ((g • T) x) =
    g x • tensor0S_curry (I := I) (M := M) s x (T x)
  change tensor0S_curry (I := I) (M := M) s x (g x • T x) = _
  exact map_smul (tensor0S_curry (I := I) (M := M) s x) (g x) (T x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curriedSection_zero {s : ℕ} :
    curriedSection I M (0 : Π x : M, Tensor0SSpace (s+1) I x) = 0 := by
  funext x
  change tensor0S_curry (I := I) (M := M) s x ((0 : Π x : M, Tensor0SSpace (s+1) I x) x) = 0
  change tensor0S_curry (I := I) (M := M) s x (0 : Tensor0SSpace (s+1) I x) = 0
  exact map_zero (tensor0S_curry (I := I) (M := M) s x)

theorem compContinuousLinearMap_fin0
    {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F₁) ℝ)
    (g : ∀ _ : Fin 0, F₂ →L[ℝ] F₁) :
    f.compContinuousLinearMap g =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ _ (f 0) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F₂) ℝ) := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  congr 1
  exact Subsingleton.elim _ _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalarFn_eq_apply_zero (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    scalarFn I M T x = (T x) 0 := by
  rfl

omit [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem mdifferentiableAt_MLF0_iff_scalar
    (f : M → ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) f x ↔
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y 0) x := by
  constructor
  · intro hf
    have hcurry :
        MDifferentiable
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) 𝓘(ℝ, ℝ)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.mdifferentiable
    exact (hcurry (f x)).comp x hf
  · intro hf
    have hcurry_symm :
        MDifferentiable 𝓘(ℝ, ℝ)
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ)
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.mdifferentiable
    have hcomp :
        MDifferentiableAt I
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ)
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (f y 0)) x :=
      (hcurry_symm (f x 0)).comp x hf
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact ((continuousMultilinearCurryFin0 ℝ E ℝ).symm_apply_apply (f y)).symm

omit [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem contMDiffAt_MLF0_iff_scalar
    (n : WithTop ℕ∞)
    (f : M → ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) (x : M) :
    ContMDiffAt I 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) n f x ↔
    ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y => f y 0) x := by
  constructor
  · intro hf
    have hcurry :
        ContMDiff
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) 𝓘(ℝ, ℝ) n
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    exact hcurry.contMDiffAt.comp x hf
  · intro hf
    have hcurry_symm :
        ContMDiff 𝓘(ℝ, ℝ)
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) n
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) n
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (f y 0)) x :=
      hcurry_symm.contMDiffAt.comp x hf
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact ((continuousMultilinearCurryFin0 ℝ E ℝ).symm_apply_apply (f y)).symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem trivializationAt_tensor0SBundle_zero_eq_scalarFn
    (T : Π x : M, Tensor0SSpace 0 I x) (x₀ y : M) :
    (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨y, T y⟩).2 =
    (continuousMultilinearCurryFin0 ℝ E ℝ).symm (scalarFn I M T y) := by
  change ((T y).compContinuousLinearMap
    (fun _ : Fin 0 => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y)) =
    ContinuousMultilinearMap.constOfIsEmpty ℝ _ (scalarFn I M T y)
  rw [compContinuousLinearMap_fin0]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem contMDiff_scalarFn_iff_section
    (T : Π x : M, Tensor0SSpace 0 I x) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn I M T) ↔
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) y (T y)) := by
  refine ⟨fun hscalar x => ?_, fun hsection x => ?_⟩
  · rw [contMDiffAt_section (F := Tensor0SModel 0 ℝ E)
      (E := fun x : M => Tensor0SSpace 0 I x)]
    have hcurry_symm :
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Tensor0SModel 0 ℝ E) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(ℝ, Tensor0SModel 0 ℝ E) ∞
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (scalarFn I M T y)) x :=
      hcurry_symm.contMDiffAt.comp x (hscalar x)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y
  · have hsec_at := (contMDiffAt_section (F := Tensor0SModel 0 ℝ E)
      (E := fun x : M => Tensor0SSpace 0 I x) x).mp (hsection x)
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ)
            ((trivializationAt (Tensor0SModel 0 ℝ E)
              (fun x : M => Tensor0SSpace 0 I x) x ⟨y, T y⟩).2)) x :=
      hcurry.contMDiffAt.comp x hsec_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y]
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).apply_symm_apply (scalarFn I M T y)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem mdifferentiableAt_scalarFn_iff_section
    (T : Π x : M, Tensor0SSpace 0 I x) {x : M} :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x ↔
    MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun y => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) y (T y)) x := by
  rw [mdifferentiableAt_section (F := Tensor0SModel 0 ℝ E)
    (E := fun x : M => Tensor0SSpace 0 I x)]
  constructor
  · intro hscalar
    have hcurry_symm :
        MDifferentiable 𝓘(ℝ, ℝ) 𝓘(ℝ, Tensor0SModel 0 ℝ E)
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.mdifferentiable
    have hcomp :
        MDifferentiableAt I 𝓘(ℝ, Tensor0SModel 0 ℝ E)
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (scalarFn I M T y)) x :=
      (hcurry_symm (scalarFn I M T x)).comp x hscalar
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y
  · intro hsection
    have hcurry :
        MDifferentiable 𝓘(ℝ, Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.mdifferentiable
    have hcomp :
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ)
            ((trivializationAt (Tensor0SModel 0 ℝ E)
              (fun x : M => Tensor0SSpace 0 I x) x ⟨y, T y⟩).2)) x :=
      (hcurry _).comp x hsection
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y]
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).apply_symm_apply (scalarFn I M T y)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem trivializationAt_tensor0SBundle_succ_fiber_eq {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x₀ y : M) :
    (trivializationAt (Tensor0SModel (s+1) ℝ E)
      (fun x : M => Tensor0SSpace (s+1) I x) x₀ ⟨y, T y⟩).2 =
    (T y).compContinuousLinearMap
      (fun _ : Fin (s+1) => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem trivializationAt_homBundle_curriedSection_fiber_eq {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x₀ y : M) :
    (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x₀
      ⟨y, curriedSection I M T y⟩).2 =
    ((trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).continuousLinearMapAt ℝ y).comp
      ((curriedSection I M T y).comp
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y)) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0SBundle_linearMapAt_apply_of_mem {s : ℕ} (x₀ y : M)
    (hy : y ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).baseSet)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) (v : Fin s → E) :
    (((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) x₀).linearMapAt ℝ y)
      ((tensor0SSpace_continuousLinearEquiv (I := I) s y).symm f)) v =
    f (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (v j)) := by
  have h_apply := congr_fun
    (Trivialization.coe_linearMapAt_of_mem (R := ℝ)
      (e := trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) x₀) hy)
    ((tensor0SSpace_continuousLinearEquiv (I := I) s y).symm f)
  rw [h_apply]
  change ((f.compContinuousLinearMap
    (fun _ : Fin s => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y))) v = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem trivializationAt_homBundle_curriedSection_eq_curry_of_mem {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x₀ y : M)
    (hy : y ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).baseSet) :
    (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x₀
      ⟨y, curriedSection I M T y⟩).2 =
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
      ((trivializationAt (Tensor0SModel (s+1) ℝ E)
        (fun x : M => Tensor0SSpace (s+1) I x) x₀ ⟨y, T y⟩).2) := by
  rw [trivializationAt_homBundle_curriedSection_fiber_eq (I := I) (M := M) T x₀ y]
  rw [trivializationAt_tensor0SBundle_succ_fiber_eq (I := I) (M := M) T x₀ y]
  ext w v
  change (((trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).linearMapAt ℝ y)
      ((tensor0SSpace_continuousLinearEquiv (I := I) s y).symm
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ) (T y)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y w)))) v =
    ((T y).compContinuousLinearMap
        (fun _ : Fin (s+1) => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y))
      (Fin.cons w v)
  rw [tensor0SBundle_linearMapAt_apply_of_mem (I := I) (M := M) x₀ y hy]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [continuousMultilinearCurryLeftEquiv_apply]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero]
  · intro k
    simp [Fin.cons_succ]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem contMDiff_curriedSection_iff_section {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s+1) I x) y (T y)) ↔
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        y (curriedSection I M T y)) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  refine ⟨fun hT x => ?_, fun hC x => ?_⟩
  · rw [contMDiffAt_section (F := E →L[ℝ] Tensor0SModel s ℝ E)
      (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)]
    have hT_at := (contMDiffAt_section (F := Tensor0SModel (s+1) ℝ E)
      (E := fun x : M => Tensor0SSpace (s+1) I x) x).mp (hT x)
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SModel (s+1) ℝ E) 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)
          (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    have hcomp := hcurry.contMDiffAt.comp x hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
        ⟨y, curriedSection I M T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ)
        ((trivializationAt (Tensor0SModel (s+1) ℝ E)
          (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2)
    exact trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy
  · rw [contMDiffAt_section (F := Tensor0SModel (s+1) ℝ E)
      (E := fun x : M => Tensor0SSpace (s+1) I x)]
    have hC_at := (contMDiffAt_section (F := E →L[ℝ] Tensor0SModel s ℝ E)
      (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x).mp (hC x)
    have hcurry_symm :
        ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E) 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)
          (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm :=
      (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    have hcomp := hcurry_symm.contMDiffAt.comp x hC_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (Tensor0SModel (s+1) ℝ E)
        (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ((trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
          ⟨y, curriedSection I M T y⟩).2)
    rw [trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy]
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
      ).symm_apply_apply _).symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem mdifferentiableAt_curriedSection_iff_section {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) {x : M} :
    MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E))
      (fun y => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s+1) I x) y (T y)) x ↔
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        y (curriedSection I M T y)) x := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  rw [mdifferentiableAt_section (F := Tensor0SModel (s+1) ℝ E)
    (E := fun x : M => Tensor0SSpace (s+1) I x)]
  rw [mdifferentiableAt_section (F := E →L[ℝ] Tensor0SModel s ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)]
  constructor
  · intro hT
    have hcurry :
        MDifferentiable 𝓘(ℝ, Tensor0SModel (s+1) ℝ E) 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).mdifferentiable
    have hcomp := (hcurry _).comp x hT
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
        ⟨y, curriedSection I M T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ)
        ((trivializationAt (Tensor0SModel (s+1) ℝ E)
          (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2)
    exact trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy
  · intro hC
    have hcurry_symm :
        MDifferentiable 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E) 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm :=
      (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ).toContinuousLinearEquiv.toContinuousLinearMap).mdifferentiable
    have hcomp := (hcurry_symm _).comp x hC
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (Tensor0SModel (s+1) ℝ E)
        (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ((trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
          ⟨y, curriedSection I M T y⟩).2)
    rw [trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy]
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
      ).symm_apply_apply _).symm

end Tensor0SNabla

end
