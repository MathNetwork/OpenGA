import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace TensorMultilinear

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem compContinuousLinearMap_isEmpty
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

theorem trivializationAt_tensor0SBundle_succ_fibre {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel (n + 1) ℝ E)
      (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2 =
    (T b).compContinuousLinearMap
      (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL ℝ b) := rfl

theorem trivializationAt_tensor0SBundle_zero_fibre
    (T : ∀ b : M, Tensor0SSpace 0 I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨b, T b⟩).2 =
    (ContinuousMultilinearMap.constOfIsEmpty ℝ _ ((T b) 0) :
      ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) := by
  change ((T b).compContinuousLinearMap
    (fun _ : Fin 0 => (trivializationAt E (TangentSpace I) x₀).symmL ℝ b)) =
    ContinuousMultilinearMap.constOfIsEmpty ℝ _ ((T b) 0)
  rw [compContinuousLinearMap_isEmpty]

theorem trivializationAt_homBundle_fibre {n : ℕ}
    (ϕ : ∀ b : M, TangentSpace I b →L[ℝ] Tensor0SSpace n I b) (x₀ b : M) :
    (trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x₀
      ⟨b, ϕ b⟩).2 =
    ((trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) x₀).continuousLinearMapAt ℝ b).comp
      ((ϕ b).comp
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ b)) := rfl

theorem tensor0SBundle_linearMapAt_apply_of_mem {n : ℕ} (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (v : Fin n → E) :
    (((trivializationAt (Tensor0SModel n ℝ E)
        (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt ℝ b)
      ((tensor0SSpace_continuousLinearEquiv (I := I) n b).symm f)) v =
    f (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ b (v j)) := by
  have h_apply := congr_fun
    (Trivialization.coe_linearMapAt_of_mem (R := ℝ)
      (e := trivializationAt (Tensor0SModel n ℝ E)
        (fun x : M => Tensor0SSpace n I x) x₀) hb)
    ((tensor0SSpace_continuousLinearEquiv (I := I) n b).symm f)
  rw [h_apply]
  change ((f.compContinuousLinearMap
    (fun _ : Fin n => (trivializationAt E (TangentSpace I) x₀).symmL ℝ b))) v = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

@[reducible]
def curriedSection {n : ℕ} (T : ∀ b : M, Tensor0SSpace (n + 1) I b) :
    ∀ b : M, TangentSpace I b →L[ℝ] Tensor0SSpace n I b :=
  fun b => tensor0S_curry (I := I) (M := M) n b (T b)

theorem trivializationAt_homBundle_curriedSection_eq {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet) :
    (trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x₀
      ⟨b, curriedSection T b⟩).2 =
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ((trivializationAt (Tensor0SModel (n + 1) ℝ E)
        (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2) := by
  rw [trivializationAt_homBundle_fibre (I := I) (M := M)
    (curriedSection (I := I) (M := M) T) x₀ b]
  rw [trivializationAt_tensor0SBundle_succ_fibre (I := I) (M := M) T x₀ b]
  ext w v
  change (((trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt ℝ b)
      ((tensor0SSpace_continuousLinearEquiv (I := I) n b).symm
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) (T b)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ b w)))) v =
    ((T b).compContinuousLinearMap
        (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL ℝ b))
      (Fin.cons w v)
  rw [tensor0SBundle_linearMapAt_apply_of_mem (I := I) (M := M) x₀ b hb]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [continuousMultilinearCurryLeftEquiv_apply]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero]
  · intro k
    simp [Fin.cons_succ]

private theorem continuous_curriedSection_of_continuous_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b)
    (hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b))) :
    Continuous (fun b : M =>
      TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) b
        (curriedSection T b)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  have hT_at : ContinuousAt
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x :=
    hT.continuousAt
  rw [FiberBundle.continuousAt_totalSpace] at hT_at
  obtain ⟨_, hT_fibre⟩ := hT_at
  have hcurry_cont : Continuous
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ :
        ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ →
        E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.continuous
  have hcomp : ContinuousAt
      (fun b : M =>
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
          ((trivializationAt (Tensor0SModel (n + 1) ℝ E)
            (fun y : M => Tensor0SSpace (n + 1) I y) x ⟨b, T b⟩).2)) x :=
    hcurry_cont.continuousAt.comp hT_fibre
  refine hcomp.congr ?_
  filter_upwards [(trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
      ((trivializationAt (Tensor0SModel (n + 1) ℝ E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x ⟨b, T b⟩).2) =
    (trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x
      ⟨b, curriedSection T b⟩).2
  exact (trivializationAt_homBundle_curriedSection_eq (I := I) (M := M) T x b hb).symm

private theorem contMDiff_curriedSection_of_contMDiff_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
          (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) b
          (curriedSection T b)) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  intro x
  rw [Bundle.contMDiffAt_section (F := E →L[ℝ] Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y)]
  have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y) x).mp (hT x)
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E) 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp x hT_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x
      ⟨b, curriedSection T b⟩).2 =
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
      ((trivializationAt (Tensor0SModel (n + 1) ℝ E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x ⟨b, T b⟩).2)
  exact trivializationAt_homBundle_curriedSection_eq (I := I) (M := M) T x b hb

omit [Module.Finite ℝ E] in
theorem tensor0S_curry_apply_eval {n : ℕ} {b : M}
    (T : Tensor0SSpace (n + 1) I b)
    (v0 : E) (vs : Fin n → E) :
    Tensor0SSpace.toModel (tensor0S_curry (I := I) (M := M) n b T v0) vs =
    Tensor0SSpace.toModel T (Fin.cons v0 vs) := by

  change (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (n + 1) b) T) v0)) vs =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (n + 1) b) T) (Fin.cons v0 vs)
  rw [continuousMultilinearCurryLeftEquiv_apply]

private theorem continuous_section_apply_aux : ∀ (n : ℕ)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, Continuous (fun b : M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))),
    Continuous (fun b : M =>
      Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b))
  | 0, T, hT, v, _hv => by
    rw [continuous_iff_continuousAt]
    intro x
    have hT_at : ContinuousAt
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel 0 ℝ E)
            (E := fun y : M => Tensor0SSpace 0 I y) b (T b)) x :=
      hT.continuousAt
    rw [FiberBundle.continuousAt_totalSpace] at hT_at
    obtain ⟨_, hT_fibre⟩ := hT_at
    have hcurry_cont : Continuous
        ((continuousMultilinearCurryFin0 ℝ E ℝ) :
          ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ → ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.continuous
    have hcomp : ContinuousAt
        (fun b : M =>
          (continuousMultilinearCurryFin0 ℝ E ℝ)
            ((trivializationAt (Tensor0SModel 0 ℝ E)
              (fun y : M => Tensor0SSpace 0 I y) x ⟨b, T b⟩).2)) x :=
      hcurry_cont.continuousAt.comp hT_fibre
    refine hcomp.congr ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) T x b]
    have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => E) ((T b) 0)) 0 = (T b) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]

    have huniq : (fun i : Fin 0 => v i b) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, T, hT, v, hv => by
    have hCurry := continuous_curriedSection_of_continuous_section (I := I) (M := M) T hT
    have hApplied : Continuous
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSection T b) (v 0 b))) :=
      Continuous.clm_bundle_apply (𝕜 := ℝ)
        (F₁ := E) (F₂ := Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (b := id) (ϕ := fun b : M => curriedSection T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := continuous_section_apply_aux n
      (fun b : M => (curriedSection T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr (fun b => ?_)

    change Tensor0SSpace.toModel ((curriedSection T b) (v 0 b))
        (fun i : Fin n => v i.succ b) =
      Tensor0SSpace.toModel (T b) (fun i : Fin (n + 1) => v i b)
    rw [tensor0S_curry_apply_eval]
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]

private theorem contMDiff_section_apply_aux : ∀ (n : ℕ)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n ℝ E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))),
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b))
  | 0, T, hT, v, _hv => by
    intro x
    have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SSpace 0 I y) x).mp (hT x)
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((trivializationAt (Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SSpace 0 I y) x ⟨b, T b⟩).2)) x :=
      hcurry.contMDiffAt.comp x hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) T x b]
    have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => E) ((T b) 0)) 0 = (T b) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]
    have huniq : (fun i : Fin 0 => v i b) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, T, hT, v, hv => by
    have hCurry := contMDiff_curriedSection_of_contMDiff_section (I := I) (M := M) T hT
    have hApplied : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSection T b) (v 0 b))) :=
      ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (IM := I) (IB := I)
        (b := id) (ϕ := fun b : M => curriedSection T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := contMDiff_section_apply_aux n
      (fun b : M => (curriedSection T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr (fun b => ?_)

    change Tensor0SSpace.toModel (T b) (fun i : Fin (n + 1) => v i b) =
      Tensor0SSpace.toModel ((curriedSection T b) (v 0 b))
        (fun i : Fin n => v i.succ b)
    rw [tensor0S_curry_apply_eval]
    refine Eq.symm ?_
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]

theorem continuous_section_apply
    {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, Continuous (fun b : M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))) :
    Continuous (fun b : M =>
      Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) :=
  continuous_section_apply_aux n T hT v hv

theorem contMDiff_section_apply
    {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n ℝ E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) :=
  contMDiff_section_apply_aux n T hT v hv

theorem contMDiffAt_curriedSection_of_contMDiffAt_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
          (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) b
          (curriedSection T b)) x₀ := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  rw [Bundle.contMDiffAt_section (F := E →L[ℝ] Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y)]
  have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y) x₀).mp hT
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E) 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp x₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x₀
      ⟨b, curriedSection T b⟩).2 =
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
      ((trivializationAt (Tensor0SModel (n + 1) ℝ E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x₀ ⟨b, T b⟩).2)
  exact trivializationAt_homBundle_curriedSection_eq (I := I) (M := M) T x₀ b hb

private theorem contMDiffAt_section_apply_aux : ∀ (n : ℕ) (x₀ : M)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n ℝ E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀),
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) x₀
  | 0, x₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SSpace 0 I y) x₀).mp hT
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((trivializationAt (Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SSpace 0 I y) x₀ ⟨b, T b⟩).2)) x₀ :=
      hcurry.contMDiffAt.comp x₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) T x₀ b]
    have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => E) ((T b) 0)) 0 = (T b) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]
    have huniq : (fun i : Fin 0 => v i b) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, x₀, T, hT, v, hv => by
    have hCurry := contMDiffAt_curriedSection_of_contMDiffAt_section
      (I := I) (M := M) T x₀ hT
    have hApplied : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSection T b) (v 0 b))) x₀ :=
      ContMDiffAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (IM := I) (IB := I)
        (b := id) (ϕ := fun b : M => curriedSection T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := contMDiffAt_section_apply_aux n x₀
      (fun b : M => (curriedSection T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_
    filter_upwards with b

    show Tensor0SSpace.toModel (T b) (fun i : Fin (n + 1) => v i b) =
      Tensor0SSpace.toModel ((curriedSection T b) (v 0 b))
        (fun i : Fin n => v i.succ b)
    rw [tensor0S_curry_apply_eval]
    refine Eq.symm ?_
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]

theorem contMDiffAt_section_apply
    {n : ℕ} {x₀ : M}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n ℝ E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) x₀ :=
  contMDiffAt_section_apply_aux n x₀ T hT v hv

private theorem contMDiffWithinAt_curriedSection_of_contMDiffWithinAt_section_prod {n : ℕ}
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b)
    (hT : ContMDiffWithinAt (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (n + 1) I x) p.1 (T p.1)) s p₀) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) p.1
        (curriedSection T p.1)) s p₀ := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  rw [Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y)
    (IB := I) (IM := I.prod 𝓘(ℝ,ℝ))]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hT_at := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y)
    (IB := I) (IM := I.prod 𝓘(ℝ,ℝ))).mp hT |>.2
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E) 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbase : {p : M × ℝ | p.1 ∈ (trivializationAt (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y) p₀.1).baseSet} ∈ nhdsWithin p₀ s := by
      apply nhdsWithin_le_nhds
      apply (continuous_fst.continuousAt).preimage_mem_nhds
      exact (trivializationAt (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y) p₀.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt _ _ _)
    filter_upwards [hbase] with p hb
    change (trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) p₀.1
        ⟨p.1, curriedSection T p.1⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SSpace (n + 1) I y) p₀.1 ⟨p.1, T p.1⟩).2)
    exact trivializationAt_homBundle_curriedSection_eq (I := I) (M := M) T p₀.1 p.1 hb
  · change (trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) p₀.1
        ⟨p₀.1, curriedSection T p₀.1⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SSpace (n + 1) I y) p₀.1 ⟨p₀.1, T p₀.1⟩).2)
    exact trivializationAt_homBundle_curriedSection_eq (I := I) (M := M) T p₀.1 p₀.1
      (mem_baseSet_trivializationAt _ _ _)

theorem contMDiffWithinAt_section_apply_prod : ∀ (n : ℕ)
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiffWithinAt (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SSpace n I x) p.1 (T p.1)) s p₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p.1)) s p₀),
    ContMDiffWithinAt (I.prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel (T p.1) (fun i => v i p.1)) s p₀
  | 0, s, p₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffWithinAt_totalSpace
      (F := Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SSpace 0 I y)
      (IB := I) (IM := I.prod 𝓘(ℝ,ℝ))).mp hT |>.2
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffWithinAt (I.prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
          (fun p : M × ℝ =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((trivializationAt (Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SSpace 0 I y) p₀.1 ⟨p.1, T p.1⟩).2)) s p₀ :=
      hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) T p₀.1 p.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p.1) 0)) = (T p.1) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p.1) 0)) 0 = (T p.1) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p.1) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
    · rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) T p₀.1 p₀.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p₀.1) 0)) = (T p₀.1) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p₀.1) 0)) 0 = (T p₀.1) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p₀.1) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
  | n + 1, s, p₀, T, hT, v, hv => by
    have hCurry := contMDiffWithinAt_curriedSection_of_contMDiffWithinAt_section_prod
      (I := I) (M := M) T hT
    have hApplied : ContMDiffWithinAt (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
        (fun p : M × ℝ =>
          TotalSpace.mk' (Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SSpace n I x) p.1
            ((curriedSection T p.1) (v 0 p.1))) s p₀ :=
      ContMDiffWithinAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (IM := I.prod 𝓘(ℝ,ℝ)) (IB := I)
        (b := Prod.fst) (ϕ := fun p : M × ℝ => curriedSection T p.1)
        (v := fun p : M × ℝ => v 0 p.1)
        hCurry (hv 0)
    have hRec := contMDiffWithinAt_section_apply_prod n
      (s := s) (p₀ := p₀)
      (fun b : M => (curriedSection T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]
    · change Tensor0SSpace.toModel (T p₀.1) (fun i : Fin (n + 1) => v i p₀.1) =
        Tensor0SSpace.toModel ((curriedSection T p₀.1) (v 0 p₀.1))
          (fun i : Fin n => v i.succ p₀.1)
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]

theorem contMDiffAt_section_apply_prod {n : ℕ} {p₀ : M × ℝ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SSpace n I x) p.1 (T p.1)) p₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i, ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p.1)) p₀) :
    ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel (T p.1) (fun i => v i p.1)) p₀ := by
  rw [← contMDiffWithinAt_univ] at hT ⊢
  exact contMDiffWithinAt_section_apply_prod n T hT v
    (fun i => (contMDiffWithinAt_univ).mpr (hv i))

theorem contMDiff_section_apply_prod {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiff (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel n ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SSpace n I x) p.1 (T p.1)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i, ContMDiff (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p.1))) :
    ContMDiff (I.prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel (T p.1) (fun i => v i p.1)) := by
  intro p₀
  exact contMDiffAt_section_apply_prod T (hT p₀) v (fun i => hv i p₀)

end TensorMultilinear

end
