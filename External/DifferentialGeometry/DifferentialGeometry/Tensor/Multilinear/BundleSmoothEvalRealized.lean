import DifferentialGeometry.Tensor.RSTensor.Field
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry


































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
open Bundle Set IsManifold ContinuousLinearMap
open Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace TensorMultilinear

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]







omit [CompleteSpace 𝕜] in
private theorem compContinuousLinearMap_isEmpty
    {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F₁) 𝕜)
    (g : ∀ _ : Fin 0, F₂ →L[𝕜] F₁) :
    f.compContinuousLinearMap g =
      (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ (f 0) :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F₂) 𝕜) := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  congr 1
  exact Subsingleton.elim _ _







omit [CompleteSpace 𝕜] in
private theorem trivializationAt_tensor0SBundle_succ_fibre {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
      (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2 =
    (T b).compContinuousLinearMap
      (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b) := rfl



omit [CompleteSpace 𝕜] in
theorem trivializationAt_tensor0SBundle_zero_fibre_gen
    (T : ∀ b : M, Tensor0SSpace 0 I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨b, T b⟩).2 =
    (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ ((T b) 0) :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜) := by
  change ((T b).compContinuousLinearMap
    (fun _ : Fin 0 => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)) =
    ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ ((T b) 0)
  rw [compContinuousLinearMap_isEmpty]


omit [CompleteSpace 𝕜] in
private theorem trivializationAt_homBundle_fibre {n : ℕ}
    (ϕ : ∀ b : M, TangentSpace I b →L[𝕜] Tensor0SSpace n I b) (x₀ b : M) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, ϕ b⟩).2 =
    ((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).continuousLinearMapAt 𝕜 b).comp
      ((ϕ b).comp
        ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)) := rfl




omit [CompleteSpace 𝕜] in
private theorem tensor0SBundle_linearMapAt_apply_of_mem {n : ℕ} (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜) (v : Fin n → E) :
    (((trivializationAt (Tensor0SModel n 𝕜 E)
        (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b)
      ((tensor0SSpace_continuousLinearEquiv (I := I) n b).symm f)) v =
    f (fun j => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b (v j)) := by
  have h_apply := congr_fun
    (Trivialization.coe_linearMapAt_of_mem (R := 𝕜)
      (e := trivializationAt (Tensor0SModel n 𝕜 E)
        (fun x : M => Tensor0SSpace n I x) x₀) hb)
    ((tensor0SSpace_continuousLinearEquiv (I := I) n b).symm f)
  rw [h_apply]
  change ((f.compContinuousLinearMap
    (fun _ : Fin n => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b))) v = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

omit [CompleteSpace 𝕜] in
private theorem tensor0SBundle_linearMapAt_apply_tensor {n : ℕ} (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet)
    (B : Tensor0SSpace n I b) (v : Fin n → E) :
    (((trivializationAt (Tensor0SModel n 𝕜 E)
        (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b) B) v =
    Tensor0SSpace.toModel B
      (fun j => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b (v j)) := by
  simpa using tensor0SBundle_linearMapAt_apply_of_mem (I := I) (M := M) x₀ b hb
    (Tensor0SSpace.toModel B) v



@[reducible]
def curriedSection_gen {n : ℕ} (T : ∀ b : M, Tensor0SSpace (n + 1) I b) :
    ∀ b : M, TangentSpace I b →L[𝕜] Tensor0SSpace n I b :=
  fun b => tensor0S_curry (I := I) (M := M) n b (T b)




omit [CompleteSpace 𝕜] in
theorem trivializationAt_homBundle_curriedSection_eq_gen {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, curriedSection_gen T b⟩).2 =
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2) := by
  rw [trivializationAt_homBundle_fibre (I := I) (M := M)
    (curriedSection_gen (I := I) (M := M) T) x₀ b]
  rw [trivializationAt_tensor0SBundle_succ_fibre (I := I) (M := M) T x₀ b]
  ext w v
  change (((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b)
      ((tensor0SSpace_continuousLinearEquiv (I := I) n b).symm
        ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜) (T b)
          ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b w)))) v =
    ((T b).compContinuousLinearMap
        (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b))
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







omit [CompleteSpace 𝕜] in
private theorem continuous_curriedSection_of_continuous_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b)
    (hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
        (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b))) :
    Continuous (fun b : M =>
      TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
        (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
        (curriedSection_gen T b)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  have hT_at : ContinuousAt
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x :=
    hT.continuousAt
  rw [FiberBundle.continuousAt_totalSpace] at hT_at
  obtain ⟨_, hT_fibre⟩ := hT_at
  have hcurry_cont : Continuous
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜 :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) => E) 𝕜 →
        E →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜) :=
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ).toContinuousLinearEquiv.continuous
  have hcomp : ContinuousAt
      (fun b : M =>
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
          ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
            (fun y : M => Tensor0SSpace (n + 1) I y) x ⟨b, T b⟩).2)) x :=
    hcurry_cont.continuousAt.comp hT_fibre
  refine hcomp.congr ?_
  filter_upwards [(trivializationAt (Tensor0SModel n 𝕜 E)
    (fun y : M => Tensor0SSpace n I y) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x ⟨b, T b⟩).2) =
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x
      ⟨b, curriedSection_gen T b⟩).2
  exact (trivializationAt_homBundle_curriedSection_eq_gen (I := I) (M := M) T x b hb).symm







omit [CompleteSpace 𝕜] in
private theorem contMDiff_curriedSection_of_contMDiff_section {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b))) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
          (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
          (curriedSection_gen T b)) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n + 1)
  intro x
  rw [Bundle.contMDiffAt_section (F := E →L[𝕜] Tensor0SModel n 𝕜 E)
    (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y)]
  have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) 𝕜 E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y) x).mp (hT x)
  have hcurry :
      ContMDiff 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E) 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜) :=
    ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp x hT_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n 𝕜 E)
    (fun y : M => Tensor0SSpace n I y) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x
      ⟨b, curriedSection_gen T b⟩).2 =
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x ⟨b, T b⟩).2)
  exact trivializationAt_homBundle_curriedSection_eq_gen (I := I) (M := M) T x b hb







omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_curry_apply_eval_gen {n : ℕ} {b : M}
    (T : Tensor0SSpace (n + 1) I b)
    (v0 : E) (vs : Fin n → E) :
    Tensor0SSpace.toModel (tensor0S_curry (I := I) (M := M) n b T v0) vs =
    Tensor0SSpace.toModel T (Fin.cons v0 vs) := by



  change (((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (n + 1) b) T) v0)) vs =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (n + 1) b) T) (Fin.cons v0 vs)
  rw [continuousMultilinearCurryLeftEquiv_apply]









omit [CompleteSpace 𝕜] in
private theorem continuous_section_apply_aux : ∀ (n : ℕ)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
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
          TotalSpace.mk' (Tensor0SModel 0 𝕜 E)
            (E := fun y : M => Tensor0SSpace 0 I y) b (T b)) x :=
      hT.continuousAt
    rw [FiberBundle.continuousAt_totalSpace] at hT_at
    obtain ⟨_, hT_fibre⟩ := hT_at
    have hcurry_cont : Continuous
        ((continuousMultilinearCurryFin0 𝕜 E 𝕜) :
          ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜 → 𝕜) :=
      (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearEquiv.continuous
    have hcomp : ContinuousAt
        (fun b : M =>
          (continuousMultilinearCurryFin0 𝕜 E 𝕜)
            ((trivializationAt (Tensor0SModel 0 𝕜 E)
              (fun y : M => Tensor0SSpace 0 I y) x ⟨b, T b⟩).2)) x :=
      hcurry_cont.continuousAt.comp hT_fibre
    refine hcomp.congr ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre_gen (I := I) (M := M) T x b]
    have hev : (continuousMultilinearCurryFin0 𝕜 E 𝕜)
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty 𝕜
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
          TotalSpace.mk' (Tensor0SModel n 𝕜 E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSection_gen T b) (v 0 b))) :=
      Continuous.clm_bundle_apply (𝕜 := 𝕜)
        (F₁ := E) (F₂ := Tensor0SModel n 𝕜 E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (b := id) (ϕ := fun b : M => curriedSection_gen T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := continuous_section_apply_aux n
      (fun b : M => (curriedSection_gen T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr (fun b => ?_)


    change Tensor0SSpace.toModel ((curriedSection_gen T b) (v 0 b))
        (fun i : Fin n => v i.succ b) =
      Tensor0SSpace.toModel (T b) (fun i : Fin (n + 1) => v i b)
    rw [tensor0S_curry_apply_eval_gen]
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_tensor0SBundle_succ_fibre_pt {n : ℕ}
    {b : M} (A : Tensor0SSpace (n + 1) I b) (x₀ : M) :
    (trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
      (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, A⟩).2 =
    A.compContinuousLinearMap
      (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b) := rfl

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_tensor0SBundle_zero_fibre_pt
    {b : M} (A : Tensor0SSpace 0 I b) (x₀ : M) :
    (trivializationAt (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨b, A⟩).2 =
    (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ (A 0) :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜) := by
  change (A.compContinuousLinearMap
    (fun _ : Fin 0 => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)) =
    ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ (A 0)
  rw [compContinuousLinearMap_isEmpty]

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_homBundle_fibre_pt {n : ℕ}
    {b : M} (φ : TangentSpace I b →L[𝕜] Tensor0SSpace n I b) (x₀ : M) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, φ⟩).2 =
    ((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).continuousLinearMapAt 𝕜 b).comp
      (φ.comp ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)) := rfl

omit [CompleteSpace 𝕜] in
private theorem trivializationAt_homBundle_curry_eq_pt {n : ℕ}
    {b : M} (A : Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, tensor0S_curry (I := I) (M := M) n b A⟩).2 =
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, A⟩).2) := by
  rw [trivializationAt_homBundle_fibre_pt (I := I) (M := M)
    (φ := tensor0S_curry (I := I) (M := M) n b A) x₀]
  rw [trivializationAt_tensor0SBundle_succ_fibre_pt (I := I) (M := M) A x₀]
  ext w v
  change (((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b)
      ((tensor0S_curry (I := I) (M := M) n b A)
        ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b w))) v =
    (A.compContinuousLinearMap
      (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b))
        (Fin.cons w v)
  rw [tensor0SBundle_linearMapAt_apply_tensor (I := I) (M := M) x₀ b hb]
  rw [tensor0S_curry_apply_eval_gen]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro k
    rfl

omit [CompleteSpace 𝕜] in
private theorem continuous_curry_of_continuous_base {P : Type*} [TopologicalSpace P]
    {n : ℕ} {b : P → M}
    {T : ∀ p : P, Tensor0SSpace (n + 1) I (b p)}
    (hb : Continuous b)
    (hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
        (E := fun x : M => Tensor0SSpace (n + 1) I x) (b p) (T p))) :
    Continuous (fun p : P =>
      TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
        (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) (b p)
        (tensor0S_curry (I := I) (M := M) n (b p) (T p))) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  have hT_at : ContinuousAt
      (fun p : P =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) (b p) (T p)) p₀ :=
    hT.continuousAt
  rw [FiberBundle.continuousAt_totalSpace] at hT_at
  obtain ⟨_, hT_fibre⟩ := hT_at
  have hcurry_cont : Continuous
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜 :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) => E) 𝕜 →
        E →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜) :=
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ).toContinuousLinearEquiv.continuous
  have hcomp : ContinuousAt
      (fun p : P =>
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
          ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
            (fun y : M => Tensor0SSpace (n + 1) I y) (b p₀)
              ⟨b p, T p⟩).2)) p₀ :=
    hcurry_cont.continuousAt.comp hT_fibre
  refine hcomp.congr ?_
  have hbase_nhds : (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun y : M => Tensor0SSpace n I y) (b p₀)).baseSet ∈ 𝓝 (b p₀) :=
    (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun y : M => Tensor0SSpace n I y) (b p₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)
  filter_upwards [hb.continuousAt.preimage_mem_nhds hbase_nhds] with p hp
  change (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun y : M => Tensor0SSpace (n + 1) I y) (b p₀) ⟨b p, T p⟩).2) =
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) (b p₀)
      ⟨b p, tensor0S_curry (I := I) (M := M) n (b p) (T p)⟩).2
  exact (trivializationAt_homBundle_curry_eq_pt (I := I) (M := M)
    (A := T p) (x₀ := b p₀) hp).symm

omit [CompleteSpace 𝕜] in
private theorem continuous_section_apply_base_aux {P : Type*} [TopologicalSpace P] :
    ∀ (n : ℕ)
    (b : P → M)
    (_hb : Continuous b)
    (T : ∀ p : P, Tensor0SSpace n I (b p))
    (_hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) (b p) (T p)))
    (v : Fin n → ∀ p : P, TangentSpace I (b p))
    (_hv : ∀ i : Fin n, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p))),
    Continuous (fun p : P =>
      Tensor0SSpace.toModel (T p) (fun i : Fin n => v i p))
  | 0, b, hb, T, hT, v, _hv => by
    rw [continuous_iff_continuousAt]
    intro p₀
    have hT_at := hT.continuousAt (x := p₀)
    rw [FiberBundle.continuousAt_totalSpace] at hT_at
    obtain ⟨_, hT_fibre⟩ := hT_at
    have hcurry_cont : Continuous
        ((continuousMultilinearCurryFin0 𝕜 E 𝕜) :
          ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜 → 𝕜) :=
      (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearEquiv.continuous
    have hcomp : ContinuousAt
        (fun p : P =>
          (continuousMultilinearCurryFin0 𝕜 E 𝕜)
            ((trivializationAt (Tensor0SModel 0 𝕜 E)
              (fun y : M => Tensor0SSpace 0 I y) (b p₀)
                ⟨b p, T p⟩).2)) p₀ :=
      hcurry_cont.continuousAt.comp hT_fibre
    refine hcomp.congr ?_
    filter_upwards with p
    rw [trivializationAt_tensor0SBundle_zero_fibre_pt
      (I := I) (M := M) (A := T p) (x₀ := b p₀)]
    change (continuousMultilinearCurryFin0 𝕜 E 𝕜)
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜
          (fun _ : Fin 0 => E) ((T p) 0)) =
      Tensor0SSpace.toModel (T p) (fun i : Fin 0 => v i p)
    have hev : (continuousMultilinearCurryFin0 𝕜 E 𝕜)
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜
          (fun _ : Fin 0 => E) ((T p) 0)) = (T p) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty 𝕜
        (fun _ : Fin 0 => E) ((T p) 0)) 0 = (T p) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]
    have huniq : (fun i : Fin 0 => v i p) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, b, hb, T, hT, v, hv => by
    have hCurry := continuous_curry_of_continuous_base (I := I) (M := M)
      (n := n) (b := b) (T := T) hb hT
    have hApplied : Continuous
        (fun p : P =>
          TotalSpace.mk' (Tensor0SModel n 𝕜 E)
            (E := fun x : M => Tensor0SSpace n I x) (b p)
            ((tensor0S_curry (I := I) (M := M) n (b p) (T p)) (v 0 p))) :=
      Continuous.clm_bundle_apply (𝕜 := 𝕜)
        (F₁ := E) (F₂ := Tensor0SModel n 𝕜 E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (b := b)
        (ϕ := fun p : P => tensor0S_curry (I := I) (M := M) n (b p) (T p))
        (v := fun p : P => v 0 p) hCurry (hv 0)
    have hRec := continuous_section_apply_base_aux n b hb
      (fun p : P => (tensor0S_curry (I := I) (M := M) n (b p) (T p)) (v 0 p))
      hApplied
      (fun (i : Fin n) (p : P) => v i.succ p)
      (fun i => hv i.succ)
    refine hRec.congr (fun p => ?_)
    change Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) n (b p) (T p)) (v 0 p))
        (fun i : Fin n => v i.succ p) =
      Tensor0SSpace.toModel (T p) (fun i : Fin (n + 1) => v i p)
    rw [tensor0S_curry_apply_eval_gen]
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]

private theorem contMDiff_section_apply_aux : ∀ (n : ℕ)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiff I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))),
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b))
  | 0, T, hT, v, _hv => by
    intro x
    have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel 0 𝕜 E)
      (E := fun y : M => Tensor0SSpace 0 I y) x).mp (hT x)
    have hcurry :
        ContMDiff 𝓘(𝕜, Tensor0SModel 0 𝕜 E) 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 𝕜 E 𝕜) :=
      (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
          (fun b : M =>
            (continuousMultilinearCurryFin0 𝕜 E 𝕜)
              ((trivializationAt (Tensor0SModel 0 𝕜 E)
                (fun y : M => Tensor0SSpace 0 I y) x ⟨b, T b⟩).2)) x :=
      hcurry.contMDiffAt.comp x hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre_gen (I := I) (M := M) T x b]
    have hev : (continuousMultilinearCurryFin0 𝕜 E 𝕜)
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty 𝕜
        (fun _ : Fin 0 => E) ((T b) 0)) 0 = (T b) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]
    have huniq : (fun i : Fin 0 => v i b) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, T, hT, v, hv => by
    have hCurry := contMDiff_curriedSection_of_contMDiff_section (I := I) (M := M) T hT
    have hApplied : ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel n 𝕜 E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSection_gen T b) (v 0 b))) :=
      ContMDiff.clm_bundle_apply (𝕜 := 𝕜) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SModel n 𝕜 E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (IM := I) (IB := I)
        (b := id) (ϕ := fun b : M => curriedSection_gen T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := contMDiff_section_apply_aux n
      (fun b : M => (curriedSection_gen T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr (fun b => ?_)


    change Tensor0SSpace.toModel (T b) (fun i : Fin (n + 1) => v i b) =
      Tensor0SSpace.toModel ((curriedSection_gen T b) (v 0 b))
        (fun i : Fin n => v i.succ b)
    rw [tensor0S_curry_apply_eval_gen]
    refine Eq.symm ?_
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]









omit [CompleteSpace 𝕜] in
theorem continuous_section_apply_gen
    {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : Continuous (fun b : M =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, Continuous (fun b : M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))) :
    Continuous (fun b : M =>
      Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) :=
  continuous_section_apply_aux n T hT v hv





omit [CompleteSpace 𝕜] in
theorem continuous_section_apply_base
    {P : Type*} [TopologicalSpace P] {n : ℕ}
    (b : P → M) (hb : Continuous b)
    (T : ∀ p : P, Tensor0SSpace n I (b p))
    (hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel n 𝕜 E)
        (E := fun x : M => Tensor0SSpace n I x) (b p) (T p)))
    (v : Fin n → ∀ p : P, TangentSpace I (b p))
    (hv : ∀ i : Fin n, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p))) :
    Continuous (fun p : P =>
      Tensor0SSpace.toModel (T p) (fun i : Fin n => v i p)) :=
  continuous_section_apply_base_aux n b hb T hT v hv





theorem contMDiff_section_apply_gen
    {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)))
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiff I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b))) :
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) :=
  contMDiff_section_apply_aux n T hT v hv






theorem contMDiff_tensor0SField_apply
    {n : ℕ}
    (T : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) n)
    (v : Fin n → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => T b (fun i : Fin n => v i b)) := by
  have hv : ∀ i : Fin n, ContMDiff I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) :=
    fun i => (v i).contMDiff
  have hEval := contMDiff_section_apply_gen (I := I) (M := M) (n := n)
    (T := fun b : M => T b) T.contMDiff (fun i b => v i b) hv
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval












omit [CompleteSpace 𝕜] in
theorem contMDiffAt_curriedSection_of_contMDiffAt_section_gen {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
          (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
          (curriedSection_gen T b)) x₀ := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n + 1)
  rw [Bundle.contMDiffAt_section (F := E →L[𝕜] Tensor0SModel n 𝕜 E)
    (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y)]
  have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) 𝕜 E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y) x₀).mp hT
  have hcurry :
      ContMDiff 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E) 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜) :=
    ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp x₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n 𝕜 E)
    (fun y : M => Tensor0SSpace n I y) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, curriedSection_gen T b⟩).2 =
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x₀ ⟨b, T b⟩).2)
  exact trivializationAt_homBundle_curriedSection_eq_gen (I := I) (M := M) T x₀ b hb




private theorem contMDiffAt_section_apply_aux : ∀ (n : ℕ) (x₀ : M)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀),
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) x₀
  | 0, x₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel 0 𝕜 E)
      (E := fun y : M => Tensor0SSpace 0 I y) x₀).mp hT
    have hcurry :
        ContMDiff 𝓘(𝕜, Tensor0SModel 0 𝕜 E) 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 𝕜 E 𝕜) :=
      (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
          (fun b : M =>
            (continuousMultilinearCurryFin0 𝕜 E 𝕜)
              ((trivializationAt (Tensor0SModel 0 𝕜 E)
                (fun y : M => Tensor0SSpace 0 I y) x₀ ⟨b, T b⟩).2)) x₀ :=
      hcurry.contMDiffAt.comp x₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre_gen (I := I) (M := M) T x₀ b]
    have hev : (continuousMultilinearCurryFin0 𝕜 E 𝕜)
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty 𝕜
        (fun _ : Fin 0 => E) ((T b) 0)) 0 = (T b) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]
    have huniq : (fun i : Fin 0 => v i b) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, x₀, T, hT, v, hv => by
    have hCurry := contMDiffAt_curriedSection_of_contMDiffAt_section_gen
      (I := I) (M := M) T x₀ hT
    have hApplied : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel n 𝕜 E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSection_gen T b) (v 0 b))) x₀ :=
      ContMDiffAt.clm_bundle_apply (𝕜 := 𝕜) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SModel n 𝕜 E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (IM := I) (IB := I)
        (b := id) (ϕ := fun b : M => curriedSection_gen T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := contMDiffAt_section_apply_aux n x₀
      (fun b : M => (curriedSection_gen T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_
    filter_upwards with b



    show Tensor0SSpace.toModel (T b) (fun i : Fin (n + 1) => v i b) =
      Tensor0SSpace.toModel ((curriedSection_gen T b) (v 0 b))
        (fun i : Fin n => v i.succ b)
    rw [tensor0S_curry_apply_eval_gen]
    refine Eq.symm ?_
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]





theorem contMDiffAt_section_apply_gen
    {n : ℕ} {x₀ : M}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) x₀ :=
  contMDiffAt_section_apply_aux n x₀ T hT v hv


omit [CompleteSpace 𝕜] in
theorem contMDiffAt_curriedSection_of_contMDiffAt_section_one {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
          (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
          (curriedSection_gen T b)) x₀ := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n + 1)
  rw [Bundle.contMDiffAt_section (F := E →L[𝕜] Tensor0SModel n 𝕜 E)
    (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y)]
  have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) 𝕜 E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y) x₀).mp hT
  have hcurry :
      ContMDiff 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)
        𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E) (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜) :=
    ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcurry_one :
      ContMDiff 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)
        𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E) (1 : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜) :=
    hcurry.of_le (by simp)
  have hcomp := hcurry_one.contMDiffAt.comp x₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n 𝕜 E)
    (fun y : M => Tensor0SSpace n I y) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, curriedSection_gen T b⟩).2 =
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x₀ ⟨b, T b⟩).2)
  exact trivializationAt_homBundle_curriedSection_eq_gen (I := I) (M := M) T x₀ b hb


private theorem contMDiffAt_section_apply_one_aux : ∀ (n : ℕ) (x₀ : M)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀),
    ContMDiffAt I 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) x₀
  | 0, x₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel 0 𝕜 E)
      (E := fun y : M => Tensor0SSpace 0 I y) x₀).mp hT
    have hcurry :
        ContMDiff 𝓘(𝕜, Tensor0SModel 0 𝕜 E) 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 𝕜 E 𝕜) :=
      (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearMap.contMDiff
    have hcurry_one :
        ContMDiff 𝓘(𝕜, Tensor0SModel 0 𝕜 E) 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 𝕜 E 𝕜) :=
      hcurry.of_le (by simp)
    have hcomp :
        ContMDiffAt I 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
          (fun b : M =>
            (continuousMultilinearCurryFin0 𝕜 E 𝕜)
              ((trivializationAt (Tensor0SModel 0 𝕜 E)
                (fun y : M => Tensor0SSpace 0 I y) x₀ ⟨b, T b⟩).2)) x₀ :=
      hcurry_one.contMDiffAt.comp x₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre_gen (I := I) (M := M) T x₀ b]
    have hev : (continuousMultilinearCurryFin0 𝕜 E 𝕜)
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty 𝕜
        (fun _ : Fin 0 => E) ((T b) 0)) 0 = (T b) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]
    have huniq : (fun i : Fin 0 => v i b) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, x₀, T, hT, v, hv => by
    have hCurry := contMDiffAt_curriedSection_of_contMDiffAt_section_one
      (I := I) (M := M) T x₀ hT
    have hApplied : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E))
        (1 : WithTop ℕ∞)
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel n 𝕜 E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSection_gen T b) (v 0 b))) x₀ :=
      ContMDiffAt.clm_bundle_apply (𝕜 := 𝕜) (n := (1 : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SModel n 𝕜 E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (IM := I) (IB := I)
        (b := id) (ϕ := fun b : M => curriedSection_gen T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := contMDiffAt_section_apply_one_aux n x₀
      (fun b : M => (curriedSection_gen T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_
    filter_upwards with b
    show Tensor0SSpace.toModel (T b) (fun i : Fin (n + 1) => v i b) =
      Tensor0SSpace.toModel ((curriedSection_gen T b) (v 0 b))
        (fun i : Fin n => v i.succ b)
    rw [tensor0S_curry_apply_eval_gen]
    refine Eq.symm ?_
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]


theorem contMDiffAt_section_apply_one
    {n : ℕ} {x₀ : M}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E))
      (1 : WithTop ℕ∞)
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
      (fun b : M => Tensor0SSpace.toModel (T b) (fun i : Fin n => v i b)) x₀ :=
  contMDiffAt_section_apply_one_aux n x₀ T hT v hv

end TensorMultilinear

end
