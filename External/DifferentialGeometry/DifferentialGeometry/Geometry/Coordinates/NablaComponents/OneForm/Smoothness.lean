import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Moving







set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]


private theorem coordinateFrame_coeff_contMDiffAt
    (Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis 𝕜 E) (s := fun y : M => Z y)
      (k := (∞ : WithTop ℕ∞)) hx Z.contMDiff.contMDiffAt j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff

private theorem coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
    (Z : (x : M) -> TangentSpace I x) {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun y : M => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis 𝕜 E) (s := Z)
      (k := (∞ : WithTop ℕ∞)) hx hZ j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold I 2 M] in
theorem oneForm_eval_coordinateFrame_contMDiffAt
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀ := by
  have hα_top := α.contMDiff x₀
  have hα := hα_top.of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hframe :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, coordinateFrameAt (I := I) x₀ j y⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := 1) (x₀ := x₀)
    (T := fun y : M => α y) hα
    (v := fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j)
    (hv := fun _ : Fin 1 => hframe)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval


theorem nabla0SFun_one_eval_smooth_slots
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  rw [nabla0SFun_one_eval_coordFrame_moving
    (I := I) cov X Z α x₀
    (modelDeriv_eq_coordDeriv0SAt (I := I) X x₀ α)
    (fun j =>
      (coordinateFrame_coeff_contMDiffAt (I := I) Z x₀ j).mdifferentiableAt
        (by simp))
    (fun j =>
      (oneForm_eval_coordinateFrame_contMDiffAt (I := I) α x₀ j).mdifferentiableAt
        (by simp))]

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_covariantDeriv_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (coordinateFrameAt (I := I) x₀ j) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let u := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hframe_smooth :
      CMDiff[u] ((∞ : WithTop ℕ∞) + 1) (T% (frame j)) := by
    exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn j).of_le
      (by simp)
  have hcov_frame :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (frame j) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M => TangentSpace I p →L[𝕜] TangentSpace I p)))
        u := by
    simpa [u, frame] using (hcov hu).contMDiff hframe_smooth
  have hX_on :
      CMDiff[u] (∞ : WithTop ℕ∞) (T% (fun p : M => X p)) :=
    (X.contMDiff.of_le (by simp :
      (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).contMDiffOn
  have hW_on :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, (cov (frame j) p) (X p)⟩ :
            TotalSpace E (TangentSpace I : M -> Type _)))
        u := by
    simpa [frame] using hcov_frame.clm_bundle_apply hX_on
  exact (hW_on x₀ hx₀).contMDiffAt (hu.mem_nhds hx₀)

set_option backward.isDefEq.respectTransparency false in






theorem nabla0SFun_one_eval_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) :
    ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p) (fun _ : Fin 1 => Z p)) := by
  let pair : M -> 𝕜 := fun y => α y (fun _ : Fin 1 => Z y)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  let Zinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => Z p, Z.contMDiff.of_le (by simp)⟩
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair := by
    simpa [pair, αinf, Zinf] using
      (TensorMultilinear.contMDiff_tensor0SField_apply
        (E := E) (H := H) (I := I) (M := M) (n := 1)
        αinf (fun _ : Fin 1 => Zinf))
  have hderiv :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) :=
    extDerivFun_apply_contMDiff (I := I) pair hpair Xinf
  let W : (p : M) -> TangentSpace I p :=
    fun p : M => (cov (fun q : M => Z q) p) (X p)
  have hWtop :
      ContMDiff I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) := by
    simpa [W] using
      (TensorLieDeriv.covariantDeriv_vectorField_contMDiff
        (𝕜 := 𝕜) (I := I) (M := M) cov hcov X Z)
  let Winf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨W, hWtop.of_le (by simp)⟩
  have hcorr_raw :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => αinf p (fun _ : Fin 1 => Winf p)) := by
    simpa using
      (TensorMultilinear.contMDiff_tensor0SField_apply
        (E := E) (H := H) (I := I) (M := M) (n := 1)
        αinf (fun _ : Fin 1 => Winf))
  have hcorr :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => α p
          (fun _ : Fin 1 => (cov (fun q : M => Z q) p) (X p))) := by
    refine hcorr_raw.congr ?_
    intro p
    simp [αinf, Winf, W]
  have hmain :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            α p (fun _ : Fin 1 => (cov (fun q : M => Z q) p) (X p))) :=
    hderiv.sub hcorr
  refine hmain.congr ?_
  intro p
  rw [nabla0SFun_one_eval_coordFrame_moving
    (I := I) cov X Z α p
    (modelDeriv_eq_coordDeriv0SAt (I := I) X p α)
    (fun j =>
      (coordinateFrame_coeff_contMDiffAt (I := I) Z p j).mdifferentiableAt
        (by simp))
    (fun j =>
        (oneForm_eval_coordinateFrame_contMDiffAt (I := I) α p j).mdifferentiableAt
        (by simp))]

set_option backward.isDefEq.respectTransparency false in






theorem nabla0SFun_one_eval_coordinateFrame_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p)
          (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)) x₀ := by
  let Z : (p : M) -> TangentSpace I p := coordinateFrameAt (I := I) x₀ j
  let pair : M -> 𝕜 := fun p => α p (fun _ : Fin 1 => Z p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    simpa [pair, Z] using oneForm_eval_coordinateFrame_contMDiffAt
      (I := I) α x₀ j
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ :=
    extDerivFun_apply_contMDiffAt (I := I) hpair Xinf
  let W : (p : M) -> TangentSpace I p :=
    fun p : M => (cov Z p) (X p)
  have hW :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    simpa [W, Z] using
      coordinateFrame_covariantDeriv_apply_contMDiffAt
        (I := I) cov hcov X x₀ j
  have hcorr_raw :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => αinf p (fun _ : Fin 1 => W p)) x₀ := by
    simpa using
      (TensorMultilinear.contMDiffAt_section_apply_gen
        (I := I) (M := M) (n := 1) (x₀ := x₀)
        (T := fun p : M => αinf p) αinf.contMDiff.contMDiffAt
        (v := fun _ : Fin 1 => W)
        (hv := fun _ : Fin 1 => hW))
  have hcorr :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => α p (fun _ : Fin 1 => W p)) x₀ := by
    refine hcorr_raw.congr_of_eventuallyEq ?_
    filter_upwards with p
    simp [αinf]
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            α p (fun _ : Fin 1 => W p)) x₀ :=
    hderiv.sub hcorr
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hZ_at :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) p := by
    simpa [Z] using
      (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hp j
  rw [nabla0SFun_one_eval_coordFrame_moving_raw
    (I := I) cov X Z α p
    (modelDeriv_eq_coordDeriv0SAt (I := I) X p α)
    (fun k =>
      (coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
        (I := I) Z hZ_at k).mdifferentiableAt (by simp))
    (fun k =>
      (oneForm_eval_coordinateFrame_contMDiffAt
        (I := I) α p k).mdifferentiableAt (by simp))
    (hZ_at.mdifferentiableAt (by simp))]

set_option backward.isDefEq.respectTransparency false in






theorem nabla0SFun_one_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) 1
    ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel 1 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p⟩ :
          TotalSpace (Tensor0SModel 1 𝕜 E) (fun p : M => Tensor0SSpace 1 I p))) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) 1
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) 1 p :=
    fun p : M =>
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 cov X α p
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  let j : CoordinateIdx (𝕜 := 𝕜) E := σ 0
  have hframe_eval :=
    nabla0SFun_one_eval_coordinateFrame_contMDiffAt
      (I := I) cov hcov X α x₀ j
  refine hframe_eval.congr_of_eventuallyEq ?_
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hslot :
      (fun a : Fin 1 =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p
            (b (σ a))) =
        fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p := by
    funext a
    fin_cases a
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hp
    rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := p) hp j]
    simpa [j, b] using
      congrArg
        (fun L : E →L[𝕜] TangentSpace I p => L (b j))
        (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hp_src)
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 1 𝕜 E)
      (Bundle.continuousMultilinearMap 𝕜 1 E (TangentSpace I : M -> Type _)) x₀
      ⟨p, F p⟩).2)
      (fun a : Fin 1 => b (σ a)) =
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α p) (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)
  change (F p).compContinuousLinearMap
      (fun _ : Fin 1 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
      (fun a : Fin 1 => b (σ a)) =
    F p (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hslot]
end DifferentialGeometry.Tensor.Coordinates
