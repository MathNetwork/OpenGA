import DifferentialGeometry.Geometry.Connection.Realization.Tensor0SBridge
import DifferentialGeometry.Geometry.Connection.Realization.HomNabla


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

noncomputable def tensor0SCovariantDerivative_zero_fun
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 0 I x :=
  ((tensor0Iso I M x).symm.toContinuousLinearMap).comp
    (extDerivFun (I := I) (scalarFn I M T) x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tensor0SCovariantDerivative_zero_fun_apply
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative_zero_fun I M T x v =
      (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T) x v) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SCovariantDerivative_zero_fun_add_section
    (T₁ T₂ : Π x : M, Tensor0SSpace 0 I x)
    {x : M}
    (h₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₁) x)
    (h₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₂) x) :
    tensor0SCovariantDerivative_zero_fun I M (T₁ + T₂) x =
      tensor0SCovariantDerivative_zero_fun I M T₁ x +
      tensor0SCovariantDerivative_zero_fun I M T₂ x := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  change (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M (T₁ + T₂)) x v) =
    (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T₁) x v) +
    (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T₂) x v)
  rw [scalarFn_add I M T₁ T₂, extDerivFun_add h₁ h₂]
  change (tensor0Iso I M x).symm
    ((extDerivFun (I := I) (scalarFn I M T₁) x v +
     extDerivFun (I := I) (scalarFn I M T₂) x v : ℝ)) = _
  exact map_add (tensor0Iso I M x).symm _ _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SCovariantDerivative_zero_fun_leibniz_section
    (T : Π x : M, Tensor0SSpace 0 I x) (g : M → ℝ) {x : M}
    (hT : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    tensor0SCovariantDerivative_zero_fun I M (g • T) x =
      g x • tensor0SCovariantDerivative_zero_fun I M T x +
      (extDerivFun (I := I) g x).smulRight (T x) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  change (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M (g • T)) x v) =
    (g x • tensor0SCovariantDerivative_zero_fun I M T x +
      (extDerivFun (I := I) g x).smulRight (T x)) v
  rw [scalarFn_smul]
  have h_extDeriv_eq : ∀ (h : M → ℝ) (v : TangentSpace I x),
      extDerivFun (I := I) h x v =
      NormedSpace.fromTangentSpace (h x) ((mfderiv I 𝓘(ℝ, ℝ) h x) v) := by
    intro h v
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [h_extDeriv_eq _ v]
  have h_prod := fromTangentSpace_mfderiv_smul_apply (I := I) hg hT v
  change (tensor0Iso I M x).symm
      (NormedSpace.fromTangentSpace ((g • scalarFn I M T) x)
        ((mfderiv I 𝓘(ℝ, ℝ) (g • scalarFn I M T) x) v)) = _
  rw [h_prod]
  rw [map_add]
  have h_eq1 : (NormedSpace.fromTangentSpace (scalarFn I M T x))
      (((mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T)) x) v) =
      (extDerivFun (I := I) (scalarFn I M T) x) v :=
    (h_extDeriv_eq (scalarFn I M T) v).symm
  have h_eq2 : (NormedSpace.fromTangentSpace (g x))
      (((mfderiv I 𝓘(ℝ, ℝ) g) x) v) =
      (extDerivFun (I := I) g x) v :=
    (h_extDeriv_eq g v).symm
  rw [show ((g x) • NormedSpace.fromTangentSpace (scalarFn I M T x)
      (((mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T)) x) v) : ℝ) =
      g x • (extDerivFun (I := I) (scalarFn I M T) x) v from by rw [h_eq1]]
  rw [show ((NormedSpace.fromTangentSpace (g x)) (((mfderiv I 𝓘(ℝ, ℝ) g) x) v)
      • scalarFn I M T x : ℝ) =
      (extDerivFun (I := I) g x) v • scalarFn I M T x from by rw [h_eq2]]
  rw [map_smul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change g x • (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T) x v) +
    (tensor0Iso I M x).symm ((extDerivFun (I := I) g x v) • scalarFn I M T x) =
    g x • (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T) x v) +
    (extDerivFun (I := I) g x v) • T x
  congr 1
  rw [map_smul]
  rw [tensor0Iso_symm_scalarFn]

noncomputable def tensor0SCovariantDerivative_succ_fun {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [ContMDiffCovariantDerivative cov_s ∞]
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x :=
  ((tensor0S_curry (I := I) (M := M) s x).symm.toContinuousLinearMap).comp
    (HomConnection.homBundleCovariantDerivativeFun I M
      (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
      cov_TM cov_s (curriedSection I M T) x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tensor0SCovariantDerivative_succ_fun_apply {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [ContMDiffCovariantDerivative cov_s ∞]
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative_succ_fun I M cov_TM cov_s T x v =
      (tensor0S_curry (I := I) (M := M) s x).symm
        (HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s (curriedSection I M T) x v) := rfl

noncomputable def tensor0SCovariantDerivative_zero
    (_cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative _cov ∞] :
    CovariantDerivative I (Tensor0SModel 0 ℝ E) (fun x : M => Tensor0SSpace 0 I x) where
  toFun := tensor0SCovariantDerivative_zero_fun I M
  isCovariantDerivativeOnUniv := {
    add := by
      intro T₁ T₂ x hT₁ hT₂ _hx
      have hT₁_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₁) x :=
        (mdifferentiableAt_scalarFn_iff_section I M T₁).mpr hT₁
      have hT₂_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₂) x :=
        (mdifferentiableAt_scalarFn_iff_section I M T₂).mpr hT₂
      exact tensor0SCovariantDerivative_zero_fun_add_section I M T₁ T₂ hT₁_scalar hT₂_scalar
    leibniz := by
      intro T g x hT hg _hx
      have hT_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x :=
        (mdifferentiableAt_scalarFn_iff_section I M T).mpr hT
      exact tensor0SCovariantDerivative_zero_fun_leibniz_section I M T g hT_scalar hg
  }

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0SCov_zero_scalar_at_Y
    (T : Π x : M, Tensor0SSpace 0 I x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) y (T y)))
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (scalarFn I M T) x (Y x)) := by
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn I M T) :=
    (contMDiff_scalarFn_iff_section I M T).mpr hT
  let fscalar : C^∞⟮I, M; ℝ⟯ := ⟨scalarFn I M T, fun x => hscalar.contMDiffAt⟩
  have h_extDeriv_section :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x (extDerivFun (I := I) fscalar x)) :=
    contMDiff_extDerivFun_section I M fscalar
  let d_fscalar : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
    ⟨fun x => extDerivFun (I := I) (scalarFn I M T) x, h_extDeriv_section⟩
  have := contMDiff_dual_apply_section I M d_fscalar Y
  simpa [d_fscalar] using this

noncomputable instance tensor0SCovariantDerivative_zero_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (tensor0SCovariantDerivative_zero I M cov) ∞ where
  contMDiff := {
    contMDiff := by
      intro T hT
      have hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
          (fun x => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
            (E := fun x : M => Tensor0SSpace 0 I x) x (T x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hT
        rwa [← contMDiffOn_univ]
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := fun x : M => Tensor0SSpace 0 I x)
        (φ := fun x => tensor0SCovariantDerivative_zero_fun I M T x)
      intro Y
      have h_scalar_at_Y := tensor0SCov_zero_scalar_at_Y I M T hT_smooth Y
      let f : C^∞⟮I, M; ℝ⟯ :=
        ⟨fun x => extDerivFun (I := I) (scalarFn I M T) x (Y x),
         fun x => h_scalar_at_Y.contMDiffAt⟩
      have h_iso_scalar : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
          (fun x => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
            (E := fun x : M => Tensor0SSpace 0 I x) x
            (tensor0SCovariantDerivative_zero_fun I M T x (Y x))) := by
        let S : Π x : M, Tensor0SSpace 0 I x :=
          fun x => tensor0SCovariantDerivative_zero_fun I M T x (Y x)
        have h_scalarFn_eq : scalarFn I M S = (f : M → ℝ) := by
          funext x
          change tensor0Iso I M x ((tensor0Iso I M x).symm
            (extDerivFun (I := I) (scalarFn I M T) x (Y x))) = _
          exact (tensor0Iso I M x).apply_symm_apply
            (extDerivFun (I := I) (scalarFn I M T) x (Y x))
        have h_scalarFn_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn I M S) := by
          rw [h_scalarFn_eq]; exact f.contMDiff
        exact (contMDiff_scalarFn_iff_section (I := I) (M := M) S).mp h_scalarFn_smooth
      exact h_iso_scalar
  }

noncomputable def tensor0SCovariantDerivative_succ {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [ContMDiffCovariantDerivative cov_s ∞] :
    letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x)) :=
      tensor0SBundle_topology (s + 1)
    letI _h_fib : FiberBundle (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) :=
      tensor0SBundle_fiber (s + 1)
    CovariantDerivative I (Tensor0SModel (s+1) ℝ E)
      (fun x : M => Tensor0SSpace (s+1) I x) :=
  { toFun := tensor0SCovariantDerivative_succ_fun I M cov_TM cov_s
    isCovariantDerivativeOnUniv := {
    add := by
      intro T₁ T₂ x hT₁ hT₂ _hx
      have hC₁ := (mdifferentiableAt_curriedSection_iff_section I M T₁).mp hT₁
      have hC₂ := (mdifferentiableAt_curriedSection_iff_section I M T₂).mp hT₂
      have h_curried_add : curriedSection I M (T₁ + T₂) =
          curriedSection I M T₁ + curriedSection I M T₂ :=
        curriedSection_add (I := I) (M := M) T₁ T₂
      have h_homAdd := (HomConnection.homBundleCovariantDerivative I M
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s).isCovariantDerivativeOnUniv.add hC₁ hC₂
      refine ContinuousLinearMap.ext (fun v => ?_)
      simp only [tensor0SCovariantDerivative_succ_fun_apply, ContinuousLinearMap.add_apply]
      rw [h_curried_add]
      have h_hom_add_apply :
          HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T₁ + curriedSection I M T₂) x =
          HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T₁) x +
          HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T₂) x := h_homAdd
      rw [h_hom_add_apply]
      rw [ContinuousLinearMap.add_apply]
      exact map_add (tensor0S_curry (I := I) (M := M) s x).symm _ _
    leibniz := by
      intro T g x hT hg _hx
      have hC := (mdifferentiableAt_curriedSection_iff_section I M T).mp hT
      have h_homLeib := (HomConnection.homBundleCovariantDerivative I M
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s).isCovariantDerivativeOnUniv.leibniz hC hg
      have h_curried_smul : curriedSection I M (g • T) = g • curriedSection I M T :=
        curriedSection_smul (I := I) (M := M) g T
      refine ContinuousLinearMap.ext (fun v => ?_)
      simp only [tensor0SCovariantDerivative_succ_fun_apply]
      rw [h_curried_smul]
      have h_hom_leib_apply :
          HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (g • curriedSection I M T) x =
          g x • HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x +
          (extDerivFun (I := I) g x).smulRight (curriedSection I M T x) := h_homLeib
      rw [h_hom_leib_apply]
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [map_add, map_smul]
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      congr 1
      rw [map_smul]
      congr 1
      change (tensor0S_curry (I := I) (M := M) s x).symm
          (tensor0S_curry (I := I) (M := M) s x (T x)) = T x
      exact (tensor0S_curry (I := I) (M := M) s x).symm_apply_apply (T x)
  } }

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem contMDiff_tensor0SCov_succ_section {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [ContMDiffCovariantDerivative cov_s ∞]
    (T : Π x : M, Tensor0SSpace (s+1) I x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s+1) I x) y (T y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel (s+1) ℝ E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => (TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x))
        x (tensor0SCovariantDerivative_succ_fun I M cov_TM cov_s T x)) := by
  have hCurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        y (curriedSection I M T y)) :=
    (contMDiff_curriedSection_iff_section I M T).mp hT
  let τ_section : Cₛ^∞⟮I; E →L[ℝ] Tensor0SModel s ℝ E,
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)⟯ :=
    ⟨curriedSection I M T, hCurried⟩
  have h_hom_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] Tensor0SSpace s I x))
        x (HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s (curriedSection I M T) x)) := by
    have hτ_plus : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) (∞ + 1)
        (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
          (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
          x (τ_section x)) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact τ_section.contMDiff
    haveI : ContMDiffCovariantDerivative
      (HomConnection.homBundleCovariantDerivative I M
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s) ∞ :=
      HomConnection.homBundleCovariantDerivative_contMDiff I M
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) cov_TM cov_s
    have h_hom_cov :=
      (‹ContMDiffCovariantDerivative
        (HomConnection.homBundleCovariantDerivative I M
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s) ∞›).contMDiff.contMDiff hτ_plus.contMDiffOn
    rwa [← contMDiffOn_univ]
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I)
    (V₂ := fun x : M => Tensor0SSpace (s+1) I x)
    (φ := fun x => tensor0SCovariantDerivative_succ_fun I M cov_TM cov_s T x)
  intro Y
  have h_hom_at_Y :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) h_hom_smooth Y.contMDiff
  let S : Π x : M, Tensor0SSpace (s+1) I x :=
    fun x => tensor0SCovariantDerivative_succ_fun I M cov_TM cov_s T x (Y x)
  have h_curried_S :
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (curriedSection I M S x)) =
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))) := by
    funext x
    have h_S_val : tensor0S_curry (I := I) (M := M) s x (S x) =
      HomConnection.homBundleCovariantDerivativeFun I M
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s (curriedSection I M T) x (Y x) := by
      change tensor0S_curry (I := I) (M := M) s x
        ((tensor0S_curry (I := I) (M := M) s x).symm
          (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))) = _
      exact (tensor0S_curry (I := I) (M := M) s x).apply_symm_apply _
    change TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (curriedSection I M S x) =
      TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))
    rw [← h_S_val]
    rfl
  rw [← h_curried_S] at h_hom_at_Y
  exact (contMDiff_curriedSection_iff_section I M S).mpr h_hom_at_Y

noncomputable instance tensor0SCovariantDerivative_succ_contMDiff {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [ContMDiffCovariantDerivative cov_s ∞] :
    ContMDiffCovariantDerivative
      (tensor0SCovariantDerivative_succ I M cov_TM cov_s) ∞ where
  contMDiff := {
    contMDiff := by
      intro T hT
      have hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)) ∞
          (fun x => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
            (E := fun x : M => Tensor0SSpace (s+1) I x) x (T x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hT
        rwa [← contMDiffOn_univ]
      rw [contMDiffOn_univ]
      exact contMDiff_tensor0SCov_succ_section I M cov_TM cov_s T hT_smooth
  }

private structure SmoothCov (s : ℕ)
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] where
  toCov : CovariantDerivative I (Tensor0SModel s ℝ E)
    (fun x : M => Tensor0SSpace s I x)
  smooth : ContMDiffCovariantDerivative toCov ∞

private noncomputable def tensor0SCovariantDerivative_aux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    (s : ℕ) → SmoothCov (E := E) s I M
  | 0 => ⟨tensor0SCovariantDerivative_zero I M cov, inferInstance⟩
  | n + 1 =>
    let prev := tensor0SCovariantDerivative_aux cov n
    haveI : ContMDiffCovariantDerivative prev.toCov ∞ := prev.smooth
    ⟨tensor0SCovariantDerivative_succ I M cov prev.toCov, inferInstance⟩

noncomputable def tensor0SCovariantDerivative (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) :=
  (tensor0SCovariantDerivative_aux I M cov s).toCov

noncomputable instance tensor0SCovariantDerivative_contMDiff (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (tensor0SCovariantDerivative I M s cov) ∞ :=
  (tensor0SCovariantDerivative_aux I M cov s).smooth

omit [CompleteSpace E] in
theorem tensor0SCovariantDerivative_zero_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    tensor0SCovariantDerivative I M 0 cov =
      tensor0SCovariantDerivative_zero I M cov := rfl

omit [CompleteSpace E] in
theorem tensor0SCovariantDerivative_succ_eq {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    tensor0SCovariantDerivative I M (s+1) cov =
      tensor0SCovariantDerivative_succ I M cov
        (tensor0SCovariantDerivative I M s cov) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SCovariantDerivative_zero_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative_zero I M cov T x v =
      (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T) x v) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_succ_apply {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [ContMDiffCovariantDerivative cov_s ∞]
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative_succ I M cov_TM cov_s T x v =
      (tensor0S_curry (I := I) (M := M) s x).symm
        (HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s (curriedSection I M T) x v) := rfl

omit [CompleteSpace E] in
theorem tensor0SCovariantDerivative_apply_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M 0 cov T x v =
      (tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T) x v) := by
  rw [tensor0SCovariantDerivative_zero_eq]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalarFn_unitZero :
    scalarFn I M
        (fun _ : M => Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) =
      fun _ : M => (1 : ℝ) := by
  funext y
  rw [scalarFn_apply]
  change (tensor0SSpace_continuousLinearEquiv (I := I) 0 y).trans
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv
      ((tensor0SSpace_continuousLinearEquiv (I := I) 0 y).symm
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = (1 : ℝ)
  rw [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) = (1 : ℝ)
  rw [continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.constOfIsEmpty_apply]

omit [CompleteSpace E] in
theorem tensor0SCovariantDerivative_unitZero_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M 0 cov
        (fun _ : M => Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
        x v = 0 := by
  rw [tensor0SCovariantDerivative_apply_zero, scalarFn_unitZero]
  have hext : extDerivFun (I := I) (fun _ : M => (1 : ℝ)) x = 0 := by
    unfold extDerivFun
    simp [mfderiv_const]
  rw [hext]
  simp

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (Tensor0SModel 3 ℝ E)
      (fun x : M => Tensor0SSpace 3 I x) :=
  tensor0SCovariantDerivative I M 3 cov

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative
      (tensor0SCovariantDerivative I M 3 cov) ∞ :=
  inferInstance

end Tensor0SNabla

end
