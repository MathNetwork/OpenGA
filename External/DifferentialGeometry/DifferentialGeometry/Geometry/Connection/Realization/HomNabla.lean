import DifferentialGeometry.Geometry.Connection.Realization.TensorNabla
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Connection.Realization.Connection
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

namespace HomConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I]

private abbrev MDiffAtHom
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x)) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
    (fun y => TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) y (τ y)) x

private abbrev MDiffAtVec
    (Y : Π x : M, TangentSpace I x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x

private abbrev MDiffAtV (σ : Π x : M, V x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, F))
    (fun y => TotalSpace.mk' F (E := V) y (σ y)) x

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem mdiffAt_apply
    {τ : Π x : M, (TangentSpace I x →L[ℝ] V x)}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hτ : MDiffAtHom I M F V τ x) (hY : MDiffAtVec I M Y x) :
    MDiffAtV I M F V (fun y => τ y (Y y)) x := by
  exact MDifferentiableAt.clm_bundle_apply (b := id) hτ hY

private def Psi
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    (V_field Y : Π x : M, TangentSpace I x) (x : M) : V x :=
  cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_TM Y x (V_field x))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_add_left
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {V_field V_field' Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M F V cov_TM cov_V τ (V_field + V_field') Y x =
      Psi I M F V cov_TM cov_V τ V_field Y x + Psi I M F V cov_TM cov_V τ V_field' Y x := by
  have h_add : (V_field + V_field' : Π x : M, TangentSpace I x) x = V_field x + V_field' x := rfl
  simp only [Psi, h_add, ContinuousLinearMap.map_add]
  abel

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_smul_left
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {f : M → ℝ} {V_field Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M F V cov_TM cov_V τ (f • V_field) Y x = f x • Psi I M F V cov_TM cov_V τ V_field Y x := by
  have h_smul : (f • V_field : Π x : M, TangentSpace I x) x = f x • V_field x := rfl
  simp only [Psi, h_smul, ContinuousLinearMap.map_smul]
  rw [smul_sub]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_add_right
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {V_field Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hτ : MDiffAtHom I M F V τ x)
    (hY : MDiffAtVec I M Y x) (hY' : MDiffAtVec I M Y' x) :
    Psi I M F V cov_TM cov_V τ V_field (Y + Y') x =
      Psi I M F V cov_TM cov_V τ V_field Y x + Psi I M F V cov_TM cov_V τ V_field Y' x := by

  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M F V hτ hY
  have hτY' : MDiffAtV I M F V (fun y => τ y (Y' y)) x := mdiffAt_apply I M F V hτ hY'
  have h_add_fun : (fun y => τ y ((Y + Y') y)) =
      (fun y => τ y (Y y)) + (fun y => τ y (Y' y)) := by
    funext y
    simp [Pi.add_apply, ContinuousLinearMap.map_add]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  have hY'_T : MDiffAt (T% fun y => Y' y) x := hY'
  simp only [Psi]

  rw [h_add_fun, cov_V.isCovariantDerivativeOn.add hτY hτY']
  rw [show (Y + Y' : Π x : M, TangentSpace I x) = (fun x => Y x) + (fun x => Y' x) from rfl,
      cov_TM.isCovariantDerivativeOn.add hY_T hY'_T]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
  abel

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_smul_right
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {V_field Y : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hτ : MDiffAtHom I M F V τ x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hY : MDiffAtVec I M Y x) :
    Psi I M F V cov_TM cov_V τ V_field (f • Y) x = f x • Psi I M F V cov_TM cov_V τ V_field Y x := by
  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M F V hτ hY

  have h_fun : (fun y => τ y ((f • Y) y)) = f • (fun y => τ y (Y y)) := by
    funext y
    exact ContinuousLinearMap.map_smul (τ y) (f y) (Y y)
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  simp only [Psi]
  rw [h_fun]

  rw [cov_V.isCovariantDerivativeOn.leibniz hτY hf]

  rw [show (f • Y : Π x : M, TangentSpace I x) = f • (fun x => Y x) from rfl,
      cov_TM.isCovariantDerivativeOn.leibniz hY_T hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul]

  rw [smul_sub]

  abel

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_tensorialAt_left
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (Y : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun V_field => Psi I M F V cov_TM cov_V τ V_field Y x) x where
  smul := fun _ _ => Psi_smul_left I M F V cov_TM cov_V τ
  add := fun _ _ => Psi_add_left I M F V cov_TM cov_V τ

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_tensorialAt_right
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x) (V_field : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun Y => Psi I M F V cov_TM cov_V τ V_field Y x) x where
  smul := fun hf hY => Psi_smul_right I M F V cov_TM cov_V τ hτ hf hY
  add := fun hY hY' => Psi_add_right I M F V cov_TM cov_V τ hτ hY hY'

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem hom_section_mdiff
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (x : M) : MDiffAtHom I M F V (τ : Π x : M, (TangentSpace I x →L[ℝ] V x)) x :=
  τ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem vec_section_mdiff
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

noncomputable def homBundleCovariantDerivativeFun
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] V x) := by
  classical
  by_cases hτ : MDiffAtHom I M F V τ x
  · exact TensorialAt.mkHom₂ (F := E) (F' := E)
      (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
      (A := V x)
      (fun V_field Y => Psi I M F V cov_TM cov_V τ V_field Y x) x
      (fun Y _ => Psi_tensorialAt_left I M F V cov_TM cov_V τ Y)
      (fun V_field _ => Psi_tensorialAt_right I M F V cov_TM cov_V τ hτ V_field)
  · exact 0

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
theorem homBundleCovariantDerivativeFun_apply
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x)
    {V_field Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V_field x) (hY : MDiffAtVec I M Y x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x (V_field x) (Y x) =
      Psi I M F V cov_TM cov_V τ V_field Y x := by
  unfold homBundleCovariantDerivativeFun
  rw [dif_pos hτ]
  exact TensorialAt.mkHom₂_apply
    (Φ := fun V_field Y => Psi I M F V cov_TM cov_V τ V_field Y x)
    (fun Y _ => Psi_tensorialAt_left I M F V cov_TM cov_V τ Y)
    (fun V_field _ => Psi_tensorialAt_right I M F V cov_TM cov_V τ hτ V_field) hV hY

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
theorem homBundleCovariantDerivativeFun_apply_eq
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x)
    {V_field Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V_field x) (hY : MDiffAtVec I M Y x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x (V_field x) (Y x) =
      cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_TM Y x (V_field x)) := by
  rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ hV hY]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem homBundleCovariantDerivativeFun_of_not_mdiff
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : ¬ MDiffAtHom I M F V τ x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x = 0 := by
  unfold homBundleCovariantDerivativeFun
  rw [dif_neg hτ]

omit [CompleteSpace E] [SigmaCompactSpace M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem homBundleCovariantDerivativeFun_isCovOn
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V) :
    IsCovariantDerivativeOn (E →L[ℝ] F)
      (homBundleCovariantDerivativeFun I M F V cov_TM cov_V) Set.univ where
  add := by
    intro τ₁ τ₂ x hτ₁ hτ₂ _hx
    have hτ₁' : MDiffAtHom I M F V τ₁ x := hτ₁
    have hτ₂' : MDiffAtHom I M F V τ₂ x := hτ₂
    have hτ_sum : MDiffAtHom I M F V (τ₁ + τ₂) x :=
      mdifferentiableAt_add_section (F := E →L[ℝ] F) hτ₁ hτ₂
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V_field : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V_field x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V (τ₁ + τ₂) hτ_sum hV_diff hY_diff]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ₁ hτ₁' hV_diff hY_diff]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ₂ hτ₂' hV_diff hY_diff]

    have h_funeq : (fun y => (τ₁ + τ₂) y (Y y)) =
        (fun y => τ₁ y (Y y)) + (fun y => τ₂ y (Y y)) := by
      funext y
      simp [Pi.add_apply, ContinuousLinearMap.add_apply]
    have hτ₁Y : MDiffAtV I M F V (fun y => τ₁ y (Y y)) x :=
      mdiffAt_apply I M F V hτ₁' hY_diff
    have hτ₂Y : MDiffAtV I M F V (fun y => τ₂ y (Y y)) x :=
      mdiffAt_apply I M F V hτ₂' hY_diff
    simp only [Psi]
    rw [h_funeq, cov_V.isCovariantDerivativeOn.add hτ₁Y hτ₂Y]
    simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
    abel
  leibniz := by
    intro τ g x hτ hg _hx
    have hτ' : MDiffAtHom I M F V τ x := hτ
    have hgτ : MDiffAtHom I M F V (g • τ) x :=
      hg.smul_section (F := E →L[ℝ] F) hτ
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V_field : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V_field x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V (g • τ) hgτ hV_diff hY_diff]

    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ' hV_diff hY_diff]

    have h_funeq : (fun y => (g • τ) y (Y y)) = g • (fun y => τ y (Y y)) := by
      funext y
      rfl
    have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x :=
      mdiffAt_apply I M F V hτ' hY_diff
    simp only [Psi]
    rw [h_funeq]
    rw [cov_V.isCovariantDerivativeOn.leibniz hτY hg]
    have hgτ_apply : (g • τ) x = g x • τ x := rfl
    rw [hgτ_apply]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [smul_sub]
    abel

noncomputable def homBundleCovariantDerivative
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V) :
    CovariantDerivative I (E →L[ℝ] F)
      (fun x => TangentSpace I x →L[ℝ] V x) where
  toFun := homBundleCovariantDerivativeFun I M F V cov_TM cov_V
  isCovariantDerivativeOnUniv := homBundleCovariantDerivativeFun_isCovOn I M F V cov_TM cov_V

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem contMDiff_hom_apply_section
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Y y))) := by
  exact ContMDiff.clm_bundle_apply (b := id) τ.contMDiff Y.contMDiff

omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace F] in
private theorem homBundleCov_section_smooth
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞]
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M => (TangentSpace I x →L[ℝ] V x))
        x ((homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x) (Y x))) := by

  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := V)
    (φ := fun x => (homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x) (Y x))
  intro Z

  have hτZ_section : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Z y))) :=
    contMDiff_hom_apply_section I M F V τ Z
  let τZ : Cₛ^∞⟮I; F, V⟯ := ⟨fun y => τ y (Z y), hτZ_section⟩

  have hcov_V_τZ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) x (cov_V τZ x)) := by
    have hτZ_plus : ContMDiff I (I.prod 𝓘(ℝ, F)) (∞ + 1) (T% fun x => τZ x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact τZ.contMDiff
    have hcov_V_smooth :=
      (‹ContMDiffCovariantDerivative cov_V ∞›).contMDiff.contMDiff hτZ_plus.contMDiffOn
    rwa [← contMDiffOn_univ]

  have h_first : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (cov_V τZ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov_V_τZ Y.contMDiff

  have h_concrete : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x
        ((concreteConn I M cov_TM Y Z) x)) :=
    (concreteConn I M cov_TM Y Z).contMDiff

  have h_second : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (τ x ((concreteConn I M cov_TM Y Z) x))) :=
    ContMDiff.clm_bundle_apply (b := id) τ.contMDiff h_concrete

  have h_eq : ∀ x, (homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x) (Y x) (Z x) =
      cov_V τZ x (Y x) - τ x ((concreteConn I M cov_TM Y Z) x) := by
    intro x
    have hτ_diff := hom_section_mdiff I M F V τ x
    have hY_diff := vec_section_mdiff I M Y x
    have hZ_diff := vec_section_mdiff I M Z x
    rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ_diff hY_diff hZ_diff]
    rfl

  have h_diff : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x
        (cov_V τZ x (Y x) - τ x ((concreteConn I M cov_TM Y Z) x))) := by

    let s₁ : Cₛ^∞⟮I; F, V⟯ := ⟨fun x => cov_V τZ x (Y x), h_first⟩
    let s₂ : Cₛ^∞⟮I; F, V⟯ :=
      ⟨fun x => τ x ((concreteConn I M cov_TM Y Z) x), h_second⟩
    have : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F (E := V) x ((s₁ - s₂) x)) := (s₁ - s₂).contMDiff
    convert this using 1

  intro x₀
  rw [contMDiffAt_section]
  have h_diff_at := h_diff x₀
  rw [contMDiffAt_section] at h_diff_at
  refine h_diff_at.congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [h_eq]

noncomputable instance homBundleCovariantDerivative_contMDiff
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞] :
    ContMDiffCovariantDerivative (homBundleCovariantDerivative I M F V cov_TM cov_V) ∞ where
  contMDiff := {
    contMDiff := by
      intro τ hτ
      have hτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
          (fun x => TotalSpace.mk' (E →L[ℝ] F)
            (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) x (τ x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hτ
        rwa [← contMDiffOn_univ]
      let τ_section : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯ :=
        ⟨τ, hτ_smooth⟩
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := fun x => TangentSpace I x →L[ℝ] V x)
        (φ := fun x => homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x)
      intro Y
      exact homBundleCov_section_smooth I M F V cov_TM cov_V τ_section Y
  }

omit [CompleteSpace E] [SigmaCompactSpace M] [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
theorem homBundleCovariantDerivative_apply
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    (homBundleCovariantDerivative I M F V cov_TM cov_V τ x v) (Y x) =
      cov_V (fun y => τ y (Y y)) x v - τ x (cov_TM Y x v) := by
  change homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x v (Y x) = _
  obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hτ_diff := hom_section_mdiff I M F V τ x
  have hV_diff := vec_section_mdiff I M V_field x
  have hY_diff := vec_section_mdiff I M Y x
  rw [show v = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
  rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ_diff hV_diff hY_diff]
  rfl

end HomConnection

end
