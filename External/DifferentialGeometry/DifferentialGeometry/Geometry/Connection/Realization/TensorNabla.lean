import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Connection.Realization.Connection
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality


noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

section DualConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev MDiffAtDual
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)) y (α y)) x

private abbrev MDiffAtVec
    (Y : Π x : M, TangentSpace I x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mdiffAt_pairing
    {α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hα : MDiffAtDual I M α x) (hY : MDiffAtVec I M Y x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x := by

  have h := MDifferentiableAt.clm_bundle_apply (b := id) hα hY

  have h' : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m (α m (Y m))) x := h

  rw [mdifferentiableAt_section (F := ℝ) (E := Bundle.Trivial M ℝ)] at h'

  exact h'

private def Psi
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    (V Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  extDerivFun (fun y => α y (Y y)) x (V x) - (α x) (cov Y x (V x))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V V' Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M cov α (V + V') Y x = Psi I M cov α V Y x + Psi I M cov α V' Y x := by
  have h_add : (V + V' : Π x : M, TangentSpace I x) x = V x + V' x := rfl
  simp only [Psi, h_add, ContinuousLinearMap.map_add]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {f : M → ℝ} {V Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M cov α (f • V) Y x = f x • Psi I M cov α V Y x := by
  have h_smul : (f • V : Π x : M, TangentSpace I x) x = f x • V x := rfl
  simp only [Psi, h_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hα : MDiffAtDual I M α x)
    (hY : MDiffAtVec I M Y x) (hY' : MDiffAtVec I M Y' x) :
    Psi I M cov α V (Y + Y') x = Psi I M cov α V Y x + Psi I M cov α V Y' x := by

  have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
    mdiffAt_pairing I M hα hY
  have hαY' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y' y)) x :=
    mdiffAt_pairing I M hα hY'
  have h_add_fun : (fun y => α y ((Y + Y') y)) =
      (fun y => α y (Y y)) + (fun y => α y (Y' y)) := by
    funext y
    simp [Pi.add_apply, ContinuousLinearMap.map_add]

  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  have hY'_T : MDiffAt (T% fun y => Y' y) x := hY'
  simp only [Psi]
  rw [h_add_fun, extDerivFun_add hαY hαY']
  rw [show (Y + Y' : Π x : M, TangentSpace I x) = (fun x => Y x) + (fun x => Y' x) from rfl,
    cov.isCovariantDerivativeOn.add hY_T hY'_T]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_smul_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V Y : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hα : MDiffAtDual I M α x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hY : MDiffAtVec I M Y x) :
    Psi I M cov α V (f • Y) x = f x • Psi I M cov α V Y x := by
  have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
    mdiffAt_pairing I M hα hY
  have h_fun : (fun y => α y ((f • Y) y)) = f • (fun y => α y (Y y)) := by
    funext y
    simp [smul_eq_mul]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  simp only [Psi]
  rw [h_fun]
  have h_extDeriv_eq : ∀ (h : M → ℝ) (y : M) (w : TangentSpace I y),
      extDerivFun (I := I) h y w =
      NormedSpace.fromTangentSpace (h y) ((mfderiv I 𝓘(ℝ, ℝ) h y) w) := by
    intro h y w
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have h_prod := fromTangentSpace_mfderiv_smul_apply (I := I) hf hαY (V x)
  rw [h_extDeriv_eq _ _ (V x), h_prod]

  rw [show (f • Y : Π x : M, TangentSpace I x) = f • (fun x => Y x) from rfl,
    cov.isCovariantDerivativeOn.leibniz hY_T hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul, smul_eq_mul]

  have h_eq2 : (NormedSpace.fromTangentSpace ((α x) (Y x)))
      (((mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (Y y))) x) (V x)) =
      (extDerivFun (fun y => α y (Y y)) x) (V x) :=
    (h_extDeriv_eq (fun y => α y (Y y)) x (V x)).symm
  have h_eq3 : (NormedSpace.fromTangentSpace (f x))
      (((mfderiv I 𝓘(ℝ, ℝ) f) x) (V x)) =
      (extDerivFun f x) (V x) :=
    (h_extDeriv_eq f x (V x)).symm
  rw [h_eq2, h_eq3]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_tensorialAt_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (Y : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun V => Psi I M cov α V Y x) x where
  smul := fun _ _ => Psi_smul_left I M cov α
  add := fun _ _ => Psi_add_left I M cov α

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_tensorialAt_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : MDiffAtDual I M α x) (V : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun Y => Psi I M cov α V Y x) x where
  smul := fun hf hY => Psi_smul_right I M cov α hα hf hY
  add := fun hY hY' => Psi_add_right I M cov α hα hY hY'

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem dual_section_mdiff
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (x : M) : MDiffAtDual I M (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x) x :=
  α.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem vec_section_mdiff
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

noncomputable def dualCovariantDerivativeFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    (x : M) :
    TangentSpace I x →L[ℝ] (Bundle.dual ℝ (TangentSpace I : M → Type _)) x := by
  classical
  by_cases hα : MDiffAtDual I M α x
  · exact TensorialAt.mkHom₂ (F := E) (F' := E)
      (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
      (fun V Y => Psi I M cov α V Y x) x
      (fun Y _ => Psi_tensorialAt_left I M cov α Y)
      (fun V _ => Psi_tensorialAt_right I M cov α hα V)
  · exact 0

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem dualCovariantDerivativeFun_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : MDiffAtDual I M α x)
    {V Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V x) (hY : MDiffAtVec I M Y x) :
    dualCovariantDerivativeFun I M cov α x (V x) (Y x) = Psi I M cov α V Y x := by
  unfold dualCovariantDerivativeFun
  rw [dif_pos hα]
  exact TensorialAt.mkHom₂_apply
    (Φ := fun V Y => Psi I M cov α V Y x)
    (fun Y _ => Psi_tensorialAt_left I M cov α Y)
    (fun V _ => Psi_tensorialAt_right I M cov α hα V) hV hY

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem dualCovariantDerivativeFun_of_not_mdiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : ¬ MDiffAtDual I M α x) :
    dualCovariantDerivativeFun I M cov α x = 0 := by
  unfold dualCovariantDerivativeFun
  rw [dif_neg hα]

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem dualCovariantDerivativeFun_isCovOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (E →L[ℝ] ℝ)
      (dualCovariantDerivativeFun I M cov) Set.univ where
  add := by
    intro α₁ α₂ x hα₁ hα₂ _hx

    have hα₁' : MDiffAtDual I M α₁ x := hα₁
    have hα₂' : MDiffAtDual I M α₂ x := hα₂
    have hα_sum : MDiffAtDual I M (α₁ + α₂) x :=
      mdifferentiableAt_add_section (F := E →L[ℝ] ℝ) hα₁ hα₂
    ext v w
    obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    rw [dualCovariantDerivativeFun_apply I M cov (α₁ + α₂) hα_sum hV_diff hY_diff]
    rw [dualCovariantDerivativeFun_apply I M cov α₁ hα₁' hV_diff hY_diff]
    rw [dualCovariantDerivativeFun_apply I M cov α₂ hα₂' hV_diff hY_diff]

    have h_funeq : (fun y => (α₁ + α₂) y (Y y)) =
        (fun y => α₁ y (Y y)) + (fun y => α₂ y (Y y)) := by
      funext y
      simp [Pi.add_apply, ContinuousLinearMap.add_apply]
    have hα₁Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α₁ y (Y y)) x :=
      mdiffAt_pairing I M hα₁' hY_diff
    have hα₂Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α₂ y (Y y)) x :=
      mdiffAt_pairing I M hα₂' hY_diff
    simp only [Psi]
    rw [h_funeq, extDerivFun_add hα₁Y hα₂Y]
    simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  leibniz := by
    intro α g x hα hg _hx
    have hα' : MDiffAtDual I M α x := hα
    have hgα : MDiffAtDual I M (g • α) x :=
      hg.smul_section (F := E →L[ℝ] ℝ) hα
    ext v w
    obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]

    rw [dualCovariantDerivativeFun_apply I M cov (g • α) hgα hV_diff hY_diff]
    change Psi I M cov (g • α) V Y x =
      g x • (dualCovariantDerivativeFun I M cov α x (V x)) (Y x) +
      ((extDerivFun g x) (V x)) * (α x) (Y x)
    rw [dualCovariantDerivativeFun_apply I M cov α hα' hV_diff hY_diff]
    have h_funeq : (fun y => (g • α) y (Y y)) = g • (fun y => α y (Y y)) := by
      funext y
      simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
      mdiffAt_pairing I M hα' hY_diff
    simp only [Psi]
    rw [h_funeq]
    have h_extDeriv_eq : ∀ (h : M → ℝ) (y : M) (u : TangentSpace I y),
        extDerivFun (I := I) h y u =
        NormedSpace.fromTangentSpace (h y) ((mfderiv I 𝓘(ℝ, ℝ) h y) u) := by
      intro h y u
      simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    have h_prod := fromTangentSpace_mfderiv_smul_apply (I := I) hg hαY (V x)
    rw [h_extDeriv_eq _ _ (V x), h_prod]
    have hgα_apply : (g • α) x = g x • α x := rfl
    rw [hgα_apply]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

    have h_eq2 : (NormedSpace.fromTangentSpace ((α x) (Y x)))
        (((mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (Y y))) x) (V x)) =
        (extDerivFun (fun y => α y (Y y)) x) (V x) :=
      (h_extDeriv_eq (fun y => α y (Y y)) x (V x)).symm
    have h_eq3 : (NormedSpace.fromTangentSpace (g x))
        (((mfderiv I 𝓘(ℝ, ℝ) g) x) (V x)) =
        (extDerivFun g x) (V x) :=
      (h_extDeriv_eq g x (V x)).symm
    rw [h_eq2, h_eq3]
    ring

noncomputable def dualCovariantDerivative
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] ℝ)
      (Bundle.dual ℝ (TangentSpace I : M → Type _)) where
  toFun := dualCovariantDerivativeFun I M cov
  isCovariantDerivativeOnUniv := dualCovariantDerivativeFun_isCovOn I M cov

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem dualCov_section_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x ((dualCovariantDerivativeFun I M cov α x) (Y x))) := by

  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := Bundle.Trivial M ℝ)
    (φ := fun x => (dualCovariantDerivativeFun I M cov α x) (Y x))
  intro Z

  have hαZ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => α y (Z y)) :=
    contMDiff_dual_apply_section I M α Z
  let fαZ : C^∞⟮I, M; ℝ⟯ := ⟨_, hαZ⟩
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x (extDerivFun (fun y => α y (Z y)) x)) := by
    have := contMDiff_extDerivFun_section I M fαZ
    simpa [fαZ] using this

  have h_extDeriv_at_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (fun y => α y (Z y)) x (Y x)) := by
    let dα : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
      ⟨fun x => extDerivFun (fun y => α y (Z y)) x, h_extDeriv⟩
    have := contMDiff_dual_apply_section I M dα Y
    simpa [dα] using this

  have h_concreteConn : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => α x ((concreteConn I M cov Y Z) x)) :=
    contMDiff_dual_apply_section I M α (concreteConn I M cov Y Z)
  have h_α_cov : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => α x (cov Z x (Y x))) := h_concreteConn

  have h_diff : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (fun y => α y (Z y)) x (Y x) - α x (cov Z x (Y x))) :=
    h_extDeriv_at_Y.sub h_α_cov

  have h_eq : ∀ x, (dualCovariantDerivativeFun I M cov α x) (Y x) (Z x) =
      extDerivFun (fun y => α y (Z y)) x (Y x) - α x (cov Z x (Y x)) := by
    intro x

    have hα := dual_section_mdiff I M α x
    have hY := vec_section_mdiff I M Y x
    have hZ := vec_section_mdiff I M Z x
    rw [dualCovariantDerivativeFun_apply I M cov α hα hY hZ]
    rfl

  intro x₀
  rw [contMDiffAt_section]

  have h_diff_at := h_diff x₀

  refine h_diff_at.congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [h_eq]

  simp [Bundle.Trivial.fiberBundle_trivializationAt']

noncomputable instance dualCovariantDerivative_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (dualCovariantDerivative I M cov) ∞ where
  contMDiff := {
    contMDiff := by

      intro α hα

      have hα_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
          (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)) x (α x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hα
        rwa [← contMDiffOn_univ]
      let α_section : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
        ⟨α, hα_smooth⟩

      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := Bundle.dual ℝ (TangentSpace I : M → Type _))
        (φ := fun x => dualCovariantDerivativeFun I M cov α x)
      intro Y
      exact dualCov_section_smooth I M cov α_section Y
  }

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem dualCovariantDerivative_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    (dualCovariantDerivative I M cov α x v) (Y x) =
      extDerivFun (fun y => α y (Y y)) x v - (α x) (cov Y x v) := by
  change dualCovariantDerivativeFun I M cov α x v (Y x) = _
  obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hα_diff := dual_section_mdiff I M α x
  have hV_diff := vec_section_mdiff I M V x
  have hY_diff := vec_section_mdiff I M Y x
  rw [show v = (V : Π x : M, TangentSpace I x) x from hVx.symm]
  rw [dualCovariantDerivativeFun_apply I M cov α hα_diff hV_diff hY_diff]
  rfl

end DualConnection

end
