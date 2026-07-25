import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelDifferenceKoszul
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorSectionMDiffAt_curriedSection_apply_loc
    (s : ℕ) (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
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
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

private def bilinEvalFn (V : Π b : M, Tensor0SSpace 2 I b)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun b => Tensor0SSpace.toModel (V b) (Fin.cons (Y b) ![Z b])

private def bilinCurriedSec (V : Π b : M, Tensor0SSpace 2 I b)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π b : M, Tensor0SSpace 0 I b :=
  fun b => Tensor0SNabla.curriedSection I M
    (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) b (Z b)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma scalarFn_bilinCurriedSec
    (V : Π b : M, Tensor0SSpace 2 I b)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Tensor0SNabla.scalarFn I M (bilinCurriedSec (I := I) (M := M) V Y Z) =
      bilinEvalFn (I := I) (M := M) V Y Z := by
  funext b
  rw [scalarFn_eq_toModel_elim0 (I := I) (M := M), bilinCurriedSec, bilinEvalFn]
  rw [Tensor0SNabla.curriedSection_apply (s := 0)
        (T := fun y : M => Tensor0SNabla.curriedSection I M V y (Y y))]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := Tensor0SNabla.curriedSection I M V b (Y b)) (v0 := Z b)
        (vs := (fun i => Fin.elim0 i))]
  rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := V)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := Fin.cons (Z b) (fun i => Fin.elim0 i))]
  congr 1

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensor0SCovariantDerivative02_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 2 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 2 V x)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)).toFun V x v)
        (Fin.cons (Y x) ![Z x]) =
      directionalDeriv (I := I) (bilinEvalFn (I := I) (M := M) V Y Z) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) ![Z x])
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) := by
  classical

  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (Y b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x :=
    tensorSectionMDiffAt_curriedSection_apply_loc (I := I) (M := M) 1 V hV Y

  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 V hV Y v ![Z x]

  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff Z v (fun i => Fin.elim0 i)

  have hbase : Tensor0SSpace.toModel
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)).toFun
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x v)
      (fun i => Fin.elim0 i) =
      directionalDeriv (I := I) (bilinEvalFn (I := I) (M := M) V Y Z) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x v]
    rw [show (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) =
        bilinCurriedSec (I := I) (M := M) V Y Z from rfl]
    rw [scalarFn_bilinCurriedSec (I := I) (M := M) V Y Z]

  have hcorr2 : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) := by
    have hW₁x : W₁ x = Tensor0SNabla.curriedSection I M V x (Y x) := rfl
    rw [hW₁x, Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := Y x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v)
        (fun i => Fin.elim0 i))]
    refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl

  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) = W₁ from rfl]
  rw [show (![Z x] : Fin 1 → E) = Fin.cons (Z x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel2, hbase, hcorr2]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad02_unitModel_eval_eq_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : TangentSpace I x)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v (Fin.cons (Y x) ![Z x])) =
      directionalDeriv (I := I)
          (bilinEvalFn (I := I) (M := M)
            (unitEvalSection (I := I) (M := M) g₀ 2 S) Y Z) x v
        - Tensor0SSpace.toModel
            (unitEvalSection (I := I) (M := M) g₀ 2 S x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) ![Z x])
        - Tensor0SSpace.toModel
            (unitEvalSection (I := I) (M := M) g₀ 2 S x)
            (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) := by
  classical

  have hV : TensorSectionMDiffAt (I := I) 2 (unitEvalSection (I := I) (M := M) g₀ 2 S) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 2 S) x).mdifferentiableAt (by simp)

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 2 S x
    (unitZeroSec (I := I) (M := M) x) (Fin.cons v (Fin.cons (Y x) ![Z x]))]

  rw [show (Fin.cons v (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x) 0 = v from rfl]
  rw [show Matrix.vecTail (Fin.cons v (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x)
        = Fin.cons (Y x) ![Z x] from by
      funext k; simp only [Matrix.vecTail, Function.comp]
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      exact j'.elim0]

  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 2 S x v]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 2 S.toSection x v]

  exact tensor0SCovariantDerivative02_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 2 S) hV Y Z v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitEvalSection_toModel_eq_ccTensorBilin
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (b : M)
    (Y Z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S b) (Fin.cons Y ![Z]) =
      smoothCcTensorBilinForm (I := I) g₀ S b Y Z := by
  rw [ccTensorBilin_apply (I := I) g₀ S b Y Z]
  rw [ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitEvalSection]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad02_unitModel_eval_eq_metricDiffCovDeriv
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S b u w =
        g₁.inner b u w - g₁'.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀)
          (fun b => X b) (fun b => Y b) (fun b => Z b) x
        - metricCovDeriv (I := I) g₁' (LeviCivita (I := I) g₀)
          (fun b => X b) (fun b => Y b) (fun b => Z b) x := by
  classical

  rw [covGrad02_unitModel_eval_eq_leibnizDefect (I := I) (M := M) g₀ S x (X x) Y Z]

  have hfun : bilinEvalFn (I := I) (M := M) (unitEvalSection (I := I) (M := M) g₀ 2 S) Y Z =
      fun b : M => g₁.inner b (Y b) (Z b) - g₁'.inner b (Y b) (Z b) := by
    funext b
    rw [bilinEvalFn, unitEvalSection_toModel_eq_ccTensorBilin (I := I) (M := M) g₀ S b (Y b) (Z b),
      hbil b (Y b) (Z b)]
  rw [hfun]

  have hcorrY : Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) ![Z x]) =
      g₁.inner x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
        - g₁'.inner x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := by
    rw [unitEvalSection_toModel_eq_ccTensorBilin (I := I) (M := M) g₀ S x
      ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x), hbil]
  have hcorrZ : Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)]) =
      g₁.inner x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - g₁'.inner x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) := by
    rw [unitEvalSection_toModel_eq_ccTensorBilin (I := I) (M := M) g₀ S x (Y x)
      ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)), hbil]
  rw [hcorrY, hcorrZ]

  have hg₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => g₁.inner b (Y b) (Z b)) x :=
    (DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g₁ Y Z x).mdifferentiableAt (by simp)
  have hg₁' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => g₁'.inner b (Y b) (Z b)) x :=
    (DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g₁' Y Z x).mdifferentiableAt (by simp)
  have hsplit : directionalDeriv (I := I)
        (fun b : M => g₁.inner b (Y b) (Z b) - g₁'.inner b (Y b) (Z b)) x (X x) =
      directionalDeriv (I := I) (fun b : M => g₁.inner b (Y b) (Z b)) x (X x)
        - directionalDeriv (I := I) (fun b : M => g₁'.inner b (Y b) (Z b)) x (X x) := by
    rw [directionalDeriv_eq, directionalDeriv_eq, directionalDeriv_eq]
    rw [show (fun b : M => g₁.inner b (Y b) (Z b) - g₁'.inner b (Y b) (Z b)) =
        (fun b : M => g₁.inner b (Y b) (Z b)) - (fun b : M => g₁'.inner b (Y b) (Z b)) from rfl]
    rw [mfderiv_sub hg₁ hg₁']
    rfl
  rw [hsplit]

  rw [metricCovDeriv, metricCovDeriv]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S b u w =
        g₁.inner b u w - g₁'.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      metricDiffCovDeriv (I := I) g₁ g₀
          (fun b => X b) (fun b => Y b) (fun b => Z b) x
        - metricDiffCovDeriv (I := I) g₁' g₀
          (fun b => X b) (fun b => Y b) (fun b => Z b) x := by
  rw [covGrad02_unitModel_eval_eq_metricDiffCovDeriv (I := I) (M := M) g₀ g₁ g₁' S hbil X Y Z x]
  rw [metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀
        (Y := fun b => Y b) (Z := fun b => Z b) Y.mdifferentiableAt Z.mdifferentiableAt,
      metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁' g₀
        (Y := fun b => Y b) (Z := fun b => Z b) Y.mdifferentiableAt Z.mdifferentiableAt]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma bilinEvalFn_unitEvalSection_eq_unitModel
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (b : M)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    bilinEvalFn (I := I) (M := M) (unitEvalSection (I := I) (M := M) g₀ 2 S) Y Z b =
      unitModel (I := I) (M := M) g₀ 2 S b (Fin.cons (Y b) ![Z b]) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_domDomCongrSection_swap_eval
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : TangentSpace I x)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v (Fin.cons (Y x) ![Z x])) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v (Fin.cons (Z x) ![Y x])) := by
  classical

  have hswap : ∀ b : M, ∀ (P Q : TangentSpace I b),
      unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) b (Fin.cons P ![Q]) =
        unitModel (I := I) (M := M) g₀ 2 S b (Fin.cons Q ![P]) := by
    intro b P Q
    rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap 0 1) S b]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext k
    fin_cases k <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

  rw [covGrad02_unitModel_eval_eq_leibnizDefect (I := I) (M := M) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) x v Y Z,
      covGrad02_unitModel_eval_eq_leibnizDefect (I := I) (M := M) g₀ S x v Z Y]

  have hbil : bilinEvalFn (I := I) (M := M)
        (unitEvalSection (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S)) Y Z =
      bilinEvalFn (I := I) (M := M) (unitEvalSection (I := I) (M := M) g₀ 2 S) Z Y := by
    funext b
    rw [bilinEvalFn_unitEvalSection_eq_unitModel, bilinEvalFn_unitEvalSection_eq_unitModel]
    exact hswap b (Y b) (Z b)
  rw [hbil]

  have hcorr1 : Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) ![Z x]) =
      Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons (Z x) ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) :=
    hswap x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) (Z x)
  have hcorr2 : Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) x)
        (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) =
      Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v) ![Y x]) :=
    hswap x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v)
  rw [hcorr1, hcorr2]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
