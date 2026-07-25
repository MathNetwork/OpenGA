import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Tensor.Multilinear.ModelProductContinuousBilinear
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficientsFibreOperators
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficientsFieldSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficientsLichnerowiczVelocityIdentity


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma symmS_eq_self_of_symm (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_empty_eq_iso {y : M} (T : Tensor0SBundle.Tensor0SSpace 0 I y)
    (m : Fin 0 → TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel T m = Tensor0SNabla.tensor0Iso I M y T := by
  have h0 : Tensor0SNabla.tensor0Iso I M y T =
      (continuousMultilinearCurryFin0 ℝ E ℝ)
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 0 y) T) := rfl
  rw [h0, continuousMultilinearCurryFin0_apply]
  exact congrArg _ (funext fun i => i.elim0)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma curried_tsmdiffAt (n : ℕ)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace (n + 1) I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (n + 1) W x)
    (Y : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) n
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) n W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel n ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace n I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma deriv0_eq_extDeriv (g : SmoothRiemannianMetric I M)
    (sc : Π y : M, Tensor0SBundle.Tensor0SSpace 0 I y) (x : M) (v : TangentSpace I x) :
    Tensor0SNabla.tensor0Iso I M x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) sc x v) =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M sc) x v := by
  rw [Tensor0SNabla.tensor0SCovariantDerivative_apply_zero]
  exact (Tensor0SNabla.tensor0Iso I M x).apply_symm_apply _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma curried2_toModel_eval
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SNabla.scalarFn I M
        (fun z : M => Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M W w (Yf w)) z (Zf z)) y =
      Tensor0SBundle.Tensor0SSpace.toModel (W y) ![Yf y, Zf y] := by
  rw [show Tensor0SNabla.scalarFn I M
      (fun z : M => Tensor0SNabla.curriedSection I M
        (fun w : M => Tensor0SNabla.curriedSection I M W w (Yf w)) z (Zf z)) y =
      Tensor0SNabla.tensor0Iso I M y
        (Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M W w (Yf w)) y (Zf y)) from rfl]
  rw [← toModel_empty_eq_iso (I := I) (M := M) _ (fun i : Fin 0 => i.elim0)]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SNabla.curriedSection I M W y (Yf y)) (v0 := Zf y)
    (vs := (fun i : Fin 0 => i.elim0))]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := W y) (v0 := Yf y) (vs := Fin.cons (Zf y) (fun i : Fin 0 => i.elim0))]
  exact congrArg _ (funext fun i => by fin_cases i <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma curried3_toModel_eval
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y)
    (Bf Cf Df : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SNabla.scalarFn I M
        (fun z : M => Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) w (Cf w)) z (Df z)) y =
      Tensor0SBundle.Tensor0SSpace.toModel (W y) ![Bf y, Cf y, Df y] := by
  rw [show Tensor0SNabla.scalarFn I M
      (fun z : M => Tensor0SNabla.curriedSection I M
        (fun w : M => Tensor0SNabla.curriedSection I M
          (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) w (Cf w)) z (Df z)) y =
      Tensor0SNabla.tensor0Iso I M y
        (Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) w (Cf w)) y (Df y)) from rfl]
  rw [← toModel_empty_eq_iso (I := I) (M := M) _ (fun i : Fin 0 => i.elim0)]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SNabla.curriedSection I M
      (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) y (Cf y)) (v0 := Df y)
    (vs := (fun i : Fin 0 => i.elim0))]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SNabla.curriedSection I M W y (Bf y)) (v0 := Cf y)
    (vs := Fin.cons (Df y) (fun i : Fin 0 => i.elim0))]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := W y) (v0 := Bf y)]
  exact congrArg _ (funext fun i => by fin_cases i <;> rfl)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma peel2_core (g : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) 2 W x)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g) W x v)
        ![Yf x, Zf x] =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M W z (Yf z)) y (Zf y))) x v
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![(LeviCivita (I := I) g).toFun (fun y => Yf y) x v, Zf x]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![Yf x, (LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
  classical
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 1 W hW
    Yf v ![Zf x]
  have hWY : TensorSectionMDiffAt (I := I) 1
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Yf y)) x :=
    curried_tsmdiffAt (I := I) (M := M) 1 W hW Yf
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 0
    (fun y : M => Tensor0SNabla.curriedSection I M W y (Yf y)) hWY
    Zf v (fun i : Fin 0 => i.elim0)
  have hcons1 : (Fin.cons (Yf x) ![Zf x] : Fin 2 → TangentSpace I x) = ![Yf x, Zf x] := by
    funext i; fin_cases i <;> rfl
  have hcons2 : (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Yf y) x v) ![Zf x] :
      Fin 2 → TangentSpace I x) =
      ![(LeviCivita (I := I) g).toFun (fun y => Yf y) x v, Zf x] := by
    funext i; fin_cases i <;> rfl
  rw [hcons1, hcons2] at hpeel1
  have hcons3 : (Fin.cons (Zf x) (fun i : Fin 0 => i.elim0) : Fin 1 → TangentSpace I x) =
      ![Zf x] := by
    funext i
    fin_cases i
    rfl
  rw [hcons3] at hpeel2
  have hcorr2 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W x (Yf x))
      (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Zf y) x v) (fun i : Fin 0 => i.elim0)) =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Yf x, (LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
    rw [Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W x) (v0 := Yf x)]
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
  have hd0 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M W z (Yf z)) y (Zf y)) x v)
      (fun i : Fin 0 => i.elim0) =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
        (fun y : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M W z (Yf z)) y (Zf y))) x v := by
    rw [toModel_empty_eq_iso (I := I) (M := M)]
    exact deriv0_eq_extDeriv (I := I) (M := M) g _ x v
  rw [hpeel1, hpeel2, hcorr2, hd0]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma peel3_core (g : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) 3 W x)
    (Bf Cf Df : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g) W x v)
        ![Bf x, Cf x, Df x] =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) z (Cf z)) y (Df y))) x v
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![(LeviCivita (I := I) g).toFun (fun y => Bf y) x v, Cf x, Df x]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![Bf x, (LeviCivita (I := I) g).toFun (fun y => Cf y) x v, Df x]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![Bf x, Cf x, (LeviCivita (I := I) g).toFun (fun y => Df y) x v] := by
  classical
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 2 W hW
    Bf v ![Cf x, Df x]
  have hWB : TensorSectionMDiffAt (I := I) 2
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Bf y)) x :=
    curried_tsmdiffAt (I := I) (M := M) 2 W hW Bf
  have hcons1 : (Fin.cons (Bf x) ![Cf x, Df x] : Fin 3 → TangentSpace I x) =
      ![Bf x, Cf x, Df x] := by
    funext i; fin_cases i <;> rfl
  have hcons2 : (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Bf y) x v) ![Cf x, Df x] :
      Fin 3 → TangentSpace I x) =
      ![(LeviCivita (I := I) g).toFun (fun y => Bf y) x v, Cf x, Df x] := by
    funext i; fin_cases i <;> rfl
  rw [hcons1, hcons2] at hpeel1
  have hpeelrest := peel2_core (I := I) (M := M) g
    (fun y : M => Tensor0SNabla.curriedSection I M W y (Bf y)) hWB Cf Df v
  have hcorrC : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W x (Bf x))
      ![(LeviCivita (I := I) g).toFun (fun y => Cf y) x v, Df x] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Bf x, (LeviCivita (I := I) g).toFun (fun y => Cf y) x v, Df x] := by
    rw [Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W x) (v0 := Bf x)]
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
  have hcorrD : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W x (Bf x))
      ![Cf x, (LeviCivita (I := I) g).toFun (fun y => Df y) x v] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Bf x, Cf x, (LeviCivita (I := I) g).toFun (fun y => Df y) x v] := by
    rw [Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W x) (v0 := Bf x)]
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
  rw [hpeel1, hpeelrest, hcorrC, hcorrD]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma bridge02_eval (gA gB : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) 2 W x)
    (v p q : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) gA) W x v)
        ![p, q] =
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) gB) W x v)
          ![p, q]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![PDE.DeTurck.connDiff (I := I) gA gB x p v, q]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![p, PDE.DeTurck.connDiff (I := I) gA gB x q v] := by
  classical
  obtain ⟨Yf, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x p
  obtain ⟨Zf, hZx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x q
  have hA := peel2_core (I := I) (M := M) gA W hW Yf Zf v
  have hB := peel2_core (I := I) (M := M) gB W hW Yf Zf v
  have hcdY := PDE.DeTurck.connDiff_apply (I := I) gA gB (σ := fun y => Yf y)
    Yf.mdifferentiableAt v
  have hcdZ := PDE.DeTurck.connDiff_apply (I := I) gA gB (σ := fun y => Zf y)
    Zf.mdifferentiableAt v
  have hsplitY : Tensor0SBundle.Tensor0SSpace.toModel (W x)
      ![(LeviCivita (I := I) gA).toFun (fun y => Yf y) x v, Zf x] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![(LeviCivita (I := I) gB).toFun (fun y => Yf y) x v, Zf x]
      + Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![PDE.DeTurck.connDiff (I := I) gA gB x (Yf x) v, Zf x] := by
    have hAB : (LeviCivita (I := I) gA).toFun (fun y => Yf y) x v =
        (LeviCivita (I := I) gB).toFun (fun y => Yf y) x v
          + PDE.DeTurck.connDiff (I := I) gA gB x (Yf x) v := by
      rw [hcdY]; abel
    rw [hAB]
    have hupd : ∀ z : TangentSpace I x,
        (![z, Zf x] : Fin 2 → TangentSpace I x) = Function.update ![0, Zf x] 0 z := by
      intro z
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hupd, hupd ((LeviCivita (I := I) gB).toFun (fun y => Yf y) x v),
      hupd (PDE.DeTurck.connDiff (I := I) gA gB x (Yf x) v)]
    exact ContinuousMultilinearMap.map_update_add _ _ 0 _ _
  have hsplitZ : Tensor0SBundle.Tensor0SSpace.toModel (W x)
      ![Yf x, (LeviCivita (I := I) gA).toFun (fun y => Zf y) x v] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Yf x, (LeviCivita (I := I) gB).toFun (fun y => Zf y) x v]
      + Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Yf x, PDE.DeTurck.connDiff (I := I) gA gB x (Zf x) v] := by
    have hAB : (LeviCivita (I := I) gA).toFun (fun y => Zf y) x v =
        (LeviCivita (I := I) gB).toFun (fun y => Zf y) x v
          + PDE.DeTurck.connDiff (I := I) gA gB x (Zf x) v := by
      rw [hcdZ]; abel
    rw [hAB]
    have hupd : ∀ z : TangentSpace I x,
        (![Yf x, z] : Fin 2 → TangentSpace I x) = Function.update ![Yf x, 0] 1 z := by
      intro z
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hupd, hupd ((LeviCivita (I := I) gB).toFun (fun y => Zf y) x v),
      hupd (PDE.DeTurck.connDiff (I := I) gA gB x (Zf x) v)]
    exact ContinuousMultilinearMap.map_update_add _ _ 1 _ _
  rw [← hYx, ← hZx]
  rw [hA, hB, hsplitY, hsplitZ]
  ring

section NormedCovectorExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma exists_covector_section_eq (x : M) (β : Tensor0SBundle.Tensor0SSpace 1 I x) :
    ∃ om : Cₛ^(⊤ : ℕ∞)⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E,
        (fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)⟯, om x = β := by
  letI : TopologicalSpace (TotalSpace (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y)) :=
    Tensor0SBundle.tensor0SBundle_topology 1
  letI : FiberBundle (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) := Tensor0SBundle.tensor0SBundle_fiber 1
  letI : VectorBundle ℝ (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) := Tensor0SBundle.tensor0SBundle_vector 1
  letI : ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) I :=
    Tensor0SBundle.tensor0SBundle_smooth _ 1
  exact ContMDiffSection.exists_eq_at x β

end NormedCovectorExtension

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma covDerivConnDiff_expand (g₁ g₀ : SmoothRiemannianMetric I M)
    (Xf Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (LeviCivita (I := I) g₀).toFun
        (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) x (Xf x) =
      covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x))
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x)) (Zf x) := by
  have hexpand : covDerivConnDiff (I := I) g₀ g₁
      (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x =
      (LeviCivita (I := I) g₀).toFun
          (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) x (Xf x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x)) (Zf x) := rfl
  rw [hexpand]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma covDerivConnDiff_symm23 (g₁ g₀ : SmoothRiemannianMetric I M)
    (Xf Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x =
      covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Yf y) (fun y => Zf y) x := by
  have h1 : covDerivConnDiff (I := I) g₀ g₁
      (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x =
      (LeviCivita (I := I) g₀).toFun
          (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) x (Xf x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x)) (Zf x) := rfl
  have h2 : covDerivConnDiff (I := I) g₀ g₁
      (fun y => Xf y) (fun y => Yf y) (fun y => Zf y) x =
      (LeviCivita (I := I) g₀).toFun
          (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Zf y) (Yf y)) x (Xf x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Zf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x)) (Yf x) := rfl
  rw [h1, h2]
  have hsec : (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Zf y) (Yf y)) =
      (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) := by
    funext y
    exact PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ y (Zf y) (Yf y)
  rw [hsec]
  rw [PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x (Zf x)
    ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x))]
  rw [PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x
    ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x)) (Yf x)]
  abel

def connDiffVecField (g₁ g₀ : SmoothRiemannianMetric I M)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y),
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Yf.contMDiff Zf.contMDiff⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma connDiffVecField_apply (g₁ g₀ : SmoothRiemannianMetric I M)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    connDiffVecField (I := I) (M := M) g₁ g₀ Yf Zf y =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma extDerivFun_sub' {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    extDerivFun (I := I) (f - g) x = extDerivFun (I := I) f x - extDerivFun (I := I) g x := by
  have h := extDerivFun_add (I := I) (g := f - g) (g' := g) (hf.sub hg) hg
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

section NormedContractionCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
lemma modelTensorWithCovectorFirst_zero_unit
    (α : Tensor0SBundle.Tensor0SModel 1 ℝ E) :
    Tensor0SBundle.model_tensorWithCovector_first (𝕜 := ℝ) (E := E) 0 α
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) = α := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [Tensor0SBundle.model_tensorWithCovector_first]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, mul_one]
  exact congrArg α (funext fun j => rfl)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma connContrCLM_toModel_apply (m k : ℕ) (x : M)
    (B : Tensor0SBundle.TensorRSSpace 1 (k + 1) I x)
    (D : Tensor0SBundle.Tensor0SSpace (m + 1) I x) (u : Fin (m + 1 + k) → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (connContrCLM (I := I) m k x B D) u =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd (k + 1)) *
          (Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis i)))
            (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd (m + 1)) := by
  classical
  have h0 : connContrCLM (I := I) m k x B D =
      contractUnitCLM (I := I) (m + 1 + k) x
        (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)) := rfl
  rw [h0]
  set Ψ : Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x :=
    (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
      (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D).comp
        (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)) with hΨ
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
      (contractUnitCLM (I := I) (m + 1 + k) x Ψ) =
      (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 (m + 1 + k)
        (Tensor0SBundle.TensorRSSpace.toModel Ψ))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl
  have hTB : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.TensorRSSpace.toModel Ψ
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i)) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (m + 1) (k + 1)
        (Tensor0SBundle.Tensor0SSpace.toModel D)
        (Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i))) := by
    intro i
    set β := Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      ((Module.finBasis ℝ E).cDualBasis i) with hβ
    rw [show β = Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) from
      (Tensor0SBundle.Tensor0SSpace.toModel_ofModel (I := I) (x := x) β).symm]
    rw [← toModel_tensorRS_apply (I := I) 1 (m + 1 + k + 1) x Ψ
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)]
    rw [← toModel_tensorRS_apply (I := I) 1 (k + 1) x B
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)]
    rw [show (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I x from Ψ)
          (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) =
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D)
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)
            (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)) from rfl]
    rw [tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [hA, Tensor0SBundle.model_contract_trace_apply, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SBundle.model_contract_covariant_bilinear_apply,
    Tensor0SBundle.model_contract_contravariant_first_bilinear_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    modelTensorWithCovectorFirst_zero_unit, hTB i]
  exact Bundle.continuousMultilinearMap.modelProduct_apply (m + 1) (k + 1)
    (Tensor0SBundle.Tensor0SSpace.toModel D)
    (Tensor0SBundle.TensorRSSpace.toModel B
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis i)))
    (Fin.cons ((Module.finBasis ℝ E) i) u)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma sum_cons_coeff_collapse {n : ℕ} {x : M}
    (D : Tensor0SBundle.Tensor0SSpace (n + 1) I x)
    (w : Fin n → E) (c : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons ((Module.finBasis ℝ E) i) w) * c i) =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Fin.cons (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i) w) := by
  classical
  have hupd : ∀ z : E, (Fin.cons z w : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) w) 0 z := by
    intro z
    rw [Fin.update_cons_zero]
  rw [hupd (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i)]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel D
      (Function.update (Fin.cons (0 : E) w) 0
        (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i)) =
      (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap
        (Function.update (Fin.cons (0 : E) w) 0
          (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i)) from rfl]
  rw [MultilinearMap.map_update_sum]
  refine (Finset.sum_congr rfl (fun i _ => ?_)).symm
  rw [MultilinearMap.map_update_smul]
  rw [show (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap
      (Function.update (Fin.cons (0 : E) w) 0 ((Module.finBasis ℝ E) i)) =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update (Fin.cons (0 : E) w) 0 ((Module.finBasis ℝ E) i)) from rfl]
  rw [← hupd ((Module.finBasis ℝ E) i)]
  rw [smul_eq_mul, mul_comm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma sum_cons_cDual_collapse {n : ℕ} {x : M}
    (D : Tensor0SBundle.Tensor0SSpace (n + 1) I x) (w : Fin n → E) (V : E) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons ((Module.finBasis ℝ E) i) w) *
          ((Module.finBasis ℝ E).cDualBasis i) V) =
      Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons V w) := by
  classical
  have hV : (∑ i : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis i) V • (Module.finBasis ℝ E) i) = V := by
    have hci : ∀ i : Fin (Module.finrank ℝ E),
        ((Module.finBasis ℝ E).cDualBasis i) V = (Module.finBasis ℝ E).repr V i := by
      intro i
      rw [cDualBasis_eq_coord (E := E)]
      rfl
    rw [show (∑ i : Fin (Module.finrank ℝ E),
        ((Module.finBasis ℝ E).cDualBasis i) V • (Module.finBasis ℝ E) i) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr V i) • (Module.finBasis ℝ E) i from
      Finset.sum_congr rfl (fun i _ => by rw [hci i])]
    exact (Module.finBasis ℝ E).sum_repr V
  rw [sum_cons_coeff_collapse (I := I) (M := M) D w
    (fun i => ((Module.finBasis ℝ E).cDualBasis i) V), hV]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connDiff_model_coeff (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (w : Fin 2 → E) :
    (Tensor0SBundle.TensorRSSpace.toModel
        (show Tensor0SBundle.TensorRSSpace 1 2 I x from
          (connDiffSection (I := I) g₁ g₀).toSection x)
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i))) w =
      ((Module.finBasis ℝ E).cDualBasis i)
        ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((w 0 : E)) ((w 1 : E)) : TangentSpace I x) : E) := by
  classical
  set β := Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
    ((Module.finBasis ℝ E).cDualBasis i) with hβdef
  have h1 : Tensor0SBundle.TensorRSSpace.toModel
      (show Tensor0SBundle.TensorRSSpace 1 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) β =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (connDiffSection (I := I) g₁ g₀).toSection x)
          (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)) := by
    rw [toModel_tensorRS_apply (I := I) 1 2 x _
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β),
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [h1]
  rw [show (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      (connDiffSection (I := I) g₁ g₀).toSection x)
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) =
      connDiffPairing (I := I) g₁ g₀ x
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) from rfl]
  rw [toModel_apply_tangent (I := I) (M := M) x _ (fun j => ((w j : E) : TangentSpace I x))]
  rw [show (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
      connDiffPairing (I := I) g₁ g₀ x
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β))
      (fun j => ((w j : E) : TangentSpace I x)) =
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
        (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((w 0 : E)) ((w 1 : E))) from rfl]
  rw [show (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
      (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((w 0 : E)) ((w 1 : E))) =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
        (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((w 0 : E)) ((w 1 : E)) : TangentSpace I x) : E)) from rfl]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [hβdef, Tensor0SBundle.model_covectorOfCLM_apply]

end NormedContractionCoordinates

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma consCast21 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.castAdd 2 : Fin 3 → E) = ![z, u 0, u 1] := by
  funext j
  fin_cases j <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma consNat21 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.natAdd 3 : Fin 2 → E) = ![u 2, u 3] := by
  funext j
  fin_cases j <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma consCast11 (z : E) (u : Fin 3 → E) :
    (Fin.cons z u ∘ Fin.castAdd 2 : Fin 2 → E) = ![z, u 0] := by
  funext j
  fin_cases j <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma consNat11 (z : E) (u : Fin 3 → E) :
    (Fin.cons z u ∘ Fin.natAdd 2 : Fin 2 → E) = ![u 1, u 2] := by
  funext j
  fin_cases j <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma consCast12 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.castAdd 3 : Fin 2 → E) = ![z, u 0] := by
  funext j
  fin_cases j <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma consNat12 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.natAdd 2 : Fin 3 → E) = ![u 1, u 2, u 3] := by
  funext j
  fin_cases j <;> rfl

section NormedConnContr21

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connContr21_insert (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) (u : Fin 4 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 2 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) u =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 2 : E)) ((u 3 : E)) :
            TangentSpace I x) : E), u 0, u 1] := by
  classical
  rw [connContrCLM_toModel_apply (I := I) (M := M) 2 1 x _ D u]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd 2) *
        (Tensor0SBundle.TensorRSSpace.toModel
            (show Tensor0SBundle.TensorRSSpace 1 2 I x from
              (connDiffSection (I := I) g₁ g₀).toSection x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd 3) =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) ![u 0, u 1]) *
        ((Module.finBasis ℝ E).cDualBasis i)
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 2 : E)) ((u 3 : E)) :
            TangentSpace I x) : E) := by
    intro i
    rw [consCast21, consNat21, connDiff_model_coeff (I := I) (M := M) g₁ g₀ x i (![u 2, u 3])]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [sum_cons_cDual_collapse (I := I) (M := M) D ![u 0, u 1]
    ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 2 : E)) ((u 3 : E)) : TangentSpace I x) : E)]
  rfl

end NormedConnContr21

section NormedConnContr11And12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connContr11_insert (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (u : Fin 3 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 1 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) u =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) :
            TangentSpace I x) : E), u 0] := by
  classical
  rw [connContrCLM_toModel_apply (I := I) (M := M) 1 1 x _ D u]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd 2) *
        (Tensor0SBundle.TensorRSSpace.toModel
            (show Tensor0SBundle.TensorRSSpace 1 2 I x from
              (connDiffSection (I := I) g₁ g₀).toSection x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd 2) =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) ![u 0]) *
        ((Module.finBasis ℝ E).cDualBasis i)
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) :
            TangentSpace I x) : E) := by
    intro i
    rw [consCast11, consNat11, connDiff_model_coeff (I := I) (M := M) g₁ g₀ x i (![u 1, u 2])]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [sum_cons_cDual_collapse (I := I) (M := M) D ![u 0]
    ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) : TangentSpace I x) : E)]
  rfl

def rs13ContrVec (x : M) (B : Tensor0SBundle.TensorRSSpace 1 3 I x)
    (q : Fin 3 → E) : E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i))) q) • (Module.finBasis ℝ E) i

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma connContr12_insert (x : M) (B : Tensor0SBundle.TensorRSSpace 1 3 I x)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (u : Fin 4 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (connContrCLM (I := I) 1 2 x B D) u =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![rs13ContrVec (I := I) (M := M) x B ![u 1, u 2, u 3], u 0] := by
  classical
  rw [connContrCLM_toModel_apply (I := I) (M := M) 1 2 x B D u]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd 3) *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd 2) =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) ![u 0]) *
        ((Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i))) ![u 1, u 2, u 3]) := by
    intro i
    rw [consCast12, consNat12]
    rw [show (![((Module.finBasis ℝ E) i : E), u 0] : Fin 2 → E) =
        Fin.cons ((Module.finBasis ℝ E) i) ![u 0] from
      funext fun j => by fin_cases j <;> rfl]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [sum_cons_coeff_collapse (I := I) (M := M) D ![u 0]
    (fun i => (Tensor0SBundle.TensorRSSpace.toModel B
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis i))) ![u 1, u 2, u 3])]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma rs13ContrVec_covGrad_eq (g₁ g₀ : SmoothRiemannianMetric I M)
    (Xf Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    rs13ContrVec (I := I) (M := M) x
        (show Tensor0SBundle.TensorRSSpace 1 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
        ![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] =
      ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
        TangentSpace I x) : E) := by
  classical
  have hcoeff : ∀ i : Fin (Module.finrank ℝ E),
      (Tensor0SBundle.TensorRSSpace.toModel
          (show Tensor0SBundle.TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)))
        ![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] =
      ((Module.finBasis ℝ E).cDualBasis i)
        ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
          TangentSpace I x) : E) := by
    intro i
    set β := Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      ((Module.finBasis ℝ E).cDualBasis i) with hβdef
    obtain ⟨om, homx⟩ := exists_covector_section_eq (I := I) (M := M) x
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
    have h1 : Tensor0SBundle.TensorRSSpace.toModel
        (show Tensor0SBundle.TensorRSSpace 1 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x) β =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            (om x)) := by
      rw [homx]
      rw [toModel_tensorRS_apply (I := I) 1 3 x _
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β),
        Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [h1]
    have h2 := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) (M := M) g₁ g₀ om Xf Yf Zf x
    rw [show (Fin.cons (Xf x) (Fin.cons (Yf x) ![Zf x]) : Fin 3 → TangentSpace I x) =
        (fun j => (![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] j : TangentSpace I x)) from by
      funext j
      fin_cases j <;> rfl] at h2
    rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          (om x))
        ![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            (om x))
          (fun j => (![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
            ((Zf x : TangentSpace I x) : E)] j : TangentSpace I x)) from rfl]
    rw [h2, homx]
    rw [show (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
        (fun _ : Fin 1 => covDerivConnDiff (I := I) g₀ g₁
          (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
          (fun _ : Fin 1 => ((covDerivConnDiff (I := I) g₀ g₁
            (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x : TangentSpace I x) : E)) from rfl]
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [hβdef, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [rs13ContrVec]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hcoeff i])]
  have hci : ∀ i : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis i)
        ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
          TangentSpace I x) : E) =
      (Module.finBasis ℝ E).repr
        ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
          TangentSpace I x) : E) i := by
    intro i
    rw [cDualBasis_eq_coord (E := E)]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => by rw [hci i])]
  exact (Module.finBasis ℝ E).sum_repr _

end NormedConnContr11And12

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_0312_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0312 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, d, b, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_0213_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0213 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, c, b, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_2301_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_2301 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![c, d, a, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_1302_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_1302 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, d, a, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_1203_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_1203 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, c, a, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_3201_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_3201 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![d, c, a, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_3102_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_3102 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![d, b, a, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_2103_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_2103 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![c, b, a, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_3012_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_3012 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![d, a, b, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_2013_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_2013 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![c, a, b, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_0231_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0231 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, c, d, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm4_0321_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0321 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, d, c, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm3_102_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (a b c : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm3_102 x D) ![a, b, c] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, a, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm3_120_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (a b c : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm3_120 x D) ![a, b, c] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, c, a] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotPerm2_10_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x)
    (a b : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm2_10 x D) ![a, b] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, a] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connContr21_insert' (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) (p q r s : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 2 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) ![p, q, r, s] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s, p, q] :=
  connContr21_insert (I := I) (M := M) g₁ g₀ x D ![p, q, r, s]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connContr11_insert' (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (p q r : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 1 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x q r, p] :=
  connContr11_insert (I := I) (M := M) g₁ g₀ x D ![p, q, r]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma connContr12_insert' (x : M) (B : Tensor0SBundle.TensorRSSpace 1 3 I x)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (p q r s : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (connContrCLM (I := I) 1 2 x B D) ![p, q, r, s] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![rs13ContrVec (I := I) (M := M) x B ![q, r, s], p] :=
  connContr12_insert (I := I) (M := M) x B D ![p, q, r, s]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma order1CLM_toModel_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (Z : Tensor0SBundle.Tensor0SSpace 3 I x) (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x) Z) ![a, b, c, d] =
      -(Tensor0SBundle.Tensor0SSpace.toModel Z
          ![a, PDE.DeTurck.connDiff (I := I) g₁ g₀ x b c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![a, c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x b d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b, c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![b, PDE.DeTurck.connDiff (I := I) g₁ g₀ x a c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![b, c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x a d]) := by
  rw [linearizedRicciConnDiffOrder1CLM]
  rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_neg, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [slotPerm4_0312_toModel, slotPerm4_0213_toModel, slotPerm4_2301_toModel,
    slotPerm4_1302_toModel, slotPerm4_1203_toModel]
  rw [connContr21_insert', connContr21_insert', connContr21_insert',
    connContr21_insert', connContr21_insert']
  rw [slotPerm3_102_toModel, slotPerm3_120_toModel, slotPerm3_102_toModel,
    slotPerm3_120_toModel]

omit [NeZero (Module.finrank ℝ E)] in
private lemma order0CLM_toModel_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (hT : Tensor0SBundle.Tensor0SSpace 2 I x) (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          hT) ![a, b, c, d] =
      (Tensor0SBundle.Tensor0SSpace.toModel hT
          ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x b
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a c), d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x a c,
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x b d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x b c,
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x a d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x b
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a d)])
      - Tensor0SBundle.Tensor0SSpace.toModel hT
          ![rs13ContrVec (I := I) (M := M) x
            ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            ![a, b, c], d]
      - Tensor0SBundle.Tensor0SSpace.toModel hT
          ![c, rs13ContrVec (I := I) (M := M) x
            ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            (![a, b, d])] := by
  rw [linearizedRicciConnDiffOrder0CLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply]
  simp only [Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  rw [slotPerm4_3201_toModel, slotPerm4_2301_toModel, slotPerm4_3102_toModel,
    slotPerm4_1302_toModel, slotPerm4_1203_toModel, slotPerm4_2103_toModel,
    slotPerm4_3012_toModel, slotPerm4_2013_toModel]
  rw [connContr21_insert', connContr21_insert', connContr21_insert',
    connContr21_insert', connContr21_insert', connContr21_insert']
  rw [connContr12_insert', connContr12_insert']
  rw [slotPerm3_102_toModel, slotPerm3_102_toModel, slotPerm3_120_toModel,
    slotPerm3_120_toModel]
  rw [connContr11_insert', connContr11_insert', connContr11_insert',
    connContr11_insert', connContr11_insert', connContr11_insert']
  rw [slotPerm2_10_toModel, slotPerm2_10_toModel, slotPerm2_10_toModel,
    slotPerm2_10_toModel]

omit [NeZero (Module.finrank ℝ E)] in
lemma covGradUnit_toModel_eval (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (y : M) (p : TangentSpace I y)
    (w : Fin n → TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (n + 1) I y from
          (covGrad (I := I) (M := M) g 0 n W).toSection y)
          (unitZeroSec (I := I) (M := M) y))
        (Fin.cons p w) =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g)
          (fun z : M =>
            (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ]
                Tensor0SBundle.Tensor0SSpace n I z from
              W.toSection z) (unitZeroSec (I := I) (M := M) z)) y p) w := by
  have h := unitModel_covGrad_eval (I := I) (M := M) g n W y (Fin.cons p w)
  rw [show unitModel (I := I) (M := M) g (n + 1) (covGrad (I := I) (M := M) g 0 n W) y
      (Fin.cons p w) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (n + 1) I y from
          (covGrad (I := I) (M := M) g 0 n W).toSection y)
          (unitZeroSec (I := I) (M := M) y))
        (Fin.cons p w) from rfl] at h
  rw [h]
  rw [show (Fin.cons p w : Fin (n + 1) → TangentSpace I y) 0 = p from rfl]
  rw [show Matrix.vecTail (Fin.cons p w : Fin (n + 1) → TangentSpace I y) = w from
    Matrix.tail_cons p w]

private def symmVelocityDiffSec (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y :=
  fun y : M =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')).toSection y) (unitZeroSec (I := I) (M := M) y)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma hUnitSec_tsmdiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (y : M) :
    TensorSectionMDiffAt (I := I) 2 (symmVelocityDiffSec (I := I) (M := M) g₀ T T') y :=
  unitEval_tensorSectionMDiffAt (I := I) (M := M) g₀ 2
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) y

private def symmVelocityDiffCovGradBaseSec (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y :=
  fun y : M =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
      (covGrad (I := I) (M := M) g₀ 0 2
        (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection y)
      (unitZeroSec (I := I) (M := M) y)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma kZeroSec_tsmdiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (y : M) :
    TensorSectionMDiffAt (I := I) 3 (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') y :=
  unitEval_tensorSectionMDiffAt (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) y

private def symmVelocityDiffCovGradRealizedSec (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y :=
  fun y : M =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
      (unitZeroSec (I := I) (M := M) y)

omit [BoundarylessManifold I M] in
private lemma kOneSec_tsmdiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) :
    TensorSectionMDiffAt (I := I) 3 (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s) y :=
  unitEval_tensorSectionMDiffAt (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
    (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) y

omit [NeZero (Module.finrank ℝ E)] in
private lemma kZeroSec_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (y : M) (p q r : TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' y) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (symmVelocityDiffSec (I := I) (M := M) g₀ T T') y p) ![q, r] := by
  have h := covGradUnit_toModel_eval (I := I) (M := M) g₀ 2
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) y p ![q, r]
  rw [show (Fin.cons p ![q, r] : Fin 3 → TangentSpace I y) = ![p, q, r] from
    funext fun j => by fin_cases j <;> rfl] at h
  exact h

private lemma kOneSec_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) (p q r : TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s y) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2
          (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (symmVelocityDiffSec (I := I) (M := M) g₀ T T') y p) ![q, r] := by
  have h := covGradUnit_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
    (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y p ![q, r]
  rw [show (Fin.cons p ![q, r] : Fin 3 → TangentSpace I y) = ![p, q, r] from
    funext fun j => by fin_cases j <;> rfl] at h
  rw [show (fun z : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I z from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection z)
        (unitZeroSec (I := I) (M := M) z)) =
      symmVelocityDiffSec (I := I) (M := M) g₀ T T' from rfl] at h
  exact h

private lemma kSec_bridge (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) (p q r : TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s y) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' y) ![p, q, r]
        - Tensor0SBundle.Tensor0SSpace.toModel (symmVelocityDiffSec (I := I) (M := M) g₀ T T' y)
            ![PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y q p, r]
        - Tensor0SBundle.Tensor0SSpace.toModel (symmVelocityDiffSec (I := I) (M := M) g₀ T T' y)
            ![q, PDE.DeTurck.connDiff (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y r p] := by
  rw [kOneSec_eval (I := I) (M := M) g₀ T T' hδ hδ' s y p q r,
    kZeroSec_eval (I := I) (M := M) g₀ T T' y p q r]
  exact bridge02_eval (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    (symmVelocityDiffSec (I := I) (M := M) g₀ T T')
    (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' y) p q r

private lemma velFibre_toModel_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3
          (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s) x (m 0)) ![m 1, m 2, m 3] := by
  have hm : m = Fin.cons (m 0) ![m 1, m 2, m 3] := by
    funext j
    fin_cases j <;> rfl
  have h := covGradUnit_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
    (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x (m 0) ![m 1, m 2, m 3]
  rw [show (fun z : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I z from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection z)
        (unitZeroSec (I := I) (M := M) z)) =
      symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s from rfl] at h
  rw [show unitModel (I := I) (M := M) g₀ 4
      (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 3
            (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s))).toSection x)
          (unitZeroSec (I := I) (M := M) x)) m from rfl]
  conv_lhs => rw [hm]
  exact h

omit [NeZero (Module.finrank ℝ E)] in
private lemma w2Fibre_toModel_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') x (m 0)) ![m 1, m 2, m 3] := by
  have hm : m = Fin.cons (m 0) ![m 1, m 2, m 3] := by
    funext j
    fin_cases j <;> rfl
  have h := covGradUnit_toModel_eval (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
    x (m 0) ![m 1, m 2, m 3]
  rw [show (fun z : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I z from
        (covGrad (I := I) (M := M) g₀ 0 2
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection z)
        (unitZeroSec (I := I) (M := M) z)) =
      symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' from rfl] at h
  rw [show unitModel (I := I) (M := M) g₀ 4
      (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))).toSection x)
          (unitZeroSec (I := I) (M := M) x)) m from rfl]
  conv_lhs => rw [hm]
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel3_add_slot0 {x : M} (T : Tensor0SBundle.Tensor0SSpace 3 I x)
    (p p' q r : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p + p', q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p', q, r] := by
  have hupd : ∀ z : TangentSpace I x,
      (![z, q, r] : Fin 3 → TangentSpace I x) = Function.update ![0, q, r] 0 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (p + p'), hupd p, hupd p']
  exact ContinuousMultilinearMap.map_update_add _ _ 0 _ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel3_add_slot1 {x : M} (T : Tensor0SBundle.Tensor0SSpace 3 I x)
    (p q q' r : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p, q + q', r] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p, q', r] := by
  have hupd : ∀ z : TangentSpace I x,
      (![p, z, r] : Fin 3 → TangentSpace I x) = Function.update ![p, 0, r] 1 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (q + q'), hupd q, hupd q']
  exact ContinuousMultilinearMap.map_update_add _ _ 1 _ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel3_add_slot2 {x : M} (T : Tensor0SBundle.Tensor0SSpace 3 I x)
    (p q r r' : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r + r'] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r'] := by
  have hupd : ∀ z : TangentSpace I x,
      (![p, q, z] : Fin 3 → TangentSpace I x) = Function.update ![p, q, 0] 2 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (r + r'), hupd r, hupd r']
  exact ContinuousMultilinearMap.map_update_add _ _ 2 _ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel2_add_slot0 {x : M} (T : Tensor0SBundle.Tensor0SSpace 2 I x)
    (p p' q : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p + p', q] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p', q] := by
  have hupd : ∀ z : TangentSpace I x,
      (![z, q] : Fin 2 → TangentSpace I x) = Function.update ![0, q] 0 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (p + p'), hupd p, hupd p']
  exact ContinuousMultilinearMap.map_update_add _ _ 0 _ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel2_add_slot1 {x : M} (T : Tensor0SBundle.Tensor0SSpace 2 I x)
    (p q q' : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p, q + q'] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p, q'] := by
  have hupd : ∀ z : TangentSpace I x,
      (![p, z] : Fin 2 → TangentSpace I x) = Function.update ![p, 0] 1 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (q + q'), hupd q, hupd q']
  exact ContinuousMultilinearMap.map_update_add _ _ 1 _ _

set_option maxHeartbeats 3200000 in

private theorem kOneSec_deriv_eq_threeArm_kernel (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3
          (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s) x a) ![b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
            (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') x a) ![b, c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel
            (linearizedRicciConnDiffOrder1CLM (I := I) x
              ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
              (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' x)) ![a, b, c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel
            (linearizedRicciConnDiffOrder0CLM (I := I) x
              ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
              ((covGrad (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
              (symmVelocityDiffSec (I := I) (M := M) g₀ T T' x)) ![a, b, c, d] := by
  classical
  obtain ⟨Af, hAx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x a
  obtain ⟨Bf, hBx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x b
  obtain ⟨Cf, hCx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x c
  obtain ⟨Df, hDx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x d
  rw [← hAx, ← hBx, ← hCx, ← hDx]
  have hL := peel3_core (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s)
    (kOneSec_tsmdiffAt (I := I) (M := M) g₀ T T' hδ hδ' s x) Bf Cf Df (Af x)
  have hR := peel3_core (I := I) (M := M) g₀
    (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T')
    (kZeroSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Bf Cf Df (Af x)
  have hDB : (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
      (fun y => Bf y) x (Af x) =
      (LeviCivita (I := I) g₀).toFun (fun y => Bf y) x (Af x)
        + PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
            (Bf x) (Af x) := by
    rw [PDE.DeTurck.connDiff_apply (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
      (σ := fun y => Bf y) Bf.mdifferentiableAt (Af x)]
    abel
  have hDC : (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
      (fun y => Cf y) x (Af x) =
      (LeviCivita (I := I) g₀).toFun (fun y => Cf y) x (Af x)
        + PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
            (Cf x) (Af x) := by
    rw [PDE.DeTurck.connDiff_apply (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
      (σ := fun y => Cf y) Cf.mdifferentiableAt (Af x)]
    abel
  have hDD : (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
      (fun y => Df y) x (Af x) =
      (LeviCivita (I := I) g₀).toFun (fun y => Df y) x (Af x)
        + PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
            (Df x) (Af x) := by
    rw [PDE.DeTurck.connDiff_apply (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
      (σ := fun y => Df y) Df.mdifferentiableAt (Af x)]
    abel
  rw [hDB, hDC, hDD, toModel3_add_slot0, toModel3_add_slot1, toModel3_add_slot2] at hL
  rw [kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      ((LeviCivita (I := I) g₀).toFun (fun y => Bf y) x (Af x)) (Cf x) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Bf x) (Af x)) (Cf x) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) ((LeviCivita (I := I) g₀).toFun (fun y => Cf y) x (Af x)) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Cf x) (Af x)) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) (Cf x) ((LeviCivita (I := I) g₀).toFun (fun y => Df y) x (Af x)),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) (Cf x) (PDE.DeTurck.connDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Df x) (Af x))] at hL
  have hexpC1 := peel2_core (I := I) (M := M) g₀
    (symmVelocityDiffSec (I := I) (M := M) g₀ T T')
    (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x)
    (connDiffVecField (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf)
    Df (Af x)
  have hexpC2 := peel2_core (I := I) (M := M) g₀
    (symmVelocityDiffSec (I := I) (M := M) g₀ T T')
    (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Cf
    (connDiffVecField (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf)
    (Af x)
  rw [show (fun y : M =>
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) y) =
      (fun y : M => PDE.DeTurck.connDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y (Cf y) (Bf y)) from rfl] at hexpC1
  rw [covDerivConnDiff_expand (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Cf Bf x] at hexpC1
  rw [show ((connDiffVecField (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) x : TangentSpace I x) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Cf x) (Bf x) from rfl] at hexpC1
  rw [toModel2_add_slot0, toModel2_add_slot0] at hexpC1
  rw [← kZeroSec_eval (I := I) (M := M) g₀ T T' x (Af x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Cf x) (Bf x)) (Df x)] at hexpC1
  rw [show (fun y : M =>
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y) =
      (fun y : M => PDE.DeTurck.connDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y (Df y) (Bf y)) from rfl] at hexpC2
  rw [covDerivConnDiff_expand (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Df Bf x] at hexpC2
  rw [show ((connDiffVecField (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) x : TangentSpace I x) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Df x) (Bf x) from rfl] at hexpC2
  rw [toModel2_add_slot1, toModel2_add_slot1] at hexpC2
  rw [← kZeroSec_eval (I := I) (M := M) g₀ T T' x (Af x) (Cf x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Df x) (Bf x))] at hexpC2
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Bf x) (Af x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Cf x) (Af x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Df x) (Af x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Cf x) (Bf x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Cf x) (Bf x)] at hexpC1
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Df x) (Bf x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Df x) (Bf x)] at hexpC2
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Cf x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Bf x))] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Df x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Bf x))] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Cf x)) (Bf x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Df x)) (Bf x)] at hL
  rw [covDerivConnDiff_symm23 (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Cf Bf x] at hexpC1
  rw [covDerivConnDiff_symm23 (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Df Bf x] at hexpC2
  have hscal : ∀ y : M,
      Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s) u (Bf u)) z (Cf z)) y' (Df y')) y =
      Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y')) y
        - Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z
                ((connDiffVecField (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y')) y
        - Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
              ((connDiffVecField (I := I) (M := M)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y')) y := by
    intro y
    rw [curried3_toModel_eval (I := I) (M := M)
      (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s) Bf Cf Df y]
    rw [curried3_toModel_eval (I := I) (M := M)
      (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') Bf Cf Df y]
    rw [curried2_toModel_eval (I := I) (M := M)
      (symmVelocityDiffSec (I := I) (M := M) g₀ T T')
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) Df y]
    rw [curried2_toModel_eval (I := I) (M := M)
      (symmVelocityDiffSec (I := I) (M := M) g₀ T T') Cf
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y]
    rw [show ((connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) y : TangentSpace I y) =
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y
          (Cf y) (Bf y) from rfl]
    rw [show ((connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y : TangentSpace I y) =
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y
          (Df y) (Bf y) from rfl]
    rw [kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s y (Bf y) (Cf y) (Df y)]
  have hMD0 : MDifferentiableAt I 𝓘(ℝ)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y'))) x :=
    (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section I M _).mpr
      (curried_tsmdiffAt (I := I) (M := M) 0 _
        (curried_tsmdiffAt (I := I) (M := M) 1 _
          (curried_tsmdiffAt (I := I) (M := M) 2 _
            (kZeroSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Bf) Cf) Df)
  have hMDC1 : MDifferentiableAt I 𝓘(ℝ)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z
            ((connDiffVecField (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y'))) x :=
    (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section I M _).mpr
      (curried_tsmdiffAt (I := I) (M := M) 0 _
        (curried_tsmdiffAt (I := I) (M := M) 1 _
          (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x)
          (connDiffVecField (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf)) Df)
  have hMDC2 : MDifferentiableAt I 𝓘(ℝ)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
          ((connDiffVecField (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y'))) x :=
    (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section I M _).mpr
      (curried_tsmdiffAt (I := I) (M := M) 0 _
        (curried_tsmdiffAt (I := I) (M := M) 1 _
          (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Cf)
        (connDiffVecField (I := I) (M := M)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf))
  have hExt : extDerivFun (I := I)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s) u (Bf u)) z (Cf z)) y' (Df y'))) x
        (Af x) =
      extDerivFun (I := I)
        (Tensor0SNabla.scalarFn I M
          (fun y' : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M
                (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y'))) x (Af x)
      - extDerivFun (I := I)
          (Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z
                ((connDiffVecField (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y'))) x (Af x)
      - extDerivFun (I := I)
          (Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
              ((connDiffVecField (I := I) (M := M)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y'))) x (Af x) := by
    have hfx : Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (symmVelocityDiffCovGradRealizedSec (I := I) (M := M) g₀ T T' hδ hδ' s) u (Bf u)) z (Cf z)) y' (Df y')) =
        (Tensor0SNabla.scalarFn I M
          (fun y' : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M
                (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y'))
          - Tensor0SNabla.scalarFn I M
              (fun y' : M => Tensor0SNabla.curriedSection I M
                (fun z : M => Tensor0SNabla.curriedSection I M
                  (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z
                  ((connDiffVecField (I := I) (M := M)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y')))
          - Tensor0SNabla.scalarFn I M
              (fun y' : M => Tensor0SNabla.curriedSection I M
                (fun z : M => Tensor0SNabla.curriedSection I M
                  (symmVelocityDiffSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
                ((connDiffVecField (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y')) := by
      funext y
      have h := hscal y
      rw [h]
      rfl
    rw [hfx]
    rw [extDerivFun_sub' (I := I) (hMD0.sub hMDC1) hMDC2,
      extDerivFun_sub' (I := I) hMD0 hMDC1]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  have hE1 := order1CLM_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' x) (Af x) (Bf x) (Cf x) (Df x)
  have hE0 := order0CLM_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (symmVelocityDiffSec (I := I) (M := M) g₀ T T' x) (Af x) (Bf x) (Cf x) (Df x)
  rw [rs13ContrVec_covGrad_eq (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Bf Cf x,
    rs13ContrVec_covGrad_eq (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Bf Df x] at hE0
  linarith [hL, hR, hExt, hexpC1, hexpC2, hE1, hE0]

omit [BoundarylessManifold I M] in
private lemma lichnerowiczFib_toModel_eq_fourTrace (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (P : Tensor0SBundle.Tensor0SSpace 4 I x)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x) P) v =
      Tensor0SBundle.Tensor0SSpace.toModel
        (ricciCometricFourTraceCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) x P) v := by
  classical
  have hsplit : (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x) P =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P
      - (1 / 2 : ℝ) •
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P) := by
    rw [show (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)
          - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl]
    have hts : ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x :
        Tensor0SBundle.TensorRSSpace 4 2 I x) =
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x
          - (1 / 2 : ℝ) • (traceHessianCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x := by
      rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
    rw [hts]
    rfl
  rw [hsplit]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      (ricciArmPrincipalCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P =
      ricciDeTurckPrincipalCoeffAtPoint (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x P from rfl]
  rw [ricciArmPrincipalCoeffFib_toModel,
    ricciPrincipalCoeffDoubleTraceModel_apply (E := E)
      (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)]
  rw [show (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      (traceHessianCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P =
      traceHessianFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x P from rfl]
  rw [traceHessianFib_toModel,
    modelDoubleTrace_apply (E := E) 2
      (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)]
  rw [ricciCometricFourTraceCLM]
  rw [ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply]
  rw [cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel,
    cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel]
  rw [slotPermCLM_apply, slotPermCLM_apply, slotPermCLM_apply]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [modelDoubleTrace_apply, modelDoubleTrace_apply, modelDoubleTrace_apply,
    modelDoubleTrace_apply]
  have h0231 : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr perm4_0231
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ![v 0, v 1, (Module.finBasis ℝ E) k]) := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  have h0321 : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr perm4_0321
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ![v 1, v 0, (Module.finBasis ℝ E) k]) := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  have h2301 : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr perm4_2301
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        ![v 0, v 1,
          cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k] := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  have hth : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        ![v 0, v 1,
          cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k] := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  rw [Finset.sum_congr rfl (fun k _ => h0231 k), Finset.sum_congr rfl (fun k _ => h0321 k),
    Finset.sum_congr rfl (fun k _ => h2301 k), Finset.sum_congr rfl (fun k _ => hth k)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

set_option maxRecDepth 16000 in

private theorem lichnerowicz_velocitySecondCovGrad_eq_threeArm_symm
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (_hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (_hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (_hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v
        + unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v
        + unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v := by
  classical
  have hVel : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 4 I x from
      (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 4 I x from
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
        (unitTensor (I := I) (M := M) x)
      + linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' x)
      + linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
          (symmVelocityDiffSec (I := I) (M := M) g₀ T T' x) := by
    apply Tensor0SBundle.tensor0SSpace_ext 4 x
    intro m
    have h2 := velFibre_toModel_eval (I := I) (M := M) g₀ T T' hδ hδ' s x m
    have h3 := kOneSec_deriv_eq_threeArm_kernel (I := I) (M := M) g₀ T T' hδ hδ' s x
      (m 0) (m 1) (m 2) (m 3)
    have h4 := w2Fibre_toModel_eval (I := I) (M := M) g₀ T T' x m
    have hm4 : m = ![m 0, m 1, m 2, m 3] := by
      funext j
      fin_cases j <;> rfl
    change unitModel (I := I) (M := M) g₀ 4
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x)
        + linearizedRicciConnDiffOrder1CLM (I := I) x
            ((connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
            (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' x)
        + linearizedRicciConnDiffOrder0CLM (I := I) x
            ((connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
            ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
            (symmVelocityDiffSec (I := I) (M := M) g₀ T T' x)) m
    rw [Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
    rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x)) m =
        unitModel (I := I) (M := M) g₀ 4
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x m from rfl]
    rw [h2, h4, h3, ← hm4]
  rw [show unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 4 I x from
            (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
            (unitTensor (I := I) (M := M) x))) v from rfl]
  rw [hVel, map_add, map_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  rw [lichnerowiczFib_toModel_eq_fourTrace (I := I) (M := M) g₀ T T' hδ hδ' s x
      (linearizedRicciConnDiffOrder1CLM (I := I) x
        ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
        (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' x)) v,
    lichnerowiczFib_toModel_eq_fourTrace (I := I) (M := M) g₀ T T' hδ hδ' s x
      (linearizedRicciConnDiffOrder0CLM (I := I) x
        ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
        ((covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
        (symmVelocityDiffSec (I := I) (M := M) g₀ T T' x)) v]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x))) v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v from rfl]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
      (ricciCometricFourTraceCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
        (linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          (symmVelocityDiffCovGradBaseSec (I := I) (M := M) g₀ T T' x))) v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 1
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v from rfl]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
      (ricciCometricFourTraceCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
        (linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
          (symmVelocityDiffSec (I := I) (M := M) g₀ T T' x))) v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x v from rfl]
  ring

theorem linearizedRicciAt_eq_threeArm_connDiffCoeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
                  + (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
                      - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s))
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 3 2
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s
                  + (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
                      - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s))
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 4 2
                (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  intro s hs x v
  have hsubsymm : ∀ (b : M) (p q : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') b p q = smoothCcTensorBilinForm (I := I) g₀ (T - T') b q p := by
    intro b p q
    rw [ccTensorBilin_sub_two, ccTensorBilin_sub_two, hTsymm b p q, hT'symm b p q]
  have hcollapse : ccTensor02Symm (I := I) (M := M) g₀ (T - T') = T - T' :=
    symmS_eq_self_of_symm (I := I) (M := M) g₀ (T - T') hsubsymm
  rw [← linearizedRicciConnDiffOrder0Coeff_eq_base_add_sub (I := I) g₀ T T' hδ hδ' s,
    ← linearizedRicciConnDiffOrder1Coeff_eq_base_add_sub (I := I) g₀ T T' hδ hδ' s]
  rw [unitModel_add_two_apply, unitModel_add_two_apply]
  rw [← hcollapse]
  rw [linearizedRicciAt_eq_lichnerowicz_velocitySecondCovGrad (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' hs x v,
    lichnerowicz_velocitySecondCovGrad_eq_threeArm_symm (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' hs x v]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
