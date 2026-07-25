import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformRiemannOperatorNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Tensor0SBundle Tensor0SNabla TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_self_nonneg' (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma exists_smooth_tensor0S_section_eq (t : ℕ) (x : M) (T₀ : Tensor0SSpace t I x) :
    ∃ A : Π b : M, Tensor0SSpace t I b, A x = T₀ ∧
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel t ℝ E)) ∞
        (fun b => TotalSpace.mk' (Tensor0SModel t ℝ E)
          (E := fun z : M => Tensor0SSpace t I z) b (A b)) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel t ℝ E) (fun y : M => Tensor0SSpace t I y)) :=
    tensor0SBundle_topology t
  letI : FiberBundle (Tensor0SModel t ℝ E) (fun y : M => Tensor0SSpace t I y) := tensor0SBundle_fiber t
  letI : VectorBundle ℝ (Tensor0SModel t ℝ E) (fun y : M => Tensor0SSpace t I y) := tensor0SBundle_vector t
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (Tensor0SModel t ℝ E)
      (fun y : M => Tensor0SSpace t I y) I := tensor0SBundle_smooth ∞ t
  exact ⟨smoothExtensionFiber (I := I) (F := Tensor0SModel t ℝ E)
      (V := fun b => Tensor0SSpace t I b) x T₀,
    smoothExtensionFiber_eq (I := I) (F := Tensor0SModel t ℝ E)
      (V := fun b => Tensor0SSpace t I b) x T₀,
    smoothExtensionFiber_contMDiff (I := I) (F := Tensor0SModel t ℝ E)
      (V := fun b => Tensor0SSpace t I b) x T₀⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorRSCov_toFun_unitEval (g : SmoothRiemannianMetric I M) (t : ℕ)
    (τ : Π y : M, TensorRSSpace 0 t I y) (x : M) (v : TangentSpace I x)
    (hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y (τ y)) x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensorRSCovariantDerivative I M 0 t (LeviCivita (I := I) g) τ x v)
        (unitZeroSec (I := I) (M := M) x) =
      tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)
        (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from τ y)
          (unitZeroSec (I := I) (M := M) y)) x v := by
  have hunit : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y (unitZeroSec (I := I) (M := M) y)) x :=
    ((unitZeroSec (I := I) (M := M)).contMDiff x).mdifferentiableAt (by simp)
  have hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((smoothExtensionTangent (I := I) x v) y)) x :=
    ((smoothExtensionTangent_contMDiff (I := I) x v) x).mdifferentiableAt (by simp)
  have hkey := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M) 0 t
    (LeviCivita (I := I) g) τ (fun y => unitZeroSec (I := I) (M := M) y)
    (smoothExtensionTangent (I := I) x v) hτ hunit hV
  rw [smoothExtensionTangent_eq (I := I) x v] at hkey
  rw [hkey]
  rw [show tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y => unitZeroSec (I := I) (M := M) y) x v = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

omit [CompactSpace M] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannSec_tensorRSCov_unitEval (g : SmoothRiemannianMetric I M) (t : ℕ)
    (X W : Π y : M, TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (τ : Π y : M, TensorRSSpace 0 t I y)
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y (τ y)))
    (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        riemannSec (tensorCov (I := I) g 0 t) X W τ x)
        (unitZeroSec (I := I) (M := M) x) =
      riemannSec (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) X W
        (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from τ y)
          (unitZeroSec (I := I) (M := M) y)) x := by
  classical
  letI : TopologicalSpace (TotalSpace (TensorRSModel 0 t ℝ E)
      (fun y : M => TensorRSSpace 0 t I y)) := tensorRSBundle_topology 0 t
  letI : FiberBundle (TensorRSModel 0 t ℝ E) (fun y : M => TensorRSSpace 0 t I y) :=
    tensorRSBundle_fiber 0 t
  letI : VectorBundle ℝ (TensorRSModel 0 t ℝ E) (fun y : M => TensorRSSpace 0 t I y) :=
    tensorRSBundle_vector 0 t
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel 0 t ℝ E)
      (fun y : M => TensorRSSpace 0 t I y) I := tensorRSBundle_smooth ∞ 0 t
  set cov := tensorCov (I := I) g 0 t with hcov_def
  set covS := tensor0SCovariantDerivative I M t (LeviCivita (I := I) g) with hcovS_def
  set A : Π y : M, Tensor0SSpace t I y :=
    fun y => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from τ y)
      (unitZeroSec (I := I) (M := M) y) with hA_def

  have hτ_at : ∀ y : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun w : M => TensorRSSpace 0 t I w) z (τ z)) y :=
    fun y => (hτ y).mdifferentiableAt (by simp)

  have hτ_succ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y (τ y)) := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hτ.of_le h_le

  have hcovApply_unit : ∀ (Z : Π y : M, TangentSpace I y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) →
      (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from
          covApply cov Z τ y) (unitZeroSec (I := I) (M := M) y)) =
        covApply covS Z A := by
    intro Z _hZ
    funext y
    have := tensorRSCov_toFun_unitEval (I := I) (M := M) g t τ y (Z y) (hτ_at y)
    rw [covApply_apply, covApply_apply]
    exact this

  have hX_at := (hX x).mdifferentiableAt (by simp)
  have hW_at := (hW x).mdifferentiableAt (by simp)

  rw [riemannSec_def, riemannSec_def]

  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  congr 1
  · congr 1
    · have hWτ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E))
          (fun z : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
            (E := fun w : M => TensorRSSpace 0 t I w) z (covApply cov W τ z)) x := by
        have := covApply_mdifferentiableAt_local (cov := cov) (X := W) (Z := τ) (x := x)
          hW_at hτ_succ
        exact this
      have hstep := tensorRSCov_toFun_unitEval (I := I) (M := M) g t (covApply cov W τ) x (X x)
        hWτ_at
      rw [hstep, hcovApply_unit W hW]
    · have hXτ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E))
          (fun z : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
            (E := fun w : M => TensorRSSpace 0 t I w) z (covApply cov X τ z)) x := by
        have := covApply_mdifferentiableAt_local (cov := cov) (X := X) (Z := τ) (x := x)
          hX_at hτ_succ
        exact this
      have hstep := tensorRSCov_toFun_unitEval (I := I) (M := M) g t (covApply cov X τ) x (W x)
        hXτ_at
      rw [hstep, hcovApply_unit X hX]
  · have hstep := tensorRSCov_toFun_unitEval (I := I) (M := M) g t τ x
      (VectorField.mlieBracket I X W x) (hτ_at x)
    rw [hstep]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_tensorCov_unitScalarRSLift_unitEval
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M) (v w : TangentSpace I x)
    (T₀ : Tensor0SSpace t I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        riemannOp (tensorCov (I := I) g 0 t) x v w
          (unitScalarRSLift (I := I) (M := M) x T₀))
        (unitZeroSec (I := I) (M := M) x) =
      riemannOp (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) x v w T₀ := by
  classical
  letI : TopologicalSpace (TotalSpace (Tensor0SModel t ℝ E)
      (fun y : M => Tensor0SSpace t I y)) := tensor0SBundle_topology t
  letI : FiberBundle (Tensor0SModel t ℝ E) (fun y : M => Tensor0SSpace t I y) :=
    tensor0SBundle_fiber t
  letI : VectorBundle ℝ (Tensor0SModel t ℝ E) (fun y : M => Tensor0SSpace t I y) :=
    tensor0SBundle_vector t
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (Tensor0SModel t ℝ E)
      (fun y : M => Tensor0SSpace t I y) I := tensor0SBundle_smooth ∞ t

  obtain ⟨A, hAx, hA_smooth⟩ := exists_smooth_tensor0S_section_eq (I := I) (M := M) t x T₀
  set Sig : Π y : M, TensorRSSpace 0 t I y :=
    unitScalarRSLiftSection (I := I) (M := M) A with hSig_def
  have hSig_smooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y (Sig y)) :=
    contMDiff_unitScalarRSLiftSection (I := I) (M := M) A hA_smooth

  set X : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x v with hX_def
  set W : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x w with hW_def
  have hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : W x = w := smoothExtensionTangent_eq (I := I) x w

  have hSigx : Sig x = unitScalarRSLift (I := I) (M := M) x T₀ := by
    rw [hSig_def, unitScalarRSLiftSection_apply, hAx]

  have hRS : riemannOp (tensorCov (I := I) g 0 t) x v w
        (unitScalarRSLift (I := I) (M := M) x T₀) =
      riemannSec (tensorCov (I := I) g 0 t) X W Sig x := by
    rw [← hXx, ← hWx, ← hSigx]
    exact riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 t) hX_smooth hW_smooth hSig_smooth
  rw [hRS]

  rw [riemannSec_tensorRSCov_unitEval (I := I) (M := M) g t X W hX_smooth hW_smooth Sig hSig_smooth x]

  have hSig_unit : (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from Sig y)
        (unitZeroSec (I := I) (M := M) y)) = A := by
    funext y
    rw [hSig_def]
    exact unitScalarRSLiftSection_apply_unit (I := I) (M := M) A y
  rw [hSig_unit]

  rw [← riemannOp_apply_smooth (cov := tensor0SCovariantDerivative I M t (LeviCivita (I := I) g))
    hX_smooth hW_smooth hA_smooth]
  rw [hXx, hWx, hAx]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_tensor0SCov_coframeS_apply_eval
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M) (v w : TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin t → Fin n)
    (u : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        (riemannOp (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) x v w
          (coframeS (I := I) (M := M) g x t e J)) u =
      - ∑ k : Fin t,
          ∏ s : Fin t, g.inner x (e (J s))
            (Function.update u k
              (riemannOp (cov := LeviCivita (I := I) g) x v w (u k)) s) := by
  classical

  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hX_def
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hW_def
  have hXx : (X : Π b : M, TangentSpace I b) x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : (W : Π b : M, TangentSpace I b) x = w := smoothExtensionTangent_eq (I := I) x w

  obtain ⟨A, hAx, hA_smooth⟩ :=
    exists_smooth_tensor0S_section_eq (I := I) (M := M) t x (coframeS (I := I) (M := M) g x t e J)

  have hop : riemannOp (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) x v w
        (coframeS (I := I) (M := M) g x t e J) =
      riemannSec (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b) A x := by
    rw [← hXx, ← hWx, ← hAx]
    exact riemannOp_apply_smooth
      (cov := tensor0SCovariantDerivative I M t (LeviCivita (I := I) g))
      (smoothExtensionTangent_contMDiff (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x w) hA_smooth
  rw [hop]
  rw [riemannSec_tensor0SCov_apply_eval (I := I) g t X W A hA_smooth x u]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)

  have hbase : riemannSec (LeviCivita (I := I) g) (fun b => X b) (fun b => W b)
        (fun b => smoothExtensionTangent (I := I) x (u k) b) x =
      riemannOp (cov := LeviCivita (I := I) g) x v w (u k) := by
    rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g)
      (X := fun b => X b) (Y := fun b => W b)
      (Z := fun b => smoothExtensionTangent (I := I) x (u k) b)
      (X.contMDiff) (W.contMDiff)
      (smoothExtensionTangent_contMDiff (I := I) x (u k))]
    rw [hXx, hWx, smoothExtensionTangent_eq (I := I) x (u k)]
  change Tensor0SSpace.toModel (A x)
      (Function.update u k (riemannSec (LeviCivita (I := I) g) (fun b => X b) (fun b => W b)
        (fun b => smoothExtensionTangent (I := I) x (u k) b) x)) = _
  rw [hAx]
  rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x t e J)
        (Function.update u k (riemannSec (LeviCivita (I := I) g) (fun b => X b) (fun b => W b)
          (fun b => smoothExtensionTangent (I := I) x (u k) b) x)) =
      coframeS (I := I) (M := M) g x t e J
        (Function.update u k (riemannSec (LeviCivita (I := I) g) (fun b => X b) (fun b => W b)
          (fun b => smoothExtensionTangent (I := I) x (u k) b) x)) from rfl]
  rw [coframeS_apply]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [hbase]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem abs_toModel_riemannOp_tensor0SCov_coframeS_le
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M) (v w : TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin t → Fin n)
    (m : Fin t → TangentSpace I x)
    (Kbase : ℝ) (hKbase : 0 ≤ Kbase)
    (hKb : ∀ (a b c : TangentSpace I x),
      g.inner x (riemannOp (cov := LeviCivita (I := I) g) x a b c)
          (riemannOp (cov := LeviCivita (I := I) g) x a b c) ≤
        Kbase * g.inner x a a * g.inner x b b * g.inner x c c)
    (hvv : g.inner x v v ≤ 1) (hww : g.inner x w w ≤ 1)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hm : ∀ s : Fin t, g.inner x (m s) (m s) ≤ 1) :
    |Tensor0SSpace.toModel
        (riemannOp (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) x v w
          (coframeS (I := I) (M := M) g x t e J)) m| ≤
      (t : ℝ) * Real.sqrt Kbase := by
  classical

  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun z : TangentSpace I x => cd.inner z z) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {z : TangentSpace I x |
      RCLike.re (cd.inner z z) < 1} := g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have hinner_eq : ∀ a b : TangentSpace I x, (inner ℝ a b : ℝ) = g.inner x a b := fun _ _ => rfl

  have hnorm_sq : ∀ a : TangentSpace I x, ‖a‖ ^ 2 = g.inner x a a := by
    intro a; rw [← hinner_eq a a]; exact (real_inner_self_eq_norm_sq a).symm

  have he_unit : ∀ i : Fin n, ‖e i‖ ≤ 1 := by
    intro i
    have h1 : ‖e i‖ ^ 2 = 1 := by rw [hnorm_sq (e i), horth i i, if_pos rfl]
    nlinarith [norm_nonneg (e i), sq_nonneg (‖e i‖ - 1), h1]
  have hm_unit : ∀ s : Fin t, ‖m s‖ ≤ 1 := by
    intro s
    have h1 : ‖m s‖ ^ 2 ≤ 1 := by rw [hnorm_sq (m s)]; exact hm s
    nlinarith [norm_nonneg (m s), h1]

  have hcurv_norm : ∀ s : Fin t,
      ‖riemannOp (cov := LeviCivita (I := I) g) x v w (m s)‖ ≤ Real.sqrt Kbase := by
    intro s
    have hg := hKb v w (m s)
    rw [← hnorm_sq] at hg
    have hbound : ‖riemannOp (cov := LeviCivita (I := I) g) x v w (m s)‖ ^ 2 ≤ Kbase := by
      refine le_trans hg ?_
      have hvv' : 0 ≤ g.inner x v v := metric_inner_self_nonneg' (I := I) g x v
      have hww' : 0 ≤ g.inner x w w := metric_inner_self_nonneg' (I := I) g x w
      have hmm' : 0 ≤ g.inner x (m s) (m s) := metric_inner_self_nonneg' (I := I) g x (m s)
      calc Kbase * g.inner x v v * g.inner x w w * g.inner x (m s) (m s)
          ≤ Kbase * 1 * 1 * 1 := by
            apply mul_le_mul
            · apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hvv hKbase
              · exact hww
              · exact hww'
              · exact mul_nonneg hKbase zero_le_one
            · exact hm s
            · exact hmm'
            · exact mul_nonneg (mul_nonneg hKbase zero_le_one) zero_le_one
        _ = Kbase := by ring
    calc ‖riemannOp (cov := LeviCivita (I := I) g) x v w (m s)‖
        = Real.sqrt (‖riemannOp (cov := LeviCivita (I := I) g) x v w (m s)‖ ^ 2) := by
          rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt Kbase := Real.sqrt_le_sqrt hbound

  have hsummand : ∀ k : Fin t,
      |∏ s : Fin t, g.inner x (e (J s))
        (Function.update m k
          (riemannOp (cov := LeviCivita (I := I) g) x v w (m k)) s)| ≤
        Real.sqrt Kbase := by
    intro k
    rw [Finset.abs_prod]

    have hsplit : ∏ s : Fin t, |g.inner x (e (J s))
          (Function.update m k
            (riemannOp (cov := LeviCivita (I := I) g) x v w (m k)) s)| =
        |g.inner x (e (J k))
            (riemannOp (cov := LeviCivita (I := I) g) x v w (m k))| *
          ∏ s ∈ Finset.univ.erase k, |g.inner x (e (J s)) (m s)| := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
      rw [Function.update_self]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl (fun s hs => ?_)
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
    rw [hsplit]

    have hk_le : |g.inner x (e (J k))
        (riemannOp (cov := LeviCivita (I := I) g) x v w (m k))| ≤ Real.sqrt Kbase := by
      rw [← hinner_eq (e (J k)) (riemannOp (cov := LeviCivita (I := I) g) x v w (m k))]
      refine le_trans (abs_real_inner_le_norm (e (J k)) _) ?_
      calc ‖e (J k)‖ * ‖riemannOp (cov := LeviCivita (I := I) g) x v w (m k)‖
          ≤ 1 * Real.sqrt Kbase :=
            mul_le_mul (he_unit (J k)) (hcurv_norm k) (norm_nonneg _) zero_le_one
        _ = Real.sqrt Kbase := one_mul _
    have hrest_le : ∏ s ∈ Finset.univ.erase k, |g.inner x (e (J s)) (m s)| ≤ 1 := by
      refine Finset.prod_le_one (fun s _ => abs_nonneg _) (fun s _ => ?_)
      rw [← hinner_eq (e (J s)) (m s)]
      refine le_trans (abs_real_inner_le_norm (e (J s)) (m s)) ?_
      calc ‖e (J s)‖ * ‖m s‖ ≤ 1 * 1 :=
            mul_le_mul (he_unit (J s)) (hm_unit s) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc |g.inner x (e (J k)) (riemannOp (cov := LeviCivita (I := I) g) x v w (m k))| *
          ∏ s ∈ Finset.univ.erase k, |g.inner x (e (J s)) (m s)|
        ≤ Real.sqrt Kbase * 1 :=
          mul_le_mul hk_le hrest_le (Finset.prod_nonneg (fun s _ => abs_nonneg _))
            (Real.sqrt_nonneg _)
      _ = Real.sqrt Kbase := mul_one _

  rw [riemannOp_tensor0SCov_coframeS_apply_eval (I := I) (M := M) g t x v w e J m]
  rw [abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ k : Fin t, |∏ s : Fin t, g.inner x (e (J s))
        (Function.update m k
          (riemannOp (cov := LeviCivita (I := I) g) x v w (m k)) s)|
      ≤ ∑ _k : Fin t, Real.sqrt Kbase := Finset.sum_le_sum (fun k _ => hsummand k)
    _ = (t : ℝ) * Real.sqrt Kbase := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_riemannOp_tensorCov_dualTensorFrameS_le
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (i j : Fin n) (J : Fin t → Fin n)
    (Kbase : ℝ) (hKbase : 0 ≤ Kbase)
    (hKb : ∀ (a b c : TangentSpace I x),
      g.inner x (riemannOp (cov := LeviCivita (I := I) g) x a b c)
          (riemannOp (cov := LeviCivita (I := I) g) x a b c) ≤
        Kbase * g.inner x a a * g.inner x b b * g.inner x c c)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 t x
        (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
          (dualTensorFrameS (I := I) (M := M) g x t e J)) ≤
      (Module.finrank ℝ E : ℝ) ^ t * ((t : ℝ) * Real.sqrt Kbase) ^ 2 := by
  classical

  have hii : g.inner x (e i) (e i) ≤ 1 := by rw [horth i i, if_pos rfl]
  have hjj : g.inner x (e j) (e j) ≤ 1 := by rw [horth j j, if_pos rfl]

  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun z : TangentSpace I x => cd.inner z z) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {z : TangentSpace I x |
      RCLike.re (cd.inner z z) < 1} := g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set nb : ℕ := Module.finrank ℝ (TangentSpace I x) with hnb_def
  set eob : OrthonormalBasis (Fin nb) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _ with heob_def
  set eb : Fin nb → TangentSpace I x := fun a => eob a with heb_def
  set K₀ : Fin 0 → Fin nb := fun a => a.elim0 with hK₀
  have hinner_eq : ∀ a b : TangentSpace I x, (inner ℝ a b : ℝ) = g.inner x a b := fun _ _ => rfl
  have hnbE : nb = Module.finrank ℝ E := rfl

  have horthb : ∀ a b : Fin nb, g.inner x (eb a) (eb b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp eob.orthonormal a b
    rw [← hinner_eq (eb a) (eb b)]; exact hite
  have hreprT : ∀ S : TensorRSSpace 0 t I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
        ∑ K : Fin 0 → Fin nb, ∑ Jp : Fin t → Fin nb,
          fiberNormSqSummand (I := I) (M := M) g x 0 t S nb eb K Jp := fun S => rfl
  set V : TensorRSSpace 0 t I x :=
    riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
      (dualTensorFrameS (I := I) (M := M) g x t e J) with hV_def

  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x 0 t eb hreprT V]

  have hdual : dualTensorFrameS (I := I) (M := M) g x t e J =
      unitScalarRSLift (I := I) (M := M) x (coframeS (I := I) (M := M) g x t e J) := by
    apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
    intro τ
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          dualTensorFrameS (I := I) (M := M) g x t e J) τ =
        tensor00Scalar (I := I) (M := M) x τ • coframeS (I := I) (M := M) g x t e J from
      dualTensorFrameS_apply (I := I) (M := M) g x t e J τ]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          unitScalarRSLift (I := I) (M := M) x (coframeS (I := I) (M := M) g x t e J)) τ =
        (tensor0Iso (I := I) M x τ) • coframeS (I := I) (M := M) g x t e J from
      unitScalarRSLift_apply (I := I) (M := M) x (coframeS (I := I) (M := M) g x t e J) τ]
    congr 1
  have hcomp_eval : ∀ Jp : Fin t → Fin nb,
      fiberNormSqComponent (I := I) (M := M) g x 0 t V nb eb K₀ Jp =
        Tensor0SSpace.toModel
          (riemannOp (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) x (e i) (e j)
            (coframeS (I := I) (M := M) g x t e J)) (fun s => eb (Jp s)) := by
    intro Jp
    unfold fiberNormSqComponent

    have hω : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun a => g.inner x (eb (K₀ a)))) = unitZeroSec (I := I) (M := M) x := by
      apply Tensor0SBundle.Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro mm
      have hL : Tensor0SBundle.Tensor0SSpace.toModel
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun a => g.inner x (eb (K₀ a)))) mm = 1 := by
        rw [show Tensor0SBundle.Tensor0SSpace.toModel
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun a => g.inner x (eb (K₀ a)))) mm =
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun a => g.inner x (eb (K₀ a)))) (fun a : Fin 0 => a.elim0) from by
          apply congrArg; funext a; exact a.elim0]
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        simp
      have hR : Tensor0SBundle.Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) mm = 1 := by
        rw [unitZeroSec_apply (I := I) (M := M) x,
          Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hL, hR]
    rw [hω, hV_def, hdual]
    rw [riemannOp_tensorCov_unitScalarRSLift_unitEval (I := I) (M := M) g t x (e i) (e j)
      (coframeS (I := I) (M := M) g x t e J)]
    rfl

  have hbnd_comp : ∀ Jp : Fin t → Fin nb,
      (fiberNormSqComponent (I := I) (M := M) g x 0 t V nb eb K₀ Jp) ^ 2 ≤
        ((t : ℝ) * Real.sqrt Kbase) ^ 2 := by
    intro Jp
    rw [hcomp_eval Jp]
    have hbd := abs_toModel_riemannOp_tensor0SCov_coframeS_le (I := I) (M := M) g t x (e i) (e j)
      e J (fun s => eb (Jp s)) Kbase hKbase hKb hii hjj horth
      (fun s => by rw [horthb (Jp s) (Jp s), if_pos rfl])
    exact sq_le_sq' (neg_le_of_abs_le hbd) (le_of_abs_le hbd)
  calc (∑ K : Fin 0 → Fin nb, ∑ Jp : Fin t → Fin nb,
          (fiberNormSqComponent (I := I) (M := M) g x 0 t V nb eb K Jp) ^ 2)
      = ∑ Jp : Fin t → Fin nb,
          (fiberNormSqComponent (I := I) (M := M) g x 0 t V nb eb K₀ Jp) ^ 2 := by
        rw [Finset.sum_eq_single K₀ (fun K _ hK => absurd (Subsingleton.elim K K₀) hK)
          (fun h => absurd (Finset.mem_univ K₀) h)]
    _ ≤ ∑ _Jp : Fin t → Fin nb, ((t : ℝ) * Real.sqrt Kbase) ^ 2 :=
          Finset.sum_le_sum (fun Jp _ => hbnd_comp Jp)
    _ = (Module.finrank ℝ E : ℝ) ^ t * ((t : ℝ) * Real.sqrt Kbase) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
          simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ, nsmul_eq_mul]
          rw [hnbE]
          push_cast
          ring

theorem exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound_of_leviCivitaGNormBound
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∀ (i j : Fin n) (J : Fin t → Fin n),
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x t e J)) ≤ K := by
  obtain ⟨Kbase, hKbase, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (g := g)
  refine ⟨(Module.finrank ℝ E : ℝ) ^ t * ((t : ℝ) * Real.sqrt Kbase) ^ 2, ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
  intro x n e horth i j J
  exact riemannianFiberNormSq_riemannOp_tensorCov_dualTensorFrameS_le (I := I) (M := M) g t x
    e i j J Kbase hKbase (fun a b c => hKb x a b c) horth

end Connection
end Integral
end DifferentialGeometry

end
