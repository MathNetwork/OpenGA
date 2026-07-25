import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ParsevalFrameDiffCurvatureTrace
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.BareSlot0CurryParseval
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma extDerivFunApply_contMDiff
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X : Π b : M, TangentSpace I b} (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun (I := I) f b (X b)) := by
  classical
  have htan : ContMDiff I.tangent (𝓘(ℝ, ℝ).tangent) ∞ (tangentMap I 𝓘(ℝ, ℝ) f) := by
    have h₁ : ContMDiff I 𝓘(ℝ, ℝ) ((∞ : WithTop ℕ∞) + 1) f := by simpa using hf
    exact h₁.contMDiff_tangentMap (le_refl _)
  have hXsec : ContMDiff I I.tangent ∞
      (fun b => (TotalSpace.mk' E b (X b) : TangentBundle I M)) := hX
  have hcomp : ContMDiff I (𝓘(ℝ, ℝ).tangent) ∞
      (fun b => tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (X b))) :=
    htan.comp hXsec
  have hsnd : ContMDiff (𝓘(ℝ, ℝ).tangent) 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2) := contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)
  have hresult : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b => (tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (X b))).2) :=
    hsnd.comp hcomp
  refine hresult.congr fun b => ?_
  simp [extDerivFun, tangentMap_snd, NormedSpace.fromTangentSpace]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma exists_globalSmoothScalar_eqOn_nhd
    {f : M → ℝ} {U : Set M} {x : M} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hU.mem_nhds hxU)
  refine ⟨fun b => χ b * f b, ?_, ?_⟩
  · have hχ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => (χ : M → ℝ) b) :=
      χ.contMDiff.of_le (by exact_mod_cast le_top)
    have hU_part : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b => χ b * f b) U :=
      (hχ_smooth.contMDiffOn).mul hf
    have hcompl_part : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b => χ b * f b) (tsupport χ)ᶜ := by
      apply (contMDiffOn_const (c := (0 : ℝ))).congr
      intro b hb
      rw [image_eq_zero_of_notMem_tsupport hb, zero_mul]
    refine contMDiff_of_contMDiffOn_union_of_isOpen hU_part hcompl_part ?_ hU
      (isOpen_compl_iff.mpr (isClosed_tsupport χ))
    rw [Set.eq_univ_iff_forall]
    intro b
    by_cases hb : b ∈ tsupport χ
    · exact Or.inl (hχ hb)
    · exact Or.inr hb
  · filter_upwards [χ.eventuallyEq_one] with b hb
    rw [hb, Pi.one_apply, one_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannSec_add_acted_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z Z' : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hZ' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z')) :
    riemannSec cov X Y (Z + Z') x = riemannSec cov X Y Z x + riemannSec cov X Y Z' x := by
  classical
  have hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hZ'_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z') := by simpa using hZ'
  have hZsum_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (Z + Z')) := by
    simpa using hZ.add_section hZ'
  have hZ_mdiff : MDifferentiable I (I.prod 𝓘(ℝ, E)) (T% Z) := hZ.mdifferentiable (by simp)
  have hZ'_mdiff : MDifferentiable I (I.prod 𝓘(ℝ, E)) (T% Z') := hZ'.mdifferentiable (by simp)
  refine riemannSec_add_third (cov := cov)
    (X := X) (Y := Y) (Z := Z) (Z' := Z') (x := x)
    (Filter.Eventually.of_forall hZ_mdiff)
    (Filter.Eventually.of_forall hZ'_mdiff)
    (covApply_mdifferentiableAt_local (cov := cov) hY_at hZ_le)
    (covApply_mdifferentiableAt_local (cov := cov) hY_at hZ'_le)
    (covApply_mdifferentiableAt_local (cov := cov) hY_at hZsum_le)
    (covApply_mdifferentiableAt_local (cov := cov) hX_at hZ_le)
    (covApply_mdifferentiableAt_local (cov := cov) hX_at hZ'_le)
    (covApply_mdifferentiableAt_local (cov := cov) hX_at hZsum_le)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma riemannSec_smul_acted_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, TangentSpace I b} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    riemannSec cov X Y (f • Z) x = f x • riemannSec cov X Y Z x := by
  classical
  have hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hfZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (f • Z)) := hf.smul_section hZ
  have hfZ_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (f • Z)) := by
    simpa using hfZ
  have hf_at2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x := by
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1
    exact (hf x).of_le hle
  have hf_mdiff : MDifferentiable I 𝓘(ℝ, ℝ) f := hf.mdifferentiable (by simp)
  have hZ_mdiff : MDifferentiable I (I.prod 𝓘(ℝ, E)) (T% Z) := hZ.mdifferentiable (by simp)
  have hZ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Z) x := hZ_mdiff x
  have hcXZ_at := covApply_mdifferentiableAt_local (cov := cov) hX_at hZ_le
  have hcYZ_at := covApply_mdifferentiableAt_local (cov := cov) hY_at hZ_le
  have hcXfZ_at := covApply_mdifferentiableAt_local (cov := cov) hX_at hfZ_le
  have hcYfZ_at := covApply_mdifferentiableAt_local (cov := cov) hY_at hfZ_le
  have hYf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun f b (Y b)) :=
    extDerivFunApply_contMDiff hf hY
  have hXf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun f b (X b)) :=
    extDerivFunApply_contMDiff hf hX
  have hYf_at : MDiffAt (fun b => extDerivFun f b (Y b)) x :=
    (hYf x).mdifferentiableAt (by simp)
  have hXf_at : MDiffAt (fun b => extDerivFun f b (X b)) x :=
    (hXf x).mdifferentiableAt (by simp)
  have hcYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov Y Z)) := by
    have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov Y Z)) Set.univ :=
      covApply_contMDiffOn (cov := cov) hY hZ_le
    intro b
    exact hop.contMDiffAt (Filter.univ_mem)
  have hcXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X Z)) := by
    have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X Z)) Set.univ :=
      covApply_contMDiffOn (cov := cov) hX hZ_le
    intro b
    exact hop.contMDiffAt (Filter.univ_mem)
  have hf_smul_cYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (f • covApply cov Y Z)) :=
    hf.smul_section hcYZ
  have hf_smul_cXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (f • covApply cov X Z)) :=
    hf.smul_section hcXZ
  have hYf_smul_Z : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% ((fun b => extDerivFun f b (Y b)) • Z)) := hYf.smul_section hZ
  have hXf_smul_Z : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% ((fun b => extDerivFun f b (X b)) • Z)) := hXf.smul_section hZ
  have hf_smul_cYZ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (f • covApply cov Y Z)) x :=
    (hf_smul_cYZ x).mdifferentiableAt (by simp)
  have hf_smul_cXZ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (f • covApply cov X Z)) x :=
    (hf_smul_cXZ x).mdifferentiableAt (by simp)
  have hYf_smul_Z_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% ((fun b => extDerivFun f b (Y b)) • Z)) x :=
    (hYf_smul_Z x).mdifferentiableAt (by simp)
  have hXf_smul_Z_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% ((fun b => extDerivFun f b (X b)) • Z)) x :=
    (hXf_smul_Z x).mdifferentiableAt (by simp)
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    (I.isInteriorPoint_iff (x := x)).mp BoundarylessManifold.isInteriorPoint
  exact riemannSec_smul_third (cov := cov)
    (f := f) (X := X) (Y := Y) (Z := Z) (x := x)
    hX_at hY_at hf_at2
    (Filter.Eventually.of_forall hf_mdiff)
    (Filter.Eventually.of_forall hZ_mdiff)
    hZ_at hcXZ_at hcYZ_at hcXfZ_at hcYfZ_at hYf_at hXf_at
    hf_smul_cYZ_at hf_smul_cXZ_at hYf_smul_Z_at hXf_smul_Z_at hx_int

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_add_acted
    (g : SmoothRiemannianMetric I M)
    (X Y Z W W' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => (W + W') b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
          (fun b => W b) x
        + nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
            (fun b => W' b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff; have hZ := Z.contMDiff
  have hW := W.contMDiff; have hW' := W'.contMDiff
  rw [nablaCurvSec_def, nablaCurvSec_def, nablaCurvSec_def]

  have hsecWW' : (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => (W + W') b) b) =
      (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b)
        + (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W' b) b) := by
    funext b
    have heq : (fun b => (W + W') b) = (fun b => W b) + (fun b => W' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq]
    simp only [Pi.add_apply]
    exact riemannSec_add_acted_smooth (cov := cov) hY hZ hW hW'
  have hRWsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b)) :=
    riemannSec_contMDiff (cov := cov) hY hZ hW
  have hRW'sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W' b) b)) :=
    riemannSec_contMDiff (cov := cov) hY hZ hW'
  have h1 : cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => (W + W') b) b)
        x (X x) =
      cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x (X x)
        + cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W' b) b) x
            (X x) := by
    rw [hsecWW', cov.isCovariantDerivativeOnUniv.add (hRWsm.mdifferentiableAt (by simp))
      (hRW'sm.mdifferentiableAt (by simp))]
    rfl

  have hcXY := covApply_contMDiff (cov := cov) hX hY
  have h2 : riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
        (fun b => (W + W') b) x =
      riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b) (fun b => W b) x
        + riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
            (fun b => W' b) x := by
    have heq : (fun b => (W + W') b) = (fun b => W b) + (fun b => W' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq]
    exact riemannSec_add_acted_smooth (cov := cov) hcXY hZ hW hW'

  have hcXZ := covApply_contMDiff (cov := cov) hX hZ
  have h3 : riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
        (fun b => (W + W') b) x =
      riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b)) (fun b => W b) x
        + riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
            (fun b => W' b) x := by
    have heq : (fun b => (W + W') b) = (fun b => W b) + (fun b => W' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq]
    exact riemannSec_add_acted_smooth (cov := cov) hY hcXZ hW hW'

  have hcovT4 : covApply cov (fun b => X b) (fun b => (W + W') b) =
      covApply cov (fun b => X b) (fun b => W b) + covApply cov (fun b => X b) (fun b => W' b) := by
    funext b
    change cov.toFun (fun b => (W + W') b) b (X b) =
      cov.toFun (fun b => W b) b (X b) + cov.toFun (fun b => W' b) b (X b)
    have heq : (fun b => (W + W') b) = (fun b => W b) + (fun b => W' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq, cov.isCovariantDerivativeOnUniv.add ((hW b).mdifferentiableAt (by simp))
      ((hW' b).mdifferentiableAt (by simp))]
    rfl
  have hcXW := covApply_contMDiff (cov := cov) hX hW
  have hcXW' := covApply_contMDiff (cov := cov) hX hW'
  have h4 : riemannSec cov (fun b => Y b) (fun b => Z b)
        (covApply cov (fun b => X b) (fun b => (W + W') b)) x =
      riemannSec cov (fun b => Y b) (fun b => Z b) (covApply cov (fun b => X b) (fun b => W b)) x
        + riemannSec cov (fun b => Y b) (fun b => Z b)
            (covApply cov (fun b => X b) (fun b => W' b)) x := by
    rw [hcovT4]
    exact riemannSec_add_acted_smooth (cov := cov) hY hZ hcXW hcXW'
  rw [h1, h2, h3, h4]
  abel

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_smul_acted
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (f • fun b => W b) x =
      f x • nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff; have hZ := Z.contMDiff; have hW := W.contMDiff
  rw [nablaCurvSec_def, nablaCurvSec_def]
  set Xf : M → ℝ := fun b => extDerivFun (I := I) f b (X b) with hXf_def
  have hXf : ContMDiff I 𝓘(ℝ, ℝ) ∞ Xf := extDerivFunApply_contMDiff hf hX
  have hfW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (f • fun b => W b)) := hf.smul_section hW

  have hsec1 :
      (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (f • fun b => W b) b) =
        f • (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) := by
    funext b
    change riemannSec cov (fun b => Y b) (fun b => Z b) (f • fun b => W b) b =
      f b • riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b
    exact riemannSec_smul_acted_smooth (cov := cov) hf hY hZ hW
  have hRWsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b)) :=
    riemannSec_contMDiff (cov := cov) hY hZ hW
  have h1 :
      cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (f • fun b => W b) b) x (X x) =
        f x • cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x (X x)
          + Xf x • riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) x := by
    rw [hsec1, cov.isCovariantDerivativeOnUniv.leibniz (hRWsm.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, hXf_def]

  have hcXY := covApply_contMDiff (cov := cov) hX hY
  have hcXZ := covApply_contMDiff (cov := cov) hX hZ
  have h2 : riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
        (f • fun b => W b) x =
      f x • riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
        (fun b => W b) x :=
    riemannSec_smul_acted_smooth (cov := cov) hf hcXY hZ hW
  have h3 : riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
        (f • fun b => W b) x =
      f x • riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
        (fun b => W b) x :=
    riemannSec_smul_acted_smooth (cov := cov) hf hY hcXZ hW

  have hcXW := covApply_contMDiff (cov := cov) hX hW
  have hsec4 : covApply cov (fun b => X b) (f • fun b => W b) =
      f • covApply cov (fun b => X b) (fun b => W b) + Xf • (fun b => W b) := by
    funext b
    change cov.toFun (f • fun b => W b) b (X b) =
      f b • cov.toFun (fun b => W b) b (X b) + Xf b • W b
    rw [cov.isCovariantDerivativeOnUniv.leibniz ((hW b).mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, hXf_def]
  have h4 : riemannSec cov (fun b => Y b) (fun b => Z b)
        (covApply cov (fun b => X b) (f • fun b => W b)) x =
      f x • riemannSec cov (fun b => Y b) (fun b => Z b)
          (covApply cov (fun b => X b) (fun b => W b)) x
        + Xf x • riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) x := by
    rw [hsec4, riemannSec_add_acted_smooth (cov := cov) hY hZ (hf.smul_section hcXW)
        (hXf.smul_section hW),
      riemannSec_smul_acted_smooth (cov := cov) hf hY hZ hcXW,
      riemannSec_smul_acted_smooth (cov := cov) hXf hY hZ hW]
  rw [h1, h2, h3, h4]
  simp only [smul_sub]
  abel

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_finsetSum_acted
    (g : SmoothRiemannianMetric I M) {ι : Type*} (s : Finset ι)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => (∑ i ∈ s, W i) b) x =
      ∑ i ∈ s, nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W i b) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]

      have h := nablaCurvSec_add_acted (g := g) X Y Z
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x
      have hfun : (fun b => ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
            + (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) b) =
          (fun b => (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) := by
        funext b; simp
      rw [hfun] at h
      exact add_eq_left.mp h.symm
  | insert a t ha ih =>
      have hfun : (fun b => (∑ i ∈ insert a t, W i) b) =
          (fun b => (W a + ∑ i ∈ t, W i) b) := by
        funext b
        rw [ContMDiffSection.finset_sum_apply, Finset.sum_insert ha,
          ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.finset_sum_apply]
      rw [hfun, nablaCurvSec_add_acted (g := g) X Y Z (W a) (∑ i ∈ t, W i) x, ih,
        Finset.sum_insert ha]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_acted_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    {X Y Z W W' : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hW' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W'))
    (hWW' : ∀ᶠ b in 𝓝 x, W b = W' b) :
    nablaCurvSec (LeviCivita (I := I) g) X Y Z W x =
      nablaCurvSec (LeviCivita (I := I) g) X Y Z W' x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hW_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% W) := by simpa using hW
  have hW'_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% W') := by simpa using hW'
  rw [nablaCurvSec_def, nablaCurvSec_def]

  have hsec_ev : ∀ᶠ b in 𝓝 x,
      riemannSec cov Y Z W b = riemannSec cov Y Z W' b := by
    rw [Filter.eventually_iff_exists_mem] at hWW' ⊢
    obtain ⟨U, hU, hWeq⟩ := hWW'
    obtain ⟨V', hV'U, hV'_open, hpV'⟩ := mem_nhds_iff.mp hU
    refine ⟨V', hV'_open.mem_nhds hpV', fun b _ => ?_⟩
    exact riemannSec_eq_of_Z_eq_at (cov := cov) hY hZ hW hW' (hWeq b (by
      have : b ∈ V' := by assumption
      exact hV'U this))
  have hRYZW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y Z W b)) :=
    riemannSec_contMDiff cov hY hZ hW
  have hRYZW'_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y Z W' b)) :=
    riemannSec_contMDiff cov hY hZ hW'
  have hT1 : cov.toFun (fun b => riemannSec cov Y Z W b) x =
      cov.toFun (fun b => riemannSec cov Y Z W' b) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hRYZW_sm.mdifferentiableAt (by simp)) (hRYZW'_sm.mdifferentiableAt (by simp))
      Filter.univ_mem hsec_ev
  rw [hT1]

  have hcXY := covApply_contMDiff (cov := cov) hX hY
  have hcXZ := covApply_contMDiff (cov := cov) hX hZ
  have hcXY_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (covApply cov X Y)) := by
    simpa using hcXY
  have hcXZ_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (covApply cov X Z)) := by
    simpa using hcXZ
  have hT2 : riemannSec cov (covApply cov X Y) Z W x =
      riemannSec cov (covApply cov X Y) Z W' x :=
    riemannSec_eq_of_Z_eventuallyEq (cov := cov) hcXY hZ hW_le hW'_le hWW'
  rw [hT2]
  have hT3 : riemannSec cov Y (covApply cov X Z) W x =
      riemannSec cov Y (covApply cov X Z) W' x :=
    riemannSec_eq_of_Z_eventuallyEq (cov := cov) hY hcXZ hW_le hW'_le hWW'
  rw [hT3]

  have hcXW := covApply_contMDiff (cov := cov) hX hW
  have hcXW' := covApply_contMDiff (cov := cov) hX hW'
  have hcXW_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (covApply cov X W)) := by
    simpa using hcXW
  have hcXW'_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (covApply cov X W')) := by
    simpa using hcXW'
  have hev_cXW : ∀ᶠ b in 𝓝 x, covApply cov X W b = covApply cov X W' b := by
    rw [Filter.eventually_iff_exists_mem] at hWW' ⊢
    obtain ⟨U, hU, hWeq⟩ := hWW'
    obtain ⟨V', hV'U, hV'_open, hpV'⟩ := mem_nhds_iff.mp hU
    refine ⟨V', hV'_open.mem_nhds hpV', fun b hbV' => ?_⟩
    have hWeq_b : ∀ᶠ b' in 𝓝 b, W b' = W' b' :=
      Filter.eventually_of_mem (hV'_open.mem_nhds hbV') (fun b' hb'V' => hWeq b' (hV'U hb'V'))
    have hcov_b : cov.toFun W b = cov.toFun W' b :=
      cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((hW b).mdifferentiableAt (by simp)) ((hW' b).mdifferentiableAt (by simp))
        Filter.univ_mem hWeq_b
    simp only [covApply_apply, hcov_b]
  have hT4 : riemannSec cov Y Z (covApply cov X W) x =
      riemannSec cov Y Z (covApply cov X W') x :=
    riemannSec_eq_of_Z_eventuallyEq (cov := cov) hY hZ hcXW_le hcXW'_le hev_cXW
  rw [hT4]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_vanish_acted
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {Δ : Π b : M, TangentSpace I b} {x : M}
    (hΔ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Δ)) (hΔx : Δ x = 0) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b) Δ x = 0 := by
  classical
  set e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M) :=
    trivializationAt E (TangentSpace I) x with he_def
  have hx_base : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hbase_open : IsOpen e.baseSet := e.open_baseSet
  set bE : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ E) ℝ E := Module.Basis.ofVectorSpace ℝ E
    with hbE_def
  set sLoc : Module.Basis.ofVectorSpaceIndex ℝ E → Π b : M, TangentSpace I b :=
    fun i => e.localFrame bE i with hsLoc_def
  set cLoc : Module.Basis.ofVectorSpaceIndex ℝ E → M → ℝ :=
    fun i b => e.localFrame_coeff I bE i b (Δ b) with hcLoc_def
  have hexpand : ∀ᶠ b in 𝓝 x, Δ b = ∑ i, cLoc i b • sLoc i b :=
    e.eventually_eq_localFrame_sum_coeff_smul bE hx_base
  have hsLoc_on : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (sLoc i)) e.baseSet :=
    fun i => e.contMDiffOn_localFrame_baseSet (n := ∞) (b := bE) i
  have hcLoc_on : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (cLoc i) e.baseSet := by
    intro i b hb
    exact (contMDiffAt_localFrame_coeff bE hb (hΔ b) i).contMDiffWithinAt
  obtain ⟨Sglob, hSglob_eq⟩ := exists_contMDiffSection_eqOn_nhd (I := I)
    (V := fun z : M => TangentSpace I z) (n := (⊤ : ℕ∞)) (s := sLoc)
    (fun i => (hsLoc_on i).of_le (by exact_mod_cast le_top)) hbase_open hx_base
  have hfglob : ∀ i, ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] cLoc i :=
    fun i => exists_globalSmoothScalar_eqOn_nhd hbase_open hx_base (hcLoc_on i)
  choose fglob hfglob_smooth hfglob_eq using hfglob
  set Ssec : Module.Basis.ofVectorSpaceIndex ℝ E → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    fun i => Sglob i with hSsec_def
  set fbun : Module.Basis.ofVectorSpaceIndex ℝ E → C^∞⟮I, M; ℝ⟯ :=
    fun i => ⟨fglob i, hfglob_smooth i⟩ with hfbun_def
  have hfbun_coe : ∀ i, (fbun i : M → ℝ) = fglob i := fun i => rfl
  have hWW' : ∀ᶠ b in 𝓝 x, Δ b = (∑ i, fbun i • Ssec i) b := by
    filter_upwards [hexpand, hSglob_eq, Filter.eventually_all.mpr hfglob_eq] with b hbexp hbS hbf
    rw [hbexp, ContMDiffSection.finset_sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hval : (fbun i • Ssec i) b = fglob i b • (Ssec i : Π z : M, TangentSpace I z) b := rfl
    rw [hval, hbf i]
    have hSb : (Ssec i : Π z : M, TangentSpace I z) b = sLoc i b := hbS i
    rw [hSb]
  have hcomb_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% ((∑ i, fbun i • Ssec i :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : Π b : M, TangentSpace I b)) :=
    (∑ i, fbun i • Ssec i).contMDiff
  rw [nablaCurvSec_acted_eventuallyEq (g := g) X.contMDiff Y.contMDiff Z.contMDiff hΔ
    hcomb_smooth hWW']
  rw [nablaCurvSec_finsetSum_acted (g := g) Finset.univ X Y Z
    (fun i => fbun i • Ssec i) x]
  apply Finset.sum_eq_zero
  intro i _
  rw [show (fun b => (fbun i • Ssec i) b) =
      ((fbun i : M → ℝ) • fun b => (Ssec i : Π z : M, TangentSpace I z) b) from rfl,
    nablaCurvSec_smul_acted (g := g) (by rw [hfbun_coe]; exact hfglob_smooth i) X Y Z (Ssec i) x]
  have hfix : (fbun i : M → ℝ) x = 0 := by
    rw [hfbun_coe, (hfglob_eq i).self_of_nhds, hcLoc_def]
    simp only [hΔx, map_zero]
  rw [hfix, zero_smul]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaCurvSec_eq_of_acted_eq
    (g : SmoothRiemannianMetric I M)
    (X Y Z W W' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hWW' : (W : Π b : M, TangentSpace I b) x = W' x) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W' b) x := by
  classical
  have hsplit := nablaCurvSec_add_acted (g := g) X Y Z W' (W - W') x
  have hfun : (fun b => (W' + (W - W')) b) = (fun b => W b) := by
    funext b
    simp only [ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply]
    abel
  rw [hfun] at hsplit
  have hvanish : nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
      (fun b => (W - W') b) x = 0 := by
    refine nablaCurvSec_vanish_acted (g := g) X Y Z (Δ := fun b => (W - W') b)
      (W - W').contMDiff ?_
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, hWW', sub_self]
  rw [hsplit, hvanish, add_zero]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaBaseSlotCurv_add_acted
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u v : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x (u + v) =
      nablaBaseSlotCurv (I := I) g X Y Z x u + nablaBaseSlotCurv (I := I) g X Y Z x v := by
  classical
  set eu := ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
    (smoothExtensionTangent_contMDiff (I := I) x u) with heu_def
  set ev := ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent_contMDiff (I := I) x v) with hev_def
  set euv := ContMDiffSection.mk (smoothExtensionTangent (I := I) x (u + v))
    (smoothExtensionTangent_contMDiff (I := I) x (u + v)) with heuv_def
  have hbase : nablaBaseSlotCurv (I := I) g X Y Z x (u + v) =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => euv b) x := nablaBaseSlotCurv_eq_nablaCurvSec (I := I) g X Y Z x (u + v)
  have hbu : nablaBaseSlotCurv (I := I) g X Y Z x u =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => eu b) x := nablaBaseSlotCurv_eq_nablaCurvSec (I := I) g X Y Z x u
  have hbv : nablaBaseSlotCurv (I := I) g X Y Z x v =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => ev b) x := nablaBaseSlotCurv_eq_nablaCurvSec (I := I) g X Y Z x v
  rw [hbase, hbu, hbv]

  have hval : (euv : Π b : M, TangentSpace I b) x = (eu + ev) x := by
    simp only [heuv_def, heu_def, hev_def, ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add,
      Pi.add_apply, smoothExtensionTangent_eq]
  rw [nablaCurvSec_eq_of_acted_eq (g := g) X Y Z euv (eu + ev) x hval]
  exact nablaCurvSec_add_acted (g := g) X Y Z eu ev x

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaBaseSlotCurv_smul_acted
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x (c • u) =
      c • nablaBaseSlotCurv (I := I) g X Y Z x u := by
  classical
  set eu := ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
    (smoothExtensionTangent_contMDiff (I := I) x u) with heu_def
  set ecu := ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • u))
    (smoothExtensionTangent_contMDiff (I := I) x (c • u)) with hecu_def
  have hbase : nablaBaseSlotCurv (I := I) g X Y Z x (c • u) =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => ecu b) x := nablaBaseSlotCurv_eq_nablaCurvSec (I := I) g X Y Z x (c • u)
  have hbu : nablaBaseSlotCurv (I := I) g X Y Z x u =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => eu b) x := nablaBaseSlotCurv_eq_nablaCurvSec (I := I) g X Y Z x u
  rw [hbase, hbu]
  have hcsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const

  set ecu' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk ((fun _ : M => c) • (fun b => smoothExtensionTangent (I := I) x u b))
      (hcsmooth.smul_section eu.contMDiff) with hecu'_def
  have hecuval : (ecu : Π b : M, TangentSpace I b) x = c • u := by
    rw [hecu_def]; change smoothExtensionTangent (I := I) x (c • u) x = c • u
    rw [smoothExtensionTangent_eq]
  have hecu'val : (ecu' : Π b : M, TangentSpace I b) x = c • u := by
    rw [hecu'_def]
    change ((fun _ : M => c) • fun b => smoothExtensionTangent (I := I) x u b) x = c • u
    change c • smoothExtensionTangent (I := I) x u x = c • u
    rw [smoothExtensionTangent_eq]
  have hval : (ecu : Π b : M, TangentSpace I b) x = (ecu' : Π b : M, TangentSpace I b) x := by
    rw [hecuval, hecu'val]
  rw [nablaCurvSec_eq_of_acted_eq (g := g) X Y Z ecu ecu' x hval]
  have h := nablaCurvSec_smul_acted (g := g) hcsmooth X Y Z eu x

  have hfield : (fun b => (ecu' : Π b : M, TangentSpace I b) b) =
      ((fun _ : M => c) • fun b => (eu : Π b : M, TangentSpace I b) b) := by
    funext b
    simp only [hecu'_def, heu_def, ContMDiffSection.coeFn_mk]
  rw [hfield]
  exact h

def nablaBaseSlotCurvFrameSumLinear
    (g : SmoothRiemannianMetric I M) {ι : Type*} [Fintype ι]
    (B : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun w := ∑ i : ι, nablaBaseSlotCurv (I := I) g (B i) (B i) Vb x w
  map_add' u v := by
    simp only [nablaBaseSlotCurv_add_acted]
    rw [Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [nablaBaseSlotCurv_smul_acted, RingHom.id_apply, Finset.smul_sum]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma nablaBaseSlotCurvFrameSumLinear_apply
    (g : SmoothRiemannianMetric I M) {ι : Type*} [Fintype ι]
    (B : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    nablaBaseSlotCurvFrameSumLinear (I := I) g B Vb x w =
      ∑ i : ι, nablaBaseSlotCurv (I := I) g (B i) (B i) Vb x w := rfl

noncomputable def nablaBaseSlotCurvFrameSumCLM
    (g : SmoothRiemannianMetric I M) {ι : Type*} [Fintype ι]
    (B : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (nablaBaseSlotCurvFrameSumLinear (I := I) g B Vb x)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma nablaBaseSlotCurvFrameSumCLM_apply
    (g : SmoothRiemannianMetric I M) {ι : Type*} [Fintype ι]
    (B : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x w =
      ∑ i : ι, nablaBaseSlotCurv (I := I) g (B i) (B i) Vb x w := rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaRicci_symm
    (g : SmoothRiemannianMetric I M)
    (X V W : Π b : M, TangentSpace I b) (x : M) :
    nablaRicci (I := I) g X V W x = nablaRicci (I := I) g X W V x := by
  classical
  rw [nablaRicci_def, nablaRicci_def]
  have hlead : (fun b => ricciTensor (I := I) g b (V b) (W b)) =
      (fun b => ricciTensor (I := I) g b (W b) (V b)) := by
    funext b; exact ricciTensor_symm (I := I) g b (V b) (W b)
  rw [hlead]
  rw [ricciTensor_symm (I := I) g x ((LeviCivita (I := I) g).toFun V x (X x)) (W x),
    ricciTensor_symm (I := I) g x (V x) ((LeviCivita (I := I) g).toFun W x (X x))]
  ring

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma nablaRicci_add_right_raw
    (g : SmoothRiemannianMetric I M)
    (X V W W' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => (W + W') b) x =
      nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x +
        nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W' b) x := by
  classical
  have hWW' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => (W + W') b)) :=
    W.contMDiff.add_section W'.contMDiff
  rw [nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g X.contMDiff V.contMDiff hWW',
    nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g X.contMDiff V.contMDiff W.contMDiff,
    nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g X.contMDiff V.contMDiff W'.contMDiff,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hadd : nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
        (smoothOrthoFrame (I := I) g x i) (fun b => V b) (fun b => (W + W') b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
          (smoothOrthoFrame (I := I) g x i) (fun b => V b) (fun b => W b) x +
        nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
          (smoothOrthoFrame (I := I) g x i) (fun b => V b) (fun b => W' b) x :=
    nablaCurvSec_add_acted (g := g)
      X (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) V W W' x
  rw [hadd, (g.inner x).map_add, ContinuousLinearMap.add_apply]

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma nablaRicci_smul_right_raw
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => (c • W) b) x =
      c • nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x := by
  classical
  have hcW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => (c • W) b)) := by
    have : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% ((fun _ : M => c) • fun b => W b)) :=
      contMDiff_const.smul_section W.contMDiff
    exact this
  rw [nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g X.contMDiff V.contMDiff hcW,
    nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g X.contMDiff V.contMDiff W.contMDiff,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hsmul : nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
        (smoothOrthoFrame (I := I) g x i) (fun b => V b) (fun b => (c • W) b) x =
      c • nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
          (smoothOrthoFrame (I := I) g x i) (fun b => V b) (fun b => W b) x := by
    have h := nablaCurvSec_smul_acted (g := g) (f := fun _ : M => c) contMDiff_const
      X (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) V W x
    have hcoe : ((fun _ : M => c) • fun b => W b) = (fun b => (c • W) b) := by
      funext b
      change c • (W : Π b : M, TangentSpace I b) b = (c • W) b
      rw [ContMDiffSection.coe_smul]
      rfl
    rw [hcoe] at h
    simpa only [ContMDiffSection.coeFn_mk] using h
  rw [hsmul, (g.inner x).map_smul, ContinuousLinearMap.smul_apply]

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma nablaRicci_eq_of_W_eq_raw
    (g : SmoothRiemannianMetric I M)
    (X V W W' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hWW' : (W : Π b : M, TangentSpace I b) x = W' x) :
    nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x =
      nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W' b) x := by
  classical
  rw [nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g X.contMDiff V.contMDiff W.contMDiff,
    nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g X.contMDiff V.contMDiff W'.contMDiff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hcc : nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
        (smoothOrthoFrame (I := I) g x i) (fun b => V b) (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b)
        (smoothOrthoFrame (I := I) g x i) (fun b => V b) (fun b => W' b) x :=
    nablaCurvSec_eq_of_acted_eq (g := g)
      X (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) V W W' x hWW'
  exact congrArg (fun t => g.inner x t (smoothOrthoFrame (I := I) g x i x)) hcc

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma nablaRicci_eq_of_V_eq_raw
    (g : SmoothRiemannianMetric I M)
    (X V V' W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hVV' : (V : Π b : M, TangentSpace I b) x = V' x) :
    nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x =
      nablaRicci (I := I) g (fun b => X b) (fun b => V' b) (fun b => W b) x := by
  classical
  rw [nablaRicci_symm (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x,
    nablaRicci_symm (I := I) g (fun b => X b) (fun b => V' b) (fun b => W b) x]
  exact nablaRicci_eq_of_W_eq_raw (g := g) X W V V' x hVV'

omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma nablaRicci_eq_of_VW_eq
    (g : SmoothRiemannianMetric I M)
    (X V V₀ W W₀ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hVV₀ : (V : Π b : M, TangentSpace I b) x = V₀ x)
    (hWW₀ : (W : Π b : M, TangentSpace I b) x = W₀ x) :
    nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x =
      nablaRicci (I := I) g (fun b => X b) (fun b => V₀ b) (fun b => W₀ b) x := by
  classical
  rw [nablaRicci_eq_of_V_eq_raw (g := g) X V V₀ W x hVV₀,
    nablaRicci_eq_of_W_eq_raw (g := g) X V₀ W W₀ x hWW₀]

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma nablaRicci_add_left_raw
    (g : SmoothRiemannianMetric I M)
    (X V V' W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaRicci (I := I) g (fun b => X b) (fun b => (V + V') b) (fun b => W b) x =
      nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x +
        nablaRicci (I := I) g (fun b => X b) (fun b => V' b) (fun b => W b) x := by
  classical
  rw [nablaRicci_symm (I := I) g (fun b => X b) (fun b => (V + V') b) (fun b => W b) x,
    nablaRicci_symm (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x,
    nablaRicci_symm (I := I) g (fun b => X b) (fun b => V' b) (fun b => W b) x]
  exact nablaRicci_add_right_raw (g := g) X W V V' x

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma nablaRicci_smul_left_raw
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaRicci (I := I) g (fun b => X b) (fun b => (c • V) b) (fun b => W b) x =
      c • nablaRicci (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x := by
  classical
  rw [nablaRicci_symm (I := I) g (fun b => X b) (fun b => (c • V) b) (fun b => W b) x,
    nablaRicci_symm (I := I) g (fun b => X b) (fun b => V b) (fun b => W b) x]
  exact nablaRicci_smul_right_raw (g := g) c X W V x

private noncomputable abbrev extSec (x : M) (v : TangentSpace I x) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent_contMDiff (I := I) x v)

omit [I.Boundaryless] [SigmaCompactSpace M] in
private lemma nablaRicciBilinAux_add_left
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v v' w : TangentSpace I x) :
    nablaRicci (I := I) g X
        (fun b => smoothExtensionTangent (I := I) x (v + v') b)
        (fun b => smoothExtensionTangent (I := I) x w b) x =
      nablaRicci (I := I) g X (fun b => smoothExtensionTangent (I := I) x v b)
          (fun b => smoothExtensionTangent (I := I) x w b) x +
        nablaRicci (I := I) g X (fun b => smoothExtensionTangent (I := I) x v' b)
          (fun b => smoothExtensionTangent (I := I) x w b) x := by
  have hdet := nablaRicci_eq_of_V_eq_raw (g := g) X (extSec (I := I) x (v + v'))
    (extSec (I := I) x v + extSec (I := I) x v') (extSec (I := I) x w) x (by
      simp only [extSec, ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add, Pi.add_apply,
        smoothExtensionTangent_eq])
  have hadd := nablaRicci_add_left_raw (g := g) X (extSec (I := I) x v) (extSec (I := I) x v')
    (extSec (I := I) x w) x
  exact hdet.trans hadd

omit [I.Boundaryless] [SigmaCompactSpace M] in
private lemma nablaRicciBilinAux_smul_left
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (c : ℝ) (v w : TangentSpace I x) :
    nablaRicci (I := I) g X
        (fun b => smoothExtensionTangent (I := I) x (c • v) b)
        (fun b => smoothExtensionTangent (I := I) x w b) x =
      c • nablaRicci (I := I) g X (fun b => smoothExtensionTangent (I := I) x v b)
          (fun b => smoothExtensionTangent (I := I) x w b) x := by
  have hdet := nablaRicci_eq_of_V_eq_raw (g := g) X (extSec (I := I) x (c • v))
    (c • extSec (I := I) x v) (extSec (I := I) x w) x (by
      simp only [extSec, ContMDiffSection.coeFn_mk, ContMDiffSection.coe_smul, Pi.smul_apply,
        smoothExtensionTangent_eq])
  exact hdet.trans (nablaRicci_smul_left_raw (g := g) c X (extSec (I := I) x v)
    (extSec (I := I) x w) x)

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma nablaRicciBilinAux_add_right
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v w w' : TangentSpace I x) :
    nablaRicci (I := I) g X
        (fun b => smoothExtensionTangent (I := I) x v b)
        (fun b => smoothExtensionTangent (I := I) x (w + w') b) x =
      nablaRicci (I := I) g X (fun b => smoothExtensionTangent (I := I) x v b)
          (fun b => smoothExtensionTangent (I := I) x w b) x +
        nablaRicci (I := I) g X (fun b => smoothExtensionTangent (I := I) x v b)
          (fun b => smoothExtensionTangent (I := I) x w' b) x := by
  have hdet := nablaRicci_eq_of_W_eq_raw (g := g) X (extSec (I := I) x v)
    (extSec (I := I) x (w + w')) (extSec (I := I) x w + extSec (I := I) x w') x (by
      simp only [extSec, ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add, Pi.add_apply,
        smoothExtensionTangent_eq])
  have hadd := nablaRicci_add_right_raw (g := g) X (extSec (I := I) x v) (extSec (I := I) x w)
    (extSec (I := I) x w') x
  exact hdet.trans hadd

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma nablaRicciBilinAux_smul_right
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (c : ℝ) (v w : TangentSpace I x) :
    nablaRicci (I := I) g X
        (fun b => smoothExtensionTangent (I := I) x v b)
        (fun b => smoothExtensionTangent (I := I) x (c • w) b) x =
      c • nablaRicci (I := I) g X (fun b => smoothExtensionTangent (I := I) x v b)
          (fun b => smoothExtensionTangent (I := I) x w b) x := by
  have hdet := nablaRicci_eq_of_W_eq_raw (g := g) X (extSec (I := I) x v)
    (extSec (I := I) x (c • w)) (c • extSec (I := I) x w) x (by
      simp only [extSec, ContMDiffSection.coeFn_mk, ContMDiffSection.coe_smul, Pi.smul_apply,
        smoothExtensionTangent_eq])
  exact hdet.trans (nablaRicci_smul_right_raw (g := g) c X (extSec (I := I) x v)
    (extSec (I := I) x w) x)

noncomputable def nablaRicciBilin
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun v w => nablaRicci (I := I) g X
      (fun b => smoothExtensionTangent (I := I) x v b)
      (fun b => smoothExtensionTangent (I := I) x w b) x)
    (fun v v' w => nablaRicciBilinAux_add_left (I := I) g X x v v' w)
    (fun c v w => nablaRicciBilinAux_smul_left (I := I) g X x c v w)
    (fun v w w' => nablaRicciBilinAux_add_right (I := I) g X x v w w')
    (fun c v w => nablaRicciBilinAux_smul_right (I := I) g X x c v w)

noncomputable def nablaRicciEndo
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (((metricFlatMap (I := I) g x).symm.toLinearMap).comp (nablaRicciBilin (I := I) g X x))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma inner_nablaRicciEndo
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v w : TangentSpace I x) :
    g.inner x (nablaRicciEndo (I := I) g X x v) w = nablaRicciBilin (I := I) g X x v w := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  change g.inner x (metricSharp (I := I) g x (nablaRicciBilin (I := I) g X x v)) w = _
  exact inner_metricSharp (I := I) g x (nablaRicciBilin (I := I) g X x v) w

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma inner_nablaRicciEndo_smooth
    (g : SmoothRiemannianMetric I M)
    (X V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    g.inner x (nablaRicciEndo (I := I) g X x (V x)) (W x) = nablaRicci (I := I) g X V W x := by
  rw [inner_nablaRicciEndo]
  change nablaRicci (I := I) g X
      (fun b => smoothExtensionTangent (I := I) x (V x) b)
      (fun b => smoothExtensionTangent (I := I) x (W x) b) x = nablaRicci (I := I) g X V W x
  exact nablaRicci_eq_of_VW_eq (g := g) X
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (V x))
      (smoothExtensionTangent_contMDiff (I := I) x (V x))) V
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (W x))
      (smoothExtensionTangent_contMDiff (I := I) x (W x))) W x
    (smoothExtensionTangent_eq (I := I) x (V x)) (smoothExtensionTangent_eq (I := I) x (W x))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorInnerPointwise_slotSubst_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TangentSpace I x →L[ℝ] TangentSpace I x)
    (A D : Tensor0SSpace s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (∑ k : Fin s,
          tensor0SToTensorRS (I := I) (M := M) x
            (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k T) A)))
        (TensorRSSpace.toModel (tensor0SToTensorRS (I := I) (M := M) x D)) =
      ∑ k : Fin s,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (tensor0SToTensorRS (I := I) (M := M) x
              (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k T) A)))
          (TensorRSSpace.toModel (tensor0SToTensorRS (I := I) (M := M) x D)) := by
  classical

  have hsum : TensorRSSpace.toModel (∑ k : Fin s,
        tensor0SToTensorRS (I := I) (M := M) x
          (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k T) A)) =
      ∑ k : Fin s, TensorRSSpace.toModel (E := E) (I := I) (M := M) (r := 0) (s := s)
        (x := x) (tensor0SToTensorRS (I := I) (M := M) x
          (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k T) A)) := by
    have hL : TensorRSSpace.toModel (∑ k : Fin s,
          tensor0SToTensorRS (I := I) (M := M) x
            (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k T) A)) =
        (TensorRSSpace.toModelL (I := I) (M := M) 0 s x) (∑ k : Fin s,
          tensor0SToTensorRS (I := I) (M := M) x
            (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k T) A)) :=
      (TensorRSSpace.toModelL_apply _).symm
    rw [hL, map_sum]
    exact Finset.sum_congr rfl (fun k _ => TensorRSSpace.toModelL_apply _)
  rw [hsum]

  let φ : TensorRSModel 0 s ℝ E →+ ℝ :=
    { toFun := fun m => tensorInnerPointwise (I := I) (M := M) g 0 s x m
        (TensorRSSpace.toModel (tensor0SToTensorRS (I := I) (M := M) x D))
      map_zero' := tensorInnerPointwise_zero_left (I := I) (M := M) g 0 s x _
      map_add' := fun a b => tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x a b _ }
  exact map_sum φ _ Finset.univ

end Connection

end Integral

end DifferentialGeometry
