import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]


omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ F] in
theorem covApply_outer_swap_eq_riemannSec
    (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, V b) (x : M) :
    cov.toFun (covApply cov Y T) x (X x) =
      cov.toFun (covApply cov X T) x (Y x)
        + cov.toFun T x (VectorField.mlieBracket I X Y x)
        + riemannSec cov X Y T x := by
  rw [riemannSec_def]
  abel

end General

section IteratedSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]


omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ F] in
theorem covApply_contMDiff
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {T : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X T)) := by
  rw [← contMDiffOn_univ]
  refine covApply_contMDiffOn (cov := cov) hX ?_
  rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
  exact hT

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ F] in
theorem covApply_covApply_contMDiff
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X (covApply cov Y T))) :=
  covApply_contMDiff (cov := cov) hX (covApply_contMDiff (cov := cov) hY hT)


omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem mlieBracket_contMDiff
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I X Y)) := by
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    have h_eq : (minSmoothness ℝ 2 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
    rw [h_eq]; infer_instance
  intro b
  have hn_le : minSmoothness ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    have h_eq : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) = (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      rw [ENat.coe_top_add_one]
    rw [h_eq]
  have hX_inf : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (T% X) b := hX b
  have hY_inf : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (T% Y) b := hY b
  haveI : IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) M := by
    have h_eq : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) = (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      rw [ENat.coe_top_add_one]
    rw [h_eq]; infer_instance
  exact hX_inf.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY_inf hn_le

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ F] in
theorem riemannSec_contMDiff
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (fun b : M => riemannSec cov X Y T b)) := by
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I X Y)) :=
    mlieBracket_contMDiff (I := I) hX hY
  have h1 := covApply_covApply_contMDiff (cov := cov) hX hY hT
  have h2 := covApply_covApply_contMDiff (cov := cov) hY hX hT
  have h3 := covApply_contMDiff (cov := cov) hbr hT
  have hresult : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (T% (covApply cov X (covApply cov Y T) -
        covApply cov Y (covApply cov X T) -
        covApply cov (VectorField.mlieBracket I X Y) T)) :=
    (h1.sub_section h2).sub_section h3
  refine hresult.congr ?_
  intro b
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ F] in
theorem covApply_covApply_eq_section
    (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, V b) :
    covApply cov X (covApply cov Y T) =
      covApply cov Y (covApply cov X T)
        + covApply cov (VectorField.mlieBracket I X Y) T
        + (fun b : M => riemannSec cov X Y T b) := by
  funext b
  simp only [Pi.add_apply, covApply_apply]
  exact covApply_outer_swap_eq_riemannSec cov X Y T b

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ F] in
theorem secondCovDeriv_swap_outer
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {B W : Π b : M, TangentSpace I b} {T : Π b : M, V b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% T)) :
    cov.toFun (covApply cov B (covApply cov W T)) x (B x) =
      cov.toFun (covApply cov B (covApply cov B T)) x (W x)
        + cov.toFun (covApply cov B T) x (VectorField.mlieBracket I B W x)
        + riemannSec cov B W (covApply cov B T) x
        + cov.toFun (covApply cov (VectorField.mlieBracket I B W) T) x (B x)
        + cov.toFun (fun b : M => riemannSec cov B W T b) x (B x) := by
  classical
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I B W)) :=
    mlieBracket_contMDiff (I := I) hB hW
  have hWBT : MDiffAt (T% (covApply cov W (covApply cov B T))) x :=
    (covApply_covApply_contMDiff (cov := cov) hW hB hT x).mdifferentiableAt (by simp)
  have hbrT : MDiffAt (T% (covApply cov (VectorField.mlieBracket I B W) T)) x :=
    (covApply_contMDiff (cov := cov) hbr hT x).mdifferentiableAt (by simp)
  have hRsec : MDiffAt (T% (fun b : M => riemannSec cov B W T b)) x :=
    (riemannSec_contMDiff (cov := cov) hB hW hT x).mdifferentiableAt (by simp)
  have hinner : covApply cov B (covApply cov W T) =
      covApply cov W (covApply cov B T)
        + covApply cov (VectorField.mlieBracket I B W) T
        + (fun b : M => riemannSec cov B W T b) :=
    covApply_covApply_eq_section cov B W T
  have hsum12 : MDiffAt (T% (covApply cov W (covApply cov B T)
      + covApply cov (VectorField.mlieBracket I B W) T)) x :=
    (((covApply_covApply_contMDiff (cov := cov) hW hB hT).add_section
        (covApply_contMDiff (cov := cov) hbr hT)) x).mdifferentiableAt (by simp)
  have hadd_full : cov.toFun (covApply cov B (covApply cov W T)) x =
      cov.toFun (covApply cov W (covApply cov B T)) x
        + cov.toFun (covApply cov (VectorField.mlieBracket I B W) T) x
        + cov.toFun (fun b : M => riemannSec cov B W T b) x := by
    rw [hinner]
    rw [cov.isCovariantDerivativeOnUniv.add hsum12 hRsec]
    rw [cov.isCovariantDerivativeOnUniv.add hWBT hbrT]
  have hat := congrFun (congrArg DFunLike.coe hadd_full) (B x)
  simp only [ContinuousLinearMap.add_apply] at hat
  have hWBatom :
      cov.toFun (covApply cov W (covApply cov B T)) x (B x) =
        cov.toFun (covApply cov B (covApply cov B T)) x (W x)
          + cov.toFun (covApply cov B T) x (VectorField.mlieBracket I B W x)
          + riemannSec cov B W (covApply cov B T) x :=
    covApply_outer_swap_eq_riemannSec cov B W (covApply cov B T) x
  rw [hat, hWBatom]

end IteratedSmooth

section TensorBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def tensorThirdOrderCurvatureDefect
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
        (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W x)
      + riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
          (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W) T) x
          (smoothOrthoFrame (I := I) g x i x)
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma Tensor3rdCurv_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorThirdOrderCurvatureDefect (I := I) g r s W T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W x)
          + riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
              (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
          + (tensorCov (I := I) g r s).toFun
              (covApply (tensorCov (I := I) g r s)
                (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W) T) x
              (smoothOrthoFrame (I := I) g x i x)
          + (tensorCov (I := I) g r s).toFun
              (fun b : M => riemannSec (tensorCov (I := I) g r s)
                (smoothOrthoFrame (I := I) g x i) W T b) x
              (smoothOrthoFrame (I := I) g x i x)) := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covApplyRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (tensorCov (I := I) g r s) X T y)) := by
  classical
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (tensorCov (I := I) g r s) X T y)) Set.univ :=
    covApply_contMDiffOn (cov := tensorCov (I := I) g r s) hX hT_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

theorem frame_trace_thirdCovDeriv_swap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g r s) W T)) x
          (smoothOrthoFrame (I := I) g x i x) =
      ∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T)) x
            (W x)
        + tensorThirdOrderCurvatureDefect (I := I) g r s W T x := by
  classical
  rw [Tensor3rdCurv_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hstep := secondCovDeriv_swap_outer (cov := tensorCov (I := I) g r s)
    (B := smoothOrthoFrame (I := I) g x i) (W := W) (T := T) (x := x) hB hW hT
  rw [hstep]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannSec_eq_riemannOp_tensorCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X W : Π b : M, TangentSpace I b} {Z : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (Z b))) :
    riemannSec (tensorCov (I := I) g r s) X W Z x =
      riemannOp (tensorCov (I := I) g r s) x (X x) (W x) (Z x) :=
  riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hW hZ

end TensorBundle

end Connection
end Integral
end DifferentialGeometry
