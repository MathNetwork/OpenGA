import DifferentialGeometry.Geometry.Curvature.Order2Defect.FrameCurvatureCore
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.FrozenFrameTrace
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSCovariantDerivativeCongrLocally


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covApply_covApply_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s) B T) y (B y))) := by
  have hInner := covApplyRS_contMDiff (I := I) g r s hT hB
  have hOuter := covApplyRS_contMDiff (I := I) g r s hInner hB
  exact hOuter

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covApply_christoffel_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((tensorCov (I := I) g r s).toFun T y
          ((LeviCivita (I := I) g).toFun B y (B y)))) := by
  have hChristoffel : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        ((LeviCivita (I := I) g).toFun B y (B y))) := by
    have hBplus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% B) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact hB
    have hOn := covApply_contMDiffOn (cov := LeviCivita (I := I) g) hB hBplus
    intro b
    exact hOn.contMDiffAt (Filter.univ_mem)
  exact covApplyRS_contMDiff (I := I) g r s hT hChristoffel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorSecondCovDeriv_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (tensorSecondCovDeriv (I := I) g r s B B T y)) := by
  have hFirst := covApply_covApply_section_contMDiff (I := I) g r s hT hB
  have hSecond := covApply_christoffel_section_contMDiff (I := I) g r s hT hB
  have hSub := hFirst.sub_section hSecond
  have hpt : (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (tensorSecondCovDeriv (I := I) g r s B B T y)) =
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) B T) y (B y) -
          (tensorCov (I := I) g r s).toFun T y
            ((LeviCivita (I := I) g).toFun B y (B y)))) := by
    funext y; rw [tensorSecondCovDeriv_def]
  rw [hpt]
  exact hSub

omit [CompactSpace M] [I.Boundaryless] in
theorem frozenFrameTrace_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (frozenFrameTrace (I := I) g r s T x y)) := by
  classical
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)) :=
    fun i => tensorSecondCovDeriv_section_contMDiff (I := I) g r s hT
      (smoothOrthoFrame_smooth (I := I) g x i)
  have hsum := ContMDiff.sum_section (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (t := fun i (y : M) =>
      tensorSecondCovDeriv (I := I) g r s
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)
    (fun i _ => hsummand i)
  have hpt : (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (frozenFrameTrace (I := I) g r s T x y)) =
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (∑ i : Fin (Module.finrank ℝ E),
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)) := by
    funext y; rw [frozenFrameTrace_def]
  rw [hpt]
  exact hsum

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCov_toFun_finset_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {ι : Type*} (t : Finset ι) (σ : ι → Π b : M, TensorRSSpace r s I b) {x : M}
    (hσ : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (σ i y)) x) :
    (tensorCov (I := I) g r s).toFun (fun y : M => ∑ i ∈ t, σ i y) x =
      ∑ i ∈ t, (tensorCov (I := I) g r s).toFun (σ i) x := by
  classical
  set cov := tensorCov (I := I) g r s with hcov_def
  induction t using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    rw [show (fun y : M => ∑ _i ∈ (∅ : Finset ι), σ _i y) =
        (0 : Π b : M, TensorRSSpace r s I b) from by
      funext y; rw [Finset.sum_empty]; rfl]
    exact cov.isCovariantDerivativeOnUniv.zero (x := x) (mem_univ x)
  | insert a t' ha ih =>
    have hpartial : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (∑ i ∈ t', σ i y)) x :=
      MDifferentiableAt.sum_section (s := t')
        (t := fun i (y : M) => σ i y) (fun i => hσ i)
    have hadd := cov.isCovariantDerivativeOnUniv.add
      (σ := (fun y => σ a y : Π b : M, TensorRSSpace r s I b))
      (σ' := (fun y => ∑ i ∈ t', σ i y : Π b : M, TensorRSSpace r s I b))
      (hσ a) hpartial (mem_univ x)
    have hsection : (fun y : M => ∑ i ∈ insert a t', σ i y) =
        ((fun y => σ a y : Π b : M, TensorRSSpace r s I b) +
          (fun y => ∑ i ∈ t', σ i y : Π b : M, TensorRSSpace r s I b)) := by
      funext y; rw [Finset.sum_insert ha]; rfl
    rw [hsection, hadd, Finset.sum_insert ha]
    rw [ih]

omit [CompactSpace M] [I.Boundaryless] in
theorem covDeriv_frozenFrameTrace_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) (v : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => frozenFrameTrace (I := I) g r s T x y) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x v := by
  classical
  have hfrozen : (fun y : M => frozenFrameTrace (I := I) g r s T x y) =
      (fun y : M => ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) := by
    funext y; rw [frozenFrameTrace_def]
  rw [hfrozen]
  have hσ : ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)) x :=
    fun i => (tensorSecondCovDeriv_section_contMDiff (I := I) g r s hT
      (smoothOrthoFrame_smooth (I := I) g x i)).mdifferentiable (by norm_num) x
  rw [tensorCov_toFun_finset_sum (I := I) g r s Finset.univ
    (fun i (y : M) => tensorSecondCovDeriv (I := I) g r s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) hσ]
  rw [ContinuousLinearMap.sum_apply]

omit [CompactSpace M] [I.Boundaryless] in
theorem covDeriv_rawConnLap_eq_frozenFrameTrace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) (v : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x v := by
  classical
  have hagree : ∀ᶠ y in 𝓝 x, rawTensorConnLap (I := I) g r s T y =
      frozenFrameTrace (I := I) g r s T x y :=
    rawTensorConnLap_eventuallyEq_frozenFrameTrace (I := I) g r s T hT x
  have hLap : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (rawTensorConnLap (I := I) g r s T y)) x :=
    (rawTensorConnLap_contMDiff (I := I) g r s T hT).mdifferentiable (by norm_num) x
  have hFrozen : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (frozenFrameTrace (I := I) g r s T x y)) x :=
    (frozenFrameTrace_section_contMDiff (I := I) g r s hT x).mdifferentiable (by norm_num) x
  have hcongr := tensorRSCovariantDerivative_congr_of_eventuallyEq (I := I) g r s
    (σ := fun y : M => rawTensorConnLap (I := I) g r s T y)
    (σ' := fun y : M => frozenFrameTrace (I := I) g r s T x y)
    hagree hLap hFrozen
  rw [show (tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x v =
      ((tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x) v from rfl]
  rw [hcongr]
  exact covDeriv_frozenFrameTrace_eq_sum (I := I) g r s hT x v

omit [CompactSpace M] [I.Boundaryless] in
theorem covDerivMap_rawConnLap_eq_frozenFrameTrace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.sum_apply]
  exact covDeriv_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x v

omit [CompactSpace M] [I.Boundaryless] in
theorem covGradBundleEquiv_covDeriv_rawConnLap_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    covGradBundleEquiv (I := I) (M := M) r s x
        ((tensorCov (I := I) g r s).toFun
          (fun y : M => rawTensorConnLap (I := I) g r s T y) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) r s x
          ((tensorCov (I := I) g r s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g r s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x) := by
  rw [covDerivMap_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x]
  exact map_sum (covGradBundleEquiv (I := I) (M := M) r s x) _ _

theorem covGrad_rawConnLap_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (covGrad (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) 0 2 x
          ((tensorCov (I := I) g 0 2).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g 0 2
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => T₀.toSection z) y) x) := by
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y (T₀.toSection y)) :=
    T₀.toSection.contMDiff
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x]
  rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toSection y) =
      (fun y : M => rawTensorConnLap (I := I) g 0 2 (fun z : M => T₀.toSection z) y) from by
    funext y; rw [rawTensorConnLapSmooth_toSection_apply]]
  exact covGradBundleEquiv_covDeriv_rawConnLap_eq_sum (I := I) g 0 2 hT x

theorem covGradRoughLapCurv_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 3
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 2 x
            ((tensorCov (I := I) g 0 2).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 2
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => T₀.toSection z) y) x)) := by
  classical
  rw [covGradRoughLapCurv_toSection_eq_sub (I := I) (M := M) g T₀ x]
  rw [rawTensorConnLap_gradTensor_toSection_eq_frame_trace (I := I) (M := M) g T₀ x]
  rw [covGrad_rawConnLap_toSection_eq_frame_sum (I := I) (M := M) g T₀ x]
  rw [← Finset.sum_sub_distrib]

end Connection
end Integral
end DifferentialGeometry

end
