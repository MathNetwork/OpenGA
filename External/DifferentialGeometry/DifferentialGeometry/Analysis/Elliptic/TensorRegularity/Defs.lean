import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents


noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def euclidPartial (i : Fin (Module.finrank ℝ E))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  fderiv ℝ u y (EuclideanSpace.single i 1)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma euclidPartial_def (i : Fin (Module.finrank ℝ E))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    euclidPartial (E := E) i u y = fderiv ℝ u y (EuclideanSpace.single i 1) := rfl

def chartInvGramEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartInvGramOnE (I := I) g α k l (toEuclidean.symm y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma chartInvGramEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartInvGramEuclid (I := I) g α k l y =
      chartInvGramOnE (I := I) g α k l (toEuclidean.symm y) := rfl

def chartChristoffelEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartChristoffel (I := I) g α k l m (toEuclidean.symm y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma chartChristoffelEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartChristoffelEuclid (I := I) g α k l m y =
      chartChristoffel (I := I) g α k l m (toEuclidean.symm y) := rfl

def weightedInvGramEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartDensityOnE (I := I) g α (toEuclidean.symm y) *
      chartInvGramEuclid (I := I) g α k l y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma weightedInvGramEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    weightedInvGramEuclid (I := I) g α k l y =
      chartDensityOnE (I := I) g α (toEuclidean.symm y) *
        chartInvGramEuclid (I := I) g α k l y := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma toEuclidean_symm_mem_extChartAt_target
    {α : M} {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (toEuclidean.symm y : E) ∈ (extChartAt I α).target := by
  classical
  obtain ⟨z, hz_mem, hz_eq⟩ := hy
  have hzy : (toEuclidean.symm y : E) = z := by
    rw [← hz_eq]
    exact toEuclidean.symm_apply_apply z
  rw [hzy]
  exact hz_mem

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma extChartAt_target_eq_interior (α : M) :
    (extChartAt I α).target = interior ((extChartAt I α).target : Set E) :=
  (isOpen_extChartAt_target (I := I) α).interior_eq.symm

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartInvGramEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramEuclid (I := I) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α k l
  have hcomp :
      ContDiffOn ℝ ∞
        (chartInvGramOnE (I := I) g α k l ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  exact hcomp

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffelEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffelEuclid (I := I) g α k l m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE_int : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α k l m)
      (interior ((extChartAt I α).target : Set E)) :=
    chartChristoffel_contDiffOn_interior (I := I) g α k l m
  have hE : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α k l m)
      (extChartAt I α).target := by
    rw [extChartAt_target_eq_interior (I := I) α]
    exact hE_int
  have hcomp :
      ContDiffOn ℝ ∞
        (chartChristoffel (I := I) g α k l m ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  exact hcomp

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem weightedInvGramEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramEuclid (I := I) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hdensity : ContDiffOn ℝ ∞
      (chartDensityOnE (I := I) g α ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine (chartDensityOnE_contDiffOn (I := I) g α).comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  rw [show weightedInvGramEuclid (I := I) g α k l =
      fun y => (chartDensityOnE (I := I) g α ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E)) y *
        chartInvGramEuclid (I := I) g α k l y from rfl]
  exact hdensity.mul (chartInvGramEuclid_contDiffOn (I := I) (M := M) g α k l)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_contDiff
    {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) i u) := by
  have hfd : ContDiff ℝ ∞ (fun y => fderiv ℝ u y) :=
    hu.fderiv_right (m := ∞) (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])
  have hcomp : euclidPartial (E := E) i u =
      (fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i 1)) ∘ (fun y => fderiv ℝ u y) := by
    funext y; rfl
  rw [hcomp]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single i 1)).contDiff.comp hfd

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_euclidPartial_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) i
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)) :=
  euclidPartial_contDiff (E := E)
    (tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx) i

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_euclidPartial_partial_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k
      (euclidPartial (E := E) l
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx))) :=
  euclidPartial_contDiff (E := E)
    (tensorChartComp_euclidPartial_contDiff (I := I) (M := M) g r s T α Idx Jdx l) k

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComp_euclidPartial_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (euclidPartial (E := E) m
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)) := by
  classical
  have hcs : HasCompactSupport
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
  have hfd : HasCompactSupport (fun y => fderiv ℝ
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) :=
    hcs.fderiv ℝ
  have hsubset : (Function.support (euclidPartial (E := E) m
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx))) ⊆
      tsupport (fun y => fderiv ℝ
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) := by
    intro y hy
    apply subset_tsupport _
    rw [Function.mem_support] at hy ⊢
    intro hcontra
    apply hy
    rw [euclidPartial_def, hcontra]
    rfl
  exact HasCompactSupport.of_support_subset_isCompact hfd hsubset

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma hasCompactSupport_finset_sum
    {ι : Type*} {β : Type*} [TopologicalSpace β]
    [AddCommMonoid β] [ContinuousAdd β]
    {s : Finset ι}
    {f : ι → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → β}
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a t ha ih =>
    have hsum_eq : (fun y => ∑ i ∈ insert a t, f i y) =
        (fun y => f a y + ∑ i ∈ t, f i y) := by
      funext y
      rw [Finset.sum_insert ha]
    rw [hsum_eq]
    refine HasCompactSupport.add ?_ ?_
    · exact hf a (Finset.mem_insert_self a t)
    · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
