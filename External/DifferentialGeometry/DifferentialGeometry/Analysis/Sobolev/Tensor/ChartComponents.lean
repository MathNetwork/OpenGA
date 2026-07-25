import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def tensorChartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartComp_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComp_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm (toEuclidean.symm y)) := by
  rw [tensorChartComp_def, tensorChartComponent_def]
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComp_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  rw [tensorChartComp_def, tensorChartComponent_def]
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S₁ α Idx Jdx +
        tensorChartComp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  simp only [tensorChartComp_def]
  exact tensorChartComponent_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := by
  simp only [tensorChartComp_def]
  exact tensorChartComponent_smul (I := I) (M := M) g r s c S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] theorem tensorChartComp_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) α Idx Jdx =
      (fun _ => (0 : ℝ)) := by
  have h := tensorChartComp_smul (I := I) (M := M) g r s
    (0 : ℝ) (0 : SmoothCcTensor g r s) α Idx Jdx
  rw [zero_smul] at h
  funext y
  have hy := congrFun h y
  simpa using hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_neg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (-S) α Idx Jdx =
      -tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := by
  have h := tensorChartComp_smul (I := I) (M := M) g r s (-1 : ℝ) S α Idx Jdx
  rw [neg_one_smul] at h
  rw [h, neg_one_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S₁ α Idx Jdx -
        tensorChartComp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  rw [sub_eq_add_neg, tensorChartComp_add, tensorChartComp_neg, ← sub_eq_add_neg]

noncomputable def tensorChartCompₗ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    SmoothCcTensor g r s →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) where
  toFun S := tensorChartComp (I := I) (M := M) g r s S α Idx Jdx
  map_add' S₁ S₂ := tensorChartComp_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx
  map_smul' c S := tensorChartComp_smul (I := I) (M := M) g r s c S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartCompₗ_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (S : SmoothCcTensor g r s) :
    tensorChartCompₗ (I := I) (M := M) g r s α Idx Jdx S =
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (𝓘(ℝ, ℝ)) ∞
      (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [tensorChartComp_def]
  exact tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  have h := tensorChartComp_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  rwa [contMDiff_iff_contDiff] at h

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (tensorChartComp_contDiff (I := I) (M := M) g r s S α Idx Jdx).contDiffOn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComp_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [tensorChartComp_def]
  exact tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) :=
  (tensorChartComp_contDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

noncomputable def tensorChartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    TensorRSModel r s ℝ E :=
  tensorChartPushedRawModel (I := I) (M := M) g r s S α y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartPushed_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s S α y =
      tensorChartPushedRawModel (I := I) (M := M) g r s S α y := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartPushed_eq_sum_tensorChartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s S α y =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y •
            tensorChartBasisElement (E := E) r s Idx Jdx := by
  simp only [tensorChartPushed_def, tensorChartComp_def]
  exact chartPushedRaw_eq_sum_tensorChartComponent
    (I := I) (M := M) g r s S α y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (h : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => 0)) :
    tensorChartPushed (I := I) (M := M) g r s S α = (fun _ => 0) := by
  funext y
  rw [tensorChartPushed_eq_sum_tensorChartComp]
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [h Idx Jdx]
  rw [zero_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_eq_zero_of_section_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : SmoothCcTensor g r s} (hS : S = 0) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => 0) := by
  rw [hS]
  exact tensorChartComp_zero (I := I) (M := M) g r s α Idx Jdx

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem card_tensorChartComp_index (r s : ℕ) :
    Fintype.card
        ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) =
      (Module.finrank ℝ E) ^ (r + s) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_add]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
