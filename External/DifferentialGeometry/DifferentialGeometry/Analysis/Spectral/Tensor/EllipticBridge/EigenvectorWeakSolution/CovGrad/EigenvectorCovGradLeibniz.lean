import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.ChartWeakIdentity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y =
      chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  rw [tensorChartComponent_def (I := I) (M := M) g r s S α Idx Jdx]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx =ᶠ[nhds y]
      (fun z : EuclN E =>
        chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M)
              g r s S α Idx Jdx) z) := by
  classical
  refine Filter.eventually_of_mem
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy) ?_
  intro z hz
  exact tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s S α Idx Jdx hz

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartPushedRaw_chartAtlasPOU_contDiffOn (α : M) :
    ContDiffOn ℝ ∞
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hPOU_global : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hPOU_src : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
      ((chartAt H α).source) :=
    hPOU_global.contMDiffOn
  exact chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hPOU_src

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem differentiableAt_chartPushedRaw_chartAtlasPOU
    (α : M) {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcontDiffAt : ContDiffAt ℝ ∞
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y :=
    (chartPushedRaw_chartAtlasPOU_contDiffOn (I := I) (M := M) α y hy).contDiffAt
      (hopen.mem_nhds hy)
  exact hcontDiffAt.differentiableAt (by decide)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem differentiableAt_chartPushedRaw_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcontDiffAt : ContDiffAt ℝ ∞
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y :=
    (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s S α Idx Jdx y hy).contDiffAt (hopen.mem_nhds hy)
  exact hcontDiffAt.differentiableAt (by decide)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem chartPushedRaw_pou_mul_euclidPartial_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y
        * euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α Idx Jdx)) y =
      euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y
        - euclidPartial (E := E) k
              (chartPushedRaw I α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y
            * chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S α Idx Jdx) y := by
  classical
  set P : EuclN E → ℝ :=
    chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hP_def
  set R : EuclN E → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) with hR_def
  have h_component_deriv :
      euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y =
        euclidPartial (E := E) k (fun z : EuclN E => P z * R z) y := by
    rw [euclidPartial_def, euclidPartial_def]
    congr 1
    exact Filter.EventuallyEq.fderiv_eq
      (tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw_raw
        (I := I) (M := M) g r s S α Idx Jdx hy)
  have hP_diff : DifferentiableAt ℝ P y :=
    differentiableAt_chartPushedRaw_chartAtlasPOU (I := I) (M := M) α hy
  have hR_diff : DifferentiableAt ℝ R y :=
    differentiableAt_chartPushedRaw_tensorChartComponentRaw
      (I := I) (M := M) g r s S α Idx Jdx hy
  have h_leibniz :
      euclidPartial (E := E) k (fun z : EuclN E => P z * R z) y =
        euclidPartial (E := E) k P y * R y +
          P y * euclidPartial (E := E) k R y :=
    euclidPartial_mul (E := E) k hP_diff hR_diff
  rw [h_component_deriv, h_leibniz]
  ring

example (g : SmoothRiemannianMetric I M) (α : M)
    (S : SmoothCcTensor g 1 2)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y
        * euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g 1 2 S α Idx Jdx)) y =
      euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g 1 2 S α Idx Jdx) y
        - euclidPartial (E := E) k
              (chartPushedRaw I α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y
            * chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M)
                  g 1 2 S α Idx Jdx) y :=
  chartPushedRaw_pou_mul_euclidPartial_eq
    (I := I) (M := M) g 1 2 S α Idx Jdx k hy

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
