import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin
import DifferentialGeometry.Geometry.Boundary.EuclideanHalfSpaceInstance
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

omit [InnerProductSpace ℝ E] in
private lemma partialDerivWithin_scalarOnE_contMDiffOn_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target := by
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  have hbase : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hpartial : ContDiffOn ℝ ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := j) hbase hUD
  exact hpartial.contMDiffOn

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma extChartAt_contMDiffOn_chart_source (α : M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E) (chartAt H α).source :=
  contMDiffOn_extChartAt

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma chart_source_subset_preimage_target (α : M) :
    (chartAt H α).source ⊆
      (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target := by
  intro x hx
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  exact (extChartAt I α).map_source hxsrc

omit [InnerProductSpace ℝ E] in
lemma gradChartCoeffWithin_contMDiffOn_full
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeffWithin (I := I) g α f i)
      (chartAt H α).source := by
  classical
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  · have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f))
        (extChartAt I α).target :=
      partialDerivWithin_scalarOnE_contMDiffOn_target (I := I) α hf j
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        (chartAt H α).source :=
      extChartAt_contMDiffOn_chart_source (I := I) α
    have hsubset : (chartAt H α).source ⊆
        (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target :=
      chart_source_subset_preimage_target (I := I) α
    exact hpartialM.comp hchart hsubset

omit [InnerProductSpace ℝ E] in
lemma gradChartLocalWithin_contMDiffOn_total_full
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocalWithin (I := I) g α f x))
      (chartAt H α).source := by
  classical
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞
      (gradChartCoeffWithin (I := I) g α f i)
      (chartAt H α).source :=
    fun i => gradChartCoeffWithin_contMDiffOn_full (I := I) g α hf i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartBasisVecFiber (I := I) α i x))
      (chartAt H α).source := by
    intro i
    refine (chartBasisVec_contMDiffOn (I := I) α i).mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (gradChartCoeffWithin (I := I) g α f i x •
          chartBasisVecFiber (I := I) α i x))
      (chartAt H α).source := by
    intro i
    exact (hcoeff i).smul_section (hbasis i)
  exact ContMDiffOn.sum_section (fun i _ => hsmul i)

omit [InnerProductSpace ℝ E] in
private lemma gradFun_eq_gradChartLocalWithin_on_chart_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∀ y ∈ (chartAt H α).source,
      gradFun (I := I) g f y = gradChartLocalWithin (I := I) g α f y := by
  intro y hy
  exact (gradChartLocalWithin_eq_gradFun (I := I) g α hf hy).symm

omit [InnerProductSpace ℝ E] in
lemma gradFun_contMDiffOn_chart_source_full
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
      (chartAt H α).source := by
  have hsmooth :=
    gradChartLocalWithin_contMDiffOn_total_full (I := I) g α hf
  have hcongr := gradFun_eq_gradChartLocalWithin_on_chart_source
    (I := I) g α hf
  refine hsmooth.congr ?_
  intro y hy
  have h := hcongr y hy
  change TotalSpace.mk' E y (gradFun (I := I) g f y) =
    TotalSpace.mk' E y (gradChartLocalWithin (I := I) g α f y)
  rw [h]

omit [InnerProductSpace ℝ E] in
theorem gradFun_contMDiff_total_full
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) := by
  rw [← contMDiffOn_univ]
  refine contMDiffOn_of_locally_contMDiffOn ?_
  intro x _
  refine ⟨(chartAt H x).source, (chartAt H x).open_source,
    mem_chart_source H x, ?_⟩
  have hsm := gradFun_contMDiffOn_chart_source_full
    (I := I) g x hf
  have hset_eq : univ ∩ (chartAt H x).source = (chartAt H x).source :=
    Set.univ_inter _
  rw [hset_eq]
  exact hsm

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure

theorem grad_g_smooth_section_full
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersEuclideanHalfSpace n).tangent ∞
      (fun x : M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)) :=
  gradFun_contMDiff_total_full
    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g hf

def grad_g_full_section
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f) :
    Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
      EuclideanSpace ℝ (Fin n),
      (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x,
    grad_g_smooth_section_full (M := M) (n := n) g hf⟩

@[simp] lemma grad_g_full_section_apply
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) :
    (grad_g_full_section (M := M) (n := n) g hf :
      Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯) x =
      gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x := rfl

@[simp] lemma grad_g_full_section_coe
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) :
    (grad_g_full_section (M := M) (n := n) g hf :
      Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯) x =
      grad_g_with_boundary (I := modelWithCornersEuclideanHalfSpace n) g f x := rfl

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

end
