import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Metric.ChartGram

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle
open TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def inverseMetricSharpFib (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α)
      map_add' := fun α β => by
        rw [map_add (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, metricSharp_def, map_add]
      map_smul' := fun c α => by
        rw [map_smul (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, map_smul]; rfl }

@[simp] lemma inverseMetricSharpFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    inverseMetricSharpFib (I := I) g x α =
      metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α) := by
  rw [inverseMetricSharpFib, LinearMap.coe_toContinuousLinearMap']; rfl

lemma inverseMetricSharpFib_inner (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g.inner x (inverseMetricSharpFib (I := I) g x α) w =
      cotangentToDualLinear (I := I) (x := x) α w := by
  rw [inverseMetricSharpFib_apply]
  exact inner_metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α) w

@[simp] lemma inverseMetricSharpFib_zero (g : SmoothRiemannianMetric I M) (x : M) :
    inverseMetricSharpFib (I := I) g x 0 = 0 := by
  rw [inverseMetricSharpFib_apply, map_zero]
  rw [metricSharp_def, map_zero]

lemma inverseMetricSharpFib_ne_zero_of_ne_zero (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    inverseMetricSharpFib (I := I) g x α ≠ 0 := by
  intro hzero
  apply hα

  have hdual : cotangentToDualLinear (I := I) (x := x) α = 0 := by
    ext w
    rw [← inverseMetricSharpFib_inner (I := I) g x α w, hzero]
    simp
  exact cotangentToDualLinear_injective (I := I) (x := x) (by rw [hdual, map_zero])

def cometricBilin (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : ℝ :=
  g.inner x (inverseMetricSharpFib (I := I) g x α) (inverseMetricSharpFib (I := I) g x β)

lemma cometricBilin_eq_inner_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      g.inner x (inverseMetricSharpFib (I := I) g x α)
        (inverseMetricSharpFib (I := I) g x β) := rfl

lemma cometricBilin_eq_dual_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      cotangentToDualLinear (I := I) (x := x) α (inverseMetricSharpFib (I := I) g x β) := by
  rw [cometricBilin_eq_inner_sharp]
  exact inverseMetricSharpFib_inner (I := I) g x α (inverseMetricSharpFib (I := I) g x β)

lemma cometricBilin_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β = cometricBilin (I := I) g x β α := by
  rw [cometricBilin_eq_inner_sharp, cometricBilin_eq_inner_sharp]
  exact g.symm x _ _

lemma cometricBilin_self_nonneg (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    0 ≤ cometricBilin (I := I) g x α α := by
  rw [cometricBilin_eq_inner_sharp]
  rcases eq_or_ne (inverseMetricSharpFib (I := I) g x α) 0 with h | h
  · rw [h]; simp
  · exact le_of_lt (g.pos x (inverseMetricSharpFib (I := I) g x α) h)

lemma cometricBilin_self_pos (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    0 < cometricBilin (I := I) g x α α := by
  rw [cometricBilin_eq_inner_sharp]
  exact g.pos x (inverseMetricSharpFib (I := I) g x α)
    (inverseMetricSharpFib_ne_zero_of_ne_zero (I := I) g x hα)

variable [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M] in

theorem cotangentSection_chartComponent_contMDiffOn
    (Y : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (Y b)
        (fun _ : Fin 1 => chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  intro x₀ hx₀
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_section_apply (n := 1) (T := fun b => Y b) (x₀ := x₀)
  · exact Y.contMDiff.contMDiffAt
  · intro i
    have hbase : (trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
      TangentBundle.trivializationAt_baseSet (I := I) γ
    have hx₀base : x₀ ∈ (trivializationAt E (TangentSpace I) γ).baseSet := by
      rw [hbase]; exact hx₀
    have hopen : IsOpen (trivializationAt E (TangentSpace I) γ).baseSet :=
      (trivializationAt E (TangentSpace I) γ).open_baseSet
    exact (chartBasisVec_contMDiffOn (I := I) γ j x₀ hx₀base).contMDiffAt
      (hopen.mem_nhds hx₀base)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in

omit [SigmaCompactSpace M] in
theorem inverseMetricSharpField_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x => inverseMetricSharpFib (I := I) g x)
  intro Y
  have hmain : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b
        (metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (Y b)))) := by
    apply metricSharp_contMDiff_total (I := I) g
    intro γ j
    have hcongr : (fun b : M => (cotangentToDualLinear (I := I) (x := b) (Y b))
          (chartBasisVecFiber (I := I) γ j b)) =
        (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) γ j b)) := by
      funext b
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [hcongr]
    exact cotangentSection_chartComponent_contMDiffOn (I := I) Y γ j
  refine hmain.congr (fun x => ?_)
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) (Y x))) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
      (inverseMetricSharpFib (I := I) g x (Y x))
  rw [inverseMetricSharpFib_apply]

def inverseMetricSharpField (g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E →L[ℝ] E,
      (fun x : M => Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x)⟯ where
  toFun := fun x : M => inverseMetricSharpFib (I := I) g x
  contMDiff_toFun := inverseMetricSharpField_contMDiff (I := I) g

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp] lemma inverseMetricSharpField_apply (g : SmoothRiemannianMetric I M) (x : M) :
    inverseMetricSharpField (I := I) g x = inverseMetricSharpFib (I := I) g x := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem cometricBilin_contMDiff (g : SmoothRiemannianMetric I M)
    (α β : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => cometricBilin (I := I) g x (α x) (β x)) := by
  have hsharpβ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b
        (metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (β b)))) := by
    apply metricSharp_contMDiff_total (I := I) g
    intro γ j
    have hcongr : (fun b : M => (cotangentToDualLinear (I := I) (x := b) (β b))
          (chartBasisVecFiber (I := I) γ j b)) =
        (fun b : M => Tensor0SSpace.toModel (β b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) γ j b)) := by
      funext b
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [hcongr]
    exact cotangentSection_chartComponent_contMDiffOn (I := I) β γ j
  have hidentity : (fun x : M => cometricBilin (I := I) g x (α x) (β x)) =
      (fun b : M => Tensor0SSpace.toModel (α b)
        (fun _ : Fin 1 =>
          metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (β b)))) := by
    funext b
    rw [cometricBilin_eq_dual_sharp, inverseMetricSharpFib_apply,
      cotangentToDualLinear_apply, cotangentToDual_apply]
    rfl
  rw [hidentity]
  apply contMDiff_section_apply (n := 1) (T := fun b => α b) α.contMDiff
  intro i
  exact hsharpβ

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem exists_uniform_cometricBilin_bound [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (α β : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, |cometricBilin (I := I) g x (α x) (β x)| ≤ C := by
  have hcont : Continuous (fun x : M => cometricBilin (I := I) g x (α x) (β x)) :=
    (cometricBilin_contMDiff (I := I) g α β).continuous
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, le_refl 0, fun x => (hM.false x).elim⟩
  · obtain ⟨x₀, -, hx₀⟩ := (isCompact_univ (X := M)).exists_isMaxOn (univ_nonempty)
      (continuous_abs.comp hcont).continuousOn
    refine ⟨|cometricBilin (I := I) g x₀ (α x₀) (β x₀)|, abs_nonneg _, fun x => ?_⟩
    exact hx₀ (mem_univ x)

end DifferentialGeometry
