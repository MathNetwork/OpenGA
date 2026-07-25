import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.LowerAllUpperIndices
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SInnerSectionContinuity
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.Tensor0SBundleLocalityIdentities
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannianBundle
open DifferentialGeometry.Tensor.Tensor0SInnerSectionContinuity
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def chartInnerRSBilin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => chartTensorInnerPointwise_rs_model
      (I := I) (M := M) g r s α b T S)
    (fun T₁ T₂ S =>
      chartTensorInnerPointwise_rs_model_add_left
        (I := I) (M := M) g r s α b T₁ T₂ S)
    (fun c T S => by
      have := chartTensorInnerPointwise_rs_model_smul_left
        (I := I) (M := M) g r s α b c T S
      simpa using this)
    (fun T S₁ S₂ =>
      chartTensorInnerPointwise_rs_model_add_right
        (I := I) (M := M) g r s α b T S₁ S₂)
    (fun c T S => by
      have := chartTensorInnerPointwise_rs_model_smul_right
        (I := I) (M := M) g r s α b c T S
      simpa using this)

@[simp] private lemma chartInnerRSBilin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T S : TensorRSModel r s ℝ E) :
    chartInnerRSBilin (I := I) (M := M) g r s α b T S =
      chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T S := rfl

private def chartInnerRSLinearOuter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] (TensorRSModel r s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (chartInnerRSBilin (I := I) (M := M) g r s α b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b (T₁ + T₂) S =
      chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T₁ S +
        chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T₂ S
    exact chartTensorInnerPointwise_rs_model_add_left
      (I := I) (M := M) g r s α b T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b (c • T) S =
      c • chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T S
    rw [chartTensorInnerPointwise_rs_model_smul_left]
    rfl

def chartTensorInnerRSCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M) :
    TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (chartInnerRSLinearOuter (I := I) (M := M) g r s α b)

@[simp] lemma chartTensorInnerRSCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerRSCLM (I := I) (M := M) g r s α b T S =
      chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T S := rfl


lemma chartTensorInnerRSCLM_continuousAt_of_baseSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {b₀ : M} (hb₀ : b₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousAt
      (fun b : M => chartTensorInnerRSCLM (I := I) (M := M) g r s α b) b₀ := by
  classical
  set basis := Module.finBasis ℝ (TensorRSModel r s ℝ E) with hbasis_def
  refine continuousAt_bilin_of_basis_continuousAt
    (F := TensorRSModel r s ℝ E) (N := M) (v := basis)
    (u := fun b => chartTensorInnerRSCLM (I := I) (M := M) g r s α b)
    (x₀ := b₀) ?_
  intro i j
  have heq : (fun b : M =>
      chartTensorInnerRSCLM (I := I) (M := M) g r s α b (basis i) (basis j))
      = (fun b : M =>
        chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b (basis i) (basis j)) := by
    funext b
    rw [chartTensorInnerRSCLM_apply]
  rw [heq]
  have hSmooth := chartTensorInnerPointwise_rs_model_contMDiffOn
    (I := I) (M := M) g r s α (basis i) (basis j)
  have hCont : ContinuousOn
      (fun b : M =>
        chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b (basis i) (basis j))
      (trivializationAt E (TangentSpace I) α).baseSet := hSmooth.continuousOn
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  exact hCont.continuousAt (hOpen.mem_nhds hb₀)


private lemma toModel_trivAt_symm_eq_chartRSTwist
    (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TensorRSModel r s ℝ E) :
    Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symm b v)
      = chartRSTwist (I := I) (M := M) α b r s v := by
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  have hb_r : b ∈ er.baseSet := hb
  have hb_s : b ∈ es.baseSet := hb
  have hb_RS : b ∈ eRS.baseSet := ⟨hb_r, hb_s⟩
  have h_sym :
      (eRS.symm b v : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        = (es.symmL ℝ b).comp (v.comp (er.continuousLinearMapAt ℝ b)) :=
    _root_.Bundle.Pretrivialization.continuousLinearMap_symm_apply'
      (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (F₂ := Tensor0SModel s ℝ E)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (e₁ := er) (e₂ := es) (b := b) hb_RS v
  refine ContinuousLinearMap.ext ?_
  intro α'
  change (Tensor0SBundle.TensorRSSpace.toModel
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
      (eRS.symm b v)) α' = chartRSTwist (I := I) (M := M) α b r s v α'
  have htoModel_apply :
      (Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        (eRS.symm b v)) α' =
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from eRS.symm b v)
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := r) (x := b) α')) := by
    rfl
  rw [htoModel_apply]
  have happ :
      ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from eRS.symm b v)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := r) (x := b) α') :
            Tensor0SSpace s I b)
        = ((es.symmL ℝ b).comp (v.comp (er.continuousLinearMapAt ℝ b)))
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := r) (x := b) α') := by
    rw [h_sym]
  rw [happ]
  simp only [ContinuousLinearMap.comp_apply]
  have h_er :
      ((er.continuousLinearMapAt ℝ b)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := r) (x := b) α') :
            Tensor0SModel r ℝ E) =
      α'.compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
    have := triv_continuousLinearMapAt_eq_compContinuousLinearMap
      (I := I) (M := M) (s := r) (b₀ := α) (b := b) hb_r
      (T := show Bundle.continuousMultilinearMap ℝ r E (TangentSpace I) b from α')
    convert this using 1
  rw [h_er]
  set Tβ : Tensor0SModel s ℝ E :=
    v (α'.compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)) with hTβ_def
  have h_es :
      (Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
        ((es.symmL ℝ b) (show Tensor0SSpace s I b from Tβ)) :
            Tensor0SModel s ℝ E) =
      Tβ.compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b) := by
    have :=
      Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
        (𝕜 := ℝ) (B := M) (F := E) (E := (TangentSpace I : M → Type _))
        (s := s) (x₀ := α) (x := b) hb_s Tβ
    have htoModel_eq :
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          ((es.symmL ℝ b) (show Tensor0SSpace s I b from Tβ)) :
            Tensor0SModel s ℝ E) =
        (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
          (es.symmL ℝ b) (show Tensor0SSpace s I b from Tβ)) := by
      exact Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply
        (I := I) (M := M) s b _
    rw [htoModel_eq]
    convert this using 1
  have h_lhs_simplify :
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
        ((es.symmL ℝ b) (show Tensor0SSpace s I b from Tβ)) =
        Tβ.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b) := h_es
  change Tensor0SBundle.Tensor0SSpace.toModel
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
      ((es.symmL ℝ b) Tβ) = chartRSTwist (I := I) (M := M) α b r s v α'
  rw [h_lhs_simplify, chartRSTwist_apply]


private lemma tensorRSRiemannianInnerCLM_at_trivAt_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v w : TensorRSModel r s ℝ E) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symm b v)
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symm b w) =
      chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b v w := by
  rw [tensorRSRiemannianInnerCLM_apply]
  rw [toModel_trivAt_symm_eq_chartRSTwist (I := I) (M := M) (E := E) r s α hb v]
  rw [toModel_trivAt_symm_eq_chartRSTwist (I := I) (M := M) (E := E) r s α hb w]
  exact (chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
    (I := I) (M := M) g r s α hb v w).symm


lemma tensorRSRiemannianInnerCLM_inCoordinates_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v w : TensorRSModel r s ℝ E) :
    ContinuousLinearMap.inCoordinates (TensorRSModel r s ℝ E)
        (fun b' : M => TensorRSSpace r s I b')
        (TensorRSModel r s ℝ E →L[ℝ] ℝ)
        (fun b' : M => TensorRSSpace r s I b' →L[ℝ] ℝ)
        α b α b
        (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b) v w =
      chartTensorInnerRSCLM (I := I) (M := M) g r s α b v w := by
  have hb' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun b' : M => TensorRSSpace r s I b') α).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hb, hb⟩
  have hb_trivR :
      b ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet :=
    mem_univ _
  have hb_dual :
      b ∈ (trivializationAt (TensorRSModel r s ℝ E →L[ℝ] ℝ)
        (fun b' : M => TensorRSSpace r s I b' →L[ℝ] ℝ) α).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hb', mem_univ _⟩
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
    (F₁ := TensorRSModel r s ℝ E) (F₂ := TensorRSModel r s ℝ E)
    (F₃ := ℝ)
    (E₁ := fun b' : M => TensorRSSpace r s I b')
    (E₂ := fun b' : M => TensorRSSpace r s I b')
    (E₃ := Bundle.Trivial M ℝ)
    (x₀ := α) (x := b)
    (ϕ := tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b)
    (v := v) (w := w) hb' hb' hb_trivR]
  have h_lm_id : ∀ y : ℝ,
      (trivializationAt ℝ (Bundle.Trivial M ℝ) α).linearMapAt ℝ b y = y := by
    intro y
    have hmem : b ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := mem_univ _
    rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) α).coe_linearMapAt_of_mem hmem]
    rfl
  rw [h_lm_id]
  rw [tensorRSRiemannianInnerCLM_at_trivAt_symm
    (I := I) (M := M) g r s α hb v w]
  rfl


theorem tensorRSRiemannianInnerCLM_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ContinuousOn (fun b : M =>
      TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ) b
        (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b))
      (chartAt H α).source := by
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  rw [show (chartAt H α).source =
    (trivializationAt E (TangentSpace I) α).baseSet from
    (TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α).symm]
  rw [ContinuousOn]
  intro b₀ hb₀
  apply ContinuousAt.continuousWithinAt
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  have hb₀_self : b₀ ∈ (trivializationAt E (TangentSpace I) b₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt (F := E)
      (E := (TangentSpace I : M → Type _)) b₀
  have hOpen_b₀ : IsOpen (trivializationAt E (TangentSpace I) b₀).baseSet :=
    (trivializationAt E (TangentSpace I) b₀).open_baseSet
  have hCont_clm := chartTensorInnerRSCLM_continuousAt_of_baseSet
    (I := I) (M := M) g r s b₀ hb₀_self
  refine ContinuousAt.congr hCont_clm ?_
  have h_nhds : (trivializationAt E (TangentSpace I) b₀).baseSet ∈ 𝓝 b₀ :=
    hOpen_b₀.mem_nhds hb₀_self
  filter_upwards [h_nhds] with x hx
  refine ContinuousLinearMap.ext ?_
  intro v
  refine ContinuousLinearMap.ext ?_
  intro w
  exact (tensorRSRiemannianInnerCLM_inCoordinates_apply
    (I := I) (M := M) g r s b₀ hx v w).symm


theorem tensorRSRiemannianInnerCLM_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Continuous (fun b : M =>
      TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ) b
        (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b)) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_source : b ∈ (chartAt H b).source := mem_chart_source H b
  have hOpen : IsOpen (chartAt H b).source := (chartAt H b).open_source
  exact (tensorRSRiemannianInnerCLM_continuousOn (I := I) (M := M) g r s b).continuousAt
    (hOpen.mem_nhds hb_source)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannianBundle
open DifferentialGeometry.Tensor.Tensor0SInnerSectionContinuity
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

instance tensorRSSpace_totalSpace_topologicalSpace (r s : ℕ) :
    TopologicalSpace (Bundle.TotalSpace (TensorRSModel r s ℝ E)
      (TensorRSSpace r s I (M := M))) :=
  Tensor0SBundle.tensorRSBundle_topology r s

instance tensorRSSpace_fiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (TensorRSSpace r s I (M := M)) :=
  Tensor0SBundle.tensorRSBundle_fiber r s

instance tensorRSSpace_vectorBundle (r s : ℕ) :
    VectorBundle ℝ (TensorRSModel r s ℝ E) (TensorRSSpace r s I (M := M)) :=
  Tensor0SBundle.tensorRSBundle_vector r s

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

instance tensorRS_isContinuousRiemannianBundle
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    IsContinuousRiemannianBundle (TensorRSModel r s ℝ E)
      (fun b : M => TensorRSSpace r s I b) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  refine ⟨?_⟩
  refine ⟨fun b => tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b, ?_, ?_⟩
  · exact tensorRSRiemannianInnerCLM_continuous (I := I) (M := M) g r s
  · intros b v w
    rfl

end DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous
