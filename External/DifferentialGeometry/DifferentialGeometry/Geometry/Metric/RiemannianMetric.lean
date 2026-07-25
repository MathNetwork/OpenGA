


import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension



noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (n : WithTop ℕ∞)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

abbrev RiemannianMetric := Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)

private noncomputable def to02Tensor_eCLM :
    (E →L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ :=
  (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap

private noncomputable def to02Tensor_uCLM :
    (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap

set_option maxHeartbeats 800000 in

private lemma to02Tensor_trivialization_eq {x₀ x : M}
    (g : RiemannianMetric I n M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    let gI := Bundle.ContMDiffRiemannianMetric.inner g
    (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (fun y => Tensor0SBundle.Tensor0SSpace 2 I y) x₀
      ⟨x, ((to02Tensor_eCLM (E := E)).comp (gI x)).uncurryLeft⟩).2
      =
    (to02Tensor_uCLM (E := E)) ((to02Tensor_eCLM (E := E)).comp
      ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, gI x⟩).2)) := by
  dsimp
  let e₀ := trivializationAt E (TangentSpace I) x₀
  ext m
  change (((e₀.continuousMultilinearMap ℝ 2)
      ⟨x, ((to02Tensor_eCLM (E := E)).comp
        ((Bundle.ContMDiffRiemannianMetric.inner g) x)).uncurryLeft⟩).2) m = _
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.uncurryLeft_apply]
  have hx' : x ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp⟩
  rw [hom_trivializationAt_apply]
  change (to02Tensor_eCLM (E := E)) (((Bundle.ContMDiffRiemannianMetric.inner g) x)
      ((Trivialization.symmL ℝ e₀ x) (m 0)))
      (Fin.tail fun i => (Trivialization.symmL ℝ e₀ x) (m i)) =
    (to02Tensor_eCLM (E := E)) (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x
      ((Bundle.ContMDiffRiemannianMetric.inner g) x) (m 0))
      (Fin.tail m)
  rw [ContinuousLinearMap.inCoordinates_eq hx hx']
  simp [to02Tensor_eCLM, hom_trivializationAt, Trivialization.continuousLinearMap_apply]
  rfl

def RiemannianMetric.to02Tensor {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    (g : RiemannianMetric I n M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (I := I) (M := M) (n := n) 2 := by
  unfold Tensor0SBundle.Tensor0SField
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  let eCLM := to02Tensor_eCLM (E := E)
  let uCLM := to02Tensor_uCLM (E := E)
  let gI := Bundle.ContMDiffRiemannianMetric.inner g
  exact ⟨fun x => (eCLM.comp (gI x)).uncurryLeft, by
    haveI := Tensor0SBundle.tensor0SBundle_smooth
      (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := n) 2
    intro x₀; rw [contMDiffAt_section]
    have hTriv := (contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        (s := gI) (x₀ := x₀)).mp (g.contMDiff.contMDiffAt (x := x₀))
    have hCurried :
        ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) n
          (fun x => eCLM.comp ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
            (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀
            ⟨x, gI x⟩).2)) x₀ := by
      exact (contMDiffAt_const (c := eCLM)).clm_comp hTriv
    refine (uCLM.contMDiffAt.comp x₀ hCurried).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
    exact to02Tensor_trivialization_eq (I := I) (n := n) (M := M) (g := g) (x := x)
      (x₀ := x₀) hx⟩

end
