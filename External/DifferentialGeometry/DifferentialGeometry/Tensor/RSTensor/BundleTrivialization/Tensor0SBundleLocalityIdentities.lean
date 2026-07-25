import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SInnerSectionContinuity
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Tensor

open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ :=
  Subtype.ext h_chart

omit [FiniteDimensional ℝ E] in
private lemma tangent_trivb₀_symmL_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

omit [FiniteDimensional ℝ E] in
private lemma tangent_trivb₀_clmAt_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

omit [FiniteDimensional ℝ E] in
private lemma tangent_trivializationAt_baseSet (b₀ : M) :
    (trivializationAt E (TangentSpace I) b₀).baseSet = (chartAt H b₀).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀

theorem triv_continuousLinearMapAt_eq_compContinuousLinearMap
    {s : ℕ} (b₀ b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet)
    (T : Bundle.continuousMultilinearMap ℝ s E (TangentSpace I) b) :
    ((trivializationAt
        (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
          ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      T.compContinuousLinearMap
        (fun _ : Fin s => (trivializationAt E (TangentSpace I) b₀).symmL ℝ b) := by
  set e := trivializationAt
    (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀ with he_def
  have hbase : b ∈ e.baseSet := hb

  have h_cLMA : (e.continuousLinearMapAt ℝ b T :
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (e ⟨b, T⟩).2 := by
    have h := congrFun (e.coe_linearMapAt_of_mem (R := ℝ) hbase) T
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply] using h
  rw [h_cLMA]

  apply ContinuousMultilinearMap.ext
  intro w

  change T (fun i : Fin s => (trivializationAt E (TangentSpace I) b₀).symmL ℝ b (w i)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem multilinear_trivAt_symmL_apply_eq_self_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    ((trivializationAt (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).symmL ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) = T := by

  have h_base : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [tangent_trivializationAt_baseSet (I := I) b₀]
    exact h_src

  have h_clmAt_id := tangent_trivb₀_clmAt_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart h_src

  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (s := s) b₀ b h_base T]

  rw [h_clmAt_id]

  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr

theorem multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : Bundle.continuousMultilinearMap ℝ s E (TangentSpace I) b) :
    ((trivializationAt (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
          ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by

  have h_base : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [tangent_trivializationAt_baseSet (I := I) b₀]
    exact h_src

  have h_symmL_id := tangent_trivb₀_symmL_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart h_src

  rw [triv_continuousLinearMapAt_eq_compContinuousLinearMap (I := I)
    (s := s) b₀ b h_base T]
  rw [h_symmL_id]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr

theorem tensor0S_trivAt_symmL_eq_one_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : Tensor0SModel s ℝ E) :
    ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) b₀).symmL ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) = T := by

  change (trivializationAt
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).symmL ℝ b T = T
  exact multilinear_trivAt_symmL_apply_eq_self_on_locality
    (s := s) (b₀ := b₀) (b := b) (h_chart := h_chart) (h_src := h_src) (T := T)

theorem tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : Tensor0SSpace s I b) :
    ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) b₀).continuousLinearMapAt ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by

  change (trivializationAt
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
        ℝ b T = T
  exact multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (s := s) (b₀ := b₀) (b := b) (h_chart := h_chart) (h_src := h_src) (T := T)

end Tensor
end DifferentialGeometry

end
