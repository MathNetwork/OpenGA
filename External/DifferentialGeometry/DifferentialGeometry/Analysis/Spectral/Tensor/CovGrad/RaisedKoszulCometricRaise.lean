import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def cometricRaiseSlot0FieldFun (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) (x : M) : Tensor0SBundle.TensorRSSpace 1 (s + 1) I x :=
  cometricRaiseSlot0Fib g₀ s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from S.toSection x)
      (unitTensor (I := I) (M := M) x))

noncomputable def cometricRaiseSlot0FieldSection (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) :=
  letI : NormedAddCommGroup (TensorRSModel 1 (s + 1) ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedAddCommGroup 1 (s + 1)
  letI : NormedSpace ℝ (TensorRSModel 1 (s + 1) ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedSpace 1 (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y)) :=
    Tensor0SBundle.tensorRSBundle_topology 1 (s + 1)
  letI : FiberBundle (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y) :=
    Tensor0SBundle.tensorRSBundle_fiber 1 (s + 1)
  letI : VectorBundle ℝ (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y) :=
    Tensor0SBundle.tensorRSBundle_vector 1 (s + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y) I :=
    Tensor0SBundle.tensorRSBundle_smooth ∞ 1 (s + 1)
  (⟨cometricRaiseSlot0FieldFun (I := I) (M := M) g₀ s S,
      cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ s
        (fun x : M =>
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from S.toSection x)
            (unitTensor (I := I) (M := M) x))
        (contMDiff_unitEvalSection (I := I) (M := M) g₀ (s + 2) S)⟩ :
    ContMDiffSection I (TensorRSModel 1 (s + 1) ℝ E) ∞ (fun y : M => TensorRSSpace 1 (s + 1) I y))

def cometricRaiseSlot0Field (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) : SmoothCcTensor g₀ 1 (s + 1) where
  toSection := cometricRaiseSlot0FieldSection (I := I) (M := M) g₀ s S
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma cometricRaiseSlot0Field_toSection (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) (x : M) :
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x =
      cometricRaiseSlot0Fib g₀ s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from S.toSection x)
          (unitTensor (I := I) (M := M) x)) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cometricRaiseSlot0Fib_clm_apply (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 2) I x) (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x D) om =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) D := by
  rfl

noncomputable def koszulCovecCc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 3 :=
  (1 / 2 : ℝ) •
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2)
          (symmSCovGrad3 (I := I) g₀ T)
        + domDomCongrSection (I := I) g₀ (finRotate 3) (symmSCovGrad3 (I := I) g₀ T)
        - domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (symmSCovGrad3 (I := I) g₀ T))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma koszulCovecCc_unitModel (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ T) x ![c, a, b] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (symmSCovGrad3 (I := I) g₀ T) x ![b, a, c]
          + unitModel (I := I) (M := M) g₀ 3 (symmSCovGrad3 (I := I) g₀ T) x ![a, b, c]
          - unitModel (I := I) (M := M) g₀ 3 (symmSCovGrad3 (I := I) g₀ T) x ![c, b, a]) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  have hperm : ∀ (σ : Equiv.Perm (Fin 3)) (m : Fin 3 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀ σ W) x m =
        unitModel (I := I) (M := M) g₀ 3 W x (fun i => m (σ i)) := by
    intro σ m
    rw [domDomCongrSection_unitModel (I := I) g₀ σ W x,
      ContinuousMultilinearMap.domDomCongr_apply]
  have hlin : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ T) x ![c, a, b] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 3) 2) W) x ![c, a, b]
          + unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀ (finRotate 3) W) x
              ![c, a, b]
          - unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀
              (Equiv.swap (1 : Fin 3) 2) W) x ![c, a, b]) := by
    simp only [koszulCovecCc, unitModel, SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_smul, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,


]
    rfl
  rw [hlin, hperm, hperm, hperm]
  have e1 : (fun i => (![c, a, b] : Fin 3 → TangentSpace I x) ((Equiv.swap (0 : Fin 3) 2) i)) =
      ![b, a, c] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have e2 : (fun i => (![c, a, b] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) = ![a, b, c] := by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]
  have e3 : (fun i => (![c, a, b] : Fin 3 → TangentSpace I x) ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![c, b, a] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [e1, e2, e3]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
