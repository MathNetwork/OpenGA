import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Operators
import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section SmoothSide

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem norm_appFullRS_sq_eq_integral
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    (W : SmoothCcTensor g r s) :
    ‖homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x (W.toSection x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hsec :
      (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x)
          ((homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W).toSection x)) =
        (homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W).toFun := by
    funext x
    rw [SmoothCcTensor.toFun_apply]
  rw [SmoothCcTensor.norm_def, ← hsec,
    tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s
      (fun x => (homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W).toSection x)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [appFullRS_toSection (I := I) (M := M) g r s s Ψ hΨ W]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem integrable_riemannianFiberNormSq_appFullRS
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    (W : SmoothCcTensor g r s) :
    Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x (W.toSection x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hmem := SmoothCcTensor.memL2_toFun (I := I) (M := M)
    (g := g) (r := r) (s := s) (homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W)
  have hint := hmem.integrable_inner_self
  refine hint.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [SmoothCcTensor.toFun_apply, appFullRS_toSection (I := I) (M := M) g r s s Ψ hΨ W x]
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
    (Ψ x (W.toSection x))).symm


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem integrable_riemannianFiberNormSq_toSection
    (W : SmoothCcTensor g r s) :
    Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hmem := SmoothCcTensor.memL2_toFun (I := I) (M := M) (g := g) (r := r) (s := s) W
  have hint := hmem.integrable_inner_self
  refine hint.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [SmoothCcTensor.toFun_apply]
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
    (W.toSection x)).symm


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem norm_appFullRS_le_sqrt_mul
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v)
    (W : SmoothCcTensor g r s) :
    ‖homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W‖ ≤ Real.sqrt C * ‖W‖ := by
  have hsq_int :
      ‖homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W‖ ^ 2 ≤ C * ‖W‖ ^ 2 := by
    rw [norm_appFullRS_sq_eq_integral (I := I) (M := M) Ψ hΨ W]
    have hWsq :
        ‖W‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      have hsec :
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
              (r := r) (s := s) (x := x) (W.toSection x)) = W.toFun := by
        funext x; rw [SmoothCcTensor.toFun_apply]
      rw [SmoothCcTensor.norm_def, ← hsec,
        tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s
          (fun x => W.toSection x)]
    rw [hWsq, ← integral_const_mul]
    refine integral_mono
      (integrable_riemannianFiberNormSq_appFullRS (I := I) (M := M) Ψ hΨ W)
      ((integrable_riemannianFiberNormSq_toSection (I := I) (M := M) W).const_mul C)
      (fun x => hbound x (W.toSection x))
  have hrhs : (0 : ℝ) ≤ Real.sqrt C * ‖W‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq_rhs : (Real.sqrt C * ‖W‖) ^ 2 = C * ‖W‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
  refine le_of_sq_le_sq ?_ hrhs
  rw [hsq_rhs]
  exact hsq_int


def fibreFieldMulSmoothCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v) :
    SmoothCcTensor g r s →L[ℝ] SmoothCcTensor g r s :=
  LinearMap.mkContinuous
    { toFun := fun W => homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W
      map_add' := fun W₁ W₂ => appFullRS_add_right (I := I) (M := M) g r s s Ψ hΨ W₁ W₂
      map_smul' := fun k W => appFullRS_smul_right (I := I) (M := M) g r s s k Ψ hΨ W }
    (Real.sqrt C)
    (fun W => norm_appFullRS_le_sqrt_mul (I := I) (M := M) Ψ hΨ hC hbound W)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
@[simp] theorem fibreFieldMulSmoothCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v)
    (W : SmoothCcTensor g r s) :
    fibreFieldMulSmoothCLM (I := I) (M := M) g r s Ψ hΨ hC hbound W =
      homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ W := rfl

end SmoothSide

section L2Operator

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


def fibreFieldMulL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  SmoothCcTensor.mapL2 (fibreFieldMulSmoothCLM (I := I) (M := M) g r s Ψ hΨ hC hbound)


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
@[simp] theorem fibreFieldMulL2_apply_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v)
    (S : SmoothCcTensor g r s) :
    fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound
        ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)) S) =
      (SmoothCcTensor.toL2 (g := g) (r := r) (s := s))
        (homTensorRSApply (I := I) (M := M) g r s s Ψ hΨ S) := by
  rw [fibreFieldMulL2, SmoothCcTensor.mapL2_apply_toL2,
    fibreFieldMulSmoothCLM_apply (I := I) (M := M) g r s Ψ hΨ hC hbound S]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem fibreFieldMulL2_opNorm_le_sqrt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v) :
    ‖fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound‖ ≤ Real.sqrt C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C) ?_
  intro y
  refine UniformSpace.Completion.induction_on
    (α := SmoothCcTensor g r s)
    (p := fun z => ‖fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound z‖ ≤
      Real.sqrt C * ‖z‖) y ?_ ?_
  · refine isClosed_le ?_ ?_
    · exact (fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound).continuous.norm
    · exact continuous_const.mul continuous_norm
  · intro S
    have hcoe :
        (S : UniformSpace.Completion (SmoothCcTensor g r s)) =
          (SmoothCcTensor.toL2 (g := g) (r := r) (s := s)) S :=
      (SmoothCcTensor.toL2_apply (g := g) (r := r) (s := s) S).symm
    rw [hcoe, fibreFieldMulL2_apply_toL2 (I := I) (M := M) g r s Ψ hΨ hC hbound S,
      SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2]
    exact norm_appFullRS_le_sqrt_mul (I := I) (M := M) Ψ hΨ hC hbound S

end L2Operator

end L2
end Integral
end DifferentialGeometry

end
