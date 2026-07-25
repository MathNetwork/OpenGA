import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenDivergenceIdentityAnySection


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma tensor0SCovariantDerivative_natCast_transport
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {a b : ℕ} (h : a = b)
    (W : Π y : M, Tensor0SSpace b I y) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M a cov
        (fun y : M => cast (congrArg (fun n => Tensor0SSpace n I y) h.symm) (W y)) x v =
      cast (congrArg (fun n => Tensor0SSpace n I x) h.symm)
        (tensor0SCovariantDerivative I M b cov W x v) := by
  subst h
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_natCast_transport
    {a b : ℕ} (h : a = b) {x : M} (T : Tensor0SSpace b I x) :
    Tensor0SSpace.toModel
        (cast (congrArg (fun n => Tensor0SSpace n I x) h.symm) T) =
      (Tensor0SSpace.toModel T).domDomCongr (finCongr h.symm) := by
  cases h
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma liftedTensorSection_zero_eq_natCast_unit
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (y : M) :
    liftedTensorSection (I := I) (M := M) g 0 s S y =
      cast (congrArg (fun n => Tensor0SSpace n I y) (Nat.zero_add s).symm)
        ((S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) := by
  refine Tensor0SSpace.toModel_injective ?_
  change Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 s S y) =
    Tensor0SSpace.toModel
      (cast (congrArg (fun n => Tensor0SSpace n I y) (Nat.zero_add s).symm)
        ((S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))))
  rw [toModel_natCast_transport (Nat.zero_add s)]
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  rw [toModel_liftedTensorSection_zero_eq_apply_unit_reindex (I := I) (M := M) g s S y u]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext j
  congr 1
  exact (Fin.ext (by simp)).symm

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem loweredCovDerivAt_eq_lower_tensorCovDerivAt_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s S x v) =
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v)) := by
  classical
  let unitSec : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
    ⟨fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
      contMDiff_unitZeroSection (I := I) (M := M)⟩
  have hcoe : (fun y : M => unitSec y) =
      fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl
  have hunit_model : Tensor0SSpace.toModel (unitSec x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    change Tensor0SSpace.toModel (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = _
    rw [Tensor0SSpace.toModel_ofModel]
  have hlowerA :
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v)) =
        (Tensor0SSpace.toModel
            ((tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v :
                Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
              (unitSec x))).domDomCongr (finCongr (Nat.zero_add s).symm) := by
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v) (unitSec x)]
    rw [hunit_model]
    rw [lowerAllUpperIndices_apply, separableFormAt_zero]
    congr 1
    funext j
    congr 1
    exact (Fin.ext (by simp)).symm
  rw [hlowerA]
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) S unitSec x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitSec y) x v) = 0 from by
    rw [hcoe]
    exact tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]
  rw [loweredCovDerivAt_def]
  rw [show liftedTensorSection (I := I) (M := M) g 0 s S =
        (fun y : M => cast (congrArg (fun n => Tensor0SSpace n I y) (Nat.zero_add s).symm)
          ((S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
            (Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
                (1 : ℝ))))) from by
      funext y
      exact liftedTensorSection_zero_eq_natCast_unit (I := I) (M := M) g s S y]
  rw [tensor0SCovariantDerivative_natCast_transport (LeviCivita (I := I) g)
    (Nat.zero_add s)
    (fun y : M => (S y : Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) x v]
  rw [toModel_natCast_transport (Nat.zero_add s)]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma loweringIntertwiner_gen (g : SmoothRiemannianMetric I M) (s : ℕ) :
    LoweringIntertwiner (I := I) (M := M) g s :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_gen (I := I) (M := M) g s S x v

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun
        (covGrad (I := I) (M := M) g 0 s v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general
    (I := I) (M := M) g s (loweringIntertwiner_gen (I := I) (M := M) g s) T v

end Connection
end Integral
end DifferentialGeometry

end
