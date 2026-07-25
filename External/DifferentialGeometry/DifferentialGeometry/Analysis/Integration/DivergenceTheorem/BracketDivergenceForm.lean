import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section NormedSmoothExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def smoothExtensionTangentSection (x : M) (v : TangentSpace I x) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma smoothExtensionTangentSection_apply (x : M) (v : TangentSpace I x) (b : M) :
    smoothExtensionTangentSection (I := I) (M := M) x v b = smoothExtensionTangent (I := I) x v b :=
  rfl

end NormedSmoothExtension

def lieBracketSection (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨VectorField.mlieBracket I (fun b : M => X b) (fun b : M => Y b),
    mlieBracket_contMDiff (I := I) X.contMDiff Y.contMDiff⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma lieBracketSection_apply
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    lieBracketSection (I := I) (M := M) X Y b =
      VectorField.mlieBracket I (fun b : M => X b) (fun b : M => Y b) b :=
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem loweredCovDerivAlongVF_firstSlot_eq_lower_covApply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s Z.toSection x)) =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (covApply (tensorCov (I := I) g r s) (fun y : M => V y)
              (fun y : M => W'.toSection y) x)))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s Z.toSection x)) := by
  classical
  have hbridge := loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs
    (I := I) (M := M) g r s W'.toSection x (V x)
  rw [loweredCovDerivAlongVF_apply, hbridge]
  rfl

theorem loweredCovDeriv_leibniz_combined_integral_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W'.toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection V x))
          + tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection x
            * divergence_g (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g r s
    W'.toSection Z.toSection V

omit [CompactSpace M] in
theorem loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g
        (smoothSmul (I := I)
          (tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection)
          (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W'.toSection Z.toSection)
          V) x =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
        + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W'.toSection x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection V x))
        + tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection x
          * divergence_g (I := I) g V x := by
  rw [divergence_g_smoothSmul (I := I) (M := M) g
    (tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection)
    (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W'.toSection Z.toSection) V x]
  rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g r s
    W'.toSection Z.toSection V x]
  rw [loweredCovDerivAlongVF_apply, loweredCovDerivAlongVF_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem divergence_g_finset_sum
    (g : SmoothRiemannianMetric I M) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g (∑ i, V i) x = ∑ i, divergence_g (I := I) g (V i) x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact divergence_g_zero (I := I) (M := M) g x
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [divergence_g_add (I := I) (M := M) g (V a) (∑ i ∈ t, V i) x]
    rw [ih]

omit [CompactSpace M] in
theorem frameSummed_covDerivAlongVF_leibniz_combined_eq_divergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) (x : M) :
    divergence_g (I := I) g
        (∑ i, smoothSmul (I := I)
          (tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (tensorInnerScalar_contMDiff (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (V i)) x =
      ∑ i, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergence_g (I := I) g (V i) x) := by
  classical
  rw [divergence_g_finset_sum (I := I) (M := M) g _ x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul
    (I := I) (M := M) g r s (W i) Z (V i) x

theorem integral_frameSummed_bracketCovDeriv_combined_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) :
    ∑ i, ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_frameSummed_covDeriv_combined_eq_zero (I := I) (M := M) g r s V W Z

end Connection
end Integral
end DifferentialGeometry

end
