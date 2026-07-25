import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorRSMetricCompatible
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def tensorInnerScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    M → ℝ :=
  fun y => tensorInnerPointwise (I := I) (M := M) g r s y
    (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp]
lemma tensorInnerScalar_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    tensorInnerScalar (I := I) (M := M) g r s W S y =
      tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y)) := rfl

omit [CompactSpace M] in
omit [CompleteSpace E] in
lemma tangentSectionAction_tensorInnerScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) V
        (tensorInnerScalar (I := I) (M := M) g r s W S) x =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s S x))
        + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))) := by
  rw [tangentSectionAction_def]
  exact tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (I := I) (M := M) g r s W S x (V x)

omit [CompleteSpace E] in
theorem integral_tensorInner_tangentAction_add_smul_divergence_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hWS : ContMDiff I 𝓘(ℝ) ∞
      (tensorInnerScalar (I := I) (M := M) g r s W S)) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s S x (V x)))
          + tensorInnerScalar (I := I) (M := M) g r s W S x
            * divergence_g (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have hV_cs : HasCompactSupport (V : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hIBP := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) (M := M) g (f := tensorInnerScalar (I := I) (M := M) g r s W S)
    hWS V hV_cs
  have hLeibniz : ∀ x : M,
      tangentSectionAction (I := I) V
          (tensorInnerScalar (I := I) (M := M) g r s W S) x =
        covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))) :=
    fun x => tangentSectionAction_tensorInnerScalar
      (I := I) (M := M) g r s W S V x
  have hLHS :
      ∫ x, tangentSectionAction (I := I) V
            (tensorInnerScalar (I := I) (M := M) g r s W S) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
                (Tensor0SSpace.toModel
                  (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g r s S x))
              + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g r s W x))
                (Tensor0SSpace.toModel
                  (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLeibniz)
  have hsum :
      ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s S x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, tensorInnerScalar (I := I) (M := M) g r s W S x
              * divergence_g (I := I) g V x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [← hLHS]; exact hIBP
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hAB_cont : Continuous
      (tangentSectionAction (I := I) V
        (tensorInnerScalar (I := I) (M := M) g r s W S)) :=
    (tangentSectionAction_contMDiff (I := I) V hWS).continuous
  have hAB_int : Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s S x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous
        (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s S x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s S x (V x)))) := by
      refine hAB_cont.congr (fun x => ?_)
      rw [tangentSectionAction_def]
      exact tensorInnerPointwise_hasMFDerivAt_metricCompatible
        (I := I) (M := M) g r s W S x (V x)
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC_int : Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g r s W S x
        * divergence_g (I := I) g V x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hf_cont : Continuous (tensorInnerScalar (I := I) (M := M) g r s W S) :=
      hWS.continuous
    have hdiv_cont : Continuous (divergence_g (I := I) g V) :=
      (divergence_g_contMDiff (I := I) g V).continuous
    exact (hf_cont.mul hdiv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add hAB_int hC_int, hsum]
  ring

omit [CompleteSpace E] in
theorem integral_tensorInner_covDeriv_integrationByParts
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hWS : ContMDiff I 𝓘(ℝ) ∞
      (tensorInnerScalar (I := I) (M := M) g r s W S))
    (hWcov_int : Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S x)))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (hScov_int : Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s W x))
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s S x (V x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        - ∫ x, tensorInnerScalar (I := I) (M := M) g r s W S x
              * divergence_g (I := I) g V x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hC_int : Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g r s W S x
        * divergence_g (I := I) g V x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hf_cont : Continuous (tensorInnerScalar (I := I) (M := M) g r s W S) :=
      hWS.continuous
    have hdiv_cont : Continuous (divergence_g (I := I) g V) :=
      (divergence_g_contMDiff (I := I) g V).continuous
    exact (hf_cont.mul hdiv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcombined := integral_tensorInner_tangentAction_add_smul_divergence_eq_zero
    (I := I) (M := M) g r s W S V hWS
  set A : M → ℝ := fun x => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
    (Tensor0SSpace.toModel
      (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
    (Tensor0SSpace.toModel
      (liftedTensorSection (I := I) (M := M) g r s S x)) with hA_def
  set B : M → ℝ := fun x => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
    (Tensor0SSpace.toModel
      (liftedTensorSection (I := I) (M := M) g r s W x))
    (Tensor0SSpace.toModel
      (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))) with hB_def
  set C : M → ℝ := fun x => tensorInnerScalar (I := I) (M := M) g r s W S x
    * divergence_g (I := I) g V x with hC_def
  have hcombined' :
      ∫ x, (A x + B x + C x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := hcombined
  have hsplitAB :
      ∫ x, (A x + B x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        (∫ x, A x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, B x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_add hWcov_int hScov_int
  have hsplitABC :
      ∫ x, (A x + B x + C x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        (∫ x, (A x + B x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, C x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_add (hWcov_int.add hScov_int) hC_int
  rw [hsplitABC, hsplitAB] at hcombined'
  linarith [hcombined']

end Connection
end Integral
end DifferentialGeometry

end
