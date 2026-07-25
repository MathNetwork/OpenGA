import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorChartTestDecoupling


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma covGradBundle_trivFibre_eq'
    (r s : ℕ) (α : M) (b : M)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((trivializationAt E (TangentSpace I) α).symmL ℝ b)) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentRaw_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
            (Matrix.vecTail Jdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  classical
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun z : M => Tensor0SSpace r I z)) := tensor0SBundle_topology r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun z : M => Tensor0SSpace (s + 1) I z)) := tensor0SBundle_topology (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundle_vector r (s + 1)
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have hb_baseS1 : b ∈ (trivializationAt (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun z : M => Tensor0SSpace r I z) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    refine ⟨⟨?_, ?_⟩, hb_int⟩
    · rw [extChartAt_source]; exact hb_chart
    · rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  set Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun z : M => S.toSection z) b with hΦ_def
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [covGrad_toSection_apply (I := I) (M := M) g r s S b]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun z : M => S.toSection z) b) = Φ from rfl]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun z : M => TensorRSSpace r (s + 1) I z) α).coe_linearMapAt_of_mem
      (R := ℝ) hb_baseS1]
  beta_reduce
  rw [covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb_base Φ]
  rw [tensorChartComponentProjection_apply,
    covGradModelEquiv_apply (E := E) r s]
  rw [covGradBundle_trivFibre_eq' (I := I) (M := M) r s α b Φ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hsymmL : (trivializationAt E (TangentSpace I) α).symmL ℝ b
      ((chartModelBasis E) (Jdx 0)) =
      chartBasisVecFiber (I := I) α (Jdx 0) b := rfl
  rw [hsymmL]
  rw [show Φ (chartBasisVecFiber (I := I) α (Jdx 0) b) =
      tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α (Jdx 0) b) from rfl]
  rw [tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
    g r s S α (Jdx 0) hb_good]
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
    g r s S α (Jdx 0) Idx (Matrix.vecTail Jdx) hy

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
