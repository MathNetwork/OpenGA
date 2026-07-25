import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedCovGrad_rs_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (i : ℕ) :
    ∃ τ : Equiv.Perm (Fin (s + i)), ∀ (x : M) (d : Tensor0SSpace r I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
            (iteratedCovGrad (I := I) g r s i Φ').toSection x) d) =
        ContinuousMultilinearMap.domDomCongr τ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) g r s i Φ).toSection x) d)) := by
  induction i with
  | zero =>
    refine ⟨σ, fun x d => ?_⟩
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
    exact hrel x d
  | succ i ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), fun x d => ?_⟩
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
    apply ContinuousMultilinearMap.ext
    intro v
    exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_rs_toModel_domDomCongr
      (I := I) (M := M) g r (s + i) τ
      (iteratedCovGrad (I := I) g r s i Φ) (iteratedCovGrad (I := I) g r s i Φ')
      hτ x d v

theorem riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
  classical
  obtain ⟨τ, hτ⟩ :=
    exists_iteratedCovGrad_rs_toModel_domDomCongr (I := I) (M := M) g r s σ Φ Φ' hrel i
  have hsec : (iteratedCovGrad (I := I) g r s i Φ').toSection x =
      tensorRS_domDomCongr τ ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
          (iteratedCovGrad (I := I) g r s i Φ').toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x from
          tensorRS_domDomCongr τ ((iteratedCovGrad (I := I) g r s i Φ).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply]
    exact hτ x d
  rw [hsec]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g r (s + i) x τ _

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g r s) (σ' : Equiv.Perm (Fin r)) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen
            (I := I) (M := M) g r s R σ')).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_reindexCoeffGen
        (I := I) (M := M) g r s R σ' i,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen_toSection,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen]

end Connection
end Integral
end DifferentialGeometry

end
