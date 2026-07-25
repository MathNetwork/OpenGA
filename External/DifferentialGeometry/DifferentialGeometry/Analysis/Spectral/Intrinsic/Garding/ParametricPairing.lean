import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.BalancedPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricAppCcJetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricScalarSmulJet








noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option maxHeartbeats 1600000 in


theorem iterL_pair_unif (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (Φ : ℝ → SmoothCcTensor g (s + 1) s) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel (s + 1) s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel (s + 1) s ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, t ∈ K → ∀ U : SmoothCcTensor g 0 s,
      |tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmoothIter (I := I) g 0 s n U).toFun
          (operatorFieldApply (I := I) (M := M) g (s + 1) s (Φ t)
            (covGrad (I := I) (M := M) g 0 s U)).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j U‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j U‖)) := by
  obtain ⟨CG, hCG_nn, hCG⟩ :=
    param_app_jet (I := I) (M := M) g (s + 1) s Φ hK hKS hjoint
  exact iterL_pair_jet_of (I := I) (M := M) g s n Φ K CG hCG_nn hCG




theorem iterL_smul_unif (g : SmoothRiemannianMetric I M) (n : ℕ)
    (zeta : ℝ → C^∞⟮I, M; ℝ⟯) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hzeta : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => (zeta p.2 : M → ℝ) p.1)
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, t ∈ K → ∀ U : SmoothCcTensor g 0 0,
      |tensorL2Inner (I := I) (M := M) g 0 0
          (oneMinusConnLapSmoothIter (I := I) g 0 0 n U).toFun
          (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 0 j U‖) *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 0 j U‖)) := by
  classical
  obtain ⟨cY, hcY_nn, hcY⟩ :=
    smul_jet_unif (I := I) (M := M) g zeta hK hKS hzeta
  obtain ⟨C, hC_nn, hC⟩ :=
    iterL_window_pair (I := I) (M := M) g 0 0 n (n / 2) 0 0
      (n + 1) n (by omega) (by omega) (by omega)
      (fun _ => 1) cY (fun _ => zero_le_one) hcY_nn
  refine ⟨C, hC_nn, fun t ht U => ?_⟩
  refine hC U U
    (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U) ?_ (hcY t ht U)
  intro p
  rw [one_mul]
  refine Finset.single_le_sum
    (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 0 j U‖)
    (fun j _ => norm_nonneg _) ?_
  rw [Finset.mem_range]
  omega

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
