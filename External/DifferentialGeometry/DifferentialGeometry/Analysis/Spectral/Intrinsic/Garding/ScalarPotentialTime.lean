import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarPotential
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricAppHsTime








noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E



theorem scalarPot_dyn_fin
    (q : SmoothRiemannianMetric I M)
    (zeta : Real → C^∞⟮I, M; Real⟯) {S : Set Real} (hS : IsOpen S)
    (hzeta : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ S))
    (m k : ℕ)
    (U : Real → tensorHs (I := I) (M := M) q 0 0 (m : Real))
    (hU : ContDiffOn Real k U S) :
    ContDiffOn Real k
      (fun t => scalarPotHs (I := I) (M := M) q (zeta t) m (U t)) S := by
  have hcoeff := scalarCc_joint (I := I) (M := M) q zeta hzeta
  have happ := appHs_dyn_fin (I := I) (M := M) q 0 0 m k
    (fun t => scalarCc (I := I) (M := M) q (zeta t)) hS hcoeff U hU
  refine happ.congr ?_
  intro t ht
  exact scalarPotHs_app (I := I) (M := M) q (zeta t) m (U t)



theorem scalarPot_dyn_cd
    (q : SmoothRiemannianMetric I M)
    (zeta : Real → C^∞⟮I, M; Real⟯) {S : Set Real} (hS : IsOpen S)
    (hzeta : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ S))
    (m : ℕ)
    (U : Real → tensorHs (I := I) (M := M) q 0 0 (m : Real))
    (hU : ContDiffOn Real ∞ U S) :
    ContDiffOn Real ∞
      (fun t => scalarPotHs (I := I) (M := M) q (zeta t) m (U t)) S := by
  rw [contDiffOn_infty] at hU ⊢
  intro k
  exact scalarPot_dyn_fin (I := I) (M := M) q zeta hS hzeta m k U (hU k)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
