import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BBSAllMBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.EndpointMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.EndpointRicciLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.ExtendShiInputs

set_option linter.style.longLine false


















































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Connection
open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]






def cinftyLimitData_of_allMBounds
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4
            (S.base.rm04 t x) ≤ K)
    (hEquiv : ∃ Lambda : ℝ, 1 ≤ Lambda ∧
      ∃ t1 : ℝ, t1 ∈ Set.Ico alpha omega ∧
        ∀ s : ℝ, s ∈ Set.Ico t1 omega →
          ∀ x : M, ∀ v : TangentSpace I x,
            Lambda⁻¹ * (S.base.metric alpha).inner x v v ≤
                (S.base.metric s).inner x v v ∧
              (S.base.metric s).inner x v v ≤
                Lambda * (S.base.metric alpha).inner x v v)
    (hbounds : ∀ m : ℕ, ∃ C : ℝ, ∀ (t : ℝ) (x : M),
        (alpha + omega) / 2 ≤ t → t < omega →
          nablaKRm04NormSqIntrinsic (I := I) S m t x ≤ C) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω := by
  let hEnd := exists_endMetric (I := I) S hdim hS hbound hEquiv
  let gInf := Classical.choose hEnd
  have hleft := Classical.choose_spec hEnd
  refine
    { limitMetric := gInf
      tendsto_left := hleft
      ricci_match := ?_ }
  intro x v w
  exact ricci_tendsto_left (I := I) S hdim hS hbound hEquiv gInf hleft x v w









def cinftyLimitData_of_solution
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (Rm04 : ℝ → Tensor04Section (I := I) (M := M))
    (hRm : ∀ t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen alpha omega hαω),
      Rm04RealizesConnection (I := I)
        (S.family.metric (t : ℝ)) (S.family.connection (t : ℝ)) (Rm04 (t : ℝ)))
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) ≤ K) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω := by
  have hRmRaw : ∀ t ∈ Set.Ico alpha omega,
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t) := by
    intro t ht
    simpa [SolutionOn.family, SolutionFamily.connection] using
      hRm (⟨t, ht⟩ : RealTimeInterval.FlowTime
        (RealTimeInterval.closedOpen alpha omega hαω))
  have hCan := rm04_bound_can (I := I) Rm04 hRmRaw hbound
  let K := Classical.choose hbound
  have hK := Classical.choose_spec hbound
  have hRic := ric_quad_le_of_soln (I := I) hRmRaw hK
  have hRicConst :
      0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K := by
    positivity
  have hEquiv := hell_of_soln (I := I) hS hRicConst hRic
  exact cinftyLimitData_of_allMBounds (I := I) S hS hdim hCan hEquiv
    (bbsAllMBounds (I := I) S hS hdim Rm04 hRm ⟨K, hK⟩)

end DifferentialGeometry.PDE.RicciFlow
