import DifferentialGeometry.Geometry.Exponential.DiagInvBranch

set_option autoImplicit false









noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential
namespace DiagInvBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]



noncomputable def diagReadout
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    (y : M × M) : E :=
  (trivializationAt E (TangentSpace I) p (B.inv y)).2



def readDom
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) : Set (M × M) :=
  B.dom ∩ Prod.fst ⁻¹' (trivializationAt E (TangentSpace I) p).baseSet



omit [ConnectedSpace M] in
omit [InnerProductSpace ℝ E] in
theorem readoutDomInf
    [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    IsOpen B.readDom ∧
      (p, p) ∈ B.readDom ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞ (diagReadout B) B.readDom ∧
      ∀ y ∈ B.readDom,
        diagExp (I := I) g hEnorm (B.inv y) = y ∧
        (B.inv y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1 (B.inv y).snd = y.2 := by
  let e := trivializationAt E (TangentSpace I) p
  have hopen : IsOpen B.readDom :=
    B.hom.open_target.inter (e.open_baseSet.preimage continuous_fst)
  have hp : (p, p) ∈ B.readDom :=
    ⟨B.center_mem, mem_baseSet_trivializationAt E (TangentSpace I) p⟩
  have hsmooth : ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
      (diagReadout B) B.readDom := by
    intro y hy
    have hbranchAt : ContMDiffAt (I.prod I) I.tangent ∞ B.inv y :=
      (B.inv_inf y hy.1).contMDiffAt (B.hom.open_target.mem_nhds hy.1)
    have hbase : (B.inv y).proj ∈ e.baseSet := by
      rw [B.proj_eq hy.1]
      exact hy.2
    have hreadAt : ContMDiffAt (I.prod I) 𝓘(ℝ, E) ∞
        (diagReadout B) y := by
      simpa only [diagReadout] using
        (((e.contMDiffAt_iff (e.mem_source.2 hbase)).mp hbranchAt).2)
    exact hreadAt.contMDiffWithinAt
  refine ⟨hopen, hp, hsmooth, ?_⟩
  intro y hy
  exact ⟨B.right_inv hy.1, B.proj_eq hy.1, B.exp_eq hy.1⟩

end DiagInvBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
