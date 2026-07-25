import DifferentialGeometry.Geometry.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Geometry.Topology.UniversalCover.ChartPullback
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import Mathlib.Topology.Covering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs











open Set Function Filter Bundle
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric chartModelBasis)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor)
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M] [PseudoEMetricSpace M] [SecondCountableTopology M]







theorem isCoveringMap_fibre_finite_of_compact
    {X E : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace E] [CompactSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) :
    Finite (p ⁻¹' {x} : Set E) := by
  haveI hdisc : DiscreteTopology (p ⁻¹' {x} : Set E) :=
    (hp x).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {x} : Set E) :=
    isClosed_singleton.preimage hp.continuous
  haveI hcomp : CompactSpace (p ⁻¹' {x} : Set E) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact finite_of_compact_of_discrete








theorem action_eval_surjective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    Function.Surjective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e') := by
  intro e''
  obtain ⟨e'v, he'v⟩ := e'
  obtain ⟨e''v, he''v⟩ := e''
  have he' : p e'v = x := he'v
  subst he'
  have he'' : p e''v = p e'v := he''v
  obtain ⟨δ⟩ := PathConnectedSpace.joined e'v e''v
  set η : Path (p e'v) (p e'v) :=
    (δ.map hp.continuous).cast rfl he''.symm with hη_def
  refine ⟨Path.Homotopic.Quotient.mk η, ?_⟩
  apply Subtype.ext
  have hcomp_fun' : p ∘ (δ : unitInterval → E) = (η : unitInterval → X) := by
    funext t; rfl
  have hη_zero : (η : unitInterval → X) 0 = p e'v := η.source
  have hlift_eq :
      hp.liftPath (η : C(unitInterval, X)) e'v hη_zero = δ.toContinuousMap := by
    symm
    refine (hp.eq_liftPath_iff' hη_zero).mpr ⟨?_, δ.source⟩
    exact hcomp_fun'
  have hval :
      (hp.liftPath (η : C(unitInterval, X)) e'v hη_zero) 1 = e''v := by
    have := congrArg (fun f : C(unitInterval, E) => f 1) hlift_eq
    simpa using this.trans δ.target
  exact hval









theorem action_eval_injective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    Function.Injective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e') := by
  refine fun γ₁ γ₂ heq => ?_
  induction γ₁ using Path.Homotopic.Quotient.ind with | _ p₁ =>
  induction γ₂ using Path.Homotopic.Quotient.ind with | _ p₂ =>
  rw [Path.Homotopic.Quotient.eq]
  have he' : p (e' : E) = x := e'.2
  set Γ₁ : C(unitInterval, E) := hp.liftPath p₁.toContinuousMap (e' : E)
    (p₁.source.trans he'.symm) with hΓ₁
  set Γ₂ : C(unitInterval, E) := hp.liftPath p₂.toContinuousMap (e' : E)
    (p₂.source.trans he'.symm) with hΓ₂
  have hΓ₁_zero : Γ₁ 0 = (e' : E) := hp.liftPath_zero _ _ _
  have hΓ₂_zero : Γ₂ 0 = (e' : E) := hp.liftPath_zero _ _ _
  have hends : Γ₁ 1 = Γ₂ 1 := by
    have hmono : (hp.monodromy (Path.Homotopic.Quotient.mk p₁) e' : E) =
        (hp.monodromy (Path.Homotopic.Quotient.mk p₂) e' : E) :=
      congrArg Subtype.val heq
    change (Γ₁ : unitInterval → E) 1 = (Γ₂ : unitInterval → E) 1
    exact hmono
  let π₁ : Path (e' : E) (Γ₁ 1) :=
    { toContinuousMap := Γ₁
      source' := hΓ₁_zero
      target' := rfl }
  let π₂ : Path (e' : E) (Γ₁ 1) :=
    { toContinuousMap := Γ₂
      source' := hΓ₂_zero
      target' := hends.symm }
  obtain ⟨H⟩ : Path.Homotopic π₁ π₂ := SimplyConnectedSpace.paths_homotopic π₁ π₂
  have hΓ_rel : ContinuousMap.HomotopicRel Γ₁ Γ₂ {0, 1} := ⟨H⟩
  have hp_comp : ContinuousMap.HomotopicRel
      ((⟨p, hp.continuous⟩ : C(E, X)).comp Γ₁)
      ((⟨p, hp.continuous⟩ : C(E, X)).comp Γ₂) {0, 1} :=
    hΓ_rel.comp_continuousMap _
  have hp_eq₁ : (⟨p, hp.continuous⟩ : C(E, X)).comp Γ₁ = p₁.toContinuousMap := by
    ext t
    exact congr_fun (hp.liftPath_lifts _ _ _) t
  have hp_eq₂ : (⟨p, hp.continuous⟩ : C(E, X)).comp Γ₂ = p₂.toContinuousMap := by
    ext t
    exact congr_fun (hp.liftPath_lifts _ _ _) t
  rw [hp_eq₁, hp_eq₂] at hp_comp
  exact hp_comp






noncomputable def fibreEquivLoopQuotient
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ Path.Homotopic.Quotient x x :=
  (Equiv.ofBijective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e')
      ⟨action_eval_injective hp x e', action_eval_surjective hp x e'⟩).symm








noncomputable def fibreEquivFundamentalGroup
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ FundamentalGroup X x :=
  (fibreEquivLoopQuotient hp x e').trans
    { toFun := FundamentalGroup.fromPath
      invFun := FundamentalGroup.toPath
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
