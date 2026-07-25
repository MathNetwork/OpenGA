import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringOrdered
import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo

set_option autoImplicit false
set_option linter.style.longLine false






































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

section Glue

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [MetricSpace M] [Nonempty M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
  [SigmaCompactSpace N]







noncomputable def PreApproxIsoDataOn.congr {K : Set M} {ε : Real} {p : Nat} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hdata : PreApproxIsoDataOn (I := I) K ε p F g h)
    (hev : ∀ x ∈ K, F' =ᶠ[nhds x] F) :
    PreApproxIsoDataOn (I := I) K ε p F' g h where
  eps_pos := hdata.eps_pos
  eps_lt_one := hdata.eps_lt_one
  smoothOn := hdata.smoothOn.congr (fun x hx => (hev x hx).self_of_nhds)
  pullback := hdata.pullback
  pullback_apply := by
    intro x hx v
    rw [(hev x hx).self_of_nhds, (hev x hx).mfderiv_eq]
    exact hdata.pullback_apply x hx v
  c0_small := hdata.c0_small
  cov_deriv_small := hdata.cov_deriv_small









omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem stepB1_glue
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (Ok : M) (Oℓ : N) (r : Real) (ε : Real) (p : Nat)
    (U : Set M) (hU : IsOpen U) (hOkU : Ok ∈ U)
    (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M → N)
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U)
    (hbase : F Ok = Oℓ)
    (hfwd : PreApproxIsoDataOn (I := I) (Metric.closedBall Ok r) ε p F g h)
    (hrev : PreApproxIsoDataOn (I := I) (F '' Metric.closedBall Ok r) ε p
      (Function.invFunOn F U) h g) :
    ∃ Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (BookApproxIsoPartialData (I := I) (Metric.closedBall Ok r) ε p Phi g h) := by
  obtain ⟨Φ, hsrc, htgt, hEq⟩ := exists_diffeo_of_injOn hloc hU hinj
  have hclosed_sub : Metric.closedBall Ok r ⊆ Φ.source := by rw [hsrc]; exact hKU

  have hev_fwd : ∀ x ∈ Metric.closedBall Ok r, (Φ : M → N) =ᶠ[nhds x] F := fun x hx =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hx)) hEq
  have fwdΦ : PreApproxIsoDataOn (I := I) (Metric.closedBall Ok r) ε p (Φ : M → N) g h :=
    hfwd.congr hev_fwd

  have hsymmEq : Set.EqOn (Φ.symm : N → M) (Function.invFunOn F U) Φ.target := by
    intro z hz
    rw [htgt] at hz
    obtain ⟨x, hxU, rfl⟩ := hz
    have hΦx : (Φ : M → N) x = F x := hEq hxU
    have h1 : (Φ.symm : N → M) (F x) = x := by
      rw [← hΦx]; exact Φ.toPartialEquiv.left_inv (by rw [hsrc]; exact hxU)
    have h2 : Function.invFunOn F U (F x) = x := hinj.leftInvOn_invFunOn hxU
    rw [h1, h2]
  have hsetEq : (Φ : M → N) '' Metric.closedBall Ok r = F '' Metric.closedBall Ok r :=
    Set.EqOn.image_eq (fun x hx => hEq (hKU hx))
  have revΦ : PreApproxIsoDataOn (I := I) ((Φ : M → N) '' Metric.closedBall Ok r) ε p
      (Φ.symm : N → M) h g := by
    rw [hsetEq]
    refine hrev.congr (fun y hy => ?_)
    have hy_tgt : y ∈ Φ.target := by rw [htgt]; exact Set.image_mono hKU hy
    exact Filter.eventuallyEq_of_mem (Φ.open_target.mem_nhds hy_tgt) hsymmEq
  exact ⟨Φ, hclosed_sub, (hEq hOkU).trans hbase,
    ⟨{ source_sub := hclosed_sub, forward := fwdΦ, reverse := revΦ }⟩⟩

end Glue






structure StepB1RawInput (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) : Prop where
  comparison : ∀ (r : Real), 0 < r → ∀ (ε : Real), 0 < ε → ε < 1 → ∀ (p : Nat),
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      letI : Nonempty (X.obj k).M := ⟨(X.obj k).basepoint⟩
      ∃ (R : Real) (_ : r < R) (F : (X.obj k).M → (X.obj ℓ).M),
        IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F (Metric.ball (X.obj k).basepoint R) ∧
        Set.InjOn F (Metric.ball (X.obj k).basepoint R) ∧
        F (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PreApproxIsoDataOn (I := I) (Metric.closedBall (X.obj k).basepoint r) ε p F
          (X.obj k).metric (X.obj ℓ).metric) ∧
        Nonempty (PreApproxIsoDataOn (I := I) (F '' Metric.closedBall (X.obj k).basepoint r) ε p
          (Function.invFunOn F (Metric.ball (X.obj k).basepoint R))
          (X.obj ℓ).metric (X.obj k).metric)


















omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem stepB1_of_raw
    [FiniteDimensional Real E]
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P)
    (r : Real) (hr : 0 < r) (ε : Real) (hε : 0 < ε) (hε1 : ε < 1) (p : Nat) :
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Metric.closedBall (X.obj k).basepoint r ⊆ Phi.source ∧
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (BookApproxIsoPartialData (I := I)
          (Metric.closedBall (X.obj k).basepoint r)
          ε p Phi (X.obj k).metric (X.obj ℓ).metric) := by
  obtain ⟨k₀, hk₀⟩ := B.comparison r hr ε hε hε1 p
  refine ⟨k₀, fun k ℓ hk hl => ?_⟩
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
  letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
  letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
  letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
  letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
  letI : MetricSpace (X.obj k).M := (P k).ms
  letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
  haveI : Nonempty (X.obj k).M := ⟨(X.obj k).basepoint⟩
  obtain ⟨R, hRr, F, hloc, hinj, hbase, ⟨hfwd⟩, ⟨hrev⟩⟩ := hk₀ k ℓ hk hl
  have hR0 : (0 : Real) < R := lt_trans hr hRr
  have hU : IsOpen (Metric.ball (X.obj k).basepoint R) := by
    have hb := Metric.isOpen_ball (x := (X.obj k).basepoint) (ε := R)
    rwa [ProperMetricOn.top_eq (X.obj k) (P k)] at hb
  exact stepB1_glue (X.obj k).metric (X.obj ℓ).metric (X.obj k).basepoint (X.obj ℓ).basepoint
    r ε p (Metric.ball (X.obj k).basepoint R) hU (Metric.mem_ball_self hR0)
    (Metric.closedBall_subset_ball hRr) F hloc hinj hbase hfwd hrev

end HCGCompactness
end DifferentialGeometry
