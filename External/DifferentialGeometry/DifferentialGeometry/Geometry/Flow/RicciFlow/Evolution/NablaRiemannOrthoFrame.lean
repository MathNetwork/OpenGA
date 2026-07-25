import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false













































































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]













section GenericFrame

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]




def nabla3InnerSlotsF
    (frame : Idx → (x : M) → TangentSpace I x) (x : M)
    (d₂ : Idx) (m : Fin 4 → Idx) :
    Fin 5 → TangentSpace I x :=
  Fin.cons (frame d₂ x) (frameTuple (I := I) frame x m)




def nabla3FrameTupleF
    (frame : Idx → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : Idx) (m : Fin 4 → Idx) :
    Fin 7 → TangentSpace I x :=
  metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
    (nabla3InnerSlotsF (I := I) frame x d₂ m)





def nablaLapCommReactionTermF
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (a b c : Idx) (m : Fin 4 → Idx) :
    Real :=
  (nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ a b c m) -
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ a c b m)) +
    curvatureAction0SAt (I := I) (S.base.rm13 t) (nablaRm04Field (I := I) S t x₀)
      (frame a x₀) (frame c x₀)
      (nabla3InnerSlotsF (I := I) frame x₀ b m)





omit [Fintype Idx] [DecidableEq Idx] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapCommF_pointwise
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (a b c : Idx) (m : Fin 4 → Idx) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTupleF (I := I) frame x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTupleF (I := I) frame x₀ c a b m) =
      nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a b c m := by
  classical
  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S hS t x₀
      (frame a x₀) (frame c x₀)
      (nabla3InnerSlotsF (I := I) frame x₀ b m)
  rw [nablaLapCommReactionTermF]
  simp only [nabla3FrameTupleF, nabla3InnerSlotsF] at hR2 ⊢
  linarith [hR2]




def roughLapNablaRmCompF
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (c : Idx) (m : Fin 4 → Idx) :
    Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ a b c m)




def nablaRoughLapRmCompF
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (c : Idx) (m : Fin 4 → Idx) :
    Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ c a b m)




omit [DecidableEq Idx] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapCommF_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (c : Idx) (m : Fin 4 → Idx) :
    roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame gInv c m -
        nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame gInv c m =
      ∑ a : Idx, ∑ b : Idx,
        gInv a b * nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a b c m := by
  classical
  rw [roughLapNablaRmCompF, nablaRoughLapRmCompF]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_sub, nablaLapCommF_pointwise (I := I) S hS t x₀ frame a b c m]









omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapCommF_orthonormalTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (horth : ∀ i j : Idx, gInv i j = if i = j then 1 else 0)
    (c : Idx) (m : Fin 4 → Idx) :
    roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame gInv c m -
        nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame gInv c m =
      ∑ a : Idx,
        nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m := by
  classical
  rw [nablaLapCommF_trace (I := I) S hS t x₀ frame gInv c m]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, one_mul]
  · intro b _ hb
    rw [horth a b, if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

end GenericFrame










section OrthonormalFrame















omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem exists_orthoFrameAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric t).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) := by
  classical

  set g := S.family.metric t with hg_def
  let cd : InnerProductSpace.Core Real (TangentSpace I x₀) := g.toRiemannianMetric.toCore x₀
  have hc : ContinuousAt (fun v : TangentSpace I x₀ => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x₀
  have hbnd : Bornology.IsVonNBounded Real {v : TangentSpace I x₀ |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x₀
  letI nag : NormedAddCommGroup (TangentSpace I x₀) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace Real (TangentSpace I x₀) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank Real (TangentSpace I x₀) with hn_def
  set e : OrthonormalBasis (Fin n) Real (TangentSpace I x₀) :=
    stdOrthonormalBasis Real (TangentSpace I x₀) with he_def

  have hinner_eq : ∀ u v : TangentSpace I x₀, (inner Real u v : Real) = g.inner x₀ u v :=
    fun u v => rfl

  refine ⟨n, fun i _x => e i, ?_⟩
  intro i j
  have horth : Orthonormal Real (fun i : Fin n => e i) := e.orthonormal
  have hite := (orthonormal_iff_ite (𝕜 := Real) (E := TangentSpace I x₀)).mp horth i j
  rw [← hinner_eq (e i) (e j)]
  simpa using hite

end OrthonormalFrame













section Adapter



def deltaInvMetric {Idx : Type*} [DecidableEq Idx] :
    Real → DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx :=
  fun _ _ i j => if i = j then 1 else 0

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem deltaInvMetric_apply {Idx : Type*} [DecidableEq Idx]
    (t : Real) (x : M) (i j : Idx) :
    deltaInvMetric (M := M) (Idx := Idx) t x i j = if i = j then 1 else 0 := rfl




omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem deltaInvMetric_orthonormal {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (t : Real) (x : M) :
    InverseMetricOrthonormalAt (M := M) (Idx := Idx) (deltaInvMetric (M := M)) t x := by
  intro i j; rfl

























omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_orthoFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric (t : Real)).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) ∧
      InverseMetricOrthonormalAt (M := M) (Idx := Fin n)
        (deltaInvMetric (M := M)) (t : Real) x₀ ∧
      ∀ (c : Fin n) (m : Fin 4 → Fin n),
        roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m =
          ∑ a : Fin n,
            nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m := by
  classical
  obtain ⟨n, frame, horthFrame⟩ := exists_orthoFrameAt (I := I) S (t : Real) x₀
  refine ⟨n, frame, horthFrame, deltaInvMetric_orthonormal (M := M) (t : Real) x₀, ?_⟩
  intro c m
  exact nablaLapCommF_orthonormalTrace (I := I) S hS t x₀ frame
    (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀)
    (fun i j => rfl) c m

end Adapter











































end DifferentialGeometry.PDE.RicciFlow
