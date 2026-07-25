import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBoundClaims
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Claim1Wiring

set_option autoImplicit false
set_option linter.style.longLine false














noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]






omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem tower_bound_to_intrinsic
    (gRef : SmoothRiemannianMetric I M)
    (T T' : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) gRef y (hframe.toBasisAt hy)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (N : ℕ) (Cpp Cppp : Real)
    (hbound :
      compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T frame) N y) ≤
        Cpp * compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T' frame) N y) + Cppp) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
        (iterCov (I := I) gRef 2 T N y)) ≤
      Cpp * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
        (iterCov (I := I) gRef 2 T' N y)) + Cppp := by
  rw [← compL2_tower_eq (I := I) gRef T frame hframe hu hy hinv N,
    ← compL2_tower_eq (I := I) gRef T' frame hframe hu hy hinv N]
  exact hbound













omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem aN_intrinsic_point
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    (hframeS : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) g) frame hframe y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y d i j) u)
    (hgsm : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g) frame y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, frameComp0S (I := I) (metricTensorField (I := I) g) frame x
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 : Real) (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (hRicSm : ∀ k : Fin 2 → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I)
        (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
          (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
        frame y k) u)
    (N : ℕ) (hN : 1 ≤ N)
    (Kg : Real) (hKg0 : 0 ≤ Kg)
    (hgB : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ N - 1 →
      compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j x) ≤ Kg)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : ∀ z ∈ u, ∀ s : ℕ, s ≤ N →
      compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
        (frameComp0S (I := I)
          (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
            (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
          frame) s z) ≤ KShi)
    {y : M} (hy : y ∈ u)
    (hinvON : Tensor0SBundle.MetricInverseInBasis (I := I) gRef y (hframe.toBasisAt hy)
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ∃ Cpp Cppp : Real, 0 ≤ Cpp ∧ 0 ≤ Cppp ∧
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
        (iterCov (I := I) gRef 2
          (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
            (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
          N y)) ≤
        Cpp * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
          (iterCov (I := I) gRef 2 (metricTensorField (I := I) g) N y)) + Cppp := by
  classical

  have hBd : ∀ c : ℕ, ∃ Bc, 0 ≤ Bc ∧ (c < N - 1 → ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (chrDiffField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')) c z) ≤ Bc) := by
    intro c
    by_cases hc : c < N - 1
    · obtain ⟨C, hC0, hCb⟩ := claim1_LC hu gRef frame hframe hframeS hchrH
        C0 Kg c
      have hCb' := hCb g hchrG hgsm Ginv hinv hGinv
        (fun x hx j h1 h2 => hgB x hx j h1 (by omega))
      refine ⟨C * (1 + Kg), mul_nonneg hC0 (by linarith), fun _ z hz => ?_⟩
      have hg := hgB z hz (c + 1) (by omega) (by omega)
      have hcb := hCb' z hz
      have hgnn := compL2_nonneg (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) (c + 1) z)
      nlinarith [hC0, hg, hcb, hgnn]
    · exact ⟨0, le_rfl, fun h => absurd h hc⟩
  choose B hB0 hBb using hBd

  obtain ⟨Ctop, hCtop0, htopGen⟩ := claim1_LC hu gRef frame hframe hframeS hchrH
    C0 Kg (N - 1)
  have htop := htopGen g hchrG hgsm Ginv hinv hGinv
    (fun x hx j h1 h2 => hgB x hx j h1 h2)
  have hDtop : ∀ x ∈ u,
      compL2 (iterCovCompU (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (chrDiffField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')) (N - 1) x) ≤
        Ctop * (1 + compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) (metricTensorField (I := I) g) frame) N x)) := by
    intro x hx
    have h := htop x hx
    rwa [show N - 1 + 1 = N from by omega] at h

  obtain ⟨Cpp, Cppp, hpp0, hppp0, hcompGen⟩ := aN_component (r₀ := 2) (rg := 2)
    hu frame
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
    hframeS hchrH N hN B hB0 Ctop hCtop0 KShi hKShi0
  have hcomp := hcompGen
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
    hchrG
    (frameComp0S (I := I)
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
        (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
      frame)
    hRicSm (fun c hc z hz => hBb c hc z hz)
    (frameComp0S (I := I) (metricTensorField (I := I) g) frame) hDtop hShi
  exact ⟨Cpp, Cppp, hpp0, hppp0,
    tower_bound_to_intrinsic gRef
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
        (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
      (metricTensorField (I := I) g) frame hframe hu hy hinvON N Cpp Cppp (hcomp y hy)⟩

end DifferentialGeometry.PDE.RicciFlow
