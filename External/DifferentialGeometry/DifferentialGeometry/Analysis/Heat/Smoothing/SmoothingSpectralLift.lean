import DifferentialGeometry.Analysis.Heat.Smoothing.HeatSemigroupIteratedDomain

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem heatSemigroup_in_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 k

noncomputable def heatSemigroupSpectralLift
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    H1Compl (I := I) (M := M) g :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose

theorem heatSemigroupSpectralLift_mem
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k ∈
      laplacianDomainPow (I := I) (M := M) g k :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose_spec.1

theorem H1ComplToLp_heatSemigroupSpectralLift
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    H1ComplToLp (I := I) (M := M) g
        (heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k) =
      heatSemigroup (I := I) (M := M) g t u_0 :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose_spec.2

noncomputable def heatSemigroupExplicitLift
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (iteratedResolventL2 (I := I) (M := M) g k
      (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0))

theorem heatSemigroupExplicitLift_mem
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupExplicitLift (I := I) (M := M) g k t u_0 ∈
      laplacianDomainPow (I := I) (M := M) g (k + 1) := by
  unfold heatSemigroupExplicitLift
  rw [laplacianDomainPow_succ_mem_iff]
  exact ⟨oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0, rfl⟩

theorem H1ComplToLp_heatSemigroupExplicitLift
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    H1ComplToLp (I := I) (M := M) g
        (heatSemigroupExplicitLift (I := I) (M := M) g k t u_0) =
      heatSemigroup (I := I) (M := M) g t u_0 := by
  unfold heatSemigroupExplicitLift
  rw [show H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k
            (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0))) =
      resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k
          (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0)) from
    (resolventL2_apply (I := I) (M := M) g _).symm]
  rw [show resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k
          (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0)) =
      iteratedResolventL2 (I := I) (M := M) g (k + 1)
        (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0) from
    (iteratedResolventL2_succ_apply (I := I) (M := M) g k _).symm]
  exact iteratedResolventL2_oneMinusLapHeat_apply (I := I) (M := M) g (k + 1) ht u_0

theorem heatSemigroup_in_laplacianDomainPow_succ_explicit
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1) ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  ⟨heatSemigroupExplicitLift (I := I) (M := M) g k t u_0,
    heatSemigroupExplicitLift_mem (I := I) (M := M) g k t u_0,
    H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g k ht u_0⟩

example (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  heatSemigroup_in_laplacianDomainPow (I := I) (M := M) g ht u_0 k

example (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k ∈
      laplacianDomainPow (I := I) (M := M) g k :=
  heatSemigroupSpectralLift_mem (I := I) (M := M) g ht u_0 k

example (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupExplicitLift (I := I) (M := M) g k t u_0 ∈
      laplacianDomainPow (I := I) (M := M) g (k + 1) :=
  heatSemigroupExplicitLift_mem (I := I) (M := M) g k t u_0

end HeatEquation
end Analysis
end DifferentialGeometry

end
