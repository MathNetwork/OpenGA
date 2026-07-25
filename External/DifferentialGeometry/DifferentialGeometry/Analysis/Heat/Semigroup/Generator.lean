import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingSpectralLift
import DifferentialGeometry.Analysis.Elliptic.LichnerowiczSpectral

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

lemma oneMinusLapHeat_one_apply
    (g : SmoothRiemannianMetric I M) (t : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    oneMinusLapHeat (I := I) (M := M) g 1 t u =
      heatSemigroup (I := I) (M := M) g t u +
        heatPower (I := I) (M := M) g 1 t u := by
  rw [oneMinusLapHeat_apply]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, one_smul]
  rw [heatPower_zero (I := I) (M := M) g t]

lemma heatSemigroupExplicitLift_zero_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (t : ℝ)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 ∈
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomain_mem_iff]
  refine ⟨oneMinusLapHeat (I := I) (M := M) g 1 t u_0, ?_⟩
  unfold heatSemigroupExplicitLift
  rw [iteratedResolventL2_zero_apply]

set_option maxHeartbeats 800000 in

theorem laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    laplacianOp (I := I) (M := M) g
        ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
          heatSemigroupExplicitLift_zero_mem_laplacianDomain
            (I := I) (M := M) g t u_0⟩ =
      -(heatPower (I := I) (M := M) g 1 t u_0) := by
  set f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    oneMinusLapHeat (I := I) (M := M) g 1 t u_0 with hf_def
  have h_lift_eq :
      heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 =
        resolvent (I := I) (M := M) g f := by
    unfold heatSemigroupExplicitLift
    rw [iteratedResolventL2_zero_apply]
  rw [show (⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
        heatSemigroupExplicitLift_zero_mem_laplacianDomain
          (I := I) (M := M) g t u_0⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨resolvent (I := I) (M := M) g f,
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ from ?_]
  · rw [laplacianOp_resolvent (I := I) (M := M) g f]
    have h_H1 : H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g f) =
        heatSemigroup (I := I) (M := M) g t u_0 := by
      have := H1ComplToLp_heatSemigroupExplicitLift
        (I := I) (M := M) g 0 ht u_0
      rwa [h_lift_eq] at this
    rw [h_H1]
    rw [hf_def, oneMinusLapHeat_one_apply (I := I) (M := M) g t u_0]
    abel
  · apply Subtype.ext
    exact h_lift_eq

set_option maxHeartbeats 800000 in

theorem hasDerivAt_heatSemigroup_eq_laplacianOp
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    HasDerivAt (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (laplacianOp (I := I) (M := M) g
        ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
          heatSemigroupExplicitLift_zero_mem_laplacianDomain
            (I := I) (M := M) g t u_0⟩)
      t := by
  have h_op := hasDerivAt_heatSemigroup (I := I) (M := M) g ht
  have h_u_const : HasDerivAt (fun _ : ℝ => u_0) (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) t :=
    hasDerivAt_const t u_0
  have h_apply : HasDerivAt
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      ((-heatPower (I := I) (M := M) g 1 t) u_0 +
        heatSemigroup (I := I) (M := M) g t 0) t :=
    h_op.clm_apply h_u_const
  have h_simp :
      ((-heatPower (I := I) (M := M) g 1 t) u_0 +
        heatSemigroup (I := I) (M := M) g t 0) =
      -(heatPower (I := I) (M := M) g 1 t u_0) := by
    rw [(heatSemigroup (I := I) (M := M) g t).map_zero]
    rw [add_zero]
    rfl
  rw [h_simp] at h_apply
  rw [laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
    (I := I) (M := M) g ht u_0]
  exact h_apply

set_option maxHeartbeats 800000 in

lemma heatSemigroupSpectralLift_one_eq_explicit_zero
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 :
        H1Compl (I := I) (M := M) g) =
      heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 := by
  have h_can_mem_pow : heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 ∈
      laplacianDomainPow (I := I) (M := M) g 1 :=
    heatSemigroupSpectralLift_mem (I := I) (M := M) g ht u_0 1
  have h_can_mem : heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 ∈
      laplacianDomain (I := I) (M := M) g := by
    rw [← laplacianDomainPow_one (I := I) (M := M) g]
    exact h_can_mem_pow
  have h_exp_mem : heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 ∈
      laplacianDomain (I := I) (M := M) g :=
    heatSemigroupExplicitLift_zero_mem_laplacianDomain
      (I := I) (M := M) g t u_0
  have h_proj_eq :
      H1ComplToLp (I := I) (M := M) g
        (heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1) =
      H1ComplToLp (I := I) (M := M) g
        (heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0) := by
    rw [H1ComplToLp_heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1]
    rw [H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g 0 ht u_0]
  exact H1ComplToLp_inj_on_laplacianDomain (I := I) (M := M) g
    (u := ⟨_, h_can_mem⟩) (v := ⟨_, h_exp_mem⟩) h_proj_eq

set_option maxHeartbeats 800000 in

theorem laplacianOp_heatSemigroupSpectralLift_one_eq_neg_heatPower_one
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    laplacianOp (I := I) (M := M) g
        ⟨(heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 :
            H1Compl (I := I) (M := M) g),
          by
            rw [← laplacianDomainPow_one (I := I) (M := M) g]
            exact heatSemigroupSpectralLift_mem
              (I := I) (M := M) g ht u_0 1⟩ =
      -(heatPower (I := I) (M := M) g 1 t u_0) := by
  rw [show (⟨(heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 :
        H1Compl (I := I) (M := M) g),
        by
          rw [← laplacianDomainPow_one (I := I) (M := M) g]
          exact heatSemigroupSpectralLift_mem
            (I := I) (M := M) g ht u_0 1⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
        heatSemigroupExplicitLift_zero_mem_laplacianDomain
          (I := I) (M := M) g t u_0⟩ from ?_]
  · exact laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
      (I := I) (M := M) g ht u_0
  · apply Subtype.ext
    exact heatSemigroupSpectralLift_one_eq_explicit_zero
      (I := I) (M := M) g ht u_0

end HeatEquation
end Analysis
end DifferentialGeometry

end
