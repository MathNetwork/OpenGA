import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.TraceDiscrepancyDecomposition
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.SlotSplitParsevalBridge


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem riemannianFiberNormSq_three_eq_sum_slot0Curry
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (slot0Curry (I := I) (M := M) g x 2 e K₀
              ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a) := by
  exact riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g 2 x
    ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)


theorem riemannianFiberNormSq_three_le_of_slot0_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hsplit : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) =
      ∑ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (slot0Curry (I := I) (M := M) g x 2 e K₀
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a))
    (B : ℝ)
    (hbound : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (slot0Curry (I := I) (M := M) g x 2 e K₀
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a) ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤ (n : ℝ) * B := by
  classical
  rw [hsplit]
  calc
    (∑ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (slot0Curry (I := I) (M := M) g x 2 e K₀
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a))
        ≤ ∑ _a : Fin n, B := Finset.sum_le_sum (fun a _ => hbound a)
    _ = (n : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private noncomputable def secondCovGradEnergyBudget
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) : ℝ :=
  riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
    riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
      ((covGrad (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfnsBudget_nonneg
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    0 ≤ secondCovGradEnergyBudget (I := I) (M := M) g T₀ x := by
  unfold secondCovGradEnergyBudget
  have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x (T₀.toSection x)
  have h2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x
    ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)
  have h3 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (3 + 1) x
    ((covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
  linarith


theorem covGradRoughLapCurv_hpt_of_slot0_budget
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (D₀ : ℝ)
    (hbudget : ∀ x : M,
      ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
        n = Module.finrank ℝ (TangentSpace I x) ∧
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) =
          (∑ a : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (slot0Curry (I := I) (M := M) g x 2 e K₀
                ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a)) ∧
        ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (slot0Curry (I := I) (M := M) g x 2 e K₀
                ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a) ≤
            D₀ ^ 2 * secondCovGradEnergyBudget (I := I) (M := M) g T₀ x) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        (Real.sqrt (Module.finrank ℝ E) * D₀) ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)) := by
  classical
  intro x
  obtain ⟨n, e, K₀, hn, hsplit, hper⟩ := hbudget x
  have hle : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        (n : ℝ) * (D₀ ^ 2 * secondCovGradEnergyBudget (I := I) (M := M) g T₀ x) :=
    riemannianFiberNormSq_three_le_of_slot0_bound (I := I) (M := M) g T₀ x e K₀ hsplit
      (D₀ ^ 2 * secondCovGradEnergyBudget (I := I) (M := M) g T₀ x) hper
  have hn_E : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by
    rw [hn]; norm_cast
  have hsq : (Real.sqrt (Module.finrank ℝ E) * D₀) ^ 2 =
      (Module.finrank ℝ E : ℝ) * D₀ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hbud_eq : secondCovGradEnergyBudget (I := I) (M := M) g T₀ x =
      (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
          ((covGrad (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)) := rfl
  rw [hsq, ← hbud_eq]
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)
        ≤ (n : ℝ) * (D₀ ^ 2 * secondCovGradEnergyBudget (I := I) (M := M) g T₀ x) := hle
    _ = (Module.finrank ℝ E : ℝ) * D₀ ^ 2 * secondCovGradEnergyBudget (I := I) (M := M) g T₀ x := by
        rw [hn_E]; ring

end Connection
end Integral
end DifferentialGeometry

end
