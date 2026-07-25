import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs


noncomputable section

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem tensorL2Inner_symm
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s S T =
      tensorL2Inner (I := I) (M := M) g r s T S := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s x (S x) (T x)


theorem tensorL2Inner_add_left
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : M → TensorRSModel r s ℝ E)
    (h₁ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S₁ x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (h₂ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S₂ x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂) T =
      tensorL2Inner (I := I) (M := M) g r s S₁ T +
        tensorL2Inner (I := I) (M := M) g r s S₂ T := by
  unfold tensorL2Inner
  have hcongr : (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x ((S₁ + S₂) x) (T x)) =
    (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S₁ x) (T x) +
        tensorInnerPointwise (I := I) (M := M) g r s x (S₂ x) (T x)) := by
    funext x
    have := tensorInnerPointwise_add_left (I := I) (M := M) g r s x
      (S₁ x) (S₂ x) (T x)
    change tensorInnerPointwise (I := I) (M := M) g r s x (S₁ x + S₂ x) (T x) =
      tensorInnerPointwise (I := I) (M := M) g r s x (S₁ x) (T x) +
        tensorInnerPointwise (I := I) (M := M) g r s x (S₂ x) (T x)
    exact this
  rw [hcongr]
  exact MeasureTheory.integral_add h₁ h₂


theorem tensorL2Inner_add_right
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : M → TensorRSModel r s ℝ E)
    (h₁ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₁ x))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (h₂ : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₂ x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Inner (I := I) (M := M) g r s S (T₁ + T₂) =
      tensorL2Inner (I := I) (M := M) g r s S T₁ +
        tensorL2Inner (I := I) (M := M) g r s S T₂ := by
  unfold tensorL2Inner
  have hcongr : (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) ((T₁ + T₂) x)) =
    (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₁ x) +
        tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₂ x)) := by
    funext x
    have := tensorInnerPointwise_add_right (I := I) (M := M) g r s x
      (S x) (T₁ x) (T₂ x)
    change tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₁ x + T₂ x) =
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₁ x) +
        tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T₂ x)
    exact this
  rw [hcongr]
  exact MeasureTheory.integral_add h₁ h₂


theorem tensorL2Inner_smul_left
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s (c • S) T =
      c * tensorL2Inner (I := I) (M := M) g r s S T := by
  unfold tensorL2Inner
  have hcongr : (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x ((c • S) x) (T x)) =
    (fun x =>
      c * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) := by
    funext x
    have := tensorInnerPointwise_smul_left (I := I) (M := M) g r s x c
      (S x) (T x)
    change tensorInnerPointwise (I := I) (M := M) g r s x (c • S x) (T x) =
      c * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
    exact this
  rw [hcongr, MeasureTheory.integral_const_mul]


theorem tensorL2Inner_smul_right
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s S (c • T) =
      c * tensorL2Inner (I := I) (M := M) g r s S T := by
  unfold tensorL2Inner
  have hcongr : (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) ((c • T) x)) =
    (fun x =>
      c * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) := by
    funext x
    have := tensorInnerPointwise_smul_right (I := I) (M := M) g r s x c
      (S x) (T x)
    change tensorInnerPointwise (I := I) (M := M) g r s x (S x) (c • T x) =
      c * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
    exact this
  rw [hcongr, MeasureTheory.integral_const_mul]


theorem tensorL2Inner_zero_left
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s
      (fun _ : M => (0 : TensorRSModel r s ℝ E)) T = 0 := by
  unfold tensorL2Inner
  have hzero :
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
          ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x) (T x))
        = (fun _ : M => (0 : ℝ)) := by
    funext x
    exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x (T x)
  rw [hzero]
  exact MeasureTheory.integral_zero M ℝ


theorem tensorL2Inner_zero_right
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    tensorL2Inner (I := I) (M := M) g r s S
      (fun _ : M => (0 : TensorRSModel r s ℝ E)) = 0 := by
  unfold tensorL2Inner
  have hzero :
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
          (S x) ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x))
        = (fun _ : M => (0 : ℝ)) := by
    funext x
    exact tensorInnerPointwise_zero_right (I := I) (M := M) g r s x (S x)
  rw [hzero]
  exact MeasureTheory.integral_zero M ℝ


theorem tensorL2Inner_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    0 ≤ tensorL2Inner (I := I) (M := M) g r s S S := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_nonneg ?_
  intro x
  exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x (S x)


theorem MemL2.integrable_inner_of_aestronglyMeasurable
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : M → TensorRSModel r s ℝ E}
    (hS : MemL2 (I := I) (M := M) g r s S)
    (hT : MemL2 (I := I) (M := M) g r s T)
    (hST_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  set F : M → ℝ := fun x =>
    tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
  set G : M → ℝ := fun x =>
    (1 / 2 : ℝ) * (tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
      tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
  have hG_integrable : MeasureTheory.Integrable G
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h_sum : MeasureTheory.Integrable (fun x =>
        tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hS.add hT
    exact h_sum.const_mul (1 / 2 : ℝ)
  have h_bound : ∀ x : M, ‖F x‖ ≤ G x := by
    intro x
    set a := tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x)
    set b := tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
    set c := tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)
    have ha : 0 ≤ a := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x (S x)
    have hc : 0 ≤ c := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x (T x)
    have hb_sq : b ^ 2 ≤ a * c :=
      tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r s x (S x) (T x)
    have habs : |b| ≤ Real.sqrt (a * c) := by
      have h1 : |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      rw [h1]
      exact Real.sqrt_le_sqrt hb_sq
    have hAMGM : Real.sqrt (a * c) ≤ (a + c) / 2 := by
      have hsq_a : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
      have hsq_c : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
      have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
      have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
      have hexpand : (Real.sqrt a - Real.sqrt c) ^ 2 =
          a + c - 2 * (Real.sqrt a * Real.sqrt c) := by
        have hpow := sq_nonneg (Real.sqrt a - Real.sqrt c)
        nlinarith [hsq_a, hsq_c]
      have hkey : 0 ≤ a + c - 2 * (Real.sqrt a * Real.sqrt c) := by
        rw [← hexpand]
        exact sq_nonneg _
      have hprod : Real.sqrt a * Real.sqrt c = Real.sqrt (a * c) :=
        (Real.sqrt_mul ha c).symm
      rw [hprod] at hkey
      linarith
    have hF_norm : ‖F x‖ = |b| := by
      change ‖b‖ = |b|
      exact Real.norm_eq_abs b
    rw [hF_norm]
    have hGx : G x = (1 / 2 : ℝ) * (a + c) := rfl
    calc |b| ≤ Real.sqrt (a * c) := habs
      _ ≤ (a + c) / 2 := hAMGM
      _ = (1 / 2 : ℝ) * (a + c) := by ring
      _ = G x := hGx.symm
  refine MeasureTheory.Integrable.mono' hG_integrable hST_meas ?_
  exact Filter.Eventually.of_forall h_bound


theorem MemL2.add
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : M → TensorRSModel r s ℝ E}
    (hS : MemL2 (I := I) (M := M) g r s S)
    (hT : MemL2 (I := I) (M := M) g r s T)
    (hST_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemL2 (I := I) (M := M) g r s (S + T) := by
  have hST : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    MemL2.integrable_inner_of_aestronglyMeasurable
      (I := I) (M := M) hS hT hST_meas
  have hTS : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (T x) (S x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hsymm :
        (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (T x) (S x)) =
        (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) := by
      funext x
      exact (tensorInnerPointwise_symm (I := I) (M := M) g r s x (T x) (S x))
    rw [hsymm]
    exact hST
  have hsum : MeasureTheory.Integrable
      (fun x =>
        tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
            tensorInnerPointwise (I := I) (M := M) g r s x (T x) (S x) +
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    ((hS.integrable_inner_self.add hST).add hTS).add hT.integrable_inner_self
  have hexpand : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g r s x ((S + T) x) ((S + T) x) =
        tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
            tensorInnerPointwise (I := I) (M := M) g r s x (T x) (S x) +
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x) := by
    intro x
    change tensorInnerPointwise (I := I) (M := M) g r s x (S x + T x) (S x + T x) =
      _
    rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
        tensorInnerPointwise_add_right]
    ring
  change MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x ((S + T) x) ((S + T) x))
      (riemannianVolumeMeasure (I := I) (M := M) g)
  have hcongr :
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x ((S + T) x) ((S + T) x)) =
      (fun x =>
        tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
            tensorInnerPointwise (I := I) (M := M) g r s x (T x) (S x) +
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)) :=
    funext (fun x => hexpand x)
  rw [hcongr]
  exact hsum


theorem MemL2.smul
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : ℝ) {S : M → TensorRSModel r s ℝ E}
    (hS : MemL2 (I := I) (M := M) g r s S) :
    MemL2 (I := I) (M := M) g r s (c • S) := by
  unfold MemL2
  have hexpand : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g r s x ((c • S) x) ((c • S) x) =
        (c * c) *
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) := by
    intro x
    change tensorInnerPointwise (I := I) (M := M) g r s x (c • S x) (c • S x) =
      _
    rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
    ring
  have hcongr :
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x ((c • S) x) ((c • S) x)) =
      (fun x => (c * c) *
        tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x)) := by
    funext x; exact hexpand x
  rw [hcongr]
  exact hS.const_mul (c * c)

end L2
end Integral
end DifferentialGeometry

end
