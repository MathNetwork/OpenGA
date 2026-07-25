import DifferentialGeometry.Analysis.Elliptic.Lichnerowicz
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound









noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




theorem scalar_hess_graph
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f),
      ∫ x, chartHessFrobeniusSq (I := I) g f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        (∫ x, (Δ_g (I := I) g hf x) ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        C * ∫ x, normGradSqFun (I := I) g f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  obtain ⟨C, hC, hRic⟩ := exists_ricci_bound (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro f hf
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let Hess : M → ℝ := fun x => chartHessFrobeniusSq (I := I) g f x
  let Ric : M → ℝ := fun x => ricciTensor (I := I) g x
    (gradFun (I := I) g f x) (gradFun (I := I) g f x)
  let Grad : M → ℝ := normGradSqFun (I := I) g f
  let LapSq : M → ℝ := fun x => (Δ_g (I := I) g hf x) ^ 2
  let Cross : M → ℝ := fun x => g.inner x
    (gradFun (I := I) g f x)
    (gradFun (I := I) g (Δ_g (I := I) g hf) x)
  have hΔf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (Δ_g (I := I) g hf) :=
    Δ_g_contMDiff (I := I) g hf
  have hHess_cont : Continuous Hess := by
    exact chartHessFrobeniusSq_continuous (I := I) g hf
  have hGrad_cont : Continuous Grad := by
    exact normGradSqFun_continuous (I := I) g hf
  have hLapSq_cont : Continuous LapSq := by
    exact hΔf.continuous.pow 2
  have hCross_cont : Continuous Cross := by
    let Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hf
    let GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hΔf
    have h := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g Gf GΔf
    simpa only [Cross, Gf, GΔf, grad_g_apply] using h
  have hRic_cont : Continuous Ric := by
    have hnormLap : Continuous
        (Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf)) :=
      (Δ_g_contMDiff (I := I) g
        (normGradSqFun_contMDiff (I := I) g hf)).continuous
    have heq : Ric = fun x =>
        (Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x -
          2 * Hess x - 2 * Cross x) / 2 := by
      funext x
      have hB := bochner_pointwise_concrete_metric_unconditional (I := I) g hf x
      dsimp only [Ric, Hess, Cross]
      linarith
    rw [heq]
    exact ((hnormLap.sub (continuous_const.mul hHess_cont)).sub
      (continuous_const.mul hCross_cont)).div_const 2
  have integrable_of_cont : ∀ {q : M → ℝ}, Continuous q → Integrable q μ := by
    intro q hq
    exact hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHess_int : Integrable Hess μ := integrable_of_cont hHess_cont
  have hRic_int : Integrable Ric μ := integrable_of_cont hRic_cont
  have hGrad_int : Integrable Grad μ := integrable_of_cont hGrad_cont
  have hLapSq_int : Integrable LapSq μ := integrable_of_cont hLapSq_cont
  have hCross_int : Integrable Cross μ := integrable_of_cont hCross_cont
  have hzero :
      ∫ x, Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x ∂μ = 0 := by
    exact integral_divergence_eq_zero_of_compact (I := I) g
      (grad_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf))
  have hbochner :
      ∫ x, Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x ∂μ =
        ∫ x, (2 * Hess x + 2 * Ric x + 2 * Cross x) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simpa only [Hess, Ric, Cross] using
      (bochner_pointwise_concrete_metric_unconditional (I := I) g hf x)
  have hmain :
      0 = 2 * (∫ x, Hess x ∂μ) + 2 * (∫ x, Ric x ∂μ) +
        2 * (∫ x, Cross x ∂μ) := by
    calc
      0 = ∫ x, Δ_g (I := I) g
          (normGradSqFun_contMDiff (I := I) g hf) x ∂μ := hzero.symm
      _ = ∫ x, (2 * Hess x + 2 * Ric x + 2 * Cross x) ∂μ := hbochner
      _ = 2 * (∫ x, Hess x ∂μ) + 2 * (∫ x, Ric x ∂μ) +
          2 * (∫ x, Cross x ∂μ) := by
        calc
          ∫ x, (2 * Hess x + 2 * Ric x + 2 * Cross x) ∂μ =
              (∫ x, 2 * Hess x + 2 * Ric x ∂μ) +
                ∫ x, 2 * Cross x ∂μ := by
            simpa only [Pi.add_apply] using
              (integral_add
                ((hHess_int.const_mul 2).add (hRic_int.const_mul 2))
                (hCross_int.const_mul 2))
          _ = ((∫ x, 2 * Hess x ∂μ) + ∫ x, 2 * Ric x ∂μ) +
                ∫ x, 2 * Cross x ∂μ := by
            rw [integral_add (hHess_int.const_mul 2) (hRic_int.const_mul 2)]
          _ = 2 * (∫ x, Hess x ∂μ) + 2 * (∫ x, Ric x ∂μ) +
                2 * (∫ x, Cross x ∂μ) := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hcross : ∫ x, Cross x ∂μ = -∫ x, LapSq x ∂μ := by
    calc
      ∫ x, Cross x ∂μ =
          ∫ x, g.inner x
            ((grad_g (I := I) g hΔf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            change g.inner x (gradFun (I := I) g f x)
                (gradFun (I := I) g (Δ_g (I := I) g hf) x) =
              g.inner x
                ((grad_g (I := I) g hΔf :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
                ((grad_g (I := I) g hf :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            rw [grad_g_apply, grad_g_apply]
            exact g.symm x _ _
      _ = -∫ x, (Δ_g (I := I) g hf x) * (Δ_g (I := I) g hf x) ∂μ :=
        green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
          (I := I) g hΔf hf (HasCompactSupport.of_compactSpace _)
      _ = -∫ x, LapSq x ∂μ := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [LapSq]
        ring
  have hbalance :
      ∫ x, Hess x ∂μ =
        (∫ x, LapSq x ∂μ) - ∫ x, Ric x ∂μ := by
    rw [hcross] at hmain
    linarith
  have hRic_lower : ∀ x : M, -C * Grad x ≤ Ric x := by
    intro x
    have hx := hRic x (gradFun (I := I) g f x)
    have hx' := (abs_le.mp hx).1
    calc
      -C * Grad x = -(C * normGradSqFun (I := I) g f x) := by
        simp only [Grad]
        ring
      _ ≤ Ric x := by
        simpa only [Ric, normGradSqFun_def] using hx'
  have hRic_int_lower :
      -C * (∫ x, Grad x ∂μ) ≤ ∫ x, Ric x ∂μ := by
    have hmono :
        (∫ x, -C * Grad x ∂μ) ≤ ∫ x, Ric x ∂μ :=
      integral_mono_ae (hGrad_int.const_mul (-C)) hRic_int
        (Filter.Eventually.of_forall hRic_lower)
    rwa [integral_const_mul] at hmono
  rw [show riemannianVolumeMeasure (I := I) (M := M) g = μ from rfl]
  change (∫ x, Hess x ∂μ) ≤
    (∫ x, LapSq x ∂μ) + C * ∫ x, Grad x ∂μ
  rw [hbalance]
  linarith

end Laplacian
end Analysis
end DifferentialGeometry

end
