import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.GreenFull
import DifferentialGeometry.Geometry.Boundary.SecondFundamentalForm
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.BoundaryLaplacian

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private local instance instMeasurableSpaceM : MeasurableSpace M := borel M

private local instance instBorelSpaceM :
    @BorelSpace M _ (borel M) := letI : MeasurableSpace M := borel M; ⟨rfl⟩

private local instance instMeasurableSpaceModel :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _

private local instance instBorelSpaceModel :
    @BorelSpace (EuclideanSpace ℝ (Fin n)) _ (borel _) := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem reilly_identity
    (g : SmoothRiemannianMetric (I_half n) M)
    {f : M → ℝ} (hf : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ f)
    (h_normGradSq_smooth :
      ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞
        (normGradSqFun (I := I_half n) g f))
    (νChart : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (bdryGrad :
      BoundaryManifold (I_half n) M →
        HasSmoothBoundary.boundaryE
          (E := EuclideanSpace ℝ (Fin n)) (H := EuclideanHalfSpace n)
          (I := I_half n))
    (bdryLap : BoundaryManifold (I_half n) M → ℝ)
    (boundaryNormalDeriv : BoundaryManifold (I_half n) M → ℝ)
    (h_bochner : ∀ x : M,
      Δ_g_classical (M := M) (n := n) g h_normGradSq_smooth x =
        2 * frobeniusSqFun (I := I_half n) (M := M)
              (hessFun (I := I_half n) g f) x +
          2 * ricciFun (I := I_half n) g x
                (gradFun (I := I_half n) g f x)
                (gradFun (I := I_half n) g f x) +
          2 * g.inner x
                (gradFun (I := I_half n) g f x)
                (gradFun (I := I_half n) g
                  (Δ_g_classical (M := M) (n := n) g hf) x))
    (h_div_thm_normGradSq :
      ∫ x, Δ_g_classical (M := M) (n := n) g h_normGradSq_smooth x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        ∫ x : BoundaryManifold (I_half n) M,
          g.inner x.val
            (outwardNormal (I := I_half n) (M := M) g x :
              TangentSpace _ x.val)
            (gradFun (I := I_half n) g
              (normGradSqFun (I := I_half n) g f) x.val)
          ∂(surfaceMeasure (I := I_half n) (M := M) g))
    (h_green_lap :
      ∫ x, (Δ_g_classical (M := M) (n := n) g hf x)^2
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) +
        ∫ x, g.inner x
              (gradFun (I := I_half n) g
                (Δ_g_classical (M := M) (n := n) g hf) x)
              (gradFun (I := I_half n) g f x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        ∫ x : BoundaryManifold (I_half n) M,
          (Δ_g_classical (M := M) (n := n) g hf) x.val *
            g.inner x.val
              (outwardNormal (I := I_half n) (M := M) g x :
                TangentSpace _ x.val)
              (gradFun (I := I_half n) g f x.val)
          ∂(surfaceMeasure (I := I_half n) (M := M) g))
    (h_normalDeriv :
      ∀ x : BoundaryManifold (I_half n) M,
        boundaryNormalDeriv x =
          g.inner x.val
            (outwardNormal (I := I_half n) (M := M) g x :
              TangentSpace _ x.val)
            (gradFun (I := I_half n) g f x.val))
    (h_codazzi_boundary :
      ∫ x : BoundaryManifold (I_half n) M,
        g.inner x.val
          (outwardNormal (I := I_half n) (M := M) g x :
            TangentSpace _ x.val)
          (gradFun (I := I_half n) g
            (normGradSqFun (I := I_half n) g f) x.val)
        ∂(surfaceMeasure (I := I_half n) (M := M) g) =
      2 * (∫ x : BoundaryManifold (I_half n) M,
              (Δ_g_classical (M := M) (n := n) g hf) x.val *
                boundaryNormalDeriv x
              ∂(surfaceMeasure (I := I_half n) (M := M) g)) -
      2 * (∫ x : BoundaryManifold (I_half n) M,
              secondFundamentalFormBoundary (I := I_half n) (M := M) g x νChart
                (bdryGrad x) (bdryGrad x)
              ∂(surfaceMeasure (I := I_half n) (M := M) g)) +
      4 * (∫ x : BoundaryManifold (I_half n) M,
              boundaryNormalDeriv x * bdryLap x
              ∂(surfaceMeasure (I := I_half n) (M := M) g)))
    (h_int_hess :
      Integrable (fun x : M =>
        frobeniusSqFun (I := I_half n) (M := M)
          (hessFun (I := I_half n) g f) x)
        (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (h_int_ric :
      Integrable (fun x : M =>
        ricciFun (I := I_half n) g x
          (gradFun (I := I_half n) g f x)
          (gradFun (I := I_half n) g f x))
        (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (h_int_innerGradΔ :
      Integrable (fun x : M =>
        g.inner x
          (gradFun (I := I_half n) g f x)
          (gradFun (I := I_half n) g
            (Δ_g_classical (M := M) (n := n) g hf) x))
        (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (h_int_lap_sq :
      Integrable (fun x : M =>
        (Δ_g_classical (M := M) (n := n) g hf x)^2)
        (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    ∫ x, ((Δ_g_classical (M := M) (n := n) g hf x)^2 -
            frobeniusSqFun (I := I_half n) (M := M)
              (hessFun (I := I_half n) g f) x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
      ∫ x, ricciFun (I := I_half n) g x
              (gradFun (I := I_half n) g f x)
              (gradFun (I := I_half n) g f x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) +
        (∫ x : BoundaryManifold (I_half n) M,
            secondFundamentalFormBoundary (I := I_half n) (M := M) g x νChart
              (bdryGrad x) (bdryGrad x)
            ∂(surfaceMeasure (I := I_half n) (M := M) g)) -
        2 * (∫ x : BoundaryManifold (I_half n) M,
              boundaryNormalDeriv x * bdryLap x
              ∂(surfaceMeasure (I := I_half n) (M := M) g)) := by
  classical
  set μ : Measure M := riemannianVolumeMeasure (I := I_half n) (M := M) g with hμ_def
  set σ : Measure (BoundaryManifold (I_half n) M) :=
    surfaceMeasure (I := I_half n) (M := M) g with hσ_def
  set HessSq : M → ℝ :=
    fun x => frobeniusSqFun (I := I_half n) (M := M)
      (hessFun (I := I_half n) g f) x with hHessSq_def
  set Ric : M → ℝ :=
    fun x => ricciFun (I := I_half n) g x
      (gradFun (I := I_half n) g f x)
      (gradFun (I := I_half n) g f x) with hRic_def
  set GfGdf : M → ℝ :=
    fun x => g.inner x
      (gradFun (I := I_half n) g f x)
      (gradFun (I := I_half n) g
        (Δ_g_classical (M := M) (n := n) g hf) x) with hGfGdf_def
  set DivNGS : M → ℝ :=
    Δ_g_classical (M := M) (n := n) g h_normGradSq_smooth with hDivNGS_def
  set LapSq : M → ℝ :=
    fun x => (Δ_g_classical (M := M) (n := n) g hf x)^2 with hLapSq_def
  set BdryNGS : BoundaryManifold (I_half n) M → ℝ :=
    fun x =>
      g.inner x.val
        (outwardNormal (I := I_half n) (M := M) g x :
          TangentSpace _ x.val)
        (gradFun (I := I_half n) g
          (normGradSqFun (I := I_half n) g f) x.val) with hBdryNGS_def
  set BdryLapNorm : BoundaryManifold (I_half n) M → ℝ :=
    fun x =>
      (Δ_g_classical (M := M) (n := n) g hf) x.val * boundaryNormalDeriv x
      with hBdryLapNorm_def
  set BdryLapNu : BoundaryManifold (I_half n) M → ℝ :=
    fun x =>
      (Δ_g_classical (M := M) (n := n) g hf) x.val *
        g.inner x.val
          (outwardNormal (I := I_half n) (M := M) g x :
            TangentSpace _ x.val)
          (gradFun (I := I_half n) g f x.val) with hBdryLapNu_def
  set BdryII : BoundaryManifold (I_half n) M → ℝ :=
    fun x =>
      secondFundamentalFormBoundary (I := I_half n) (M := M) g x νChart
        (bdryGrad x) (bdryGrad x) with hBdryII_def
  set BdryNormLap : BoundaryManifold (I_half n) M → ℝ :=
    fun x => boundaryNormalDeriv x * bdryLap x with hBdryNormLap_def
  set IH : ℝ := ∫ x, HessSq x ∂μ with hIH_def
  set IR : ℝ := ∫ x, Ric x ∂μ with hIR_def
  set IG : ℝ := ∫ x, GfGdf x ∂μ with hIG_def
  set ID : ℝ := ∫ x, DivNGS x ∂μ with hID_def
  set IL : ℝ := ∫ x, LapSq x ∂μ with hIL_def
  set JN : ℝ := ∫ x, BdryNGS x ∂σ with hJN_def
  set JL : ℝ := ∫ x, BdryLapNu x ∂σ with hJL_def
  set JLn : ℝ := ∫ x, BdryLapNorm x ∂σ with hJLn_def
  set JII : ℝ := ∫ x, BdryII x ∂σ with hJII_def
  set JM : ℝ := ∫ x, BdryNormLap x ∂σ with hJM_def
  have h_bochner_int : ID = 2 * IH + 2 * IR + 2 * IG := by
    have h_eq : ∀ x : M, DivNGS x = 2 * HessSq x + 2 * Ric x + 2 * GfGdf x := by
      intro x
      exact h_bochner x
    have h_int_eq :
        ∫ x, DivNGS x ∂μ =
          ∫ x, (2 * HessSq x + 2 * Ric x + 2 * GfGdf x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall h_eq)
    have h_int_2H : Integrable (fun x => 2 * HessSq x) μ :=
      h_int_hess.const_mul 2
    have h_int_2R : Integrable (fun x => 2 * Ric x) μ :=
      h_int_ric.const_mul 2
    have h_int_2G : Integrable (fun x => 2 * GfGdf x) μ :=
      h_int_innerGradΔ.const_mul 2
    have h_int_2H2R : Integrable (fun x => 2 * HessSq x + 2 * Ric x) μ :=
      h_int_2H.add h_int_2R
    have h_split :
        ∫ x, (2 * HessSq x + 2 * Ric x + 2 * GfGdf x) ∂μ =
          (∫ x, 2 * HessSq x ∂μ) + (∫ x, 2 * Ric x ∂μ) +
            (∫ x, 2 * GfGdf x ∂μ) := by
      rw [integral_add h_int_2H2R h_int_2G,
          integral_add h_int_2H h_int_2R]
    have hp1 : ∫ x, 2 * HessSq x ∂μ = 2 * IH := by
      rw [hIH_def]; exact integral_const_mul _ _
    have hp2 : ∫ x, 2 * Ric x ∂μ = 2 * IR := by
      rw [hIR_def]; exact integral_const_mul _ _
    have hp3 : ∫ x, 2 * GfGdf x ∂μ = 2 * IG := by
      rw [hIG_def]; exact integral_const_mul _ _
    calc ID
        = ∫ x, DivNGS x ∂μ := hID_def
      _ = ∫ x, (2 * HessSq x + 2 * Ric x + 2 * GfGdf x) ∂μ := h_int_eq
      _ = (∫ x, 2 * HessSq x ∂μ) + (∫ x, 2 * Ric x ∂μ) +
            (∫ x, 2 * GfGdf x ∂μ) := h_split
      _ = 2 * IH + 2 * IR + 2 * IG := by rw [hp1, hp2, hp3]
  have h_divthm : ID = JN := by
    rw [hID_def, hJN_def]
    exact h_div_thm_normGradSq
  have h_green : IL + IG = JL := by
    rw [hIL_def, hIG_def, hJL_def]
    have h_swap : ∀ x : M,
        g.inner x
          (gradFun (I := I_half n) g
            (Δ_g_classical (M := M) (n := n) g hf) x)
          (gradFun (I := I_half n) g f x) =
        g.inner x
          (gradFun (I := I_half n) g f x)
          (gradFun (I := I_half n) g
            (Δ_g_classical (M := M) (n := n) g hf) x) := by
      intro x; exact g.symm x _ _
    have h_swap_int :
        ∫ x, g.inner x
              (gradFun (I := I_half n) g
                (Δ_g_classical (M := M) (n := n) g hf) x)
              (gradFun (I := I_half n) g f x) ∂μ =
          ∫ x, g.inner x
                (gradFun (I := I_half n) g f x)
                (gradFun (I := I_half n) g
                  (Δ_g_classical (M := M) (n := n) g hf) x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall h_swap)
    have h_green_full := h_green_lap
    rw [h_swap_int] at h_green_full
    exact h_green_full
  have h_lap_nu_eq : JL = JLn := by
    rw [hJL_def, hJLn_def]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    change (Δ_g_classical (M := M) (n := n) g hf) x.val *
        g.inner x.val
          (outwardNormal (I := I_half n) (M := M) g x :
            TangentSpace _ x.val)
          (gradFun (I := I_half n) g f x.val) =
      (Δ_g_classical (M := M) (n := n) g hf) x.val * boundaryNormalDeriv x
    rw [h_normalDeriv x]
  have h_codazzi_packed : JN = 2 * JLn - 2 * JII + 4 * JM := by
    rw [hJN_def, hJLn_def, hJII_def, hJM_def]
    exact h_codazzi_boundary
  have h_main : IL - IH = IR + JII - 2 * JM := by
    have h_IG_eq : IG = JLn - IL := by linarith [h_green, h_lap_nu_eq]
    have h_combined : ID = 2 * IH + 2 * IR + 2 * (JLn - IL) := by
      rw [h_bochner_int, h_IG_eq]
    have h_JN_eq : JN = 2 * IH + 2 * IR + 2 * (JLn - IL) := by
      rw [← h_divthm]; exact h_combined
    linarith [h_codazzi_packed, h_JN_eq]
  have h_lhs : ∫ x, ((Δ_g_classical (M := M) (n := n) g hf x)^2 -
              frobeniusSqFun (I := I_half n) (M := M)
                (hessFun (I := I_half n) g f) x) ∂μ = IL - IH := by
    rw [integral_sub h_int_lap_sq h_int_hess]
  rw [h_lhs]
  have h_rhs :
      (∫ x, ricciFun (I := I_half n) g x
              (gradFun (I := I_half n) g f x)
              (gradFun (I := I_half n) g f x) ∂μ +
        (∫ x : BoundaryManifold (I_half n) M,
            secondFundamentalFormBoundary (I := I_half n) (M := M) g x νChart
              (bdryGrad x) (bdryGrad x) ∂σ) -
        2 * (∫ x : BoundaryManifold (I_half n) M,
              boundaryNormalDeriv x * bdryLap x ∂σ)) =
      IR + JII - 2 * JM := by
    rw [hIR_def, hJII_def, hJM_def]
  rw [h_rhs]
  exact h_main

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
