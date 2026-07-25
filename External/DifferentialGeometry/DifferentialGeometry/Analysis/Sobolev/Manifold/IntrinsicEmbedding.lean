import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

set_option autoImplicit false








namespace DifferentialGeometry.Analysis.Sobolev

noncomputable section

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff



theorem sobolev_intrinsic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M)
    {p : Real} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank Real E : Real)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        eLpNorm u
            (ENNReal.ofReal
              ((Module.finrank Real E : Real) * p /
                ((Module.finrank Real E : Real) - p)))
            (riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            (eLpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (gradFun (I := I) g u x)
                    (gradFun (I := I) g u x)))
                (ENNReal.ofReal p) (riemannianVolumeMeasure I M g)) := by
  classical
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have hp_enn : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cs, hCs, hs⟩ :=
    Chart.sobolev_closed (I := I) (M := M) g hp_one hp_dim
  obtain ⟨Cr, hCr, hr⟩ :=
    EquivalenceReverse.wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
      (I := I) (M := M) g hp_enn ENNReal.ofReal_ne_top
  refine ⟨Cs * Cr, mul_nonneg hCs hCr, ?_⟩
  intro u hu
  have hmem :
      Chart.MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u :=
    Equivalence.MemWkpChart_of_contMDiff (I := I) (M := M) g hp_enn hu
  calc
    eLpNorm u
          (ENNReal.ofReal
            ((Module.finrank Real E : Real) * p /
              ((Module.finrank Real E : Real) - p)))
          (riemannianVolumeMeasure I M g) ≤
        ENNReal.ofReal Cs *
          Chart.wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u :=
      hs hu.continuous.measurable hmem
    _ ≤ ENNReal.ofReal Cs *
        (ENNReal.ofReal Cr *
          (eLpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (gradFun (I := I) g u x)
                  (gradFun (I := I) g u x)))
              (ENNReal.ofReal p) (riemannianVolumeMeasure I M g))) :=
      mul_le_mul_right (hr hu) _
    _ = ENNReal.ofReal (Cs * Cr) *
        (eLpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (gradFun (I := I) g u x)
                (gradFun (I := I) g u x)))
            (ENNReal.ofReal p) (riemannianVolumeMeasure I M g)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hCs]


theorem sobolev_lpNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M)
    {p : Real} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank Real E : Real)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        lpNorm u
            (ENNReal.ofReal
              ((Module.finrank Real E : Real) * p /
                ((Module.finrank Real E : Real) - p)))
            (riemannianVolumeMeasure I M g) ≤
          C *
            (lpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
              lpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (gradFun (I := I) g u x)
                    (gradFun (I := I) g u x)))
                (ENNReal.ofReal p) (riemannianVolumeMeasure I M g)) := by
  classical
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure I M g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let q := ENNReal.ofReal
    ((Module.finrank Real E : Real) * p /
      ((Module.finrank Real E : Real) - p))
  obtain ⟨C, hC, hSob⟩ := sobolev_intrinsic (I := I) (M := M) g hp_one hp_dim
  refine ⟨C, hC, ?_⟩
  intro u hu
  let gradNorm : M -> Real := fun x => Real.sqrt
    (g.inner x
      (gradFun (I := I) g u x)
      (gradFun (I := I) g u x))
  have hgrad_cont : Continuous gradNorm := by
    have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (grad_g (I := I) g hu) (grad_g (I := I) g hu)
    exact Real.continuous_sqrt.comp (by
      simpa only [gradNorm, grad_g_apply] using hinner)
  have hu_mem : MemLp u (ENNReal.ofReal p) μ := by
    exact hu.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrad_mem : MemLp gradNorm (ENNReal.ofReal p) μ := by
    exact hgrad_cont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright_ne :
      ENNReal.ofReal C *
          (eLpNorm u (ENNReal.ofReal p) μ +
            eLpNorm gradNorm (ENNReal.ofReal p) μ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp)
      (ENNReal.add_ne_top.2
        ⟨hu_mem.eLpNorm_ne_top, hgrad_mem.eLpNorm_ne_top⟩)
  have hreal := ENNReal.toReal_mono hright_ne (hSob hu)
  simpa only [q, μ, gradNorm, ENNReal.toReal_mul, ENNReal.toReal_add,
      ENNReal.toReal_ofReal hC,
      ENNReal.toReal_add hu_mem.eLpNorm_ne_top hgrad_mem.eLpNorm_ne_top,
      toReal_eLpNorm hu.continuous.aestronglyMeasurable,
      toReal_eLpNorm hgrad_cont.aestronglyMeasurable] using hreal

end

end DifferentialGeometry.Analysis.Sobolev
