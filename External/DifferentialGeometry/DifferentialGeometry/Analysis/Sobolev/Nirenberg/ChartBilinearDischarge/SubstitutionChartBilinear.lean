import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmoothChartBilinear
import DifferentialGeometry.Analysis.Sobolev.Solutions.Mollification
import DifferentialGeometry.Analysis.Sobolev.Approximation.H1WeakSolutionApprox


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeChartBilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma diffQuot_mul_apply
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (f g : EuclN → ℝ) (x : EuclN) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (fun y => f y * g y) x =
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h f x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h g x +
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h f x * g x :=
  DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply
    (d := Module.finrank ℝ E) k h f g x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma integral_F_diffQuot_neg_eq_neg_integral_diffQuot_F
    {F G : EuclN → ℝ} (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0)
    (hF_cont : Continuous F) (hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G)
    (hG_supp : HasCompactSupport G) :
    ∫ x, F x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) G x ∂(volume : Measure EuclN) =
      -∫ x, DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h F x * G x
        ∂(volume : Measure EuclN) := by
  have h_ibp :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution.integral_diffQuot_mul_eq_neg_integral_mul_diffQuot_locally_supported
      (d := Module.finrank ℝ E) (k := k) (f := F) (g := G) hh hF_cont
      hG_smooth hG_supp
  linarith [h_ibp]

end SubstitutionDischargeChartBilinear
end Sobolev
end Analysis
end DifferentialGeometry
