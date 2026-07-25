import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl_H1_0
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.StandardNirenbergTest
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient
import DifferentialGeometry.Analysis.Sobolev.Solutions.Mollification


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace NirenbergCrossBound

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
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_diffQuot_restrict_le_of_cthickening
    {Ω'' K : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (_hΩ''_compact_closure : IsCompact (closure Ω''))
    (hK_meas : MeasurableSet K)
    {w : EuclN → ℝ} (hw_l2 : MemLp w 2 ((volume : Measure EuclN).restrict K))
    (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| (closure Ω'') ⊆ K) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h w) 2
        ((volume : Measure EuclN).restrict Ω'') ≤
      (2 / ENNReal.ofReal |h|) *
        eLpNorm w 2 ((volume : Measure EuclN).restrict K) := by
  classical
  set w_ext : EuclN → ℝ := K.indicator w with hw_ext_def
  have hw_ext_aesm : AEStronglyMeasurable w_ext (volume : Measure EuclN) := by
    rw [hw_ext_def]
    exact (aestronglyMeasurable_indicator_iff hK_meas).mpr hw_l2.aestronglyMeasurable
  have hw_ext_eLpNorm :
      eLpNorm w_ext 2 (volume : Measure EuclN) =
        eLpNorm w 2 ((volume : Measure EuclN).restrict K) := by
    rw [hw_ext_def]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hK_meas]
  have h_dq_eq_on_Ω'' : ∀ x ∈ Ω'',
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h w_ext x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h w x := by
    intro x hx
    have hx_in_clos : x ∈ closure Ω'' := subset_closure hx
    have hx_in_cthick : x ∈ Metric.cthickening |h| (closure Ω'') :=
      Metric.self_subset_cthickening _ hx_in_clos
    have hx_in_K : x ∈ K := h_thick hx_in_cthick
    set y : EuclN := x + h • EuclideanSpace.single k 1 with hy_def
    have h_dist_y_x : dist y x = |h| := by
      have h_diff : y - x = h • EuclideanSpace.single k 1 := by
        rw [hy_def]; abel
      have heq : dist y x = ‖y - x‖ := by rw [dist_eq_norm]
      rw [heq, h_diff, norm_smul]
      have hsing_norm :
          ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing_norm, mul_one, Real.norm_eq_abs]
    have hy_in_cthick : y ∈ Metric.cthickening |h| (closure Ω'') :=
      Metric.mem_cthickening_of_dist_le y x |h| _ hx_in_clos (le_of_eq h_dist_y_x)
    have hy_in_K : y ∈ K := h_thick hy_in_cthick
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh w_ext x,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh w x]
    rw [hw_ext_def, Set.indicator_of_mem hy_in_K, Set.indicator_of_mem hx_in_K]
  have hΩ''_meas : MeasurableSet Ω'' := hΩ''_open.measurableSet
  have h_eq_eLpNorm :
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h w) 2
          ((volume : Measure EuclN).restrict Ω'') =
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h w_ext) 2
          ((volume : Measure EuclN).restrict Ω'') := by
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' hΩ''_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact (h_dq_eq_on_Ω'' x hx).symm
  rw [h_eq_eLpNorm]
  have h_le_global :
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h w_ext) 2
          ((volume : Measure EuclN).restrict Ω'') ≤
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h w_ext) 2
          (volume : Measure EuclN) :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  refine h_le_global.trans ?_
  have h_dq_eq_pointwise :
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h w_ext =
      fun x => h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext x - w_ext x) := by
    funext x
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh w_ext x]
    change (w_ext (x + h • EuclideanSpace.single k 1) - w_ext x) / h =
      h⁻¹ * (w_ext (x + h • EuclideanSpace.single k 1) - w_ext x)
    field_simp
  rw [h_dq_eq_pointwise]
  have h_pull_const :
      (fun x => h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext x - w_ext x)) =
      (fun x => h⁻¹ * ((DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext - w_ext) x)) := by
    funext x; rfl
  rw [h_pull_const]
  have h_const_pull :
      eLpNorm
          (fun x => h⁻¹ * ((DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h w_ext - w_ext) x)) 2
          (volume : Measure EuclN) =
        ENNReal.ofReal |h⁻¹| *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h w_ext - w_ext) 2
            (volume : Measure EuclN) := by
    have h_eq : (fun x => h⁻¹ * ((DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext - w_ext) x)) =
        h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h w_ext - w_ext) := by
      funext x; rw [Pi.smul_apply, smul_eq_mul]
    rw [h_eq, eLpNorm_const_smul]
    simp [Real.enorm_eq_ofReal_abs]
  rw [h_const_pull]
  have hτ_aesm :
      AEStronglyMeasurable
        (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h w_ext) (volume : Measure EuclN) := by
    have hMP : MeasurePreserving
        (fun x : EuclN => x + h • EuclideanSpace.single k 1) volume volume :=
      measurePreserving_add_right volume _
    exact hw_ext_aesm.comp_measurePreserving hMP
  have h_minkowski :
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext - w_ext) 2
        (volume : Measure EuclN) ≤
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h w_ext) 2 (volume : Measure EuclN) +
          eLpNorm w_ext 2 (volume : Measure EuclN) :=
    eLpNorm_sub_le hτ_aesm hw_ext_aesm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hτ_eLpNorm :
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext) 2 (volume : Measure EuclN) =
        eLpNorm w_ext 2 (volume : Measure EuclN) := by
    have hMP : MeasurePreserving
        (fun x : EuclN => x + h • EuclideanSpace.single k 1) volume volume :=
      measurePreserving_add_right volume _
    have h_eq : DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext =
      w_ext ∘ (fun x : EuclN => x + h • EuclideanSpace.single k 1) := rfl
    rw [h_eq]
    exact eLpNorm_comp_measurePreserving hw_ext_aesm hMP
  rw [hτ_eLpNorm] at h_minkowski
  have h_two : eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h w_ext - w_ext) 2
        (volume : Measure EuclN) ≤ 2 * eLpNorm w_ext 2 (volume : Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_inv_abs : |h⁻¹| = |h|⁻¹ := abs_inv h
  have h_ofReal_inv : ENNReal.ofReal |h⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  rw [h_ofReal_inv]
  rw [hw_ext_eLpNorm] at h_two
  calc (ENNReal.ofReal |h|)⁻¹ *
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h w_ext - w_ext) 2 (volume : Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ *
          (2 * eLpNorm w 2 ((volume : Measure EuclN).restrict K)) := by
        gcongr
    _ = 2 / ENNReal.ofReal |h| *
          eLpNorm w 2 ((volume : Measure EuclN).restrict K) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

end NirenbergCrossBound
end Laplacian
end Analysis
end DifferentialGeometry
