import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSSmoothQuasilinear
import DifferentialGeometry.Geometry.Flow.LieDerivativeChartFrameIdentity


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartFrameVec_eq_chartBasisVecFiber
    (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    chartFrameVec (I := I) α i b = chartBasisVecFiber (I := I) α i b := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartLieDerivMetricMatrix_eq_lieDerivMetric_chartFrame
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ∀ x ∈ chartLeviCivitaGoodSet (I := I) α,
      chartLieDerivMetricMatrix (I := I) g W α i j x =
        lieDerivMetric (I := I) g W x
          (chartFrameVec (I := I) α i x)
          (chartFrameVec (I := I) α j x) :=
  DifferentialGeometry.PDE.DeTurck.chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis
    (I := I) g W α i j

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieDerivMetric_pairing_contMDiff
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lieDerivMetric (I := I) g W b (Y b) (Z b)) := by
  classical
  intro b₀
  set e := trivializationAt E (TangentSpace I : M → Type _) b₀ with he_def
  have h_baseSet_eq :
      (trivializationAt E (TangentSpace I) b₀).baseSet = (chartAt H b₀).source :=
    TangentBundle.trivializationAt_baseSet (I := I) b₀
  have hb₀_chartSrc : b₀ ∈ (chartAt H b₀).source := mem_chart_source H b₀
  have hb₀_baseSet : b₀ ∈ e.baseSet := by
    rw [he_def, h_baseSet_eq]; exact hb₀_chartSrc
  have h_chart_open : IsOpen ((chartAt H b₀).source) :=
    (chartAt H b₀).open_source
  have h_chart_nhd : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    h_chart_open.mem_nhds hb₀_chartSrc
  have h_coeffY : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (chartCoeff (I := I) b₀ Y i) (chartAt H b₀).source := by
    intro i
    have h := chartCoeff_contMDiffOn (I := I) b₀ Y i
    rwa [h_baseSet_eq] at h
  have h_coeffZ : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (chartCoeff (I := I) b₀ Z j) (chartAt H b₀).source := by
    intro j
    have h := chartCoeff_contMDiffOn (I := I) b₀ Z j
    rwa [h_baseSet_eq] at h
  have h_pair :
      ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            lieDerivMetric (I := I) g W b
              (chartFrameVec (I := I) b₀ i b) (chartFrameVec (I := I) b₀ j b))
          (chartAt H b₀).source := fun i j =>
    liederivmetric_chart_component_smooth_in_g_w_input (I := I) g W b₀ i j
  have h_decomp : ∀ b ∈ (chartAt H b₀).source,
      lieDerivMetric (I := I) g W b (Y b) (Z b) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartCoeff (I := I) b₀ Y i b *
              chartCoeff (I := I) b₀ Z j b *
              lieDerivMetric (I := I) g W b
                (chartFrameVec (I := I) b₀ i b)
                (chartFrameVec (I := I) b₀ j b) := by
    intro b hb_chart
    have hb_baseSet : b ∈ e.baseSet := by
      rw [he_def, h_baseSet_eq]; exact hb_chart
    have hY_decomp : Y b =
        ∑ i, chartCoeff (I := I) b₀ Y i b •
          chartBasisVecFiber (I := I) b₀ i b :=
      chartCoeff_recompose (I := I) b₀ Y hb_baseSet
    have hZ_decomp : Z b =
        ∑ j, chartCoeff (I := I) b₀ Z j b •
          chartBasisVecFiber (I := I) b₀ j b :=
      chartCoeff_recompose (I := I) b₀ Z hb_baseSet
    set B : TangentSpace I b →ₗ[ℝ] TangentSpace I b →ₗ[ℝ] ℝ :=
      lieDerivMetric (I := I) g W b with hB_def
    rw [hY_decomp]
    rw [map_sum]
    have h_smul_left : ∀ i,
        B (chartCoeff (I := I) b₀ Y i b •
            chartBasisVecFiber (I := I) b₀ i b) =
          chartCoeff (I := I) b₀ Y i b •
            B (chartBasisVecFiber (I := I) b₀ i b) := by
      intro i; rw [LinearMap.map_smul]
    simp_rw [h_smul_left, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hZ_decomp]
    rw [map_sum]
    simp_rw [LinearMap.map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [show chartFrameVec (I := I) b₀ i b = chartBasisVecFiber (I := I) b₀ i b from rfl,
        show chartFrameVec (I := I) b₀ j b = chartBasisVecFiber (I := I) b₀ j b from rfl]
    ring
  have h_summand_smooth :
      ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            chartCoeff (I := I) b₀ Y i b *
              chartCoeff (I := I) b₀ Z j b *
              lieDerivMetric (I := I) g W b
                (chartFrameVec (I := I) b₀ i b)
                (chartFrameVec (I := I) b₀ j b))
          (chartAt H b₀).source := by
    intro i j
    exact ((h_coeffY i).mul (h_coeffZ j)).mul (h_pair i j)
  have h_sum_smooth :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b : M =>
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartCoeff (I := I) b₀ Y i b *
                chartCoeff (I := I) b₀ Z j b *
                lieDerivMetric (I := I) g W b
                  (chartFrameVec (I := I) b₀ i b)
                  (chartFrameVec (I := I) b₀ j b))
        (chartAt H b₀).source := by
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    exact contMDiffOn_finset_sum (fun j _ => h_summand_smooth i j)
  have h_pair_on_chart :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b : M => lieDerivMetric (I := I) g W b (Y b) (Z b))
        (chartAt H b₀).source :=
    h_sum_smooth.congr (fun b hb => h_decomp b hb)
  exact (h_pair_on_chart b₀ hb₀_chartSrc).contMDiffAt h_chart_nhd

end RicciFlow
end PDE
end DifferentialGeometry
