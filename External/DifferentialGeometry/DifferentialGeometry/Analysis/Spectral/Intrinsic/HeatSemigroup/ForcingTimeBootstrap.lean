import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingCoordinateTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem deTurckForcing_smoothTimeCoordinateFieldSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothCoordinate_aeTimeJetSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce hgforce
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (a : ℝ) (Nat.cast_nonneg a)
  have hslab_sum : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (f i t) ^ 2) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)) (sq_nonneg _)
    · have := hB_le i t ht
      rwa [iteratedDeriv_zero] at this
  set F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) d₂ then
      ⟨fun i => f i t, hslab_sum t ht⟩ else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t := by
    intro t ht i
    simp only [hF_def, dif_pos ht]
  refine ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, ?_, hF_coeff⟩
  have hjoint : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ i, (gforce t).coeff i = f i t :=
    (MeasureTheory.ae_all_iff).2 hf_ae
  have hrestrict : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      t ∈ Set.Icc (0 : ℝ) d₂ :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hjoint, hrestrict] with t ht_eq ht_mem
  refine tensorHs.ext ?_
  funext i
  rw [ht_eq i, hF_coeff t ht_mem i]


theorem deTurckForcing_smoothTimeCoordinateFamilySymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) := by
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coeff⟩ :=
    deTurckForcing_smoothTimeCoordinateFieldSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce hgforce
  have hF_coord_cont : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂) := by
    intro i
    refine ContinuousOn.congr (f := fun t => f i t) ?_ ?_
    · exact (hf_smooth i).continuous.continuousOn
    · intro t ht
      exact hF_coeff t ht i
  exact ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
