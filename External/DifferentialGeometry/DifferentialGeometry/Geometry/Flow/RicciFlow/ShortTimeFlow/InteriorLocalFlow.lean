import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldFlowFamily
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.Glue
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Bijective
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ChartBridge








namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem interior_local_flow_existence
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hCont : ContinuousOn (Function.uncurry (fun t x => X_DT t x))
      (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X_DT t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X_DT t ((chartAt H α).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) :=
  time_dependent_vf_chart_local_picard_with_lipschitz (I := I) X_DT α hCont hLip

set_option linter.unusedVariables false in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartcover_orbit_is_bare_integral_curve
    (X : ℝ → ∀ x : M, TangentSpace I x) (hX : AutonomizedFieldJointC1 (I := I) X)
    (T : ℝ) (hT : 0 < T) (Φcc : ℝ → M → M)
    (hΦcc0 : ∀ x : M, Φcc 0 x = x)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hTle : ∀ α : M, T ≤ (hper α).T)
    (hrepr : ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧ ∀ s : ℝ, Φcc s x =
      (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s)))
    (hconf : ∀ x : M, ∀ α : M, x ∈ (hper α).U →
      ∀ t : ℝ, 0 < t → t < T →
        ((hper α).flow (I ((chartAt H α) x))) ⁻¹' (Set.range I) ∈
          𝓝[Set.Icc (0 : ℝ) (hper α).T] t)
    (htgt : ∀ x : M, ∀ α : M, x ∈ (hper α).U →
      ∀ t : ℝ, 0 < t → t < T →
        (hper α).flow (I ((chartAt H α) x)) t ∈ (extChartAt I α).target) :
    ∀ t : ℝ, 0 < t → t < T → ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
      (∀ s : ℝ, Φcc s x =
        (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φcc s x)
        (Set.Icc (0 : ℝ) (hper α).T) t
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
            ((hper α).flow (I ((chartAt H α) x)) t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φcc t x)))) := by
  intro t ht0 htT x
  obtain ⟨α, hxU, hΦrepr⟩ := hrepr x
  refine ⟨α, hxU, hΦrepr, ?_⟩
  set y : E := I ((chartAt H α) x) with hy
  have ht_Icc : t ∈ Set.Icc (0 : ℝ) (hper α).T :=
    ⟨ht0.le, (htT.le).trans (hTle α)⟩
  have hconf_t : ((hper α).flow y) ⁻¹' (Set.range I) ∈
      𝓝[Set.Icc (0 : ℝ) (hper α).T] t := hconf x α hxU t ht0 htT
  have htgt_t : (hper α).flow y t ∈ (extChartAt I α).target := htgt x α hxU t ht0 htT
  have hbridge :
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (chartAt H α).symm (I.symm ((hper α).flow y s)))
        (Set.Icc 0 (hper α).T) t
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
            ((hper α).flow y t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight
            (X t ((chartAt H α).symm (I.symm ((hper α).flow y t)))))) :=
    manifoldFlow_hasMFDerivWithinAt_of_chartLocal (I := I) X α x (hper α)
      hxU t ht_Icc hconf_t htgt_t
  have hcurve : (fun s : ℝ => Φcc s x) =
      fun s : ℝ => (chartAt H α).symm (I.symm ((hper α).flow y s)) := by
    funext s; rw [hΦrepr s]
  have hvel : (X t (Φcc t x) : E) =
      (X t ((chartAt H α).symm (I.symm ((hper α).flow y t))) : E) := by
    rw [hΦrepr t]
  rw [hcurve, hvel]
  exact hbridge









private structure ChartFlowEngineInputs
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (I := I) (fun t x => -(X t x)) α) where
  localFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target)
  localRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target)
  bijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x





private noncomputable def glueFlow
    (Y : ℝ → ∀ x : M, TangentSpace I x)
    (hperY : ∀ α : M, ChartLocalPicardData (I := I) Y α) : ℝ → M → M :=
  (time_dependent_vf_global_flow_glue (I := I) Y hperY).choose_spec.2.choose_spec.2.choose

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem glueFlow_spec
    (Y : ℝ → ∀ x : M, TangentSpace I x)
    (hperY : ∀ α : M, ChartLocalPicardData (I := I) Y α) :
    (∀ x : M, glueFlow (I := I) Y hperY 0 x = x) ∧
    (∀ x : M, ∃ α : M, x ∈ (hperY α).U ∧ ∀ s : ℝ,
      glueFlow (I := I) Y hperY s x =
        (chartAt H α).symm (I.symm ((hperY α).flow (I ((chartAt H α) x)) s))) := by
  have hspec :=
    (time_dependent_vf_global_flow_glue (I := I) Y hperY).choose_spec.2.choose_spec.2.choose_spec
  refine ⟨hspec.1, fun x => ?_⟩
  obtain ⟨α, _hαS, hxU, hrepr⟩ := hspec.2 x
  exact ⟨α, hxU, hrepr⟩





private noncomputable def flowBijectiveHorizon
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (I := I) (fun t x => -(X t x)) α)
    (hinputs : ChartFlowEngineInputs (I := I) X hper hperNeg) : ℝ :=
  chart_cover_flow_bijective_two_sided_uniform_horizon (I := I) X hper hperNeg
    (glueFlow (I := I) X hper) (glueFlow (I := I) (fun t x => -(X t x)) hperNeg)
    (glueFlow_spec (I := I) X hper).1 (glueFlow_spec (I := I) (fun t x => -(X t x)) hperNeg).1
    (fun x => let ⟨α, _, h⟩ := (glueFlow_spec (I := I) X hper).2 x; ⟨α, h⟩)
    (fun x => let ⟨α, _, h⟩ := (glueFlow_spec (I := I) (fun t x => -(X t x)) hperNeg).2 x; ⟨α, h⟩)
    (hinputs.bijPerChart (glueFlow (I := I) X hper)
      (glueFlow (I := I) (fun t x => -(X t x)) hperNeg)
      (glueFlow_spec (I := I) X hper).1 (glueFlow_spec (I := I) (fun t x => -(X t x)) hperNeg).1
      (fun x => let ⟨α, _, h⟩ := (glueFlow_spec (I := I) X hper).2 x; ⟨α, h⟩)
      (fun x => let ⟨α, _, h⟩ := (glueFlow_spec (I := I) (fun t x => -(X t x)) hperNeg).2 x;
        ⟨α, h⟩)) |>.choose

set_option linter.unusedVariables false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem interior_flow_uniqueness_glue
    (X : ℝ → ∀ x : M, TangentSpace I x) (hX : AutonomizedFieldJointC1 (I := I) X)
    (T : ℝ) (hT : 0 < T)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (I := I) (fun t x => -(X t x)) α)
    (hTle : ∀ α : M, T ≤ (hper α).T)
    (hTleNeg : ∀ α : M, T ≤ (hperNeg α).T)
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E)))
    (hinputs : ChartFlowEngineInputs (I := I) X hper hperNeg)
    (hThoriz : T ≤ flowBijectiveHorizon (I := I) X hper hperNeg hinputs)
    (hconf : ∀ x : M, ∀ α : M, x ∈ (hper α).U →
      ∀ t : ℝ, 0 < t → t < T →
        ((hper α).flow (I ((chartAt H α) x))) ⁻¹' (Set.range I) ∈
          𝓝[Set.Icc (0 : ℝ) (hper α).T] t)
    (htgt : ∀ x : M, ∀ α : M, x ∈ (hper α).U →
      ∀ t : ℝ, 0 < t → t < T →
        (hper α).flow (I ((chartAt H α) x)) t ∈ (extChartAt I α).target) :
    ∃ Φcc : ℝ → M → M, (∀ x : M, Φcc 0 x = x) ∧
      (∀ x : M, ∃ α : M, ∀ s : ℝ, Φcc s x =
        (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φcc t x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        (∀ s : ℝ, Φcc s x =
          (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φcc s x)
          (Set.Icc (0 : ℝ) (hper α).T) t
          ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
              ((hper α).flow (I ((chartAt H α) x)) t)) ∘L
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φcc t x))))) := by
  classical
  set Φ : ℝ → M → M := glueFlow (I := I) X hper with hΦ_def
  set Ψ : ℝ → M → M := glueFlow (I := I) (fun t x => -(X t x)) hperNeg with hΨ_def
  obtain ⟨hΦ0, hΦreprU⟩ := glueFlow_spec (I := I) X hper
  obtain ⟨hΨ0, hΨreprU⟩ := glueFlow_spec (I := I) (fun t x => -(X t x)) hperNeg
  have hΦrepr : ∀ x : M, ∃ α : M, ∀ s : ℝ, Φ s x =
      (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) :=
    fun x => let ⟨α, _, h⟩ := hΦreprU x; ⟨α, h⟩
  have hΨrepr : ∀ x : M, ∃ α : M, ∀ s : ℝ, Ψ s x =
      (chartAt H α).symm (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s)) :=
    fun x => let ⟨α, _, h⟩ := hΨreprU x; ⟨α, h⟩
  have hΦreprU' : ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧ ∀ s : ℝ, Φ s x =
      (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) := hΦreprU
  refine ⟨Φ, hΦ0, hΦrepr, ?_, ?_⟩
  · have hΦsmooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t) :=
      time_dependent_vf_flow_smooth_in_space X T hT Φ
        (hinputs.localFwd Φ T hT hΦreprU)
    have hΨreprU' : ∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧ ∀ s : ℝ, Ψ s x =
        (chartAt H α).symm (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s)) := hΨreprU
    have hΨsmooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t) :=
      time_dependent_vf_flow_smooth_in_space (fun t x => -(X t x)) T hT Ψ
        (hinputs.localRev Ψ T hT hΨreprU)
    have hbij := (chart_cover_flow_bijective_two_sided_uniform_horizon (I := I) X hper hperNeg
      Φ Ψ hΦ0 hΨ0 hΦrepr hΨrepr
      (hinputs.bijPerChart Φ Ψ hΦ0 hΨ0 hΦrepr hΨrepr)).choose_spec
    have hTbij_def : flowBijectiveHorizon (I := I) X hper hperNeg hinputs =
        (chart_cover_flow_bijective_two_sided_uniform_horizon (I := I) X hper hperNeg
          Φ Ψ hΦ0 hΨ0 hΦrepr hΨrepr
          (hinputs.bijPerChart Φ Ψ hΦ0 hΨ0 hΦrepr hΨrepr)).choose := rfl
    obtain ⟨_hTbij_pos, hΨΦ, hΦΨ⟩ := hbij
    have hΨΦ_T : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x := by
      intro s hs x
      exact hΨΦ s ⟨hs.1, lt_of_lt_of_le hs.2 (by rw [hTbij_def] at hThoriz; exact hThoriz)⟩ x
    have hΦΨ_T : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x := by
      intro s hs x
      exact hΦΨ s ⟨hs.1, lt_of_lt_of_le hs.2 (by rw [hTbij_def] at hThoriz; exact hThoriz)⟩ x
    intro t ht
    exact time_dependent_vf_hdiffeo_of_smooth_bijective Φ Ψ T
      hΦsmooth hΨsmooth hΨΦ_T hΦΨ_T t ht.1 ht.2
  · intro t ht x
    exact chartcover_orbit_is_bare_integral_curve X hX T hT Φ hΦ0 hper hTle
      hΦreprU' hconf htgt t ht.1 ht.2 x

end DifferentialGeometry.PDE.RicciFlow
