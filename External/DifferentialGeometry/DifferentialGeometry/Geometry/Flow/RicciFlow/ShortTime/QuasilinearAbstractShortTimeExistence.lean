import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegSolutionJointlySmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRealizedSolutionFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem quasilinear_strictlyParabolic_2ndOrder_shortTimeExistence
    (F : SmoothRiemannianMetric I M → (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (ha_eq : a = 4 * Module.finrank ℝ E + 10)
    (Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a:ℝ)+2) → tensorHs (I := I) (M := M) g₀ 0 2 (a:ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S) δ), SmoothCcTensor g₀ 0 2)
    (_H0 : ∀ (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x), F g x v w = F g x w v)
    (_H1 : IsStrictlyParabolicMetricRHS (I := I) F g₀)
    {L : ℝ≥0} (hLipN : LipschitzWith L Nfun)
    (H2 : ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    (_H3 : IsSmoothQuasilinearMetricRHS (I := I) F)
    (hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S) δ) (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀ (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w
        = F (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w)
    (hForce : ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
        (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a Nfun hLipN H2).choose)
        (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
        (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
        (hforce : gforce =ᵐ[timeMeasure T]
          (fun t => Nfun (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
        (hgforce : ‖gforce‖ ≤ 1 / (16 * ((H2.choose : ℝ) + 1)))
        (htrace : timeH1.trace0 _ T u = 0),
      ∃ (d₂F : ℝ), 0 < d₂F ∧ d₂F ≤ T ∧
        ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ),
          (∀ i, ContDiff ℝ ∞ (f i)) ∧
          (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
            ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
              ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
                tensorSobolevWeight (I := I) (M := M) i τ *
                    (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
            tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
              perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) ∧
          ∃ (R₀ : ℝ), 0 < R₀ ∧
            (∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
              ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
                SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
                  tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Nat.cast_nonneg a) (timeH1.toFun u t) →
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀) ∧
            (∀ {T₁ : ℝ} (_hT₁_pos : 0 < T₁) (_hT₁_le : T₁ ≤ T)
                (_hT₁_le_d2F : T₁ ≤ d₂F)
                (Ffam : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
                (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
                  (ccTensorBilinSymm (I := I) g₀ (Ffam t)) δ)
                (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
                  SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Ffam t) =
                    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                      (Nat.cast_nonneg a) (timeH1.toFun u t))
                (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Ffam t)‖ ≤ R₀),
              ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
                f i t = tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                      (Nsec (Ffam t) hδ_lt (hδ t))) i)) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I) F g₀ T g_DT ∧ JointChartGramSmooth (I := I) T g_DT := by
  classical
  obtain ⟨_, hT₀pos, hsol⟩ := (quasilinear_maxreg_solution_of_nemytskii g₀ a Nfun hLipN H2).choose_spec
  set T : ℝ := min (quasilinear_maxreg_solution_of_nemytskii g₀ a Nfun hLipN H2).choose 1 with hT_def
  have hT_pos : 0 < T := lt_min hT₀pos one_pos
  have hT_le₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a Nfun hLipN H2).choose :=
    min_le_left _ _
  have hT_le1 : T ≤ 1 := min_le_right _ _
  obtain ⟨u, gforce, hduh, hforce, htrace, hderiv, hgforce⟩ := hsol hT_pos hT_le₀ hT_le1
  have hForce2 :
      ∃ (d₂F : ℝ), 0 < d₂F ∧ d₂F ≤ T ∧
        ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ),
          (∀ i, ContDiff ℝ ∞ (f i)) ∧
          (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
            ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
              ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
                tensorSobolevWeight (I := I) (M := M) i τ *
                    (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
            tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
              perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) ∧
          ∃ (R₀ : ℝ), 0 < R₀ ∧
            (∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
              ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
                SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
                  tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Nat.cast_nonneg a) (timeH1.toFun u t) →
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀) ∧
            (∀ {T₁ : ℝ} (hT₁_pos : 0 < T₁) (hT₁_le : T₁ ≤ T)
                (hT₁_le_d2F : T₁ ≤ d₂F)
                (Ffam : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
                (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
                  (ccTensorBilinSymm (I := I) g₀ (Ffam t)) δ)
                (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
                  SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Ffam t) =
                    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                      (Nat.cast_nonneg a) (timeH1.toFun u t))
                (hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Ffam t)‖ ≤ R₀),
              ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
                f i t = tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                      (Nsec (Ffam t) hδ_lt (hδ t))) i) :=
    hForce hT_pos hT_le1 hT_le₀ u gforce hduh hforce hgforce htrace
  obtain ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, R₀, hR₀pos, hHorizon, hForceRepr_fam⟩ :=
    hForce2
  obtain ⟨T₁, hT₁pos, hT₁le, F_fam, δ, hδ_lt, hδ, hF_zero, hF_pin, hF_flow, hF_joint⟩ :=
    maxreg_solution_jointly_smooth_representative_of_nemytskii g₀ a ha_super ha_eq Nfun F Nsec hRepr
      hT_pos hT_le1 u htrace hd₂F_pos hd₂F_le f hf_smooth hf_mass hf_id hR₀pos hHorizon hForceRepr_fam
  refine ⟨T₁, fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F_fam t) hδ_lt (hδ t), ⟨hT₁pos, ?_, ?_⟩, hF_joint⟩
  · refine smoothRiemannianMetric_ext_inner (fun x v w => ?_)
    rw [tensorSectionRealizeMetric_inner, hF_zero, ccTensorBilinSymm_zero_apply, add_zero]
  · intro t ht x v w
    have hcongr : (fun s : ℝ => (tensorSectionRealizeMetric (I := I) g₀ (F_fam s) hδ_lt (hδ s)).inner x v w) =
        fun s : ℝ => g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (F_fam s) x v w := by
      funext s; rw [tensorSectionRealizeMetric_inner]
    rw [hcongr]
    exact (hF_flow t ht x v w).const_add (g₀.inner x v w)

end DifferentialGeometry.PDE.RicciFlow
