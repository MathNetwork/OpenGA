import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.NonlinearitySpectral

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def DuhamelMildSolutionData (g : SmoothRiemannianMetric I M) (a : ℝ) (T : ℝ)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (N_cont : tensorHs (I := I) (M := M) g 0 2 (a + 1) →
      tensorHs (I := I) (M := M) g 0 2 a)
    (R : ℝ)
    (gtraj : ℝ → tensorHs (I := I) (M := M) g 0 2 a) : Prop :=
  ∃ (Te : ℝ) (hT : 0 < T) (hTe : T ≤ Te) (hTe1 : Te ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) Te),
    ContinuousOn N_cont
      (Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (a + 1) ≤ a + 2 by linarith)
          (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2))) R) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show a ≤ a + 2 by linarith) (u₂ s)
        = timeH1.toFun
            (maxRegDuhamelMap (I := I) (M := M) a (lt_of_lt_of_le hT hTe) hTe1
              (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) gforce) s) ∧
    (gforce =ᵐ[timeMeasure Te]
      (fun t => N_cont (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a
        (lt_of_lt_of_le hT hTe) hTe1
        (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) gforce t))) ∧
    (∀ᵐ t ∂(timeMeasure Te),
      maxRegDuhamelSolFieldHa1 (I := I) (M := M) a (lt_of_lt_of_le hT hTe) hTe1
          (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) gforce t ∈
        Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (a + 1) ≤ a + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2))) R) ∧
    ((gforce : ℝ → tensorHs (I := I) (M := M) g 0 2 a)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] gtraj)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem DuhamelMildSolutionData.mono {g : SmoothRiemannianMetric I M} {a : ℝ} {T T' : ℝ}
    {u₂ : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2)}
    {N_cont : tensorHs (I := I) (M := M) g 0 2 (a + 1) →
      tensorHs (I := I) (M := M) g 0 2 a}
    {R : ℝ} {gtraj : ℝ → tensorHs (I := I) (M := M) g 0 2 a}
    (hTT' : T' ≤ T) (hT' : 0 < T')
    (h : DuhamelMildSolutionData (I := I) (M := M) g a T u₂ N_cont R gtraj) :
    DuhamelMildSolutionData (I := I) (M := M) g a T' u₂ N_cont R gtraj := by
  obtain ⟨Te, _hT, hTe, hTe1, gforce, hN_cont, hid, hforce, hball, htraj⟩ := h
  refine ⟨Te, hT', le_trans hTT' hTe, hTe1, gforce, hN_cont,
    fun s hs => hid s ⟨hs.1, le_trans hs.2 hTT'⟩, hforce, hball, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl hTT') htraj

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem DuhamelMildSolutionData.congr_gtraj {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    {u₂ : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2)}
    {N_cont : tensorHs (I := I) (M := M) g 0 2 (a + 1) →
      tensorHs (I := I) (M := M) g 0 2 a}
    {R : ℝ} {gtraj gtraj' : ℝ → tensorHs (I := I) (M := M) g 0 2 a}
    (hg : gtraj =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] gtraj')
    (h : DuhamelMildSolutionData (I := I) (M := M) g a T u₂ N_cont R gtraj) :
    DuhamelMildSolutionData (I := I) (M := M) g a T u₂ N_cont R gtraj' := by
  obtain ⟨Te, hT, hTe, hTe1, gforce, hN_cont, hid, hforce, hball, htraj⟩ := h
  exact ⟨Te, hT, hTe, hTe1, gforce, hN_cont, hid, hforce, hball, htraj.trans hg⟩

theorem deTurckRemainder_strong_shortTime_exists
    (g_bg : SmoothRiemannianMetric I M) {a : ℝ}
    {N : tensorHs (I := I) (M := M) g_bg 0 2 (a + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 < R)
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => N (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              a hT hT1 u₀ gforce t)) ∧
          timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                (show a ≤ a + 2 by linarith) u₀ ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR.le hN)
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) ∧
          ∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t ∈
              Metric.closedBall
                (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                  (show (a + 1) ≤ a + 2 by linarith) u₀) R :=
  quasilinear_strong_existence_locallyLipschitz_smallTime_stayDischarged_ofCompact
    (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (a := a)
    (N := N) (L_R := L_R) (R := R) hR
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
    u₀ hN

theorem firstOrderRemainderCLM_strong_shortTime_exists
    (g_bg : SmoothRiemannianMetric I M) {a : ℝ}
    (R : tensorHs (I := I) (M := M) g_bg 0 2 (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g_bg 0 2 a)
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 (a + 2)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => R (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              a hT hT1 u₀ gforce t)) ∧
          timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                (show a ≤ a + 2 by linarith) u₀ ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M)
                  (zero_le_one)
                  (show LipschitzOnWith (‖R‖₊) (⇑R) (Metric.closedBall
                    (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                      (show (a + 1) ≤ a + 2 by linarith) u₀) (1 : ℝ))
                    from (R.lipschitz).lipschitzOnWith))
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) := by
  have hN : LipschitzOnWith (‖R‖₊) (⇑R) (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
        (show (a + 1) ≤ a + 2 by linarith) u₀) (1 : ℝ)) :=
    (R.lipschitz).lipschitzOnWith
  obtain ⟨T₀, hT₀_pos, hsol⟩ :=
    deTurckRemainder_strong_shortTime_exists (I := I) (M := M) g_bg
      (N := ⇑R) (L_R := ‖R‖₊) (R := (1 : ℝ)) one_pos u₀ hN
  refine ⟨T₀, hT₀_pos, fun {T} hT hTT₀ hT1 => ?_⟩
  obtain ⟨u, gforce, hduh, hforce, htrace, hderiv, _hball⟩ := hsol hT hTT₀ hT1
  exact ⟨u, gforce, hduh, hforce, htrace, hderiv⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
