import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautHs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarFluxJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IterCovGradHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricAppHsTime









noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E




theorem lapDiffHs_decomp
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ (m : ℕ) s, s ∈ Set.Icc (0 : ℝ) tau →
        ∀ U : tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0
          ((m : ℝ) + 2),
          lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
              (G.metric ((T : ℝ) - s)) m U =
            appHs (G.metric (T : ℝ)) 2 0 m
                (scalarTraceCoeff (I := I) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)))
                (iterCovGradHs (I := I) (M := M)
                  (G.metric (T : ℝ)) 0 2 m U) -
              appHs (G.metric (T : ℝ)) 1 0 m
                (connTraceCoeff (I := I) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)))
                (iterCovGradHs (I := I) (M := M)
                  (G.metric (T : ℝ)) 0 1 m
                  (tensorHsInclusion (I := I) (M := M)
                    (g := G.metric (T : ℝ)) (r := 0) (s := 0)
                    (by norm_num : (m : ℝ) + ((1 : ℕ) : ℝ) ≤
                      (m : ℝ) + 2) U)) := by
  classical
  obtain ⟨tau, htau, htau_one, hreg, hcore⟩ :=
    lapDiffHs_core (I := I) (M := M) G hG T
  refine ⟨tau, htau, htau_one, hreg, ?_⟩
  intro m s hs U
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let h : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : (m : ℝ) + ((1 : ℕ) : ℝ) ≤ (m : ℝ) + 2)
  let D₂ := iterCovGradHs (I := I) (M := M) q 0 2 m
  let D₁ := (iterCovGradHs (I := I) (M := M) q 0 1 m).comp J
  let L := lapDiffHs (I := I) (M := M) q h m
  let R :=
    (appHs q 2 0 m (scalarTraceCoeff (I := I) q h)).comp D₂ -
      (appHs q 1 0 m (connTraceCoeff (I := I) q h)).comp D₁
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) q 0 ((m : ℝ) + 2)) :=
    ccToHsLin_dense (I := I) (M := M) q 0 (by positivity)
  have hLR : (L : _ → _) = R := hdense.equalizer L.continuous R.continuous (by
    funext W
    change
      L (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W) =
        R (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W)
    have hcoreW :
        L (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W) =
          ccTensorToHs (I := I) (M := M) q 0 (m : ℝ)
            (scalarLapDiffCc (I := I) q h W) := by
      simpa only [L, q, h] using hcore m s hs W
    rw [hcoreW]
    change
      ccTensorToHs (I := I) (M := M) q 0 (m : ℝ)
          (scalarLapDiffCc (I := I) q h W) =
        appHs q 2 0 m (scalarTraceCoeff (I := I) q h)
            (iterCovGradHs (I := I) (M := M) q 0 2 m
              (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W)) -
          appHs q 1 0 m (connTraceCoeff (I := I) q h)
            (iterCovGradHs (I := I) (M := M) q 0 1 m
              (J (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W)))
    have hD₂ :
        iterCovGradHs (I := I) (M := M) q 0 2 m
            (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W) =
          ccTensorToHs (I := I) (M := M) q 2 (m : ℝ)
            (iteratedCovGrad (I := I) q 0 0 2 W) := by
      exact iterCovGradHs_core (I := I) (M := M) q 0 2 m W
    rw [hD₂]
    have hJ :
        J (ccTensorToHs (I := I) (M := M) q 0 ((m : ℝ) + 2) W) =
          ccTensorToHs (I := I) (M := M) q 0
            ((m : ℝ) + ((1 : ℕ) : ℝ)) W := by
      apply tensorHs.ext
      funext i
      simp only [J, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    rw [hJ]
    have hD₁ :
        iterCovGradHs (I := I) (M := M) q 0 1 m
            (ccTensorToHs (I := I) (M := M) q 0
              ((m : ℝ) + ((1 : ℕ) : ℝ)) W) =
          ccTensorToHs (I := I) (M := M) q 1 (m : ℝ)
            (iteratedCovGrad (I := I) q 0 0 1 W) := by
      exact iterCovGradHs_core (I := I) (M := M) q 0 1 m W
    rw [hD₁, appHs_core, appHs_core]
    let X := operatorFieldApply (I := I) q 2 0 (scalarTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 2 W)
    let Y := operatorFieldApply (I := I) q 1 0 (connTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 1 W)
    have hsub :
        ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) (X - Y) =
          ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) X -
            ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) Y := by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) q 0 (m : ℝ)) X Y
    rw [show scalarLapDiffCc (I := I) q h W = X - Y by rfl, hsub])
  simpa only [L, R, D₂, D₁, J, q, h,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] using congrFun hLR U



theorem lapDiffHs_path_cd
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ (m : ℕ)
        (U : tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0
          ((m : ℝ) + 2)),
        ContDiffOn ℝ ∞
          (fun s => lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric ((T : ℝ) - s)) m U)
          (Set.Icc (0 : ℝ) tau) := by
  classical
  obtain ⟨tau, htau, htau_one, hreg, hdec⟩ :=
    lapDiffHs_decomp (I := I) (M := M) G hG T
  refine ⟨tau, htau, htau_one, hreg, ?_⟩
  intro m U
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : (m : ℝ) + ((1 : ℕ) : ℝ) ≤ (m : ℝ) + 2)
  let V₂ := iterCovGradHs (I := I) (M := M) q 0 2 m U
  let V₁ := iterCovGradHs (I := I) (M := M) q 0 1 m (J U)
  have h₂ := appHs_path_cd (I := I) (M := M) q 2 0 m
    (fun t => scalarTraceCoeff (I := I) q (G.metric t))
    D.regular_isOpen (scalarTrace_joint (I := I) (M := M) G hG q) V₂
  have h₁ := appHs_path_cd (I := I) (M := M) q 1 0 m
    (fun t => connTraceCoeff (I := I) q (G.metric t))
    D.regular_isOpen (connTrace_joint (I := I) (M := M) G hG q) V₁
  have hb : ContDiff ℝ ∞ (fun s : ℝ => (T : ℝ) - s) :=
    contDiff_const.sub contDiff_id
  have h₂b : ContDiffOn ℝ ∞
      (fun s => appHs q 2 0 m
        (scalarTraceCoeff (I := I) q (G.metric ((T : ℝ) - s))) V₂)
      (Set.Icc (0 : ℝ) tau) := by
    simpa only [Function.comp_apply] using
      h₂.comp hb.contDiffOn (fun s hs => hreg s hs)
  have h₁b : ContDiffOn ℝ ∞
      (fun s => appHs q 1 0 m
        (connTraceCoeff (I := I) q (G.metric ((T : ℝ) - s))) V₁)
      (Set.Icc (0 : ℝ) tau) := by
    simpa only [Function.comp_apply] using
      h₁.comp hb.contDiffOn (fun s hs => hreg s hs)
  refine (h₂b.sub h₁b).congr ?_
  intro s hs
  simpa only [q, J, V₂, V₁] using hdec m s hs U



theorem lapDiffHs_dyn_fin
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ a, 0 < a → a ≤ tau → ∀ (m k : ℕ)
        (U : ℝ → tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0
          ((m : ℝ) + 2)),
        ContDiffOn ℝ k U (Set.Ioo (0 : ℝ) a) →
        ContDiffOn ℝ k
          (fun s => lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric ((T : ℝ) - s)) m (U s))
          (Set.Ioo (0 : ℝ) a) := by
  classical
  obtain ⟨tau, htau, htau_one, hreg, hdec⟩ :=
    lapDiffHs_decomp (I := I) (M := M) G hG T
  refine ⟨tau, htau, htau_one, hreg, ?_⟩
  intro a _ha hat m k U hU
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : (m : ℝ) + ((1 : ℕ) : ℝ) ≤ (m : ℝ) + 2)
  let D₂ := iterCovGradHs (I := I) (M := M) q 0 2 m
  let D₁ := (iterCovGradHs (I := I) (M := M) q 0 1 m).comp J
  let V₂ : ℝ → tensorHs (I := I) (M := M) q 0 2 (m : ℝ) :=
    fun s => D₂ (U s)
  let V₁ : ℝ → tensorHs (I := I) (M := M) q 0 1 (m : ℝ) :=
    fun s => D₁ (U s)
  have hV₂ : ContDiffOn ℝ k V₂ (Set.Ioo (0 : ℝ) a) := by
    simpa only [V₂, Function.comp_apply] using D₂.contDiff.comp_contDiffOn hU
  have hV₁ : ContDiffOn ℝ k V₁ (Set.Ioo (0 : ℝ) a) := by
    simpa only [V₁, Function.comp_apply] using D₁.contDiff.comp_contDiffOn hU
  have hback : Set.Ioo (0 : ℝ) a ⊆
      {s : ℝ | (T : ℝ) - s ∈ D.regular} := by
    intro s hs
    exact hreg s ⟨hs.1.le, hs.2.le.trans hat⟩
  have h₂ := appHs_dyn_fin (I := I) (M := M) q 2 0 m k
    (fun s => scalarTraceCoeff (I := I) q (G.metric ((T : ℝ) - s)))
    isOpen_Ioo
    (scalarTrace_rev_on (I := I) (M := M) G hG q (T : ℝ) hback) V₂ hV₂
  have h₁ := appHs_dyn_fin (I := I) (M := M) q 1 0 m k
    (fun s => connTraceCoeff (I := I) q (G.metric ((T : ℝ) - s)))
    isOpen_Ioo
    (connTrace_rev_on (I := I) (M := M) G hG q (T : ℝ) hback) V₁ hV₁
  refine (h₂.sub h₁).congr ?_
  intro s hs
  simpa only [q, J, D₂, D₁, V₂, V₁,
    ContinuousLinearMap.comp_apply] using
      hdec m s ⟨hs.1.le, hs.2.le.trans hat⟩ (U s)



theorem lapDiffHs_dyn_cd
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ a, 0 < a → a ≤ tau → ∀ (m : ℕ)
        (U : ℝ → tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0
          ((m : ℝ) + 2)),
        ContDiffOn ℝ ∞ U (Set.Ioo (0 : ℝ) a) →
        ContDiffOn ℝ ∞
          (fun s => lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric ((T : ℝ) - s)) m (U s))
          (Set.Ioo (0 : ℝ) a) := by
  obtain ⟨tau, htau, htau_one, hreg, hfin⟩ :=
    lapDiffHs_dyn_fin (I := I) (M := M) G hG T
  refine ⟨tau, htau, htau_one, hreg, ?_⟩
  intro a ha hat m U hU
  rw [contDiffOn_infty] at hU ⊢
  intro k
  exact hfin a ha hat m k U (hU k)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
