import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautHs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffH0
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarLapDiffCore









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




theorem lapDiffHs_eq_A20
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∀ᶠ s in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
      ∀ u : tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0 2,
        tensorHs.castEquiv (I := I) (M := M)
            (g := G.metric (T : ℝ)) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) = 0)
            (lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
              (G.metric ((T : ℝ) - s)) 0
              (tensorHs.castEquiv (I := I) (M := M)
                (g := G.metric (T : ℝ)) (r := 0) (s := 0)
                (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2) u)) =
          lapDiffA20 (I := I) (M := M) G T s u := by
  classical
  obtain ⟨tau, htau, _, _, hHs⟩ :=
    lapDiffHs_core (I := I) (M := M) G hG T
  have hIcc : Set.Icc (0 : ℝ) tau ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
    Icc_mem_nhdsGE htau
  have hle : 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ) :=
    nhdsWithin_le_nhds
  have hA20 :=
    (lapDiffA20_core (I := I) (M := M) G hG T).filter_mono
      hle
  filter_upwards [hIcc, hA20] with s hs hsA20
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let h : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  let J : tensorHs (I := I) (M := M) q 0 0 2 →L[ℝ]
      tensorHs (I := I) (M := M) q 0 0 (((0 : ℕ) : ℝ) + 2) :=
    (tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2)).toContinuousLinearEquiv.toContinuousLinearMap
  let K : tensorHs (I := I) (M := M) q 0 0 ((0 : ℕ) : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) q 0 0 0 :=
    (tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) = 0)).toContinuousLinearEquiv.toContinuousLinearMap
  let L := K.comp ((lapDiffHs (I := I) (M := M) q h 0).comp J)
  let R := lapDiffA20 (I := I) (M := M) G T s
  intro u
  change L u = R u
  have hdense : DenseRange
      (ScalarH2Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 2)).denseRange_val
  have heq :
      L ∘ (ScalarH2Core (I := I) (M := M) q).subtype =
        R ∘ (ScalarH2Core (I := I) (M := M) q).subtype := by
    funext v
    let U : SmoothCcTensor q 0 0 :=
      tensorHsSmoothRepr (I := I) (M := M) v.1 v.2
    have hrepr :
        ccTensorToHs (I := I) (M := M) q 0 2 U = v.1 := by
      simpa only [U, ccToHsLin_apply] using
        (ccToHsLin_repr (I := I) (M := M) q 0
          (show (0 : ℝ) ≤ 2 by norm_num) v.1 v.2)
    change L v.1 = R v.1
    rw [← hrepr]
    have hJ :
        J (ccTensorToHs (I := I) (M := M) q 0 2 U) =
          ccTensorToHs (I := I) (M := M) q 0 (((0 : ℕ) : ℝ) + 2) U := by
      apply tensorHs.ext
      funext i
      rfl
    rw [show L (ccTensorToHs (I := I) (M := M) q 0 2 U) =
        ccTensorToHs (I := I) (M := M) q 0 0
          (scalarLapDiffCc (I := I) q h U) by
      change K (lapDiffHs (I := I) (M := M) q h 0
          (J (ccTensorToHs (I := I) (M := M) q 0 2 U))) = _
      rw [hJ]
      rw [hHs 0 s hs U]
      apply tensorHs.ext
      funext i
      rfl]
    apply tensorHs.ext
    funext i
    rw [ccTensorToHs_coeff]
    have hc := congrArg
      (fun Z : TensorL2 0 0 q =>
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0) Z i)
      (hsA20 v)
    simp only [tensorHsZeroEquivL2_tensorL2Coeff] at hc
    rw [lapDiffCore_eq_cc (I := I) (M := M)] at hc
    simpa only [R, q, h, U, hrepr] using hc.symm
  have hfun := hdense.equalizer L.continuous R.continuous heq
  exact congr_fun hfun u

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
