import DifferentialGeometry.Geometry.Comparison.CenterOfMass
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
























noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic





theorem hasDerivAt_eq_of_le {f h : ℝ → ℝ} {f' h' c : ℝ}
    (hle : ∀ᶠ s in nhds c, f s ≤ h s) (heq : f c = h c)
    (hf : HasDerivAt f f' c) (hh : HasDerivAt h h' c) : f' = h' := by
  have hmin : IsLocalMin (fun s => h s - f s) c := by
    refine hle.mono fun s hs => ?_
    have h0 : h c - f c = 0 := by rw [heq]; ring
    change h c - f c ≤ h s - f s
    rw [h0]; linarith
  have hd : HasDerivAt (fun s => h s - f s) (h' - f') c := hh.sub hf
  have hzero : h' - f' = 0 := hmin.hasDerivAt_eq_zero hd
  linarith

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem arcLength_radial
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (a b : ℝ) :
    arcLength (I := I) g (intrinsicGeodesic (I := I) g hEnorm p v) a b
      = (b - a) * Real.sqrt (g.inner p v v) := by
  have hI : arcLength (I := I) g (intrinsicGeodesic (I := I) g hEnorm p v) a b
      = ∫ _t in a..b, Real.sqrt (g.inner p v v) := by
    unfold arcLength
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    congr 1
    exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v t
  rw [hI, intervalIntegral.integral_const, smul_eq_mul]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem exists_dist_eq_sqrt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q : M) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {v : TangentSpace I q},
      Real.sqrt (g.inner q v v) < ρ →
        dist q (expMapIntrinsic (I := I) g hEnorm q v) = Real.sqrt (g.inner q v v) := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨ρ, hρ, hradial⟩ := radial_riemannianEDist_eq_of_small' (I := I) g hEnorm q
  refine ⟨ρ, hρ, ?_⟩
  intro v hv
  rw [HopfRinow.riemMetric_dist_eq (I := I) q (expMapIntrinsic (I := I) g hEnorm q v),
    hradial hv]
  exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [ConnectedSpace M] in
theorem exists_expMapIntrinsic_normalChart
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {pt : M},
      pt ∈ (NormalCoordinates.normalChartAt (I := I) g q).source →
      Real.sqrt (g.inner q (NormalCoordinates.normalChartAt (I := I) g q pt : E)
        (NormalCoordinates.normalChartAt (I := I) g q pt : E)) < ρ →
      expMapIntrinsic (I := I) g hEnorm q
        (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt) = pt := by
  obtain ⟨ρ, hρ, hagree⟩ := exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm q
  refine ⟨ρ, hρ, ?_⟩
  intro pt hpt_src hsmall
  set ψ := NormalCoordinates.normalChartAt (I := I) g q with hψ
  set w : E := ψ pt with hw
  have hw_target : w ∈ ψ.target := ψ.map_source hpt_src
  have hexp_eq : expMap (I := I) g q (show TangentSpace I q from w) = pt := by
    have hround : ψ.symm (ψ pt) = pt :=
      NormalCoordinates.normalChartAt_left_inv (I := I) g q hpt_src
    have hsymm : ψ.symm w = expMap (I := I) g q (show TangentSpace I q from w) :=
      NormalCoordinates.normalChartAt_symm_apply (I := I) g q
        (show w ∈ ψ.symm.source from hw_target)
    rw [← hsymm, hw, hround]
  rw [hagree hsmall]
  exact hexp_eq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






theorem exists_central_geodesic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q : M) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {pt : M},
      pt ∈ (NormalCoordinates.normalChartAt (I := I) g q).source → pt ≠ q →
      Real.sqrt (g.inner q (NormalCoordinates.normalChartAt (I := I) g q pt : E)
        (NormalCoordinates.normalChartAt (I := I) g q pt : E)) < ρ →
      ∃ (u : TangentSpace I q) (L : ℝ), 0 < L ∧ L = dist q pt ∧
        g.inner q u u = 1 ∧
        intrinsicGeodesic (I := I) g hEnorm q u L = pt ∧
        (L • u : TangentSpace I q) =
          (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt) ∧
        IsGeodesicOn (I := I) g (intrinsicGeodesic (I := I) g hEnorm q u) (Set.Icc 0 L) ∧
        (mfderiv (𝓘(ℝ, ℝ)) I (intrinsicGeodesic (I := I) g hEnorm q u) 0 (1 : ℝ) : E) = (u : E) ∧
        arcLength (I := I) g (intrinsicGeodesic (I := I) g hEnorm q u) 0 L = L := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨ρ₄, hρ₄, hround⟩ := exists_expMapIntrinsic_normalChart (I := I) g hEnorm q
  obtain ⟨ρ₃, hρ₃, hdistlem⟩ := exists_dist_eq_sqrt (I := I) g hEnorm q
  refine ⟨min ρ₃ ρ₄, lt_min hρ₃ hρ₄, ?_⟩
  intro pt hpt_src hpt_ne hsmall
  set v₀ : TangentSpace I q :=
    (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt) with hv₀
  have hs3 : Real.sqrt (g.inner q v₀ v₀) < ρ₃ := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hs4 : Real.sqrt (g.inner q v₀ v₀) < ρ₄ := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hexp : expMapIntrinsic (I := I) g hEnorm q v₀ = pt := hround hpt_src hs4
  set L : ℝ := dist q pt with hL
  have hdist_eq : L = Real.sqrt (g.inner q v₀ v₀) := by
    rw [hL, ← hexp]; exact hdistlem hs3
  have hLpos : 0 < L := dist_pos.mpr (fun h => hpt_ne h.symm)
  have hgpos : 0 < g.inner q v₀ v₀ := Real.sqrt_pos.mp (hdist_eq ▸ hLpos)
  have hLsq : L ^ 2 = g.inner q v₀ v₀ := by rw [hdist_eq]; exact Real.sq_sqrt hgpos.le
  have hLne : L ≠ 0 := ne_of_gt hLpos
  set u : TangentSpace I q := L⁻¹ • v₀ with hu
  have hu_unit : g.inner q u u = 1 := by
    rw [hu, gInner_smul_self (I := I) g q L⁻¹ v₀, ← hLsq, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hLne)
  have hLu : (L • u : TangentSpace I q) = v₀ := by
    rw [hu, smul_smul, mul_inv_cancel₀ hLne, one_smul]
  have hgL : intrinsicGeodesic (I := I) g hEnorm q u L = pt := by
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm q u L, hLu, ← expMapIntrinsic_def]
    exact hexp
  refine ⟨u, L, hLpos, hL, hu_unit, hgL, hLu, ?_, ?_, ?_⟩
  · exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm q u).isGeodesicOn _
  · exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q u
  · rw [arcLength_radial (I := I) g hEnorm q u 0 L, hu_unit, Real.sqrt_one]; ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




theorem exists_halfSqDist_md
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (pt : M) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {q : M},
      q ∈ (NormalCoordinates.normalChartAt (I := I) g pt).source →
      Real.sqrt
          (g.inner pt
            (NormalCoordinates.normalChartAt (I := I) g pt q)
            (NormalCoordinates.normalChartAt (I := I) g pt q)) < ρ →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨ρd, hρd, hdist⟩ := exists_dist_eq_sqrt (I := I) g hEnorm pt
  obtain ⟨ρe, hρe, hexp⟩ := exists_expMapIntrinsic_normalChart (I := I) g hEnorm pt
  refine ⟨min ρd ρe, lt_min hρd hρe, ?_⟩
  intro q hqsrc hsmall
  let ψ := NormalCoordinates.normalChartAt (I := I) g pt
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner pt
  have hψ : ContMDiffAt I 𝓘(ℝ, E) 1 ψ q :=
    ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g pt) q hqsrc).contMDiffAt
      ((NormalCoordinates.normalChartAt (I := I) g pt).open_source.mem_nhds hqsrc)
  have hquad : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y : M ↦ (1 / 2 : ℝ) * g.inner pt (ψ y) (ψ y)) q := by
    have hquadB : ContMDiffAt I 𝓘(ℝ, ℝ) 1
        (fun y : M ↦ (1 / 2 : ℝ) * B (ψ y) (ψ y)) q :=
      contMDiffAt_const.mul
        (((contMDiffAt_const (c := B)).clm_apply hψ).clm_apply hψ)
    simpa only [B] using hquadB
  have hrad : ContinuousAt
      (fun y : M ↦ Real.sqrt (g.inner pt (ψ y) (ψ y))) q :=
    (continuous_sqrt_gInner_self (I := I) g pt).continuousAt.comp hψ.continuousAt
  have hsmall_ev : ∀ᶠ y in nhds q,
      Real.sqrt (g.inner pt (ψ y) (ψ y)) < min ρd ρe :=
    hrad (isOpen_Iio.mem_nhds hsmall)
  have hsrc_ev : ∀ᶠ y in nhds q, y ∈ ψ.source :=
    ψ.open_source.mem_nhds hqsrc
  have heq : CenterOfMass.halfSqDist pt =ᶠ[nhds q]
      fun y : M ↦ (1 / 2 : ℝ) * g.inner pt (ψ y) (ψ y) := by
    filter_upwards [hsrc_ev, hsmall_ev] with y hysrc hysmall
    have hsd : Real.sqrt (g.inner pt (ψ y) (ψ y)) < ρd :=
      lt_of_lt_of_le hysmall (min_le_left _ _)
    have hse : Real.sqrt (g.inner pt (ψ y) (ψ y)) < ρe :=
      lt_of_lt_of_le hysmall (min_le_right _ _)
    have hexpy : expMapIntrinsic (I := I) g hEnorm pt
        (show TangentSpace I pt from ψ y) = y :=
      hexp hysrc hse
    have hdisty : dist pt y = Real.sqrt (g.inner pt (ψ y) (ψ y)) := by
      calc
        dist pt y = dist pt (expMapIntrinsic (I := I) g hEnorm pt
            (show TangentSpace I pt from ψ y)) :=
          congrArg (fun z : M ↦ dist pt z) hexpy.symm
        _ = Real.sqrt (g.inner pt (ψ y) (ψ y)) := hdist hsd
    unfold CenterOfMass.halfSqDist
    rw [dist_comm y pt, hdisty,
      Real.sq_sqrt (gInner_self_nonneg (I := I) g pt (ψ y))]
  exact (hquad.congr_of_eventuallyEq heq).mdifferentiableAt one_ne_zero

end Radial

end Riemannian
end Geometry
end DifferentialGeometry

end
