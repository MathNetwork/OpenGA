import DifferentialGeometry.Geometry.Comparison.HalfSqDistGrad
import DifferentialGeometry.Geometry.Comparison.HalfSqDistGradVar
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval











noncomputable section


open Set Function Filter Manifold Bundle
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem halfArcLengthSq_deriv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q pt : M) (u : TangentSpace I q) (L : ℝ) (hL : 0 < L)
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (hfc : ∀ t : ℝ, f 0 t = intrinsicGeodesic (I := I) g hEnorm q u t)
    (hgL : intrinsicGeodesic (I := I) g hEnorm q u L = pt)
    (hfixL : ∀ s : ℝ, f s L = pt)
    (hguu : g.inner q u u = 1) :
    HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * arcLength (I := I) g (fun t : ℝ => f s t) 0 L ^ 2)
      (L * (- g.inner q
        (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s 0) 0 (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (intrinsicGeodesic (I := I) g hEnorm q u) 0 (1 : ℝ)))) 0 := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q u with hγ
  have hγ_geoOn : IsGeodesicOn (I := I) g γ (Set.Icc 0 L) :=
    (intrinsicGeodesic_isGeodesic (I := I) g hEnorm q u).isGeodesicOn _
  have hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1 :=
    fun t _ => (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q u t).trans hguu
  have hfixL' : ∀ s : ℝ, f s L = γ L := fun s => (hfixL s).trans (hγ ▸ hgL).symm
  have hArc := first_variation_geodesic_fixed_end (I := I) g γ f L hf hL hγ_geoOn hfc hfixL' hUnit
  have hγ0 : γ 0 = q := intrinsicGeodesic_zero (I := I) g hEnorm q u

  have harc0 : arcLength (I := I) g (fun t : ℝ => f 0 t) 0 L = L := by
    have hfγ : (fun t : ℝ => f 0 t) = γ := funext hfc
    rw [hfγ, hγ, arcLength_radial (I := I) g hEnorm q u 0 L, hguu, Real.sqrt_one]
    ring

  have hA := (hArc.pow 2).const_mul (1 / 2 : ℝ)

  have hval : (1 / 2 : ℝ) * (2 * arcLength (I := I) g (fun t : ℝ => f 0 t) 0 L ^ (2 - 1) *
        (- g.inner (γ 0) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ))))
      = L * (- g.inner q (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s 0) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ))) := by
    rw [harc0, hγ0]
    norm_num
    ring
  rw [← hval]
  exact hA

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem halfSqDist_curve_hasDerivAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (pt q : M)
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (hf00 : f 0 0 = q) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q →
    HasDerivAt (fun s : ℝ => CenterOfMass.halfSqDist pt (f s 0))
      (mfderiv I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s 0) 0 (1 : ℝ))) 0 := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro hdiff
  set β : ℝ → M := fun s : ℝ => f s 0 with hβ_def
  have hsl : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) β :=
    hf.comp (contMDiff_id.prodMk contMDiff_const)
  have hβmd : MDifferentiableAt 𝓘(ℝ, ℝ) I β 0 :=
    (hsl.contMDiffAt).mdifferentiableAt (by norm_num)
  have hβ0 : β 0 = q := by rw [hβ_def]; exact hf00
  have hg : HasMFDerivAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) (β 0)
      (mfderiv I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q) := by
    rw [hβ0]; exact hdiff.hasMFDerivAt
  have hcomp := hg.comp (0 : ℝ) hβmd.hasMFDerivAt
  rw [hasMFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt] at hcomp
  simpa [ContinuousLinearMap.comp_apply] using hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] in
theorem arcLength_nonneg
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) :
    0 ≤ arcLength (I := I) g γ a b := by
  unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
  exact intervalIntegral.integral_nonneg hab (fun t _ => Real.sqrt_nonneg _)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem dist_le_arcLength
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist (γ a) (γ b) ≤ arcLength (I := I) g γ a b := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  rw [HopfRinow.riemMetric_dist_eq (I := I) (γ a) (γ b)]
  calc (riemannianEDist I (γ a) (γ b)).toReal
      ≤ (ENNReal.ofReal (arcLength (I := I) g γ a b)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (Geodesic.riemannianEDist_le_arcLength (I := I) g hab hγ hEnorm)
    _ = arcLength (I := I) g γ a b :=
        ENNReal.toReal_ofReal (arcLength_nonneg (I := I) g hab)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





omit [T2Space (TangentBundle I M)] in
theorem halfSqDist_dir_deriv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q pt : M) (u : TangentSpace I q) (L : ℝ) (hL : 0 < L)
    (hguu : g.inner q u u = 1)
    (hgL : intrinsicGeodesic (I := I) g hEnorm q u L = pt)
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (hfc : ∀ t : ℝ, f 0 t = intrinsicGeodesic (I := I) g hEnorm q u t)
    (hfixL : ∀ s : ℝ, f s L = pt)
    (hf00 : f 0 0 = q) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist q pt = L →
    MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q →
    mfderiv I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s 0) 0 (1 : ℝ))
      = L * (- g.inner q
          (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s 0) 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u) 0 (1 : ℝ))) := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro hLdist hdiff
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q u with hγ_def
  have hA := halfArcLengthSq_deriv (I := I) g hEnorm q pt u L hL f hf hfc hgL hfixL hguu
  have hD := halfSqDist_curve_hasDerivAt (I := I) pt q f hf hf00 hdiff
  have hcompare : ∀ s : ℝ,
      CenterOfMass.halfSqDist pt (f s 0)
        ≤ (1 / 2 : ℝ) * arcLength (I := I) g (fun t : ℝ => f s t) 0 L ^ 2 := by
    intro s
    have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t : ℝ => f s t) (Set.Icc 0 L) :=
      ((hf.comp (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)).contMDiffOn
    have hEn : ∀ t ∈ Set.Icc (0 : ℝ) L,
        ‖mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => f s t) t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner ((fun t : ℝ => f s t) t)
                (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => f s t) t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => f s t) t (1 : ℝ)))) :=
      fun t _ => hEnorm (f s t) (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => f s t) t (1 : ℝ))
    have hdle := dist_le_arcLength (I := I) g (le_of_lt hL) hC1 hEn
    rw [hfixL s] at hdle
    have hdnn : (0 : ℝ) ≤ dist (f s 0) pt := dist_nonneg
    have hsq : dist (f s 0) pt ^ 2
        ≤ arcLength (I := I) g (fun t : ℝ => f s t) 0 L ^ 2 :=
      pow_le_pow_left₀ hdnn hdle 2
    unfold CenterOfMass.halfSqDist
    linarith [hsq]
  have heq0 : CenterOfMass.halfSqDist pt (f 0 0)
      = (1 / 2 : ℝ) * arcLength (I := I) g (fun t : ℝ => f 0 t) 0 L ^ 2 := by
    have hfγ : (fun t : ℝ => f 0 t) = γ := funext hfc
    have harcγ : arcLength (I := I) g γ 0 L = L := by
      rw [hγ_def, arcLength_radial (I := I) g hEnorm q u 0 L, hguu, Real.sqrt_one]; ring
    rw [hf00, hfγ, harcγ]
    unfold CenterOfMass.halfSqDist
    rw [hLdist]
  exact hasDerivAt_eq_of_le (Filter.Eventually.of_forall hcompare) heq0 hD hA

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



theorem grad_halfSqDist_min
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q pt : M) (v : TangentSpace I q) :
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    expMapIntrinsic (I := I) g hEnorm q v = pt →
    Real.sqrt (g.inner q v v) = (riemannianEDist I q pt).toReal →
    MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q →
    gradientFun (I := I) g (CenterOfMass.halfSqDist pt) q = -v := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro hexp hlen hdiff
  by_cases hpt : pt = q
  · rw [hpt] at hlen hdiff ⊢
    have hsqrt : Real.sqrt (g.inner q v v) = 0 := by
      rw [riemannianEDist_self, ENNReal.toReal_zero] at hlen
      exact hlen
    have hinner0 : g.inner q v v = 0 := by
      nlinarith [Real.sq_sqrt (gInner_self_nonneg (I := I) g q v)]
    have hv0 : v = 0 := by
      by_contra hv
      exact absurd hinner0 (ne_of_gt (g.pos q v hv))
    have hlocal : IsLocalMin (CenterOfMass.halfSqDist q) q := by
      unfold IsLocalMin IsMinFilter
      refine Filter.Eventually.of_forall ?_
      intro z
      unfold CenterOfMass.halfSqDist
      have hsq : 0 ≤ dist z q ^ 2 := sq_nonneg _
      rw [dist_self]
      nlinarith
    have hgrad0 : gradientFun (I := I) g (CenterOfMass.halfSqDist q) q = 0 :=
      gradientFun_eq_zero_of_isLocalMin (I := I) g hlocal hdiff
    simpa only [hv0, neg_zero] using hgrad0
  · set L : ℝ := dist q pt with hL
    have hLpos : 0 < L := by
      rw [hL]
      exact dist_pos.mpr (fun h => hpt h.symm)
    have hdist_eq : L = Real.sqrt (g.inner q v v) := by
      rw [hL, HopfRinow.riemMetric_dist_eq (I := I) (M := M) q pt]
      exact hlen.symm
    have hgpos : 0 < g.inner q v v := Real.sqrt_pos.mp (hdist_eq ▸ hLpos)
    have hLsq : L ^ 2 = g.inner q v v := by
      rw [hdist_eq]
      exact Real.sq_sqrt hgpos.le
    have hLne : L ≠ 0 := ne_of_gt hLpos
    set u : TangentSpace I q := L⁻¹ • v with hu
    have hu_unit : g.inner q u u = 1 := by
      rw [hu, gInner_smul_self (I := I) g q L⁻¹ v, ← hLsq, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hLne)
    have hLu : (L • u : TangentSpace I q) = v := by
      rw [hu, smul_smul, mul_inv_cancel₀ hLne, one_smul]
    have hgL : intrinsicGeodesic (I := I) g hEnorm q u L = pt := by
      rw [← intrinsicGeodesic_smul (I := I) g hEnorm q u L, hLu,
        ← expMapIntrinsic_def]
      exact hexp
    have hflat :
        (mfderiv I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q).toLinearMap =
          metricFlatEquiv (I := I) g q (-v) := by
      apply LinearMap.ext
      intro w
      obtain ⟨f, hf, hf0, hfixL, hfderiv⟩ :=
        exists_gradVariation (I := I) g hEnorm q pt u L hLpos hgL w
      have hf00 : f 0 0 = q := by
        rw [hf0 0]
        exact intrinsicGeodesic_zero (I := I) g hEnorm q u
      have hval :=
        halfSqDist_dir_deriv (I := I) g hEnorm q pt u L hLpos hu_unit hgL
          f hf hf0 hfixL hf00 hL.symm hdiff
      have hw' : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s 0) 0 (1 : ℝ) = w := hfderiv
      have hu' :
          mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u) 0 (1 : ℝ) = u :=
        intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q u
      rw [hw', hu'] at hval
      have hvw : g.inner q v w = L * g.inner q u w := by
        rw [← hLu, (g.inner q).map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      change mfderiv I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q w =
        g.inner q (-v) w
      rw [hval, (g.inner q).map_neg, ContinuousLinearMap.neg_apply, hvw,
        g.symm q w u, mul_neg]
    exact gradientFun_eq_of_flat (I := I) g hflat

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem halfSqDist_flat
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
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q →
      (mfderiv I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q).toLinearMap =
        metricFlatEquiv (I := I) g q
          (-(show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt)) := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨ρ, hρ, hgeo⟩ := exists_central_geodesic (I := I) g hEnorm q
  refine ⟨ρ, hρ, ?_⟩
  intro pt hpt_src hpt_ne hsmall hdiff
  obtain ⟨u, L, hLpos, hLdist, hguu, hgL, hLu, hgeoOn, hmfd, harc⟩ :=
    hgeo hpt_src hpt_ne hsmall
  apply LinearMap.ext
  intro w
  obtain ⟨f, hf, hf0, hfixL, hfderiv⟩ :=
    exists_gradVariation (I := I) g hEnorm q pt u L hLpos hgL w
  have hf00 : f 0 0 = q := by
    rw [hf0 0]; exact intrinsicGeodesic_zero (I := I) g hEnorm q u
  have hval :=
    halfSqDist_dir_deriv (I := I) g hEnorm q pt u L hLpos hguu hgL f hf hf0 hfixL hf00
      hLdist.symm hdiff
  have hw' : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s 0) 0 (1 : ℝ) = w := hfderiv
  have hu' : mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm q u) 0 (1 : ℝ) = u := hmfd
  rw [hw', hu'] at hval
  have hnc : g.inner q
      (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt) w
      = L * g.inner q u w := by
    rw [← hLu, (g.inner q).map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  show mfderiv I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q w
      = g.inner q
          (-(show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt)) w
  rw [hval, (g.inner q).map_neg, ContinuousLinearMap.neg_apply, hnc, g.symm q w u,
    mul_neg]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




theorem grad_halfSqDist
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
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt) q →
      gradientFun (I := I) g (CenterOfMass.halfSqDist pt) q =
        -(show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt) := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨ρ, hρ, hflat⟩ := halfSqDist_flat (I := I) g hEnorm q
  refine ⟨ρ, hρ, ?_⟩
  intro pt hsrc hne hsmall hdiff
  exact gradientFun_eq_of_flat (I := I) g (hflat hsrc hne hsmall hdiff)

end Riemannian
end Geometry
end DifferentialGeometry

end
