import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.MfderivZero
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.InjectivityRadius
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Exponential.ChartFlow.SmallVelocityRescaling
import DifferentialGeometry.Geometry.Exponential.ChartFlow.RescaledLift
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformExistence
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Analysis.ODE.RadialSeminormFencing
import Mathlib.Geometry.Manifold.Riemannian.PathELength



noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section RadialMinimizerConvention

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section LengthBookkeeping


set_option linter.unusedVariables false in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem subArc_of_minimizer_is_minimizer
    {γ : ℝ → M} {a b s t : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hfin : pathELength I γ a b ≠ ⊤)
    (hab : a ≤ b) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    riemannianEDist I (γ s) (γ t) = pathELength I γ s t := by
  set L_left := pathELength I γ a s with hL_left_def
  set L_mid := pathELength I γ s t with hL_mid_def
  set L_right := pathELength I γ t b with hL_right_def
  have h_ast : a ≤ t := has.trans hst
  have h_sb : s ≤ b := hst.trans htb
  have hγ_as : CMDiff[Icc a s] 1 γ := hγ.mono (Icc_subset_Icc le_rfl h_sb)
  have hγ_st : CMDiff[Icc s t] 1 γ := hγ.mono (Icc_subset_Icc has htb)
  have hγ_tb : CMDiff[Icc t b] 1 γ := hγ.mono (Icc_subset_Icc h_ast le_rfl)
  have hadd_left : L_left + L_mid = pathELength I γ a t :=
    pathELength_add (γ := γ) (I := I) has hst
  have hadd_total : pathELength I γ a t + L_right = pathELength I γ a b :=
    pathELength_add (γ := γ) (I := I) h_ast htb
  have hpath_total : L_left + L_mid + L_right = pathELength I γ a b := by
    rw [hadd_left, hadd_total]
  have hL_left_finite : L_left ≠ ⊤ := by
    have hle : L_left ≤ pathELength I γ a b := by
      rw [← hpath_total]
      have h₁ : L_left ≤ L_left + L_mid := le_self_add
      exact h₁.trans le_self_add
    exact ne_top_of_le_ne_top hfin hle
  have hL_right_finite : L_right ≠ ⊤ := by
    have hle : L_right ≤ pathELength I γ a b := by
      rw [← hpath_total]
      exact le_add_self
    exact ne_top_of_le_ne_top hfin hle
  have hD_left : riemannianEDist I (γ a) (γ s) ≤ L_left :=
    riemannianEDist_le_pathELength hγ_as rfl rfl has
  have hD_right : riemannianEDist I (γ t) (γ b) ≤ L_right :=
    riemannianEDist_le_pathELength hγ_tb rfl rfl htb
  have hD_mid_le : riemannianEDist I (γ s) (γ t) ≤ L_mid :=
    riemannianEDist_le_pathELength hγ_st rfl rfl hst
  have htri₁ : riemannianEDist I (γ a) (γ b) ≤
      riemannianEDist I (γ a) (γ t) + riemannianEDist I (γ t) (γ b) :=
    riemannianEDist_triangle
  have htri₂ : riemannianEDist I (γ a) (γ t) ≤
      riemannianEDist I (γ a) (γ s) + riemannianEDist I (γ s) (γ t) :=
    riemannianEDist_triangle
  have htri_combined : riemannianEDist I (γ a) (γ b) ≤
      riemannianEDist I (γ a) (γ s) + riemannianEDist I (γ s) (γ t)
        + riemannianEDist I (γ t) (γ b) :=
    htri₁.trans (add_le_add htri₂ le_rfl)
  have hpath_le : pathELength I γ a b ≤
      L_left + riemannianEDist I (γ s) (γ t) + L_right := by
    have := htri_combined
    rw [hmin] at this
    refine this.trans ?_
    exact add_le_add (add_le_add hD_left le_rfl) hD_right
  have hsqueeze : L_left + L_mid + L_right
        ≤ L_left + riemannianEDist I (γ s) (γ t) + L_right := by
    calc L_left + L_mid + L_right = pathELength I γ a b := hpath_total
      _ ≤ L_left + riemannianEDist I (γ s) (γ t) + L_right := hpath_le
  have hsqueeze' : L_left + L_right + L_mid
        ≤ L_left + L_right + riemannianEDist I (γ s) (γ t) := by
    have heq₁ : L_left + L_mid + L_right = L_left + L_right + L_mid := by ring
    have heq₂ : L_left + riemannianEDist I (γ s) (γ t) + L_right
                  = L_left + L_right + riemannianEDist I (γ s) (γ t) := by ring
    rw [heq₁, heq₂] at hsqueeze
    exact hsqueeze
  have hL_lr_finite : L_left + L_right ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hL_left_finite, hL_right_finite⟩
  have hmid_le_D : L_mid ≤ riemannianEDist I (γ s) (γ t) :=
    (ENNReal.add_le_add_iff_left hL_lr_finite).mp hsqueeze'
  exact le_antisymm hD_mid_le hmid_le_D

end LengthBookkeeping

section RadialUniqueMinimizer

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]


private theorem radialDist_endpoint_le_pathELength
    (g : SmoothRiemannianMetric I M) (p : M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hγa : γ a = p)
    (hγ : CMDiff[Set.Icc a b] 1 γ)
    (hsrc : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hbball : ∀ t ∈ Set.Icc a b,
      ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
        expMapC2Radius (I := I) g p)
    (hdom : ∀ t ∈ Set.Icc a b,
      (show TangentSpace I p from
          NormalCoordinates.normalChartAt (I := I) g p (γ t))
        ∈ expDomain (I := I) g p) :
    ENNReal.ofReal (Real.sqrt
        (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ b))
          (NormalCoordinates.normalChartAt (I := I) g p (γ b)))) ≤
      pathELength I γ a b := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  set φ : ℝ → ℝ := fun t =>
    Real.sqrt (g.inner (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1))
    with hφ_def
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hccont : ContinuousOn c (Set.Icc a b) := hψcont.comp hγcont hsrc
  have hρc : ContinuousOn ρ (Set.Icc a b) :=
    ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
  have hca : c a = 0 := by
    rw [hc_def]; simp only; rw [hγa, hψ_def]
    exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hρa : ρ a ≤ 0 := by
    rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero, le_refl]
  have hρb : ρ b = Real.sqrt (g.inner p (ψ (γ b)) (ψ (γ b))) := rfl
  rw [hρb.symm]
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    have hle0 : ρ a ≤ 0 := hρa
    have hzero : ρ a = 0 := le_antisymm hle0 (by rw [hρ_def]; exact Real.sqrt_nonneg _)
    rw [hzero, ENNReal.ofReal_zero]; exact bot_le
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := fun x hx => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact (uniqueDiffOn_Icc hab_lt) x hx
  have hLift : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := fun t ht => by simpa using ht
  have hVel : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)) (Set.Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin (le_refl 1) hUnique).comp
      hLift.continuousOn hMaps).congr (fun t _ => rfl)
  have hφc : ContinuousOn φ (Set.Icc a b) := by
    rw [hφ_def]
    exact Real.continuous_sqrt.comp_continuousOn
      (Variation.continuousOn_g_inner_along_curve (I := I) g hVel hVel)
  have hφnn : ∀ t ∈ Set.Icc a b, 0 ≤ φ t := fun t _ => Real.sqrt_nonneg _
  have hφint : MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume :=
    hφc.integrableOn_compact isCompact_Icc
  have hφcont : ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x := by
    intro x hx
    refine (hφc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
      intro z hz; exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
  have hφ_eq_mfderiv : ∀ t ∈ Set.Ioo a b,
      φ t = Real.sqrt
        (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) := by
    intro t ht
    rw [hφ_def]; simp only
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    set cv : E := mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x 1 with hcv_def
    have hcderiv : HasDerivWithinAt c cv (Set.Ici x) x := by
      have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
        (hγ.mdifferentiableOn (by norm_num)) x hxIcc
      have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
        (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)
      have hcomp : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x :=
        hψdiff.comp x hγdiff (fun t ht => hsrc t ht)
      have hmf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x) := hcomp.hasMFDerivWithinAt
      rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hmf
      have hHDW : HasDerivWithinAt c cv (Set.Icc a b) x := hmf.hasDerivWithinAt
      refine hHDW.mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz; exact ⟨le_trans hx.1 hz.2, le_of_lt hz.1⟩⟩
    by_cases hcx : c x = 0
    · have htend : Filter.Tendsto (fun z => slope ρ x z)
          (nhdsWithin x (Set.Ioi x)) (nhds (Real.sqrt (B cv cv))) := by
        have hcz : Filter.Tendsto (fun z => (z - x)⁻¹ • c z)
            (nhdsWithin x (Set.Ioi x)) (nhds cv) := by
          have h0 := hcderiv.mono (Set.Ioi_subset_Ici_self)
          rw [hasDerivWithinAt_iff_tendsto_slope] at h0
          have hset : Set.Ioi x \ {x} = Set.Ioi x := by
            ext z; simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_singleton_iff]
            exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
          rw [hset] at h0
          refine (Filter.tendsto_congr' ?_).mp h0
          filter_upwards with z; rw [slope_def_module, hcx, sub_zero]
        have hcont : Continuous (fun w : E => Real.sqrt (B w w)) := by fun_prop
        have htend2 := (hcont.tendsto cv).comp hcz
        refine (Filter.tendsto_congr' ?_).mp htend2
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hzx : 0 < z - x := sub_pos.mpr hz
        have heq : slope ρ x z
            = Real.sqrt (B ((z - x)⁻¹ • c z) ((z - x)⁻¹ • c z)) := by
          rw [hρ_def, slope_def_module, hcx]
          simp only [map_zero, Real.sqrt_zero, sub_zero, smul_eq_mul, map_smul,
            ContinuousLinearMap.smul_apply]
          rw [show (z - x)⁻¹ * ((z - x)⁻¹ * B (c z) (c z))
              = ((z - x)⁻¹) ^ 2 * B (c z) (c z) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
        simp only [Function.comp_apply]
        exact heq.symm
      have hφx_eq : φ x = Real.sqrt (B cv cv) := by
        have hγx_p : γ x = p := by
          have hcx' : ψ (γ x) = 0 := hcx
          have hpsrc : p ∈ ψ.source := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p
          have hψp : ψ p = 0 := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g p
          exact ψ.injOn (hsrc x hxIcc) hpsrc (by rw [hcx', hψp])
        have hcv_eq : cv = mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x 1 := by
          rw [hcv_def]
          have hUnique : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Set.Icc a b) x := by
            rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact (uniqueDiffOn_Icc hab_lt) x hxIcc
          have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
            (hγ.mdifferentiableOn (by norm_num)) x hxIcc
          have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
            (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
              one_ne_zero (γ x) (hsrc x hxIcc)
          have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E))
            (f := γ) (g := ψ) (s := Set.Icc a b) (u := ψ.source) x hψdiff hγdiff
            (fun t ht => hsrc t ht) hUnique
          have hcomp_eq : c = ψ ∘ γ := rfl
          rw [hcomp_eq, hchain]
          simp only [Function.comp_apply]
          have hsource_nhds : ψ.source ∈ nhds (γ x) :=
            (NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc)
          rw [mfderivWithin_of_mem_nhds hsource_nhds, hγx_p,
            NormalCoordinates.mfderiv_normalChartAt_self]
          rfl
        simp only [hφ_def]
        rw [hcv_eq, hγx_p, hB_def]; rfl
      rw [hφx_eq] at hr
      exact (htend.eventually_lt_const hr).frequently
    · have hxIoo : x ∈ Set.Ioo a b := by
        refine ⟨lt_of_le_of_ne hx.1 ?_, hx.2⟩
        intro hxa; apply hcx; rw [← hxa]; exact hca
      have hmem : Set.Icc a b ∈ nhds x := Icc_mem_nhds hxIoo.1 hxIoo.2
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ x :=
        ((hγ.mdifferentiableOn (by norm_num)) x hxIcc).mdifferentiableAt hmem
      have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ x) :=
        ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)).mdifferentiableAt
          ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc))
      have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x := hψdiff.comp x hγdiff
      set cv₂ : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x 1 with hcv₂_def
      have hcHDA : HasDerivAt c cv₂ x := by
        have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x) :=
          hcdiff.hasMFDerivAt
        rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
        exact hmf.hasDerivAt
      have hpos : 0 < B (c x) (c x) := by rw [hB_def]; exact g.pos p (c x) hcx
      have hρderiv : HasDerivAt ρ (B (c x) cv₂ / Real.sqrt (B (c x) (c x))) x :=
        radialDist_hasDerivAt B hBsym c cv₂ hcHDA hpos
      set ρ' : ℝ := B (c x) cv₂ / Real.sqrt (B (c x) (c x)) with hρ'_def
      have hev : ∀ᶠ s in nhds x, γ s ∈ ψ.source := by
        have hopen : Set.Ioo a b ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
        filter_upwards [hopen] with s hs using hsrc s (Ioo_subset_Icc_self hs)
      have hball : ‖ψ (γ x)‖ < expMapC2Radius (I := I) g p := hbball x hxIcc
      have hune : ψ (γ x) ≠ 0 := hcx
      have hgauss := gauss_pointwise_speed_lower_bound (I := I) g p hγdiff
        (hsrc x hxIcc) (hdom x hxIcc) hball hune hev
      have hcv₂_eq : cv₂ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => ψ (γ s)) x (1 : ℝ) := rfl
      have hρ'sq_le : ρ' ^ 2 ≤
          g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) := by
        have hρ'sq : ρ' ^ 2 = (B (c x) cv₂) ^ 2 / B (c x) (c x) := by
          rw [hρ'_def, div_pow, Real.sq_sqrt hpos.le]
        rw [hρ'sq, hcv₂_eq, hB_def]
        exact hgauss
      have hφx_eq : φ x = Real.sqrt
          (g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1)) := by
        simp only [hφ_def]
        rw [mfderivWithin_of_mem_nhds hmem]
      have hρ'_le : ρ' ≤ φ x := by
        rw [hφx_eq]
        calc ρ' ≤ |ρ'| := le_abs_self _
          _ = Real.sqrt (ρ' ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ _ := Real.sqrt_le_sqrt hρ'sq_le
      have hρ'_lt : ρ' < r := lt_of_le_of_lt hρ'_le hr
      exact (hρderiv.hasDerivWithinAt (s := Set.Ici x)).liminf_right_slope_le hρ'_lt
  have hftc : ρ b ≤ ∫ t in a..b, φ t :=
    image_radialDist_le_intervalIntegral_of_slope_le hab hρc hρa hφint hφcont hslope
  have hpath : ENNReal.ofReal (∫ t in a..b, φ t) ≤ pathELength I γ a b := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo,
      intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hφint.mono_set Ioo_subset_Icc_self)
        (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
            using hφnn x (Ioo_subset_Icc_self hx))]
    apply MeasureTheory.setLIntegral_mono_ae' measurableSet_Ioo
    filter_upwards with t ht
    rw [hφ_eq_mfderiv t ht]
    exact le_of_eq (hEnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)).symm
  calc ENNReal.ofReal (ρ b)
        ≤ ENNReal.ofReal (∫ t in a..b, φ t) := ENNReal.ofReal_le_ofReal hftc
    _ ≤ pathELength I γ a b := hpath

private theorem mfderiv_expMap_injective_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {u : E}
    (hu : ‖u‖ < expMapC2Radius (I := I) g p) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) I
        (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) u) := by
  classical
  set Φ := NormalCoordinates.expMapDiffeo (I := I) g p with hΦ_def
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  have hsrc : u ∈ Φ.source := by
    have := ball_subset_normalChartAt_target (I := I) g p hu
    rw [NormalCoordinates.normalChartAt_target_eq] at this
    exact this
  have hΦ_exp : Φ =ᶠ[nhds u]
      (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) := by
    refine Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hsrc) ?_
    intro y hy
    exact NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hy
  set A : E →L[ℝ] TangentSpace I (expMap (I := I) g p (show TangentSpace I p from u)) :=
    mfderiv 𝓘(ℝ, E) I
      (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) u with hA_def
  have hA_eq : A = mfderiv 𝓘(ℝ, E) I Φ u := by
    rw [hA_def, hΦ_exp.mfderiv_eq]
  have hΦu : Φ u = expMap (I := I) g p (show TangentSpace I p from u) :=
    NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hsrc
  have hψΦ_id : (ψ ∘ Φ) =ᶠ[nhds u] (_root_.id : E → E) := by
    refine Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hsrc) ?_
    intro y hy
    change ψ (Φ y) = y
    exact Φ.left_inv hy
  have hΦ_diff : MDifferentiableAt 𝓘(ℝ, E) I Φ u :=
    (Φ.contMDiffOn_toFun.mdifferentiableOn one_ne_zero u hsrc).mdifferentiableAt
      (Φ.open_source.mem_nhds hsrc)
  have hΦu_target : Φ u ∈ ψ.source := by
    rw [hψ_def, NormalCoordinates.normalChartAt_source_eq]
    exact Φ.map_source hsrc
  have hψ_diff : MDifferentiableAt I 𝓘(ℝ, E) ψ (Φ u) :=
    ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
      one_ne_zero (Φ u) hΦu_target).mdifferentiableAt
      ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds hΦu_target)
  have hchain := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
    (f := Φ) (g := ψ) (x := u) hψ_diff hΦ_diff
  have hid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ ∘ Φ) u
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (_root_.id : E → E) u := hψΦ_id.mfderiv_eq
  have hleft : Function.LeftInverse
      (mfderiv I 𝓘(ℝ, E) ψ (Φ u)) (mfderiv 𝓘(ℝ, E) I Φ u) := by
    intro x
    have hidx := congrArg (fun (T : E →L[ℝ] E) => T x) hid
    simp only at hidx
    rw [hchain] at hidx
    rw [mfderiv_id] at hidx
    simpa using hidx
  have hΦinj : Function.Injective (mfderiv 𝓘(ℝ, E) I Φ u) := hleft.injective
  rw [hA_eq]
  exact hΦinj

set_option linter.unusedVariables false in
theorem normalBall_radial_length_le_riemannianEDist
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (hsmall_g : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p) :
    ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) := by
  set q := expMap (I := I) g p (show TangentSpace I p from v) with hq_def
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set S : ℝ := Real.sqrt (g.inner p v v) with hS_def
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  set Rₑ : ℝ := expMapC2Radius (I := I) g p with hRₑ_def
  have hRₑ_pos : 0 < Rₑ := expMapC2Radius_pos (I := I) g p
  set Bp : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hBp_def
  have hBpsym : ∀ x y : E, Bp x y = Bp y x := g.symm p
  have hBpnn : ∀ x : E, 0 ≤ Bp x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set nE : E → ℝ := fun w => Real.sqrt (Bp w w) with hnE_def
  have hnE_cont : Continuous nE := (psd_sqrt_lipschitz Bp hBpsym hBpnn).continuous
  have hnE_to_ball : ∀ {w : E}, nE w < expRadiusGp (I := I) g p → ‖w‖ < Rₑ := by
    intro w hw
    have : Real.sqrt (g.inner p w w) < expRadiusGp (I := I) g p := hw
    exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p this
  refine le_of_forall_gt (fun r hr => ?_)
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr
      (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one with
    ⟨γ, hγ0, hγ1, hγ_smooth, hγ_len, _, _⟩
  have hγ1' : γ 1 = q := by simp [hq_def, hγ1]
  set hM : M → ℝ := fun x => nE (ψ x) with hhM_def
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hhM_cont : ContinuousOn hM ψ.source := hnE_cont.comp_continuousOn hψcont
  have hγcont : Continuous γ := hγ_smooth.continuous
  have hψp : ψ p = 0 := by rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hpsrc : p ∈ ψ.source := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p
  have hψq : ψ q = v := by
    rw [hψ_def, hq_def]
    have hsource : v ∈ ψ.symm.source := hball
    have hsymm := NormalCoordinates.normalChartAt_symm_apply (I := I) g p (v := v) hsource
    rw [← hψ_def, hψ_def, ← hsymm]
    exact NormalCoordinates.normalChartAt_right_inv (I := I) g p hball
  obtain ⟨δ, hSδ, hδR⟩ := exists_between hsmall_g
  have hδ_pos : 0 < δ := lt_of_le_of_lt hS_nn hSδ
  set D : Set E := {w : E | nE w ≤ δ} with hD_def
  have hD_sub_target : D ⊆ ψ.target := by
    intro w hw
    have hw' : nE w < expRadiusGp (I := I) g p := lt_of_le_of_lt hw hδR
    rw [hψ_def]
    exact ball_subset_normalChartAt_target (I := I) g p (hnE_to_ball hw')
  have hcoerc : 0 < gpCoerciveConst (I := I) g p := gpCoerciveConst_pos (I := I) g p
  set cδ : ℝ := δ / Real.sqrt (gpCoerciveConst (I := I) g p) with hcδ_def
  have hcδ_nn : 0 ≤ cδ := div_nonneg hδ_pos.le (Real.sqrt_nonneg _)
  have hbound : ∀ {x : E}, nE x ≤ δ → ‖x‖ ≤ cδ := by
    intro x hx
    have hg_le : g.inner p x x ≤ δ ^ 2 := by
      have hsqrt_le : Real.sqrt (g.inner p x x) ≤ δ := hx
      have h := Real.sq_sqrt (show (0:ℝ) ≤ g.inner p x x from hBpnn x)
      calc g.inner p x x = Real.sqrt (g.inner p x x) ^ 2 := h.symm
        _ ≤ δ ^ 2 := by
            apply pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le
    have hcx : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
      gpCoerciveConst_le (I := I) g p x
    have hsq : ‖x‖ ^ 2 ≤ cδ ^ 2 := by
      rw [hcδ_def, div_pow, Real.sq_sqrt hcoerc.le, le_div_iff₀ hcoerc]
      calc ‖x‖ ^ 2 * gpCoerciveConst (I := I) g p
            = gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 := by ring
        _ ≤ g.inner p x x := hcx
        _ ≤ δ ^ 2 := hg_le
    exact (sq_le_sq₀ (norm_nonneg x) hcδ_nn).mp hsq
  have hD_compact : IsCompact D := by
    haveI : ProperSpace E := FiniteDimensional.proper_rclike (K := ℝ) (E := E)
    have hD_closed : IsClosed D := isClosed_le hnE_cont continuous_const
    have hD_bdd : Bornology.IsBounded D := by
      apply Metric.isBounded_iff.mpr
      refine ⟨2 * cδ, fun x hx y hy => ?_⟩
      have hbx : ‖x‖ ≤ cδ := hbound hx
      have hby : ‖y‖ ≤ cδ := hbound hy
      calc dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
        _ ≤ 2 * cδ := by linarith
    exact Metric.isCompact_of_isClosed_isBounded hD_closed hD_bdd
  have hψsymm_cont : ContinuousOn ψ.symm ψ.target :=
    (NormalCoordinates.normalChartAt_symm_contMDiffOn (I := I) g p).continuousOn
  set K : Set M := ψ.symm '' D with hK_def
  have hK_compact : IsCompact K :=
    hD_compact.image_of_continuousOn (hψsymm_cont.mono hD_sub_target)
  haveI : T2Space M := gauss_t2Space_base (I := I) (M := M)
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hmem_K_of_src : ∀ {x : M}, x ∈ ψ.source → ψ x ∈ D → x ∈ K := by
    intro x hxsrc hxD
    refine ⟨ψ x, hxD, ?_⟩
    exact ψ.left_inv hxsrc
  have hK_src : ∀ {x : M}, x ∈ K → x ∈ ψ.source := by
    rintro x ⟨w, hwD, rfl⟩
    exact ψ.symm_mapsTo (hD_sub_target hwD)
  have hK_chart : ∀ {x : M}, x ∈ K → ψ x ∈ D := by
    rintro x ⟨w, hwD, rfl⟩
    have : ψ (ψ.symm w) = w := ψ.right_inv (hD_sub_target hwD)
    rw [this]; exact hwD
  have hpK : p ∈ K := hmem_K_of_src hpsrc (by
    change nE (ψ p) ≤ δ; rw [hψp, hnE_def]; simp only [map_zero, Real.sqrt_zero]; exact hδ_pos.le)
  have hqsrc : q ∈ ψ.source := by
    have hsymm_src : ψ.symm v ∈ ψ.source := ψ.symm_mapsTo hball
    have hqeq : ψ.symm v = q := by
      rw [hq_def, hψ_def]
      exact NormalCoordinates.normalChartAt_symm_apply (I := I) g p hball
    rwa [hqeq] at hsymm_src
  set Z : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 | γ t ∉ K} with hZ_def
  by_cases hZ : Z = ∅
  · have hall_K : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ K := by
      intro t ht
      by_contra hcon
      have htZ : t ∈ Z := ⟨ht, hcon⟩
      rw [hZ] at htZ
      exact Set.notMem_empty t htZ
    have hsrc' : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ ψ.source :=
      fun t ht => hK_src (hall_K t ht)
    have hbball' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖ψ (γ t)‖ < Rₑ := by
      intro t ht
      have hch : ψ (γ t) ∈ D := hK_chart (hall_K t ht)
      exact hnE_to_ball (lt_of_le_of_lt hch hδR)
    have hdom' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (show TangentSpace I p from ψ (γ t)) ∈ expDomain (I := I) g p :=
      fun t ht => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball' t ht)
    have hlb := radialDist_endpoint_le_pathELength (I := I) g p hEnorm
      (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one hγ0 hγ_smooth.contMDiffOn
      hsrc' hbball' hdom'
    rw [show (NormalCoordinates.normalChartAt (I := I) g p (γ 1)) = v by
      rw [← hψ_def, hγ1', hψq]] at hlb
    have hSeq : Real.sqrt (g.inner p v v) = S := rfl
    rw [hSeq] at hlb
    exact lt_of_le_of_lt hlb hγ_len
  · rw [← Ne.eq_def, ← Set.nonempty_iff_ne_empty] at hZ
    have hZ_sub : Z ⊆ Set.Icc (0 : ℝ) 1 := fun t ht => ht.1
    have hZbdd : BddBelow Z := ⟨0, fun t ht => ht.1.1⟩
    set t₀ : ℝ := sInf Z with ht₀_def
    have ht₀_nn : 0 ≤ t₀ := le_csInf hZ (fun t ht => ht.1.1)
    have ht₀_le1 : t₀ ≤ 1 := by
      obtain ⟨t, ht⟩ := hZ
      exact le_trans (csInf_le hZbdd ht) ht.1.2
    have hpre_K : ∀ s, 0 ≤ s → s < t₀ → γ s ∈ K := by
      intro s hs0 hst₀
      by_contra hcon
      have hsZ : s ∈ Z := ⟨⟨hs0, le_trans hst₀.le ht₀_le1⟩, hcon⟩
      exact absurd (csInf_le hZbdd hsZ) (not_le.mpr hst₀)
    have ht₀_K : γ t₀ ∈ K := by
      rcases eq_or_lt_of_le ht₀_nn with h0 | h0
      · rw [← h0]; rw [hγ0]; exact hpK
      · have htend : Filter.Tendsto (fun s => γ s) (nhdsWithin t₀ (Set.Iio t₀))
            (nhds (γ t₀)) :=
          (hγcont.continuousWithinAt (s := Set.Iio t₀) (x := t₀))
        have hev : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀), γ s ∈ K := by
          have hpos : Set.Ioo 0 t₀ ∈ nhdsWithin t₀ (Set.Iio t₀) := by
            rw [mem_nhdsWithin]
            exact ⟨Set.Ioi 0, isOpen_Ioi, h0, by
              intro z hz; exact ⟨hz.1, hz.2⟩⟩
          filter_upwards [hpos] with s hs using hpre_K s hs.1.le hs.2
        haveI hne : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := nhdsLT_neBot t₀
        exact hK_closed.mem_of_tendsto htend hev
    have hall_K_prefix : ∀ s ∈ Set.Icc (0 : ℝ) t₀, γ s ∈ K := by
      intro s hs
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h]; exact ht₀_K
      · exact hpre_K s hs.1 h
    have ht₀_src : γ t₀ ∈ ψ.source := hK_src ht₀_K
    have ht₀_le_δ : hM (γ t₀) ≤ δ := hK_chart ht₀_K
    have ht₀_eq_δ : hM (γ t₀) = δ := by
      refine le_antisymm ht₀_le_δ ?_
      by_contra hcon
      rw [not_le] at hcon
      have hopenW : IsOpen (ψ.source ∩ hM ⁻¹' (Set.Iio δ)) := by
        have h1 : IsOpen ψ.source := NormalCoordinates.normalChartAt_open_source (I := I) g p
        exact hhM_cont.isOpen_inter_preimage h1 isOpen_Iio
      have ht₀_mem : γ t₀ ∈ ψ.source ∩ hM ⁻¹' (Set.Iio δ) := ⟨ht₀_src, hcon⟩
      have hpre : γ ⁻¹' (ψ.source ∩ hM ⁻¹' (Set.Iio δ)) ∈ nhds t₀ :=
        hγcont.continuousAt.preimage_mem_nhds (hopenW.mem_nhds ht₀_mem)
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hε_sub⟩
      have ht₀_lt1 : t₀ < 1 := by
        rcases eq_or_lt_of_le ht₀_le1 with h1 | h1
        · exfalso
          obtain ⟨t, htZ⟩ := hZ
          have htge : t₀ ≤ t := csInf_le hZbdd htZ
          have htle : t ≤ 1 := htZ.1.2
          have : t = 1 := le_antisymm htle (by rw [h1] at htge; exact htge)
          rw [this] at htZ
          have hqD : ψ q ∈ D := by
            change nE (ψ q) ≤ δ
            rw [hψq]
            have hnv : nE v = S := rfl
            rw [hnv]; exact hSδ.le
          have hq_in_K : γ 1 ∈ K := by rw [hγ1']; exact hmem_K_of_src hqsrc hqD
          exact htZ.2 hq_in_K
        · exact h1
      set t₁ : ℝ := min (t₀ + ε / 2) 1 with ht₁_def
      have ht₀_lt_t₁ : t₀ < t₁ := by
        rw [ht₁_def, lt_min_iff]
        exact ⟨by linarith, ht₀_lt1⟩
      have ht₁_le1 : t₁ ≤ 1 := min_le_right _ _
      have ht₁_dist : dist t₁ t₀ < ε := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [ht₀_lt_t₁.le] : (0:ℝ) ≤ t₁ - t₀)]
        have : t₁ ≤ t₀ + ε / 2 := min_le_left _ _
        linarith
      have ht₁_mem : t₁ ∈ Metric.ball t₀ ε := by rw [Metric.mem_ball]; exact ht₁_dist
      have hγt₁_W : γ t₁ ∈ ψ.source ∩ hM ⁻¹' (Set.Iio δ) := hε_sub ht₁_mem
      have hγt₁_K : γ t₁ ∈ K := by
        refine hmem_K_of_src hγt₁_W.1 ?_
        change nE (ψ (γ t₁)) ≤ δ
        exact le_of_lt hγt₁_W.2
      have hge : t₁ ≤ t₀ := by
        apply le_csInf hZ
        intro t htZ
        by_contra hlt
        rw [not_le] at hlt
        have htge : t₀ ≤ t := csInf_le hZbdd htZ
        have htdist : dist t t₀ < ε := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - t₀)]
          have : t < t₁ := hlt
          have ht₁le : t₁ ≤ t₀ + ε / 2 := min_le_left _ _
          linarith
        have htW : γ t ∈ ψ.source ∩ hM ⁻¹' (Set.Iio δ) :=
          hε_sub (by rw [Metric.mem_ball]; exact htdist)
        have htK : γ t ∈ K := by
          refine hmem_K_of_src htW.1 ?_
          change nE (ψ (γ t)) ≤ δ
          exact le_of_lt htW.2
        exact htZ.2 htK
      linarith
    have hsrc' : ∀ t ∈ Set.Icc (0 : ℝ) t₀, γ t ∈ ψ.source :=
      fun t ht => hK_src (hall_K_prefix t ht)
    have hbball' : ∀ t ∈ Set.Icc (0 : ℝ) t₀, ‖ψ (γ t)‖ < Rₑ := by
      intro t ht
      have hch : ψ (γ t) ∈ D := hK_chart (hall_K_prefix t ht)
      exact hnE_to_ball (lt_of_le_of_lt hch hδR)
    have hdom' : ∀ t ∈ Set.Icc (0 : ℝ) t₀,
        (show TangentSpace I p from ψ (γ t)) ∈ expDomain (I := I) g p :=
      fun t ht => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball' t ht)
    have hγ_pref : CMDiff[Set.Icc (0:ℝ) t₀] 1 γ := hγ_smooth.contMDiffOn
    have hlb := radialDist_endpoint_le_pathELength (I := I) g p hEnorm
      (a := (0 : ℝ)) (b := t₀) ht₀_nn hγ0 hγ_pref hsrc' hbball' hdom'
    have hendpt : Real.sqrt (g.inner p (ψ (γ t₀)) (ψ (γ t₀))) = δ := by
      have : hM (γ t₀) = δ := ht₀_eq_δ
      rwa [hhM_def, hnE_def, hBp_def] at this
    rw [hendpt] at hlb
    have hpath_mono : pathELength I γ (0 : ℝ) t₀ ≤ pathELength I γ (0 : ℝ) 1 := by
      have hadd : pathELength I γ (0:ℝ) t₀ + pathELength I γ t₀ 1 = pathELength I γ (0:ℝ) 1 :=
        pathELength_add (γ := γ) (I := I) ht₀_nn ht₀_le1
      calc pathELength I γ (0:ℝ) t₀ ≤ pathELength I γ (0:ℝ) t₀ + pathELength I γ t₀ 1 :=
            le_self_add
        _ = pathELength I γ (0:ℝ) 1 := hadd
    have hSlt : ENNReal.ofReal S < ENNReal.ofReal δ :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS_nn |>.mpr hSδ
    calc ENNReal.ofReal S < ENNReal.ofReal δ := hSlt
      _ ≤ pathELength I γ (0:ℝ) t₀ := hlb
      _ ≤ pathELength I γ (0:ℝ) 1 := hpath_mono
      _ < r := hγ_len

private theorem minimizer_confined_to_C2_ball
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsmall_g : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Set.Icc a b] 1 γ) (hγa : γ a = p)
    (hγ_inBall : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hlen_le : pathELength I γ a b ≤
      ENNReal.ofReal (Real.sqrt (g.inner p v v))) :
    ∀ t ∈ Set.Icc a b,
      ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
        expMapC2Radius (I := I) g p := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set S : ℝ := Real.sqrt (g.inner p v v) with hS_def
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hccont : ContinuousOn c (Set.Icc a b) := hψcont.comp hγcont hγ_inBall
  have hρc : ContinuousOn ρ (Set.Icc a b) :=
    ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
  have hρ_to_ball : ∀ {t : ℝ}, ρ t < expRadiusGp (I := I) g p →
      ‖c t‖ < expMapC2Radius (I := I) g p := by
    intro t ht
    exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p ht
  suffices hbound : ∀ t ∈ Set.Icc a b, ρ t < expRadiusGp (I := I) g p by
    intro t ht
    exact hρ_to_ball (hbound t ht)
  obtain ⟨δ, hSδ, hδR⟩ := exists_between hsmall_g
  have hδ_pos : 0 < δ := lt_of_le_of_lt hS_nn hSδ
  suffices hle : ∀ t ∈ Set.Icc a b, ρ t ≤ δ by
    intro t ht; exact lt_of_le_of_lt (hle t ht) hδR
  by_contra hcon
  simp only [not_forall, not_le, exists_prop] at hcon
  obtain ⟨t', ht'Icc, ht'δ⟩ := hcon
  set Z : Set ℝ := {t ∈ Set.Icc a b | δ ≤ ρ t} with hZ_def
  have hZne : Z.Nonempty := ⟨t', ht'Icc, ht'δ.le⟩
  have hZbdd : BddBelow Z := ⟨a, fun t ht => ht.1.1⟩
  set t₀ : ℝ := sInf Z with ht₀_def
  have ht₀_lb : a ≤ t₀ := le_csInf hZne (fun t ht => ht.1.1)
  have ht₀_ub : t₀ ≤ b := by
    obtain ⟨t, ht⟩ := hZne; exact le_trans (csInf_le hZbdd ht) ht.1.2
  have ht₀Icc : t₀ ∈ Set.Icc a b := ⟨ht₀_lb, ht₀_ub⟩
  have hpre : ∀ s ∈ Set.Icc a b, s < t₀ → ρ s < δ := by
    intro s hs hst₀
    by_contra hns
    have hns' : δ ≤ ρ s := not_lt.mp hns
    have hsZ : s ∈ Z := ⟨hs, hns'⟩
    exact absurd (csInf_le hZbdd hsZ) (not_le.mpr hst₀)
  have hρt₀_ge : δ ≤ ρ t₀ := by
    have hZclosed : IsClosed Z := by
      have h2 : Z = Set.Icc a b ∩ ρ ⁻¹' (Set.Ici δ) := by
        ext t; simp only [hZ_def, Set.mem_setOf_eq, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_Ici]
      rw [h2]
      exact hρc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have ht₀mem : t₀ ∈ Z := by
      rw [← hZclosed.closure_eq]
      exact csInf_mem_closure hZne hZbdd
    exact ht₀mem.2
  have hρt₀_le : ρ t₀ ≤ δ := by
    rcases eq_or_lt_of_le ht₀_lb with h0 | h0
    · rw [← h0]
      have hca : c a = 0 := by
        rw [hc_def]; simp only; rw [hγa, hψ_def]
        exact NormalCoordinates.normalChartAt_centre (I := I) g p
      rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero]; exact hδ_pos.le
    · have htend : Filter.Tendsto ρ (nhdsWithin t₀ (Set.Iio t₀)) (nhds (ρ t₀)) :=
        (hρc.continuousWithinAt ht₀Icc).mono_of_mem_nhdsWithin (by
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi a, isOpen_Ioi, h0, by
            intro z hz; exact ⟨hz.1.le, le_trans hz.2.le ht₀_ub⟩⟩)
      have hev : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀), ρ s ≤ δ := by
        have hpos : Set.Ioo a t₀ ∈ nhdsWithin t₀ (Set.Iio t₀) := by
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi a, isOpen_Ioi, h0, by intro z hz; exact ⟨hz.1, hz.2⟩⟩
        filter_upwards [hpos] with s hs
        exact (hpre s ⟨hs.1.le, le_trans hs.2.le ht₀_ub⟩ hs.2).le
      haveI : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := nhdsLT_neBot t₀
      exact le_of_tendsto htend hev
  have ht₀_eq : ρ t₀ = δ := le_antisymm hρt₀_le hρt₀_ge
  have hpref_le : ∀ s ∈ Set.Icc a t₀, ρ s ≤ δ := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]; exact hρt₀_le
    · exact (hpre s ⟨hs.1, le_trans hs.2 ht₀_ub⟩ h).le
  have hsrc' : ∀ s ∈ Set.Icc a t₀, γ s ∈ ψ.source :=
    fun s hs => hγ_inBall s ⟨hs.1, le_trans hs.2 ht₀_ub⟩
  have hbball' : ∀ s ∈ Set.Icc a t₀, ‖ψ (γ s)‖ < expMapC2Radius (I := I) g p := by
    intro s hs
    exact hρ_to_ball (lt_of_le_of_lt (hpref_le s hs) hδR)
  have hdom' : ∀ s ∈ Set.Icc a t₀,
      (show TangentSpace I p from ψ (γ s)) ∈ expDomain (I := I) g p :=
    fun s hs => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball' s hs)
  have hγ_pref : CMDiff[Set.Icc a t₀] 1 γ := hγ.mono (Set.Icc_subset_Icc le_rfl ht₀_ub)
  have hlb := radialDist_endpoint_le_pathELength (I := I) g p hEnorm
    (a := a) (b := t₀) ht₀_lb hγa hγ_pref hsrc' hbball' hdom'
  have hendpt : Real.sqrt (g.inner p (ψ (γ t₀)) (ψ (γ t₀))) = δ := by
    have : ρ t₀ = δ := ht₀_eq
    rwa [hρ_def, hc_def, hB_def] at this
  rw [hendpt] at hlb
  have hpath_mono : pathELength I γ a t₀ ≤ pathELength I γ a b := by
    have hadd : pathELength I γ a t₀ + pathELength I γ t₀ b = pathELength I γ a b :=
      pathELength_add (γ := γ) (I := I) ht₀_lb ht₀_ub
    calc pathELength I γ a t₀ ≤ pathELength I γ a t₀ + pathELength I γ t₀ b := le_self_add
      _ = pathELength I γ a b := hadd
  have hδS : ENNReal.ofReal δ ≤ ENNReal.ofReal S := by
    calc ENNReal.ofReal δ ≤ pathELength I γ a t₀ := hlb
      _ ≤ pathELength I γ a b := hpath_mono
      _ ≤ ENNReal.ofReal S := hlen_le
  have hδS' : δ ≤ S := (ENNReal.ofReal_le_ofReal_iff hS_nn).mp hδS
  exact absurd hδS' (not_le.mpr hSδ)

private theorem radial_minimizer_radiality
    (g : SmoothRiemannianMetric I M) (p : M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : CMDiff[Set.Icc a b] 1 γ) (hγa : γ a = p)
    (hγ_inBall : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hbball : ∀ t ∈ Set.Icc a b,
      ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
        expMapC2Radius (I := I) g p)
    (hlen : pathELength I γ a b =
      ENNReal.ofReal (Real.sqrt
        (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ b))
          (NormalCoordinates.normalChartAt (I := I) g p (γ b))))) :
    (∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
        Real.sqrt (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ s))
            (NormalCoordinates.normalChartAt (I := I) g p (γ s)))
          ≤ Real.sqrt (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
            (NormalCoordinates.normalChartAt (I := I) g p (γ t)))) ∧
    (∀ t ∈ Set.Ioo a b,
      NormalCoordinates.normalChartAt (I := I) g p (γ t) ≠ 0 →
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ)
        = (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
              (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
                (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ))
            / g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
                (NormalCoordinates.normalChartAt (I := I) g p (γ t)))
          • NormalCoordinates.normalChartAt (I := I) g p (γ t)) := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  set φ : ℝ → ℝ := fun t =>
    Real.sqrt (g.inner (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1))
    with hφ_def
  have hdom : ∀ t ∈ Set.Icc a b,
      (show TangentSpace I p from ψ (γ t)) ∈ expDomain (I := I) g p :=
    fun t ht => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball t ht)
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hccont : ContinuousOn c (Set.Icc a b) := hψcont.comp hγcont hγ_inBall
  have hρc : ContinuousOn ρ (Set.Icc a b) :=
    ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
  have hca : c a = 0 := by
    rw [hc_def]; simp only; rw [hγa, hψ_def]
    exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hρa0 : ρ a = 0 := by rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero]
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    refine ⟨?_, ?_⟩
    · intro s t hs ht hst
      have hsa : s = a := le_antisymm hs.2 hs.1
      have hta : t = a := le_antisymm ht.2 ht.1
      rw [hsa, hta]
    · intro t ht; exact absurd ht (by simp)
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := fun x hx => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact (uniqueDiffOn_Icc hab_lt) x hx
  have hLift : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := fun t ht => by simpa using ht
  have hVel : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)) (Set.Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin (le_refl 1) hUnique).comp
      hLift.continuousOn hMaps).congr (fun t _ => rfl)
  have hφc : ContinuousOn φ (Set.Icc a b) := by
    rw [hφ_def]
    exact Real.continuous_sqrt.comp_continuousOn
      (Variation.continuousOn_g_inner_along_curve (I := I) g hVel hVel)
  have hφnn : ∀ t ∈ Set.Icc a b, 0 ≤ φ t := fun t _ => Real.sqrt_nonneg _
  have hφint : MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume :=
    hφc.integrableOn_compact isCompact_Icc
  have hsrc : ∀ t ∈ Set.Icc a b, γ t ∈ ψ.source := hγ_inBall
  have hφcont : ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x := by
    intro x hx
    refine (hφc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
      intro z hz; exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
  have hφ_eq_mfderiv : ∀ t ∈ Set.Ioo a b,
      φ t = Real.sqrt
        (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) := by
    intro t ht
    rw [hφ_def]; simp only
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    set cv : E := mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x 1 with hcv_def
    have hcderiv : HasDerivWithinAt c cv (Set.Ici x) x := by
      have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
        (hγ.mdifferentiableOn (by norm_num)) x hxIcc
      have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
        (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)
      have hcomp : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x :=
        hψdiff.comp x hγdiff (fun t ht => hsrc t ht)
      have hmf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x) := hcomp.hasMFDerivWithinAt
      rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hmf
      have hHDW : HasDerivWithinAt c cv (Set.Icc a b) x := hmf.hasDerivWithinAt
      refine hHDW.mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz; exact ⟨le_trans hx.1 hz.2, le_of_lt hz.1⟩⟩
    by_cases hcx : c x = 0
    · have htend : Filter.Tendsto (fun z => slope ρ x z)
          (nhdsWithin x (Set.Ioi x)) (nhds (Real.sqrt (B cv cv))) := by
        have hcz : Filter.Tendsto (fun z => (z - x)⁻¹ • c z)
            (nhdsWithin x (Set.Ioi x)) (nhds cv) := by
          have h0 := hcderiv.mono (Set.Ioi_subset_Ici_self)
          rw [hasDerivWithinAt_iff_tendsto_slope] at h0
          have hset : Set.Ioi x \ {x} = Set.Ioi x := by
            ext z; simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_singleton_iff]
            exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
          rw [hset] at h0
          refine (Filter.tendsto_congr' ?_).mp h0
          filter_upwards with z; rw [slope_def_module, hcx, sub_zero]
        have hcont : Continuous (fun w : E => Real.sqrt (B w w)) := by fun_prop
        have htend2 := (hcont.tendsto cv).comp hcz
        refine (Filter.tendsto_congr' ?_).mp htend2
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hzx : 0 < z - x := sub_pos.mpr hz
        have heq : slope ρ x z
            = Real.sqrt (B ((z - x)⁻¹ • c z) ((z - x)⁻¹ • c z)) := by
          rw [hρ_def, slope_def_module, hcx]
          simp only [map_zero, Real.sqrt_zero, sub_zero, smul_eq_mul, map_smul,
            ContinuousLinearMap.smul_apply]
          rw [show (z - x)⁻¹ * ((z - x)⁻¹ * B (c z) (c z))
              = ((z - x)⁻¹) ^ 2 * B (c z) (c z) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
        simp only [Function.comp_apply]
        exact heq.symm
      have hφx_eq : φ x = Real.sqrt (B cv cv) := by
        have hγx_p : γ x = p := by
          have hcx' : ψ (γ x) = 0 := hcx
          have hpsrc : p ∈ ψ.source := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p
          have hψp : ψ p = 0 := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g p
          exact ψ.injOn (hsrc x hxIcc) hpsrc (by rw [hcx', hψp])
        have hcv_eq : cv = mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x 1 := by
          rw [hcv_def]
          have hUnique : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Set.Icc a b) x := by
            rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact (uniqueDiffOn_Icc hab_lt) x hxIcc
          have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
            (hγ.mdifferentiableOn (by norm_num)) x hxIcc
          have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
            (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
              one_ne_zero (γ x) (hsrc x hxIcc)
          have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E))
            (f := γ) (g := ψ) (s := Set.Icc a b) (u := ψ.source) x hψdiff hγdiff
            (fun t ht => hsrc t ht) hUnique
          have hcomp_eq : c = ψ ∘ γ := rfl
          rw [hcomp_eq, hchain]
          simp only [Function.comp_apply]
          have hsource_nhds : ψ.source ∈ nhds (γ x) :=
            (NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc)
          rw [mfderivWithin_of_mem_nhds hsource_nhds, hγx_p,
            NormalCoordinates.mfderiv_normalChartAt_self]
          rfl
        simp only [hφ_def]
        rw [hcv_eq, hγx_p, hB_def]; rfl
      rw [hφx_eq] at hr
      exact (htend.eventually_lt_const hr).frequently
    · have hxIoo : x ∈ Set.Ioo a b := by
        refine ⟨lt_of_le_of_ne hx.1 ?_, hx.2⟩
        intro hxa; apply hcx; rw [← hxa]; exact hca
      have hmem : Set.Icc a b ∈ nhds x := Icc_mem_nhds hxIoo.1 hxIoo.2
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ x :=
        ((hγ.mdifferentiableOn (by norm_num)) x hxIcc).mdifferentiableAt hmem
      have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ x) :=
        ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)).mdifferentiableAt
          ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc))
      have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x := hψdiff.comp x hγdiff
      set cv₂ : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x 1 with hcv₂_def
      have hcHDA : HasDerivAt c cv₂ x := by
        have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x) :=
          hcdiff.hasMFDerivAt
        rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
        exact hmf.hasDerivAt
      have hpos : 0 < B (c x) (c x) := by rw [hB_def]; exact g.pos p (c x) hcx
      have hρderiv : HasDerivAt ρ (B (c x) cv₂ / Real.sqrt (B (c x) (c x))) x :=
        radialDist_hasDerivAt B hBsym c cv₂ hcHDA hpos
      set ρ' : ℝ := B (c x) cv₂ / Real.sqrt (B (c x) (c x)) with hρ'_def
      have hev : ∀ᶠ s in nhds x, γ s ∈ ψ.source := by
        have hopen : Set.Ioo a b ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
        filter_upwards [hopen] with s hs using hsrc s (Ioo_subset_Icc_self hs)
      have hball : ‖ψ (γ x)‖ < expMapC2Radius (I := I) g p := hbball x hxIcc
      have hune : ψ (γ x) ≠ 0 := hcx
      have hgauss := gauss_pointwise_speed_lower_bound (I := I) g p hγdiff
        (hsrc x hxIcc) (hdom x hxIcc) hball hune hev
      have hcv₂_eq : cv₂ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => ψ (γ s)) x (1 : ℝ) := rfl
      have hρ'sq_le : ρ' ^ 2 ≤
          g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) := by
        have hρ'sq : ρ' ^ 2 = (B (c x) cv₂) ^ 2 / B (c x) (c x) := by
          rw [hρ'_def, div_pow, Real.sq_sqrt hpos.le]
        rw [hρ'sq, hcv₂_eq, hB_def]
        exact hgauss
      have hφx_eq : φ x = Real.sqrt
          (g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1)) := by
        simp only [hφ_def]
        rw [mfderivWithin_of_mem_nhds hmem]
      have hρ'_le : ρ' ≤ φ x := by
        rw [hφx_eq]
        calc ρ' ≤ |ρ'| := le_abs_self _
          _ = Real.sqrt (ρ' ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ _ := Real.sqrt_le_sqrt hρ'sq_le
      have hρ'_lt : ρ' < r := lt_of_le_of_lt hρ'_le hr
      exact (hρderiv.hasDerivWithinAt (s := Set.Ici x)).liminf_right_slope_le hρ'_lt
  have hpath_eq : pathELength I γ a b = ENNReal.ofReal (∫ t in a..b, φ t) := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo,
      intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hφint.mono_set Ioo_subset_Icc_self)
        (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
            using hφnn x (Ioo_subset_Icc_self hx))]
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only
    rw [hφ_eq_mfderiv t ht]
    exact hEnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
  have hφii : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      IntervalIntegrable φ MeasureTheory.volume s t := by
    intro s t has hst htb
    refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hst]
    exact hφint.mono_set (Set.Icc_subset_Icc has htb)
  have hint_nn : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ∫ u in s..t, φ u := by
    intro s t has hst htb
    rw [intervalIntegral.integral_of_le hst]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun u hu => hφnn u ⟨le_trans has (le_of_lt hu.1), le_trans hu.2 htb⟩)
  have hρb_nn : 0 ≤ ρ b := Real.sqrt_nonneg _
  have hρb_int : ρ b = ∫ t in a..b, φ t := by
    have hρb_eq : ρ b = Real.sqrt
        (g.inner p (ψ (γ b)) (ψ (γ b))) := rfl
    have h : ENNReal.ofReal (ρ b) = ENNReal.ofReal (∫ t in a..b, φ t) := by
      rw [hρb_eq, ← hlen, hpath_eq]
    exact (ENNReal.ofReal_eq_ofReal_iff hρb_nn (hint_nn a b le_rfl hab le_rfl)).mp h
  have hρ_le_int : ∀ t ∈ Set.Icc a b, ρ t ≤ ∫ s in a..t, φ s := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    refine image_radialDist_le_intervalIntegral_of_slope_le hat
      (hρc.mono (Set.Icc_subset_Icc le_rfl htb)) (le_of_eq hρa0)
      (hφint.mono_set (Set.Icc_subset_Icc le_rfl htb)) ?_ ?_
    · intro x hx
      exact hφcont x ⟨hx.1, lt_of_lt_of_le hx.2 htb⟩
    · intro x hx r hr
      exact hslope x ⟨hx.1, lt_of_lt_of_le hx.2 htb⟩ r hr
  have hρb_sub_le : ∀ t ∈ Set.Icc a b, ρ b - ρ t ≤ ∫ s in t..b, φ s := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hkey := image_radialDist_le_intervalIntegral_of_slope_le
      (ρ := fun s => ρ s - ρ t) (φ := φ) htb
      ((hρc.mono (Set.Icc_subset_Icc hat le_rfl)).sub continuousOn_const)
      (by simp) (hφint.mono_set (Set.Icc_subset_Icc hat le_rfl)) ?_ ?_
    · simpa using hkey
    · intro x hx
      exact hφcont x ⟨le_trans hat hx.1, hx.2⟩
    · intro x hx r hr
      have hsl := hslope x ⟨le_trans hat hx.1, hx.2⟩ r hr
      refine hsl.mono (fun z hz => ?_)
      have hsleq : slope (fun s => ρ s - ρ t) x z = slope ρ x z := by
        rw [slope_def_field, slope_def_field]; ring_nf
      rw [hsleq]; exact hz
  have hρ_int : ∀ t ∈ Set.Icc a b, ρ t = ∫ s in a..t, φ s := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hsplit : (∫ s in a..t, φ s) + ∫ s in t..b, φ s = ∫ s in a..b, φ s :=
      intervalIntegral.integral_add_adjacent_intervals
        (hφii a t le_rfl hat htb) (hφii t b hat htb le_rfl)
    have hle1 := hρ_le_int t ht
    have hle2 := hρb_sub_le t ht
    have : ρ b ≤ ∫ s in a..b, φ s := by
      rw [← hsplit]
      calc ρ b = ρ t + (ρ b - ρ t) := by ring
        _ ≤ (∫ s in a..t, φ s) + ∫ s in t..b, φ s := add_le_add hle1 hle2
    rw [hρb_int] at this
    have heq1 : ρ t = ∫ s in a..t, φ s := by
      by_contra hne
      have hlt1 : ρ t < ∫ s in a..t, φ s := lt_of_le_of_ne hle1 hne
      have : ρ b < ∫ s in a..b, φ s := by
        rw [← hsplit]
        calc ρ b = ρ t + (ρ b - ρ t) := by ring
          _ < (∫ s in a..t, φ s) + ∫ s in t..b, φ s := by
              exact add_lt_add_of_lt_of_le hlt1 hle2
      rw [hρb_int] at this; exact absurd rfl (ne_of_lt this)
    exact heq1
  have hmono : ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t → ρ s ≤ ρ t := by
    intro s t hs ht hst
    rw [hρ_int s hs, hρ_int t ht]
    have hsub : (∫ u in a..t, φ u) - ∫ u in a..s, φ u = ∫ u in s..t, φ u := by
      rw [intervalIntegral.integral_interval_sub_left
        (hφii a t le_rfl ht.1 ht.2) (hφii a s le_rfl hs.1 hs.2)]
    have hnn : 0 ≤ ∫ u in s..t, φ u := hint_nn s t hs.1 hst ht.2
    linarith [hsub ▸ hnn]
  refine ⟨fun s t hs ht hst => ?_, ?_⟩
  · have := hmono s t hs ht hst
    rwa [hρ_def, hc_def, hB_def] at this
  · intro t ht hne
    have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hmem : Set.Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      ((hγ.mdifferentiableOn (by norm_num)) t htIcc).mdifferentiableAt hmem
    have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ t) :=
      ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
        one_ne_zero (γ t) (hsrc t htIcc)).mdifferentiableAt
        ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc t htIcc))
    have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t := hψdiff.comp t hγdiff
    set cv₂ : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 with hcv₂_def
    have hcHDA : HasDerivAt c cv₂ t := by
      have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t) :=
        hcdiff.hasMFDerivAt
      rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
      exact hmf.hasDerivAt
    have hcx_ne : c t ≠ 0 := hne
    have hpos : 0 < B (c t) (c t) := by rw [hB_def]; exact g.pos p (c t) hcx_ne
    have hρderiv1 : HasDerivAt ρ (B (c t) cv₂ / Real.sqrt (B (c t) (c t))) t :=
      radialDist_hasDerivAt B hBsym c cv₂ hcHDA hpos
    have hρderiv2 : HasDerivAt ρ (φ t) t := by
      have hftc : HasDerivAt (fun u => ∫ s in a..u, φ s) (φ t) t :=
        intervalIntegral.integral_hasDerivAt_right
          (hφii a t le_rfl (le_of_lt ht.1) (le_of_lt ht.2))
          ⟨Set.Icc a b, hmem, hφc.aestronglyMeasurable measurableSet_Icc⟩
          (hφc.continuousAt hmem)
      refine hftc.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hρ_int s (Ioo_subset_Icc_self hs)
    have hρ'_eq : B (c t) cv₂ / Real.sqrt (B (c t) (c t)) = φ t :=
      hρderiv1.unique hρderiv2
    have hev : ∀ᶠ s in nhds t, γ s ∈ ψ.source := by
      have hopen : Set.Ioo a b ∈ nhds t := isOpen_Ioo.mem_nhds ht
      filter_upwards [hopen] with s hs using hsrc s (Ioo_subset_Icc_self hs)
    have hball : ‖ψ (γ t)‖ < expMapC2Radius (I := I) g p := hbball t htIcc
    have hgauss := gauss_pointwise_speed_lower_bound (I := I) g p hγdiff
      (hsrc t htIcc) (hdom t htIcc) hball hne hev
    have hcv₂_eq : cv₂ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => ψ (γ s)) t (1 : ℝ) := rfl
    have hφt_sq : φ t ^ 2 =
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hφ_def]; simp only
      rw [mfderivWithin_of_mem_nhds hmem, Real.sq_sqrt]
      rcases eq_or_ne (mfderiv 𝓘(ℝ, ℝ) I γ t 1) 0 with h0 | h0
      · rw [h0]; simp
      · exact (g.pos (γ t) _ h0).le
    have hLHS_sq : (B (c t) cv₂) ^ 2 / B (c t) (c t) = φ t ^ 2 := by
      have : (B (c t) cv₂ / Real.sqrt (B (c t) (c t))) ^ 2 = φ t ^ 2 := by rw [hρ'_eq]
      rwa [div_pow, Real.sq_sqrt hpos.le] at this
    have htight : (B (c t) cv₂) ^ 2 / B (c t) (c t) =
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hLHS_sq, hφt_sq]
    have hchain := radial_chain_mfderiv (I := I) g p hγdiff (hsrc t htIcc) hball hev
    have hbase : expMap (I := I) g p (show TangentSpace I p from (ψ (γ t))) = γ t :=
      expMap_normalChartAt (I := I) g p (hsrc t htIcc)
    have hdexp : mfderiv 𝓘(ℝ, E) I
        (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
        (show TangentSpace I p from cv₂) = mfderiv 𝓘(ℝ, ℝ) I γ t 1 :=
      hchain.symm
    have hRHS :
        g.inner (expMap (I := I) g p (show TangentSpace I p from (ψ (γ t))))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂)) =
          g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hdexp, hbase]
    have hgauss_eq :
        (g.inner p (ψ (γ t)) cv₂) ^ 2 / g.inner p (ψ (γ t)) (ψ (γ t)) =
          g.inner (expMap (I := I) g p (show TangentSpace I p from (ψ (γ t))))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂)) := by
      rw [hRHS]; exact htight
    have hiff := gauss_radial_lower_bound_eq_iff (I := I) g p (hdom t htIcc) hball hne cv₂
    have horth_dexp := hiff.mp hgauss_eq
    have hinj := mfderiv_expMap_injective_of_norm_lt_radius (I := I) g p hball
    have horth_zero :
        cv₂ - (g.inner p (ψ (γ t)) cv₂ / g.inner p (ψ (γ t)) (ψ (γ t))) • (ψ (γ t)) = 0 :=
      hinj (horth_dexp.trans (ContinuousLinearMap.map_zero _).symm)
    have hradial : cv₂ =
        (g.inner p (ψ (γ t)) cv₂ / g.inner p (ψ (γ t)) (ψ (γ t))) • (ψ (γ t)) :=
      sub_eq_zero.mp horth_zero
    rw [hcv₂_eq] at hradial
    exact hradial

set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
theorem normalBall_radial_minimizer_equality
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (hsmall_g : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : CMDiff[Set.Icc a b] 1 γ)
    (hγa : γ a = p)
    (hγb : γ b = expMap (I := I) g p (show TangentSpace I p from v))
    (hγ_inBall : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hlen : pathELength I γ a b =
      ENNReal.ofReal (Real.sqrt (g.inner p v v))) :
    ∃ φ : ℝ → ℝ, MonotoneOn φ (Set.Icc a b) ∧ φ a = 0 ∧ φ b = 1 ∧
      ∀ t ∈ Set.Icc a b,
        γ t = expMap (I := I) g p (show TangentSpace I p from (φ t • v)) := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set S : ℝ := Real.sqrt (g.inner p v v) with hS_def
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  have hca : c a = 0 := by
    rw [hc_def]; simp only; rw [hγa, hψ_def]
    exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hcb : c b = v := by
    have hsymm := NormalCoordinates.normalChartAt_symm_apply (I := I) g p (v := v) hball
    have hrinv := NormalCoordinates.normalChartAt_right_inv (I := I) g p hball
    change ψ (γ b) = v
    rw [hγb, hψ_def, ← hsymm, hrinv]
  have hρa : ρ a = 0 := by rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero]
  have hρb : ρ b = S := by
    change Real.sqrt (B (c b) (c b)) = S
    rw [hcb]; rfl
  have hSsq : S ^ 2 = B v v := by
    rw [hS_def]
    exact Real.sq_sqrt (hBnn v)
  have hbball : ∀ t ∈ Set.Icc a b,
      ‖ψ (γ t)‖ < expMapC2Radius (I := I) g p :=
    minimizer_confined_to_C2_ball (I := I) g p hEnorm hsmall_g hγ hγa hγ_inBall (le_of_eq hlen)
  have hψγb : NormalCoordinates.normalChartAt (I := I) g p (γ b) = v := by
    rw [← hψ_def]; exact hcb
  have hlen' : pathELength I γ a b = ENNReal.ofReal (Real.sqrt
      (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ b))
        (NormalCoordinates.normalChartAt (I := I) g p (γ b)))) := by
    rw [hlen, hψγb]
  obtain ⟨hmono, hradial⟩ :=
    radial_minimizer_radiality (I := I) g p hEnorm (le_of_lt hab) hγ hγa hγ_inBall hbball hlen'
  have hρmono : ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t → ρ s ≤ ρ t := by
    intro s t hs ht hst; exact hmono s t hs ht hst
  have hρnn : ∀ t, 0 ≤ ρ t := fun t => Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hS_nn with hS0 | hSpos
  · have hSeq : S = 0 := hS0.symm
    have hvz : v = 0 := by
      have : B v v = 0 := by rw [← hSsq, hSeq]; ring
      by_contra hv0
      exact absurd this (ne_of_gt (by rw [hB_def]; exact g.pos p v hv0))
    have hρ0 : ∀ t ∈ Set.Icc a b, ρ t = 0 := by
      intro t ht
      refine le_antisymm ?_ (hρnn t)
      calc ρ t ≤ ρ b := hρmono t b ht ⟨le_of_lt hab, le_rfl⟩ ht.2
        _ = 0 := by rw [hρb, hSeq]
    have hct0 : ∀ t ∈ Set.Icc a b, c t = 0 := by
      intro t ht
      have : B (c t) (c t) = 0 := by
        have h := hρ0 t ht; rw [hρ_def] at h; simp only at h
        nlinarith [Real.sq_sqrt (hBnn (c t)), Real.sqrt_nonneg (B (c t) (c t)), h,
          Real.sq_sqrt (hBnn (c t))]
      by_contra hc0
      exact absurd this (ne_of_gt (by rw [hB_def]; exact g.pos p (c t) hc0))
    refine ⟨fun t => (t - a) / (b - a), ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      simp only
      gcongr
      linarith
    · simp only [sub_self, zero_div]
    · simp only; rw [div_self (by linarith : b - a ≠ 0)]
    · intro t ht
      have hctz : c t = 0 := hct0 t ht
      have hγtp : γ t = p := by
        have : ψ (γ t) = ψ p := by
          rw [show ψ (γ t) = c t from rfl, hctz, hψ_def,
            NormalCoordinates.normalChartAt_centre (I := I) g p]
        exact ψ.injOn (hγ_inBall t ht)
          (by rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p) this
      rw [hγtp, hvz, smul_zero]
      have h0tgt : (0 : E) ∈ (NormalCoordinates.normalChartAt (I := I) g p).target :=
        NormalCoordinates.zero_mem_normalChartAt_target (I := I) g p
      have hsymm := NormalCoordinates.normalChartAt_symm_apply (I := I) g p
        (v := (0 : E)) h0tgt
      rw [NormalCoordinates.normalChartAt_symm_zero (I := I) g p] at hsymm
      exact hsymm
  · have hSpos' : 0 < S := hSpos
    have hcderiv : ∀ t ∈ Set.Ioo a b,
        HasDerivAt c (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) t := by
      intro t ht
      have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hmem : Set.Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
        ((hγ.mdifferentiableOn (by norm_num)) t htIcc).mdifferentiableAt hmem
      have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ t) :=
        ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ t) (hγ_inBall t htIcc)).mdifferentiableAt
          ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hγ_inBall t htIcc))
      have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t := hψdiff.comp t hγdiff
      have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t) :=
        hcdiff.hasMFDerivAt
      rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
      exact hmf.hasDerivAt
    have hccont : ContinuousOn c (Set.Icc a b) :=
      ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn).comp
        hγ.continuousOn hγ_inBall
    have hρc : ContinuousOn ρ (Set.Icc a b) :=
      ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
    set θ : ℝ → E := fun t => (ρ t)⁻¹ • c t with hθ_def
    have hθderiv : ∀ t ∈ Set.Ioo a b, 0 < ρ t → HasDerivAt θ 0 t := by
      intro t ht hρt
      have hct_ne : c t ≠ 0 := by
        intro h0
        have : ρ t = 0 := by rw [hρ_def]; simp only [h0, map_zero, Real.sqrt_zero]
        exact absurd this (ne_of_gt hρt)
      have hBpos : 0 < B (c t) (c t) := by rw [hB_def]; exact g.pos p (c t) hct_ne
      have hc' : HasDerivAt c (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) t := hcderiv t ht
      have hρ' : HasDerivAt ρ
          (B (c t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) / Real.sqrt (B (c t) (c t))) t :=
        radialDist_hasDerivAt B hBsym c (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) hc' hBpos
      have hρt_eq : Real.sqrt (B (c t) (c t)) = ρ t := rfl
      rw [hρt_eq] at hρ'
      have hrad' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1
          = (B (c t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) / B (c t) (c t)) • (c t) :=
        hradial t ht (by
          show NormalCoordinates.normalChartAt (I := I) g p (γ t) ≠ 0
          rw [← hψ_def]; exact hct_ne)
      have hρtsq : ρ t ^ 2 = B (c t) (c t) := by
        rw [hρ_def]; simp only; rw [Real.sq_sqrt (hBnn (c t))]
      exact angular_hasDerivAt_zero B hc' hρt hρ' hρtsq hrad'
    have hθb : θ b = (S)⁻¹ • v := by
      rw [hθ_def]; simp only [hρb, hcb]
    have hθ_const : ∀ t ∈ Set.Ioo a b, 0 < ρ t → θ t = θ b := by
      intro t ht hρt
      have hρpos_on : ∀ s ∈ Set.Icc t b, 0 < ρ s := by
        intro s hs
        have hsIcc : s ∈ Set.Icc a b := ⟨le_trans (le_of_lt ht.1) hs.1, hs.2⟩
        exact lt_of_lt_of_le hρt
          (hρmono t s ⟨le_of_lt ht.1, le_of_lt ht.2⟩ hsIcc hs.1)
      have hθcont : ContinuousOn θ (Set.Icc t b) := by
        apply ContinuousOn.smul
        · apply ContinuousOn.inv₀
          · exact (hρc.mono (Set.Icc_subset_Icc (le_of_lt ht.1) le_rfl))
          · exact fun s hs => ne_of_gt (hρpos_on s hs)
        · exact hccont.mono (Set.Icc_subset_Icc (le_of_lt ht.1) le_rfl)
      have hθrd : ∀ x ∈ Set.Ico t b, HasDerivWithinAt θ 0 (Set.Ici x) x := by
        intro x hx
        have hxIoo : x ∈ Set.Ioo a b := ⟨lt_of_lt_of_le ht.1 hx.1, hx.2⟩
        have hρx : 0 < ρ x := hρpos_on x ⟨hx.1, le_of_lt hx.2⟩
        exact (hθderiv x hxIoo hρx).hasDerivWithinAt
      have hconst := constant_of_has_deriv_right_zero hθcont hθrd
      exact (hconst b (Set.right_mem_Icc.2 (le_of_lt ht.2))).symm
    have hc_formula : ∀ t ∈ Set.Icc a b, c t = (ρ t / S) • v := by
      intro t ht
      rcases eq_or_lt_of_le (hρnn t) with hρt0 | hρtpos
      · have hct0 : c t = 0 := by
          have : B (c t) (c t) = 0 := by
            have h : ρ t = 0 := hρt0.symm
            rw [hρ_def] at h; simp only at h
            nlinarith [Real.sq_sqrt (hBnn (c t)), Real.sqrt_nonneg (B (c t) (c t)), h]
          by_contra hc0
          exact absurd this (ne_of_gt (by rw [hB_def]; exact g.pos p (c t) hc0))
        rw [hct0, ← hρt0, zero_div, zero_smul]
      · rcases eq_or_lt_of_le ht.2 with htb | htb
        · rw [htb, hcb, hρb, div_self (ne_of_gt hSpos'), one_smul]
        · have hta : a < t := by
            rcases eq_or_lt_of_le ht.1 with hta | hta
            · exfalso; rw [← hta] at hρtpos; exact (hρtpos.ne') hρa
            · exact hta
          have htIoo : t ∈ Set.Ioo a b := ⟨hta, htb⟩
          have hθt := hθ_const t htIoo hρtpos
          rw [hθb] at hθt
          have hθt' : (ρ t)⁻¹ • c t = S⁻¹ • v := hθt
          have hctv : c t = ρ t • (S⁻¹ • v) := by
            rw [← hθt', smul_smul, mul_inv_cancel₀ hρtpos.ne', one_smul]
          rw [hctv, smul_smul, div_eq_mul_inv]
    refine ⟨fun t => ρ t / S, ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      simp only
      gcongr
      exact hρmono s t hs ht hst
    · simp only [hρa, zero_div]
    · simp only [hρb, div_self (ne_of_gt hSpos')]
    · intro t ht
      have hctf := hc_formula t ht
      have hγt_symm : γ t = ψ.symm (c t) := by
        rw [hc_def]; simp only
        exact (NormalCoordinates.normalChartAt_left_inv (I := I) g p (hγ_inBall t ht)).symm
      rw [hγt_symm, hctf]
      have hwtgt : ((ρ t / S) • v) ∈
          (NormalCoordinates.normalChartAt (I := I) g p).symm.source := by
        change ((ρ t / S) • v) ∈ (NormalCoordinates.normalChartAt (I := I) g p).target
        rw [← hctf, hc_def]; simp only
        exact (NormalCoordinates.normalChartAt (I := I) g p).map_source (hγ_inBall t ht)
      change ψ.symm ((ρ t / S) • v) = _
      rw [hψ_def]
      exact NormalCoordinates.normalChartAt_symm_apply (I := I) g p hwtgt

end RadialUniqueMinimizer

section LocalRadialIdentification

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]


omit [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma radialCurve_contMDiffOn_Icc
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) :
    CMDiff[Set.Icc (0 : ℝ) 1] 1
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) := by
  intro t ht
  have hnorm : ‖t • a‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht
    have habs : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    calc |t| * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖a‖ := one_mul _
      _ < _ := ha
  exact ((radialCurve_contMDiffAt2 (I := I) g p a t hnorm).of_le
    (by norm_num)).contMDiffWithinAt

private lemma radialCurve_pathELength_eq
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) :
    pathELength I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 1
      = ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
  classical
  set γr : ℝ → M :=
    fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)
    with hγr_def
  have hintegrand : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) I γr t 1‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
    intro t ht
    have hsp := radialSpeedSq_eq_inner (I := I) g p a ha t ht
    have hsp' : g.inner (γr t) (mfderiv 𝓘(ℝ, ℝ) I γr t 1) (mfderiv 𝓘(ℝ, ℝ) I γr t 1)
        = g.inner p a a := hsp
    rw [hEnorm (γr t) (mfderiv 𝓘(ℝ, ℝ) I γr t 1), hsp']
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hintegrand]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one, mul_one]

theorem edist_exp_le_radius
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) :
    riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from a)) ≤
      ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
  set γr : ℝ → M :=
    fun u : ℝ ↦ (expMap (I := I) g p
      (show TangentSpace I p from (u • a)) : M) with hγr_def
  have hγr0 : γr 0 = p := by
    rw [hγr_def]
    simp only [zero_smul]
    exact expMap_zero (I := I) g p
  have hγr1 : γr 1 =
      expMap (I := I) g p (show TangentSpace I p from a) := by
    rw [hγr_def]
    simp only [one_smul]
  have hγr_C1 : CMDiff[Set.Icc (0 : ℝ) 1] 1 γr :=
    radialCurve_contMDiffOn_Icc (I := I) g p a ha
  have hdist := riemannianEDist_le_pathELength
    (I := I) (γ := γr) (a := 0) (b := 1) hγr_C1 rfl rfl zero_le_one
  rw [hγr0, hγr1,
    radialCurve_pathELength_eq (I := I) g p a hEnorm ha] at hdist
  exact hdist

private theorem radial_riemannianEDist_eq_radius
    (g : SmoothRiemannianMetric I M) (p : M) {a : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (ha_dom : (show TangentSpace I p from a) ∈ expDomain (I := I) g p)
    (ha_ball : a ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (ha_small : Real.sqrt (g.inner p a a) < expRadiusGp (I := I) g p) :
    riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from a))
      = ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
  classical
  have ha_eucl : ‖a‖ < expMapC2Radius (I := I) g p :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p ha_small
  have hge : ENNReal.ofReal (Real.sqrt (g.inner p a a)) ≤
      riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from a)) :=
    normalBall_radial_length_le_riemannianEDist (I := I) g p hEnorm ha_dom ha_ball ha_small
  have hle : riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from a))
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
    set γr : ℝ → M :=
      fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)
      with hγr_def
    have hγr0 : γr 0 = p := by
      rw [hγr_def]; simp only [zero_smul]; exact expMap_zero (I := I) g p
    have hγr1 : γr 1 = expMap (I := I) g p (show TangentSpace I p from a) := by
      rw [hγr_def]; simp only [one_smul]
    have hγr_C1 : CMDiff[Set.Icc (0 : ℝ) 1] 1 γr :=
      radialCurve_contMDiffOn_Icc (I := I) g p a ha_eucl
    have hdist_le : riemannianEDist I (γr 0) (γr 1) ≤ pathELength I γr 0 1 :=
      riemannianEDist_le_pathELength (I := I) (γ := γr) (a := 0) (b := 1)
        hγr_C1 rfl rfl zero_le_one
    rw [hγr0, hγr1] at hdist_le
    refine hdist_le.trans ?_
    rw [radialCurve_pathELength_eq (I := I) g p a hEnorm ha_eucl]
  exact le_antisymm hle hge

theorem edist_exp_eq_radius
    (g : SmoothRiemannianMetric I M) (p : M) {a : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (ha_small : Real.sqrt (g.inner p a a) < expRadiusGp (I := I) g p) :
    riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from a))
      = ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
  have ha_eucl : ‖a‖ < expMapC2Radius (I := I) g p :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p ha_small
  exact radial_riemannianEDist_eq_radius (I := I) g p hEnorm
    (mem_expDomain_of_norm_lt_radius (I := I) g p ha_eucl)
    (ball_subset_normalChartAt_target (I := I) g p ha_eucl) ha_small

omit [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem exists_forward_confinement_to_smallBall
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} {t₀ : ℝ}
    (hγ : CMDiff[Set.Icc a b] 1 γ) (ht₀ : t₀ ∈ Set.Ioo a b)
    {q : M} (hq : γ t₀ = q) :
    ∃ δ : ℝ, 0 < δ ∧ t₀ + δ ≤ b ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + δ),
        γ t ∈ (NormalCoordinates.normalChartAt (I := I) g q).source) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + δ),
        Real.sqrt (g.inner q
            (NormalCoordinates.normalChartAt (I := I) g q (γ t))
            (NormalCoordinates.normalChartAt (I := I) g q (γ t)))
          < expRadiusGp (I := I) g q) := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g q with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner q with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm q
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos q x h).le
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have ht₀Icc : t₀ ∈ Set.Icc a b := ⟨ht₀.1.le, ht₀.2.le⟩
  have hqsrc : q ∈ ψ.source := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g q
  have hψq : ψ q = 0 := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g q
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (ψ (γ t)) (ψ (γ t))) with hρ_def
  have hγt₀_src : γ t₀ ∈ ψ.source := by rw [hq]; exact hqsrc
  have hopen_src : IsOpen ψ.source := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_open_source (I := I) g q
  have hpre_nhds : γ ⁻¹' ψ.source ∈ nhdsWithin t₀ (Set.Icc a b) :=
    (hγcont t₀ ht₀Icc).preimage_mem_nhdsWithin (hopen_src.mem_nhds hγt₀_src)
  have hρt₀ : ρ t₀ = 0 := by
    rw [hρ_def]; simp only [hq, hψq, map_zero, Real.sqrt_zero]
  have hψcont : ContinuousOn ψ ψ.source := by
    rw [hψ_def]; exact (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g q).continuousOn
  have hρ_contWithin : ContinuousWithinAt ρ (Set.Icc a b ∩ γ ⁻¹' ψ.source) t₀ := by
    have hcomp : ContinuousWithinAt (fun t => ψ (γ t))
        (Set.Icc a b ∩ γ ⁻¹' ψ.source) t₀ := by
      have h1 : ContinuousWithinAt γ (Set.Icc a b ∩ γ ⁻¹' ψ.source) t₀ :=
        (hγcont t₀ ht₀Icc).mono Set.inter_subset_left
      have hmaps : Set.MapsTo γ (Set.Icc a b ∩ γ ⁻¹' ψ.source) ψ.source :=
        fun t ht => ht.2
      exact (hψcont _ hγt₀_src).comp h1 hmaps
    exact ((psd_sqrt_lipschitz B hBsym hBnn).continuous.continuousAt.comp_continuousWithinAt hcomp)
  have hR_pos : 0 < expRadiusGp (I := I) g q := expRadiusGp_pos (I := I) g q
  have hρ_small_nhds : {t | ρ t < expRadiusGp (I := I) g q} ∈
      nhdsWithin t₀ (Set.Icc a b ∩ γ ⁻¹' ψ.source) := by
    have : Set.Iio (expRadiusGp (I := I) g q) ∈ nhds (ρ t₀) := by
      rw [hρt₀]; exact isOpen_Iio.mem_nhds hR_pos
    exact hρ_contWithin this
  have hS_nhds : {t | γ t ∈ ψ.source ∧ ρ t < expRadiusGp (I := I) g q} ∈
      nhdsWithin t₀ (Set.Icc a b) := by
    have hpre_nhds' : (γ ⁻¹' ψ.source) ∈ nhdsWithin t₀ (Set.Icc a b) := hpre_nhds
    have hρ_in_Icc : {t | ρ t < expRadiusGp (I := I) g q} ∈
        nhdsWithin t₀ (Set.Icc a b) := by
      rw [show Set.Icc a b ∩ γ ⁻¹' ψ.source
          = (Set.Icc a b) ∩ (γ ⁻¹' ψ.source) from rfl] at hρ_small_nhds
      rw [nhdsWithin_inter_of_mem' hpre_nhds'] at hρ_small_nhds
      exact hρ_small_nhds
    filter_upwards [hpre_nhds', hρ_in_Icc] with t htpre htρ
    exact ⟨htpre, htρ⟩
  have ht₀_lt_b : t₀ < b := ht₀.2
  have hIco_sub : Set.Ico t₀ b ⊆ Set.Icc a b := fun t ht => ⟨ht₀.1.le.trans ht.1, ht.2.le⟩
  have hS_nhds_right : {t | γ t ∈ ψ.source ∧ ρ t < expRadiusGp (I := I) g q} ∈
      nhdsWithin t₀ (Set.Ico t₀ b) :=
    nhdsWithin_mono t₀ hIco_sub hS_nhds
  rw [nhdsWithin_Ico_eq_nhdsGE ht₀_lt_b, mem_nhdsGE_iff_exists_Ico_subset] at hS_nhds_right
  obtain ⟨u, hu_mem, hu_sub⟩ := hS_nhds_right
  have hu_gt : t₀ < u := hu_mem
  set δ : ℝ := min ((u - t₀) / 2) (b - t₀) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact lt_min (by linarith) (by linarith [ht₀_lt_b])
  have hδ_le_b : t₀ + δ ≤ b := by
    rw [hδ_def]; have := min_le_right ((u - t₀) / 2) (b - t₀); linarith
  have hδ_lt_u : t₀ + δ < u := by
    rw [hδ_def]; have := min_le_left ((u - t₀) / 2) (b - t₀); linarith
  have hmemS : ∀ t ∈ Set.Icc t₀ (t₀ + δ),
      γ t ∈ ψ.source ∧ ρ t < expRadiusGp (I := I) g q := by
    intro t ht
    have ht_Ico : t ∈ Set.Ico t₀ u := ⟨ht.1, lt_of_le_of_lt ht.2 hδ_lt_u⟩
    exact hu_sub ht_Ico
  refine ⟨δ, hδ_pos, hδ_le_b, ?_, ?_⟩
  · intro t ht; exact (hmemS t ht).1
  · intro t ht; exact (hmemS t ht).2

theorem local_radial_identification_of_minimizer
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hfin : pathELength I γ a b ≠ ⊤)
    (hab : a ≤ b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ Icc t₀ (t₀ + δ) ⊆ Icc a b ∧
      ∃ (v : TangentSpace I (γ t₀)) (σ : ℝ → ℝ),
        MonotoneOn σ (Icc 0 δ) ∧ σ 0 = 0 ∧
        ∀ s : ℝ, s ∈ Icc 0 δ →
          γ (t₀ + s) = expMap (I := I) g (γ t₀) (σ s • v) := by
  classical
  set q : M := γ t₀ with hq_def
  obtain ⟨δ, hδ_pos, hδ_le_b, hsrc, hradial_small⟩ :=
    exists_forward_confinement_to_smallBall (I := I) g hγ ht₀ (q := q) hq_def.symm
  have ht₀_ge_a : a ≤ t₀ := ht₀.1.le
  have h_subset : Icc t₀ (t₀ + δ) ⊆ Icc a b :=
    Icc_subset_Icc ht₀_ge_a hδ_le_b
  set ψ := NormalCoordinates.normalChartAt (I := I) g q with hψ_def
  set v : E := ψ (γ (t₀ + δ)) with hv_def
  have hδ_endIcc : t₀ + δ ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith, le_rfl⟩
  have hγ_sub : CMDiff[Set.Icc t₀ (t₀ + δ)] 1 γ := hγ.mono h_subset
  have hsub_min : riemannianEDist I (γ t₀) (γ (t₀ + δ)) = pathELength I γ t₀ (t₀ + δ) :=
    subArc_of_minimizer_is_minimizer (I := I) hγ hmin hfin hab ht₀_ge_a
      (by linarith) hδ_le_b
  have hv_small : Real.sqrt (g.inner q v v) < expRadiusGp (I := I) g q := by
    have h := hradial_small (t₀ + δ) hδ_endIcc
    rw [hv_def]; exact h
  have hv_eucl : ‖v‖ < expMapC2Radius (I := I) g q :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g q hv_small
  have hv_ball : v ∈ ψ.target := by
    rw [hψ_def]; exact ball_subset_normalChartAt_target (I := I) g q hv_eucl
  have hv_dom : (show TangentSpace I q from v) ∈ expDomain (I := I) g q :=
    mem_expDomain_of_norm_lt_radius (I := I) g q hv_eucl
  have hγend_src : γ (t₀ + δ) ∈ ψ.source := hsrc (t₀ + δ) hδ_endIcc
  have hend_eq : γ (t₀ + δ) = expMap (I := I) g q (show TangentSpace I q from v) := by
    have hround : ψ.symm (ψ (γ (t₀ + δ))) = γ (t₀ + δ) := by
      rw [hψ_def]
      exact NormalCoordinates.normalChartAt_left_inv (I := I) g q hγend_src
    have hsymm : ψ.symm v = expMap (I := I) g q (show TangentSpace I q from v) := by
      rw [hψ_def]
      exact NormalCoordinates.normalChartAt_symm_apply (I := I) g q
        (show v ∈ ψ.symm.source from hv_ball)
    rw [← hround, ← hv_def, hsymm]
  have hdist_eq : riemannianEDist I q (expMap (I := I) g q (show TangentSpace I q from v))
      = ENNReal.ofReal (Real.sqrt (g.inner q v v)) :=
    radial_riemannianEDist_eq_radius (I := I) g q hEnorm hv_dom hv_ball hv_small
  have hlen : pathELength I γ t₀ (t₀ + δ)
      = ENNReal.ofReal (Real.sqrt (g.inner q v v)) := by
    rw [← hsub_min]
    show riemannianEDist I (γ t₀) (γ (t₀ + δ)) = _
    rw [hq_def, hend_eq]; exact hdist_eq
  have hab_sub : t₀ < t₀ + δ := by linarith
  have hγa_sub : γ t₀ = q := hq_def
  have hγb_sub : γ (t₀ + δ) = expMap (I := I) g q (show TangentSpace I q from v) := hend_eq
  have hγ_inBall : ∀ t ∈ Set.Icc t₀ (t₀ + δ), γ t ∈ ψ.source := by
    intro t ht; rw [hψ_def]; exact hsrc t ht
  obtain ⟨φ, hφ_mono, hφ0, hφ1, hφ_eq⟩ :=
    normalBall_radial_minimizer_equality (I := I) g q hEnorm hv_dom hv_ball hv_small
      hab_sub hγ_sub hγa_sub hγb_sub hγ_inBall hlen
  refine ⟨δ, hδ_pos, h_subset, (show TangentSpace I q from v), fun s => φ (t₀ + s), ?_, ?_, ?_⟩
  · intro s hs t ht hst
    have hs' : t₀ + s ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have ht' : t₀ + t ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hφ_mono hs' ht' (by linarith)
  · simp only [add_zero]; exact hφ0
  · intro s hs
    have hs' : t₀ + s ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := hφ_eq (t₀ + s) hs'
    rw [hq_def]; exact this


omit [RiemannianBundle (fun x : M => TangentSpace I x)] in
omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma norm_le_sqrt_inner_div_sqrt_coercive
    (g : SmoothRiemannianMetric I M) (c : M) (x : E) :
    ‖x‖ ≤ Real.sqrt (g.inner c x x) / Real.sqrt (gpCoerciveConst (I := I) g c) := by
  have hc_pos : 0 < gpCoerciveConst (I := I) g c := gpCoerciveConst_pos (I := I) g c
  have hsc_pos : 0 < Real.sqrt (gpCoerciveConst (I := I) g c) := Real.sqrt_pos.mpr hc_pos
  have hcoerc : gpCoerciveConst (I := I) g c * ‖x‖ ^ 2 ≤ g.inner c x x :=
    gpCoerciveConst_le (I := I) g c x
  have hgnn : 0 ≤ g.inner c x x := le_trans (by positivity) hcoerc
  have hkey : Real.sqrt (gpCoerciveConst (I := I) g c) * ‖x‖ ≤ Real.sqrt (g.inner c x x) := by
    have hlhs_eq : Real.sqrt (gpCoerciveConst (I := I) g c) * ‖x‖
        = Real.sqrt (gpCoerciveConst (I := I) g c * ‖x‖ ^ 2) := by
      rw [Real.sqrt_mul hc_pos.le, Real.sqrt_sq (norm_nonneg x)]
    rw [hlhs_eq]
    exact Real.sqrt_le_sqrt hcoerc
  rw [le_div_iff₀ hsc_pos, mul_comm]
  exact hkey

private theorem path_confined_to_normalBall
    (g : SmoothRiemannianMetric I M) (c : M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} (hγ : CMDiff[Set.Icc (0 : ℝ) 1] 1 γ) (hγ0 : γ 0 = c)
    (hlen : pathELength I γ 0 1 < ENNReal.ofReal (expRadiusGp (I := I) g c)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g c).source ∧
      Real.sqrt (g.inner c
          (NormalCoordinates.normalChartAt (I := I) g c (γ t))
          (NormalCoordinates.normalChartAt (I := I) g c (γ t)))
        < expRadiusGp (I := I) g c := by
  classical
  haveI : T2Space M := gauss_t2Space_base (I := I) (M := M)
  haveI : ProperSpace E := FiniteDimensional.proper_rclike (K := ℝ) (E := E)
  set R : ℝ := expRadiusGp (I := I) g c with hR_def
  have hR_pos : 0 < R := expRadiusGp_pos (I := I) g c
  set ψ := NormalCoordinates.normalChartAt (I := I) g c with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner c with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm c
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos c x h).le
  set ρ : ℝ → ℝ := fun t => Real.sqrt (g.inner c (ψ (γ t)) (ψ (γ t))) with hρ_def
  have hlen_ne_top : pathELength I γ 0 1 ≠ ⊤ := hlen.ne_top
  set L₀ : ℝ := (pathELength I γ 0 1).toReal with hL₀_def
  have hL₀_lt_R : L₀ < R := by
    rw [hL₀_def]; exact (ENNReal.lt_ofReal_iff_toReal_lt hlen_ne_top).mp hlen
  have hL₀_nn : 0 ≤ L₀ := ENNReal.toReal_nonneg
  have hcsrc : c ∈ ψ.source := by rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g c
  have hψc : ψ c = 0 := by rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g c
  have hopen_src : IsOpen ψ.source := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_open_source (I := I) g c
  have hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := hγ.continuousOn
  have hψcont : ContinuousOn ψ ψ.source := by
    rw [hψ_def]; exact (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g c).continuousOn
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ s ∈ Set.Icc (0 : ℝ) t, γ s ∈ ψ.source ∧ ρ s ≤ L₀} with hS_def
  suffices hS1 : (1 : ℝ) ∈ S by
    intro t ht
    obtain ⟨_, hall⟩ := hS1
    obtain ⟨hsrc, hρle⟩ := hall t ⟨ht.1, ht.2⟩
    refine ⟨hsrc, ?_⟩
    calc ρ t ≤ L₀ := hρle
      _ < R := hL₀_lt_R
  have hρ0 : ρ 0 = 0 := by
    change Real.sqrt (B (ψ (γ 0)) (ψ (γ 0))) = 0
    rw [hγ0, hψc]
    simp
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    intro s hs
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    exact ⟨by rw [hγ0]; exact hcsrc, by rw [hρ0]; exact hL₀_nn⟩
  have hSne : S.Nonempty := ⟨0, h0S⟩
  have hSbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  set t₀ : ℝ := sSup S with ht₀_def
  have ht₀_lb : (0 : ℝ) ≤ t₀ := le_csSup hSbdd h0S
  have ht₀_ub : t₀ ≤ 1 := csSup_le hSne (fun t ht => ht.1.2)
  have ht₀Icc : t₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨ht₀_lb, ht₀_ub⟩
  have hpre : ∀ s ∈ Set.Icc (0 : ℝ) t₀, s < t₀ → γ s ∈ ψ.source ∧ ρ s ≤ L₀ := by
    intro s hs hst₀
    obtain ⟨t, htS, hst⟩ := exists_lt_of_lt_csSup hSne hst₀
    exact htS.2 s ⟨hs.1, le_of_lt hst⟩
  have hfence : ∀ u ∈ Set.Icc (0 : ℝ) 1, (∀ s ∈ Set.Icc (0 : ℝ) u, γ s ∈ ψ.source ∧ ρ s < R) →
      ρ u ≤ L₀ := by
    intro u huIcc hconf
    have hγ_pref : CMDiff[Set.Icc (0 : ℝ) u] 1 γ :=
      hγ.mono (Set.Icc_subset_Icc le_rfl huIcc.2)
    have hsrc' : ∀ s ∈ Set.Icc (0 : ℝ) u, γ s ∈ ψ.source := fun s hs => (hconf s hs).1
    have hbball' : ∀ s ∈ Set.Icc (0 : ℝ) u,
        ‖ψ (γ s)‖ < expMapC2Radius (I := I) g c := by
      intro s hs
      exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g c (hconf s hs).2
    have hdom' : ∀ s ∈ Set.Icc (0 : ℝ) u,
        (show TangentSpace I c from ψ (γ s)) ∈ expDomain (I := I) g c :=
      fun s hs => mem_expDomain_of_norm_lt_radius (I := I) g c (hbball' s hs)
    have hlb := radialDist_endpoint_le_pathELength (I := I) g c hEnorm
      (a := 0) (b := u) huIcc.1 hγ0 hγ_pref hsrc' hbball' hdom'
    have hlb' : ENNReal.ofReal (ρ u) ≤ pathELength I γ 0 u := by
      rw [hρ_def, hψ_def]; exact hlb
    have hmono : pathELength I γ 0 u ≤ pathELength I γ 0 1 := by
      have hadd : pathELength I γ 0 u + pathELength I γ u 1 = pathELength I γ 0 1 :=
        pathELength_add (γ := γ) (I := I) huIcc.1 huIcc.2
      calc pathELength I γ 0 u ≤ pathELength I γ 0 u + pathELength I γ u 1 := le_self_add
        _ = pathELength I γ 0 1 := hadd
    have hchain : ENNReal.ofReal (ρ u) ≤ pathELength I γ 0 1 := le_trans hlb' hmono
    have : ENNReal.ofReal (ρ u) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hreal : ρ u ≤ L₀ := by
      rw [hL₀_def]
      have := (ENNReal.toReal_le_toReal this hlen_ne_top).mpr hchain
      rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
    exact hreal
  have ht₀S : t₀ ∈ S := by
    refine ⟨ht₀Icc, ?_⟩
    set sc : ℝ := Real.sqrt (gpCoerciveConst (I := I) g c) with hsc_def
    have hsc_pos : 0 < sc := Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g c)
    set r₀ : ℝ := L₀ / sc with hr₀_def
    have hr₀_nn : 0 ≤ r₀ := div_nonneg hL₀_nn hsc_pos.le
    have hR_factored : R = sc * expMapC2Radius (I := I) g c := by
      rw [hR_def, expRadiusGp, hsc_def]
    have hC2_eq : expMapC2Radius (I := I) g c = R / sc := by
      rw [hR_factored, mul_comm, mul_div_assoc, div_self (ne_of_gt hsc_pos), mul_one]
    have hr₀_lt : r₀ < expMapC2Radius (I := I) g c := by
      rw [hC2_eq, hr₀_def]
      exact (div_lt_div_iff_of_pos_right hsc_pos).mpr hL₀_lt_R
    have hball_tgt : Metric.closedBall (0 : E) r₀ ⊆ ψ.target := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      rw [hψ_def]
      exact ball_subset_normalChartAt_target (I := I) g c (lt_of_le_of_lt hx hr₀_lt)
    set K : Set M := ψ.symm '' (Metric.closedBall (0 : E) r₀) with hK_def
    have hKcompact : IsCompact K := by
      rw [hK_def]
      refine (isCompact_closedBall (0 : E) r₀).image_of_continuousOn ?_
      have hψsymm_cont : ContinuousOn ψ.symm ψ.target := by
        rw [hψ_def]
        exact (NormalCoordinates.normalChartAt_symm_contMDiffOn (I := I) g c).continuousOn
      exact hψsymm_cont.mono hball_tgt
    have hKclosed : IsClosed K := hKcompact.isClosed
    have hKsub : K ⊆ ψ.source := by
      intro y hy
      rw [hK_def] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      rw [← hxy]
      exact ψ.map_target (hball_tgt hx)
    have hγs_in_K : ∀ s ∈ Set.Icc (0 : ℝ) t₀, s < t₀ → γ s ∈ K := by
      intro s hs hst₀
      obtain ⟨hsrc, hρle⟩ := hpre s hs hst₀
      rw [hK_def]
      refine ⟨ψ (γ s), ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        have hnb := norm_le_sqrt_inner_div_sqrt_coercive (I := I) g c (ψ (γ s))
        rw [← hsc_def] at hnb
        have hρs_eq : Real.sqrt (g.inner c (ψ (γ s)) (ψ (γ s))) = ρ s := rfl
        rw [hρs_eq] at hnb
        rw [hr₀_def]
        refine le_trans hnb ?_
        exact div_le_div_of_nonneg_right hρle hsc_pos.le
      · rw [hψ_def]; exact NormalCoordinates.normalChartAt_left_inv (I := I) g c hsrc
    have hγt₀_src : γ t₀ ∈ ψ.source := by
      rcases eq_or_lt_of_le ht₀_lb with ht₀0 | ht₀0
      · rw [← ht₀0, hγ0]; exact hcsrc
      · have hγcontWithin : ContinuousWithinAt γ (Set.Iio t₀) t₀ := by
          have : ContinuousWithinAt γ (Set.Icc (0 : ℝ) 1) t₀ := hγcont t₀ ht₀Icc
          refine this.mono_of_mem_nhdsWithin ?_
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi 0, isOpen_Ioi, ht₀0, by
            intro z hz; exact ⟨hz.1.le, lt_of_lt_of_le hz.2 ht₀_ub |>.le⟩⟩
        have htend : Filter.Tendsto γ (nhdsWithin t₀ (Set.Iio t₀)) (nhds (γ t₀)) :=
          hγcontWithin
        have hev : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀), γ s ∈ K := by
          have hpos : Set.Ioo 0 t₀ ∈ nhdsWithin t₀ (Set.Iio t₀) := by
            rw [mem_nhdsWithin]
            exact ⟨Set.Ioi 0, isOpen_Ioi, ht₀0, by intro z hz; exact ⟨hz.1, hz.2⟩⟩
          filter_upwards [hpos] with s hs
          exact hγs_in_K s ⟨hs.1.le, hs.2.le⟩ hs.2
        haveI : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := nhdsLT_neBot t₀
        exact hKsub (hKclosed.mem_of_tendsto htend hev)
    refine fun s hs => ?_
    rcases eq_or_lt_of_le hs.2 with hst₀ | hst₀
    · subst hst₀
      refine ⟨hγt₀_src, ?_⟩
      rcases eq_or_lt_of_le ht₀_lb with ht₀0 | ht₀0
      · rw [← ht₀0, hρ0]; exact hL₀_nn
      · have hIoo_nhds : Set.Ioo 0 t₀ ∈ nhdsWithin t₀ (Set.Iio t₀) := by
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi 0, isOpen_Ioi, ht₀0, by intro z hz; exact ⟨hz.1, hz.2⟩⟩
        have hρcontWithin : ContinuousWithinAt ρ (Set.Ioo 0 t₀) t₀ := by
          have hcomp : ContinuousWithinAt (fun s => ψ (γ s)) (Set.Ioo 0 t₀) t₀ := by
            have h1 : ContinuousWithinAt γ (Set.Ioo 0 t₀) t₀ := by
              have hsub : Set.Ioo (0 : ℝ) t₀ ⊆ Set.Icc (0 : ℝ) 1 :=
                fun z hz => ⟨hz.1.le, lt_of_lt_of_le hz.2 ht₀_ub |>.le⟩
              exact (hγcont t₀ ht₀Icc).mono hsub
            have hmaps : Set.MapsTo γ (Set.Ioo 0 t₀) ψ.source :=
              fun z hz => (hpre z ⟨hz.1.le, hz.2.le⟩ hz.2).1
            exact (hψcont _ hγt₀_src).comp h1 hmaps
          exact ((psd_sqrt_lipschitz B hBsym hBnn).continuous.continuousAt.comp_continuousWithinAt hcomp)
        have htend : Filter.Tendsto ρ (nhdsWithin t₀ (Set.Ioo 0 t₀)) (nhds (ρ t₀)) :=
          hρcontWithin
        have hev : ∀ᶠ s in nhdsWithin t₀ (Set.Ioo 0 t₀), ρ s ≤ L₀ := by
          have hself : Set.Ioo 0 t₀ ∈ nhdsWithin t₀ (Set.Ioo 0 t₀) := self_mem_nhdsWithin
          filter_upwards [hself] with s hs
          exact (hpre s ⟨hs.1.le, hs.2.le⟩ hs.2).2
        haveI : (nhdsWithin t₀ (Set.Ioo 0 t₀)).NeBot := by
          refine mem_closure_iff_nhdsWithin_neBot.mp ?_
          rw [closure_Ioo (ne_of_lt ht₀0)]
          exact Set.right_mem_Icc.mpr ht₀0.le
        exact le_of_tendsto htend hev
    · exact hpre s hs hst₀
  have ht₀_eq_one : t₀ = 1 := by
    by_contra hne
    have ht₀_lt_one : t₀ < 1 := lt_of_le_of_ne ht₀_ub hne
    obtain ⟨hγt₀_src, hρt₀_le⟩ := ht₀S.2 t₀ ⟨ht₀_lb, le_rfl⟩
    have hρt₀_lt : ρ t₀ < R := lt_of_le_of_lt hρt₀_le hL₀_lt_R
    have hpre_nhds : γ ⁻¹' ψ.source ∈ nhdsWithin t₀ (Set.Icc (0 : ℝ) 1) :=
      (hγcont t₀ ht₀Icc).preimage_mem_nhdsWithin (hopen_src.mem_nhds hγt₀_src)
    have hρcontWithin : ContinuousWithinAt ρ
        (Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' ψ.source) t₀ := by
      have hcomp : ContinuousWithinAt (fun s => ψ (γ s))
          (Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' ψ.source) t₀ := by
        have h1 : ContinuousWithinAt γ (Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' ψ.source) t₀ :=
          (hγcont t₀ ht₀Icc).mono Set.inter_subset_left
        have hmaps : Set.MapsTo γ (Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' ψ.source) ψ.source :=
          fun s hs => hs.2
        exact (hψcont _ hγt₀_src).comp h1 hmaps
      exact ((psd_sqrt_lipschitz B hBsym hBnn).continuous.continuousAt.comp_continuousWithinAt hcomp)
    have hρ_small_nhds : {s | ρ s < R} ∈
        nhdsWithin t₀ (Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' ψ.source) := by
      have : Set.Iio R ∈ nhds (ρ t₀) := isOpen_Iio.mem_nhds hρt₀_lt
      exact hρcontWithin this
    have hgood_nhds : {s | γ s ∈ ψ.source ∧ ρ s < R} ∈
        nhdsWithin t₀ (Set.Icc (0 : ℝ) 1) := by
      have hρ_in : {s | ρ s < R} ∈ nhdsWithin t₀ (Set.Icc (0 : ℝ) 1) := by
        rw [nhdsWithin_inter_of_mem' hpre_nhds] at hρ_small_nhds
        exact hρ_small_nhds
      filter_upwards [hpre_nhds, hρ_in] with s hspre hsρ
      exact ⟨hspre, hsρ⟩
    have hIco_sub : Set.Ico t₀ 1 ⊆ Set.Icc (0 : ℝ) 1 :=
      fun s hs => ⟨le_trans ht₀_lb hs.1, hs.2.le⟩
    have hgood_right : {s | γ s ∈ ψ.source ∧ ρ s < R} ∈
        nhdsWithin t₀ (Set.Ico t₀ 1) := nhdsWithin_mono t₀ hIco_sub hgood_nhds
    rw [nhdsWithin_Ico_eq_nhdsGE ht₀_lt_one, mem_nhdsGE_iff_exists_Ico_subset] at hgood_right
    obtain ⟨u, hu_mem, hu_sub⟩ := hgood_right
    have hu_gt : t₀ < u := hu_mem
    set t₁ : ℝ := min ((t₀ + u) / 2) 1 with ht₁_def
    have ht₁_gt : t₀ < t₁ := by
      rw [ht₁_def]; exact lt_min (by linarith) ht₀_lt_one
    have ht₁_le_one : t₁ ≤ 1 := by rw [ht₁_def]; exact min_le_right _ _
    have ht₁_lt_u : t₁ < u := by
      rw [ht₁_def]
      calc min ((t₀ + u) / 2) 1 ≤ (t₀ + u) / 2 := min_le_left _ _
        _ < u := by linarith
    have ht₁S : t₁ ∈ S := by
      refine ⟨⟨le_trans ht₀_lb ht₁_gt.le, ht₁_le_one⟩, ?_⟩
      intro s hs
      rcases le_or_gt s t₀ with hle | hgt
      · exact ht₀S.2 s ⟨hs.1, hle⟩
      · have hs_Ico : s ∈ Set.Ico t₀ u := ⟨le_of_lt hgt, lt_of_le_of_lt hs.2 ht₁_lt_u⟩
        obtain ⟨hsrc, hsρ⟩ := hu_sub hs_Ico
        refine ⟨hsrc, ?_⟩
        have hconf : ∀ z ∈ Set.Icc (0 : ℝ) s, γ z ∈ ψ.source ∧ ρ z < R := by
          intro z hz
          rcases le_or_gt z t₀ with hzle | hzgt
          · obtain ⟨hzsrc, hzρ⟩ := ht₀S.2 z ⟨hz.1, hzle⟩
            exact ⟨hzsrc, lt_of_le_of_lt hzρ hL₀_lt_R⟩
          · have hz_Ico : z ∈ Set.Ico t₀ u :=
              ⟨le_of_lt hzgt, lt_of_le_of_lt hz.2 (lt_of_le_of_lt hs.2 ht₁_lt_u)⟩
            exact hu_sub hz_Ico
        exact hfence s ⟨hs.1, le_trans hs.2 ht₁_le_one⟩ hconf
    exact absurd (le_csSup hSbdd ht₁S) (not_le.mpr ht₁_gt)
  rw [← ht₀_eq_one]; exact ht₀S

theorem metricBall_subset_normalBall
    (g : SmoothRiemannianMetric I M) (c : M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {y : M} (hfin : riemannianEDist I c y ≠ ⊤)
    (hy : (riemannianEDist I c y).toReal < expRadiusGp (I := I) g c) :
    ∃ v : E, v ∈ (NormalCoordinates.normalChartAt (I := I) g c).target ∧
        (show TangentSpace I c from v) ∈ expDomain (I := I) g c ∧
        Real.sqrt (g.inner c (show TangentSpace I c from v) (show TangentSpace I c from v))
          = (riemannianEDist I c y).toReal ∧
        y = expMap (I := I) g c v := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g c with hψ_def
  have hlt : riemannianEDist I c y < ENNReal.ofReal (expRadiusGp (I := I) g c) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr hy
  obtain ⟨γ, hγ0, hγ1, hγ, hγlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  obtain ⟨hy_src, hy_rad⟩ :=
    path_confined_to_normalBall (I := I) g c hEnorm hγ hγ0 hγlen 1 ⟨zero_le_one, le_rfl⟩
  rw [hγ1] at hy_src hy_rad
  set v : E := ψ y with hv_def
  have hv_small : Real.sqrt (g.inner c v v) < expRadiusGp (I := I) g c := hy_rad
  have hv_eucl : ‖v‖ < expMapC2Radius (I := I) g c :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g c hv_small
  have hv_ball : v ∈ ψ.target := by
    rw [hψ_def]; exact ball_subset_normalChartAt_target (I := I) g c hv_eucl
  have hv_dom : (show TangentSpace I c from v) ∈ expDomain (I := I) g c :=
    mem_expDomain_of_norm_lt_radius (I := I) g c hv_eucl
  have hy_eq : y = expMap (I := I) g c (show TangentSpace I c from v) := by
    have hround : ψ.symm (ψ y) = y := by
      rw [hψ_def]; exact NormalCoordinates.normalChartAt_left_inv (I := I) g c hy_src
    have hsymm : ψ.symm v = expMap (I := I) g c (show TangentSpace I c from v) := by
      rw [hψ_def]
      exact NormalCoordinates.normalChartAt_symm_apply (I := I) g c
        (show v ∈ ψ.symm.source from hv_ball)
    rw [← hround, ← hv_def, hsymm]
  have hdist_eq : riemannianEDist I c (expMap (I := I) g c (show TangentSpace I c from v))
      = ENNReal.ofReal (Real.sqrt (g.inner c v v)) :=
    radial_riemannianEDist_eq_radius (I := I) g c hEnorm hv_dom hv_ball hv_small
  refine ⟨v, hv_ball, hv_dom, ?_, hy_eq⟩
  have hdy : riemannianEDist I c y = ENNReal.ofReal (Real.sqrt (g.inner c v v)) := by
    rw [hy_eq]; exact hdist_eq
  rw [hdy, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

theorem memNChartSrcOfDist
    (g : SmoothRiemannianMetric I M) (c : M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {y : M} (hfin : riemannianEDist I c y ≠ ⊤)
    (hy : (riemannianEDist I c y).toReal < expRadiusGp (I := I) g c) :
    y ∈ (NormalCoordinates.normalChartAt (I := I) g c).source := by
  obtain ⟨v, hv_tgt, _hv_dom, _hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) g c hEnorm hfin hy
  set ψ := NormalCoordinates.normalChartAt (I := I) g c with hψ_def
  have hv_symm_src : v ∈ ψ.symm.source := by
    rw [hψ_def]
    exact hv_tgt
  have hy_symm : ψ.symm v = y := by
    rw [hy_eq]
    rw [hψ_def]
    exact NormalCoordinates.normalChartAt_symm_apply (I := I) g c hv_symm_src
  have hsrc : ψ.symm v ∈ ψ.source := by
    exact ψ.symm.map_source hv_symm_src
  rw [← hy_symm]
  exact hsrc

end LocalRadialIdentification

end RadialMinimizerConvention

end Riemannian
end Geometry
end DifferentialGeometry
