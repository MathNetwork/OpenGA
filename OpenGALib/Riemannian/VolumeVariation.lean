import DifferentialGeometry.Analysis.Integration.Measure.VolumeVariation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Local-in-time variation of Riemannian volume

DifferentialGeometry's volume variation theorem uses a metric family regular
on the whole real time axis. Here regularity is required only on an open time
neighborhood. A smooth time localization agrees with the identity near the
time under consideration and takes all its values in that neighborhood.

The integration and chart-gluing proofs are reused from
qinz1yang/differential-geometry, Apache-2.0, v0.1.2,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
-/

noncomputable section

open Bundle Filter Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Integral.Measure

namespace OpenGA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Joint continuity of the metric coefficients and their time derivatives on
an open time interval. These are regularity assumptions, not a variation formula. -/
structure MetricFamilyRegularOn (g : ℝ → SmoothRiemannianMetric I M) (U : Set ℝ) : Prop where
  differentiableAt : ∀ a i j x,
    x ∈ (trivializationAt E (TangentSpace I) a).baseSet → ∀ t ∈ U,
    DifferentiableAt ℝ (fun s => chartGramMatrix (g s) a x i j) t
  continuousOn : ∀ a i j,
    ContinuousOn (fun p : ℝ × M => chartGramMatrix (g p.1) a p.2 i j)
      (U ×ˢ (trivializationAt E (TangentSpace I) a).baseSet)
  continuousOn_deriv : ∀ a i j,
    ContinuousOn (fun p : ℝ × M => deriv (fun s => chartGramMatrix (g s) a p.2 i j) p.1)
      (U ×ˢ (trivializationAt E (TangentSpace I) a).baseSet)

omit [FiniteDimensional ℝ E] in
private theorem contMDiffAt_partial_deriv_time
    {f : ℝ × M → ℝ} {p : ℝ × M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f p) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => deriv (fun t => f (t, q.2)) q.1) p := by
  have harg : ContMDiffAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) ∞ (fun q : (ℝ × M) × ℝ => (q.2, q.1.2)) (p, p.1) :=
    contMDiffAt_snd.prodMk contMDiffAt_fst.snd
  have hF := hf.comp (p, p.1) harg
  have h := ContMDiffAt.mfderiv_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (f := fun (q : ℝ × M) (t : ℝ) => f (t, q.2))
    (g := fun q : ℝ × M => q.1) (g₁ := fun q : ℝ × M => q)
    (g₂ := fun _ : ℝ × M => (1 : ℝ)) (x₀ := p) (m := ∞)
    hF contMDiffAt_fst contMDiffAt_id contMDiffAt_const (le_refl _)
  simpa [inTangentCoordinates_model_space] using! h

/-- Smooth space-time metric coefficients supply the local regularity interface. -/
theorem MetricFamilyRegularOn.of_contMDiffAt
    {g : ℝ → SmoothRiemannianMetric I M} {U : Set ℝ}
    (hg : ∀ a i j t, t ∈ U → ∀ x,
      x ∈ (trivializationAt E (TangentSpace I) a).baseSet →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) a p.2 i j) (t, x)) :
    MetricFamilyRegularOn g U where
  differentiableAt a i j x hx t ht := by
    have h := (hg a i j t ht x hx).comp t
      (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (contMDiffAt_iff_contDiffAt.mp h).differentiableAt (by simp)
  continuousOn a i j p hp := (hg a i j p.1 hp.1 p.2 hp.2).continuousAt.continuousWithinAt
  continuousOn_deriv a i j p hp :=
    (contMDiffAt_partial_deriv_time (hg a i j p.1 hp.1 p.2 hp.2)).continuousAt.continuousWithinAt

private theorem exists_smooth_time_localization {U : Set ℝ} {t : ℝ} (hU : U ∈ 𝓝 t) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ (∀ s, r s ∈ U) ∧ r =ᶠ[𝓝 t] id := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  let b : ContDiffBump t := ⟨ε / 2, ε, by positivity, by linarith⟩
  refine ⟨fun s => t + b s * (s - t),
    contDiff_const.add (b.contDiff.mul (contDiff_id.sub contDiff_const)), ?_, ?_⟩
  · intro s
    apply hball
    by_cases hs : s ∈ Metric.ball t ε
    · rw [Metric.mem_ball, Real.dist_eq]
      have hst : |s - t| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      calc |t + b s * (s - t) - t| = |b s| * |s - t| := by
             rw [add_sub_cancel_left, abs_mul]
           _ ≤ 1 * |s - t| := mul_le_mul_of_nonneg_right
             (by rw [abs_of_nonneg b.nonneg]; exact b.le_one) (abs_nonneg _)
           _ < ε := by simpa using hst
    · have hb : b s = 0 := b.zero_of_le_dist (by simpa [b, Metric.mem_ball] using hs)
      simpa [hb] using Metric.mem_ball_self (x := t) hε
  · filter_upwards [b.eventuallyEq_one] with s hs
    simp [hs]

theorem MetricFamilyRegularOn.comp
    {g : ℝ → SmoothRiemannianMetric I M} {U : Set ℝ}
    (hg : MetricFamilyRegularOn g U) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hmap : ∀ s, r s ∈ U) (t : ℝ) :
    MetricFamilyRegularAt (fun s => g (r s)) t := by
  apply MetricFamilyRegularAt.of_chartGram_timeDeriv
  intro a i j
  refine ⟨fun s x => deriv (fun u => chartGramMatrix (g u) a x i j) (r s) * deriv r s,
    ?_, ?_, ?_⟩
  · intro s x hx
    exact (hg.differentiableAt a i j x hx (r s) (hmap s)).hasDerivAt.comp s
      (hr.differentiable (by simp)).differentiableAt.hasDerivAt
  · exact (hg.continuousOn a i j).comp
      ((hr.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨hmap p.1, hp.2⟩)
  · exact ((hg.continuousOn_deriv a i j).comp
      ((hr.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨hmap p.1, hp.2⟩)).mul
      ((hr.continuous_deriv (by simp)).comp continuous_fst).continuousOn

/-- Total Riemannian volume, as a real integral. It is finite on compact manifolds. -/
def totalRiemannianVolume [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) : ℝ :=
  ∫ _ : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g)

theorem hasDerivAt_totalRiemannianVolume_of_regular [T2Space M] [CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hg : MetricFamilyRegularAt g t) :
    HasDerivAt (fun s => totalRiemannianVolume (g s))
      (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric I g t x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t))) t := by
  simpa [totalRiemannianVolume, riemannianMeasureFamily, deriv_const] using
    volume_variation_formula (f := fun _ _ => (1 : ℝ)) hg (FunctionRegularAt_const 1 t)

/-- Volume variation needs regularity only near the time of differentiation. -/
theorem hasDerivAt_totalRiemannianVolume [T2Space M] [CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {U : Set ℝ} {t : ℝ}
    (hg : MetricFamilyRegularOn g U) (hU : U ∈ 𝓝 t) :
    HasDerivAt (fun s => totalRiemannianVolume (g s))
      (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric I g t x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t))) t := by
  obtain ⟨r, hr, hmap, heq⟩ := exists_smooth_time_localization hU
  have hrt : r t = t := heq.eq_of_nhds
  have h := hasDerivAt_totalRiemannianVolume_of_regular (fun s => g (r s)) t
    (hg.comp r hr hmap t)
  have htrace : ∀ x, traceTimeDerivMetric I (fun s => g (r s)) t x =
      traceTimeDerivMetric I g t x := by
    intro x
    unfold traceTimeDerivMetric
    dsimp only
    rw [hrt]
    congr 3
    funext i j
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [heq] with s hs
    simp only [hs, id_eq]
  simp_rw [hrt, htrace] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [heq] with s hs
  simp only [hs, id_eq]

end OpenGA
