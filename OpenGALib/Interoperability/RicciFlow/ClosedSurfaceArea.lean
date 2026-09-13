import OpenGALib.Riemannian.Surface.Area
import OpenGALib.Interoperability.RicciFlow.SurfaceAreaVariation
import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness

/-!
# Global area variation of an immersed closed surface under Ricci flow

For a fixed smooth immersion, construct the induced metric and its global
area measure. Smoothness of the actual ambient Ricci-flow metric supplies
the local-in-time regularity needed for differentiation. The derivative is
minus the integral of the ambient Ricci tensor traced on the immersed tangent
plane. No global normal or tangent frame, global existence in time, or
separate domination hypothesis is assumed.

This is the smooth immersion case of Colding-Minicozzi, arXiv:0707.0108,
Section 1.5, equation (1.16). Minimality, Gauss-Bonnet, branch points and the
extension to Sobolev sweepouts remain separate results.
-/

noncomputable section

open Bundle Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

namespace OpenGA.RicciFlow

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

omit [T2Space M] in
/-- Pulling back a smooth ambient metric family by a fixed immersion preserves
the local space-time regularity needed for volume variation. -/
theorem inducedMetric_regularOn
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x)) :
    MetricFamilyRegularOn (fun s => Surface.inducedMetric (g s) f hf hinj) D.regular := by
  apply MetricFamilyRegularOn.of_contMDiffAt
  intro a i j t ht x hx
  have hbase := (trivializationAt Surface.Model (TangentSpace 𝓘(ℝ, Surface.Model)) a).open_baseSet.mem_nhds hx
  have htf : ContMDiff 𝓘(ℝ, Surface.Model).tangent I.tangent ∞
      (tangentMap 𝓘(ℝ, Surface.Model) I f) := hf.contMDiff_tangentMap (le_refl _)
  have hv (k : Fin (Module.finrank ℝ Surface.Model)) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Surface.Model)) I.tangent ∞
        (fun p : ℝ × N => TotalSpace.mk' E (f p.2)
          (mfderiv 𝓘(ℝ, Surface.Model) I f p.2
            (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) a k p.2))) (t, x) :=
    htf.contMDiffAt.comp (t, x)
      (((chartBasisVec_contMDiffOn a k).contMDiffAt hbase).comp (t, x) contMDiffAt_snd)
  have hmetric := (hg.metricCLMSmoothAt (x := f x) (D.regular_isOpen.mem_nhds ht)).comp (t, x)
    (contMDiffAt_fst.prodMk (hf.contMDiffAt.comp (t, x) contMDiffAt_snd))
  have hpair := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun b : M => TangentSpace I b) (E₂ := fun b : M => TangentSpace I b)
    (E₃ := fun _ : M => ℝ)
    (b := fun p : ℝ × N => f p.2) (ψ := fun p => (g p.1).inner (f p.2))
    (v := fun p => mfderiv 𝓘(ℝ, Surface.Model) I f p.2
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) a i p.2))
    (w := fun p => mfderiv 𝓘(ℝ, Surface.Model) I f p.2
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) a j p.2)) hmetric (hv i) (hv j)
  rw [contMDiffAt_totalSpace] at hpair
  exact hpair.2

/-- The ambient Ricci tensor evaluated on the images of a centered chart basis.
The same basis is used in the induced metric matrix below. -/
def inducedRicciMatrix {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (f : N → M) (t : ℝ) (x : N) :
    Matrix (Fin (Module.finrank ℝ Surface.Model)) (Fin (Module.finrank ℝ Surface.Model)) ℝ :=
  fun i j => S.ricciAt t (f x) (vec2
    (mfderiv 𝓘(ℝ, Surface.Model) I f x
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x i x))
    (mfderiv 𝓘(ℝ, Surface.Model) I f x
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x j x)))

/-- Trace of the ambient Ricci tensor along the immersed tangent plane. -/
def inducedRicciTrace {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    (t : ℝ) (x : N) : ℝ :=
  Matrix.trace ((chartGramMatrix (Surface.inducedMetric (S.family.metric t) f hf hinj) x x)⁻¹ *
    inducedRicciMatrix S f t x)

theorem traceTimeDeriv_inducedMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    {t : ℝ} (ht : t ∈ D.regular) (x : N) :
    traceTimeDerivMetric 𝓘(ℝ, Surface.Model)
      (fun s => Surface.inducedMetric (S.family.metric s) f hf hinj) t x =
      -2 * inducedRicciTrace S f hf hinj t x := by
  have hentries : (Matrix.of fun i j =>
      deriv (fun s => chartGramMatrix (Surface.inducedMetric (S.family.metric s) f hf hinj)
        x x i j) t) = (-2 : ℝ) • inducedRicciMatrix S f t x := by
    ext i j
    exact (metricDerivAt S hS ⟨t, ht⟩ (f x)
      (mfderiv 𝓘(ℝ, Surface.Model) I f x
        (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x i x))
      (mfderiv 𝓘(ℝ, Surface.Model) I f x
        (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x j x))).deriv
  unfold traceTimeDerivMetric inducedRicciTrace
  rw [hentries, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Global area variation of a fixed smooth immersion of a closed surface.
All regularity and domination needed for the integral are derived from the
actual smooth Ricci flow and compactness of the domain surface. -/
theorem hasDerivAt_area [CompactSpace N]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt (fun s => Surface.area (S.family.metric s) f hf hinj)
      (-∫ x, inducedRicciTrace S f hf hinj t x
        ∂(Surface.areaMeasure (S.family.metric t) f hf hinj)) t := by
  have h := hasDerivAt_totalRiemannianVolume
    (fun s => Surface.inducedMetric (S.family.metric s) f hf hinj)
    (inducedMetric_regularOn S.family.metric hS.smoothMetric f hf hinj)
    (D.regular_isOpen.mem_nhds ht)
  simp_rw [traceTimeDeriv_inducedMetric S hS f hf hinj ht] at h
  have halg : ∀ x, (1 / 2 : ℝ) * (-2 * inducedRicciTrace S f hf hinj t x) =
      -inducedRicciTrace S f hf hinj t x := by intro x; ring
  simpa only [halg, integral_neg, Surface.area, Surface.areaMeasure] using h

end OpenGA.RicciFlow
