import OpenGALib.Interoperability.RicciFlow.SurfaceArea
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Area variation of parametrized surface patches under Ricci flow

The induced matrix is computed from the actual manifold derivative of a fixed
map from the Euclidean plane. Its density is `sqrt (det (f* g))`. The Ricci
matrix is the pullback of the ambient Ricci tensor by that same derivative.
DifferentialGeometry's metric evolution and Jacobi formula prove the pointwise
variation, and dominated differentiation gives the integral formula on a patch.

Upstream: qinz1yang/differential-geometry, Apache-2.0, v0.1.2,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Reference: Colding-Minicozzi, arXiv:0707.0108, Section 1.5.

The positive determinant assumption excludes branch points. This is a local
parameter-domain result: gluing charts to a closed surface, deriving the
domination bounds from compactness, and treating branched minimal spheres
are separate tasks. No global tangent frame on a sphere is assumed.
-/

noncomputable section

open Bundle Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

namespace OpenGA.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-- The pullback of the actual ambient Ricci tensor to the parameter plane. -/
def surfaceRicciMatrix {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (f : SurfaceParameter → M) (t : ℝ) (u : SurfaceParameter) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => S.ricciAt t (f u)
    (vec2 (surfaceTangent (I := I) f u i) (surfaceTangent (I := I) f u j))

/-- The Ricci tensor traced using the induced two-dimensional metric. -/
def surfaceRicciTrace {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (f : SurfaceParameter → M) (t : ℝ) (u : SurfaceParameter) : ℝ :=
  Matrix.trace ((surfaceMetricMatrix (S.family.metric t) f u)⁻¹ * surfaceRicciMatrix S f t u)

/-- The local area-density variation of a fixed nondegenerate parametrization. -/
theorem hasDerivAt_surfaceDensity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (f : SurfaceParameter → M)
    {t : ℝ} (ht : t ∈ D.regular) (u : SurfaceParameter)
    (hpos : 0 < (surfaceMetricMatrix (S.family.metric t) f u).det) :
    HasDerivAt (fun s => surfaceDensity (S.family.metric s) f u)
      (-surfaceRicciTrace S f t u * surfaceDensity (S.family.metric t) f u) t := by
  have hentries : ∀ i j, HasDerivAt
      (fun s => surfaceMetricMatrix (S.family.metric s) f u i j)
      (((-2 : ℝ) • surfaceRicciMatrix S f t u) i j) t := by
    intro i j
    exact metricDerivAt S hS ⟨t, ht⟩ (f u)
      (surfaceTangent (I := I) f u i) (surfaceTangent (I := I) f u j)
  have h := DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (fun s => surfaceMetricMatrix (S.family.metric s) f u)
    ((-2 : ℝ) • surfaceRicciMatrix S f t u) t hentries hpos
  dsimp only [surfaceDensity, surfaceRicciTrace]
  convert h using 1
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

/-- Differentiation under the area integral with explicit local domination.
The hypotheses concern integrability and regularity, not the desired derivative. -/
theorem hasDerivAt_patchArea
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (f : SurfaceParameter → M) (Ω : Set SurfaceParameter)
    {t : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 t) (hregular : U ⊆ D.regular)
    (hpos : ∀ᵐ u ∂volume.restrict Ω, ∀ s ∈ U,
      0 < (surfaceMetricMatrix (S.family.metric s) f u).det)
    (hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (surfaceDensity (S.family.metric s) f) (volume.restrict Ω))
    (hint : Integrable (surfaceDensity (S.family.metric t) f) (volume.restrict Ω))
    (htrace : AEStronglyMeasurable
      (fun u => -surfaceRicciTrace S f t u * surfaceDensity (S.family.metric t) f u)
      (volume.restrict Ω))
    (bound : SurfaceParameter → ℝ) (hbound_int : Integrable bound (volume.restrict Ω))
    (hbound : ∀ᵐ u ∂volume.restrict Ω, ∀ s ∈ U,
      ‖-surfaceRicciTrace S f s u * surfaceDensity (S.family.metric s) f u‖ ≤ bound u) :
    HasDerivAt (fun s => patchArea (S.family.metric s) f Ω)
      (-∫ u in Ω, surfaceRicciTrace S f t u * surfaceDensity (S.family.metric t) f u) t := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict Ω) hU hmeas hint htrace hbound hbound_int
    (hpos.mono (fun u hu s hs => hasDerivAt_surfaceDensity S hS f (hregular hs) u (hu s hs)))
  simpa only [patchArea, neg_mul, integral_neg] using h.2

end OpenGA.RicciFlow
