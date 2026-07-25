import DifferentialGeometry.Geometry.Curvature.Realized.Operators

set_option autoImplicit false













namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open DifferentialGeometry.Integral.Connection
open Set
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]








structure IsHeatPotOn
    (D : RealTimeInterval)
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (V u : Real → M → Real) : Prop where

  jointSmooth :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => u q.1 q.2) (D.regular ×ˢ univ)

  jointCont :
    ContinuousOn (fun q : Real × M => u q.1 q.2)
      (D.carrier ×ˢ univ)

  sliceSmooth :
    ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (u t)

  equation :
    ∀ t : Real, t ∈ D.regular → ∀ x : M,
      HasDerivAt (fun s : Real => u s x)
        (laplacianAt (I := I) G t (u t) x + V t x * u t x) t

namespace IsHeatPotOn



theorem mono
    {D D' : RealTimeInterval}
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    {V u : Real → M → Real}
    (h : IsHeatPotOn D G V u)
    (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) :
    IsHeatPotOn D' G V u where
  jointSmooth := h.jointSmooth.mono
    (Set.prod_mono hregular Set.Subset.rfl)
  jointCont := h.jointCont.mono
    (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := h.sliceSmooth t (hcarrier ht)
  equation t ht x := h.equation t (hregular ht) x

end IsHeatPotOn

end

end DifferentialGeometry.Analysis.Parabolic
