import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]









omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metric_coordinateFrame_component_contMDiffAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        g.inner p (coordinateFrameAt (I := I) x₀ i p)
          (coordinateFrameAt (I := I) x₀ j p)) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have hi :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ i p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      hx i
  have hj :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ j p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      hx j
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun p : M =>
          (⟨p,
            g.inner p (coordinateFrameAt (I := I) x₀ i p)
              (coordinateFrameAt (I := I) x₀ j p)⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hj
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metric_coordinateFrame_component_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        g.inner p (coordinateFrameAt (I := I) x₀ i p)
          (coordinateFrameAt (I := I) x₀ j p)) x₀ :=
  metric_coordinateFrame_component_contMDiffAt_of_mem
    (I := I) g x₀ (coordinateFrameAt_mem (I := I) x₀) i j



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metric_coordinateFrame_component_directional_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        extDerivFun (I := I)
          (fun q : M =>
            g.inner q (coordinateFrameAt (I := I) x₀ i q)
              (coordinateFrameAt (I := I) x₀ j q))
          p (coordinateFrameAt (I := I) x₀ a p)) x₀ := by
  have hf := metric_coordinateFrame_component_contMDiffAt
    (I := I) g x₀ i j
  have ha :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ a p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) a
  exact extDerivFun_apply_contMDiffAt_of_section
    (I := I) (f := fun q : M =>
      g.inner q (coordinateFrameAt (I := I) x₀ i q)
        (coordinateFrameAt (I := I) x₀ j q))
    (X := coordinateFrameAt (I := I) x₀ a) hf ha
end DifferentialGeometry.Integral.Connection
