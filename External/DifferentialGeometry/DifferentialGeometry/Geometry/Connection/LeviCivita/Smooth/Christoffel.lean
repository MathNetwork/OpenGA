import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Model

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
theorem metricFlatModelInChart_component_center
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    metricFlatModelInChart_component (I := I) g x₀ i j (extChartAt I x₀ x₀) =
      g.inner x₀ (coordinateFrameAt (I := I) x₀ i x₀)
        (coordinateFrameAt (I := I) x₀ j x₀) := by
  rw [metricFlatModelInChart_component, metricFlatModelInChart_center_eq]
  change ((metricFlatContinuousEquiv (I := I) g x₀)
      ((Module.finBasis Real E) i)) ((Module.finBasis Real E) j) =
    g.inner x₀ (coordinateFrameAt (I := I) x₀ i x₀)
      (coordinateFrameAt (I := I) x₀ j x₀)
  have hi : coordinateFrameAt (I := I) x₀ i x₀ = (Module.finBasis Real E) i := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ i]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  have hj : coordinateFrameAt (I := I) x₀ j x₀ = (Module.finBasis Real E) j := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ j]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  rw [metricFlatContinuousEquiv_apply (I := I) g x₀
    ((Module.finBasis Real E) i) ((Module.finBasis Real E) j), hi, hj]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricFlatModelInChart_component_eq_coord_component_comp_eventually_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) {y₀ : E}
    (hy₀ : y₀ ∈ (extChartAt I x₀).target) :
    metricFlatModelInChart_component (I := I) g x₀ i j
      =ᶠ[𝓝[Set.range I] y₀]
      fun y : E =>
        g.inner ((extChartAt I x₀).symm y)
          (coordinateFrameAt (I := I) x₀ i ((extChartAt I x₀).symm y))
          (coordinateFrameAt (I := I) x₀ j ((extChartAt I x₀).symm y)) := by
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy₀] with y hy
  unfold metricFlatModelInChart_component metricFlatModelInChart
  rw [hom_trivializationAt_apply]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀
        ((extChartAt I x₀).symm y) x₀ ((extChartAt I x₀).symm y)
        (g.inner ((extChartAt I x₀).symm y))
        ((Module.finBasis Real E) i)) ((Module.finBasis Real E) j) =
      g.inner ((extChartAt I x₀).symm y)
        (coordinateFrameAt (I := I) x₀ i ((extChartAt I x₀).symm y))
        (coordinateFrameAt (I := I) x₀ j ((extChartAt I x₀).symm y))
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
  have hyT :
      (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hy_src
  have hyDual :
      (extChartAt I x₀).symm y ∈
        (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hyT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hyT hyDual]
  rw [Trivialization.coe_continuousLinearEquivAt_eq'
    (e := trivializationAt (E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] Real) x₀) (R := Real) hyDual]
  rw [Trivialization.symm_continuousLinearEquivAt_eq'
    (e := trivializationAt E (TangentSpace I : M -> Type _) x₀) (R := Real) hyT]
  simp only [ContinuousLinearMap.comp_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base j]
  rw [(extChartAt I x₀).right_inv hy]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hy_src]
  rw [(extChartAt I x₀).right_inv hy]
  have hj_symm :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symm
          ((extChartAt I x₀).symm y) ((Module.finBasis Real E) j) =
        (mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j) := by
    change (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
        ((extChartAt I x₀).symm y) ((Module.finBasis Real E) j) =
      (mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
        (Set.range I) y) ((Module.finBasis Real E) j)
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hy_src]
    rw [(extChartAt I x₀).right_inv hy]
    rfl
  change
      (((Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)).toPretrivialization.linearMapAt Real
          ((extChartAt I x₀).symm y)
          ((g.inner ((extChartAt I x₀).symm y))
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
              (Set.range I) y) ((Module.finBasis Real E) i))))
        ((Module.finBasis Real E) j)) =
      g.inner ((extChartAt I x₀).symm y)
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) i))
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j))
  rw [Pretrivialization.linearMapAt_apply]
  have hyDual' :
      (extChartAt I x₀).symm y ∈
        (Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)).toPretrivialization.baseSet := by
    change (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet ∩
        (trivializationAt Real (fun _ : M => Real) x₀).baseSet
    exact ⟨hyT, by simp⟩
  rw [if_pos hyDual']
  change
      ((Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)
        (⟨(extChartAt I x₀).symm y,
          (g.inner ((extChartAt I x₀).symm y))
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
              (Set.range I) y) ((Module.finBasis Real E) i))⟩ :
          TotalSpace (E →L[Real] Real)
            (fun p : M => TangentSpace I p →L[Real] Real))).2
        ((Module.finBasis Real E) j)) =
      g.inner ((extChartAt I x₀).symm y)
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) i))
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j))
  rw [Bundle.Trivialization.continuousLinearMap_apply]
  simp [Trivial.trivialization, ContinuousLinearMap.comp_apply,
    Trivialization.linearMapAt_apply, Trivialization.symmL_apply]
  have hj_symm' :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symm
          ((chartAt H x₀).symm (I.symm y)) ((Module.finBasis Real E) j) =
        (mfderivWithin 𝓘(Real, E) I ((chartAt H x₀).symm ∘ I.symm)
          (Set.range I) y) ((Module.finBasis Real E) j) := by
    simpa [extChartAt] using hj_symm
  rw [hj_symm']
  rfl


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart_component (I := I) g x₀ i j)
      (Set.range I) (extChartAt I x₀ x₀) := by
  have h := metricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have hi :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          metricFlatModelInChart (I := I) g x₀ y ((Module.finBasis Real E) i))
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using h.clm_apply contDiffWithinAt_const
  simpa [metricFlatModelInChart_component] using hi.clm_apply contDiffWithinAt_const




omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_component_deriv_center
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) (extChartAt I x₀ x₀) ((Module.finBasis Real E) a) =
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ a)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x₀ i y)
            (coordinateFrameAt (I := I) x₀ j y)) x₀ := by
  let z₀ : E := extChartAt I x₀ x₀
  let f : M -> Real := fun y : M =>
    g.inner y (coordinateFrameAt (I := I) x₀ i y)
      (coordinateFrameAt (I := I) x₀ j y)
  have hzRange : z₀ ∈ Set.range I := by
    exact extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have heq :
      metricFlatModelInChart_component (I := I) g x₀ i j
        =ᶠ[𝓝[Set.range I] z₀]
        writtenInExtChartAt I 𝓘(Real, Real) x₀ f := by
    simpa [z₀, f, writtenInExtChartAt] using
      metricFlatModelInChart_component_eq_coord_component_comp_eventually_of_mem
        (I := I) g x₀ i j (mem_extChartAt_target (I := I) x₀)
  have hfd :
      fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) z₀ =
        fderivWithin Real
          (writtenInExtChartAt I 𝓘(Real, Real) x₀ f)
          (Set.range I) z₀ :=
    heq.fderivWithin_eq_of_mem hzRange
  have hf_md : MDifferentiableAt I 𝓘(Real, Real) f x₀ :=
    (metric_coordinateFrame_component_contMDiffAt (I := I) g x₀ i j).mdifferentiableAt
      (by simp)
  have hframe_center :
      coordinateFrameAt (I := I) x₀ a x₀ = (Module.finBasis Real E) a := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ a]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  unfold directionalDerivAlong extDerivFun
  change
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) z₀ ((Module.finBasis Real E) a) =
      (mfderiv I 𝓘(Real, Real) f x₀) (coordinateFrameAt (I := I) x₀ a x₀)
  rw [hframe_center, hf_md.mfderiv, hfd]
  rfl



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_component_deriv_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) y ((Module.finBasis Real E) a))
      (Set.range I) (extChartAt I x₀ x₀) := by
  have hf :=
    metricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ i j
  have hconst :
      ContDiffWithinAt Real ∞
        (fun _ : E => (Module.finBasis Real E) a)
        (Set.range I) (extChartAt I x₀ x₀) :=
    contDiffWithinAt_const
  exact hf.fderivWithin_right_apply hconst I.uniqueDiffOn (by simp)
    (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀))


noncomputable def leviCivitaChristoffelModelRHS
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  (1 / 2 : Real) *
    ∑ l : CoordinateIdx (𝕜 := Real) E,
      ((Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ y))
          (LinearMap.toContinuousLinearMap
            ((Module.finBasis Real E).coord l)))) *
        (fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ j l)
            (Set.range I) y ((Module.finBasis Real E) i) +
          fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ i l)
            (Set.range I) y ((Module.finBasis Real E) j) -
          fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) y ((Module.finBasis Real E) l))



omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaChristoffelModelRHS_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (leviCivitaChristoffelModelRHS (I := I) g x₀ i j k)
      (Set.range I) (extChartAt I x₀ x₀) := by
  classical
  unfold leviCivitaChristoffelModelRHS
  refine contDiffWithinAt_const.mul ?_
  refine ContDiffWithinAt.sum fun l _ => ?_
  have hinv :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ k l
  have h₁ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ i j l
  have h₂ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ j i l
  have h₃ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ l i j
  exact hinv.mul ((h₁.add h₂).sub h₃)



omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaChristoffelModelRHS_center_eq_christoffel
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    leviCivitaChristoffelModelRHS (I := I) g x₀ i j k (extChartAt I x₀ x₀) =
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i j k := by
  classical
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      (Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))
  have hinv : MetricInverseInBasis_gen (I := I) g x₀
      (coordinateFrameAt_toBasis (I := I) x₀) gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x₀
  have hformula :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_coordinate_christoffel_formula
      (I := I) g x₀ gInv hinv i j k
  rw [hformula]
  unfold leviCivitaChristoffelModelRHS
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  dsimp [gInv]
  congr 1
  ·
    have h₁ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ j l)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) i) =
          directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ i)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ j y)
                (coordinateFrameAt (I := I) x₀ l y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ i j l
    have h₂ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i l)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) j) =
          directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ j)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ l y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ j i l
    have h₃ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) l) =
          directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ l)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ j y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ l i j
    rw [h₁, h₂, h₃]


omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_apply_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (v w : E) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v w =
      g.inner x
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
  have hx_src : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x) = x :=
    (extChartAt I x₀).left_inv hx_src
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  have hxT :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hxDual :
      x ∈ (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply]


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_component_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    metricFlatModelInChart_component (I := I) g x₀ i j (extChartAt I x₀ x) =
      g.inner x (coordinateFrameAt (I := I) x₀ i x)
        (coordinateFrameAt (I := I) x₀ j x) := by
  have hx_src : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  have hchart : x ∈ (chartAt H x₀).source := by
    simpa [extChartAt_source] using hx_src
  have hi :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x
          ((Module.finBasis Real E) i) =
        coordinateFrameAt (I := I) x₀ i x := by
    have hsymm := congrArg
      (fun L : E →L[Real] TangentSpace I x => L ((Module.finBasis Real E) i))
      (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real)
        (x₀ := x₀) (x := x) hchart)
    rw [coordinateFrameAt_apply_of_mem (I := I) hx i]
    simpa using hsymm
  have hj :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x
          ((Module.finBasis Real E) j) =
        coordinateFrameAt (I := I) x₀ j x := by
    have hsymm := congrArg
      (fun L : E →L[Real] TangentSpace I x => L ((Module.finBasis Real E) j))
      (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real)
        (x₀ := x₀) (x := x) hchart)
    rw [coordinateFrameAt_apply_of_mem (I := I) hx j]
    simpa using hsymm
  unfold metricFlatModelInChart_component
  rw [metricFlatModelInChart_apply_of_mem (I := I) g x₀ hx]
  rw [hi, hj]



omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
private theorem inverseMetricFlatModelInChart_metricInverseInBasis_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    MetricInverseInBasis_gen (I := I) g x (coordinateFrameAt_basis (I := I) x₀ hx)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)))
            (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))) := by
  classical
  let A : E →L[Real] E →L[Real] Real :=
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => (Module.finBasis Real E).coord k
      ((ContinuousLinearMap.inverse A) (ε l))
  have hxT :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hA_local :
      A =
        localMetricFlatBasis (I := I)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (Module.finBasis Real E) g x := by
    ext v w
    calc
      A v w =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            simpa [A] using metricFlatModelInChart_apply_of_mem
              (I := I) g x₀ hx v w
      _ =
          localMetricFlatBasis (I := I)
            (trivializationAt E (TangentSpace I : M -> Type _) x₀)
            (Module.finBasis Real E) g x v w := by
            rw [localMetricFlatBasis_eq_inner
              (I := I)
              (e := trivializationAt E (TangentSpace I : M -> Type _) x₀)
              (b := Module.finBasis Real E) g hxT v w]
  have hInv : A.IsInvertible := by
    rw [hA_local]
    exact localMetricFlatBasis_isInvertible
      (I := I)
      (e := trivializationAt E (TangentSpace I : M -> Type _) x₀)
      (b := Module.finBasis Real E) g hxT
  have hA_symm (v w : E) : A v w = A w v := by
    calc
      A v w =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            simpa [A] using metricFlatModelInChart_apply_of_mem
              (I := I) g x₀ hx v w
      _ =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) := by
            exact g.symm x _ _
      _ = A w v := by
            symm
            simpa [A] using metricFlatModelInChart_apply_of_mem
              (I := I) g x₀ hx w v
  have hcomp (i j : CoordinateIdx (𝕜 := Real) E) :
      A ((Module.finBasis Real E) i) ((Module.finBasis Real E) j) =
        g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) i)
          ((coordinateFrameAt_basis (I := I) x₀ hx) j) := by
    have hmetric :=
      metricFlatModelInChart_component_of_mem
        (I := I) g x₀ hx i j
    simpa [A, metricFlatModelInChart_component,
      coordinateFrameAt_basis_apply] using hmetric
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l =
        (Module.finBasis Real E).coord k ((ContinuousLinearMap.inverse A) (ε l)) := rfl
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k ((ContinuousLinearMap.inverse A) (ε l))
          = (ε k) ((ContinuousLinearMap.inverse A) (ε l)) := rfl
      _ = (A ((ContinuousLinearMap.inverse A) (ε k)))
            ((ContinuousLinearMap.inverse A) (ε l)) := by
            rw [hInv.self_apply_inverse]
      _ = (A ((ContinuousLinearMap.inverse A) (ε l)))
            ((ContinuousLinearMap.inverse A) (ε k)) := by
            rw [hA_symm]
      _ = (ε l) ((ContinuousLinearMap.inverse A) (ε k)) := by
            rw [hInv.self_apply_inverse]
      _ = (Module.finBasis Real E).coord l ((ContinuousLinearMap.inverse A) (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) i)
            ((coordinateFrameAt_basis (I := I) x₀ hx) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) i)
            ((coordinateFrameAt_basis (I := I) x₀ hx) k) * gInv k j)
          = ∑ k : CoordinateIdx (𝕜 := Real) E,
              A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                (Module.finBasis Real E).coord k ((ContinuousLinearMap.inverse A) (ε j)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hginv]
            rw [hcomp i k]
      _ = A ((Module.finBasis Real E) i)
            (∑ k : CoordinateIdx (𝕜 := Real) E,
              (Module.finBasis Real E).coord k ((ContinuousLinearMap.inverse A) (ε j)) •
                (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [map_smul]
            simp [smul_eq_mul]
            ring
      _ = A ((Module.finBasis Real E) i)
            ((ContinuousLinearMap.inverse A) (ε j)) := by
            have hsum :=
              (Module.finBasis Real E).sum_repr
                ((ContinuousLinearMap.inverse A) (ε j))
            exact congrArg (fun v => A ((Module.finBasis Real E) i) v)
              (by simpa [Module.Basis.coord] using hsum)
      _ = ε j ((Module.finBasis Real E) i) := by
            rw [hA_symm]
            have happ := congrArg
              (fun L : E →L[Real] Real => L ((Module.finBasis Real E) i))
              (hInv.self_apply_inverse (ε j))
            simpa using happ
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := fun h => hij h.symm
              simp [ε, hji, hij]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) k)
            ((coordinateFrameAt_basis (I := I) x₀ hx) j))
          = ∑ k : CoordinateIdx (𝕜 := Real) E,
              g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) j)
                ((coordinateFrameAt_basis (I := I) x₀ hx) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x ((coordinateFrameAt_basis (I := I) x₀ hx) k)
              ((coordinateFrameAt_basis (I := I) x₀ hx) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j





omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem fderivWithin_writtenInExtChartAt_eq_directionalDeriv_of_mem
    [I.Boundaryless]
    {f : M -> Real} {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (a : CoordinateIdx (𝕜 := Real) E) :
    fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f)
        (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) a) =
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ a) f x := by
  let z : E := extChartAt I x₀ x
  let φ : E -> Real := writtenInExtChartAt I 𝓘(Real, Real) x₀ f
  let V : TangentSpace I x := coordinateFrameAt (I := I) x₀ a x
  have hx_src : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  have hz_tgt : z ∈ (extChartAt I x₀).target := by
    simpa [z] using (extChartAt I x₀).map_source hx_src
  have hφ_within :
      MDifferentiableWithinAt 𝓘(Real, E) 𝓘(Real, Real)
        (f ∘ (extChartAt I x₀).symm) (Set.range I) z := by
    have hsrc : x ∈ (chartAt H x₀).source := by
      simpa [extChartAt_source] using hx_src
    simpa [z, extChartAt, Function.comp_def] using
      (mdifferentiableAt_iff_source_of_mem_source
        (I := I) (I' := 𝓘(Real, Real)) (x := x₀) (x' := x) hsrc).mp hf
  have hφ : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real) φ z := by
    rw [← mdifferentiableWithinAt_univ]
    simpa [φ, z, writtenInExtChartAt, Function.comp_def,
      ModelWithCorners.Boundaryless.range_eq_univ (I := I)] using hφ_within
  have hchart : MDifferentiableAt I 𝓘(Real, E) (extChartAt I x₀) x := by
    have hsrc : x ∈ (chartAt H x₀).source := by
      simpa [extChartAt_source] using hx_src
    exact mdifferentiableAt_extChartAt (I := I) (x := x₀) hsrc
  have hlocal : f =ᶠ[𝓝 x] φ ∘ (extChartAt I x₀) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds hx_src] with y hy
    have hy_chart : y ∈ (chartAt H x₀).source := by
      simpa [extChartAt_source] using hy
    simp [φ, writtenInExtChartAt, extChartAt, Function.comp_def,
      (chartAt H x₀).left_inv hy_chart]
  have hmfd :
      mfderiv I 𝓘(Real, Real) f x =
        mfderiv I 𝓘(Real, Real) (φ ∘ (extChartAt I x₀)) x :=
    hlocal.mfderiv_eq
  have hVchart :
      (mfderiv I 𝓘(Real, E) (extChartAt I x₀) x) V =
        (Module.finBasis Real E) a := by
    have hcomp := congrArg
      (fun L : E →L[Real] E => L ((Module.finBasis Real E) a))
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        (I := I) (x := x₀) hx_src)
    dsimp [V]
    rw [coordinateFrameAt_apply_of_mem (I := I) hx a]
    simpa [ContinuousLinearMap.comp_apply] using hcomp
  have hmodel :
      fderiv Real φ z ((Module.finBasis Real E) a) =
        (mfderiv I 𝓘(Real, Real) (φ ∘ (extChartAt I x₀)) x) V := by
    rw [← mfderiv_eq_fderiv (𝕜 := Real) (f := φ) (x := z)]
    rw [mfderiv_comp_apply (I := I) (I' := 𝓘(Real, E))
      (I'' := 𝓘(Real, Real)) (g := φ)
      (f := extChartAt I x₀) (x := x) (v := V) hφ hchart]
    rw [hVchart]
    rfl
  rw [fderivWithin_of_mem_nhds]
  · rw [hmodel]
    rw [← hmfd]
    simp [directionalDerivAlong, V, extDerivFun_real_eq_mfderiv]
    rfl
  · rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_component_deriv_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) a) =
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ a)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x₀ i y)
            (coordinateFrameAt (I := I) x₀ j y)) x := by
  let z : E := extChartAt I x₀ x
  let f : M -> Real := fun y : M =>
    g.inner y (coordinateFrameAt (I := I) x₀ i y)
      (coordinateFrameAt (I := I) x₀ j y)
  have hx_src : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  have hz_tgt : z ∈ (extChartAt I x₀).target := by
    simpa [z] using (extChartAt I x₀).map_source hx_src
  have hzRange : z ∈ Set.range I :=
    extChartAt_target_subset_range x₀ hz_tgt
  have heq :
      metricFlatModelInChart_component (I := I) g x₀ i j
        =ᶠ[𝓝[Set.range I] z]
        writtenInExtChartAt I 𝓘(Real, Real) x₀ f := by
    simpa [z, f, writtenInExtChartAt] using
      metricFlatModelInChart_component_eq_coord_component_comp_eventually_of_mem
        (I := I) g x₀ i j hz_tgt
  have hfd :
      fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) z =
        fderivWithin Real
          (writtenInExtChartAt I 𝓘(Real, Real) x₀ f)
          (Set.range I) z :=
    heq.fderivWithin_eq_of_mem hzRange
  have hf_md : MDifferentiableAt I 𝓘(Real, Real) f x :=
    (metric_coordinateFrame_component_contMDiffAt_of_mem
      (I := I) g x₀ hx i j).mdifferentiableAt (by simp)
  calc
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) z ((Module.finBasis Real E) a)
        = fderivWithin Real
            (writtenInExtChartAt I 𝓘(Real, Real) x₀ f)
            (Set.range I) z ((Module.finBasis Real E) a) := by
            rw [hfd]
    _ = directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ a) f x := by
            exact fderivWithin_writtenInExtChartAt_eq_directionalDeriv_of_mem
              (I := I) hx hf_md a







omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaChristoffelModelRHS_eq_christoffel_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    leviCivitaChristoffelModelRHS (I := I) g x₀ i j k (extChartAt I x₀ x) =
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x i j k := by
  classical
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      (Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))
  have hinv : MetricInverseInBasis_gen (I := I) g x
      (coordinateFrameAt_basis (I := I) x₀ hx) gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_of_mem (I := I) g x₀ hx
  have hformula :=
    DifferentialGeometry.Integral.Connection.coordinateFrame_christoffel_formula_point_of_isLeviCivita
      (I := I) (cov := leviCivitaConnectionOfMetric (I := I) g) g
      (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g)
      x₀ hx gInv hinv i j k
  rw [hformula]
  unfold leviCivitaChristoffelModelRHS
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  dsimp [gInv]
  congr 1
  ·
    have h₁ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ j l)
            (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) i) =
          directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ i)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ j y)
                (coordinateFrameAt (I := I) x₀ l y)) x := by
        exact metricFlatModelInChart_component_deriv_of_mem
          (I := I) g x₀ hx i j l
    have h₂ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i l)
            (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) j) =
          directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ j)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ l y)) x := by
        exact metricFlatModelInChart_component_deriv_of_mem
          (I := I) g x₀ hx j i l
    have h₃ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) l) =
          directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ l)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ j y)) x := by
        exact metricFlatModelInChart_component_deriv_of_mem
          (I := I) g x₀ hx l i j
    simpa [extChartAt] using show
      (fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ j l)
              (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) i) +
            fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i l)
              (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) j) -
          fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) (extChartAt I x₀ x) ((Module.finBasis Real E) l)) =
        directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ i)
              (fun y : M =>
                g.inner y (coordinateFrameAt (I := I) x₀ j y)
                  (coordinateFrameAt (I := I) x₀ l y)) x +
            directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ j)
              (fun y : M =>
                g.inner y (coordinateFrameAt (I := I) x₀ i y)
                  (coordinateFrameAt (I := I) x₀ l y)) x -
          directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x₀ l)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ j y)) x by
      rw [h₁, h₂, h₃]





omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_component_contDiffWithinAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart_component (I := I) g x₀ i j)
      (Set.range I) y := by
  have h := metricFlatModelInChart_contDiffWithinAt_of_mem (I := I) g x₀ hy
  have hi :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          metricFlatModelInChart (I := I) g x₀ y ((Module.finBasis Real E) i))
        (Set.range I) y := by
    simpa using h.clm_apply contDiffWithinAt_const
  simpa [metricFlatModelInChart_component] using hi.clm_apply contDiffWithinAt_const



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_component_deriv_contDiffWithinAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) y ((Module.finBasis Real E) a))
      (Set.range I) y := by
  have hf :=
    metricFlatModelInChart_component_contDiffWithinAt_of_mem
      (I := I) g x₀ hy i j
  have hconst :
      ContDiffWithinAt Real ∞
        (fun _ : E => (Module.finBasis Real E) a)
        (Set.range I) y :=
    contDiffWithinAt_const
  exact hf.fderivWithin_right_apply hconst I.uniqueDiffOn (by simp)
    (extChartAt_target_subset_range x₀ hy)



omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
theorem metricFlatModelInChart_isInvertible_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    (metricFlatModelInChart (I := I) g x₀ y).IsInvertible := by
  let p : M := (extChartAt I x₀).symm y
  have hp_src : p ∈ (extChartAt I x₀).source := by
    simpa [p] using (extChartAt I x₀).map_target hy
  have hp_coord : p ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source]
      using hp_src
  have hpT :
      p ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hp_coord
  have hpy : extChartAt I x₀ p = y := by
    simpa [p] using (extChartAt I x₀).right_inv hy
  have hlocal :
      metricFlatModelInChart (I := I) g x₀ y =
        localMetricFlatBasis (I := I)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (Module.finBasis Real E) g p := by
    rw [← hpy]
    ext v w
    calc
      metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ p) v w =
          g.inner p
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real p v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real p w) := by
            simpa using metricFlatModelInChart_apply_of_mem
              (I := I) g x₀ hp_coord v w
      _ =
          localMetricFlatBasis (I := I)
            (trivializationAt E (TangentSpace I : M -> Type _) x₀)
            (Module.finBasis Real E) g p v w := by
            rw [localMetricFlatBasis_eq_inner
              (I := I)
              (e := trivializationAt E (TangentSpace I : M -> Type _) x₀)
              (b := Module.finBasis Real E) g hpT v w]
  rw [hlocal]
  exact localMetricFlatBasis_isInvertible
    (I := I)
    (e := trivializationAt E (TangentSpace I : M -> Type _) x₀)
    (b := Module.finBasis Real E) g hpT



omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_component_contDiffWithinAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y))
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis Real E).coord l))))
      (Set.range I) y := by
  let εl : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)
  let εk : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hinv :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ y))
        (Set.range I) y := by
    exact
      (metricFlatModelInChart_isInvertible_of_mem (I := I) g x₀ hy).contDiffAt_map_inverse
        |>.comp_contDiffWithinAt
          (x := y)
          (metricFlatModelInChart_contDiffWithinAt_of_mem (I := I) g x₀ hy)
  have happ :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          (ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y)) εl)
        (Set.range I) y := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  simpa [εk, εl] using (contDiffWithinAt_const (c := εk)).clm_apply happ



omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaChristoffelModelRHS_contDiffWithinAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (leviCivitaChristoffelModelRHS (I := I) g x₀ i j k)
      (Set.range I) y := by
  classical
  unfold leviCivitaChristoffelModelRHS
  refine contDiffWithinAt_const.mul ?_
  refine ContDiffWithinAt.sum fun l _ => ?_
  have hinv :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt_of_mem
      (I := I) g x₀ hy k l
  have h₁ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt_of_mem
      (I := I) g x₀ hy i j l
  have h₂ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt_of_mem
      (I := I) g x₀ hy j i l
  have h₃ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt_of_mem
      (I := I) g x₀ hy l i j
  exact hinv.mul ((h₁.add h₂).sub h₃)
end DifferentialGeometry.Integral.Connection
