import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricCoord

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















noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  ((metricFlatEquiv (I := I) g x₀).trans
    (LinearMap.toContinuousLinearMap :
      (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real))).toContinuousLinearEquiv

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w = g.inner x₀ v w := by
  change ((metricFlatEquiv (I := I) g x₀) v) w = g.inner x₀ v w
  rw [metricFlatEquiv_apply]



noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  (trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
      ⟨(extChartAt I x₀).symm y, g.inner ((extChartAt I x₀).symm y)⟩).2

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real)) := by
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  ext v w
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀ x₀ x₀ x₀
        (g.inner x₀) v) w =
      ((metricFlatContinuousEquiv (I := I) g x₀) v) w
  have hxT :
      x₀ ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simp
  have hxDual :
      x₀ ∈ (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  simp [metricFlatContinuousEquiv, hom_trivializationAt,
    Trivialization.continuousLinearMap_apply]
  have hL :
      (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ =
        (1 : E →L[Real] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x₀) (b := x₀) (mem_chart_source H x₀)]
    ext z
    exact (tangentBundleCore I M).coordChange_self (achart H x₀) x₀
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x₀) z
  have hsymm (z : E) :
      (trivializationAt E (TangentSpace I) x₀).symm x₀ z = z := by
    change (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ z = z
    rw [hL]
    rfl
  rw [hsymm v, hsymm w]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv


omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x₀ :=
    (g.contMDiff.contMDiffAt (x := x₀)).of_le (by simp)
  have hcoord :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2) x₀ :=
    by
      rw [contMDiffAt_totalSpace] at hg
      simpa [e] using hg.2
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => (e ⟨p, g.inner p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt
      (x := extChartAt I x₀ x₀) hsymm
  exact hcomp.contDiffWithinAt



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_apply_of_target
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v w : E) :
    metricFlatModelInChart (I := I) g x₀ y v w =
      g.inner ((extChartAt I x₀).symm y)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
          ((extChartAt I x₀).symm y) v)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
          ((extChartAt I x₀).symm y) w) := by
  let p : M := (extChartAt I x₀).symm y
  have hp_src : p ∈ (extChartAt I x₀).source := by
    simpa [p] using (extChartAt I x₀).map_target hy
  have hpy : extChartAt I x₀ p = y := by
    simpa [p] using (extChartAt I x₀).right_inv hy
  have hcenter : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
    (extChartAt I x₀).left_inv hp_src
  rw [← hpy, hcenter]
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  have hpT :
      p ∈
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_src
  have hpDual :
      p ∈
        (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hpT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hpT hpDual]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply]


omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact
    (metricFlatModelInChart_center_isInvertible (I := I) g x₀).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt
        (x := extChartAt I x₀ x₀)
        (metricFlatModelInChart_contDiffWithinAt (I := I) g x₀)



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_contDiffWithinAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) y := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let b := Module.finBasis Real E
  let p : M := (extChartAt I x₀).symm y
  have hp_src : p ∈ (extChartAt I x₀).source := by
    simpa [p] using (extChartAt I x₀).map_target hy
  have hpE : p ∈ e.baseSet := by
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_src
  have hlocal :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => localMetricFlatBasis (I := I) e b g p) p :=
    localMetricFlatBasis_contMDiffAt (I := I) e b g hpE
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) y := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) x₀ hy
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => localMetricFlatBasis (I := I) e b g p) ∘
          (extChartAt I x₀).symm)
        (Set.range I) y :=
    hlocal.comp_contMDiffWithinAt (x := y) hsymm
  have heq :
      metricFlatModelInChart (I := I) g x₀ =ᶠ[𝓝[Set.range I] y]
        fun y' : E =>
          localMetricFlatBasis (I := I) e b g ((extChartAt I x₀).symm y') := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy] with y' hy'
    have hp'_src : (extChartAt I x₀).symm y' ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy'
    have hp'E : (extChartAt I x₀).symm y' ∈ e.baseSet := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp'_src
    ext v w
    calc
      metricFlatModelInChart (I := I) g x₀ y' v w =
          g.inner ((extChartAt I x₀).symm y')
            (e.symmL Real ((extChartAt I x₀).symm y') v)
            (e.symmL Real ((extChartAt I x₀).symm y') w) := by
            simpa [e] using metricFlatModelInChart_apply_of_target
              (I := I) g x₀ hy' v w
      _ =
          localMetricFlatBasis (I := I) e b g ((extChartAt I x₀).symm y') v w := by
            rw [localMetricFlatBasis_eq_inner (I := I) e b g hp'E v w]
  exact hcomp.contDiffWithinAt.congr_of_eventuallyEq heq
    (heq.self_of_nhdsWithin (extChartAt_target_subset_range x₀ hy))


omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y))
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis Real E).coord l))))
      (Set.range I) (extChartAt I x₀ x₀) := by
  let εl : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)
  let εk : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hinv := inverseMetricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have happ :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          (ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y)) εl)
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  simpa [εk, εl] using (contDiffWithinAt_const (c := εk)).clm_apply happ

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (Module.finBasis Real E).coord i
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord j))) =
      (Module.finBasis Real E).coord j
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i))) := by
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  rw [hInv]
  calc
    (Module.finBasis Real E).coord i (A.symm (ε j))
        = (ε i) (A.symm (ε j)) := rfl
    _ = (A (A.symm (ε i))) (A.symm (ε j)) := by
          rw [A.apply_symm_apply]
    _ = g.inner x₀ (A.symm (ε i)) (A.symm (ε j)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = g.inner x₀ (A.symm (ε j)) (A.symm (ε i)) := by
          exact g.symm x₀ (A.symm (ε i)) (A.symm (ε j))
    _ = (A (A.symm (ε j))) (A.symm (ε i)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = (ε j) (A.symm (ε i)) := by
          rw [A.apply_symm_apply]
    _ = (Module.finBasis Real E).coord j (A.symm (ε i)) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis_gen (I := I) g x₀ (coordinateFrameAt_toBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
            (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))) := by
  classical
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      (Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀))) (ε l))
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  have hbasis :
      coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis Real E :=
    coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.symm (ε l)) := by
    dsimp [gInv]
    simpa [extChartAt] using
      congrArg (fun L : (E →L[Real] Real) →L[Real] E =>
        (Module.finBasis Real E).coord k (L (ε l))) hInv
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.symm (ε l))
          = (ε k) (A.symm (ε l)) := rfl
      _ = (A (A.symm (ε k))) (A.symm (ε l)) := by
            rw [A.apply_symm_apply]
      _ = g.inner x₀ (A.symm (ε k)) (A.symm (ε l)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = g.inner x₀ (A.symm (ε l)) (A.symm (ε k)) := by
            exact g.symm x₀ (A.symm (ε k)) (A.symm (ε l))
      _ = (A (A.symm (ε l))) (A.symm (ε k)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = (ε l) (A.symm (ε k)) := by
            rw [A.apply_symm_apply]
      _ = (Module.finBasis Real E).coord l (A.symm (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) i)
            ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    rw [hbasis]
    simp only [hginv]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.symm (ε j)))
          = g.inner x₀ ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.symm (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (g.inner x₀ ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.symm (ε j)))
                ((Module.finBasis Real E) k)
            calc
              g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.symm (ε j))
                  = (Module.finBasis Real E).coord k (A.symm (ε j)) *
                      g.inner x₀ ((Module.finBasis Real E) i)
                        ((Module.finBasis Real E) k) := by ring
              _ = (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    g.inner x₀ ((Module.finBasis Real E) i)
                      ((Module.finBasis Real E) k) := by simp
              _ = g.inner x₀ ((Module.finBasis Real E) i)
                    ((Module.finBasis Real E).coord k (A.symm (ε j)) •
                      (Module.finBasis Real E) k) := hmap.symm
      _ = g.inner x₀ ((Module.finBasis Real E) i) (A.symm (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    (Module.finBasis Real E) k) = A.symm (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.symm (ε j))
            exact congrArg (fun v => g.inner x₀ ((Module.finBasis Real E) i) v) hsum
      _ = g.inner x₀ (A.symm (ε j)) ((Module.finBasis Real E) i) := by
            exact g.symm x₀ ((Module.finBasis Real E) i) (A.symm (ε j))
      _ = (A (A.symm (ε j))) ((Module.finBasis Real E) i) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = ε j ((Module.finBasis Real E) i) := by
            rw [A.apply_symm_apply]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := by exact fun h => hij h.symm
              simp [ε, hji, hij]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
            ((coordinateFrameAt_toBasis (I := I) x₀) j))
          = ∑ k : CoordinateIdx (𝕜 := Real) E,
              g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) j)
                ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
              ((coordinateFrameAt_toBasis (I := I) x₀) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j




noncomputable def metricFlatModelInChart_component
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  metricFlatModelInChart (I := I) g x₀ y
    ((Module.finBasis Real E) i) ((Module.finBasis Real E) j)
end DifferentialGeometry.Integral.Connection
