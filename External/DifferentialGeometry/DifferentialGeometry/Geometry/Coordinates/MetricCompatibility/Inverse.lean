import DifferentialGeometry.Geometry.Connection.MetricCompatibility
import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame
import DifferentialGeometry.Geometry.Curvature.Basic
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false










namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}



noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  ((metricFlatEquiv (I := I) g x₀).trans
    (LinearMap.toContinuousLinearMap :
      (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real))).toContinuousLinearEquiv

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
  rw [metricFlatContinuousEquiv_apply]
  simp only [hom_trivializationAt, Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply, Function.comp_apply]
  have hxR : x₀ ∈ (trivializationAt Real (fun _ : M => Real) x₀).baseSet := by
    simp
  rw [Trivialization.continuousLinearMapAt_apply]
  rw [(trivializationAt Real (fun _ : M => Real) x₀).coe_linearMapAt_of_mem
    (R := Real) hxR]
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
  have hsymmL (z : E) :
      (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ z = z := by
    rw [hL]
    rfl
  change g.inner x₀ ((trivializationAt E (TangentSpace I) x₀).symm x₀ v)
      ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w) = g.inner x₀ v w
  calc
    g.inner x₀ ((trivializationAt E (TangentSpace I) x₀).symm x₀ v)
        ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w)
        = g.inner x₀ v ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w) := by
          exact congrArg
            (fun z => g.inner x₀ z ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w))
            (hsymm v)
    _ = g.inner x₀ v w := by
          exact congrArg (fun z => g.inner x₀ v z) (hsymmL w)

omit [FiniteDimensional ℝ E] in
theorem flatChart_apply
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

theorem flatChart_inv
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)).IsInvertible := by
  haveI : CompleteSpace (E →L[Real] Real) := inferInstance
  let A : E →ₗ[Real] (E →L[Real] Real) :=
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)).toLinearMap
  have hxT :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hker : LinearMap.ker A = ⊥ := by
    ext v
    constructor
    · intro hv
      change A v = 0 at hv
      have hself :
          metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v v = 0 := by
        exact congrArg (fun L : E →L[Real] Real => L v) hv
      have hinner :
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) = 0 := by
        rw [← flatChart_apply (I := I) g x₀ hx v v]
        exact hself
      by_contra hvne
      have hsymm_ne :
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v ≠ 0 := by
        intro hzero
        have hmap := congrArg
          ((trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
            Real x) hzero
        have hcancel :
            (trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
                Real x
              ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) = v :=
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt_symmL
            (R := Real) hxT v
        rw [hcancel] at hmap
        exact hvne (by simpa using hmap)
      exact False.elim ((ne_of_gt (g.pos x
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
        hsymm_ne)) hinner)
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      simp [A, hv0]
  have hdim :
      Module.finrank Real E = Module.finrank Real (E →L[Real] Real) := by
    calc
      Module.finrank Real E = Module.finrank Real (Module.Dual Real E) :=
        Subspace.dual_finrank_eq.symm
      _ = Module.finrank Real (E →L[Real] Real) :=
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real)).finrank_eq
  let Aequiv : E ≃ₗ[Real] (E →L[Real] Real) :=
    A.linearEquivOfInjective (LinearMap.ker_eq_bot.mp hker) hdim
  let Acle : E ≃L[Real] (E →L[Real] Real) :=
    Aequiv.toContinuousLinearEquiv
  have hA : (Acle : E →L[Real] E →L[Real] Real) =
      metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) := by
    ext v w
    change Aequiv v w =
      metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v w
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  rw [← hA]
  exact ContinuousLinearMap.isInvertible_equiv

theorem coordBasis_model
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordinateFrameAt_basis (I := I) x₀ hx i =
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x
        ((Module.finBasis Real E) i) := by
  rw [coordinateFrameAt_basis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) hx i]
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  simpa [Trivialization.symmL_apply, extChartAt] using
    (congrArg (fun L : E →L[Real] TangentSpace I x => L ((Module.finBasis Real E) i))
      (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_src)).symm

theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv


omit [FiniteDimensional ℝ E] in
theorem metricFlatModelInChart_contDiffWithinAt
    [CompleteSpace E]
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


theorem inverseMetricFlatModelInChart_contDiffWithinAt
    [CompleteSpace E]
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

noncomputable def inverseMetricFlatModelInChart_component
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  (Module.finBasis Real E).coord k
    ((ContinuousLinearMap.inverse
        (metricFlatModelInChart (I := I) g x₀ y))
      (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))


theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (inverseMetricFlatModelInChart_component (I := I) g x₀ k l)
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
  simpa [inverseMetricFlatModelInChart_component, εk, εl] using
    (contDiffWithinAt_const (c := εk)).clm_apply happ

theorem gInvComp_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀ := by
  haveI : CompleteSpace E := FiniteDimensional.complete Real E
  let f : E -> Real :=
    inverseMetricFlatModelInChart_component (I := I) g x₀ k l
  have hf :
      ContDiffWithinAt Real ∞ f (Set.range I) (extChartAt I x₀ x₀) :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ k l
  have hchart :
      ContMDiffWithinAt I 𝓘(Real, E) ∞ (extChartAt I x₀)
        (extChartAt I x₀).source x₀ :=
    (contMDiffAt_extChartAt (I := I) (x := x₀)).contMDiffWithinAt
  have hcomp :
      ContMDiffWithinAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀)
        (extChartAt I x₀).source x₀ := by
    exact hf.comp_contMDiffWithinAt hchart (by
      intro y hy
      exact extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hy))
  have hcompAt :
      ContMDiffAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀) x₀ :=
    hcomp.contMDiffAt ((isOpen_extChartAt_source (I := I) x₀).mem_nhds
      (mem_extChartAt_source (I := I) x₀))
  simpa [f, Function.comp_def] using hcompAt

theorem gInvComp_mdiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀ := by
  exact (gInvComp_contMDiffAt (I := I) g x₀ k l).mdifferentiableAt (by simp)

theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ x₀) =
      inverseMetricFlatModelInChart_component (I := I) g x₀ j i
        (extChartAt I x₀ x₀) := by
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  simp only [inverseMetricFlatModelInChart_component]
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



theorem gInvChart_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ x) =
      inverseMetricFlatModelInChart_component (I := I) g x₀ j i
        (extChartAt I x₀ x) := by
  let A : E →L[Real] (E →L[Real] Real) :=
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv : A.IsInvertible := flatChart_inv (I := I) g x₀ hx
  have hA_sym (v w : E) : A v w = A w v := by
    calc
      A v w =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            exact flatChart_apply (I := I) g x₀ hx v w
      _ =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) := by
            exact g.symm x _ _
      _ = A w v := by
            rw [flatChart_apply (I := I) g x₀ hx w v]
  simp only [inverseMetricFlatModelInChart_component]
  calc
    (Module.finBasis Real E).coord i (ContinuousLinearMap.inverse A (ε j))
        = (ε i) (ContinuousLinearMap.inverse A (ε j)) := rfl
    _ = (A (ContinuousLinearMap.inverse A (ε i)))
          (ContinuousLinearMap.inverse A (ε j)) := by
          rw [hInv.self_apply_inverse]
    _ = (A (ContinuousLinearMap.inverse A (ε j)))
          (ContinuousLinearMap.inverse A (ε i)) := by
          exact hA_sym (ContinuousLinearMap.inverse A (ε i))
            (ContinuousLinearMap.inverse A (ε j))
    _ = (ε j) (ContinuousLinearMap.inverse A (ε i)) := by
          rw [hInv.self_apply_inverse]
    _ = (Module.finBasis Real E).coord j (ContinuousLinearMap.inverse A (ε i)) := rfl

theorem gInvBasisAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    MetricInverseInBasis_gen (I := I) g x (coordinateFrameAt_basis (I := I) x₀ hx)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ x)) := by
  classical
  let A : E →L[Real] (E →L[Real] Real) :=
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => inverseMetricFlatModelInChart_component (I := I) g x₀ k l
      (extChartAt I x₀ x)
  have hInv : A.IsInvertible := flatChart_inv (I := I) g x₀ hx
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.inverse (ε l)) := by
    rfl
  have hA_sym (v w : E) : A v w = A w v := by
    calc
      A v w =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            exact flatChart_apply (I := I) g x₀ hx v w
      _ =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) := by
            exact g.symm x _ _
      _ = A w v := by
            rw [flatChart_apply (I := I) g x₀ hx w v]
  have hmetric (i j : CoordinateIdx (𝕜 := Real) E) :
      g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) i)
          ((coordinateFrameAt_basis (I := I) x₀ hx) j) =
        A ((Module.finBasis Real E) i) ((Module.finBasis Real E) j) := by
    rw [coordBasis_model (I := I) x₀ hx i]
    rw [coordBasis_model (I := I) x₀ hx j]
    rw [flatChart_apply (I := I) g x₀ hx]
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.inverse (ε l))
          = (ε k) (A.inverse (ε l)) := rfl
      _ = (A (A.inverse (ε k))) (A.inverse (ε l)) := by
            rw [hInv.self_apply_inverse]
      _ = (A (A.inverse (ε l))) (A.inverse (ε k)) := by
            exact hA_sym (A.inverse (ε k)) (A.inverse (ε l))
      _ = (ε l) (A.inverse (ε k)) := by
            rw [hInv.self_apply_inverse]
      _ = (Module.finBasis Real E).coord l (A.inverse (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) i)
            ((coordinateFrameAt_basis (I := I) x₀ hx) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    simp only [hmetric, hginv]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.inverse (ε j)))
          = A ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (A ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.inverse (ε j)))
                ((Module.finBasis Real E) k)
            calc
              A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.inverse (ε j))
                  =
                (Module.finBasis Real E).coord k (A.inverse (ε j)) *
                  A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by ring
              _ =
                (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                  A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by simp
              _ =
                A ((Module.finBasis Real E) i)
                  ((Module.finBasis Real E).coord k (A.inverse (ε j)) •
                    (Module.finBasis Real E) k) := hmap.symm
      _ = A ((Module.finBasis Real E) i) (A.inverse (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                    (Module.finBasis Real E) k) = A.inverse (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.inverse (ε j))
            exact congrArg (fun v => A ((Module.finBasis Real E) i) v) hsum
      _ = (A (A.inverse (ε j))) ((Module.finBasis Real E) i) := by
            exact hA_sym ((Module.finBasis Real E) i) (A.inverse (ε j))
      _ = (ε j) ((Module.finBasis Real E) i) := by
            rw [hInv.self_apply_inverse]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := fun h => hij h.symm
              simp [ε, hij, hji]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) k)
            ((coordinateFrameAt_basis (I := I) x₀ hx) j))
          =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
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

theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis_gen (I := I) g x₀ (coordinateFrameAt_toBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ x₀)) := by
  classical
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => inverseMetricFlatModelInChart_component (I := I) g x₀ k l
      (extChartAt I x₀ x₀)
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
    dsimp [gInv, inverseMetricFlatModelInChart_component]
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


def metricCompForMetricInFrame
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  g.inner x (frame i x) (frame j x)

theorem gInvBasisNhds
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M => ∑ k : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x₀ i k
          (extChartAt I x₀ y) *
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) y k j) =ᶠ[𝓝 x₀]
      fun _ : M => if i = j then 1 else 0 := by
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
    (coordinateFrameAt_mem (I := I) x₀)] with y hy
  have h := (gInvBasisAt (I := I) g x₀ hy i j).1
  simpa [metricCompForMetricInFrame, coordinateFrameAt_basis_apply] using h

end Components

end
end DifferentialGeometry.Tensor.Coordinates
