import DifferentialGeometry.Geometry.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Topology.UniversalCover.LiftedMetricSmoothness
import DifferentialGeometry.Geometry.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import DifferentialGeometry.Geometry.Curvature.Riemann.Ricci
import DifferentialGeometry.Geometry.Geodesic.Equation
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic





















open Set Function Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Integral.Measure
  (SmoothRiemannianMetric chartBasisVecFiber chartModelBasis chartGramMatrix)
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartInvGramMatrix chartGramOnE chartChristoffel partialDeriv
   chartRiemannTensor chartRicciTensor)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]
























omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem chartBasisVecFiber_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (i : Fin (Module.finrank ℝ E))
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source) :
    chartBasisVecFiber (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        α' i x' =
      chartBasisVecFiber (I := I) (M := M)
        (proj (X := M) α') i (proj (X := M) x') := by
  let _ := g
  have hx'_cover : x' ∈ (coverChartAt α').source := hx'
  have hx'_inter : x' ∈ (localSection (M := M) α').source ∩
      (localSection (M := M) α') ⁻¹' (chartAt H (proj α')).source := by
    have hsrc : ((coverChartAt α') :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection α').source ∩
          (localSection α') ⁻¹' (chartAt H (proj α')).source :=
      coverChartAt_source_eq α'
    rw [hsrc] at hx'_cover; exact hx'_cover
  obtain ⟨_hLSsrc, hLSchart⟩ := hx'_inter
  have hLS_x' : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  have hprojx'_chartM : proj x' ∈ (chartAt H (proj α')).source := by
    rw [Set.mem_preimage, hLS_x'] at hLSchart
    exact hLSchart
  have hLHS_symm :
      chartBasisVecFiber (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          α' i x'
        = (trivializationAt E (TangentSpace I :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
              → Type _) α').symmL ℝ x' (chartModelBasis E i) := by
    change (trivializationAt E (TangentSpace I :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
          → Type _) α').symm x' (chartModelBasis E i)
      = (trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            → Type _) α').symmL ℝ x' (chartModelBasis E i)
    rw [Bundle.Trivialization.symmL_apply]
  have hRHS_symm :
      chartBasisVecFiber (I := I) (M := M)
          (proj (X := M) α') i (proj (X := M) x')
        = (trivializationAt E (TangentSpace I : M → Type _)
            (proj α')).symmL ℝ (proj x') (chartModelBasis E i) := by
    change (trivializationAt E (TangentSpace I : M → Type _) (proj α')).symm
        (proj x') (chartModelBasis E i)
      = (trivializationAt E (TangentSpace I : M → Type _)
          (proj α')).symmL ℝ (proj x') (chartModelBasis E i)
    rw [Bundle.Trivialization.symmL_apply]
  rw [hLHS_symm, hRHS_symm]
  have hSymmL :
      ((trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            → Type _) α').symmL ℝ x' : E →L[ℝ] E)
        = ((trivializationAt E (TangentSpace I : M → Type _)
            (proj α')).symmL ℝ (proj x') : E →L[ℝ] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (b₀ := α') (b := x') hx',
        TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
          (b₀ := proj α') (b := proj x') hprojx'_chartM]
    exact uc_tangentBundleCore_coordChange_agree (I := I) α' x'
      ⟨hx', mem_chart_source H x'⟩
  have hAt := congrArg (fun L : E →L[ℝ] E => L (chartModelBasis E i)) hSymmL
  exact hAt
















omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem chartGramMatrix_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (i j : Fin (Module.finrank ℝ E))
    (hx' : x' ∈ (chartAt H α').source) :
    chartGramMatrix
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' x' i j =
      chartGramMatrix (M := M) g
        (proj (X := M) α') (proj (X := M) x') i j := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' x' i j,
      DifferentialGeometry.Integral.Measure.chartGramMatrix_apply
        (I := I) (M := M) g (proj α') (proj x') i j]
  rw [chartBasisVecFiber_lifted (I := I) (M := M) g α' i x' hx',
      chartBasisVecFiber_lifted (I := I) (M := M) g α' j x' hx']
  rfl









omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
lemma extChartAt_proj_eq
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    extChartAt I α' x' = extChartAt I (proj (X := M) α') (proj (X := M) x') := by
  have hConj := (uc_coverChartAt_extend_conjugacy (I := I) α').1
  have := congrArg (fun f => f x') hConj
  simp only [Function.comp_apply] at this
  have hLS : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  change ((coverChartAt α').extend I) x' = _ at this
  rw [hLS] at this
  exact this

















































omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem chartChristoffel_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k (extChartAt I α' x') =
      chartChristoffel (M := M) g (proj (X := M) α') i j k
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  set y₀ : E := extChartAt I α' x' with hy₀_def
  have hy_eq : extChartAt I α' x' = extChartAt I (proj α') (proj x') :=
    extChartAt_proj_eq (I := I) (M := M) α' x'
  rw [show extChartAt I (proj (X := M) α') (proj (X := M) x') = y₀ from hy_eq.symm]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k y₀,
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_def
        (I := I) (M := M) g (proj α') i j k y₀]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  have hx'_ext : x' ∈ (extChartAt I α').source := by
    rw [extChartAt_source]; exact hx'
  have hsymm_LHS : (extChartAt I α').symm y₀ = x' := by
    rw [hy₀_def]
    exact (extChartAt I α').left_inv hx'_ext
  have hx'_inter : x' ∈ (localSection (M := M) α').source ∩
      (localSection (M := M) α') ⁻¹' (chartAt H (proj α')).source := by
    have hsrc : ((coverChartAt α') :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection α').source ∩
          (localSection α') ⁻¹' (chartAt H (proj α')).source :=
      coverChartAt_source_eq α'
    have hx'_cover : x' ∈ (coverChartAt α').source := hx'
    rw [hsrc] at hx'_cover; exact hx'_cover
  obtain ⟨hx'_LSsrc, hx'_LSchart⟩ := hx'_inter
  have hLS_x' : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  have hproj_x'_chart : proj x' ∈ (chartAt H (proj α')).source := by
    rw [Set.mem_preimage, hLS_x'] at hx'_LSchart
    exact hx'_LSchart
  have hproj_x'_ext : proj x' ∈ (extChartAt I (proj α')).source := by
    rw [extChartAt_source]; exact hproj_x'_chart
  have hsymm_RHS : (extChartAt I (proj α')).symm y₀ = proj x' := by
    rw [hy₀_def, hy_eq]
    exact (extChartAt I (proj α')).left_inv hproj_x'_ext
  rw [hsymm_LHS, hsymm_RHS]
  have hGramMatEq :
      chartGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x' =
        chartGramMatrix (M := M) g (proj α') (proj x') := by
    ext p q
    exact chartGramMatrix_lifted (I := I) (M := M) g α' x' p q hx'
  have hInvGramEq :
      chartInvGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x' k l =
        chartInvGramMatrix (M := M) g (proj α') (proj x') k l := by
    change (chartGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x')⁻¹ k l =
        (chartGramMatrix (M := M) g (proj α') (proj x'))⁻¹ k l
    rw [hGramMatEq]
  rw [hInvGramEq]
  congr 1
  have hGramOnE_eventuallyEq :
      ∀ (p q : Fin (Module.finrank ℝ E)),
        chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' p q
          =ᶠ[𝓝 y₀]
        chartGramOnE (M := M) g (proj α') p q := by
    intro p q
    set ECov : OpenPartialHomeomorph
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
      coverChartAt α' with hECov_def
    have hContCoverInv : ContinuousAt (ECov.extend I).symm y₀ := by
      have : (ECov.extend I) x' = y₀ := by
        rw [hy₀_def]
        rfl
      rw [← this]
      exact OpenPartialHomeomorph.continuousAt_extend_symm (I := I) ECov hx'
    have hOpenCoverSrc : IsOpen ECov.source := ECov.open_source
    have hCoverSrc_mem : (ECov.extend I).symm y₀ ∈ ECov.source := by
      have hy₀_alt : (ECov.extend I) x' = y₀ := by
        rw [hy₀_def]; rfl
      have : (ECov.extend I).symm ((ECov.extend I) x') = x' :=
        OpenPartialHomeomorph.extend_left_inv (I := I) ECov hx'
      rw [hy₀_alt] at this
      rw [this]
      exact hx'
    have hPreCover : (ECov.extend I).symm ⁻¹' ECov.source ∈ 𝓝 y₀ :=
      hContCoverInv (hOpenCoverSrc.mem_nhds hCoverSrc_mem)
    set EBase : OpenPartialHomeomorph M H := chartAt H (proj α') with hEBase_def
    have hContBaseInv : ContinuousAt (EBase.extend I).symm y₀ := by
      have hy₀_base : (EBase.extend I) (proj x') = y₀ := by
        change extChartAt I (proj α') (proj x') = y₀
        exact hy_eq.symm
      rw [← hy₀_base]
      exact OpenPartialHomeomorph.continuousAt_extend_symm (I := I)
        EBase hproj_x'_chart
    have hOpenLSTgt : IsOpen (localSection α').target := (localSection α').open_target
    have hLSTgt_mem : (EBase.extend I).symm y₀ ∈ (localSection α').target := by
      have hy₀_base : (EBase.extend I) (proj x') = y₀ := by
        change extChartAt I (proj α') (proj x') = y₀
        exact hy_eq.symm
      have hinv : (EBase.extend I).symm ((EBase.extend I) (proj x')) = proj x' :=
        OpenPartialHomeomorph.extend_left_inv (I := I) EBase hproj_x'_chart
      rw [hy₀_base] at hinv
      rw [hinv]
      have := (localSection α').map_source hx'_LSsrc
      rwa [hLS_x'] at this
    have hPreBase : (EBase.extend I).symm ⁻¹' (localSection α').target ∈ 𝓝 y₀ :=
      hContBaseInv (hOpenLSTgt.mem_nhds hLSTgt_mem)
    filter_upwards [hPreCover, hPreBase] with y hyCover hyBase
    change chartGramMatrix
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' ((extChartAt I α').symm y) p q
        = chartGramMatrix (M := M) g (proj α')
            ((extChartAt I (proj α')).symm y) p q
    have hConjSymm := (uc_coverChartAt_extend_conjugacy (I := I) α').2
    have hSymmDecomp : (extChartAt I α').symm y =
        (localSection α').symm ((EBase.extend I).symm y) := by
      change (ECov.extend I).symm y = (localSection α').symm ((EBase.extend I).symm y)
      have := congrArg (fun f => f y) hConjSymm
      simpa [Function.comp_apply] using this
    have hsrc_cover_y : (extChartAt I α').symm y ∈ (chartAt H α').source := by
      change (ECov.extend I).symm y ∈ ECov.source
      exact hyCover
    rw [chartGramMatrix_lifted (I := I) (M := M) g α'
          ((extChartAt I α').symm y) p q hsrc_cover_y]
    have hProj_eq : proj ((extChartAt I α').symm y)
        = (extChartAt I (proj α')).symm y := by
      rw [hSymmDecomp]
      have hproj_eq_LS :
          proj ((localSection α').symm ((EBase.extend I).symm y))
            = (localSection α')
                ((localSection α').symm ((EBase.extend I).symm y)) := by
        have := congrArg
            (fun f => f ((localSection α').symm ((EBase.extend I).symm y)))
            (proj_eq_localSection α')
        simpa using this
      rw [hproj_eq_LS, (localSection α').right_inv hyBase]
      rfl
    rw [hProj_eq]
  have hP_ij_lj :
      partialDeriv (E := E) i
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' l j) y₀
        = partialDeriv (E := E) i
            (chartGramOnE (M := M) g (proj α') l j) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' l j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E i)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') l j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E i)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq l j)]
  have hP_ji_li :
      partialDeriv (E := E) j
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' l i) y₀
        = partialDeriv (E := E) j
            (chartGramOnE (M := M) g (proj α') l i) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' l i) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E j)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') l i) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E j)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq l i)]
  have hP_lij :
      partialDeriv (E := E) l
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' i j) y₀
        = partialDeriv (E := E) l
            (chartGramOnE (M := M) g (proj α') i j) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' i j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E l)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') i j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E l)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq i j)]
  rw [hP_ij_lj, hP_ji_li, hP_lij]



















omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem chartChristoffelContraction_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source) (v w : E) :
    DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' v w (extChartAt I α' x') =
      DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction
        (M := M) g (proj (X := M) α') v w
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  rw [DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' v w (extChartAt I α' x'),
      DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_def
        (I := I) (M := M) g (proj α') v w
        (extChartAt I (proj (X := M) α') (proj (X := M) x'))]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [chartChristoffel_lifted (I := I) (M := M) g α' x' hx' i j k]
















omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
lemma chartChristoffel_lifted_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i j k : Fin (Module.finrank ℝ E)) :
    (fun y => chartChristoffel
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k y)
      =ᶠ[𝓝 (extChartAt I α' x')]
    (fun y => chartChristoffel (M := M) g (proj (X := M) α') i j k y) := by
  classical
  set y₀ : E := extChartAt I α' x' with hy₀_def
  have hx'_ext : x' ∈ (extChartAt I α').source := by
    rw [extChartAt_source]; exact hx'
  have hContInv : ContinuousAt (extChartAt I α').symm y₀ := by
    have hy₀_alt : (extChartAt I α') x' = y₀ := by rw [hy₀_def]
    rw [← hy₀_alt]
    exact continuousAt_extChartAt_symm' (I := I) (x := α') hx'_ext
  have hOpenSrc : IsOpen (chartAt H α').source :=
    (chartAt H α').open_source
  have hSrc_mem : (extChartAt I α').symm y₀ ∈ (chartAt H α').source := by
    have hinv : (extChartAt I α').symm ((extChartAt I α') x') = x' :=
      (extChartAt I α').left_inv hx'_ext
    have hy₀_alt : (extChartAt I α') x' = y₀ := by rw [hy₀_def]
    rw [← hy₀_alt, hinv]; exact hx'
  have hPreImage :
      (extChartAt I α').symm ⁻¹' (chartAt H α').source ∈ 𝓝 y₀ :=
    hContInv (hOpenSrc.mem_nhds hSrc_mem)
  have hTargetOpen : IsOpen (extChartAt I α').target :=
    isOpen_extChartAt_target (I := I) α'
  have hy₀_target : y₀ ∈ (extChartAt I α').target := by
    rw [hy₀_def]; exact (extChartAt I α').map_source hx'_ext
  have hTgtMem : (extChartAt I α').target ∈ 𝓝 y₀ :=
    hTargetOpen.mem_nhds hy₀_target
  filter_upwards [hPreImage, hTgtMem] with y hyPre hyTgt
  set x'_y :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M :=
    (extChartAt I α').symm y with hx'_y_def
  have hx'_y_src : x'_y ∈ (chartAt H α').source := hyPre
  have hExt_x'_y : extChartAt I α' x'_y = y := by
    rw [hx'_y_def]; exact (extChartAt I α').right_inv hyTgt
  have hLifted := chartChristoffel_lifted (I := I) (M := M) g α' x'_y hx'_y_src i j k
  have hExt_proj_x'_y :
      extChartAt I (proj (X := M) α') (proj (X := M) x'_y) =
        extChartAt I α' x'_y :=
    (extChartAt_proj_eq (I := I) (M := M) α' x'_y).symm
  rw [hExt_x'_y, hExt_proj_x'_y, hExt_x'_y] at hLifted
  exact hLifted















omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem chartRiemannTensor_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannTensor
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k l (extChartAt I α' x') =
      chartRiemannTensor (M := M) g (proj (X := M) α') i j k l
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  set y₀ : E := extChartAt I α' x' with hy₀_def
  have hy_eq : extChartAt I α' x' = extChartAt I (proj α') (proj x') :=
    extChartAt_proj_eq (I := I) (M := M) α' x'
  rw [show extChartAt I (proj (X := M) α') (proj (X := M) x') = y₀ from hy_eq.symm]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k l y₀,
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor_def
        (I := I) (M := M) g (proj α') i j k l y₀]
  have hChristAt : ∀ (a b c : Fin (Module.finrank ℝ E)),
      chartChristoffel
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' a b c y₀
        = chartChristoffel (M := M) g (proj α') a b c y₀ := by
    intro a b c
    have h := chartChristoffel_lifted (I := I) (M := M) g α' x' hx' a b c
    rw [show extChartAt I α' x' = y₀ from rfl,
        show extChartAt I (proj (X := M) α') (proj (X := M) x') = y₀ from hy_eq.symm] at h
    exact h
  have hChristEvEq : ∀ (a b c : Fin (Module.finrank ℝ E)),
      (fun y => chartChristoffel
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' a b c y)
        =ᶠ[𝓝 y₀]
      (fun y => chartChristoffel (M := M) g (proj α') a b c y) := by
    intro a b c
    have := chartChristoffel_lifted_eventuallyEq (I := I) (M := M) g α' x' hx' a b c
    exact this
  have hPartialDeriv : ∀ (n : Fin (Module.finrank ℝ E)) (a b c : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) n
          (chartChristoffel
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' a b c) y₀
        = partialDeriv (E := E) n
            (chartChristoffel (M := M) g (proj α') a b c) y₀ := by
    intro n a b c
    change fderiv ℝ
        (chartChristoffel
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' a b c) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E n)
      = fderiv ℝ
          (chartChristoffel (M := M) g (proj α') a b c) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E n)
    rw [Filter.EventuallyEq.fderiv_eq (hChristEvEq a b c)]
  rw [hPartialDeriv j i k l, hPartialDeriv k i j l]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [hChristAt j m l, hChristAt i k m, hChristAt k m l, hChristAt i j m]












omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem chartRicciTensor_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i k : Fin (Module.finrank ℝ E)) :
    chartRicciTensor
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i k (extChartAt I α' x') =
      chartRicciTensor (M := M) g (proj (X := M) α') i k
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i k (extChartAt I α' x'),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor_def
        (I := I) (M := M) g (proj α') i k
        (extChartAt I (proj (X := M) α') (proj (X := M) x'))]
  refine Finset.sum_congr rfl ?_
  intro j _
  exact chartRiemannTensor_lifted (I := I) (M := M) g α' x' hx' i j k j

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
