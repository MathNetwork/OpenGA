import DifferentialGeometry.Geometry.Curvature.OpenSubtypeNaturality
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Tensor.RSTensor.Coordinates.OpensRestrict

set_option autoImplicit false








noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open Bundle Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
    in
private theorem chartBasisVec_open
    (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (a x : U)
    (hx : (x : M) ∈ (chartAt H (a : M)).source)
    (i : Fin (Module.finrank Real E)) :
    chartBasisVecFiber (I := I) a i x =
      chartBasisVecFiber (I := I) (a : M) i (x : M) := by
  letI : Nonempty U := ⟨a⟩
  have hxU : x ∈ (chartAt H a).source := by
    rw [TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  change
    (trivializationAt E (TangentSpace I (M := U)) a).symmL Real x
        (chartModelBasis E i) =
      (trivializationAt E (TangentSpace I (M := M)) (a : M)).symmL Real (x : M)
        (chartModelBasis E i)
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) hxU,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hx,
    tangentCoordChange_opens (I := I) a x x hx]
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
    in
private theorem chartGram_open
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (a x : U)
    (hx : (x : M) ∈ (chartAt H (a : M)).source)
    (i j : Fin (Module.finrank Real E)) :
    chartGramMatrix (I := I) (g.restrictOpen (I := I) U) a x i j =
      chartGramMatrix (I := I) g (a : M) (x : M) i j := by
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    SmoothRiemannianMetric.restrictOpen_inner,
    chartBasisVec_open (I := I) U a x hx i,
    chartBasisVec_open (I := I) U a x hx j]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
    in
private theorem chartGramOnE_open [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (a : U)
    (i j : Fin (Module.finrank Real E)) :
    chartGramOnE (I := I) (g.restrictOpen (I := I) U) a i j
        =ᶠ[nhds (extChartAt I a a)]
      chartGramOnE (I := I) g (a : M) i j := by
  letI : Nonempty U := ⟨a⟩
  filter_upwards [extChartAt_target_mem_nhds (I := I) a] with y hy
  change chartGramMatrix (I := I) (g.restrictOpen (I := I) U) a
      ((extChartAt I a).symm y) i j =
    chartGramMatrix (I := I) g (a : M)
      ((extChartAt I (a : M)).symm y) i j
  have hzU : (extChartAt I a).symm y ∈ (extChartAt I a).source :=
    (extChartAt I a).map_target hy
  have hzM : (((extChartAt I a).symm y : U) : M) ∈
      (chartAt H (a : M)).source := by
    rw [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hzU
    exact hzU
  have hval : (((extChartAt I a).symm y : U) : M) =
      (extChartAt I (a : M)).symm y := by
    have hyTarget : I.symm y ∈ (chartAt H a).target := by
      have hy' : (∃ z, I z = y) ∧ I.symm y ∈ (chartAt H a).target := by
        simpa [extChartAt] using hy
      exact hy'.2
    change ((chartAt H a).symm (I.symm y) : U) =
      (chartAt H (a : M)).symm (I.symm y)
    rw [TopologicalSpace.Opens.chartAt_eq] at hyTarget ⊢
    exact OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ hyTarget
  rw [← hval]
  exact chartGram_open (I := I) g U a ((extChartAt I a).symm y) hzM i j



omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem christoffel_open [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (a : U)
    (i j k : Fin (Module.finrank Real E)) :
    chartChristoffel (I := I) (g.restrictOpen (I := I) U) a i j k
        (extChartAt I a a) =
      chartChristoffel (I := I) g (a : M) i j k
        (extChartAt I (a : M) (a : M)) := by
  classical
  letI : Nonempty U := ⟨a⟩
  set y₀ : E := extChartAt I a a with hy₀
  have hy_eq : extChartAt I a a = extChartAt I (a : M) (a : M) := rfl
  rw [show extChartAt I (a : M) (a : M) = y₀ from hy_eq.symm.trans hy₀]
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  have hsymmU : (extChartAt I a).symm y₀ = a := by
    rw [hy₀]
    exact (extChartAt I a).left_inv (mem_extChartAt_source a)
  have hsymmM : (extChartAt I (a : M)).symm y₀ = (a : M) := by
    rw [hy₀, hy_eq]
    exact (extChartAt I (a : M)).left_inv (mem_extChartAt_source (a : M))
  rw [hsymmU, hsymmM]
  have hGramMatEq :
      chartGramMatrix (I := I) (g.restrictOpen (I := I) U) a a =
        chartGramMatrix (I := I) g (a : M) (a : M) := by
    ext p q
    exact chartGram_open (I := I) g U a a (mem_chart_source H (a : M)) p q
  have hInvGramEq :
      chartInvGramMatrix (I := I) (g.restrictOpen (I := I) U) a a k l =
        chartInvGramMatrix (I := I) g (a : M) (a : M) k l := by
    change (chartGramMatrix (I := I) (g.restrictOpen (I := I) U) a a)⁻¹ k l =
      (chartGramMatrix (I := I) g (a : M) (a : M))⁻¹ k l
    rw [hGramMatEq]
  rw [hInvGramEq]
  congr 1
  have hP_ij_lj :
      partialDeriv (E := E) i
          (chartGramOnE (I := I) (g.restrictOpen (I := I) U) a l j) y₀ =
        partialDeriv (E := E) i (chartGramOnE (I := I) g (a : M) l j) y₀ := by
    change fderiv Real
        (chartGramOnE (I := I) (g.restrictOpen (I := I) U) a l j) y₀
          (chartModelBasis E i) =
      fderiv Real (chartGramOnE (I := I) g (a : M) l j) y₀
        (chartModelBasis E i)
    rw [(chartGramOnE_open (I := I) g U a l j).fderiv_eq]
  have hP_ji_li :
      partialDeriv (E := E) j
          (chartGramOnE (I := I) (g.restrictOpen (I := I) U) a l i) y₀ =
        partialDeriv (E := E) j (chartGramOnE (I := I) g (a : M) l i) y₀ := by
    change fderiv Real
        (chartGramOnE (I := I) (g.restrictOpen (I := I) U) a l i) y₀
          (chartModelBasis E j) =
      fderiv Real (chartGramOnE (I := I) g (a : M) l i) y₀
        (chartModelBasis E j)
    rw [(chartGramOnE_open (I := I) g U a l i).fderiv_eq]
  have hP_lij :
      partialDeriv (E := E) l
          (chartGramOnE (I := I) (g.restrictOpen (I := I) U) a i j) y₀ =
        partialDeriv (E := E) l (chartGramOnE (I := I) g (a : M) i j) y₀ := by
    change fderiv Real
        (chartGramOnE (I := I) (g.restrictOpen (I := I) U) a i j) y₀
          (chartModelBasis E l) =
      fderiv Real (chartGramOnE (I := I) g (a : M) i j) y₀
        (chartModelBasis E l)
    rw [(chartGramOnE_open (I := I) g U a i j).fderiv_eq]
  rw [hP_ij_lj, hP_ji_li, hP_lij]



omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem contr_open [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (a : U) (v w : E) :
    chartChristoffelContraction (I := I) (g.restrictOpen (I := I) U) a v w
        (extChartAt I a a) =
      chartChristoffelContraction (I := I) g (a : M) v w
        (extChartAt I (a : M) (a : M)) := by
  classical
  rw [chartChristoffelContraction_def, chartChristoffelContraction_def]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [christoffel_open (I := I) g U a i j k]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem geodesicEq_open_iff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (gamma : Real → U) (t : Real) :
    HasGeodesicEquationAt (I := I) (g.restrictOpen (I := I) U) gamma t ↔
      HasGeodesicEquationAt (I := I) g (fun s => (gamma s : M)) t := by
  have hcurve : (fun s => extChartAt I (gamma t) (gamma s)) =
      (fun s => extChartAt I (gamma t : M) (gamma s : M)) := rfl
  unfold HasGeodesicEquationAt chartLocalCurve
  rw [hcurve]
  constructor
  · rintro ⟨v, a, hv, hev, ha, hid⟩
    refine ⟨v, a, by simpa using hv, by simpa using hev, by simpa using ha, ?_⟩
    calc
      a + chartChristoffelContraction (I := I) g (gamma t : M) v v
            (extChartAt I (gamma t : M) (gamma t : M)) =
          a + chartChristoffelContraction (I := I)
            (g.restrictOpen (I := I) U) (gamma t) v v
              (extChartAt I (gamma t) (gamma t)) :=
        congrArg (fun z => a + z)
          (contr_open (I := I) g U (gamma t) v v).symm
      _ = 0 := hid
  · rintro ⟨v, a, hv, hev, ha, hid⟩
    refine ⟨v, a, by simpa using hv, by simpa using hev, by simpa using ha, ?_⟩
    calc
      a + chartChristoffelContraction (I := I)
            (g.restrictOpen (I := I) U) (gamma t) v v
              (extChartAt I (gamma t) (gamma t)) =
          a + chartChristoffelContraction (I := I) g (gamma t : M) v v
            (extChartAt I (gamma t : M) (gamma t : M)) :=
        congrArg (fun z => a + z) (contr_open (I := I) g U (gamma t) v v)
      _ = 0 := hid



omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem geodesicOn_open_iff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (gamma : Real → U) (s : Set Real) :
    IsGeodesicOn (I := I) (g.restrictOpen (I := I) U) gamma s ↔
      IsGeodesicOn (I := I) g (fun t => (gamma t : M)) s := by
  constructor
  · intro hgamma t ht
    exact (geodesicEq_open_iff (I := I) g U gamma t).mp (hgamma t ht)
  · intro hgamma t ht
    exact (geodesicEq_open_iff (I := I) g U gamma t).mpr (hgamma t ht)



omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem geodesic_open_iff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U] (gamma : Real → U) :
    IsGeodesic (I := I) (g.restrictOpen (I := I) U) gamma ↔
      IsGeodesic (I := I) g (fun t => (gamma t : M)) := by
  constructor
  · intro hgamma t
    exact (geodesicEq_open_iff (I := I) g U gamma t).mp (hgamma t)
  · intro hgamma t
    exact (geodesicEq_open_iff (I := I) g U gamma t).mpr (hgamma t)

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
