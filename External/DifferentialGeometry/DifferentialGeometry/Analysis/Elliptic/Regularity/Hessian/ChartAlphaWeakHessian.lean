import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PerChart
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.TensorChartSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaWeakRaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private noncomputable def chartPushedPouFun
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
    (I := I) (M := M) (chartAtlasPOU I M) α
    ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)

private lemma chartPushedPouFun_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedPouFun (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartPushedPouFun
  exact (chartH2NonSmoothPOUWitness_of_laplacianDomain
    (I := I) (M := M) g hu_h α).memWkp_two

private lemma chartPushedPouFun_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedPouFun (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := chartPushedPouFun_memWkp_two_two (I := I) (M := M) g α hu_h
  exact h.memW1p

noncomputable def chosenChartFirstWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 j
    (chartPushedPouFun (I := I) (M := M) g α u_h)
    (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chosenChartFirstWeakPartial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (j : Fin (Module.finrank ℝ E)) :
    chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h j =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j
        (chartPushedPouFun (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α) := rfl

theorem chosenChartFirstWeakPartial_isWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (j : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h j)
      (chartPushedPouFun (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenChartFirstWeakPartial
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
    (chartPushedPouFun_memW1p (I := I) (M := M) g α hu_h) j

theorem chosenChartFirstWeakPartial_memLp_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp (chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h j) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenChartFirstWeakPartial
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    (chartPushedPouFun_memW1p (I := I) (M := M) g α hu_h) j

theorem chosenChartFirstWeakPartial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (j : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h j) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := chosenChartFirstWeakPartial_memLp_chartTarget
    (I := I) (M := M) g α hu_h j
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

noncomputable def chosenChartSecondWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 k
      (chartPushedPouFun (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chosenChartSecondWeakPartial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) :
    chosenChartSecondWeakPartial (I := I) (M := M) g α hu_h k l =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushedPouFun (I := I) (M := M) g α u_h)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) := rfl

theorem chosenChartSecondWeakPartial_memLp_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) :
    MemLp (chosenChartSecondWeakPartial (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_memWkp_2 := chartPushedPouFun_memWkp_two_two (I := I) (M := M) g α hu_h
  have h_inner_memW1p : DeGiorgi.MemW1p 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushedPouFun (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_step := h_memWkp_2.chosenWeakPartial_mem k
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h_step
    exact h_step
  unfold chosenChartSecondWeakPartial
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    h_inner_memW1p l

theorem chosenChartSecondWeakPartial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chosenChartSecondWeakPartial (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := chosenChartSecondWeakPartial_memLp_chartTarget
    (I := I) (M := M) g α hu_h k l
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

noncomputable def chartChristoffelCorrectionWeak
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y) *
      chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h m y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartChristoffelCorrectionWeak_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartChristoffelCorrectionWeak (I := I) (M := M) g α hu_h k l y =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y) *
          chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h m y := rfl

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartChristoffel_toE_symm_continuousOn_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun y : EuclN => chartChristoffel (I := I) g α k l m
        ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.continuous
  have h_int_eq_target : interior (extChartAt I α).target = (extChartAt I α).target :=
    (isOpen_extChartAt_target (I := I) α).interior_eq
  have h_chris_cont : ContinuousOn (chartChristoffel (I := I) g α k l m)
      (extChartAt I α).target := by
    rw [← h_int_eq_target]
    exact (chartChristoffel_contDiffOn_interior (I := I) g α k l m).continuousOn
  have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
    toEuclidean_symm_mem_target (I := I) hy
  exact h_chris_cont.comp h_toE_cont.continuousOn h_maps

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartChristoffel_toE_symm_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      |chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y)| ≤ C := by
  classical
  by_cases hKne : K.Nonempty
  · have h_cont_on_K : ContinuousOn (fun y : EuclN =>
        chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y)) K :=
      (chartChristoffel_toE_symm_continuousOn_chartTargetEuclid
        (I := I) (M := M) g α k l m).mono hK_in
    have h_abs_cont_on_K : ContinuousOn (fun y : EuclN =>
        |chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y)|) K :=
      h_cont_on_K.abs
    obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
      hK_compact.exists_isMaxOn hKne h_abs_cont_on_K
    refine ⟨|chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y₀)|,
      abs_nonneg _, ?_⟩
    intro y hy
    exact hy₀_max hy
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    rw [hKne] at hy
    exact absurd hy (Set.notMem_empty y)

private lemma chartChristoffelCorrectionWeak_summand_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l m : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun y : EuclN =>
        chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y) *
          chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h m y) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  have h_partial_memLp : MemLp
      (chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h m) 2
      ((volume : Measure EuclN).restrict K) :=
    chosenChartFirstWeakPartial_locally_memLp (I := I) (M := M) g α hu_h m
      hK_compact hK_in
  obtain ⟨C, hC_nn, hC_bd⟩ := chartChristoffel_toE_symm_bounded_on_compact
    (I := I) (M := M) g α k l m hK_compact hK_in
  have h_chris_contOn_K : ContinuousOn (fun y : EuclN =>
      chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y)) K :=
    (chartChristoffel_toE_symm_continuousOn_chartTargetEuclid
      (I := I) (M := M) g α k l m).mono hK_in
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_chris_aemeas :
      AEStronglyMeasurable (fun y : EuclN =>
        chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y))
        ((volume : Measure EuclN).restrict K) := by
    refine ContinuousOn.aestronglyMeasurable_of_isCompact h_chris_contOn_K
      hK_compact hK_meas
  refine MemLp.of_le_mul (c := C) h_partial_memLp
    (h_chris_aemeas.mul (h_partial_memLp.1)) ?_
  refine (MeasureTheory.ae_restrict_iff' hK_meas).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC_bd y hy) (abs_nonneg _)

theorem chartChristoffelCorrectionWeak_memLp_chartTarget_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chartChristoffelCorrectionWeak (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  unfold chartChristoffelCorrectionWeak
  exact MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun m _ => chartChristoffelCorrectionWeak_summand_memLp
      (I := I) (M := M) g α hu_h k l m hK_compact hK_in)

noncomputable def chartTensorWeakHessianRaw
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chosenChartSecondWeakPartial (I := I) (M := M) g α hu_h k l y -
    chartChristoffelCorrectionWeak (I := I) (M := M) g α hu_h k l y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartTensorWeakHessianRaw_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y =
      chosenChartSecondWeakPartial (I := I) (M := M) g α hu_h k l y -
        chartChristoffelCorrectionWeak (I := I) (M := M) g α hu_h k l y := rfl

theorem chartTensorWeakHessianRaw_memLp_chartTarget_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict K) := by
  unfold chartTensorWeakHessianRaw
  exact (chosenChartSecondWeakPartial_locally_memLp
    (I := I) (M := M) g α hu_h k l hK_compact hK_in).sub
    (chartChristoffelCorrectionWeak_memLp_chartTarget_compact
      (I := I) (M := M) g α hu_h k l hK_compact hK_in)

end HessianChartAlphaWeakRaw
end Laplacian
end Analysis
end DifferentialGeometry

end
