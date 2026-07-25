import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PerChart
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianLpClass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def chartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) : EuclN → ℝ :=
  chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
    ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)

private lemma chartPushedU_memWkp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := laplacianDomain_memWkpChart_two_unconditional (I := I) (M := M) g hu_h
  exact h.1 α

private lemma chartPushedU_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DeGiorgi.MemW1p 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedU_memWkp_two (I := I) (M := M) g α hu_h).memW1p

private lemma chosenInner_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := chartPushedU_memWkp_two (I := I) (M := M) g α hu_h
  have hstep := h.chosenWeakPartial_mem i
  rw [MemWkp.one_iff_memW1p] at hstep
  exact hstep

noncomputable def laplacianDomainHessianChart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
    (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in

private lemma laplacianDomainHessianChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chartPushedU (I := I) (M := M) g α u_h)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) := rfl

theorem laplacianDomainHessianChart_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [laplacianDomainHessianChart_def]
  exact chosenWeakPartial'_memLp_of_mem
    (chosenInner_memW1p (I := I) (M := M) g α hu_h i) j

omit [NeZero (Module.finrank ℝ E)] in

private lemma chartPushedU_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chartPushedU (I := I) (M := M) g α u_h
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  refine (ae_restrict_iff' hV_open.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  unfold chartPushedU
  exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
    α _ hy.1 hy.2

private lemma chartPushedU_memW1p_sdiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DeGiorgi.MemW1p 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hV_subset : V ⊆ chartTargetEuclid (I := I) (M := M) α := Set.diff_subset
  have hu : DeGiorgi.MemW1p 2 (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedU_memW1p (I := I) (M := M) g α hu_h
  refine ⟨?_, ?_⟩
  · exact hu.1.mono_measure (Measure.restrict_mono_set volume hV_subset)
  · intro k
    obtain ⟨gk, hgk_memLp, hgk_weak⟩ := hu.2 k
    refine ⟨gk, ?_, ?_⟩
    · exact hgk_memLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
    · exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset hgk_weak

omit [NeZero (Module.finrank ℝ E)] in

private lemma chosenWeakPartial_chartPushedU_ae_zero_sdiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hae_zero :
      chartPushedU (I := I) (M := M) g α u_h
        =ᵐ[(volume : Measure EuclN).restrict V]
        (fun _ : EuclN => (0 : ℝ)) :=
    chartPushedU_ae_zero_off_support (I := I) (M := M) g α u_h
  exact chosenWeakPartial'_ae_zero_of_ae_zero
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open
    hae_zero i

private lemma chosenWeakPartial_chartPushedU_restrict_ae_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hV_subset : V ⊆ chartTargetEuclid (I := I) (M := M) α := Set.diff_subset

  have hu_full := chartPushedU_memW1p (I := I) (M := M) g α hu_h
  have hu_sdiff := chartPushedU_memW1p_sdiff (I := I) (M := M) g α hu_h
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_full i
  have h_partial_Ω_on_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      (chartPushedU (I := I) (M := M) g α u_h) V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset h_partial_Ω
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h) V)
      (chartPushedU (I := I) (M := M) g α u_h) V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_sdiff i

  have hmemLp_Ω : MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict V) := by
    have hLp := chosenWeakPartial'_memLp_of_mem hu_full i
    exact hLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
  have h_loc_Ω : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      ((volume : Measure EuclN).restrict V) :=
    hmemLp_Ω.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hmemLp_V : MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h) V) 2
      ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartial'_memLp_of_mem hu_sdiff i
  have h_loc_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h) V)
      ((volume : Measure EuclN).restrict V) :=
    hmemLp_V.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open h_partial_Ω_on_V h_partial_V
    h_loc_Ω h_loc_V

private lemma chosenWeakPartial_chartPushedU_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  exact (chosenWeakPartial_chartPushedU_restrict_ae_eq
      (I := I) (M := M) g α hu_h i).trans
    (chosenWeakPartial_chartPushedU_ae_zero_sdiff
      (I := I) (M := M) g α hu_h i)

private lemma chosenWeakPartial_outer_sdiff_ae_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chartPushedU (I := I) (M := M) g α u_h)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed

  exact chosenWeakPartial'_ae_zero_of_ae_zero
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open
    (chosenWeakPartial_chartPushedU_ae_zero_off_support
      (I := I) (M := M) g α hu_h i) j

private lemma chosenInner_sdiff_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) := by
  have h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) := by

    classical
    set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
      chartImagePOUTsupport (I := I) (M := M) α with hV_def
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    have hΩ_open : IsOpen Ω :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
    have hV_subset : V ⊆ Ω := Set.diff_subset

    refine ⟨chartPushedU_memW1p_sdiff (I := I) (M := M) g α hu_h, ?_⟩
    intro k

    rw [MemWkp.one_iff_memW1p]
    have h_inner_Ω := chosenInner_memW1p (I := I) (M := M) g α hu_h k
    have h_inner_V : DeGiorgi.MemW1p 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (chartPushedU (I := I) (M := M) g α u_h) Ω) V := by
      refine ⟨?_, ?_⟩
      · exact h_inner_Ω.1.mono_measure (Measure.restrict_mono_set volume hV_subset)
      · intro j
        obtain ⟨gj, hgj_memLp, hgj_weak⟩ := h_inner_Ω.2 j
        refine ⟨gj, ?_, ?_⟩
        · exact hgj_memLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
        · exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset hgj_weak

    have hae := chosenWeakPartial_chartPushedU_restrict_ae_eq
      (I := I) (M := M) g α hu_h k
    exact (MemW1p_congr_ae
      (d := Module.finrank ℝ E) hV_open hae).mp h_inner_V
  have hstep := h.chosenWeakPartial_mem i
  rw [MemWkp.one_iff_memW1p] at hstep
  exact hstep

lemma laplacianDomainHessianChart_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hV_subset : V ⊆ Ω := Set.diff_subset

  set inner_Ω := chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
    (chartPushedU (I := I) (M := M) g α u_h) Ω with hinner_Ω_def
  set FΩ := chosenWeakPartial' (d := Module.finrank ℝ E) 2 j inner_Ω Ω
    with hFΩ_def
  set Fmid := chosenWeakPartial' (d := Module.finrank ℝ E) 2 j inner_Ω V
    with hFmid_def

  have h_outer_V_zero : Fmid =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial_outer_sdiff_ae_zero (I := I) (M := M) g α hu_h i j

  have h_FΩ_partial_on_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E)
      j FΩ inner_Ω V := by
    have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E)
        j FΩ inner_Ω Ω :=
      chosenWeakPartial'_isWeakPartial_of_mem
        (chosenInner_memW1p (I := I) (M := M) g α hu_h i) j
    exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset h_partial_Ω

  have h_inner_Ω_W1p_V : DeGiorgi.MemW1p 2 inner_Ω V := by
    have h_inner_Ω_W1p_Ω := chosenInner_memW1p (I := I) (M := M) g α hu_h i
    refine ⟨?_, ?_⟩
    · exact h_inner_Ω_W1p_Ω.1.mono_measure (Measure.restrict_mono_set volume hV_subset)
    · intro k
      obtain ⟨gk, hgk_memLp, hgk_weak⟩ := h_inner_Ω_W1p_Ω.2 k
      refine ⟨gk, ?_, ?_⟩
      · exact hgk_memLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset hgk_weak
  have h_Fmid_partial_on_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E)
      j Fmid inner_Ω V :=
    chosenWeakPartial'_isWeakPartial_of_mem h_inner_Ω_W1p_V j

  have h_FΩ_Lp_Ω : MemLp FΩ 2 ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartial'_memLp_of_mem
      (chosenInner_memW1p (I := I) (M := M) g α hu_h i) j
  have h_FΩ_Lp_V : MemLp FΩ 2 ((volume : Measure EuclN).restrict V) :=
    h_FΩ_Lp_Ω.mono_measure (Measure.restrict_mono_set volume hV_subset)
  have h_FΩ_loc : LocallyIntegrable FΩ ((volume : Measure EuclN).restrict V) :=
    h_FΩ_Lp_V.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_Fmid_Lp_V : MemLp Fmid 2 ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartial'_memLp_of_mem h_inner_Ω_W1p_V j
  have h_Fmid_loc : LocallyIntegrable Fmid ((volume : Measure EuclN).restrict V) :=
    h_Fmid_Lp_V.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

  have hae_FΩ_Fmid : FΩ =ᵐ[(volume : Measure EuclN).restrict V] Fmid :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open
      h_FΩ_partial_on_V h_Fmid_partial_on_V h_FΩ_loc h_Fmid_loc

  change FΩ =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ))
  exact hae_FΩ_Fmid.trans h_outer_V_zero

noncomputable def laplacianDomainHessFrobeniusSqChart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) : EuclN → ℝ :=
  fun y => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  invGramOnEuclid (I := I) g α i k y *
                    invGramOnEuclid (I := I) g α j l y *
                    laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
                    laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma laplacianDomainHessFrobeniusSqChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) :
    laplacianDomainHessFrobeniusSqChart (I := I) (M := M) g α hu_h y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := rfl

noncomputable def chartCutoffα (α : M) : EuclN → ℝ :=
  Classical.choose
    (DifferentialGeometry.Analysis.Sobolev.Chart.exists_chartCutoff
      (I := I) (M := M) α).choose_spec

lemma chartCutoffα_spec (α : M) :
    let cutoff := chartCutoffα (I := I) (M := M) α
    let δ := (DifferentialGeometry.Analysis.Sobolev.Chart.exists_chartCutoff
      (I := I) (M := M) α).choose
    0 < δ ∧
      Metric.cthickening δ (chartImagePOUTsupport (I := I) (M := M) α) ⊆
        chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) cutoff ∧
      HasCompactSupport cutoff ∧
      Set.range cutoff ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Metric.cthickening δ
        (chartImagePOUTsupport (I := I) (M := M) α), cutoff y = 1) ∧
      tsupport cutoff ⊆ chartTargetEuclid (I := I) (M := M) α :=
  (DifferentialGeometry.Analysis.Sobolev.Chart.exists_chartCutoff
    (I := I) (M := M) α).choose_spec.choose_spec

lemma chartCutoffα_smooth (α : M) :
    ContDiff ℝ (⊤ : ℕ∞) (chartCutoffα (I := I) (M := M) α) :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.1

lemma chartCutoffα_compactSupport (α : M) :
    HasCompactSupport (chartCutoffα (I := I) (M := M) α) :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.2.1

lemma chartCutoffα_range (α : M) :
    Set.range (chartCutoffα (I := I) (M := M) α) ⊆ Set.Icc (0 : ℝ) 1 :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.2.2.1

lemma chartCutoffα_eq_one_on_K (α : M) :
    ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
      chartCutoffα (I := I) (M := M) α y = 1 := by
  intro y hy
  have hone := (chartCutoffα_spec (I := I) (M := M) α).2.2.2.2.2.1
  apply hone y
  exact Metric.self_subset_cthickening _ hy

lemma chartCutoffα_tsupport (α : M) :
    tsupport (chartCutoffα (I := I) (M := M) α) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.2.2.2.2

lemma abs_chartCutoffα_le (α : M) (y : EuclN) :
    |chartCutoffα (I := I) (M := M) α y| ≤ 1 := by
  have hrange := chartCutoffα_range (I := I) (M := M) α
  have hy : chartCutoffα (I := I) (M := M) α y ∈ Set.Icc (0 : ℝ) 1 :=
    hrange (Set.mem_range_self y)
  rw [abs_of_nonneg hy.1]
  exact hy.2

noncomputable def cutoffInvGram
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartCutoffα (I := I) (M := M) α y *
    invGramOnEuclid (I := I) g α i j y

lemma cutoffInvGram_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    cutoffInvGram (I := I) (M := M) g α i j y =
      chartCutoffα (I := I) (M := M) α y *
        invGramOnEuclid (I := I) g α i j y := rfl

lemma cutoffInvGram_bounded
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN,
      |cutoffInvGram (I := I) (M := M) g α i j y| ≤ C := by
  classical

  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α

  have hη_bdd : ∀ y : EuclN, |η y| ≤ 1 := abs_chartCutoffα_le (I := I) (M := M) α

  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffInvGram (I := I) (M := M) g α i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffInvGram
    rw [hη_zero, zero_mul]

  have hG_cont_on : ContinuousOn (invGramOnEuclid (I := I) g α i j) Ω :=
    (invGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn

  by_cases hKη_ne : Kη.Nonempty
  · have hG_cont_on_Kη : ContinuousOn (invGramOnEuclid (I := I) g α i j) Kη :=
      hG_cont_on.mono hKη_sub_Ω
    have hG_norm_cont : ContinuousOn
        (fun y : EuclN => ‖invGramOnEuclid (I := I) g α i j y‖) Kη :=
      hG_cont_on_Kη.norm
    obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
      hKη_compact.exists_isMaxOn hKη_ne hG_norm_cont
    set C := ‖invGramOnEuclid (I := I) g α i j y₀‖ with hC_def
    have hC_nn : 0 ≤ C := norm_nonneg _
    refine ⟨C, hC_nn, ?_⟩
    intro y
    by_cases hyK : y ∈ Kη
    · have h1 : |cutoffInvGram (I := I) (M := M) g α i j y| =
          |η y| * |invGramOnEuclid (I := I) g α i j y| := by
        unfold cutoffInvGram
        rw [abs_mul]
      rw [h1]
      have hηy : |η y| ≤ 1 := hη_bdd y
      have hGy : ‖invGramOnEuclid (I := I) g α i j y‖ ≤ C := hy₀_max hyK
      have hG_abs_eq : |invGramOnEuclid (I := I) g α i j y| =
          ‖invGramOnEuclid (I := I) g α i j y‖ := rfl
      rw [hG_abs_eq]
      calc |η y| * ‖invGramOnEuclid (I := I) g α i j y‖
          ≤ 1 * ‖invGramOnEuclid (I := I) g α i j y‖ := by
              exact mul_le_mul_of_nonneg_right hηy (norm_nonneg _)
        _ ≤ 1 * C := by exact mul_le_mul_of_nonneg_left hGy zero_le_one
        _ = C := one_mul _
    · rw [h_zero_off y hyK, abs_zero]
      exact hC_nn
  · refine ⟨0, le_refl 0, ?_⟩
    intro y
    have hy_notK : y ∉ Kη := fun hyK => hKη_ne ⟨y, hyK⟩
    rw [h_zero_off y hy_notK, abs_zero]

lemma cutoffInvGram_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    Continuous (cutoffInvGram (I := I) (M := M) g α i j) := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def

  have hη_cont : Continuous η :=
    (chartCutoffα_smooth (I := I) (M := M) α).continuous
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α

  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffInvGram (I := I) (M := M) g α i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffInvGram
    rw [hη_zero, zero_mul]

  rw [continuous_iff_continuousAt]
  intro y
  by_cases hyKη : y ∈ Kη
  · have hyΩ : y ∈ Ω := hKη_sub_Ω hyKη
    have hG_cont_at : ContinuousAt (invGramOnEuclid (I := I) g α i j) y := by
      have hG_cont_on : ContinuousOn (invGramOnEuclid (I := I) g α i j) Ω :=
        (invGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
      exact hG_cont_on.continuousAt (hΩ_open.mem_nhds hyΩ)
    have hη_cont_at : ContinuousAt η y := hη_cont.continuousAt
    exact hη_cont_at.mul hG_cont_at
  · have h_nbd : (Kη)ᶜ ∈ 𝓝 y :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hyKη
    have hVal_y : cutoffInvGram (I := I) (M := M) g α i j y = 0 :=
      h_zero_off y hyKη

    have h_eventually_zero :
        cutoffInvGram (I := I) (M := M) g α i j =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_nbd] with z hz
      exact h_zero_off z hz
    have h_const_continuous : ContinuousAt (fun _ : EuclN => (0 : ℝ)) y :=
      continuousAt_const
    have : ContinuousAt (cutoffInvGram (I := I) (M := M) g α i j) y :=
      h_const_continuous.congr h_eventually_zero.symm
    exact this

lemma cutoffInvGram_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (μ : Measure EuclN) :
    AEStronglyMeasurable (cutoffInvGram (I := I) (M := M) g α i j) μ :=
  (cutoffInvGram_continuous (I := I) (M := M) g α i j).aestronglyMeasurable

private lemma invGram_mul_H_H_ae_eq_cutoff_mul_H_H
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    (fun y : EuclN => invGramOnEuclid (I := I) g α i k y *
        invGramOnEuclid (I := I) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => cutoffInvGram (I := I) (M := M) g α i k y *
        cutoffInvGram (I := I) (M := M) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  set V : Set EuclN := Ω \ K with hV_def

  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_sub_Ω : K ⊆ Ω := chartImagePOUTsupport_subset_target (I := I) (M := M) α

  have h_pt_K : ∀ y ∈ K,
      invGramOnEuclid (I := I) g α i k y *
        invGramOnEuclid (I := I) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y =
      cutoffInvGram (I := I) (M := M) g α i k y *
        cutoffInvGram (I := I) (M := M) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := by
    intro y hy
    have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
      chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
    unfold cutoffInvGram
    rw [hη_one]
    ring

  have h_H_zero_ij := laplacianDomainHessianChart_ae_zero_off_support
    (I := I) (M := M) g α hu_h i j
  have h_H_zero_kl := laplacianDomainHessianChart_ae_zero_off_support
    (I := I) (M := M) g α hu_h k l

  have hV_meas : MeasurableSet V := hΩ_meas.diff hK_meas

  refine (ae_restrict_iff' hΩ_meas).mpr ?_

  have hae_ij : (fun y : EuclN =>
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y)
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)) :=
    h_H_zero_ij
  have hae_kl : (fun y : EuclN =>
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y)
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)) :=
    h_H_zero_kl

  have hae_ij' : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y = 0 := by
    have := (ae_restrict_iff' hV_meas).mp hae_ij
    filter_upwards [this] with y hy hyV
    exact hy hyV
  have hae_kl' : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 := by
    have := (ae_restrict_iff' hV_meas).mp hae_kl
    filter_upwards [this] with y hy hyV
    exact hy hyV
  filter_upwards [hae_ij', hae_kl'] with y hy_ij hy_kl hyΩ
  by_cases hyK : y ∈ K
  · exact h_pt_K y hyK
  · have hyV : y ∈ V := ⟨hyΩ, hyK⟩
    have hH_ij_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y = 0 :=
      hy_ij hyV
    have hH_kl_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 :=
      hy_kl hyV
    rw [hH_ij_zero, hH_kl_zero]
    ring

private lemma laplacianDomainHessianChart_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (laplacianDomainHessianChart_memLp_two
    (I := I) (M := M) g α hu_h i j).aestronglyMeasurable

private lemma H_ij_mul_H_kl_integrable
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    Integrable
      (fun y : EuclN =>
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_ij := laplacianDomainHessianChart_memLp_two
    (I := I) (M := M) g α hu_h i j
  have h_kl := laplacianDomainHessianChart_memLp_two
    (I := I) (M := M) g α hu_h k l
  exact MemLp.integrable_mul h_ij h_kl

private lemma cutoffSummand_memLp_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y : EuclN =>
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical

  obtain ⟨C_ik, hC_ik_nn, hC_ik_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α i k
  obtain ⟨C_jl, hC_jl_nn, hC_jl_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α j l

  have h_HH_int := H_ij_mul_H_kl_integrable
    (I := I) (M := M) g α hu_h i j k l
  have h_HH_memLp_one : MemLp (fun y : EuclN =>
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_one_iff_integrable.mpr h_HH_int

  set C := C_ik * C_jl with hC_def
  have hC_nn : 0 ≤ C := mul_nonneg hC_ik_nn hC_jl_nn

  set bdd_fn : EuclN → ℝ := fun y =>
    C * |laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y|
    with hbdd_def
  have hbdd_memLp : MemLp bdd_fn 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_abs : MemLp (fun y => |laplacianDomainHessianChart
        (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y|) 1
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := h_HH_memLp_one.abs
    exact h_abs.const_mul C

  refine MemLp.mono hbdd_memLp ?_ ?_
  · have h_cont_ik : Continuous (cutoffInvGram (I := I) (M := M) g α i k) :=
      cutoffInvGram_continuous (I := I) (M := M) g α i k
    have h_cont_jl : Continuous (cutoffInvGram (I := I) (M := M) g α j l) :=
      cutoffInvGram_continuous (I := I) (M := M) g α j l
    have h_aesm_ik : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α i k)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_cont_ik.aestronglyMeasurable
    have h_aesm_jl : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α j l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_cont_jl.aestronglyMeasurable
    have h_aesm_ij_H := laplacianDomainHessianChart_aestronglyMeasurable
      (I := I) (M := M) g α hu_h i j
    have h_aesm_kl_H := laplacianDomainHessianChart_aestronglyMeasurable
      (I := I) (M := M) g α hu_h k l
    exact ((h_aesm_ik.mul h_aesm_jl).mul h_aesm_ij_H).mul h_aesm_kl_H
  · refine Filter.Eventually.of_forall ?_
    intro y

    simp only [Real.norm_eq_abs, hbdd_def]

    set H_ij := laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j with hH_ij_def
    set H_kl := laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l with hH_kl_def
    set Gik := cutoffInvGram (I := I) (M := M) g α i k with hGik_def
    set Gjl := cutoffInvGram (I := I) (M := M) g α j l with hGjl_def

    have h_abs : |Gik y * Gjl y * H_ij y * H_kl y| =
        |Gik y| * |Gjl y| * |H_ij y * H_kl y| := by
      rw [show Gik y * Gjl y * H_ij y * H_kl y =
            (Gik y * Gjl y) * (H_ij y * H_kl y) by ring]
      rw [abs_mul, abs_mul]
    rw [h_abs]
    have h_step1 : |Gik y| * |Gjl y| ≤ C_ik * C_jl := by
      have h1 := hC_ik_bd y
      have h2 := hC_jl_bd y
      calc |Gik y| * |Gjl y|
          ≤ C_ik * |Gjl y| := by
              exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ C_ik * C_jl := by
              exact mul_le_mul_of_nonneg_left h2 hC_ik_nn
    have h_nonneg_abs_HH : 0 ≤ |H_ij y * H_kl y| := abs_nonneg _
    have h_le_C : |Gik y| * |Gjl y| * |H_ij y * H_kl y| ≤
        C * |H_ij y * H_kl y| := by
      rw [hC_def]
      exact mul_le_mul_of_nonneg_right h_step1 h_nonneg_abs_HH
    set absHH := |H_ij y * H_kl y| with habsHH_def
    have habsHH_nn : 0 ≤ absHH := abs_nonneg _
    have h_eq_abs : C * absHH = |C * absHH| :=
      (abs_of_nonneg (mul_nonneg hC_nn habsHH_nn)).symm
    linarith [h_le_C, h_eq_abs.le, (h_eq_abs.symm).le]

private lemma summand_memLp_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y : EuclN =>
        invGramOnEuclid (I := I) g α i k y *
          invGramOnEuclid (I := I) g α j l y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_cutoff_memLp := cutoffSummand_memLp_one
    (I := I) (M := M) g α hu_h i j k l
  exact MemLp.ae_eq
    (invGram_mul_H_H_ae_eq_cutoff_mul_H_H
      (I := I) (M := M) g α hu_h i j k l).symm h_cutoff_memLp

theorem laplacianDomainHessFrobeniusSqChart_memLp_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (laplacianDomainHessFrobeniusSqChart (I := I) (M := M) g α hu_h) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical

  have h_eq : laplacianDomainHessFrobeniusSqChart (I := I) (M := M) g α hu_h =
      fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := by
    funext y
    rw [laplacianDomainHessFrobeniusSqChart_def]
  rw [h_eq]

  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun i _ => ?_)
  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun j _ => ?_)
  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun k _ => ?_)
  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => ?_)
  exact summand_memLp_one (I := I) (M := M) g α hu_h i j k l

omit [NeZero (Module.finrank ℝ E)] in

theorem laplacianDomainHessianChart_smooth_case
    (g : SmoothRiemannianMetric I M) (α : M)
    (f : SmoothScalar g) (i j : Fin (Module.finrank ℝ E))
    (h_bridge :
      chartPushedU (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g f)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        chartPushed (I := I) (M := M) (chartAtlasPOU I M) α f.toFun) :
    laplacianDomainHessianChart (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) f) i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α f.toFun)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical

  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u_h_mem := smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) f
  set u₁ : EuclN → ℝ := chartPushedU (I := I) (M := M) g α
    (smoothToH1Compl (I := I) (M := M) g f) with hu₁_def
  set u₂ : EuclN → ℝ := chartPushed (I := I) (M := M) (chartAtlasPOU I M) α f.toFun
    with hu₂_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α

  have h_inner_eq :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₁ Ω
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₂ Ω :=
    chosenWeakPartial'_ae_congr (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_bridge i

  have h_outer_eq :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₁ Ω) Ω
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₂ Ω) Ω :=
    chosenWeakPartial'_ae_congr (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_inner_eq j

  change chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₁ Ω) Ω
    =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₂ Ω) Ω
  exact h_outer_eq

end HessianLpClass
end Laplacian
end Analysis
end DifferentialGeometry

end
